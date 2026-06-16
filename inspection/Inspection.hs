{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -fplugin=Stock -fplugin=Test.Inspection.Plugin #-}

-- | Compile-time zero-cost proof.  @inspection-testing@ is a TEST-ONLY
-- dependency; the @stock@ library never depends on it, so users pay nothing.
-- Two complementary pins, each of which FAILS the build if violated:
--
-- (1) Byte-identical to stock (@(==-)@, equality up to types and coercions):
--     the Stock-derived method optimises to the /same Core/ as GHC's own
--     @deriving@ on a twin type.  This needs a stock twin and Core that does
--     not mention the datatype's own names, so it fits @Eq@\/@Ord@\/@Enum@\/
--     @Functor@ — pinned byte-identical here.
--
-- (2) Wrapper fully erased ('hasNoType'): for the classes without a usable
--     twin (@Show@; the lifted @Eq1@\/@Ord1@\/@Show1@\/@Foldable@ and
--     @Eq2@\/@Ord2@\/@Show2@\/@Bifoldable@ — GHC has no stock @deriving@ for
--     these, so there is nothing to @(==-)@ against).  Trick: wrap the argument
--     with the @Stock@\/@Stock1@\/@Stock2@ constructor so the plugin's own
--     unwrap coercion cancels it (@(Stock t) |> rCo = t@); fully applied, the
--     method worker inlines and NO wrapper type survives.  @hasNoType@ proves
--     the newtype and its @coerce@ are gone — i.e. zero cost.
--
-- Pin (2) needs the obligation to /consume/ its result (return @Int@\/@()@\/
-- @String@…) so GHC can't eta-reduce it back to a bare dictionary cast.  Given
-- that, even single-value \"producers\" — @<>@, @mempty@, @minBound@\/
-- @maxBound@ — pin fine: wrap the inputs and consume\/@unStock@ the output, and
-- every wrapper cancels.  The sole holdout is @Read@ (and @Read1@\/@Read2@): it
-- builds a @[(Stock T, String)]@ through opaque combinators (@readParen@\/@lex@
-- at @Stock T@), so the wrapper is baked into intermediate types that can't be
-- consumed away.  @Read@ is covered behaviourally by the @spec@ suite.
module Main (main) where

import Stock
import Test.Inspection
import Data.Functor.Classes (Eq1(..), Ord1(..), Show1(..), Eq2(..), Ord2(..), Show2(..))
import Data.Bifoldable (Bifoldable(..))
import Data.Bitraversable (Bitraversable(..))

-- product: Eq / Ord  (name-free Core — twin-comparable)
data P  = P Int Bool deriving (Eq, Ord) via Stock P
data P' = P' Int Bool deriving stock (Eq, Ord)

-- Show: pinned by newtype erasure (see below)
data S = MkS Int Bool deriving Show via Stock S


-- enumeration: Enum
data E  = E0 | E1 | E2 deriving Enum via Stock E
data E' = F0 | F1 | F2 deriving stock Enum

-- single-value producers: Semigroup/Monoid (mempty, <>) and Bounded
-- (minBound/maxBound).  Unlike Read, the result is one value, so @unStock@
-- cancels the plugin's output wrap pointwise — no wrapper survives.
data Sg = Sg [Int] [Int] deriving (Semigroup, Monoid) via Stock Sg
data Bd = Bd Bool Ordering deriving Bounded via Stock Bd
data Bd' = Bd' Bool Ordering deriving stock Bounded   -- twin for the (==-) pin

-- type constructor: Functor (==-) + Foldable/Eq1/Ord1/Show1 (newtype erasure)
data T  a = T Int a [a]
  deriving stock (Eq, Ord, Show)            -- satisfy the lifted classes' superclasses
  deriving Functor                      via Stock1 T
  deriving (Foldable, Eq1, Ord1, Show1) via Stock1 T
data T' a = T' Int a [a] deriving stock (Functor, Foldable)

-- two-parameter constructor: Bifoldable/Eq2/Ord2/Show2 (newtype erasure)
data B a b = B a b [b]
  deriving stock (Eq, Ord, Show)               -- base of the superclass tower
  deriving (Eq1, Ord1, Show1)              via Stock1 (B a)   -- Eq2/Ord2/Show2 superclasses
  deriving (Bifoldable, Eq2, Ord2, Show2)  via Stock2 B

sEq, tEq :: P -> P -> Bool
sEq = (==)
tEq = \(P a b) (P c d) -> P' a b == P' c d

sCmp, tCmp :: P -> P -> Ordering
sCmp = compare
tCmp = \(P a b) (P c d) -> compare (P' a b) (P' c d)

sFromE, tFromE :: E -> Int
sFromE = fromEnum
tFromE = \e -> fromEnum (toEnum (fromEnum e) :: E')   -- structural twin

sFmap, tFmap :: (a -> b) -> T a -> T b
sFmap = fmap
tFmap = \f (T n x xs) -> T n (f x) (map f xs)

-- Bounded: route the twin through case-of-known-con so its cons cancel,
-- leaving identical name-free Core (same trick as Eq/Ord/Enum/Functor).
sMinB, tMinB, sMaxB, tMaxB :: Bd
sMinB = minBound
tMinB = case (minBound :: Bd') of Bd' a b -> Bd a b
sMaxB = maxBound
tMaxB = case (maxBound :: Bd') of Bd' a b -> Bd a b

-- Foldable: toList; twin routed through T' (its cons cancel).  Pins the
-- explicitly-synthesized foldr against GHC's stock foldr.
sToList, tToList :: T Int -> [Int]
sToList = foldr (:) []
tToList = \(T n x xs) -> foldr (:) [] (T' n x xs)

-- Traversable via the one-liner, pinned against the natural applicative walk.
sTr, tTr :: (Int -> Maybe Int) -> T Int -> Maybe (T Int)
sTr g = fmap unStock1 . traverse g . Stock1
tTr g = \x -> case x of T n y ys -> pure (T n) <*> g y <*> traverse g ys

-- @Show@ can't be twin-pinned with @(==-)@ (it embeds the constructor name, so
-- a same-named twin must live in another module and its worker is a distinct
-- top-level id).  Instead we certify the property that matters for zero cost:
-- /manually/ wrapping the argument with the @Stock@ constructor makes the
-- plugin's own unwrap coercion cancel it — @(Stock t) |> rCo = t@ — and, fully
-- applied (to @""@), the method worker inlines, so NO @Stock@ survives
-- optimisation.  'hasNoType' proves the wrapper and its @coerce@ are erased.
sShow :: Int -> S -> String
sShow d t = showsPrec d (Stock t) ""             -- wrap; plugin unwraps; cancels

-- @Read@ is the exception we cannot pin: it /produces/ the value, so
-- @readsPrec@ at @Stock S@ has result type @[(Stock S, String)]@ — @Stock@ is in
-- the parse result itself, not a cancellable input wrapper.  So neither
-- @(==-)@ (stock uses @ReadPrec@, the plugin the Report's @ReadS@) nor
-- 'hasNoType' applies; @Read@ is covered behaviourally by the @spec@ suite.

-- Lifted classes (no stock twin to @(==-)@ against): pin them the same way as
-- Show — wrap with the @Stock1@ constructor (the plugin's unwrap cancels it),
-- fully apply, and certify no @Stock1@ survives.  All are /consumers/ here.
sFold :: T Int -> Int
sFold t = sum (Stock1 t)

sLiftEq :: T Int -> T Int -> Bool
sLiftEq x y = liftEq (==) (Stock1 x) (Stock1 y)

sLiftCmp :: T Int -> T Int -> Ordering
sLiftCmp x y = liftCompare compare (Stock1 x) (Stock1 y)

sLiftShow :: Int -> T Int -> String
sLiftShow d t = liftShowsPrec showsPrec showList d (Stock1 t) ""

sBifold :: B Int Int -> Int
sBifold x = bifoldr (+) (+) 0 (Stock2 x)

-- @bifoldr@: GHC has no stock @Bifoldable@, so we pin against the natural
-- hand-written /direct/ recursion (the twin routes through @B@'s fields).  This
-- passes only because @bifoldr@ is synthesized directly; the @Endo@-based class
-- default would not match.
sBiFr, tBiFr :: (Int -> [Int] -> [Int]) -> (Int -> [Int] -> [Int]) -> [Int] -> B Int Int -> [Int]
sBiFr = bifoldr
tBiFr = \f g z x -> case x of B a b bs -> f a (g b (foldr g z bs))

-- @bitraverse@ via the one-liner (@fmap unStock2 . bitraverse . Stock2@) pinned
-- against the natural hand-written applicative walk @pure Con <*> .. <*> ..@.
-- Verifies the Stock2 wrapper cancels and the structure matches.
sBiTr, tBiTr :: (Int -> Maybe Int) -> (Int -> Maybe Int) -> B Int Int -> Maybe (B Int Int)
sBiTr f g = fmap unStock2 . bitraverse f g . Stock2
tBiTr f g = \x -> case x of B a b bs -> pure B <*> f a <*> g b <*> traverse g bs

sLiftEq2 :: B Int Int -> B Int Int -> Bool
sLiftEq2 x y = liftEq2 (==) (==) (Stock2 x) (Stock2 y)

sLiftCmp2 :: B Int Int -> B Int Int -> Ordering
sLiftCmp2 x y = liftCompare2 compare compare (Stock2 x) (Stock2 y)

sLiftShow2 :: Int -> B Int Int -> String
sLiftShow2 d x = liftShowsPrec2 showsPrec showList showsPrec showList d (Stock2 x) ""

-- single-value producers: wrap inputs and unwrap the result; both cancel.
-- /consume/ the @<>@ result (return Int) so GHC can't eta-reduce to a bare
-- producer dictionary cast (the same reason 'sShow' returns a String): the
-- @<>@ worker inlines, inputs and output wrappers cancel, no Stock survives.
sMappend :: Sg -> Sg -> Int
sMappend x y = case unStock (Stock x <> Stock y) of Sg p q -> sum p + sum q

sMempty :: Sg
sMempty = unStock (mempty :: Stock Sg)

sMinBound :: Bd
sMinBound = unStock (minBound :: Stock Bd)

sMaxBound :: Bd
sMaxBound = unStock (maxBound :: Stock Bd)

inspect $ 'sEq    ==- 'tEq
inspect $ 'sCmp   ==- 'tCmp
inspect $ 'sFromE ==- 'tFromE
inspect $ 'sFmap  ==- 'tFmap
inspect $ 'sMinB  ==- 'tMinB
inspect $ 'sMaxB  ==- 'tMaxB
inspect $ 'sToList ==- 'tToList
inspect $ 'sTr     ==- 'tTr
inspect $ 'sShow     `hasNoType` ''Stock
inspect $ 'sFold     `hasNoType` ''Stock1
inspect $ 'sLiftEq   `hasNoType` ''Stock1
inspect $ 'sLiftCmp  `hasNoType` ''Stock1
inspect $ 'sLiftShow `hasNoType` ''Stock1
inspect $ 'sBifold   `hasNoType` ''Stock2
inspect $ 'sBiFr     ==- 'tBiFr
inspect $ 'sBiTr     ==- 'tBiTr
inspect $ 'sLiftEq2  `hasNoType` ''Stock2
inspect $ 'sLiftCmp2 `hasNoType` ''Stock2
inspect $ 'sLiftShow2 `hasNoType` ''Stock2
inspect $ 'sMappend  `hasNoType` ''Stock
inspect $ 'sMempty   `hasNoType` ''Stock
inspect $ 'sMinBound `hasNoType` ''Stock
inspect $ 'sMaxBound `hasNoType` ''Stock

main :: IO ()
main = putStrLn "ok: Eq/Ord/Enum/Functor/Bounded/Foldable Core-identical (bifoldr = hand-written); Show/Semigroup/Monoid + lifted consumers erase the wrapper"
