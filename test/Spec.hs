{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
-- numeric literals default to Integer in a couple of checks, and the twin
-- types intentionally have unused selectors — both fine in a test module.
{-# OPTIONS_GHC -fplugin Stock -Wno-type-defaults -Wno-unused-top-binds #-}

-- | Test-suite for the Virtual-Via plugin.  Each synthesized instance is
-- checked against the corresponding @deriving@-derived "twin" type (so the
-- oracle is GHC's own stock deriving), plus round-trip properties.
module Main (main) where

import qualified Stock
import qualified Twin
import Stock.Override (Override(..), Overriding, Override1(..), Overriding1, Override2(..), Overriding2, type (:=), type (-->), At, Keep)
import Control.Applicative (ZipList(..))
import Data.Ord (Down(..))
import qualified Data.Monoid as Mon (Sum(..), Product(..))
import Data.Ix (Ix, range, index, inRange, rangeSize)
import Data.Functor.Contravariant (Contravariant(..), Predicate(..))
import Data.Functor.Classes (Eq1(..), Ord1(..), Show1(..), showsPrec1, Read1(..), readsPrec1, Eq2(..), Ord2(..), Show2(..), Read2(..))
import Text.Read (readPrec, readListPrec, readPrec_to_S)
import Data.Functor.Identity (Identity(..))
import Data.Bifunctor (Bifunctor(..))
import Data.Bifoldable (Bifoldable(..))
import Data.Bitraversable (Bitraversable(..))
import qualified Data.Foldable
import GHC.Generics
  ( Generic, Generically(..), Generically1(..), Rep, from, to, M1(..)
  , datatypeName, conName, conIsRecord, conFixity, selDecidedStrictness
  , Fixity(..), Associativity(..), DecidedStrictness(..), D1, Meta(..)
  , Generic1, from1, to1 )
import qualified GHC.Generics as G
import Data.Kind (Type)
import Data.Coerce (coerce)
import Control.Category (Category)
import qualified Control.Category as Cat
import Control.Arrow (Kleisli(..))
import Data.Type.Equality ((:~:)(Refl), TestEquality(..), castWith)
import Data.Type.Coercion (TestCoercion(..), coerceWith)
import System.Exit (exitFailure)
import Data.List (isInfixOf)
import qualified Data.List
import Control.Monad (unless)
import Control.Exception (try, evaluate, SomeException)

-- ----- types under test (instances synthesized by the plugin) -------------

data Color = Red | Green | Blue
  deriving (Eq, Ord, Show, Read, Enum, Bounded, Ix) via Stock.Stock Color

-- Bounded for a single-constructor product: each field takes its own bound.
data BB = BB Bool Ordering
  deriving (Eq, Show, Bounded) via Stock.Stock BB

-- A "finite singleton" GADT: TestEquality/TestCoercion via Stock1.
data TY a where
  TInt  :: TY Int
  TBool :: TY Bool
  TChar :: TY Char
deriving via Stock.Stock1 TY instance TestEquality TY
deriving via Stock.Stock1 TY instance TestCoercion TY

-- Two constructors share an index (both @TZ_ :: TZ Int@): testEquality compares
-- the type index, not the tag, so TZa\/TZb are mutually "equal".
data TZ a where
  TZa :: TZ Int
  TZb :: TZ Int
  TZc :: TZ Bool
deriving via Stock.Stock1 TZ instance TestEquality TZ

data Sum = A | B Int | C Int Bool | Rec { rf :: Int, rg :: Bool }
  deriving (Eq, Ord, Show, Read) via Stock.Stock Sum
  deriving Generic               via Stock.Stock Sum

data Pair a = Pair a a
  deriving (Eq, Ord, Show, Read) via Stock.Stock (Pair a)

-- infix constructors with distinct fixities
infixr 5 :+:
infixl 6 :*:
data Expr = Lit Int | Expr :+: Expr | Expr :*: Expr
  deriving (Eq, Show, Read) via Stock.Stock Expr

infixr 5 :+.
infixl 6 :*.
data Expr' = Lit' Int | Expr' :+. Expr' | Expr' :*. Expr'
  deriving (Eq, Show)

data Prod = Prod [Int] [Int]
  deriving (Eq, Show)              via Stock.Stock Prod
  deriving Generic                 via Stock.Stock Prod
  deriving (Semigroup, Monoid)     via Generically Prod

-- direct pointwise Semigroup/Monoid (a "faster Generically"), same result
data Sg = Sg [Int] [Int]
  deriving (Eq, Show)
  deriving (Semigroup, Monoid)     via Stock.Stock Sg

-- per-field Override: combine cx additively (Sum) and cy multiplicatively
-- (Product) — both unsaturated @Type -> Type@ modifiers, broadcast to the
-- field's own type.  A behaviour you cannot get from plain @Stock Coord@
-- without rewriting the datatype's field types.
data Coord = Coord { cx :: Int, cy :: Int }
  deriving (Eq, Show)
  deriving Semigroup
    -- lowercase surface sugar (lowered to "cx" := Sum, "cy" := Product by the
    -- same -fplugin Stock at parse time):
    via Stock.Stock (Override Coord [ cx via Mon.Sum, cy via Mon.Product ])

-- type-keyed Override: every Int field via Sum (no record labels needed)
data TK = TK Int Int
  deriving (Eq, Show)
  deriving Semigroup via Stock.Stock (Override TK '[ Int via Mon.Sum ])

-- position-keyed Override: field 0 via Sum, field 1 via Product
data PK = PK Int Int
  deriving (Eq, Show)
  deriving Semigroup
    via Stock.Stock (Override PK [ PK at 0 via Mon.Sum, PK at 1 via Mon.Product ])

-- positional [[..]] Override: one inner list per constructor, one element per
-- field.  @_@ (lowered to 'Keep' by the surface pass) leaves a field alone, so
-- this overrides only the first two fields and keeps the @[Int]@ as-is.
-- Outer list is ticked (single-element ⇒ would otherwise parse as the list type).
data Pos = Pos Int Int [Int]
  deriving (Eq, Show)
  deriving Semigroup
    via Stock.Stock (Override Pos '[ [Mon.Sum, Mon.Product, _] ])

-- the canonical example: @[[Sum Int, _, _]]@ changes only the first field of the
-- first constructor (a /saturated/ @Sum Int :: Type@ modifier, pinned to the
-- field's @Int@); the rest are kept.  'Keep' is poly-kinded, so it sits in a
-- @[Type]@ list here just as it sat in the @[Type -> Type]@ list above.
data PosS = PosS Int [Int] [Int]
  deriving (Eq, Show)
  deriving Semigroup
    via Stock.Stock (Override PosS '[ [Mon.Sum Int, _, _] ])

-- multi-constructor --> paths, observed through the (SDK-native) Eq: a field
-- overridden to 'Mod5' compares modulo 5.  @'MA --> 0 --> Mod5@ targets only
-- MA's first field; @'MB --> Mod5@ every field of MB.  Mod5 is a saturated
-- (pinned) modifier — Coercible Int Mod5.
newtype Mod5 = Mod5 Int
instance Eq Mod5 where Mod5 a == Mod5 b = a `mod` 5 == b `mod` 5
data Multi = MA Int Int | MB Int
  deriving Show
  deriving Eq
    via Stock.Stock (Override Multi '[ 'MA --> 0 --> Mod5, 'MB --> Mod5 ])

-- Ord now respects Override too (was a viaSynth holdout): field0 via Down
-- reverses its comparison, field1 stays normal.
data OrdOv = OrdOv Int Int
  deriving (Eq, Show)
  deriving Ord via Stock.Stock (Override OrdOv '[ [Down, _] ])

-- Show + Read both respect Override: showing field0 as a 'Sum' and reading it
-- back (coercing to Int) round-trips — proving both directions honour it.
data SR = SR Int Int
  deriving stock Eq
  deriving (Show, Read) via Stock.Stock (Override SR '[ [Mon.Sum, _] ])

-- The payoff: Generic respects Override, so @Generically (Override A cfg)@
-- derives /any/ Generically class over the overridden fields.  Here Semigroup
-- combines field0 additively (Sum) and field1 multiplicatively (Product) —
-- driven entirely through the Generic Rep, no Stock-Semigroup deriver.
data CoordG = CoordG Int Int
  deriving (Eq, Show)
  deriving Semigroup
    via Generically (Overriding CoordG '[ [Mon.Sum, Mon.Product] ])

-- ===== Override across the remaining classes that honour it =====

-- Monoid: mempty/mappend through Sum (additive) + Product (multiplicative); the
-- identities are 0 and 1, not Int's (which has no Monoid).
data MonOv = MonOv Int Int deriving (Eq, Show)
  deriving (Semigroup, Monoid)
    via Stock.Stock (Override MonOv '[ [Mon.Sum, Mon.Product] ])

-- Bounded over a product: field0's bounds come from Hi (100..200), not Int's.
newtype Hi = Hi Int deriving (Eq, Show)
instance Bounded Hi where { minBound = Hi 100 ; maxBound = Hi 200 }
data BdOv = BdOv Int Bool deriving (Eq, Show)
  deriving Bounded via Stock.Stock (Override BdOv '[ [Hi, _] ])

-- Enum / Ix are enum-only (no fields): an all-blank config is the identity,
-- so Override neither breaks nor changes them.
data EnOv = EnA | EnB | EnC deriving (Eq, Show)
  deriving (Enum, Ix, Ord) via Stock.Stock (Override EnOv '[ '[], '[], '[] ])

-- top-level empty config @'[]@ on a type WITH fields is the identity: exactly
-- like plain @Stock@ (regression: @'[]@ was mis-read as a 0-constructor
-- positional config and rejected).
data EmptyOv = EmptyOv Int Bool
  deriving (Eq, Show) via Stock.Stock (Override EmptyOv '[])

-- Functor via Override1 with an observable, law-breaking modifier: @Blah@ counts
-- each @fmap@ in its @Int@ slot.  The field @(Int, a)@ is reshaped to @Blah@, so
-- mapping bumps the counter — visibly proving the override is honoured.
newtype Blah a = Blah (Int, a)
instance Functor Blah where fmap f (Blah (n, a)) = Blah (1 + n, f a)
data WithCount a = WithCount (Int, a) deriving (Eq, Show)
  deriving Functor via Overriding1 WithCount '[ '[Blah] ]

-- Contravariant via Override1: the Predicate field reshaped to Neg, whose
-- contramap negates the result (the one observable tweak that stays well-typed).
newtype Neg a = Neg (Predicate a)
instance Contravariant Neg where
  contramap f (Neg (Predicate p)) = Neg (Predicate (not . p . f))
newtype CV a = CV (Predicate a)
  deriving Contravariant via Overriding1 CV '[ '[Neg] ]
runCV :: CV a -> a -> Bool
runCV (CV (Predicate p)) = p

-- Bifunctor via Override2: each list field reshaped to RevL, whose fmap reverses,
-- so bimap reverses both lists.
newtype RevL a = RevL [a]
instance Functor RevL where fmap f (RevL xs) = RevL (reverse (map f xs))
data B2 a b = B2 [a] [b] deriving (Eq, Show)
  deriving Functor   via Stock.Stock1 (B2 a)
  deriving Bifunctor via Overriding2 B2 '[ '[RevL, RevL] ]

-- Override1 / Override2 with the SAME field-keyed surface as value Override,
-- only at a different modifier kind (a functor here) — and in the bare-lowercase
-- plugin notation (@nkXs := m@ / @fld via m@), lowered by the source plugin.
data NK a = NK { nkXs :: [a] } deriving (Eq, Show)
  deriving Functor via Overriding1 NK '[ nkXs := RevL ]
data NK2 a b = NK2 { nk2a :: [a], nk2b :: [b] } deriving (Eq, Show)
  deriving Functor   via Stock.Stock1 (NK2 a)
  deriving Bifunctor via Overriding2 NK2 '[ nk2a via RevL, nk2b via RevL ]

-- A blind/reversing list modifier (coercible to [a]) for the lifted comparison
-- + folding classes: Eq1/Ord1 blind (all equal), Show1 fixed, Foldable reversed.
newtype BL a = BL [a]
instance Eq1   BL where liftEq _ _ _          = True
instance Ord1  BL where liftCompare _ _ _     = EQ
instance Show1 BL where liftShowsPrec _ _ _ _ = showString "BL"
instance Foldable BL where foldMap f (BL xs)  = foldMap f (reverse xs)
-- base instances (the quantified superclasses of BL's lifted instances), blind to match
instance Eq   (BL a) where _ == _       = True
instance Ord  (BL a) where compare _ _  = EQ
instance Show (BL a) where showsPrec _ _ = showString "BL"

-- Eq1 / Ord1 / Show1 via Override1 (the [a] field through BL).  The base
-- Eq/Ord/Show satisfy the lifted classes' quantified superclasses.
data Lc a = Lc [a] deriving (Eq, Ord, Show)
  deriving Eq1   via Overriding1 Lc '[ '[BL] ]
  deriving Ord1  via Overriding1 Lc '[ '[BL] ]
  deriving Show1 via Overriding1 Lc '[ '[BL] ]

-- Eq2 / Ord2 / Show2 / Bifoldable via Override2 (both fields through BL).  The
-- one-parameter lifted instances (superclasses of the two-parameter ones) are
-- plain Stock1.
data Bc a b = Bc [a] [b] deriving (Eq, Ord, Show)
  deriving (Eq1, Ord1, Show1) via Stock.Stock1 (Bc a)
  deriving Eq2        via Overriding2 Bc '[ '[BL, BL] ]
  deriving Ord2       via Overriding2 Bc '[ '[BL, BL] ]
  deriving Show2      via Overriding2 Bc '[ '[BL, BL] ]
  deriving Bifoldable via Overriding2 Bc '[ '[BL, BL] ]

-- Generic1 via Override1 → Applicative via Generically1: the [a] field reshaped
-- to ZipList, so the /generically/-derived Applicative ZIPS instead of the
-- cartesian []-product.  (Proves Generic1 honours Override1 at the Rep1 level.)
data Zg a = Zg [a]
  deriving (Eq, Show)
  deriving Generic1 via Overriding1 Zg '[ '[ZipList] ]
  deriving (Functor, Applicative) via Generically1 Zg
runZg :: Zg a -> [a]
runZg (Zg xs) = xs

-- `_` (Keep) sugar in an Override1 positional config: an identity reshape (the
-- field is left as []).  Confirms the source plugin lowers `_` for the
-- Overriding1 wrapper too, not just value Override.
data Kp a = Kp [a] deriving (Eq, Show)
  deriving Functor via Overriding1 Kp '[ '[_] ]

-- A reversing list modifier (coercible to [a]) whose Read1 reads a list then
-- /reverses/ it — observably different from []'s, so a parsed value reflects the
-- override.  Read1's quantified superclass needs a matching base Read (RL a).
newtype RL a = RL [a]
instance Read1 RL where
  liftReadsPrec rp rl d s = [ (RL (reverse ys), s') | (ys, s') <- liftReadsPrec rp rl d s ]
instance Read a => Read (RL a) where
  readsPrec d s = [ (RL (reverse ys), s') | (ys, s') <- readsPrec d s ]

-- Read1 via Override1: reading @"Lr [1,2,3]"@ parses the field through RL, so the
-- list comes back reversed — proof the modifier is honoured (plain [] would give
-- @Lr [1,2,3]@).
data Lr a = Lr [a] deriving (Eq, Show, Read)
  deriving Read1 via Overriding1 Lr '[ '[RL] ]

-- Read2 via Override2: both list fields parsed through RL ⇒ both come back
-- reversed.  Read2's superclass needs a plain Read1 (Br a).
data Br a b = Br [a] [b] deriving (Eq, Show, Read)
  deriving Read1 via Stock.Stock1 (Br a)
  deriving Read2 via Overriding2 Br '[ '[RL, RL] ]



-- For the representational-fidelity check: 'Gen' has GHC's *stock* Generic
-- (giving the real @Rep Gen@), while the plugin provides @Generic (Stock Gen)@.
-- The two Reps differ only by newtype @M1@/@K1@ layers, so they are 'Coercible'.
data Gen = Gen [Int] [Int]
  deriving (Eq, Generic)

-- A SUM type with stock Generic, for the sum version of the cross-Rep round-trip.
data GenS = GA | GB Int | GC Int Bool
  deriving (Eq, Generic)

-- For metadata (M1) checks: a single-constructor record.
data MetaR = MetaR { mfield :: Int }
  deriving Generic via Stock.Stock MetaR

-- Cross-validation: stock @Generic Gen@ and the plugin's @Generic (Stock Gen)@
-- must drive the SAME @Generically@ algorithm to the SAME result.  We compute
-- @(<>)@ / @mempty@ both ways on the same value (bridging with 'coerce') and
-- compare — a behavioural proof that the synthesized Rep equals stock's.
viaGen, viaStockGen :: Gen -> Gen -> Gen
viaGen      a b = coerce ((coerce a :: Generically Gen)               <> coerce b)
viaStockGen a b = coerce ((coerce a :: Generically (Stock.Stock Gen)) <> coerce b)
memptyGen, memptyStockGen :: Gen
memptyGen      = coerce (mempty :: Generically Gen)
memptyStockGen = coerce (mempty :: Generically (Stock.Stock Gen))

-- Functor via Stock1 (parameter field, constant field, functor field)
data Trio a = Trio Int a [a]
  deriving (Eq, Ord, Show, Read) via Stock.Stock (Trio a)
  deriving Functor    via Stock.Stock1 Trio
  deriving Foldable   via Stock.Stock1 Trio
  -- Eq1/Ord1: Int field (own Eq/Ord), the parameter (supplied fn), [a] (lifted)
  deriving (Eq1, Ord1) via Stock.Stock1 Trio
  deriving Show1       via Stock.Stock1 Trio
  deriving Read1       via Stock.Stock1 Trio
data Trio' a = Trio' Int a [a] deriving (Eq, Show, Functor, Foldable)

-- Applicative via Stock1 handles a constant field Const-style (needs Monoid),
-- exactly as Generically1: pure fills it with mempty, <*> combines it with (<>).
data Ap a = Ap [Int] a
  deriving (Eq, Show)
  deriving (Functor, Applicative) via Stock.Stock1 Ap

-- Override1: the [a] field reshaped to ZipList, so Applicative ZIPS (instead of
-- the cartesian product []), and Functor is unchanged.
data Zl a = Zl [a]
  deriving (Eq, Show)
  deriving Functor     via Overriding1 Zl '[ '[ZipList] ]
  deriving Applicative via Overriding1 Zl '[ '[ZipList] ]
  deriving Foldable    via Overriding1 Zl '[ '[ZipList] ]

-- Traversable: the instance is SYNTHESIZED at @Stock1 _@ (DerivingVia can't
-- coerce it onto the type — abstract-applicative nominal role), and put on the
-- type with the one-liner.  Trav is recursive (param + recursive-functor + list
-- fields); Trav' is GHC's own stock-derived oracle.
data Trav a = TLeaf | TNode (Trav a) a [a]
  deriving (Eq, Show)
  deriving (Functor, Foldable) via Stock.Stock1 Trav
instance Traversable Trav where
  traverse g = fmap Stock.unStock1 . traverse g . Stock.Stock1
data Trav' a = TLeaf' | TNode' (Trav' a) a [a]
  deriving (Eq, Show, Functor, Foldable, Traversable)

-- Nested + tuple fields: Functor/Foldable/Traversable must match GHC's full
-- structural walk (nested [[a]], Maybe [a], tuple (a,a)). NestG is GHC's oracle.
data Nest a = Nest [[a]] (Maybe [a]) (a, a) a
  deriving (Eq, Show)
  deriving (Functor, Foldable) via Stock.Stock1 Nest
instance Traversable Nest where
  traverse g = fmap Stock.unStock1 . traverse g . Stock.Stock1
data NestG a = NestG [[a]] (Maybe [a]) (a, a) a
  deriving (Eq, Show, Functor, Foldable, Traversable)
nestVal :: ([[Int]], Maybe [Int], (Int, Int), Int)
nestVal = ([[1,2],[3]], Just [4,5], (6,7), 8)
cNe :: Nest Int -> ([[Int]], Maybe [Int], (Int, Int), Int)
cNe (Nest a b c d) = (a, b, c, d)
cNeG :: NestG Int -> ([[Int]], Maybe [Int], (Int, Int), Int)
cNeG (NestG a b c d) = (a, b, c, d)

-- Ix on a single-constructor PRODUCT (GHC derives it; we now match): range is
-- the Cartesian product, index mixed-radix. IxPG is GHC's stock twin.
data IxP = IxP Int Bool deriving (Eq, Ord, Show)
  deriving Ix via Stock.Stock IxP
data IxPG = IxPG Int Bool deriving (Eq, Ord, Show, Ix)
cIxP :: IxP -> (Int, Bool)
cIxP (IxP a b) = (a, b)
cIxPG :: IxPG -> (Int, Bool)
cIxPG (IxPG a b) = (a, b)

-- Generic META parity: infix constructor fixity (#1) and field strictness (#3)
-- must match GHC's derived Rep (phantom type-level meta, vs twins).
infixr 7 :*:.
data MOp  = Int :*:. Int  deriving (Eq, Show) ; deriving via Stock.Stock MOp instance Generic MOp
infixr 7 :*:~
data MOpG = Int :*:~ Int  deriving (Eq, Show, Generic)
data MStr  = MStr  ![Int] Int deriving (Eq, Show) ; deriving via Stock.Stock MStr instance Generic MStr
data MStrG = MStrG ![Int] Int deriving (Eq, Show, Generic)
data MSum = MN | MP Int Bool | MR { mrf :: Int, mrg :: Bool } deriving (Eq, Show)
deriving via Stock.Stock MSum instance Generic MSum

-- STATIC Rep parity: normalize only the module/package strings in the outer D1
-- (those legitimately differ Main vs Twin), then assert the ENTIRE Rep type —
-- datatype name + isNewtype, constructor fixity (#1), selector strictness (#3),
-- record/field meta, and the balanced sum/product shape — is IDENTICAL to GHC's
-- derived Rep.  Any divergence is a compile-time type error.
type family DummyMP (r :: Type -> Type) :: Type -> Type where
  DummyMP (D1 ('MetaData n _ _ nt) x) = D1 ('MetaData n "M" "P" nt) x
repParityMOp  :: DummyMP (Rep MOp)  () :~: DummyMP (Rep Twin.MOp)  ()
repParityMOp  = Refl
repParityMStr :: DummyMP (Rep MStr) () :~: DummyMP (Rep Twin.MStr) ()
repParityMStr = Refl
repParityMSum :: DummyMP (Rep MSum) () :~: DummyMP (Rep Twin.MSum) ()
repParityMSum = Refl

-- Ord relational ops (#6): a small (<=3-con) product gets direct <,<=,>,>= ;
-- they must agree with GHC's derived twin for every pair.
data OrdT  = OA  | OB  Int Bool
  deriving (Eq, Show) deriving Ord via Stock.Stock OrdT
data OrdTG = OAg | OBg Int Bool deriving (Eq, Show, Ord)
cOrdT :: OrdT -> OrdTG
cOrdT OA = OAg ; cOrdT (OB i b) = OBg i b
ordVals :: [OrdT]
ordVals = [OA, OB 1 True, OB 1 False, OB 2 False, OB 2 True]

data KTr = KLeaf | KNode KTr Int [Int] deriving (Eq, Show)
cTr :: Trav Int -> KTr
cTr TLeaf = KLeaf ; cTr (TNode l x xs) = KNode (cTr l) x xs
cTr' :: Trav' Int -> KTr
cTr' TLeaf' = KLeaf ; cTr' (TNode' l x xs) = KNode (cTr' l) x xs

-- Override1 + Traversable: the [a] field traverses through ZipList's Traversable.
instance Traversable Zl where
  traverse g = fmap Stock.unStock1 . traverse g . Stock.Stock1

-- Bitraversable: synthesized at @Stock2 _@ + the one-liner.  GHC has no
-- stock @deriving Bitraversable@, so we check the law @bitraverse (Just . f)
-- (Just . g) = Just . bimap f g@ (and identity / short-circuit).
data BT a b = BTNil | BTBoth a b | BTList a [b] Int
  deriving (Eq, Show)
  deriving (Functor, Foldable)     via Stock.Stock1 (BT a)
  deriving (Bifunctor, Bifoldable) via Stock.Stock2 BT
instance Bitraversable BT where
  bitraverse f g = fmap Stock.unStock2 . bitraverse f g . Stock.Stock2

runZl :: Zl a -> [a]
runZl (Zl xs) = xs

-- @f@ is abstract, so @Eq (f a)@ / @Ord (f a)@ / @Show (f a)@ can only come
-- from the quantified superclass of @Eq1 f@ / @Ord1 f@ / @Show1 f@.
eqViaEq1 :: (Eq1 f, Eq a) => f a -> f a -> Bool
eqViaEq1 = (==)
cmpViaOrd1 :: (Ord1 f, Ord a) => f a -> f a -> Ordering
cmpViaOrd1 = compare
showViaShow1 :: (Show1 f, Show a) => f a -> String
showViaShow1 x = show x

-- a parameterised record, to exercise Show1's record path (K {l = v, …})
data Recd a = Recd { rx :: a, ry :: [a] }
  deriving (Eq, Show, Read) via Stock.Stock (Recd a)
  deriving Show1  via Stock.Stock1 Recd
  deriving Read1  via Stock.Stock1 Recd

-- @f@ abstract ⇒ Read (f a) can only come from the quantified Read1 superclass
readViaRead1 :: (Read1 f, Read a) => String -> f a
readViaRead1 = read

-- Generic1 via Stock1: Par1 (@a@), Rec1 (@[a]@), Rec0 (@Int@), and @:.:@
-- composition (@[[a]]@ = @[] :.: Rec1 []@).
data G1 a = G1 Int a [a] [[a]] | G1' a
  deriving (Eq, Show)
  deriving Generic1 via Stock.Stock1 G1

-- Contravariant via Stock1: the parameter only in negative positions.  GHC has
-- no stock 'deriving Contravariant', so we check against the laws directly.
-- 'Sel' mixes a function field (negative), a constant, and a 'Pred' subfield
-- (itself contravariant) — and 'Pred' is a newtype (unwrapped by coercion).
newtype Pred a = Pred (a -> Bool)
  deriving Contravariant via Stock.Stock1 Pred
data Sel r a = Sel (a -> r) Int (Pred a)
  deriving Contravariant via Stock.Stock1 (Sel r)

runPred :: Pred a -> a -> Bool
runPred (Pred p) = p

-- Variance fidelity: the parameter under nested function arrows.  @(a -> Int)
-- -> Int@ is double-negative ⇒ covariant ⇒ a 'Functor' (GHC's stock
-- DeriveFunctor accepts it too); the triple-nested one is contravariant.
newtype Cps a = Cps ((a -> Int) -> Int)
  deriving Functor via Stock.Stock1 Cps
runCps :: Cps a -> (a -> Int) -> Int
runCps (Cps g) = g
newtype Cps3 a = Cps3 (((a -> Int) -> Int) -> Int)
  deriving Contravariant via Stock.Stock1 Cps3
forceCps3 :: Cps3 a -> ()
forceCps3 (Cps3 g) = g `seq` ()

-- multi-argument contravariant field (parameter in two negative positions)
newtype Foo2 a = Foo2 (a -> a -> Int)
  deriving Contravariant via Stock.Stock1 Foo2
runFoo2 :: Foo2 a -> a -> a -> Int
runFoo2 (Foo2 h) = h

-- Bifunctor / Bifoldable via Stock2 (mix of a-, b-, [b]- and constant fields).
-- Bifunctor's quantified superclass forall a. Functor (Bi a) needs Functor too.
data Bi a b = Bi a b | OnlyA a | Bs b [b] | Tag Int
  deriving (Eq, Ord, Show, Read)
  deriving (Functor, Eq1, Ord1, Show1, Read1)              via Stock.Stock1 (Bi a)
  deriving (Bifunctor, Bifoldable, Eq2, Ord2, Show2, Read2) via Stock.Stock2 Bi

-- Bifunctor with a NESTED bifunctor field (@Either a b@) and a nested covariant
-- field (@[b]@) — both reached by the n-ary variance engine (the self-app case
-- for @Either a b@; deep functor recursion for @[b]@), which the flat
-- 'classifyBiField' could not map.
data BiE a b = BiE (Either a b) [b]
  deriving (Eq, Show)
  deriving Functor   via Stock.Stock1 (BiE a)
  deriving Bifunctor via Stock.Stock2 BiE

-- Category via Stock2: pointwise id/(.) over a single-constructor product whose
-- fields are each a Category in the two params (here (:~:) and (->)).
data P2 a b = P2 (a :~: b) (a -> b)
  deriving Category via Stock.Stock2 P2

runP2 :: P2 a b -> (a -> b)
runP2 (P2 _ f) = f

-- Category with a CONSTANT field (Sum Int): handled Const-style via Monoid
-- (id = mempty, (.) = (<>)) — no Basic / Override2 needed.
data LC a b = LC (Mon.Sum Int) (a -> b)
  deriving Category via Stock.Stock2 LC

runLC :: LC a b -> (Mon.Sum Int, a -> b)
runLC (LC s f) = (s, f)

-- A trivial Category that ignores its parameters and just accumulates a monoid.
newtype Basic m a b = Basic m
instance Monoid m => Category (Basic m) where
  id :: Basic m a a
  id = Basic mempty
  (.) :: Basic m b c -> Basic m a b -> Basic m a c
  Basic x . Basic y = Basic (x <> y)

-- The payoff: fields that are NOT yet categories (an Int, a String, an
-- @a -> Maybe b@) are reshaped by Override2 into ones — Basic (Sum Int),
-- Basic String, Kleisli Maybe — and Category is then derived pointwise.
data Foo a b = Foo Int String (a -> Maybe b)
  deriving Category
    via Overriding2 Foo '[ '[ Basic (Mon.Sum Int), Basic String, Kleisli Maybe ] ]

runFoo :: Foo a b -> (Int, String, a -> Maybe b)
runFoo (Foo i s f) = (i, s, f)

-- Run a value through stock @from@, 'coerce' between the two (representationally
-- equal) Reps, then bring it back with the plugin's @to@.  Compiles only if
-- @Rep (Stock Gen) ~R Rep Gen@, and round-trips only if @to@ is correct.
repCrossRoundtrip :: Gen -> Gen
repCrossRoundtrip g =
  Stock.unStock (to (coerce (from g :: Rep Gen ()) :: Rep (Stock.Stock Gen) ()))

-- same, for a SUM type: exercises the @:+:@ structure across the two Reps
repCrossRoundtripS :: GenS -> GenS
repCrossRoundtripS g =
  Stock.unStock (to (coerce (from g :: Rep GenS ()) :: Rep (Stock.Stock GenS) ()))

-- parameterised INFIX types: exercise Read1/Read2 ambiguous-parse ORDER, which
-- only the ReadPrec-based synthesis matches (plain prefix/record can't show it).
infixr 5 :++
data InfF a = ILit a | InfF a :++ InfF a
  deriving (Eq, Show)
  deriving Read  via Stock.Stock (InfF a)     -- Read1's quantified superclass needs it
  deriving Read1 via Stock.Stock1 InfF
infixr 5 :**
data InfB a b = IB a b | a :** b
  deriving (Eq, Show)
  deriving Read  via Stock.Stock (InfB a b)
  deriving Read1 via Stock.Stock1 (InfB a)
  deriving Read2 via Stock.Stock2 InfB

-- ----- stock-derived twins (the oracle) -----------------------------------

data Color' = Red' | Green' | Blue'
  deriving (Eq, Ord, Show, Enum, Bounded)
data Sum' = A' | B' Int | C' Int Bool | Rec' { rf' :: Int, rg' :: Bool }
  deriving (Eq, Ord, Show)

-- drop the primes and map the twin operators (@:+.@/@:*.@) back to ours
-- (@:+:@/@:*:@) so a twin's `show` matches ours textually
norm :: String -> String
norm = map (\c -> if c == '.' then ':' else c) . filter (/= '\'')

-- ----- Read parity vs GHC stock (the strong check) -------------------------
--
-- Round-trips only prove @read . show = id@.  These compare the FULL @readsPrec@
-- ReadS result (parsed value + leftover string + list order/length) of the
-- plugin's instance against GHC's own derived @Read@ on a name-identical twin,
-- over valid / whitespaced / parenthesised / negative / garbage / trailing-junk
-- inputs at several precedences.  Equality of the lists == identical behaviour.

-- neutral canonical forms (so the two distinct twin types are comparable)
data KS = KA | KB Int | KC Int Bool | KRec Int Bool deriving (Eq, Show)
data KE = KLit Int | KAdd KE KE | KMul KE KE         deriving (Eq, Ord, Show)
data KBi = KBi Int Bool | KOnlyA Int | KBs Bool [Bool] | KTag Int deriving (Eq, Show)

cS :: Sum -> KS
cS A = KA; cS (B i) = KB i; cS (C i b) = KC i b; cS (Rec i b) = KRec i b
cST :: Twin.Sum -> KS
cST Twin.A = KA; cST (Twin.B i) = KB i; cST (Twin.C i b) = KC i b; cST (Twin.Rec i b) = KRec i b

cE :: Expr -> KE
cE (Lit i)  = KLit i; cE (a :+: b) = KAdd (cE a) (cE b); cE (a :*: b) = KMul (cE a) (cE b)
cET :: Twin.Expr -> KE
cET (Twin.Lit i)    = KLit i
cET (a Twin.:+: b)  = KAdd (cET a) (cET b)
cET (a Twin.:*: b)  = KMul (cET a) (cET b)

cT :: Trio Int -> (Int, Int, [Int])
cT (Trio i a xs) = (i, a, xs)
cTT :: Twin.Trio Int -> (Int, Int, [Int])
cTT (Twin.Trio i a xs) = (i, a, xs)

cR :: Recd Int -> (Int, [Int])
cR (Recd x ys) = (x, ys)
cRT :: Twin.Recd Int -> (Int, [Int])
cRT (Twin.Recd x ys) = (x, ys)

cB :: Bi Int Bool -> KBi
cB (Bi a b) = KBi a b; cB (OnlyA a) = KOnlyA a; cB (Bs b xs) = KBs b xs; cB (Tag i) = KTag i
cBT :: Twin.Bi Int Bool -> KBi
cBT (Twin.Bi a b) = KBi a b; cBT (Twin.OnlyA a) = KOnlyA a
cBT (Twin.Bs b xs) = KBs b xs; cBT (Twin.Tag i) = KTag i

data KInf = KIL Int | KIAdd KInf KInf deriving (Eq, Ord, Show)
cInf :: InfF Int -> KInf
cInf (ILit n) = KIL n; cInf (a :++ b) = KIAdd (cInf a) (cInf b)
cInfT :: Twin.InfF Int -> KInf
cInfT (Twin.ILit n) = KIL n; cInfT (a Twin.:++ b) = KIAdd (cInfT a) (cInfT b)

data KIB = KIB Int Bool | KIBop Int Bool deriving (Eq, Ord, Show)
cIB :: InfB Int Bool -> KIB
cIB (IB a b) = KIB a b; cIB (a :** b) = KIBop a b
cIBT :: Twin.InfB Int Bool -> KIB
cIBT (Twin.IB a b) = KIB a b; cIBT (a Twin.:** b) = KIBop a b

-- mismatches between plugin ReadS and twin ReadS over (precision, input) pairs
parityAt :: Eq k
         => [Int] -> (Int -> ReadS a) -> (Int -> ReadS b)
         -> (a -> k) -> (b -> k) -> [String] -> [(Int, String, [(k, String)], [(k, String)])]
parityAt precs rp rpT ca cb inputs =
  [ (p, s, l, r)
  | p <- precs, s <- inputs
  , let l = map (Data.Bifunctor.first ca) (rp p s)
        r = map (Data.Bifunctor.first cb) (rpT p s)
  , l /= r ]

parityCheck :: (Eq k, Show k)
            => String -> [Int] -> (Int -> ReadS a) -> (Int -> ReadS b)
            -> (a -> k) -> (b -> k) -> [String] -> IO Bool
parityCheck = parityCheckWith id

-- Read1/Read2 entry via the ReadPrec methods with NATIVE readPrec leaves (the
-- fair oracle: the default ReadS entry @liftReadsPrec readsPrec readList@ wraps
-- leaves with @readS_to_Prec@, which perturbs ReadP result order independently
-- of the synthesis).
rp1 :: (Read1 f, Read a) => Int -> ReadS (f a)
rp1 = readPrec_to_S (liftReadPrec readPrec readListPrec)
rp2 :: (Read2 f, Read a, Read b) => Int -> ReadS (f a b)
rp2 = readPrec_to_S (liftReadPrec2 readPrec readListPrec readPrec readListPrec)

-- For ambiguous INFIX grammars the SET of parses is identical but the list
-- ORDER differs (GHC's 'ReadPrec' search vs our 'ReadS' append) — so we compare
-- as a multiset.  This is the one documented ReadS-vs-ReadPrec residual; @read@
-- and any unique-parse input are unaffected (a single result has no order).
parityCheckU :: (Ord k, Show k)
             => String -> [Int] -> (Int -> ReadS a) -> (Int -> ReadS b)
             -> (a -> k) -> (b -> k) -> [String] -> IO Bool
parityCheckU = parityCheckWith Data.List.sort

parityCheckWith :: (Eq k, Show k)
                => ([(k, String)] -> [(k, String)])
                -> String -> [Int] -> (Int -> ReadS a) -> (Int -> ReadS b)
                -> (a -> k) -> (b -> k) -> [String] -> IO Bool
parityCheckWith norm0 name precs rp rpT ca cb inputs = do
  let ms = [ m | m@(_, _, l, r) <- parityAt precs rp rpT ca cb inputs, norm0 l /= norm0 r ]
  mapM_ (\(p, s, l, r) -> putStrLn (unlines
           [ "   prec=" ++ show p ++ " input=" ++ show s
           , "     via Stock: " ++ show l
           , "     GHC stock: " ++ show r ])) ms
  check name (null ms)

sumInputs, exprInputs, trioInputs, recdInputs, biInputs :: [String]
sumInputs =
  [ "A", "B 5", "B (-5)", "C 1 True", "C 0 False"
  , "Rec {rf = 3, rg = False}", "Rec {rf=3,rg=True}", "Rec { rf = 1 , rg = True }"
  , "  A  ", " B 7 ", "(A)", "((B 9))", "(C 1 True)"
  , "", "B", "B x", "Zzz", "C 1", "A xyz", "B 5 rest"
  , "Rec {rf=1}", "Rec {rf=1, foo=2}", "B 5.0", "-3", "B 0x10" ]
exprInputs =
  [ "Lit 1", "Lit (-2)", "Lit 1 :+: Lit 2", "Lit 1 :+: Lit 2 :+: Lit 3"
  , "Lit 1 :*: Lit 2 :+: Lit 3", "Lit 1 :+: Lit 2 :*: Lit 3"
  , "(Lit 1 :+: Lit 2) :*: Lit 3", "Lit 1 :*: (Lit 2 :+: Lit 3)"
  , " Lit 1 :+: Lit 2 ", "((Lit 1))"
  , "", "Lit", "Lit 1 :+:", ":+: Lit 1", "Lit 1 :+: Lit 2 rest" ]
trioInputs =
  [ "Trio 1 2 [3,4]", "Trio (-1) (-2) [-3,-4]", " Trio 0 0 [] "
  , "(Trio 1 2 [3])", "", "Trio 1 2", "Trio 1 2 [3,4] rest", "Trio 1 2 3" ]
recdInputs =
  [ "Recd {rx = 1, ry = [2,3]}", "Recd {rx=0, ry=[]}", " Recd { rx = 5 , ry = [1] } "
  , "", "Recd {rx=1}", "Recd {rx=1, ry=[2], z=3}" ]
biInputs =
  [ "Bi 1 True", "OnlyA 5", "OnlyA (-5)", "Bs True [False,True]", "Tag 9", "Tag (-9)"
  , " Bi 1 True ", "(OnlyA 5)", "", "Bi 1", "Bs True", "Zzz", "Bi 1 True rest" ]
infInputs, ibInputs :: [String]
infInputs =
  [ "ILit 1", "ILit (-2)", "ILit 1 :++ ILit 2", "ILit 1 :++ ILit 2 :++ ILit 3"
  , "ILit 1 :++ (ILit 2 :++ ILit 3)", "(ILit 1 :++ ILit 2) :++ ILit 3"
  , " ILit 1 :++ ILit 2 ", "", "ILit", "ILit 1 :++", "ILit 1 :++ ILit 2 rest" ]
ibInputs =
  [ "IB 1 True", "1 :** True", "(IB 1 True)", "(1 :** True)", " 1 :** True "
  , "", "IB 1", "1 :**", "IB 1 True rest" ]

-- ----- tiny assertion harness ---------------------------------------------

check :: String -> Bool -> IO Bool
check name ok = do
  putStrLn ((if ok then "ok   " else "FAIL ") ++ name)
  pure ok

-- True if forcing @x@ throws (GHC's derived toEnum/succ/pred error out of range;
-- ours must too, not segfault).
throws :: a -> IO Bool
throws x = do
  r <- try (evaluate (x `seq` ())) :: IO (Either SomeException ())
  pure (either (const True) (const False) r)

main :: IO ()
main = do
  enumOOB  <- throws (toEnum 99 :: Color)
  enumSucc <- throws (succ Blue)
  enumPred <- throws (pred Red)
  rs <- sequence
    [ -- Eq / Ord against twins
      check "Eq enum"       (Red == Red && Red /= Blue)
    , check "Ord enum"      (compare Blue Red == compare Blue' Red')
    , check "Ord fields"    (compare (C 1 True) (C 1 False) == GT && B 1 < C 0 False)
    , check "Ord lexico"    ([minimum xs, maximum xs] == [A, Rec 9 True])
      -- #6: direct <,<=,>,>= for a small type agree with GHC's derived twin
    , check "Ord rel ops"   (and [ (x <  y) == (cOrdT x <  cOrdT y)
                                 && (x <= y) == (cOrdT x <= cOrdT y)
                                 && (x >  y) == (cOrdT x >  cOrdT y)
                                 && (x >= y) == (cOrdT x >= cOrdT y)
                                  | x <- ordVals, y <- ordVals ])
      -- Show against twins (record, prefix, nesting, negatives)
    , check "Show enum"     (show Green == norm (show Green'))
    , check "Show prefix"   (show (C 1 True) == norm (show (C' 1 True)))
    , check "Show neg"      (show (B (-5)) == norm (show (B' (-5))))
    , check "Show record"   (show (Rec 3 True) == norm (show (Rec' 3 True)))
    , check "Show nested"   (show (Just (B 7)) == norm (show (Just (B' 7))))
      -- Read round-trips
    , check "Read enum"     (read "Green" == Green)
    , check "Read rt prefix"(read (show (C 4 False)) == C 4 False)
    , check "Read rt record"(read (show (Rec 5 False)) == Rec 5 False)
    , check "Read paren/ws" (read "  (B (-2)) " == B (-2))
      -- Read PARITY: full readsPrec ReadS output == GHC's own derived Read
    , parityCheck "Read parity Sum"   [0,11] readsPrec readsPrec cS cST sumInputs
    , parityCheck "Read parity Expr"  [0,6,7,11] readsPrec readsPrec cE cET exprInputs
    , parityCheck "Read parity Trio"  [0,11] readsPrec readsPrec cT cTT trioInputs
    , parityCheck "Read parity Recd"  [0,11] readsPrec readsPrec cR cRT recdInputs
      -- Read1 PARITY: liftReadPrec (native readPrec leaves) at a concrete type
      -- == GHC's derived Read of the monomorphic twin
    , parityCheck "Read1 parity Trio" [0,11] rp1 readsPrec cT cTT trioInputs
    , parityCheck "Read1 parity Recd" [0,11] rp1 readsPrec cR cRT recdInputs
      -- Read2 PARITY: liftReadPrec2 at concrete types == derived Read of twin
    , parityCheck "Read2 parity Bi"   [0,11] rp2 readsPrec cB cBT biInputs
      -- INFIX parity: the ambiguous-parse ORDER (only ReadPrec synthesis matches)
    , parityCheck "Read parity InfF"  [0,5,6,11] readsPrec readsPrec cInf cInfT infInputs
    , parityCheck "Read1 parity InfF" [0,5,6,11] rp1 readsPrec cInf cInfT infInputs
    , parityCheck "Read2 parity InfB" [0,5,6,11] rp2 readsPrec cIB cIBT ibInputs
      -- Traversable: synthesized at Stock1, used via the one-liner; behaviour
      -- matches GHC's stock-derived twin (Maybe applicative: success + failure),
      -- and obeys the identity law.
    , check "Traversable rt"  (let t  = TNode (TNode TLeaf 1 [2,3]) 4 [5 :: Int]
                                   t' = TNode' (TNode' TLeaf' 1 [2,3]) 4 [5]
                               in fmap cTr (traverse (Just . (*10)) t)
                                  == fmap cTr' (traverse (Just . (*10)) t'))
    , check "Traversable fail"(traverse (\x -> if x == 4 then Nothing else Just x)
                                 (TNode TLeaf (4 :: Int) [5]) == Nothing)
    , check "Traversable id"  (let t = TNode (TNode TLeaf 1 [2,3]) 4 [5 :: Int]
                               in runIdentity (traverse Identity t) == t)
    , check "Traversable Ov1" (let z = Zl [1,2,3 :: Int]
                               in fmap runZl (traverse Just z) == Just [1,2,3])
      -- Bitraversable: no GHC stock oracle, so check the bimap law + id + failure
    , check "Bitraversable law"(let t = BTList 1 [True,False] 9 :: BT Int Bool
                                in bitraverse (Just . (+1)) (Just . not) t
                                   == Just (bimap (+1) not t))
    , check "Bitraversable id" (let t = BTBoth (7 :: Int) True
                                in bitraverse Just Just t == Just t)
    , check "Bitraversable fl" (bitraverse (\x -> if x > 0 then Just x else Nothing) Just
                                  (BTBoth (-1 :: Int) True) == Nothing)
      -- nested/tuple Functor+Foldable+Traversable must match GHC's full walk
    , check "FFT nest fmap" (let (a,b,c,d) = nestVal
                             in cNe (fmap (*10) (Nest a b c d))
                                == cNeG (fmap (*10) (NestG a b c d)))
    , check "FFT nest fold" (let (a,b,c,d) = nestVal
                             in Data.Foldable.toList (Nest a b c d)
                                == Data.Foldable.toList (NestG a b c d))
    , check "FFT nest trav" (let (a,b,c,d) = nestVal
                             in fmap cNe (traverse Just (Nest a b c d))
                                == fmap cNeG (traverse Just (NestG a b c d)))
      -- parameterised
    , check "param Eq"      (Pair (1::Int) 2 == Pair 1 2 && Pair 1 2 /= Pair 1 3)
    , check "param rt"      (read (show (Pair (1::Int) 2)) == Pair 1 2)
      -- Enum / Bounded
    , check "Enum from"     (map fromEnum [Red ..] == [0,1,2])
    , check "Enum to"       (toEnum 1 == Green)
      -- GHC's derived toEnum/succ/pred ERROR out of range; ours must too
    , check "Enum oob"      enumOOB
    , check "Enum succ max" enumSucc
    , check "Enum pred min" enumPred
    , check "Enum range"    ([Red ..] == [Red, Green, Blue])
    , check "Bounded"       ((minBound, maxBound) == (Red, Blue))
    , check "Bounded prod"  ((minBound, maxBound) == (BB False LT, BB True GT))
      -- Ix
    , check "Ix range"      (range (Red, Blue) == [Red, Green, Blue])
    , check "Ix index"      (index (Red, Blue) Green == 1)
    , check "Ix inRange"    (inRange (Red, Blue) Green && not (inRange (Green, Blue) Red))
    , check "Ix rangeSize"  (rangeSize (Red, Blue) == 3)
      -- Ix on a single-con product == GHC's derived twin (Cartesian range etc.)
    , check "Ix product"    (let (lp,up) = (IxP 1 False, IxP 2 True)
                                 (lg,ug) = (IxPG 1 False, IxPG 2 True)
                             in map cIxP (range (lp,up)) == map cIxPG (range (lg,ug))
                                && map (index (lp,up)) (range (lp,up))
                                   == map (index (lg,ug)) (range (lg,ug))
                                && rangeSize (lp,up) == rangeSize (lg,ug)
                                && and [ inRange (lp,up) (IxP i b) == inRange (lg,ug) (IxPG i b)
                                       | i <- [0..3], b <- [False,True] ])
      -- Generic META: infix-con fixity (#1) and field strictness (#3) match GHC
    , check "Generic fixity"(conFixity (unM1 (from (1 :*:. 2)))
                             == conFixity (unM1 (from (1 :*:~ 2)))
                             && conFixity (unM1 (from (1 :*:. 2))) == Infix RightAssociative 7)
    , check "Generic strict"(let sd x = case unM1 (unM1 (from x)) of l G.:*: _ -> selDecidedStrictness l
                             in sd (MStr [1] 2) == sd (MStrG [1] 2) && sd (MStr [1] 2) == DecidedStrict)
      -- Generic + Generically (the synthesized Rep bootstraps these)
    , check "Generic rt"    (to (from (Prod [1] [2])) == Prod [1] [2])
    , check "Generically <>"(Prod [1] [2] <> Prod [3] [4] == Prod [1,3] [2,4])
    , check "Generically me"(mempty == Prod [] [])
      -- direct pointwise Semigroup/Monoid via Stock (same result as Generically)
    , check "Semigroup <>"  (Sg [1] [2] <> Sg [3] [4] == Sg [1,3] [2,4])
    , check "Monoid mempty" (mempty == Sg [] [])
      -- empty config '[] is the identity (same as plain Stock), with fields
    , check "Override '[] id" (show (EmptyOv 1 True) == "EmptyOv 1 True"
                               && EmptyOv 1 True == EmptyOv 1 True
                               && EmptyOv 1 True /= EmptyOv 2 True)
      -- per-field Override: cx via Sum (additive), cy via Product (multiplicative)
    , check "Override <>"   (Coord 2 3 <> Coord 5 7 == Coord 7 21)
      -- positional [[..]]: field0 Sum (additive), field1 Product, field2 _ (kept, ++)
    , check "Override pos"  (Pos 2 3 [1] <> Pos 5 7 [2] == Pos 7 21 [1,2])
      -- [[Sum Int, _, _]]: only the first field changes (saturated/pinned)
    , check "Override pos1" (PosS 2 [1] [3] <> PosS 5 [2] [4] == PosS 7 [1,2] [3,4])
      -- multi-ctor --> paths via Eq: 'MA-->0-->Mod5 (field0 mod 5, field1 normal),
      -- 'MB-->Mod5 (MB's field mod 5)
    , check "Override -->"  (MA 1 7 == MA 6 7          -- field0 1≡6 (mod5), field1 7=7
                             && not (MA 1 7 == MA 1 8) -- field1 normal: 7≠8
                             && MB 1 == MB 6           -- MB field 1≡6 (mod5)
                             && not (MA 1 7 == MB 1))  -- different constructors
      -- Ord respects Override (viaSynth): field0 via Down reverses, field1 normal
    , check "Override Ord"  (compare (OrdOv 1 5) (OrdOv 2 5) == GT
                             && compare (OrdOv 5 1) (OrdOv 5 2) == LT)
      -- Show + Read respect Override: round-trip through a Sum-overridden field
    , check "Override S/R"  (read (show (SR 3 7)) == SR 3 7)
      -- Generic respects Override: Generically derives Semigroup over the
      -- overridden fields (field0 additive, field1 multiplicative)
    , check "Override Gen"  (CoordG 2 5 <> CoordG 3 4 == CoordG 5 20)
    , check "Override type" (TK 2 3 <> TK 5 7 == TK 7 10)     -- Int via Sum (both fields)
    , check "Override at"   (PK 2 3 <> PK 5 7 == PK 7 21)     -- at 0 via Sum, at 1 via Product
      -- Monoid respects Override: mempty = (Sum 0, Product 1), mappend additive/mult.
    , check "Override mempty"(mempty == MonOv 0 1)
    , check "Override <> M"  (MonOv 2 3 <> MonOv 5 7 == MonOv 7 21)
      -- Bounded respects Override: field0's bounds come from Hi (100..200)
    , check "Override Bnd"   ((minBound, maxBound) == (BdOv 100 False, BdOv 200 True))
      -- Enum / Ix: all-blank Override is the identity on a fieldless enum
    , check "Override Enum"  (map fromEnum [EnA ..] == [0,1,2] && toEnum 1 == EnB)
    , check "Override Ix"    (range (EnA, EnC) == [EnA, EnB, EnC] && index (EnA, EnC) EnB == 1)
      -- Functor respects Override1: Blah counts the fmap (0 -> 1) while mapping
    , check "Override Functor"(fmap (+ (10 :: Int)) (WithCount (0, 5)) == WithCount (1, 15))
      -- Contravariant respects Override1: Neg negates, so (5+1 > 6 = False) flips to True
    , check "Override Contra"(runCV (contramap (+ (1 :: Int)) (CV (Predicate (> 6)))) 5)
      -- Bifunctor respects Override2: each list field reshaped to RevL ⇒ reversed
    , check "Override Bifun" (bimap (+ (1 :: Int)) not (B2 [1, 2] [True, False])
                              == B2 [3, 2] [True, False])
      -- Eq1/Ord1/Show1 respect Override1: BL is blind/fixed
    , check "Override Eq1"   (liftEq (==) (Lc [1]) (Lc [9, 9 :: Int])
                              && liftCompare compare (Lc [1]) (Lc [9 :: Int]) == EQ)
    , check "Override Show1" (let s = liftShowsPrec showsPrec showList 0 (Lc [1, 2 :: Int]) ""
                              in "BL" `isInfixOf` s && not ('1' `elem` s))
      -- Bifoldable respects Override2: BL folds its list reversed
    , check "Override Bifold"(bifoldMap (: []) (: []) (Bc [1, 2] [3, 4 :: Int]) == [2, 1, 4, 3])
      -- Eq2 respects Override2: BL blind ⇒ all equal (same b-shape)
    , check "Override Eq2"   (liftEq2 (==) (==) (Bc [1] [3]) (Bc [9, 9] [8, 8 :: Int]))
      -- Generic1 honours Override1: Generically1 Applicative zips (ZipList), not cartesian
    , check "Override Gen1Ap"(runZg (Zg [(+ 1), (* 10)] <*> Zg [5, 6]) == ([6, 60] :: [Int]))
      -- Ord2 honours Override2: BL's blind liftCompare ⇒ EQ regardless of contents
    , check "Override Ord2"  (liftCompare2 compare compare (Bc [1] [3]) (Bc [9, 9] [8 :: Int]) == EQ
                              && liftCompare compare (Lc [1]) (Lc [9 :: Int]) == EQ)
      -- Show2 honours Override2: each field renders through BL ⇒ "BL", not the list
    , check "Override Show2" (let s = liftShowsPrec2 showsPrec showList showsPrec showList 0 (Bc [1] [2 :: Int]) ""
                              in "BL" `isInfixOf` s && not ('1' `elem` s))
      -- Read1 honours Override1: RL reverses on read, so the field comes back reversed
    , check "Override Read1" (case liftReadsPrec readsPrec readList 0 "Lr [1,2,3]" of
                                ((v, _) : _) -> v == Lr [3, 2, 1 :: Int] ; _ -> False)
      -- Read2 honours Override2: both fields parsed through RL ⇒ both reversed
    , check "Override Read2" (case liftReadsPrec2 readsPrec readList readsPrec readList 0 "Br [1,2] [3,4]" of
                                ((v, _) : _) -> v == Br [2, 1] [4, 3 :: Int] ; _ -> False)
      -- `_` (Keep) sugar lowered for Overriding1 too (identity reshape)
    , check "Override1 _ Keep" (fmap (+ (1 :: Int)) (Kp [1, 2, 3]) == Kp [2, 3, 4])
      -- field-keyed (name :=) Override1/Override2 — same surface as value Override
    , check "Override1 := name" (fmap (+ (1 :: Int)) (NK [1, 2, 3]) == NK [4, 3, 2])
    , check "Override2 := name" (bimap (+ (1 :: Int)) not (NK2 [1, 2] [True, False])
                                 == NK2 [3, 2] [True, False])
      -- Generic for a SUM type: from/to round-trips through the :+: structure
    , check "Generic sum rt"(all (\x -> to (from x) == x) [A, B 7, C 1 True, Rec 2 False])
      -- cross-validation: stock Generic Gen and plugin's Generic (Stock Gen)
      -- drive the same Generically algorithm to the same result
    , check "xval <>"       (let x = Gen [1] [2]; y = Gen [3] [4]
                             in viaGen x y == viaStockGen x y
                                && viaGen x y == Gen [1,3] [2,4])
    , check "xval mempty"   (memptyGen == memptyStockGen && memptyGen == Gen [] [])
      -- Rep (Stock T) ~R Rep T for a SUM type too
    , check "Rep ~R sum"    (all (\x -> repCrossRoundtripS x == x) [GA, GB 5, GC 2 True])
      -- M1 metadata layers carry the right names (datatype, constructor, record)
    , check "Meta datatype" (datatypeName (from (MetaR 1)) == "MetaR")
    , check "Meta con"      (conName (unM1 (from (MetaR 1))) == "MetaR")
    , check "Meta record"   (conIsRecord (unM1 (from (MetaR 1))))
      -- Generic1: from1/to1 round-trip (Par1 / Rec1 / Rec0, sum + product)
    , check "Generic1 rt"   (all (\x -> to1 (from1 x) == x)
                               [G1 7 (1::Int) [2,3] [[4],[5,6]], G1' 9, G1 0 5 [] []])
      -- Rep (Stock T) is *representationally* equal to stock's Rep T (the M1
      -- metadata layers are newtypes): coerce across them and round-trip.
    , check "Rep ~R Rep T"  (repCrossRoundtrip (Gen [1] [2]) == Gen [1] [2])
      -- infix constructors (fixity-aware Show/Read)
    , check "Show infix"    (show e1 == norm (show e1'))
    , check "Show infix ()" (show e2 == norm (show e2'))
    , check "Read infix rt" (read (show e1) == e1 && read (show e2) == e2)
      -- Functor via Stock1, against a stock DeriveFunctor twin
    , check "Functor fmap"  (fmap (+1) (Trio 1 2 [3,4]) == Trio 1 3 [4,5])
    , check "Functor vs twin"
        (show (fmap (*2) (Trio 1 2 [3])) == norm (show (fmap (*2) (Trio' 1 2 [3]))))
    , check "Functor <$"    ((9 <$ Trio 1 2 [3,4]) == Trio 1 9 [9,9])
      -- Foldable via Stock1, against the stock twin
      -- Applicative with a constant field (Const-style, via Monoid)
    , check "Applicative pure" (pure 'z' == (Ap [] 'z' :: Ap Char))
    , check "Applicative <*>"  ((Ap [1] (+1) <*> Ap [2] 10) == (Ap [1,2] 11 :: Ap Int))
      -- Override1: [] field → ZipList, so <*> zips (cartesian [] would give 4 elems)
    , check "Override1 zip <*>" (runZl (Zl [(+1),(*10)] <*> Zl [5,6]) == ([6,60] :: [Int]))
    , check "Override1 zip lA2" (runZl (liftA2 (+) (Zl [1,2,3]) (Zl [10,20,30])) == ([11,22,33] :: [Int]))
    , check "Override1 Foldable" (Data.Foldable.toList (Zl [4,5,6 :: Int]) == [4,5,6] && sum (Zl [1,2,3 :: Int]) == 6)
    , check "Foldable sum"  (sum (Trio 9 1 [2,3,4]) == sum (Trio' 9 1 [2,3,4]))
    , check "Foldable toL"  (Data.Foldable.toList (Trio 9 5 [6,7]) == [5,6,7])
    , check "Foldable len"  (length (Trio 9 1 [2,3]) == 3)
      -- Eq1 / Ord1 via Stock1, tied to the (verified) Eq / Ord on Trio:
      -- liftEq (==) must agree with (==); liftCompare compare with compare.
    , check "Eq1 vs Eq"     (let a = Trio 1 'x' "pq"; b = Trio 1 'x' "pq"; c = Trio 1 'y' "pr"
                             in liftEq (==) a b == (a == b)
                                && liftEq (==) a c == (a == c))
    , check "Eq1 param fn"  (-- a custom relation on the parameter is threaded to
                             -- both the bare field and the [a] field
                             liftEq (\_ _ -> True) (Trio 1 'x' "pq") (Trio 1 'z' "rs")
                             && not (liftEq (\_ _ -> False) (Trio 1 'x' "p") (Trio 1 'x' "p")))
    , check "Ord1 vs Ord"   (let a = Trio 1 'x' "pq"; c = Trio 1 'y' "pr"
                             in liftCompare compare a c == compare a c
                                && liftCompare compare a a == EQ)
      -- the quantified superclass: from (Eq1 f, Eq a) alone we must get Eq (f a),
      -- and from (Ord1 f, Ord a) we must get Ord (f a) — f is abstract in the
      -- helpers below, so this can only resolve through the synthesized super.
    , check "Eq1 superclass"  (eqViaEq1 (Trio 1 'x' "p") (Trio (1::Int) 'x' "p"))
    , check "Ord1 superclass" (cmpViaOrd1 (Trio 1 'x' "p") (Trio (1::Int) 'y' "p") == LT)
      -- Show1: showsPrec1 (which feeds liftShowsPrec the standard showsPrec/
      -- showList) must agree with the verified Show; a custom sp is threaded.
    , check "Show1 vs Show"  (showsPrec1 0 (Trio (1::Int) 'x' "pq") "" == show (Trio (1::Int) 'x' "pq"))
    , check "Show1 twin"     (showViaShow1 (Trio 9 (1::Int) [2,3]) == norm (show (Trio' 9 (1::Int) [2,3])))
    , check "Show1 param fn" (liftShowsPrec (\_ _ s -> 'Z':s) showList 0 (Trio (1::Int) 'x' "pq") ""
                              == "Trio 1 Z \"pq\"")
    , check "Show1 paren"    (showsPrec1 11 (Trio 9 (1::Int) [2]) "" == "(Trio 9 1 [2])")
    , check "Show1 record"   (showsPrec1 0 (Recd (1::Int) [2,3]) "" == show (Recd (1::Int) [2,3]))
      -- Read1: readsPrec1 (fed the standard readsPrec/readList) must invert
      -- Show; the quantified Read superclass gives Read (f a) from f abstract.
    , check "Read1 rt"       (let t = Trio (1::Int) (2::Int) [3,4]
                              in case readsPrec1 0 (show t) of ((x,_):_) -> x == t; _ -> False)
    , check "Read1 super"    (let t = Trio (9::Int) (1::Int) [2,3] in readViaRead1 (show t) == t)
    , check "Read1 record"   (let t = Recd (1::Int) [2,3] in readViaRead1 (show t) == t)
      -- Contravariant via Stock1 (newtype + function/constant/sub-Pred fields)
    , check "Contra pred"   (let p = contramap length (Pred even)
                             in runPred p "abcd" && not (runPred p "abc"))
    , check "Contra law id" (let p = contramap id (Pred (> (3::Int)))
                             in runPred p 4 && not (runPred p 3))
    , check "Contra mixed"  (let Sel f _ (Pred q) =
                                   contramap (length :: [a] -> Int)
                                             (Sel (> (10::Int)) 0 (Pred (> 5)))
                             in f "abcdefghijk" && not (f "abc")
                                && q "abcdef" && not (q "abc"))
    , check "Contra 2-arg"  (runFoo2 (contramap length (Foo2 (+))) "ab" "cde" == 5)
      -- variance through nested function arrows
    , check "Functor cps"   (runCps (fmap (*2) (Cps (\k -> k 5))) id == 10)
    , check "Contra cps3"   (forceCps3 (contramap (length :: String -> Int)
                                                  (Cps3 (const 0)) :: Cps3 String) == ())
      -- Category via Stock2: pointwise id and composition over the fields
    , check "Category id"   (runP2 (Cat.id :: P2 Int Int) 5 == (5 :: Int))
    , check "Category ."     (runP2 ((P2 Refl (+1) :: P2 Int Int) Cat.. P2 Refl (*2)) 5 == (11 :: Int))
      -- Category with a constant (Sum Int) field, handled via Monoid (no Basic)
    , check "Category const"
        (let (s, f) = runLC ((LC 1 (+1) :: LC Int Int) Cat.. LC 2 (*2)) in s == 3 && f 5 == 11)
      -- Category via Overriding2: each field reshaped into a Category, then
      -- derived pointwise (Sum adds, String appends, Kleisli composes monadically)
    , check "Category Ov id"
        (let (i, s, f) = runFoo (Cat.id :: Foo Int Int) in i == 0 && s == "" && f 9 == Just 9)
    , check "Category Ov ."
        (let (i, s, f) = runFoo ((Foo 3 "x" (\n -> Just (n+1)) :: Foo Int Int)
                                   Cat.. Foo 4 "y" (\n -> Just (n*2)))
         in i == 7 && s == "xy" && f 5 == Just 11)
      -- Bifunctor / Bifoldable via Stock2
    , check "Bifunctor bi"  (bimap (+(1::Int)) not (Bi 1 True) == Bi 2 False)
    , check "Bifunctor 1st" (first (+(1::Int)) (OnlyA 7 :: Bi Int Bool) == OnlyA 8)
    , check "Bifunctor 2nd" (second not (Bs True [False]) == (Bs False [True] :: Bi () Bool))
    , check "Bifunctor sup" (fmap not (Bs True [False,True]) == (Bs False [True,False] :: Bi () Bool))
      -- nested Either a b + [b] fields, via the n-ary self-application case
    , check "Bifunctor Either" (bimap (+(1::Int)) not (BiE (Left 5) [True])
                                  == (BiE (Left 6) [False] :: BiE Int Bool))
    , check "Bifunctor Either2" (bimap (+(1::Int)) not (BiE (Right True) [])
                                  == (BiE (Right False) [] :: BiE Int Bool))
      -- Eq2 / Ord2 via Stock2 (liftEq2 / liftCompare2 across both parameters)
    , check "Eq2"           (liftEq2 (==) (==) (Bi (1::Int) True) (Bi 1 True)
                             && not (liftEq2 (==) (==) (Bi (1::Int) True) (Bi 2 True)))
    , check "Show2"         (let p :: Bi Int Bool -> String
                                 p x = liftShowsPrec2 showsPrec showList showsPrec showList 0 x ""
                             in p (Bi 1 True) == show (Bi (1::Int) True)
                                && p (Bs True [False,True]) == show (Bs True [False,True] :: Bi Int Bool))
      -- Read2 via Stock2: read back what show produced (ties to verified Show+Eq)
    , check "Read2"         (let rd :: String -> Bi Int Bool
                                 rd s = case liftReadsPrec2 readsPrec readList readsPrec readList 0 s of
                                          [(v, "")] -> v
                                          _         -> error "Read2: no/ambiguous parse"
                             in rd (show (Bi (1::Int) True)) == Bi 1 True
                                && rd (show (Bs True [False,True] :: Bi Int Bool)) == Bs True [False,True])
    , check "Ord2"          (liftCompare2 compare compare (Bi (1::Int) True) (Bi 1 False)
                             == compare True False
                             && liftCompare2 compare compare (Bi (1::Int) (2::Int)) (OnlyA 1) == LT)
    , check "Bifoldable"    (bifoldMap (\a->[a]) (\b->[b]) (Bs 9 [1,2,3]) == [9,1,2,3::Int]
                             && bifoldMap (\a->[a]) (\b->[b]) (Bi 1 2) == [1,2::Int])
    -- TestEquality / TestCoercion on the singleton GADT
    , check "TestEq same"   (case testEquality TInt TInt of Just Refl -> True; _ -> False)
    , check "TestEq diff"   (case testEquality TInt TBool of Nothing -> True; _ -> False)
    , check "TestEq refl"   (case testEquality TBool TBool of
                               Just Refl -> True && (True :: Bool); _ -> False)
    , check "TestEq use"    (case testEquality TInt TInt of
                               Just r  -> castWith r (5 :: Int) == 5; Nothing -> False)
    , check "TestCo same"   (case testCoercion TChar TChar of
                               Just c  -> coerceWith c 'x' == 'x'; Nothing -> False)
    , check "TestCo diff"   (case testCoercion TInt TChar of Nothing -> True; _ -> False)
    -- same index, different constructors: compares the type, not the tag
    , check "TestEq sameIx" (case testEquality TZa TZb of Just Refl -> True; _ -> False)
    , check "TestEq sameIx'"(case testEquality TZb TZa of Just Refl -> True; _ -> False)
    , check "TestEq self"   (case testEquality TZb TZb of Just Refl -> True; _ -> False)
    , check "TestEq mixIx"  (case testEquality TZa TZc of Nothing   -> True; _ -> False)
    , check "TestEq useZ"   (case testEquality TZa TZb of
                               Just r  -> castWith r (7 :: Int) == 7; Nothing -> False)
    ]
  unless (and rs) exitFailure
  where
    xs = [C 1 True, A, B 1, Rec 9 True, A]
    e1  = Lit 1 :+: Lit 2 :*: Lit 3 ;  e1' = Lit' 1 :+. Lit' 2 :*. Lit' 3
    e2  = (Lit 1 :+: Lit 2) :*: Lit 3; e2' = (Lit' 1 :+. Lit' 2) :*. Lit' 3



