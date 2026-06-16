{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -fplugin Stock #-}
module Main (main) where

import Stock (Stock(..), Stock1(..), Stock2(..))
import Stock.QuickCheck                       -- classes + registers DeriveStock(1,2) Arbitrary
  ( Arbitrary(..), Arbitrary1(..), Arbitrary2(..), CoArbitrary(..) )
import Stock.Override (Override(..), Overriding, Overriding1, Overriding2, Override1(..), Override2(..), Keep, type (:=))
import Test.QuickCheck
  ( Gen, NonNegative(..), ASCIIString(..), generate, resize, vectorOf )
import Data.Char (isAscii)
import Control.Exception (evaluate)
import Control.Monad (unless)
import System.Exit (exitFailure)

-- a finite sum of products; CoArbitrary lets us generate functions FROM T
data T = A | B Int | C Bool Int
  deriving (Eq, Show)
  deriving (Arbitrary, CoArbitrary) via Stock T

-- a single-constructor product (no choice)
data P = P Int Bool [Int]
  deriving (Eq, Show)
  deriving Arbitrary via Stock P

-- RECURSIVE: must terminate thanks to the size bias (terminal Leaf at size 0)
-- and the size division across Node's two recursive fields.
data Tree = Leaf Int | Node Tree Tree
  deriving (Eq, Show)
  deriving Arbitrary via Stock Tree

size :: Tree -> Int
size (Leaf _)   = 1
size (Node l r) = 1 + size l + size r

-- Arbitrary1: parameter + constant + functor field
data F a = F Int a [a]
  deriving (Eq, Show)
  deriving Arbitrary1 via Stock1 F

-- Arbitrary1 over a RECURSIVE type constructor must still terminate
data L a = Nil | Cons a (L a)
  deriving (Eq, Show)
  deriving Arbitrary1 via Stock1 L

len :: L a -> Int
len Nil        = 0
len (Cons _ l) = 1 + len l

-- An observable modifier: @NE@ is a newtype over @[a]@ (so coercible to the real
-- field) whose 'Arbitrary1' never produces the empty list.  Honoring Override1 is
-- then visible: a generated @Bag@ is always non-empty, even at size 0.
newtype NE a = NE [a]
instance Arbitrary1 NE where
  liftArbitrary g = NE <$> ((:) <$> g <*> liftArbitrary g)

data Bag a = Bag [a]
  deriving Arbitrary1 via Overriding1 Bag '[ '[NE] ]

unBag :: Bag a -> [a]
unBag (Bag xs) = xs

-- value-level Arbitrary via Override using a stock QuickCheck modifier: the Int
-- field generates through @NonNegative@, so it is always >= 0.
data AV = AV Int deriving (Eq, Show)
  deriving Arbitrary via Overriding AV '[ '[NonNegative] ]
avInt :: AV -> Int
avInt (AV n) = n

-- value-level CoArbitrary via Override: @BlindCo@'s coarbitrary is the identity
-- (no perturbation), so a generated function @CVc -> Int@ /ignores/ the field —
-- it returns the same value for every input.  (Plain Int would perturb, giving
-- different outputs.)  Proof the override is honoured on the consumer side.
newtype BlindCo = BlindCo Int
instance CoArbitrary BlindCo where coarbitrary _ = id
data CVc = CVc Int
  deriving CoArbitrary via Overriding CVc '[ '[BlindCo] ]

-- field-keyed Override with the BARE-lowercase surface @nafn := …@ (not the
-- quoted @"nafn"@): the source plugin lowers @nafn@ to the field-name Symbol.
-- Generated @name@s are then all-ASCII.
data Person = Person { name :: String, age :: Int } deriving (Eq, Show)
  deriving Arbitrary via Overriding Person '[ name := ASCIIString ]
pname :: Person -> String
pname (Person n _) = n

-- Arbitrary2: a two-parameter type with every supported field shape — @a@, @b@,
-- @[a]@, @Maybe b@, and a constant @Int@.
data TP a b = TP a b [a] (Maybe b) Int
  deriving (Eq, Show)
  deriving Arbitrary2 via Stock2 TP

-- Arbitrary2 over a sum: stockChoose must visit both constructors.
data E2 a b = L2 a | R2 b [b]
  deriving (Eq, Show)
  deriving Arbitrary2 via Stock2 E2

-- Override2 + Arbitrary2: the @[b]@ field is reshaped via NE, so liftArbitrary2
-- generates it through NE's (non-empty) Arbitrary1 — every @[b]@ is non-empty.
data OB a b = OB a [b]
  deriving (Eq, Show)
  deriving Arbitrary2 via Overriding2 OB '[ '[ _, NE ] ]

sizeF :: F a -> Int
sizeF (F n _ xs) = n + length xs

tag :: T -> Int
tag A = 0; tag (B _) = 1; tag (C _ _) = 2

main :: IO ()
main = do
  ts <- generate (vectorOf 300 arbitrary) :: IO [T]
  ps <- generate (vectorOf 50  arbitrary) :: IO [P]
  -- generate trees at a healthy size; the bias must keep them finite
  trs <- generate (vectorOf 200 (resize 30 arbitrary)) :: IO [Tree]
  let ctorsSeen = length (foldr (\t a -> if tag t `elem` a then a else tag t : a) [] ts)
      pOk       = sum [ n + length xs | P n _ xs <- ps ] `seq` True
  totalNodes <- evaluate (sum (map size trs))   -- size traverses every tree fully (terminates!)
  -- CoArbitrary: generate a function T -> Int (needs CoArbitrary T) and apply it
  fn <- generate (arbitrary :: Gen (T -> Int))
  coOk <- evaluate ((fn A + fn (B 1) + fn (C True 2)) `seq` True)
  -- structural shrink: a single-field constructor shrinks exactly its field;
  -- a nullary constructor has nothing to shrink.
  let shrinkOk = shrink (B 5) == map B (shrink (5 :: Int)) && null (shrink A)
  -- Arbitrary1: liftArbitrary draws the parameter from the supplied Gen
  fs <- generate (vectorOf 50 (liftArbitrary arbitrary)) :: IO [F Int]
  ls <- generate (vectorOf 100 (resize 30 (liftArbitrary arbitrary))) :: IO [L Int]
  liftedNodes <- evaluate (sum (map sizeF fs) + sum (map len ls))   -- forces both (recursive L terminates)
  -- Override1 + Arbitrary1: the NE modifier forces every Bag non-empty, even at
  -- size 0 where a plain [a] field would routinely generate [].
  bags <- generate (mapM (\n -> resize n (liftArbitrary arbitrary)) [0 .. 30]) :: IO [Bag Int]
  let bagOk = all (not . null . unBag) bags
  -- value Override: AV's Int field generates via NonNegative, so always >= 0.
  avs <- generate (vectorOf 300 arbitrary) :: IO [AV]
  let avOk = all ((>= 0) . avInt) avs
  -- value Override (CoArbitrary): BlindCo perturbs nothing, so the function
  -- ignores its argument — same output for every input.
  fnc <- generate (arbitrary :: Gen (CVc -> Int))
  let coOvOk = all (\k -> fnc (CVc k) == fnc (CVc 0)) [1 .. 50]
  -- bare-lowercase field-keyed Override (`name := ASCIIString`): name is all-ASCII.
  people <- generate (vectorOf 200 arbitrary) :: IO [Person]
  let nameOk = all (all isAscii . pname) people
  -- Arbitrary2: distinct generators (pure 7 / pure True) prove that @a@ positions
  -- draw from gA and @b@ positions from gB (incl. the @[a]@ and @Maybe b@ fields).
  tps <- generate (vectorOf 100 (liftArbitrary2 (pure (7 :: Int)) (pure True))) :: IO [TP Int Bool]
  let tpOk = all (\(TP a b as mb _) -> a == 7 && b && all (== 7) as && all id mb) tps
  -- Arbitrary2 over a sum: both constructors appear, each field from the right gen.
  es <- generate (vectorOf 200 (liftArbitrary2 (pure (1 :: Int)) (pure 'z'))) :: IO [E2 Int Char]
  let e2Ok = any (\e -> case e of L2 _ -> True; _ -> False) es
          && any (\e -> case e of R2 _ _ -> True; _ -> False) es
          && all (\e -> case e of L2 a -> a == 1; R2 c zs -> c == 'z' && all (== 'z') zs) es
  -- Override2 + Arbitrary2: the NE modifier forces every @[b]@ field non-empty,
  -- even at size 0 where a plain @[b]@ would routinely generate @[]@.
  obs <- generate (mapM (\n -> resize n (liftArbitrary2 (pure ()) arbitrary)) [0 .. 30]) :: IO [OB () Int]
  let obOk = all (\(OB _ bs) -> not (null bs)) obs
  unless (ctorsSeen == 3 && pOk && coOk && shrinkOk && totalNodes >= 200 && liftedNodes >= 0
          && bagOk && avOk && coOvOk && nameOk && tpOk && e2Ok && obOk) exitFailure
  putStrLn ("ok: Arbitrary + CoArbitrary + shrink + Arbitrary1/Arbitrary2 (incl. Override/Override1/Override2) via stock-quickcheck (sized; "
            ++ show totalNodes ++ " tree nodes)")
