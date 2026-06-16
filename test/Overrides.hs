{-# OPTIONS_GHC -fplugin Stock -Wno-unused-imports #-}
{-# LANGUAGE DerivingVia, DataKinds, TypeOperators, KindSignatures #-}
{-# LANGUAGE FlexibleContexts, UndecidableInstances #-}
{-# LANGUAGE QuantifiedConstraints, StandaloneDeriving #-}

-- | Override-via-newtype coverage: derive each class through a /modifier
-- newtype/ (Sum, Product, Any, All, Min, Max, Down, Compose, ZipList, Op,
-- Basic, Kleisli, a Bounded-flip, …) and check at runtime that the reshape
-- actually took effect.  These exercise the @Override@\/@Overriding@ reshape
-- paths — historically the most bug-prone part of the plugin.
module Main (main) where

import Data.Kind (Type)
import Stock
import Control.Category (Category, id, (.))
import Control.Arrow (Kleisli(..))
import Control.Applicative (ZipList(..))
import Data.Functor.Classes (Eq1(..), Ord1(..), Show1(..), Read1)
import Text.Read (readMaybe)
import Control.Monad (unless)
import System.Exit (exitFailure)
import Data.Functor.Compose (Compose(..))
import Data.Functor.Const (Const(..))
import Data.Functor.Identity (Identity(..))
import GHC.Generics (Generically1(..))
import Data.Coerce (Coercible)
import Data.Monoid (Sum(..), Product(..), Any(..), All(..))
import Data.Semigroup (Min(..), Max(..))
import Data.Ord (Down(..))
import Prelude hiding (id, (.))

-- custom modifier newtypes
newtype Op cat a b = Op (cat b a)
instance Category cat => Category (Op cat) where { id = Op id; Op f . Op g = Op (g . f) }
newtype Basic m a b = Basic m
instance Monoid m => Category (Basic m) where { id = Basic mempty; Basic a . Basic b = Basic (a <> b) }
newtype Hi a = Hi a   -- flips a field's bounds
instance Bounded a => Bounded (Hi a) where { minBound = Hi maxBound; maxBound = Hi minBound }

-- ── Semigroup / Monoid through assorted monoid newtypes ──
data Acc = Acc Int Int Bool deriving (Eq, Show) via Stock Acc
  deriving (Semigroup, Monoid) via Overriding Acc '[ '[ Sum Int, Product Int, Any ] ]

data Mm = Mm Int Int deriving (Eq, Show) via Stock Mm
  deriving Semigroup via Overriding Mm '[ '[ Min, Max ] ]

data Flags = Flags Bool Bool deriving (Eq, Show) via Stock Flags
  deriving (Semigroup, Monoid) via Overriding Flags '[ '[ All, Any ] ]

-- ── Ord: reverse one field with Down ──
data OrdD = OrdD Int Int deriving (Eq, Show) via Stock OrdD
  deriving Ord via Stock (Override OrdD '[ '[ Down, _ ] ])

-- ── Bounded: flip one field's bounds with Hi ──
data Bd = Bd Bool Ordering deriving (Eq, Show) via Stock Bd
  deriving Bounded via Stock (Override Bd '[ '[ Hi, _ ] ])

-- ── Functor / Foldable / Applicative: reshape a nested [[a]] via Compose ──
data Nest a = Nest [[a]] a deriving Show via Stock (Nest a)
  deriving (Functor, Foldable, Applicative) via
    Overriding1 Nest '[ '[ (Compose [] [] :: Type -> Type), Keep ] ]

-- ── Applicative: zip semantics via ZipList ──
data Zp a = Zp [a] [a] deriving (Eq, Show) via Stock (Zp a)
  deriving (Functor, Applicative) via Overriding1 Zp '[ '[ ZipList, ZipList ] ]

-- ── Category: per-field modifiers (sparse At form): Basic + Op ──
data Trans a b = Trans { fwd :: a -> b, lbl :: String, bwd :: b -> a }
  deriving Category via Overriding2 Trans
    '[ Trans at 1 via Basic String, Trans at 2 via Op (->) ]

-- ── Category: monadic arrows via Kleisli ──
data Km a b = Km (a -> Maybe b)
  deriving Category via Overriding2 Km '[ '[ Kleisli Maybe ] ]

runKm :: Km a b -> a -> Maybe b
runKm (Km f) = f

-- ── "iterate through play": algebraic-identity substitutions on a field ──
-- Compose Identity = id : reshaping a  Maybe a  field via  Compose Identity Maybe
-- must behave exactly like leaving it alone.  Compose [] Maybe wraps it in a list.
data Wp a = Wp (Maybe a) a deriving (Eq, Show) via Stock (Wp a)
  deriving Functor via Stock1 Wp
data WpI a = WpI (Maybe a) a deriving (Eq, Show) via Stock (WpI a)
  deriving Functor via Overriding1 WpI '[ '[ Compose Identity Maybe, Keep ] ]
data WpL a = WpL [Maybe a] a deriving (Eq, Show) via Stock (WpL a)
  deriving Functor via Overriding1 WpL '[ '[ Compose [] Maybe, Keep ] ]

-- depth-3 nested Compose still reaches the bottom
data N3 a = N3 [[[a]]] a deriving (Eq, Show) via Stock (N3 a)
  deriving Functor via Overriding1 N3 '[ '[ Compose (Compose [] []) [], Keep ] ]

-- single-level polymorphic modifier (abstract f, g): derivation produces a context
data Dfg (f :: Type -> Type) (g :: Type -> Type) a = Dfg (f (g a)) a
deriving via Overriding1 (Dfg f g) '[ '[ Compose f g, Keep ] ]
  instance (Functor f, Functor g) => Functor (Dfg f g)

-- nested-abstract Compose: derives once each functor carries  Representational1 f
-- = (forall x y. Coercible x y => Coercible (f x) (f y)), which lets GHC coerce
-- under the abstract functor.  (The reshape validation is checked at the closed
-- type (), so its evidence stays well-scoped — see Stock.Functor.)
data Rt (f :: Type -> Type) (g :: Type -> Type) a = Rt (f (g (f (g a)))) a
deriving via Overriding1 (Rt f g) '[ '[ Compose f (Compose g (Compose f g)), Keep ] ]
  instance ( Functor f, Functor g
           , (forall x y. Coercible x y => Coercible (f x) (f y))
           , (forall x y. Coercible x y => Coercible (g x) (g y)) )
        => Functor (Rt f g)
deriving via Overriding1 (Rt f g) '[ '[ Compose f (Compose g (Compose f g)), Keep ] ]
  instance ( Foldable f, Foldable g
           , (forall x y. Coercible x y => Coercible (f x) (f y))
           , (forall x y. Coercible x y => Coercible (g x) (g y)) )
        => Foldable (Rt f g)

-- poly-kinded modifier: Const's 2nd arg is kind-polymorphic, so a constant field
-- reshaped via Const (Sum Int) used to be requested at a skolem kind ("No instance
-- for Functor (Const (Sum Int))").  The Const field gives the Int a Sum-monoid in
-- Applicative (pure = Sum 0, <*> = (+)); the [[a]] field zips via Compose.
data Cn a = Cn Int [[a]] deriving (Eq, Show) via Stock (Cn a)
  deriving (Functor, Foldable, Applicative) via
    Overriding1 Cn '[ Cn at 0 via Const (Sum Int), Cn at 1 via Compose [] [] ]

-- a Const override is honored by Eq1 too (Classes1 path), for one-level fields:
-- the constant Int field is compared via Const (Sum Int)'s Eq1 (ignores the param).
data Eqc a = Eqc Int [a] deriving (Show) via Stock (Eqc a)
deriving via Stock (Eqc a) instance Eq a => Eq (Eqc a)
deriving via Overriding1 Eqc '[ Eqc at 0 via Const (Sum Int), Eqc at 1 via Keep ]
  instance Eq1 Eqc

-- the SAME overrides routed through Generically1: the Override1 config must leak
-- into Rep1 (Overriding1 Gn cfg) uniformly — including the constant Int field —
-- so the generic Functor/Applicative sees the reshaped leaves.
data Gn a = Gn Int [[a]] deriving (Eq, Show) via Stock (Gn a)
  deriving (Functor, Applicative) via
    Generically1 (Overriding1 Gn '[ Gn at 0 via Const (Sum Int), Gn at 1 via Compose [] [] ])

-- nested lifted classes WITHOUT an override: Eq1/Ord1/Show1/Read1 now walk a
-- nested functor field ([[a]]) like Functor/Foldable, not one-level only.
data Nl a = Nl [[a]]
deriving via Stock (Nl a) instance Eq a   => Eq   (Nl a)
deriving via Stock (Nl a) instance Ord a  => Ord  (Nl a)
deriving via Stock (Nl a) instance Show a => Show (Nl a)
deriving via Stock (Nl a) instance Read a => Read (Nl a)
deriving via Stock1 Nl instance Eq1   Nl
deriving via Stock1 Nl instance Ord1  Nl
deriving via Stock1 Nl instance Show1 Nl
deriving via Stock1 Nl instance Read1 Nl

main :: IO ()
main = do
  let ck s b = if b then putStrLn ("ok   " ++ s)
                    else putStrLn ("FAIL " ++ s) >> exitFailure
  ck "Semigroup  Sum/Product/Any"  (Acc 1 2 False <> Acc 10 3 True == Acc 11 6 True)
  ck "Monoid     mempty"           (mempty == Acc 0 1 False)
  ck "Semigroup  Min/Max"          (Mm 3 5 <> Mm 1 9 == Mm 1 9)
  ck "Monoid     All/Any"          (mempty == Flags True False)
  ck "Semigroup  All/Any"          (Flags True True <> Flags True False == Flags True True)
  ck "Ord        Down field0"      (compare (OrdD 1 0) (OrdD 2 0) == GT)
  ck "Bounded    Hi flips field0"  (minBound == Bd True LT && maxBound == Bd False GT)
  ck "Functor    over [[a]]"       (case fmap (+1) (Nest [[1],[2,3]] 9) of Nest xs y -> xs == [[2],[3,4]] && y == 10)
  ck "Foldable   over [[a]]"       (sum (Nest [[1,2],[3]] 4) == 10)
  ck "Applicative pure (Compose)"  (case (pure 5 :: Nest Int) of Nest xs y -> xs == [[5]] && y == 5)
  ck "Applicative ZipList <*>"     (((,) <$> Zp [1,2] [10] <*> Zp [3,4] [20]) == Zp [(1,3),(2,4)] [(10,20)])
  let t1 = Trans (+1) "a" (subtract 1) :: Trans Int Int
      t2 = Trans (*2) "b" (`div` 2)    :: Trans Int Int
      t3 = t1 . t2
  ck "Category   fwd composes"     (fwd t3 3 == 7)
  ck "Category   Basic String <>"  (lbl t3 == "ab")
  let k1 = Km (\x -> if x > 0 then Just (x*2) else Nothing) :: Km Int Int
      k2 = Km (\x -> Just (x+1))                            :: Km Int Int
  ck "Category   Kleisli compose"  (runKm (k1 . k2) 3 == Just 8 && runKm (k1 . k2) (-5) == Nothing)
  -- Compose Identity = id : the override must be invariant w.r.t. plain Stock1
  ck "Compose Identity ≅ plain"    (case (fmap (+1) (Wp (Just 1) 9), fmap (+1) (WpI (Just 1) 9)) of
                                       (Wp a x, WpI b y) -> (a, x) == (b, y) && (a, x) == (Just 2, 10))
  ck "Compose [] T wraps field"    (case fmap (+1) (WpL [Just 1, Nothing] 9) of WpL a x -> a == [Just 2, Nothing] && x == 10)
  ck "depth-3 Compose reaches bot" (case fmap (+1) (N3 [[[1, 2]]] 9) of N3 a x -> a == [[[2, 3]]] && x == 10)
  ck "polymorphic Compose f g"     (case fmap (+1) (Dfg (Just [1, 2]) 9 :: Dfg Maybe [] Int) of Dfg a x -> a == Just [2, 3] && x == 10)
  ck "nested-abstract via Repr1"   (case fmap (+1) (Rt (Just [Just [1]]) 9 :: Rt Maybe [] Int) of Rt a x -> a == Just [Just [2]] && x == 10)
  ck "nested-abstract Foldable"    (sum (Rt (Just [Just [1], Just [2, 3]]) 100 :: Rt Maybe [] Int) == 106)
  ck "poly-kinded Const modifier"  ((pure 7 :: Cn Int) == Cn 0 [[7]])
  ck "Const (Sum Int) <*> adds"    (((+) <$> Cn 10 [[1]] <*> Cn 100 [[2]] :: Cn Int) == Cn 110 [[3]])
  ck "Generically1 override leaks" (fmap (+1) (Gn 5 [[1,2],[3]]) == Gn 5 [[2,3],[4]]
                                    && (pure 7 :: Gn Int) == Gn 0 [[7]]
                                    && ((+) <$> Gn 10 [[1]] <*> Gn 100 [[2]] :: Gn Int) == Gn 110 [[3]])
  ck "Foldable skips Const field"  (sum (Cn 99 [[1,2],[3]]) == 6)        -- Const contributes nothing
  ck "Eq1 honors Const override"   (liftEq (==) (Eqc 5 [1]) (Eqc 5 [1::Int])
                                    && not (liftEq (==) (Eqc 5 [1]) (Eqc 9 [1::Int])))
  ck "Eq1 nested [[a]] walk"       (liftEq (==) (Nl [[1,2],[3]]) (Nl [[1,2],[3::Int]])
                                    && not (liftEq (==) (Nl [[1]]) (Nl [[2::Int]])))
  ck "Ord1 nested [[a]] walk"      (liftCompare compare (Nl [[1],[2]]) (Nl [[1],[3::Int]]) == LT)
  ck "Show1 nested [[a]] walk"     (liftShowsPrec showsPrec showList 0 (Nl [[1,2::Int]]) "" == "Nl [[1,2]]")
  ck "Read1 nested [[a]] walk"     (show (readMaybe "Nl [[1,2],[3]]" :: Maybe (Nl Int)) == "Just (Nl [[1,2],[3]])")
