{-# OPTIONS_GHC -fplugin Stock #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}   -- Generic's @Rep@ equation is not decreasing
{-# OPTIONS_GHC -Wno-orphans -Wno-unused-imports -Wno-type-defaults #-}

-- | A showcase: derive as many instances as the plugin (and its companion
-- packages) can, one representative type per arity.  Everything here is
-- synthesised by @-fplugin Stock@ — no @Generic@, no hand-written boilerplate.
module Main (main) where

import Stock
import Stock.NFData     ()   -- companion deriver instances (discovered by the plugin)
import Stock.Hashable   ()
import Stock.Aeson      ()
import Stock.QuickCheck ()
import Stock.Profunctor ()

import Data.Ix (Ix)
import Data.List (sort)
import Data.Foldable (toList)
import Data.Bifunctor (Bifunctor(bimap))
import Data.Bifoldable (Bifoldable)
import Control.Category (Category)
import GHC.Generics (Generic, Generic1)
import Data.Functor.Classes (Eq1, Ord1, Show1, Read1, Eq2, Ord2, Show2, Read2)
import Data.Type.Equality (TestEquality(testEquality))
import Data.Type.Coercion (TestCoercion)
import Control.DeepSeq (NFData, NFData1, NFData2)
import Data.Hashable (Hashable)
import Data.Hashable.Lifted (Hashable1, Hashable2)
import Data.Aeson (ToJSON, FromJSON, ToJSON1, FromJSON1, ToJSON2, FromJSON2)
import Test.QuickCheck (Arbitrary, CoArbitrary)
import Data.Profunctor (Profunctor)
import Data.Monoid (Sum(..), Any(..))   -- constructors needed: the reshape is validated

-- ── enum (kind Type): 14 classes from one wrapper ──
data Grade = F | D | C | B | A
  deriving (Eq, Ord, Show, Read, Enum, Bounded, Ix, Generic,
            NFData, Hashable, ToJSON, FromJSON, Arbitrary, CoArbitrary)
    via Stock Grade

-- ── product (kind Type): + Semigroup/Monoid via per-field modifiers ──
data Config = Config Int Bool
  deriving (Eq, Ord, Show, Read, Bounded, Ix, Generic,
            NFData, Hashable, ToJSON, FromJSON, Arbitrary, CoArbitrary)
    via Stock Config
  deriving (Semigroup, Monoid)
    via Overriding Config '[ Int via Sum, Bool via Any ]

-- ── unary (kind Type -> Type) ──
-- the lifted classes carry quantified superclasses (e.g. @NFData1 f@ needs
-- @forall a. NFData a => NFData (f a)@), so the lower tier is derived too.
data Trio a = Trio Int a [a]
  deriving (Eq, Ord, Show, Read, NFData, Hashable, ToJSON, FromJSON) via Stock (Trio a)
  deriving (Functor, Foldable, Generic1,
            Eq1, Ord1, Show1, Read1,
            NFData1, Hashable1, ToJSON1, FromJSON1)
    via Stock1 Trio

-- Traversable can't be reached by a bare `deriving via` (its result @f (t b)@
-- puts the wrapper under an abstract applicative — nominal role); it's the
-- documented one-liner instead (still fully synthesised at @Stock1 Trio@).
instance Traversable Trio where
  traverse f = fmap unStock1 . traverse f . Stock1

-- a separate unary type for Applicative (every field is the parameter or an
-- applicative over it — no bare constant field).
data Pair a = Pair a [a]
  deriving (Functor, Applicative, Foldable) via Stock1 Pair
instance Traversable Pair where
  traverse f = fmap unStock1 . traverse f . Stock1

-- ── binary (kind Type -> Type -> Type) ──
-- full tower: each 2-class needs the matching 1-class (Eq2 ⊃ Eq1), which needs
-- the 0-class (Eq1 ⊃ Eq) — all derived.
data Two a b = Two a b [b]
  deriving (Eq, Ord, Show, Read, Generic, NFData, Hashable, ToJSON, FromJSON)
    via Stock (Two a b)
  deriving (Functor, Foldable, Eq1, Ord1, Show1, Read1,
            NFData1, Hashable1, ToJSON1, FromJSON1)
    via Stock1 (Two a)
  deriving (Bifunctor, Bifoldable, Eq2, Ord2, Show2, Read2,
            NFData2, Hashable2, ToJSON2, FromJSON2)
    via Stock2 Two

-- ── Category & Profunctor (a forward arrow) ──
data Fn a b = Fn (a -> b)
  deriving (Category, Profunctor) via Stock2 Fn

-- ── singleton GADT: TestEquality / TestCoercion ──
data Ty a where
  TInt  :: Ty Int
  TBool :: Ty Bool
deriving via Stock1 Ty instance TestEquality Ty
deriving via Stock1 Ty instance TestCoercion Ty

main :: IO ()
main = do
  print (sort [A, F, C])                       -- Ord / Enum
  print (Config 1 True <> Config 2 False)      -- Semigroup: Sum + Any  => Config 3 True
  print (sum (Trio 9 1 [2,3]))                 -- Foldable (constant Int skipped) => 6
  print (fmap (+1) (Trio 0 1 [2,3]))           -- Functor                => Trio 0 2 [3,4]
  print (bimap not (+1) (Two True 0 [1,2]))    -- Bifunctor              => Two False 1 [2,3]
  print (toList (Pair 1 [2,3]) :: [Int])       -- Foldable on Pair       => [1,2,3]
  putStrLn (case testEquality TInt TInt of Just _ -> "TInt =~= TInt"; Nothing -> "?")
