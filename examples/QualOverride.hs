{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -fplugin Stock -Wno-unused-top-binds #-}

-- | Regression: the @-fplugin Stock@ surface pass must qualify the markers it
-- generates (@:=@, @At@, @Keep@) the /same way @Override@ itself was imported/.
-- Here "Stock.Override" is imported __only qualified__ (as @O@), so an
-- unqualified @Keep@ or @:=@ in the lowered config would be out of scope.  The
-- modifiers themselves (@Sum@, @Product@) keep whatever scope the user gave them.
module QualOverride (qualCheck) where

import Stock (Stock(..))
import Stock.Override qualified as O
import Data.Monoid (Sum(..), Product(..))

-- entry surface: @via@ lowers to @O.:=@ (mirrors the @O.Override@ qualifier).
data A = A { ax :: Int, ay :: Int }
  deriving (Eq, Show) via Stock A
  deriving Semigroup  via Stock (O.Override A '[ ax via Sum, ay via Product ])

-- positional surface: @_@ lowers to @O.Keep@.  Field 0 (@Int@) via @Sum@; field
-- 1 (@[Int]@) kept at its own list 'Semigroup'.
data B = B Int [Int]
  deriving (Eq, Show) via Stock B
  deriving Semigroup  via Stock (O.Override B '[ [ Sum, _ ] ])

qualCheck :: [(String, Bool)]
qualCheck =
  [ ("qualified Override, via ⇒ O.:=", A 2 3 <> A 5 7 == A 7 21)
  , ("qualified Override, _ ⇒ O.Keep", B 1 [2] <> B 3 [4] == B 4 [2, 4])
  ]
