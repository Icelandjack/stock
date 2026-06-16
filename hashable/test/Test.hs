{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -fplugin Stock #-}
module Main (main) where
import Stock (Stock(..), Stock1(..), Stock2(..))
import Stock.Hashable (Hashable(..), Hashable1(..), Hashable2(..))  -- classes + registers DeriveStock(1,2)
import Stock.Override (Override(..), Overriding1, Overriding2, Override1(..), Override2(..), Keep, type (:=))
import Data.Functor.Classes (Eq1(..), Eq2)

data T = T Int Bool deriving (Eq, Hashable) via Stock T

data G a = G Int a [a]
  deriving (Eq, Hashable)   via Stock (G a)
  deriving (Eq1, Hashable1) via Stock1 G

-- the full tower: Hashable2 P needs Eq2 P (built-in) and, via the quantified
-- superclass, Hashable1 (P a) (and so Eq1/Eq/Hashable down the chain).
data P a b = P a b [a]
  deriving (Eq, Hashable)     via Stock (P a b)
  deriving (Eq1, Hashable1)   via Stock1 (P a)
  deriving (Eq2, Hashable2)   via Stock2 P

lhws :: Hashable a => G a -> Int
lhws = liftHashWithSalt hashWithSalt 0

lhws2 :: (Hashable a, Hashable b) => P a b -> Int
lhws2 = liftHashWithSalt2 hashWithSalt hashWithSalt 0

-- An observable modifier: @Blind@ is a newtype over @[a]@ (so coercible to the
-- real field) whose 'Hashable1' ignores the elements.  Honoring Override is then
-- visible: lists of different contents hash equally.
-- @Blind@ is blind across the whole tower (Eq/Eq1/Hashable/Hashable1): deriving
-- @Hashable1@/@Hashable2@ via this override drags in the @Eq1@/@Eq2@ superclass
-- through the /same/ config, so the modifier must answer for those too.
newtype Blind a = Blind [a]
instance Eq        (Blind a) where _ == _                = True
instance Eq1       Blind     where liftEq _ _ _          = True
instance Hashable  (Blind a) where hashWithSalt s _      = s
instance Hashable1 Blind     where liftHashWithSalt _ s _ = s

-- Hashable1 via Override1: the @[a]@ field hashed through @Blind@ (content blind).
data HB a = HB [a]
  deriving (Eq, Hashable)   via Stock (HB a)
  deriving (Eq1, Hashable1) via Overriding1 HB '[ '[Blind] ]

-- Hashable2 via Override2: first parameter's @[a]@ hashed through @Blind@; @b@ kept.
data HB2 a b = HB2 [a] b
  deriving (Eq, Hashable)   via Stock (HB2 a b)
  deriving (Eq1, Hashable1) via Stock1 (HB2 a)
  deriving (Eq2, Hashable2) via Overriding2 HB2 '[ '[Blind, Keep] ]

hb :: Hashable a => HB a -> Int
hb = liftHashWithSalt hashWithSalt 0

hb2 :: (Hashable a, Hashable b) => HB2 a b -> Int
hb2 = liftHashWithSalt2 hashWithSalt hashWithSalt 0

-- value-level Hashable via Override: @Blind0@ (newtype over Int) hashes blind,
-- so field 0's contents do not affect the hash.
newtype Blind0 = Blind0 Int deriving Eq
instance Hashable Blind0 where hashWithSalt s _ = s
-- complex config (type-keyed): every @Int@ field hashed blind.
data HV = HV Int Bool deriving Eq
  deriving Hashable via Stock (Override HV '[ Int := Blind0 ])

main :: IO ()
main | hash (T 1 True) == hash (T 1 True)
     , hash (T 1 True) /= hash (T 2 True)
     , lhws (G 1 (2 :: Int) [3]) == lhws (G 1 (2 :: Int) [3])
     , lhws (G 1 (2 :: Int) [3]) /= lhws (G 1 (9 :: Int) [3])
     , lhws2 (P (1 :: Int) 'c' [2]) == lhws2 (P (1 :: Int) 'c' [2])
     , lhws2 (P (1 :: Int) 'c' [2]) /= lhws2 (P (1 :: Int) 'd' [2])
       -- Override1: @Blind@ ignores contents, so differing lists hash equally.
     , hb (HB [1, 2, 3 :: Int]) == hb (HB [9 :: Int])
       -- Override2: list blind, but the kept @b@ still distinguishes.
     , hb2 (HB2 [1, 2 :: Int] 'c') == hb2 (HB2 [7, 8, 9 :: Int] 'c')
     , hb2 (HB2 [1, 2 :: Int] 'c') /= hb2 (HB2 [1, 2 :: Int] 'd')
       -- value Override: HV's Int field hashed blind, so its contents don't matter.
     , hash (HV 1 True) == hash (HV 999 True)
     , hash (HV 1 True) /= hash (HV 1 False)
       = putStrLn "ok: Hashable + Hashable1 + Hashable2 (incl. Override + Override1/2) via stock-hashable"
     | otherwise = error "hashable mismatch"
