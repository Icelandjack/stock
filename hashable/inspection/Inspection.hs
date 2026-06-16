{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -fplugin=Stock -fplugin=Test.Inspection.Plugin #-}

-- | Zero-cost proof for the @stock-hashable@ companion: @Hashable@\/
-- @Hashable1@\/@Hashable2@ are /consumers/ (@hashWithSalt :: Int -> a -> Int@),
-- so wrapping the argument with the @Stock@\/@Stock1@\/@Stock2@ constructor lets
-- the plugin's unwrap coercion cancel it; 'hasNoType' certifies no wrapper type
-- survives.  See @inspection/Inspection.hs@ in @stock@ for the full rationale.
-- (The result is combined with the salt so GHC can't eta-reduce to a bare
-- dictionary cast — the wrapped value is otherwise the trailing argument.)
module Main (main) where

import Stock
import Stock.Hashable ()
import Data.Hashable (Hashable, hashWithSalt)
import Data.Hashable.Lifted (Hashable1, Hashable2, liftHashWithSalt, liftHashWithSalt2)
import Data.Functor.Classes (Eq1, Eq2)
import Test.Inspection

data T = T Int Bool deriving (Eq, Hashable) via Stock T

data G a = G Int a [a]
  deriving (Eq, Hashable)   via Stock (G a)
  deriving (Eq1, Hashable1) via Stock1 G

data P a b = P a b [a]
  deriving (Eq, Hashable)   via Stock (P a b)
  deriving (Eq1, Hashable1) via Stock1 (P a)
  deriving (Eq2, Hashable2) via Stock2 P

sHash :: Int -> T -> Int
sHash s t = s + hashWithSalt s (Stock t)

sLiftHash :: Int -> G Int -> Int
sLiftHash s x = s + liftHashWithSalt hashWithSalt s (Stock1 x)

sLiftHash2 :: Int -> P Int Int -> Int
sLiftHash2 s x = s + liftHashWithSalt2 hashWithSalt hashWithSalt s (Stock2 x)

inspect $ 'sHash      `hasNoType` ''Stock
inspect $ 'sLiftHash  `hasNoType` ''Stock1
inspect $ 'sLiftHash2 `hasNoType` ''Stock2

main :: IO ()
main = putStrLn "ok: Hashable/Hashable1/Hashable2 erase the Stock wrapper (zero cost)"
