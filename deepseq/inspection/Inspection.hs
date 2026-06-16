{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -fplugin=Stock -fplugin=Test.Inspection.Plugin #-}

-- | Zero-cost proof for the @stock-deepseq@ companion: @NFData@\/@NFData1@\/
-- @NFData2@ are all /consumers/ (@rnf :: a -> ()@), so wrapping the argument
-- with the @Stock@\/@Stock1@\/@Stock2@ constructor lets the plugin's own unwrap
-- coercion cancel it, and 'hasNoType' certifies that no wrapper type survives
-- optimisation.  See @inspection/Inspection.hs@ in @stock@ for the full rationale.
module Main (main) where

import Stock
import Stock.NFData ()
import Control.DeepSeq (NFData, NFData1, NFData2, rnf, liftRnf, liftRnf2)
import Test.Inspection

data T = T Int Bool | U deriving NFData via Stock T

data F a = F Int a [a]
  deriving NFData  via Stock (F a)
  deriving NFData1 via Stock1 F

data P a b = P a b [a]
  deriving NFData  via Stock (P a b)
  deriving NFData1 via Stock1 (P a)
  deriving NFData2 via Stock2 P

-- force via @seq@ into a non-@()@ result so GHC can't eta-reduce @\t -> rnf
-- (Stock t)@ to a bare @rnf@ dictionary cast (the wrapped value is the trailing
-- arg here, unlike 'sLiftRnf' whose function arg blocks that).
sRnf :: T -> Int
sRnf t = rnf (Stock t) `seq` 0

sLiftRnf :: F Int -> ()
sLiftRnf x = liftRnf rnf (Stock1 x)

sLiftRnf2 :: P Int Int -> ()
sLiftRnf2 x = liftRnf2 rnf rnf (Stock2 x)

inspect $ 'sRnf      `hasNoType` ''Stock
inspect $ 'sLiftRnf  `hasNoType` ''Stock1
inspect $ 'sLiftRnf2 `hasNoType` ''Stock2

main :: IO ()
main = putStrLn "ok: NFData/NFData1/NFData2 erase the Stock wrapper (zero cost)"
