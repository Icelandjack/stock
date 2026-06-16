{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin Stock #-}
-- | The same @Semigroup@ instance reached FOUR ways, on a 2-list product.
-- All must agree (same code); we time each.  The point of the project: the
-- @via Stock@ route is a /faster Generically/ — static synthesis, no @Rep@.
module Main (main) where

import qualified Stock as Stock
import GHC.Generics (Generic, Generically(..))
import System.CPUTime (getCPUTime)
import System.Mem (performGC)
import System.Environment (getArgs)
import Control.Exception (evaluate)
import Text.Printf (printf)
import System.IO (hSetBuffering, stdout, BufferMode(LineBuffering))

-- (1) our direct pointwise synthesis
data SVia = SVia [Int] [Int] deriving (Eq, Show)
  deriving Semigroup via Stock.Stock SVia
-- (2) our synthesized Generic, then base's Generically
data SGen = SGen [Int] [Int] deriving (Eq, Show)
  deriving Generic    via Stock.Stock SGen
  deriving Semigroup  via Generically SGen
-- (3) GHC stock Generic, then base's Generically
data SGenS = SGenS [Int] [Int] deriving (Eq, Show, Generic)
  deriving Semigroup via Generically SGenS
-- (4) hand-written
data SHand = SHand [Int] [Int] deriving (Eq, Show)
instance Semigroup SHand where SHand a b <> SHand x y = SHand (a <> x) (b <> y)

n :: Int
n = 200000

-- fold (<>) over n small products, return a checksum (total element count)
runVia, runGen, runGenS, runHand :: Int -> Int
runVia  d = csum (foldr1 (<>) [ SVia  [i+d] [i] | i <- [1..n] ]) where csum (SVia  a b) = length a + length b
runGen  d = csum (foldr1 (<>) [ SGen  [i+d] [i] | i <- [1..n] ]) where csum (SGen  a b) = length a + length b
runGenS d = csum (foldr1 (<>) [ SGenS [i+d] [i] | i <- [1..n] ]) where csum (SGenS a b) = length a + length b
runHand d = csum (foldr1 (<>) [ SHand [i+d] [i] | i <- [1..n] ]) where csum (SHand a b) = length a + length b

time :: String -> (Int -> Int) -> IO ()
time label work = do
  d0 <- length <$> getArgs
  let once i = do performGC; t0 <- getCPUTime; !r <- evaluate (work (d0+i)); t1 <- getCPUTime
                  pure (fromIntegral (t1-t0) / (1e12 :: Double), r)
  ss <- mapM once [0 .. 4]
  let r = case ss of ((_, x) : _) -> x ; [] -> 0
  printf "  %-22s  %.3f s   (checksum %d)\n" label (minimum (map fst ss)) r

-- each config's @(<>)@ on the same inputs, projected to a comparable shape
viaPair, genPair, genSPair, handPair :: ([Int], [Int])
viaPair  = case SVia  [1,3] [2] <> SVia  [4] [5,6] of SVia  a b -> (a, b)
genPair  = case SGen  [1,3] [2] <> SGen  [4] [5,6] of SGen  a b -> (a, b)
genSPair = case SGenS [1,3] [2] <> SGenS [4] [5,6] of SGenS a b -> (a, b)
handPair = case SHand [1,3] [2] <> SHand [4] [5,6] of SHand a b -> (a, b)

main :: IO ()
main = do
  hSetBuffering stdout LineBuffering
  putStrLn ("all four configs agree: " ++ show
    (all (== handPair) [viaPair, genPair, genSPair] && handPair == ([1,3,4], [2,5,6])))
  putStrLn ("Semigroup <> fold over " ++ show n ++ " products (best-of-5):")
  time "via Stock (direct)"          runVia
  time "via Generically (Stock)"     runGen
  time "via Generically (stock Gen)" runGenS
  time "hand-written"                runHand
