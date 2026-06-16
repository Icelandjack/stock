{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE BangPatterns #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | A like-for-like benchmark: the same datatype defined three ways — instances
-- synthesized by the plugin (@via Stock@), GHC's stock @deriving@, and
-- hand-written — running identical workloads.  The expectation is that all
-- three are within noise of each other (the plugin synthesizes the same
-- operations, so the optimized Core is essentially identical).
module Main (main) where

import qualified Stock as Stock
import Data.List (sort, foldl')
import System.CPUTime (getCPUTime)
import System.Mem (performGC)
import System.Environment (getArgs)
import Control.Exception (evaluate)
import Text.Printf (printf)
import System.IO (hSetBuffering, stdout, BufferMode(LineBuffering))

----------------------------------------------------------------------
-- A 3-field record, three ways (for Eq/Ord)
----------------------------------------------------------------------

data RV = RV Int Int Int deriving (Eq, Ord) via Stock.Stock RV      -- plugin
data RS = RS Int Int Int deriving (Eq, Ord)                         -- stock
data RH = RH Int Int Int                                            -- hand-written
instance Eq RH  where RH a b c == RH x y z = a == x && b == y && c == z
instance Ord RH where compare (RH a b c) (RH x y z) =
                        compare a x <> compare b y <> compare c z

----------------------------------------------------------------------
-- A parameterised type, three ways (for Functor)
----------------------------------------------------------------------

data FV a = FV a a a deriving Functor via Stock.Stock1 FV           -- plugin
data FS a = FS a a a deriving Functor                              -- stock
data FH a = FH a a a                                               -- hand-written
instance Functor FH where fmap f (FH a b c) = FH (f a) (f b) (f c)

----------------------------------------------------------------------

n :: Int
n = 100000

-- strict sum (avoid building a giant thunk)
ssum :: [Int] -> Int
ssum = foldl' (+) 0

-- Time a strict Int-producing workload, best-of-5 with a full GC before each
-- run.  @work@ must be a function of a dummy argument so each repetition
-- rebuilds its thunk from scratch (otherwise the result is shared and only the
-- first run does any work).  Best-of-N + per-run GC removes the ordering/GC
-- artefacts that otherwise inflate whichever workload happens to run first.
time :: String -> (Int -> Int) -> IO ()
time label work = do
  -- @d0@ is a genuinely runtime-unknown 0 (no args ⇒ length [] = 0); adding the
  -- repetition index gives each run a distinct argument, so GHC can neither
  -- constant-fold the workload nor share it across the 5 repetitions.
  d0 <- length <$> getArgs
  let once i = do performGC
                  t0 <- getCPUTime
                  !r <- evaluate (work (d0 + i))
                  t1 <- getCPUTime
                  pure (fromIntegral (t1 - t0) / (1e12 :: Double), r)
  samples <- mapM once [0 .. 4]
  let best = minimum (map fst samples)
      r    = case samples of (s:_) -> snd s; [] -> 0
  printf "  %-12s  %.3f s   (checksum %d)\n" label (best :: Double) r

main :: IO ()
main = do
  hSetBuffering stdout LineBuffering
  -- @d@ is always 0 at run time, but since it is a function argument GHC cannot
  -- treat the workload as a constant and share it — each repetition rebuilds.
  let seeds d = [ (i `mod` 97, i `mod` 31, i + d) | i <- [1 .. n] ]
  putStrLn ("Ord: sort " ++ show n ++ " 3-field records, then checksum")
  time "via Stock"   (\d -> ssum [ a + b + c | RV a b c <- sort [ RV x y z | (x,y,z) <- seeds d ] ])
  time "stock"       (\d -> ssum [ a + b + c | RS a b c <- sort [ RS x y z | (x,y,z) <- seeds d ] ])
  time "handwritten" (\d -> ssum [ a + b + c | RH a b c <- sort [ RH x y z | (x,y,z) <- seeds d ] ])
  let reps = 50 :: Int        -- compose fmap enough times to be measurable
      bump g = iterate (fmap (+1)) g !! reps
  putStrLn ("Functor: fmap (+1) x" ++ show reps ++ " over " ++ show n ++ " values, then checksum")
  time "via Stock"   (\d -> ssum [ a + b + c | FV a b c <- map bump [ FV x y z | (x,y,z) <- seeds d ] ])
  time "stock"       (\d -> ssum [ a + b + c | FS a b c <- map bump [ FS x y z | (x,y,z) <- seeds d ] ])
  time "handwritten" (\d -> ssum [ a + b + c | FH a b c <- map bump [ FH x y z | (x,y,z) <- seeds d ] ])
