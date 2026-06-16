-- | Runs the should-fail harness ('negative/run-negative.sh') as a cabal test:
-- compiles invalid per-field overrides and asserts they are rejected (and that
-- valid controls still compile).  Exits with the script's status.
module Main (main) where

import System.Process (rawSystem)
import System.Exit (exitWith)

main :: IO ()
main = rawSystem "bash" ["negative/run-negative.sh"] >>= exitWith
