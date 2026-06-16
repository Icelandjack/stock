{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
-- record selectors below are illustrative and intentionally unused
{-# OPTIONS_GHC -fplugin Stock -Wno-unused-top-binds #-}

-- | Stock supplies the /structural/ instance; the standard @DerivingVia@
-- modifier newtypes then reshape it.  Each type below derives through
-- @Modifier (Stock … )@, so the modifier delegates to the instance the plugin
-- synthesizes:
--
--   * 'Down'      — structural 'Ord', reversed.
--   * 'Reverse'   — structural 'Foldable', folded back-to-front.
--   * 'Backwards' — the structural 'Applicative', effects sequenced right-to-left.
module Main (main) where

import Stock (Stock(..), Stock1(..))
import Stock.Override (Override(..), type (:=))
import QualOverride (qualCheck)
import Data.Ord (Down(..))
import Data.Monoid (Sum(..), Product(..))
import Data.Functor.Reverse (Reverse(..))
import Control.Applicative.Backwards (Backwards(..))
import Data.Foldable (toList)
import Control.Monad (unless)
import System.Exit (exitFailure)

-- @Ord@ as the reverse of the structural order: @Gold < Silver < Bronze@.
data Medal = Bronze | Silver | Gold
  deriving (Eq, Show) via Stock Medal
  deriving Ord        via Down (Stock Medal)

-- @Foldable@ that visits fields back-to-front.
data Triple a = Triple a a a
  deriving Show     via Stock (Triple a)
  deriving Foldable via Reverse (Stock1 Triple)

-- The structural (position-wise) @Applicative@, run backwards.
data Two a = Two a a
  deriving (Eq, Show)  via Stock (Two a)
  deriving Functor     via Stock1 Two
  deriving Applicative via Backwards (Stock1 Two)

-- Per-field @Override@ (lowered from the lowercase surface by the same
-- @-fplugin Stock@): combine @vx@ additively (@Sum@) and @vy@ multiplicatively
-- (@Product@) — a @Semigroup@ you cannot get from plain @Stock V@ without
-- rewriting @V@'s field types.
data V = V { vx :: Int, vy :: Int }
  deriving (Eq, Show) via Stock V
  deriving Semigroup  via Stock (Override V [ vx via Sum, vy via Product ])

main :: IO ()
main = do
  let checks =
        [ ("Down reverses Ord",     compare Bronze Gold == GT
                                    && maximum [Bronze, Silver, Gold] == Bronze)
        , ("Reverse reverses fold", toList (Triple 1 2 (3 :: Int)) == [3, 2, 1])
        , ("Backwards Applicative", (Two (+1) (+10) <*> Two 100 (200 :: Int)) == Two 101 210)
        , ("Override per-field <>", V 2 3 <> V 5 7 == V 7 21)
        ] ++ qualCheck
  mapM_ (\(name, ok) -> putStrLn ((if ok then "ok   " else "FAIL ") ++ name)) checks
  unless (all snd checks) exitFailure
