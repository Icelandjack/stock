{-# LANGUAGE BlockArguments #-}
-- @head@/@last cons@ are guarded by the caller's
-- enum-or-single-constructor contract and the class always having its methods.
{-# OPTIONS_GHC -Wno-x-partial -Wno-unused-imports #-}

-- | @Bounded@ via the SOP-EDSL.  @minBound@\/@maxBound@ are values, so this is
-- pure 'injectSOP' (no @matchSOP@): an enumeration injects its first\/last
-- (nullary) constructor; a single-constructor product injects that constructor
-- with each field set to its own @minBound@\/@maxBound@ ('pureFields' +
-- 'field').  A clean demonstration that the SDK alone expresses a real
-- synthesizer — this module needs nothing from the plugin substrate.
module Stock.Bounded (boundedDeriver) where

import GHC.Plugins
import GHC.Core.Class (classMethods)
import Stock.Derive

-- | The caller guarantees the type is an enumeration or a single constructor
-- (GHC's @Bounded@ deriving has the same restriction).
boundedDeriver :: Deriver
boundedDeriver = Deriver \cls dt -> do
  let cons   = dtCons dt
      minSel = classMethod "minBound" cls
      maxSel = classMethod "maxBound" cls
      bound sel ft d = mkApps (Var sel) [Type ft, d]
  if all (null . conFields) cons
    then                                     -- enumeration: first / last constructor
      pure (classDict cls (dtVia dt) [ injectSOP dt (head cons) []
                                     , injectSOP dt (last cons) [] ])
    else do                                  -- single product: each field at its bound
      let con = productCon dt
      fds <- pureFields (\ft -> do d <- field cls ft; pure (ft, d)) con
      pure (classDict cls (dtVia dt)
              [ injectSOP dt con [ bound minSel ft d | (ft, d) <- fds ]
              , injectSOP dt con [ bound maxSel ft d | (ft, d) <- fds ] ])
