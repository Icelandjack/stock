{-# LANGUAGE CPP #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DerivingVia #-}
{-# OPTIONS_GHC -Wno-x-partial -Wno-incomplete-uni-patterns -Wno-unused-imports #-}
-- | @Semigroup@ \/ @Monoid@ synthesizers: pointwise over a single-constructor product.
module Stock.Semigroup where
-- Most names below (data-con/type builders, coercion builders, occ-name
-- helpers, …) are re-exported by 'GHC.Plugins', so we only import explicitly
-- the ones it does not provide.
import GHC.Plugins hiding (TcPlugin)
import GHC.Tc.Plugin
import GHC.Tc.Types
import GHC.Tc.Types.Constraint
#if MIN_VERSION_ghc(9,12,0)
import GHC.Tc.Types.CtLoc (CtLoc)
#else
import GHC.Tc.Types.Constraint (CtLoc)
#endif
import GHC.Tc.Types.Evidence
import GHC.Tc.Utils.Monad (addErrTc)
import GHC.Tc.Errors.Types (mkTcRnUnknownMessage)
import GHC.Types.Error (mkPlainError, noHints)
import GHC.Core.Class (Class, className, classMethods, classOpItems, classTyCon)
import GHC.Core.Predicate (classifyPredType, Pred(ClassPred), mkClassPred)
import GHC.Builtin.Types.Prim (intPrimTy)
import GHC.Builtin.PrimOps (PrimOp(TagToEnumOp))
import GHC.Builtin.PrimOps.Ids (primOpId)
import GHC.Builtin.Names ( eqClassName, ordClassName, appendName
                         , enumClassName, mapName, numClassName
                         , enumFromToName, enumFromThenToName
                         , eqStringName
                         , genClassName, repTyConName, u1TyConName, k1TyConName
                         , prodTyConName, sumTyConName
                         , monoidClassName, foldableClassName, functorClassName
                         , semigroupClassName )
import Stock.Compat ( gHC_INTERNAL_SHOW, gHC_INTERNAL_READ
                    , gHC_INTERNAL_LIST, gHC_INTERNAL_GENERICS )
import GHC.Core.Reduction (mkReduction)
import GHC.Core.TyCo.Rep (UnivCoProvenance(PluginProv))
import GHC.Rename.Fixity (lookupFixityRn)
import GHC.Types.Fixity (Fixity(..), defaultFixity)
import GHC.Core.TyCo.Compare (eqType)
import GHC.Core.Multiplicity (scaledThing)
import GHC.Core.SimpleOpt (defaultSimpleOpts)
import GHC.Core.Unfold.Make (mkInlineUnfoldingWithArity)
import GHC.Core.InstEnv (classInstances, is_dfun, is_tys)
import GHC.Runtime.Loader (getValueSafely)
import Stock.Derive
import Data.Maybe (catMaybes, fromJust, isJust, fromMaybe)
import qualified Data.Monoid as Mon (Alt(..))  -- 'Alt' clashes with GHC.Core's case-alt 'Alt'
import Stock.Trans (MaybeT(..))
import Control.Monad (forM, zipWithM, unless, guard)
import Data.IORef (IORef, newIORef, readIORef, modifyIORef')
import Stock.Internal
-- @gmappend x y = productTypeTo (cliftA2_NP (Proxy \@Semigroup) (mapIII (<>))
--                                            (productTypeFrom x) (productTypeFrom y))@
semigroupDeriver :: Deriver
semigroupDeriver = Deriver \cls dt -> do
  let via       = dtVia dt
      sappSel   = classMethod "<>" cls                 -- (<>)
      mapSapp ft d x y = mkApps (Var sappSel) [Type ft, d, x, y]
  aId <- fresh via "a" ; bId <- fresh via "b"
  body <- fromProduct dt via (Var aId) \xs ->
          fromProduct dt via (Var bId) \ys ->
          toProduct dt <$> czipFields cls mapSapp (productCon dt) xs ys
  dict <- liftTc (recDictWith cls via [] [(0, mkLams [aId, bId] body)])
  pure (EvExpr dict)

-- | Pointwise @Monoid@ for a single-constructor product: @mempty = C mempty..@.
-- Its @Semigroup@ superclass is the 'semigroupDeriver' dictionary;
-- @mappend@\/@mconcat@ come from the class defaults.
--
-- @gmempty = productTypeTo (cpure_NP (Proxy \@Monoid) (I mempty))@
monoidDeriver :: Deriver
monoidDeriver = Deriver \cls dt -> do
  semigroupCls <- liftTc (tcLookupClass semigroupClassName)
  superEv      <- runDeriver semigroupDeriver semigroupCls dt
  let via       = dtVia dt
      memptySel = classMethod "mempty" cls                 -- mempty
      mapMempty ft d = mkApps (Var memptySel) [Type ft, d]
  memptyVal <- toProduct dt <$> cpureFields cls mapMempty (productCon dt)
  dict <- liftTc (recDictWith cls via [unwrapEv superEv] [(0, memptyVal)])
  pure (EvExpr dict)

