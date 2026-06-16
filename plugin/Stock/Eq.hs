{-# LANGUAGE CPP #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DerivingVia #-}
{-# OPTIONS_GHC -Wno-x-partial -Wno-incomplete-uni-patterns -Wno-unused-imports #-}
-- | @Eq@ synthesizer: two values are equal iff same constructor and all fields equal.
module Stock.Eq where
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

-- @(==)@ is the SOP eliminator twice over: dispatch @a@, then @b@; equal
-- constructors conjoin their per-field @(==)@s (each field's @Eq@ a wanted),
-- mismatched constructors are @False@.  @(/=)@ negates @(==)@.
eqDeriver :: Deriver
eqDeriver = Deriver \cls dt -> do
  let via    = dtVia dt
      eqSel  = classMethod "==" cls
      true_  = Var (dataConWorkId trueDataCon)
      false_ = Var (dataConWorkId falseDataCon)
      -- x0==y0 && x1==y1 && … , short-circuiting via nested case; the last
      -- field is the bare comparison (as @&&@ and stock @deriving@ produce).
      eqField (ft, x, y) = do d <- field cls ft   -- the continuation: get Eq ft
                              pure (mkApps (Var eqSel) [Type ft, d, x, y])
      conjEq []     = pure true_
      conjEq [t]    = eqField t
      conjEq (t : rest) = do
        e     <- eqField t
        restE <- conjEq rest
        scr   <- fresh boolTy "c"
        pure (Case e scr boolTy
                [ Alt (DataAlt falseDataCon) [] false_
                , Alt (DataAlt trueDataCon)  [] restE ])
  aId <- fresh via "a"
  bId <- fresh via "b"
  body <- matchSOP dt boolTy (Var aId) \i ci xs ->
          matchSOP dt boolTy (Var bId) \j _  ys ->
            if i == j then conjEq (zip3 (conFields ci) xs ys) else pure false_
  let eqImpl = mkLams [aId, bId] body
  na <- fresh via "a" ; nb <- fresh via "b" ; ns <- fresh boolTy "c"
  let neqImpl = mkLams [na, nb] $
        Case (mkApps eqImpl [Var na, Var nb]) ns boolTy
          [ Alt (DataAlt falseDataCon) [] true_
          , Alt (DataAlt trueDataCon)  [] false_ ]
  pure (classDict cls via [eqImpl, neqImpl])

-- | Pointwise @Semigroup@ for a single-constructor product: @C x.. \<\> C y.. =
-- C (x \<\> y)..@, each field combined with its own @(\<\>)@ (a wanted).  Same
-- result as @Generically@, synthesized statically (a \"faster Generically\").
-- @sconcat@\/@stimes@ come from the class defaults.
synthEq :: Class -> CtLoc -> Type -> Type -> Coercion -> [(DataCon, [Coercion])]
        -> TcPluginM (EvTerm, [Ct])
synthEq cls loc wrappedTy innerTy co dcons = do
  let true_   = Var (dataConWorkId trueDataCon)
      false_  = Var (dataConWorkId falseDataCon)
      scrut v = Cast (Var v) co               -- (v |> co) :: innerTy
      indexed = zip [0 :: Int ..] dcons
      realFts dc = fieldTysAt innerTy dc       -- field's real (bind) type

  aId <- freshId wrappedTy "a"
  bId <- freshId wrappedTy "b"

  -- case (a|>co) of { Ci x.. -> case (b|>co) of { Cj y.. -> body i j } }
  outer <- forM indexed \(i, (dci, cosI)) -> do
    xs <- zipWithM (\n ft -> freshId ft ("x" ++ show n)) [0 :: Int ..] (realFts dci)
    inner <- forM indexed \(j, (dcj, _)) -> do
      ys <- zipWithM (\n ft -> freshId ft ("y" ++ show n)) [0 :: Int ..] (realFts dcj)
      if i == j
        then do
          (body, ws) <- conj loc (zip3 xs ys cosI)
          pure (Alt (DataAlt dcj) ys body, ws)
        else pure (Alt (DataAlt dcj) ys false_, [])
    innerBndr <- freshId innerTy "cb"
    let (ialts, iws) = unzip inner
    pure (Alt (DataAlt dci) xs (Case (scrut bId) innerBndr boolTy ialts), concat iws)

  outerBndr <- freshId innerTy "ca"
  let (oalts, ows) = unzip outer
      eqImpl = mkLams [aId, bId] (Case (scrut aId) outerBndr boolTy oalts)

  -- (/=) = \a b -> case (==) a b of { False -> True; True -> False }
  na <- freshId wrappedTy "a"
  nb <- freshId wrappedTy "b"
  ns <- freshId boolTy "c"
  let neqImpl = mkLams [na, nb] $
        Case (mkApps eqImpl [Var na, Var nb]) ns boolTy
          [ Alt (DataAlt falseDataCon) [] true_
          , Alt (DataAlt trueDataCon)  [] false_ ]
      dict = mkClassDict cls wrappedTy [eqImpl, neqImpl]
  pure (EvExpr dict, concat ows)

-- | Conjoin per-field equalities — @and [x0 == y0, x1 == y1, …]@ — via 'andE'
-- (the short-circuiting @&&@ chain).  Each field's @Eq@ dictionary is a wanted.
-- Each triple is @(x, y, fieldCo)@; the field is compared at its modifier type
-- (@coercionRKind fieldCo@, the real type when 'Refl'), the bound values coerced.
conj :: CtLoc -> [(Id, Id, Coercion)] -> TcPluginM (CoreExpr, [Ct])
conj loc triples = do
  eqCls <- tcLookupClass eqClassName
  let eqSel = classMethod "==" eqCls              -- (==)
  evs <- mapM (\(_, _, fco) -> newWanted loc (mkClassPred eqCls [coercionRKind fco])) triples
  let cmp ((x, y, fco), ev) = mkApps (Var eqSel)
        [Type (coercionRKind fco), ctEvExpr ev, castInto (Var x) fco, castInto (Var y) fco]
  body <- andE (map cmp (zip triples evs))
  pure (body, map mkNonCanonical evs)

-- | Synthesize a full @Ord (Stock Inner)@ dictionary for any single-level
-- algebraic type: tag order between constructors, lexicographic within.  Every
-- comparison is derived from a single @compare@.  Returns the field @Ord@ and
-- @Eq@-superclass wanteds.
