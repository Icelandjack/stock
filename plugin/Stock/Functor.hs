{-# LANGUAGE CPP #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DerivingVia #-}
{-# OPTIONS_GHC -Wno-x-partial -Wno-incomplete-uni-patterns -Wno-unused-imports #-}
-- | @Functor@ \/ @Contravariant@ and @Foldable@ synthesizers over @Stock1@ (the variance walk).
module Stock.Functor where
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
import Data.List (zipWith4)
import Data.IORef (IORef, newIORef, readIORef, modifyIORef')
import Stock.Internal

synthFunctor :: GenEnv -> Class -> CtLoc -> Type -> Type
             -> TcPluginM (Maybe (EvTerm, [Ct]))
synthFunctor = synthMap1 Cov

-- | Synthesize @Contravariant (Stock1 F)@ — the contravariant instance of
-- @synthMap1@.
synthContravariant :: GenEnv -> Class -> CtLoc -> Type -> Type
                   -> TcPluginM (Maybe (EvTerm, [Ct]))
synthContravariant = synthMap1 Con

-- | The shared engine for the two single-parameter map-like classes over
-- @Stock1 F@.  @fmap@ and @contramap@ differ only in: the order of the two type
-- variables in the method (@forall a b@ vs @forall a' a@), the direction of the
-- supplied function (@a -> b@ vs @a' -> a@), and which 'varMap' base case it
-- feeds — so both are this one definition.  The non-overridden method (@(\<$)@
-- resp. @(>$)@, both at class-method index 1) comes from the class default; the
-- field walk is the full variance recursion in 'varMap'.
synthMap1 :: Variance -> GenEnv -> Class -> CtLoc -> Type -> Type
          -> TcPluginM (Maybe (EvTerm, [Ct]))
synthMap1 dir gen cls loc wrappedTy f =
  case geStock1 gen of
    Just st1Tc
      -- peel an optional @Override1 cfg F@: @realF@ is the genuine constructor,
      -- @mMods@ the per-field functor modifiers (e.g. @[] -> ZipList@).
      | let (realF, mMods) = peelOverride1 gen f
      , Just fTc <- tyConAppTyCon_maybe realF -> do
      functorCls <- tcLookupClass functorClassName
      let isCov   = case dir of Cov -> True; Con -> False
          fixed   = tyConAppArgs realF
          dcons   = tyConDataCons fTc
          coAt t  = coDown1 gen st1Tc wrappedTy f realF t   -- Stock1 (Override1? F) t ~R F t
      svTv <- freshTyVar "a"                                 -- scrutinee param (input @f@ is at it)
      rvTv <- freshTyVar (if isCov then "b" else "a'")       -- result param
      let svTy = mkTyVarTy svTv ; rvTy = mkTyVarTy rvTv
          innerS = mkTyConApp fTc (fixed ++ [svTy])
          gTy    = if isCov then mkVisFunTyMany svTy rvTy     -- fmap:      a  -> b
                            else mkVisFunTyMany rvTy svTy     -- contramap: a' -> a
      gId  <- freshId gTy "g"
      sfId <- freshId (mkAppTy wrappedTy svTy) "sf"
      cb   <- freshId innerS "cb"

      -- the only per-direction knobs: where the bare parameter maps, and whether
      -- contravariant subfields (@Pred a@) are allowed.  The variance walk then
      -- handles constants, covariant functor fields, and arbitrary arrow nesting.
      let (covFwd, conFwd, mContra)
            | isCov     = (Just (Var gId), Nothing,          Nothing)
            | otherwise = (Nothing,        Just (Var gId),   Just cls)
          -- @i@/@rvFt@ let an @Override1@ modifier reshape this field's functor
          -- (@h a -> m a@), feeding @varMap@ the modifier type and bridging the
          -- field value with @realFt ~R m a@ coercions.
          mapField i x ftA rvFt = case override1Mod gen mMods i of
            Nothing -> do
              m <- varMap functorCls mContra loc svTv rvTy covFwd conFwd Cov ftA
              pure (fmap (\(e, ws) -> (App e (Var x), ws)) m)
            Just modf -> do
              let effFt = mkAppTy modf svTy                                     -- m a
                  coS   = mkStockCo (PluginProv "stock") Representational ftA  effFt
                  coR   = mkStockCo (PluginProv "stock") Representational rvFt (mkAppTy modf rvTy)
              -- validate the reshape: GHC must agree @field a ~R m a@, else the
              -- unchecked @coS@\/@coR@ axioms would be unsound (reject bad overrides).
              -- We check it at the CLOSED type @()@ rather than the method binder
              -- @svTv@: the reshape is parametric in the element, so this still
              -- rejects bad overrides, while keeping the (possibly dictionary-shaped,
              -- e.g. via @Representational1@) evidence free of the method-local
              -- @svTv@ — otherwise GHC binds that evidence at instance level, where
              -- @svTv@ is out of scope, and emits ill-scoped Core (a nested-abstract
              -- @Compose@ reshape did exactly this).
              vw <- newWanted loc (mkStockReprEq (substTyWith [svTv] [unitTy] ftA)
                                                 (mkAppTy modf unitTy))
              m <- varMap functorCls mContra loc svTv rvTy covFwd conFwd Cov effFt
              pure (fmap (\(e, ws) -> (Cast (App e (Cast (Var x) coS)) (mkSymCo coR), mkNonCanonical vw : ws)) m)
          binders = if isCov then [svTv, rvTv] else [rvTv, svTv]

      malts <- forM dcons \dc -> do
        let fts   = map scaledThing (dataConInstOrigArgTys dc (fixed ++ [svTy]))
            rvFts = map scaledThing (dataConInstOrigArgTys dc (fixed ++ [rvTy]))
        xs <- zipWithM (\n ft -> freshId ft ("x" ++ show n)) [0 :: Int ..] fts
        mfs <- sequence (zipWith4 mapField [0 :: Int ..] xs fts rvFts)
        case sequence mfs of
          Nothing    -> pure Nothing
          Just pairs ->
            let (vals, wss) = unzip pairs
                body = Cast (mkCoreConApps dc (map Type (fixed ++ [rvTy]) ++ vals))
                            (mkSymCo (coAt rvTy))            -- F rv -> Stock1 F rv
            in pure (Just (Alt (DataAlt dc) xs body, concat wss))

      case sequence malts of
        Nothing     -> pure Nothing
        Just altWss -> do
          let (alts, wss) = unzip altWss
              methodImpl = mkLams (binders ++ [gId, sfId])
                (destructInner fTc (fixed ++ [svTy]) (Cast (Var sfId) (coAt svTy))
                               cb (mkAppTy wrappedTy rvTy) alts)
          dmExtra <- defMethId cls 1                         -- (<$) / (>$)
          dict <- recClassDict cls wrappedTy \dvar ->
                    pure [ methodImpl, mkApps (Var dmExtra) [Type wrappedTy, Var dvar] ]
          pure (Just (EvExpr dict, concat wss))
    _ -> pure Nothing

-- | Synthesize @Foldable (Stock1 F)@.  @foldMap@ maps the parameter fields and
-- folds @H a@ fields with their own @foldMap@, combining contributions with
-- @(<>)@ (constant fields contribute nothing); all other @Foldable@ methods
-- come from the class defaults.  'Nothing' for unsupported field shapes.
synthFoldable :: GenEnv -> Class -> CtLoc -> Type -> Type
              -> TcPluginM (Maybe (EvTerm, [Ct]))
synthFoldable gen foldableCls loc wrappedTy f =
  case geStock1 gen of
    Just st1Tc
      | let (realF, mMods) = peelOverride1 gen f   -- @Override1@: reshape h-a fields
      , Just fTc <- tyConAppTyCon_maybe realF -> do
      monoidCls <- tcLookupClass monoidClassName
      let fixed      = tyConAppArgs realF
          dcons      = tyConDataCons fTc
          foldMapSel = classMethod "foldMap" foldableCls
          memptySel  = classMethod "mempty" monoidCls
          mappendSel = classMethod "mappend" monoidCls
          coAt t     = coDown1 gen st1Tc wrappedTy f realF t
      atv <- freshTyVar "a" ; mtv <- freshTyVar "m"
      let aTy = mkTyVarTy atv ; mTy = mkTyVarTy mtv
          innerA = mkTyConApp fTc (fixed ++ [aTy])
      dM  <- freshId (mkClassPred monoidCls [mTy]) "dM"
      gId <- freshId (mkVisFunTyMany aTy mTy) "g"
      tId <- freshId (mkAppTy wrappedTy aTy) "t"
      cb  <- freshId innerA "cb"
      let memptyE      = mkApps (Var memptySel) [Type mTy, Var dM]
          mappendE x y = mkApps (Var mappendSel) [Type mTy, Var dM, x, y]
          -- field contribution: Nothing = unsupported; Just Nothing = omitted
          -- foldMap :: forall m a. Monoid m => ...  (m is quantified first)
          foldMapOf h ev x = mkApps (Var foldMapSel)
                               [Type h, ev, Type mTy, Type aTy, Var dM, Var gId, x]
          -- GHC's @ft_*@ fold over a field's structure: a constant contributes
          -- nothing; the parameter contributes @g x@; a tuple folds every
          -- component and combines with @(<>)@; a covariant @H larg@ folds via
          -- @H@'s @foldMap@ (nested @[[a]]@ ⇒ @foldMap (foldMap g)@); a function
          -- field is rejected.  'Nothing' unsupported / @Just Nothing@ no
          -- contribution / @Just (Just (e,ws))@ contributes @e@.
          foldField ft xe
            | not (atv `elemVarSet` tyCoVarsOfType ft) = pure (Just Nothing)
            | ft `eqType` aTy                          = pure (Just (Just (App (Var gId) xe, [])))
            | Just _ <- splitFunTy_maybe ft            = pure Nothing
            | Just (tc, args) <- splitTyConApp_maybe ft
            , isTupleTyCon tc, length args >= 2 = do
                xs <- mapM (`freshId` "u") args
                rs <- zipWithM foldField args (map Var xs)
                case sequence rs of
                  Nothing  -> pure Nothing
                  Just mcs -> do
                    cb <- freshId ft "cb"
                    let (es, wss) = unzip (catMaybes mcs)
                        body = if null es then memptyE else foldr1 mappendE es
                    pure (Just (Just ( Case xe cb mTy
                           [Alt (DataAlt (tupleDataCon Boxed (length args))) xs body]
                           , concat wss )))
            | Just (h, larg) <- splitAppTy_maybe ft
            , not (atv `elemVarSet` tyCoVarsOfType h) = do
                y  <- freshId larg "y"
                mi <- foldField larg (Var y)
                case mi of
                  Just (Just (e, w)) -> do
                    ev <- newWanted loc (mkClassPred foldableCls [h])
                    pure (Just (Just ( mkApps (Var foldMapSel)
                           [Type h, ctEvExpr ev, Type mTy, Type larg, Var dM, Lam y e, xe]
                           , mkNonCanonical ev : w )))
                  _ -> pure Nothing
            | otherwise = pure Nothing
          contrib i x ftA = case override1Mod gen mMods i of
            -- Override1 reshapes the field's (one-level) functor @h a -> m a@.
            Just m  -> do ev <- newWanted loc (mkClassPred foldableCls [m])
                          -- validate at the closed type @()@ (see synthMap1) so the
                          -- evidence stays free of the method-local @atv@.
                          vw <- newWanted loc (mkStockReprEq (substTyWith [atv] [unitTy] ftA)
                                                             (mkAppTy m unitTy))
                          let co = mkStockCo (PluginProv "stock") Representational ftA (mkAppTy m aTy)
                          pure (Just (Just (foldMapOf m (ctEvExpr ev) (Cast (Var x) co), [mkNonCanonical ev, mkNonCanonical vw])))
            Nothing -> foldField ftA (Var x)
      malts <- forM dcons \dc -> do
        let ftsA = map scaledThing (dataConInstOrigArgTys dc (fixed ++ [aTy]))
        xs  <- zipWithM (\n ft -> freshId ft ("x" ++ show n)) [0 :: Int ..] ftsA
        mcs <- sequence (zipWith3 contrib [0 :: Int ..] xs ftsA)
        case sequence mcs of
          Nothing       -> pure Nothing
          Just contribs ->
            let (es, wss) = unzip (catMaybes contribs)
                body = if null es then memptyE else foldr1 mappendE es
            in pure (Just (Alt (DataAlt dc) xs body, concat wss))
      -- @foldr@ (so @toList@\/@foldr@ do not fall back to the @Endo@-based
      -- default, which drags the @Stock1@ coercion along): synthesized to match
      -- GHC's stock derivation byte-for-byte.  @foldr f z (Con .. xi ..)@ nests
      -- a contribution per field around @z@: a constant passes the accumulator
      -- through; the parameter is @f xi rest@; a covariant @H a@ field is
      -- @(\\b1 b2 -> foldr (elemFn) b2 b1) xi rest@ (GHC's flip shape), where
      -- @elemFn@ recurses for nested structure.  Skipped under @Override1@
      -- (which reshapes fields and is handled only by @foldMap@).
      let foldrSel = classMethod "foldr" foldableCls
      faTv <- freshTyVar "a" ; fbTv <- freshTyVar "b"
      let faTy = mkTyVarTy faTv ; fbTy = mkTyVarTy fbTv
      ffId <- freshId (mkVisFunTyMany faTy (mkVisFunTyMany fbTy fbTy)) "f"
      fzId <- freshId fbTy "z"
      ftId <- freshId (mkAppTy wrappedTy faTy) "t"
      fcb  <- freshId (mkTyConApp fTc (fixed ++ [faTy])) "cb"
      let -- element-combine function for values of type @t@ (leaves are @faTy@,
          -- folded by @ffId@): @t -> b -> b@.
          mkElemFn :: Type -> TcPluginM (Maybe (CoreExpr, [Ct]))
          mkElemFn t
            | t `eqType` faTy = pure (Just (Var ffId, []))
            | Just (h, larg) <- splitAppTy_maybe t
            , not (faTv `elemVarSet` tyCoVarsOfType h) = do
                mfn <- mkElemFn larg
                case mfn of
                  Nothing        -> pure Nothing
                  Just (efn, w0) -> do
                    ev  <- newWanted loc (mkClassPred foldableCls [h])
                    p   <- freshId t "p" ; acc <- freshId fbTy "acc"
                    let e = mkLams [p, acc] (mkApps (Var foldrSel)
                              [Type h, ctEvExpr ev, Type larg, Type fbTy, efn, Var acc, Var p])
                    pure (Just (e, mkNonCanonical ev : w0))
            | otherwise = pure Nothing
          -- one field's contribution wrapped around continuation @k :: b@.
          contribR :: Type -> Id -> CoreExpr -> TcPluginM (Maybe (CoreExpr, [Ct]))
          contribR ft x k
            | not (faTv `elemVarSet` tyCoVarsOfType ft) = pure (Just (k, []))
            | ft `eqType` faTy = pure (Just (mkApps (Var ffId) [Var x, k], []))
            | Just _ <- splitFunTy_maybe ft = pure Nothing
            | Just (tc, args) <- splitTyConApp_maybe ft
            , isTupleTyCon tc, length args >= 2 = do
                us  <- mapM (`freshId` "u") args
                cbt <- freshId ft "ct"
                mb  <- combineR (zip args us) k
                pure $ flip fmap mb \(body, w) ->
                  ( Case (Var x) cbt fbTy
                      [Alt (DataAlt (tupleDataCon Boxed (length args))) us body], w )
            | Just (h, larg) <- splitAppTy_maybe ft
            , not (faTv `elemVarSet` tyCoVarsOfType h) = do
                mfn <- mkElemFn larg
                case mfn of
                  Nothing        -> pure Nothing
                  Just (efn, w0) -> do
                    ev <- newWanted loc (mkClassPred foldableCls [h])
                    b1 <- freshId ft "b1" ; b2 <- freshId fbTy "b2"
                    let flipLam = mkLams [b1, b2] (mkApps (Var foldrSel)
                          [Type h, ctEvExpr ev, Type larg, Type fbTy, efn, Var b2, Var b1])
                    pure (Just (mkApps flipLam [Var x, k], mkNonCanonical ev : w0))
            | otherwise = pure Nothing
          -- nest contributions right-to-left around @z@ (= leftmost field outermost).
          combineR :: [(Type, Id)] -> CoreExpr -> TcPluginM (Maybe (CoreExpr, [Ct]))
          combineR []            k = pure (Just (k, []))
          combineR ((ft, x) : r) k = do
            mr <- combineR r k
            case mr of
              Nothing       -> pure Nothing
              Just (k', w') -> do mc <- contribR ft x k'
                                  pure (fmap (\(e, w) -> (e, w ++ w')) mc)
      mFoldrAlts <- if isJust mMods then pure Nothing else fmap sequence $ forM dcons \dc -> do
        let ftsA = map scaledThing (dataConInstOrigArgTys dc (fixed ++ [faTy]))
        xs <- zipWithM (\n ft -> freshId ft ("x" ++ show n)) [0 :: Int ..] ftsA
        mb <- combineR (zip ftsA xs) (Var fzId)
        pure (fmap (\(body, w) -> (Alt (DataAlt dc) xs body, w)) mb)
      case sequence malts of
        Nothing     -> pure Nothing
        Just altWss -> do
          let (alts, wss) = unzip altWss
              foldMapImpl = mkLams [mtv, atv, dM, gId, tId]   -- forall m a. Monoid m => ...
                (destructInner fTc (fixed ++ [aTy]) (Cast (Var tId) (coAt aTy))
                               cb mTy alts)
              idxOf nm = head [ i | (i, m) <- zip [0 :: Int ..] (classMethods foldableCls)
                                  , occNameString (occName m) == nm ]
              (foldrMethods, foldrWs) = case mFoldrAlts of
                Just altWs ->
                  let (fAlts, fWss) = unzip altWs
                      foldrImpl = mkLams [faTv, fbTv, ffId, fzId, ftId]
                        (destructInner fTc (fixed ++ [faTy]) (Cast (Var ftId) (coAt faTy))
                                       fcb fbTy fAlts)
                  in ([(idxOf "foldr", foldrImpl)], concat fWss)
                Nothing -> ([], [])
          dict <- recDictWith foldableCls wrappedTy []
                    ((idxOf "foldMap", foldMapImpl) : foldrMethods)
          pure (Just (EvExpr dict, concat wss ++ foldrWs))
    _ -> pure Nothing

-- | Classify a field of a two-parameter type against the last two parameters
-- @a@ (first) and @b@ (second).
