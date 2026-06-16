{-# LANGUAGE CPP #-}
{-# LANGUAGE BlockArguments #-}
-- | A deliberately /minimal, forward-safe/ 'Data.Type.Equality.TestEquality'
-- (and 'Data.Type.Coercion.TestCoercion') synthesizer.
--
-- It handles exactly the unambiguous "finite singleton" GADT: a one-parameter
-- type whose every constructor is nullary, has no existentials, and pins the
-- parameter to a /ground/ type:
--
-- > data T a where { TInt :: T Int; TBool :: T Bool }
--
-- For these the lawful behaviour is forced: @testEquality x y@ is @Just Refl@
-- exactly when the type /indices/ of @x@ and @y@ coincide (NOT when they are
-- the same constructor: two constructors pinning the same type are equal), and
-- @Nothing@ otherwise.  Because that is the only law-abiding implementation, it
-- can never disagree with a future, more general design, so it commits us to
-- nothing.  Anything outside the subset is refused.
module Stock.TestEquality (synthTestEquality, synthTestCoercion) where

import GHC.Plugins hiding (TcPlugin)
import GHC.Tc.Plugin (TcPluginM, unsafeTcPluginTcM)
import GHC.Tc.Types.Constraint (Ct)
#if MIN_VERSION_ghc(9,12,0)
import GHC.Tc.Types.CtLoc (CtLoc)
#else
import GHC.Tc.Types.Constraint (CtLoc)
#endif
import GHC.Tc.Types.Evidence (EvTerm(EvExpr))
import GHC.Core.Class (Class, classMethods)
import GHC.Core.TyCo.Compare (eqType)
import Stock.Internal

-- | A datacon's GADT equality refinements (no public accessor; via the sig).
dcEqSpec :: DataCon -> [EqSpec]
dcEqSpec dc = let (_, _, eqs, _, _, _) = dataConFullSig dc in eqs

-- | A constructor in the supported subset; returns its pinned ground index.
pinnedGround :: DataCon -> Maybe Type
pinnedGround dc = case dcEqSpec dc of
  [es] | null (dataConExTyCoVars dc)               -- no existentials
       , null (dataConOrigArgTys dc)               -- nullary (no value fields)
       , let ty = snd (eqSpecPair es)
       , isEmptyVarSet (tyCoVarsOfType ty)         -- ground (closed) index
       -> Just ty
  _    -> Nothing

synthTestEquality, synthTestCoercion
  :: GenEnv -> Class -> CtLoc -> Type -> Type -> TcPluginM (Maybe (EvTerm, [Ct]))
synthTestEquality = synthEqLike True
synthTestCoercion = synthEqLike False

-- | @useRefl = True@ ⇒ 'TestEquality' (@(:~:)@ \/ @Refl@); @False@ ⇒
-- 'TestCoercion' (@Coercion@).
synthEqLike :: Bool -> GenEnv -> Class -> CtLoc -> Type -> Type
            -> TcPluginM (Maybe (EvTerm, [Ct]))
synthEqLike useRefl gen cls _loc wrappedTy f =
  case (geStock1 gen, tyConAppTyCon_maybe f) of
    (Just st1Tc, Just fTc)
      | null (tyConAppArgs f)                       -- F is a bare one-param tycon
      , dcons@(dc0 : _) <- tyConDataCons fTc
      , Just pins <- traverse pinnedGround dcons
      , (es0 : _) <- dcEqSpec dc0
      -- the witness type (@(:~:)@ \/ @Coercion@) straight from the method's
      -- signature, so we never have to name a (re-exported) module.
      , (meth : _) <- classMethods cls
      , (witTc : _) <- [ tc | tc <- nonDetEltsUniqSet (tyConsOfType (varType meth))
                            , nameOccName (tyConName tc)
                                == mkTcOcc (if useRefl then ":~:" else "Coercion") ] -> do
          let witCon = tyConSingleDataCon witTc
              kK     = tyVarKind (fst (eqSpecPair es0))
              coAt   = coDown1 gen st1Tc wrappedTy f f
          aTv <- freshTyVarK kK "a"
          bTv <- freshTyVarK kK "b"
          xId <- freshId (mkAppTy wrappedTy (mkTyVarTy aTv)) "x"
          yId <- freshId (mkAppTy wrappedTy (mkTyVarTy bTv)) "y"
          wbX <- freshId (mkTyConApp fTc [mkTyVarTy aTv]) "wx"
          wbY <- freshId (mkTyConApp fTc [mkTyVarTy bTv]) "wy"
          let aTy = mkTyVarTy aTv ; bTy = mkTyVarTy bTv
              witOf x y = mkTyConApp witTc [kK, x, y]
              resTy     = mkTyConApp maybeTyCon [witOf aTy bTy]
              nothingE  = mkCoreConApps nothingDataCon [Type (witOf aTy bTy)]
              -- same index: cox : a~#t, coy : b~#t  ⇒  abCo : a~#b.
              --   Refl     :: forall k (a b). (b ~# a)     => a :~: b    (eqSpec)
              --   Coercion :: forall k (a b). Coercible a b => Coercion a b
              -- so we feed the proof directly; for Coercion we first box the
              -- representational coercion into a Coercible dictionary with the
              -- wired-in 'coercibleDataCon' (@MkCoercible :: (a ~R# b) ->
              -- Coercible a b@).  No Cast, no constraint solving.
              same cox coy =
                let abCo  = mkTransCo (mkCoVarCo cox) (mkSymCo (mkCoVarCo coy))
                    proof | useRefl   = Coercion (mkSymCo abCo)   -- b ~# a (nominal)
                          | otherwise = mkCoreConApps coercibleDataCon
                                          [Type kK, Type aTy, Type bTy
                                          , Coercion (mkSubCo abCo)]   -- a ~R# b boxed
                    wit = mkCoreConApps witCon [Type kK, Type aTy, Type bTy, proof]
                in mkCoreConApps justDataCon [Type (witOf aTy bTy), wit]
          -- testEquality compares the type /indices/, not constructor tags:
          -- two constructors pinning the same ground type ⇒ Just Refl.
          let innerAlts ti cox = mapM mkInner (zip dcons pins)
                where mkInner (dcj, tj) = do
                        coy <- freshCoVar (mkPrimEqPred bTy tj)
                        let rhs = if eqType ti tj then same cox coy else nothingE
                        pure (Alt (DataAlt dcj) [coy] rhs)
          outerAlts <- mapM
            (\(dci, ti) -> do
                cox <- freshCoVar (mkPrimEqPred aTy ti)
                ialts <- innerAlts ti cox
                let inner = Case (Cast (Var yId) (coAt bTy)) wbY resTy ialts
                pure (Alt (DataAlt dci) [cox] inner))
            (zip dcons pins)
          let impl = mkCoreLams [aTv, bTv, xId, yId] $
                       Case (Cast (Var xId) (coAt aTy)) wbX resTy outerAlts
              -- TestEquality/TestCoercion are poly-kinded (@class C (f :: k ->
              -- Type)@), so the dictionary takes the kind @k@ first.
              dict = mkCoreConApps (classDataCon cls) [Type kK, Type wrappedTy, impl]
          pure (Just (EvExpr dict, []))
    _ -> pure Nothing

freshCoVar :: Type -> TcPluginM CoVar
freshCoVar ty = do
  u <- unsafeTcPluginTcM getUniqueM
  pure (mkCoVar (mkSystemName u (mkVarOccFS (fsLit "co"))) ty)
