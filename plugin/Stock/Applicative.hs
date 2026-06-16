{-# LANGUAGE CPP #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-x-partial -Wno-incomplete-uni-patterns -Wno-unused-imports #-}

-- | Pointwise @Applicative@ via @Stock1@, for single-constructor (product)
-- types — a faster @Generically1@: @pure@ replicates into every field and
-- @(\<*\>)@ applies field-wise.  Each field must be the parameter (applied
-- directly), an @Applicative@ functor of it (delegating to that functor), or a
-- constant — which, Const-style (exactly as @Generically1@), is fine given a
-- @Monoid@: @pure@ fills it with @mempty@ and @(\<*\>)@\/@liftA2@ combine with
-- @(\<>)@.  (Any sum type is still rejected.)  The @Functor@ superclass
-- dictionary comes from 'synthFunctor'.
module Stock.Applicative where

import GHC.Plugins hiding (TcPlugin)
import GHC.Tc.Plugin
import GHC.Tc.Types.Constraint
#if MIN_VERSION_ghc(9,12,0)
import GHC.Tc.Types.CtLoc (CtLoc)
#else
import GHC.Tc.Types.Constraint (CtLoc)
#endif
import GHC.Tc.Types.Evidence
import GHC.Core.Class (Class)
import GHC.Core.Predicate (mkClassPred)
import GHC.Core.Multiplicity (scaledThing)
import GHC.Core.TyCo.Rep (UnivCoProvenance(PluginProv))
import GHC.Builtin.Names (functorClassName, monoidClassName)
import Control.Monad (forM, zipWithM)
import Stock.Derive (classMethod)
import Stock.Internal
import Stock.Functor (synthFunctor)

-- | How one field of the product is handled by @pure@\/@(\<*\>)@\/@liftA2@: it
-- /is/ the parameter; an @Applicative@ functor @m@ of it (with @m@'s dict, and a
-- @Just@ @h t ~R m t@ coercion builder when reshaped by an @Override1@, else
-- @Nothing@); or a constant of type @ft@ handled Const-style via its @Monoid@.
data FldSpec = FsParam
             | FsApp Type CoreExpr (Maybe (Type -> Coercion))
             | FsConst Type CoreExpr

-- | Coerce a field value /into/ the modifier functor (@h t ~R m t@); identity
-- when the field is not reshaped.
castInOv :: Maybe (Type -> Coercion) -> Type -> CoreExpr -> CoreExpr
castInOv Nothing       _ e = e
castInOv (Just coFn)   t e = Cast e (coFn t)

-- | Coerce a result /back/ from the modifier functor to the real field type.
castBackOv :: Maybe (Type -> Coercion) -> Type -> CoreExpr -> CoreExpr
castBackOv Nothing     _ e = e
castBackOv (Just coFn) t e = Cast e (mkSymCo (coFn t))

synthApplicative :: GenEnv -> Class -> CtLoc -> Type -> Type
                 -> TcPluginM (Maybe (EvTerm, [Ct]))
synthApplicative gen applicativeCls loc wrappedTy f =
  case geStock1 gen of
    Just st1Tc
      -- peel an optional @Override1 cfg F@ (functor reshape, e.g. @[] -> ZipList@)
      | let (realF, mMods) = peelOverride1 gen f
      , Just fTc <- tyConAppTyCon_maybe realF
      , [dc] <- tyConDataCons fTc -> do          -- products only: one constructor
          functorCls <- tcLookupClass functorClassName
          monoidCls  <- tcLookupClass monoidClassName
          let fixed     = tyConAppArgs realF
              pureSel   = classMethod "pure"    applicativeCls    -- index 0: pure
              apSel     = classMethod "<*>"     applicativeCls    -- index 1: (<*>)
              laSel     = classMethod "liftA2"  applicativeCls    -- index 2: liftA2
              memptySel = classMethod "mempty"  monoidCls
              mappendSel= classMethod "mappend" monoidCls
              coAt t  = coDown1 gen st1Tc wrappedTy f realF t   -- Stock1 (Override1? F) t ~R F t

          -- Classify each field once: parameter, an @Applicative@ functor of it,
          -- or a constant — which (Const-style, as @Generically1@ does) is fine
          -- given a @Monoid@: @pure@ uses @mempty@, @(\<*\>)@ uses @(\<>)@.
          ctv <- freshTyVar "p"
          let ctvTy  = mkTyVarTy ctv
              fldTys = map scaledThing (dataConInstOrigArgTys dc (fixed ++ [ctvTy]))
              kinds  = map (classifyField ctv ctvTy) fldTys

          -- @FsParam@ | @FsApp h dApplicative@ | @FsConst ft dMonoid@; an arrow or
          -- other unsupported shape still bails with 'Nothing'.
          specsW <- forM (zip3 [0 :: Int ..] kinds fldTys) \(i, k, ft) ->
            -- Consult the @Override1@ modifier FIRST, regardless of the field's
            -- raw shape: that lets a modifier reshape an otherwise-unsupported
            -- field (e.g. a nested @[[a]]@ via @Compose [] []@) into a one-level
            -- applicative @m a@ — exactly as Functor\/Foldable\/Traversable do.
            -- The @field t ~R m t@ coercion is threaded through pure\/\<*\>.
            case override1Mod gen mMods i of
              Just m  -> do ev <- newWanted loc (mkClassPred applicativeCls [m])
                            -- validate at the closed type @()@ (see Stock.Functor)
                            -- so the evidence stays free of the method-local @ctv@.
                            vw <- newWanted loc (mkStockReprEq (substTyWith [ctv] [unitTy] ft)
                                                               (mkAppTy m unitTy))
                            let coFn t = mkStockCo (PluginProv "stock") Representational
                                                   (substTyWith [ctv] [t] ft) (mkAppTy m t)
                            pure (Just (FsApp m (ctEvExpr ev) (Just coFn), [mkNonCanonical ev, mkNonCanonical vw]))
              Nothing -> case k of
                Just FParam   -> pure (Just (FsParam, []))
                Just (FApp h) -> do ev <- newWanted loc (mkClassPred applicativeCls [h])
                                    pure (Just (FsApp h (ctEvExpr ev) Nothing, [mkNonCanonical ev]))
                Just FConst   -> do ev <- newWanted loc (mkClassPred monoidCls [ft])
                                    pure (Just (FsConst ft (ctEvExpr ev), [mkNonCanonical ev]))
                _             -> pure Nothing

          case sequence specsW of
            Nothing  -> pure Nothing
            Just sw  -> do
              let fieldSpec = map fst sw
                  appWs     = concatMap snd sw

              -- pure :: forall a. a -> Stock1 F a
              aP  <- freshTyVar "a"
              let aPt = mkTyVarTy aP
              xId <- freshId aPt "x"
              let pureVal FsParam          = Var xId
                  pureVal (FsApp m d mco)  = castBackOv mco aPt (mkApps (Var pureSel) [Type m, d, Type aPt, Var xId])
                  pureVal (FsConst ft d)   = mkApps (Var memptySel) [Type ft, d]
                  pureImpl = mkLams [aP, xId] $
                    Cast (mkCoreConApps dc (map Type (fixed ++ [aPt]) ++ map pureVal fieldSpec))
                         (mkSymCo (coAt aPt))

              -- (<*>) :: forall a b. Stock1 F (a -> b) -> Stock1 F a -> Stock1 F b
              aS <- freshTyVar "a" ; bS <- freshTyVar "b"
              let aSt = mkTyVarTy aS ; bSt = mkTyVarTy bS ; fnTy = mkVisFunTyMany aSt bSt
              sffId <- freshId (mkAppTy wrappedTy fnTy) "sff"
              sfaId <- freshId (mkAppTy wrappedTy aSt)  "sfa"
              ffs <- zipWithM (\n t -> freshId t ("ff" ++ show n)) [0 :: Int ..]
                       (map scaledThing (dataConInstOrigArgTys dc (fixed ++ [fnTy])))
              xas <- zipWithM (\n t -> freshId t ("xa" ++ show n)) [0 :: Int ..]
                       (map scaledThing (dataConInstOrigArgTys dc (fixed ++ [aSt])))
              cbF <- freshId (mkTyConApp fTc (fixed ++ [fnTy])) "cbf"
              cbA <- freshId (mkTyConApp fTc (fixed ++ [aSt]))  "cba"
              let apVal FsParam         ff xa = App (Var ff) (Var xa)
                  apVal (FsApp m d mco) ff xa =
                    castBackOv mco bSt (mkApps (Var apSel)
                      [ Type m, d, Type aSt, Type bSt
                      , castInOv mco fnTy (Var ff), castInOv mco aSt (Var xa) ])
                  apVal (FsConst ft d) ff xa =        -- combine the constants with (<>)
                    mkApps (Var mappendSel) [Type ft, d, Var ff, Var xa]
                  apImpl = mkLams [aS, bS, sffId, sfaId] $
                    destructInner fTc (fixed ++ [fnTy]) (Cast (Var sffId) (coAt fnTy))
                                  cbF (mkAppTy wrappedTy bSt)
                      [ Alt (DataAlt dc) ffs $
                          destructInner fTc (fixed ++ [aSt]) (Cast (Var sfaId) (coAt aSt))
                                        cbA (mkAppTy wrappedTy bSt)
                            [ Alt (DataAlt dc) xas $
                                Cast (mkCoreConApps dc (map Type (fixed ++ [bSt])
                                                         ++ zipWith3 apVal fieldSpec ffs xas))
                                     (mkSymCo (coAt bSt)) ] ]

              -- liftA2 :: forall a b c. (a -> b -> c) -> Stock1 F a -> Stock1 F b -> Stock1 F c
              -- Given DIRECTLY (one structural pass) rather than via the class
              -- default @liftA2 g x = (g \<$\> x) \<*\> y@, which would @fmap@ then
              -- @\<*\>@ (two passes).  Each field: @g p q@ for the parameter, or
              -- @liftA2 \@h g p q@ for an Applicative-functor field.
              laA <- freshTyVar "a" ; laB <- freshTyVar "b" ; laC <- freshTyVar "c"
              let laAt = mkTyVarTy laA ; laBt = mkTyVarTy laB ; laCt = mkTyVarTy laC
                  gTy  = mkVisFunTyMany laAt (mkVisFunTyMany laBt laCt)
              gId  <- freshId gTy "g"
              ls1  <- freshId (mkAppTy wrappedTy laAt) "s1"
              ls2  <- freshId (mkAppTy wrappedTy laBt) "s2"
              ps   <- zipWithM (\n t -> freshId t ("p" ++ show n)) [0 :: Int ..]
                        (map scaledThing (dataConInstOrigArgTys dc (fixed ++ [laAt])))
              qs   <- zipWithM (\n t -> freshId t ("q" ++ show n)) [0 :: Int ..]
                        (map scaledThing (dataConInstOrigArgTys dc (fixed ++ [laBt])))
              cb1  <- freshId (mkTyConApp fTc (fixed ++ [laAt])) "cb1"
              cb2  <- freshId (mkTyConApp fTc (fixed ++ [laBt])) "cb2"
              let laVal FsParam         p q = mkApps (Var gId) [Var p, Var q]
                  laVal (FsApp m d mco) p q =
                    castBackOv mco laCt (mkApps (Var laSel)
                      [ Type m, d, Type laAt, Type laBt, Type laCt, Var gId
                      , castInOv mco laAt (Var p), castInOv mco laBt (Var q) ])
                  laVal (FsConst ft d) p q =          -- constants ignore g, combine with (<>)
                    mkApps (Var mappendSel) [Type ft, d, Var p, Var q]
                  liftA2Impl = mkLams [laA, laB, laC, gId, ls1, ls2] $
                    destructInner fTc (fixed ++ [laAt]) (Cast (Var ls1) (coAt laAt))
                                  cb1 (mkAppTy wrappedTy laCt)
                      [ Alt (DataAlt dc) ps $
                          destructInner fTc (fixed ++ [laBt]) (Cast (Var ls2) (coAt laBt))
                                        cb2 (mkAppTy wrappedTy laCt)
                            [ Alt (DataAlt dc) qs $
                                Cast (mkCoreConApps dc (map Type (fixed ++ [laCt])
                                                         ++ zipWith3 laVal fieldSpec ps qs))
                                     (mkSymCo (coAt laCt)) ] ]

              -- the @Functor@ superclass dictionary is the first dict-con field
              synthFunctor gen functorCls loc wrappedTy f >>= \case
                Nothing         -> pure Nothing
                Just (fEv, fWs) -> do
                  dict <- recDictWith applicativeCls wrappedTy [unwrapEv fEv]
                                      [(0, pureImpl), (1, apImpl), (2, liftA2Impl)]
                  pure (Just (EvExpr dict, fWs ++ appWs))
    _ -> pure Nothing
