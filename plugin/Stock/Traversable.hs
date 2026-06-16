{-# LANGUAGE CPP #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-x-partial -Wno-incomplete-uni-patterns -Wno-unused-imports #-}
-- | @Traversable (Stock1 F)@, synthesized directly (DeriveTraversable-style
-- Core), NOT by coercion.  @traverse@'s result @f (t b)@ places the wrapper
-- under an /abstract/ applicative @f@ (nominal role), so DerivingVia cannot
-- coerce @Traversable (Stock1 F)@ onto @F@ — but the instance itself is
-- perfectly definable and usable at the wrapper.  Put it on your own type with
-- the one-liner (which works with @Override1@ too):
--
-- > instance Traversable F where
-- >   traverse g = fmap unStock1 . traverse g . Stock1
module Stock.Traversable (synthTraversable) where

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
import GHC.Core.TyCo.Compare (eqType)
import GHC.Core.TyCo.Subst (substTyWith)
import GHC.Core.TyCo.Rep (UnivCoProvenance(PluginProv))
import GHC.Builtin.Names (applicativeClassName, functorClassName, foldableClassName)
import Control.Monad (forM, zipWithM)
import Data.List (zipWith4)
import Stock.Derive (classMethod)
import Stock.Internal
import Stock.Functor (synthFunctor, synthFoldable)

-- | Synthesize @Traversable (Stock1 F)@: per constructor, @pure mkCon \<*\> f1
-- \<*\> … \<*\> fn@ where the parameter field uses the supplied @g@, a constant
-- uses @pure@, and a sub-functor @H a@ field uses @traverse \@H g@ (an
-- @Override1@-reshaped functor traverses through the modifier, re-wrapped with
-- @pure coerce \<*\> _@ — never a cast under the abstract @f@).  @Functor@ and
-- @Foldable@ superclasses come from their own synthesizers.
synthTraversable :: GenEnv -> Class -> CtLoc -> Type -> Type
                 -> TcPluginM (Maybe (EvTerm, [Ct]))
synthTraversable gen travCls loc wrappedTy f =
  case geStock1 gen of
    Just st1Tc
      | let (realF, mMods) = peelOverride1 gen f
      , Just fTc <- tyConAppTyCon_maybe realF -> do
      appCls  <- tcLookupClass applicativeClassName
      funcCls <- tcLookupClass functorClassName
      foldCls <- tcLookupClass foldableClassName
      let fixed = tyConAppArgs realF
          dcons = tyConDataCons fTc
          traverseSel = classMethod "traverse" travCls
          pureSel     = classMethod "pure" appCls
          apSel       = classMethod "<*>"  appCls
          coAt t      = coDown1 gen st1Tc wrappedTy f realF t   -- Stock1 (Override1? F) t ~R F t
      fTv <- freshTyVarK (mkVisFunTyMany liftedTypeKind liftedTypeKind) "f"  -- f :: Type -> Type
      aTv <- freshTyVar "a" ; bTv <- freshTyVar "b"
      let fTy = mkTyVarTy fTv ; aTy = mkTyVarTy aTv ; bTy = mkTyVarTy bTv
          fOf t  = mkAppTy fTy t
          innerA = mkTyConApp fTc (fixed ++ [aTy])
          gTy    = mkVisFunTyMany aTy (fOf bTy)              -- a -> f b
          stbTy  = mkAppTy wrappedTy bTy                     -- Stock1 F b
      dApp <- freshId (mkClassPred appCls [fTy]) "dApp"
      gId  <- freshId gTy "g"
      xId  <- freshId (mkAppTy wrappedTy aTy) "x"
      cb   <- freshId innerA "cb"
      let pureE ty e        = mkApps (Var pureSel) [Type fTy, Var dApp, Type ty, e]
          apE tyA tyB ac fe = mkApps (Var apSel)   [Type fTy, Var dApp, Type tyA, Type tyB, ac, fe]
          subB t = substTyWith [aTv] [bTy] t                  -- t[a := b]
          -- GHC's @ft_*@ traversal of a field: a constant ⇒ @pure x@; the
          -- parameter ⇒ @g x@; a tuple ⇒ @pure (,..) \<*\> t1 \<*\> …@ (every
          -- component); a covariant @H larg@ ⇒ @traverse \@H@ (nested @[[a]]@ ⇒
          -- @traverse (traverse g)@); a function field rejected.  Result is
          -- @f (subB ft)@.
          traverseField ft xe
            | not (aTv `elemVarSet` tyCoVarsOfType ft) = pure (Just (pureE ft xe, []))
            | ft `eqType` aTy                          = pure (Just (App (Var gId) xe, []))
            | Just _ <- splitFunTy_maybe ft            = pure Nothing
            | Just (tc, args) <- splitTyConApp_maybe ft
            , isTupleTyCon tc, length args >= 2 = do
                xs <- mapM (`freshId` "u") args
                rs <- zipWithM traverseField args (map Var xs)
                case sequence rs of
                  Nothing    -> pure Nothing
                  Just travs -> do
                    let subArgs = map subB args
                        dc      = tupleDataCon Boxed (length args)
                        subTup  = subB ft
                        rs'     = scanr mkVisFunTyMany subTup subArgs
                    ys <- mapM (`freshId` "v") subArgs
                    cb <- freshId ft "cb"
                    let mkTup = mkLams ys (mkCoreConApps dc (map Type subArgs ++ map Var ys))
                        built = foldl (\ac (k, te, sa) -> apE sa (rs' !! (k + 1)) ac te)
                                      (pureE (head rs') mkTup)
                                      (zip3 [0 :: Int ..] (map fst travs) subArgs)
                    pure (Just ( Case xe cb (fOf subTup) [Alt (DataAlt dc) xs built]
                               , concatMap snd travs ))
            | Just (h, larg) <- splitAppTy_maybe ft
            , not (aTv `elemVarSet` tyCoVarsOfType h) =
                if larg `eqType` aTy
                  then do ev <- newWanted loc (mkClassPred travCls [h])
                          pure (Just ( mkApps (Var traverseSel)
                                 [Type h, ctEvExpr ev, Type fTy, Type aTy, Type bTy, Var dApp, Var gId, xe]
                                 , [mkNonCanonical ev] ))
                  else do y     <- freshId larg "y"
                          inner <- traverseField larg (Var y)
                          case inner of
                            Nothing     -> pure Nothing
                            Just (e, w) -> do
                              ev <- newWanted loc (mkClassPred travCls [h])
                              pure (Just ( mkApps (Var traverseSel)
                                     [Type h, ctEvExpr ev, Type fTy, Type larg, Type (subB larg)
                                     , Var dApp, Lam y e, xe]
                                     , mkNonCanonical ev : w ))
            | otherwise = pure Nothing
          -- one field's effect @f rvFt@; Override1 reshapes the (one-level)
          -- functor @h a -> m a@, otherwise the full structural walk.
          fieldOf i x ftA rvFt = case override1Mod gen mMods i of
            Just m -> do        -- Override1: traverse through @m@, re-wrap @m b -> h b@
              ev <- newWanted loc (mkClassPred travCls [m])
              -- validate at the closed type @()@ (see Stock.Functor) so the
              -- evidence stays free of the method-local @aTv@.
              vw <- newWanted loc (mkStockReprEq (substTyWith [aTv] [unitTy] ftA)
                                                 (mkAppTy m unitTy))
              let coS  = mkStockCo (PluginProv "stock") Representational ftA (mkAppTy m aTy)
                  coRb = mkStockCo (PluginProv "stock") Representational (mkAppTy m bTy) rvFt
                  trav = mkApps (Var traverseSel)
                           [Type m, ctEvExpr ev, Type fTy, Type aTy, Type bTy
                           , Var dApp, Var gId, Cast (Var x) coS]          -- :: f (m b)
              mb <- freshId (mkAppTy m bTy) "mb"
              let coerceFn = Lam mb (Cast (Var mb) coRb)                   -- m b -> h b
              pure (Just ( apE (mkAppTy m bTy) rvFt
                             (pureE (mkVisFunTyMany (mkAppTy m bTy) rvFt) coerceFn) trav
                         , [mkNonCanonical ev, mkNonCanonical vw] ))
            Nothing -> traverseField ftA (Var x)
      malts <- forM dcons \dc -> do
        let fts   = map scaledThing (dataConInstOrigArgTys dc (fixed ++ [aTy]))
            rvFts = map scaledThing (dataConInstOrigArgTys dc (fixed ++ [bTy]))
        xs   <- zipWithM (\n ft -> freshId ft ("x" ++ show n)) [0 :: Int ..] fts
        mfes <- sequence (zipWith4 fieldOf [0 :: Int ..] xs fts rvFts)
        case sequence mfes of
          Nothing  -> pure Nothing
          Just fes -> do
            let (fieldExprs, wss) = unzip fes
            ys <- zipWithM (\n ft -> freshId ft ("y" ++ show n)) [0 :: Int ..] rvFts
            let mkCon = mkLams ys (Cast (mkCoreConApps dc (map Type (fixed ++ [bTy]) ++ map Var ys))
                                        (mkSymCo (coAt bTy)))                -- rvFt.. -> Stock1 F b
                rs    = scanr mkVisFunTyMany stbTy rvFts                     -- R_0 … R_n(=Stock1 F b)
                body  = foldl (\ac (k, fe, rvFt) -> apE rvFt (rs !! (k + 1)) ac fe)
                              (pureE (head rs) mkCon)
                              (zip3 [0 :: Int ..] fieldExprs rvFts)
            pure (Just (Alt (DataAlt dc) xs body, concat wss))
      case sequence malts of
        Nothing     -> pure Nothing
        Just altWss -> do
          let (alts, wss) = unzip altWss
              traverseImpl = mkLams [fTv, aTv, bTv, dApp, gId, xId]
                (destructInner fTc (fixed ++ [aTy]) (Cast (Var xId) (coAt aTy)) cb (fOf stbTy) alts)
          mFunc <- synthFunctor  gen funcCls loc wrappedTy f
          mFold <- synthFoldable gen foldCls loc wrappedTy f
          case (mFunc, mFold) of
            (Just (fEv, fWs), Just (foEv, foWs)) -> do
              dict <- recDictWith travCls wrappedTy [unwrapEv fEv, unwrapEv foEv] [(0, traverseImpl)]
              pure (Just (EvExpr dict, fWs ++ foWs ++ concat wss))
            _ -> pure Nothing
    _ -> pure Nothing
