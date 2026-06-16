{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE InstanceSigs #-}
{-# OPTIONS_GHC -Wno-orphans #-}   -- the @DeriveStock(1)@ registrations are necessarily orphans

-- | A companion \"solver\" package teaching the @stock@ plugin to derive
-- @NFData@ (and its higher order variant @NFData1@) from @deepseq@, without
-- being a plugin itself.  It depends only on the SDK ("Stock.Derive" /
-- "Stock.Internal") + @deepseq@.
--
-- Downstream: @data T = … deriving NFData via Stock T@ (or @NFData1 via Stock1
-- T@), just depend on @stock-deepseq@; no extra @-fplugin@.
module Stock.NFData
  ( NFData(..)
  , NFData1(..)
  , NFData2(..)
  ) where

import GHC.Plugins
import GHC.Core.Class (Class, classSCTheta, classTyVars)
import GHC.Tc.Plugin (newWanted)
import GHC.Tc.Types.Constraint (ctEvExpr, mkNonCanonical)
import GHC.Core.Predicate (mkClassPred, classifyPredType, Pred(ClassPred, ForAllPred))
import GHC.Core.TyCo.Subst (substTy)
import GHC.Core.Multiplicity (scaledThing)
import Control.DeepSeq (NFData(..), NFData1(..), NFData2(..))
import Control.Monad (forM, zipWithM)
import Data.Maybe (listToMaybe, fromMaybe)
import GHC.Core.TyCo.Rep (UnivCoProvenance(PluginProv))
import Stock.Derive
import Stock.Internal
import Stock.Bifunctor (BiField(..), classifyBiField)

-- | Recover a base class from a lifted class's quantified superclass
-- @forall a. C a => C' (f a)@ (so @NFData2 -> NFData1 -> NFData@).
baseClassOf :: Class -> Maybe Class
baseClassOf c1 = listToMaybe
  [ c | sc <- classSCTheta c1
      , ForAllPred _ _ hd <- [classifyPredType sc]
      , ClassPred c _      <- [classifyPredType hd] ]

-- | @rnf@ dispatches on the constructor ('matchSOP') and chains each field's
-- @rnf@ with @seq@ ('cfoldlFields').
instance DeriveStock NFData where
  deriveStock :: Deriver
  deriveStock = Deriver \cls dt -> do
    let rnfSel = classMethod "rnf" cls                       -- rnf :: a -> ()
        unit   = Var (dataConWorkId unitDataCon)
        rnfOf ft d e = mkApps (Var rnfSel) [Type ft, d, e]   -- rnf @ft d e :: ()
    xId <- fresh (dtVia dt) "x"
    -- rnf x = case x of Cᵢ f.. -> rnf f0 `seq` rnf f1 `seq` … `seq` ()
    body <- matchSOP dt unitTy (Var xId) \_ con fields ->
      cfoldlFields cls
        (\acc ft d e -> do w <- fresh unitTy "w"
                           pure (Case (rnfOf ft d e) w unitTy [Alt DEFAULT [] acc]))
        unit con fields
    pure (classDict cls (dtVia dt) [mkLams [xId] body])

-- | @liftRnf g@ forces each field: the parameter via the supplied @g :: a ->
-- ()@, a constant via its own @rnf@, an @h a@ field via @liftRnf@ of @h@; all
-- chained with @seq@.
instance DeriveStock1 NFData1 where
  deriveStock1 :: Deriver1
  deriveStock1 = Deriver1 \nf1Cls loc wrappedTy f -> do
    mNf   <- lookupClassMaybe "Control.DeepSeq" "NFData"
    tcs   <- lookupOvTcs "Override1"
    let mOv1 = ovWrap tcs ; mKeep = ovKeep tcs
    -- @f@ may be @Override1 cfg realF@ (positional or field-keyed): peel it.
        (realF, mMods) = peelOverride1With tcs f
    case (tyConAppTyCon_maybe wrappedTy, tyConAppTyCon_maybe realF, mNf) of
      (Just st1Tc, Just fTc, Just nfCls) -> do
            let fixed      = tyConAppArgs realF
                dcons      = tyConDataCons fTc
                liftRnfSel = classMethod "liftRnf" nf1Cls
                rnfSel     = classMethod "rnf" nfCls
                unit       = Var (dataConWorkId unitDataCon)
                coAt t     = coDown1With mOv1 st1Tc wrappedTy f realF t
            atv <- freshTyVar "a"
            let aTy    = mkTyVarTy atv
                innerA = mkTyConApp fTc (fixed ++ [aTy])
            gId <- freshId (mkVisFunTyMany aTy unitTy) "g"
            tId <- freshId (mkAppTy wrappedTy aTy) "t"
            cb  <- freshId innerA "cb"
            -- one field's contribution (a @()@), or 'Nothing' if its shape is
            -- unsupported (contravariant / nested parameter).
            let contrib i x ftA = case classifyField atv aTy ftA of
                  Nothing       -> pure Nothing
                  Just FParam   -> pure (Just (App (Var gId) (Var x), []))
                  Just FConst   -> do ev <- newWanted loc (mkClassPred nfCls [ftA])
                                      pure (Just ( mkApps (Var rnfSel) [Type ftA, ctEvExpr ev, Var x]
                                                 , [mkNonCanonical ev] ))
                  -- under @Override1@, force the @h a@ field via the modifier @m@'s
                  -- @liftRnf@, coercing the field value @h a ~R m a@ first.
                  Just (FApp h) -> do let mMod = override1ModWith mKeep mMods i
                                          m    = fromMaybe h mMod
                                          xv   = case mMod of
                                                   Nothing -> Var x
                                                   Just _  -> Cast (Var x) (mkStockCo (PluginProv "stock")
                                                                Representational (mkAppTy h aTy) (mkAppTy m aTy))
                                      ev <- newWanted loc (mkClassPred nf1Cls [m])
                                      pure (Just ( mkApps (Var liftRnfSel)
                                                     [Type m, ctEvExpr ev, Type aTy, Var gId, xv]
                                                 , [mkNonCanonical ev] ))
                -- c0 `seq` c1 `seq` … `seq` ()
                seqChain []       = pure unit
                seqChain (c : cs) = do w    <- freshId unitTy "w"
                                       rest <- seqChain cs
                                       pure (Case c w unitTy [Alt DEFAULT [] rest])
            malts <- forM dcons \dc -> do
              let ftsA = fieldsAt fixed dc aTy
              xs  <- zipWithM (\n ft -> freshId ft ("x" ++ show n)) [0 :: Int ..] ftsA
              mcs <- sequence (zipWith3 contrib [0 :: Int ..] xs ftsA)
              case sequence mcs of
                Nothing -> pure Nothing
                Just cs -> do let (es, wss) = unzip cs
                              body <- seqChain es
                              pure (Just (Alt (DataAlt dc) xs body, concat wss))
            case sequence malts of
              Nothing     -> pure Nothing
              Just altWss -> do
                let (alts, wss) = unzip altWss
                    impl = mkLams [atv, gId, tId]
                             (destructInner fTc (fixed ++ [aTy]) (Cast (Var tId) (coAt aTy)) cb unitTy alts)
                -- NFData1's quantified superclass  forall a. NFData a => NFData (f a):
                -- since  rnf @(f a) = liftRnf (rnf @a),  it is just the method above
                -- instantiated with the given @NFData a@.
                bTv <- freshTyVar "b"
                let bTy = mkTyVarTy bTv
                dB <- freshId (mkClassPred nfCls [bTy]) "d"
                let rnfAtB  = mkApps impl [Type bTy, mkApps (Var rnfSel) [Type bTy, Var dB]]
                    superEv = mkLams [bTv, dB] (mkClassDict nfCls (mkAppTy wrappedTy bTy) [rnfAtB])
                pure (Just (classDict nf1Cls wrappedTy [superEv, impl], concat wss))
      _ -> pure Nothing

-- | @liftRnf2 gA gB@ forces each field: the first parameter via @gA@, the
-- second via @gB@, a constant via its own @rnf@, an @h a@\/@h b@ field via
-- @liftRnf@ of @h@; all chained with @seq@.  NFData2's superclass
-- @forall a. NFData a => NFData1 (p a)@ is requested as a wanted and discharged
-- via the @Stock2@-newtype passthrough from the user's own @NFData1 (P a)@.
instance DeriveStock2 NFData2 where
  deriveStock2 :: Deriver2
  deriveStock2 = Deriver2 \nf2Cls loc wrappedTy p -> do
    tcs   <- lookupOvTcs "Override2"
    let mOv2 = ovWrap tcs ; mKeep = ovKeep tcs
    -- @p@ may be @Override2 cfg realP@ (positional or field-keyed): peel it.
        (realP, mMods) = peelOverride2With tcs p
    case (tyConAppTyCon_maybe wrappedTy, tyConAppTyCon_maybe realP, baseClassOf nf2Cls) of
      (Just st2Tc, Just pTc, Just nf1Cls) -> case baseClassOf nf1Cls of
        Nothing    -> pure Nothing
        Just nfCls -> do
          let fixed      = tyConAppArgs realP
              dcons      = tyConDataCons pTc
              liftRnfSel = classMethod "liftRnf" nf1Cls
              rnfSel     = classMethod "rnf" nfCls
              unit       = Var (dataConWorkId unitDataCon)
              coAt t1 t2 = coDown2With mOv2 st2Tc wrappedTy p realP t1 t2
          atv <- freshTyVar "a" ; btv <- freshTyVar "b"
          let aTy = mkTyVarTy atv ; bTy = mkTyVarTy btv
              innerAB = mkTyConApp pTc (fixed ++ [aTy, bTy])
          gA  <- freshId (mkVisFunTyMany aTy unitTy) "gA"
          gB  <- freshId (mkVisFunTyMany bTy unitTy) "gB"
          tId <- freshId (mkAppTy (mkAppTy wrappedTy aTy) bTy) "t"
          cb  <- freshId innerAB "cb"
          let -- consume an @h pTy@ field via the (optional) modifier @m@'s liftRnf,
              -- coercing the field value @h pTy ~R m pTy@ under @Override2@.
              liftRnfOf h mMod g pTy x = do
                let m  = fromMaybe h mMod
                    xv = case mMod of
                           Nothing -> Var x
                           Just _  -> Cast (Var x) (mkStockCo (PluginProv "stock")
                                        Representational (mkAppTy h pTy) (mkAppTy m pTy))
                ev <- newWanted loc (mkClassPred nf1Cls [m])
                pure (Just ( mkApps (Var liftRnfSel) [Type m, ctEvExpr ev, Type pTy, Var g, xv]
                           , [mkNonCanonical ev] ))
              contrib i x ft = case classifyBiField atv btv aTy bTy ft of
                Nothing          -> pure Nothing
                Just BFA         -> pure (Just (App (Var gA) (Var x), []))
                Just BFB         -> pure (Just (App (Var gB) (Var x), []))
                Just BFConst     -> do ev <- newWanted loc (mkClassPred nfCls [ft])
                                       pure (Just ( mkApps (Var rnfSel) [Type ft, ctEvExpr ev, Var x]
                                                  , [mkNonCanonical ev] ))
                Just (BFFoldA h) -> liftRnfOf h (override1ModWith mKeep mMods i) gA aTy x
                Just (BFFoldB h) -> liftRnfOf h (override1ModWith mKeep mMods i) gB bTy x
              seqChain []       = pure unit
              seqChain (c : cs) = do w <- freshId unitTy "w"
                                     rest <- seqChain cs
                                     pure (Case c w unitTy [Alt DEFAULT [] rest])
          malts <- forM dcons \dc -> do
            let fts = map scaledThing (dataConInstOrigArgTys dc (fixed ++ [aTy, bTy]))
            xs  <- zipWithM (\n ft -> freshId ft ("x" ++ show n)) [0 :: Int ..] fts
            mcs <- sequence (zipWith3 contrib [0 :: Int ..] xs fts)
            case sequence mcs of
              Nothing       -> pure Nothing
              Just contribs -> do let (es, wss) = unzip contribs
                                  body <- seqChain es
                                  pure (Just (Alt (DataAlt dc) xs body, concat wss))
          case sequence malts of
            Nothing     -> pure Nothing
            Just altWss -> do
              let (alts, wss) = unzip altWss
                  impl = mkLams [atv, btv, gA, gB, tId]
                           (destructInner pTc (fixed ++ [aTy, bTy]) (Cast (Var tId) (coAt aTy bTy)) cb unitTy alts)
                  subst   = case classTyVars nf2Cls of
                              (tv : _) -> zipTvSubst [tv] [wrappedTy]
                              _        -> emptySubst
                  scPreds = map (substTy subst) (classSCTheta nf2Cls)
              scEvs <- forM scPreds (newWanted loc)
              pure (Just ( classDict nf2Cls wrappedTy (map ctEvExpr scEvs ++ [impl])
                         , map mkNonCanonical scEvs ++ concat wss ))
      _ -> pure Nothing
