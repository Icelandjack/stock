{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE InstanceSigs #-}
{-# OPTIONS_GHC -Wno-orphans #-}     -- the @DeriveStock(1)@ registrations are necessarily orphans

-- | A companion \"solver\" package teaching the @stock@ plugin to derive
-- @Hashable@ (and its higher order variant @Hashable1@), without being a plugin
-- itself.  It depends only on the SDK ("Stock.Derive" \/ "Stock.Internal") +
-- @hashable@.
--
-- Downstream: @data T = … deriving (Eq, Hashable) via Stock T@ (or, for a type
-- constructor, @deriving (Eq1, Hashable1) via Stock1 T@ alongside the @Eq@ \/
-- @Hashable@ instances its superclasses need).
module Stock.Hashable
  ( hashableWitness
  , Hashable(..)
  , Hashable1(..)
  , Hashable2(..)
  ) where

import GHC.Plugins
import GHC.Builtin.Names (eqClassName)
import GHC.Core.Class (Class, classSCTheta, classTyVars)
import GHC.Tc.Plugin (TcPluginM, tcLookupClass, newWanted)
import GHC.Tc.Types.Constraint (ctEvExpr, mkNonCanonical)
import GHC.Core.Predicate (mkClassPred, classifyPredType, Pred(ClassPred, ForAllPred))
import GHC.Core.TyCo.Subst (substTy)
import GHC.Core.Multiplicity (scaledThing)
import Control.Monad (forM, zipWithM)
import Data.Maybe (listToMaybe, fromMaybe)
import GHC.Core.TyCo.Rep (UnivCoProvenance(PluginProv))
import Data.Hashable (Hashable(..))
import Data.Hashable.Lifted (Hashable1(..), Hashable2(..))
import Stock.Derive
import Stock.Internal
import Stock.Bifunctor (BiField(..), classifyBiField)

-- | A witness whose constraints name the three base classes.  The plugin reads
-- them straight off this value's type, so the deriver can recover @Hashable@ \/
-- @Hashable1@ on @hashable < 1.5@ (where they are not reachable as quantified
-- superclasses, and the defining module @Data.Hashable.Class@ is hidden) —
-- version-independently, without any module-name lookup.
hashableWitness :: (Hashable a, Hashable1 f, Hashable2 g) => (a, f x, g y z) -> ()
hashableWitness _ = ()

-- | @hashWithSalt@ dispatches on the constructor ('matchSOP', mixing the tag in
-- for sums), folds each field's @hashWithSalt@ through the salt ('cfoldlFields'),
-- and 'classDictWith' fills @hash@ from its default and supplies the @Eq@
-- superclass (also derived @via Stock@).
instance DeriveStock Hashable where
  deriveStock :: Deriver
  deriveStock = Deriver \cls dt -> do
    let via    = dtVia dt
        hwsSel = classMethod "hashWithSalt" cls                -- hashWithSalt :: Int -> a -> Int
        nCons  = length (dtCons dt)
        hws ft d salt e = mkApps (Var hwsSel) [Type ft, d, salt, e]   -- hashWithSalt @ft d salt e
    eqCls   <- liftTc (tcLookupClass eqClassName)
    eqDict  <- field eqCls via                                 -- Eq superclass (also via Stock)
    intHash <- field cls intTy                                 -- Hashable Int (for the tag)
    saltId  <- fresh intTy "salt"
    xId     <- fresh via "x"
    body <- matchSOP dt intTy (Var xId) \i con fields -> do
      let s0 | nCons > 1 = hws intTy intHash (Var saltId) (mkUncheckedIntExpr (fromIntegral i))
             | otherwise = Var saltId
      case fields of
        [] -> do d <- field cls unitTy
                 pure (hws unitTy d s0 (Var (dataConWorkId unitDataCon)))
        _  -> cfoldlFields cls (\salt ft d e -> pure (hws ft d salt e)) s0 con fields
    classDictWith cls via [eqDict] [(0, mkLams [saltId, xId] body)]

-- | @liftHashWithSalt g@ threads the salt through the fields: the parameter via
-- the supplied @g :: Int -> a -> Int@, a constant via its own @hashWithSalt@, an
-- @h a@ field via @liftHashWithSalt@ of @h@; sums mix in the constructor tag.
-- @Hashable1@'s superclasses (@Eq1 f@ and @forall a. Hashable a => Hashable (f
-- a)@) are requested as wanteds and discharged by the plugin (the @Eq1@ built-in,
-- and the @Stock1@-newtype passthrough from the user's own @Hashable@ instance).
instance DeriveStock1 Hashable1 where
  deriveStock1 :: Deriver1
  deriveStock1 = Deriver1 \h1Cls loc wrappedTy f ->
    -- hashable < 1.5 gives @Hashable1@ only an @Eq1@ superclass (the quantified
    -- @forall a. Hashable a => Hashable (f a)@ arrived in 1.5), so recover
    -- @Hashable@ by a direct lookup when the superclass scan comes up empty.
    baseOrWitness h1Cls "Hashable" >>= \mHash ->
    lookupOvTcs "Override1" >>= \tcs ->
    let mOv1 = ovWrap tcs ; mKeep = ovKeep tcs
        -- @f@ may be @Override1 cfg realF@ (positional or field-keyed): peel it.
        (realF, mMods) = peelOverride1With tcs f in
    case (tyConAppTyCon_maybe wrappedTy, tyConAppTyCon_maybe realF, mHash) of
      (Just st1Tc, Just fTc, Just hashCls) -> do
          let fixed      = tyConAppArgs realF
              dcons      = tyConDataCons fTc
              nCons      = length dcons
              liftHwsSel = classMethod "liftHashWithSalt" h1Cls
              hwsSel     = classMethod "hashWithSalt" hashCls
              coAt t     = coDown1With mOv1 st1Tc wrappedTy f realF t
          atv <- freshTyVar "a"
          let aTy    = mkTyVarTy atv
              innerA = mkTyConApp fTc (fixed ++ [aTy])
          gId    <- freshId (mkVisFunTyMany intTy (mkVisFunTyMany aTy intTy)) "g"
          saltId <- freshId intTy "salt"
          faId   <- freshId (mkAppTy wrappedTy aTy) "fa"
          cb     <- freshId innerA "cb"
          mTagEv <- if nCons > 1 then Just <$> newWanted loc (mkClassPred hashCls [intTy])
                                 else pure Nothing
          let step i x ftA = case classifyField atv aTy ftA of
                Nothing       -> pure Nothing
                Just FParam   -> pure (Just (\s -> mkApps (Var gId) [s, Var x], []))
                Just FConst   -> do ev <- newWanted loc (mkClassPred hashCls [ftA])
                                    pure (Just ( \s -> mkApps (Var hwsSel) [Type ftA, ctEvExpr ev, s, Var x]
                                               , [mkNonCanonical ev] ))
                Just (FApp h) -> hashApp i x h
              -- under @Override1@, hash the @h a@ field via the modifier @m@'s
              -- liftHashWithSalt, coercing the field value @h a ~R m a@ first.
              hashApp i x h = do
                let mMod = override1ModWith mKeep mMods i
                    m    = fromMaybe h mMod
                    xv   = maybe (Var x) (const (Cast (Var x) (mkStockCo (PluginProv "stock")
                             Representational (mkAppTy h aTy) (mkAppTy m aTy)))) mMod
                ev <- newWanted loc (mkClassPred h1Cls [m])
                pure (Just ( \s -> mkApps (Var liftHwsSel) [Type m, ctEvExpr ev, Type aTy, Var gId, s, xv]
                           , [mkNonCanonical ev] ))
          malts <- forM (zip [0 :: Int ..] dcons) \(i, dc) -> do
            let ftsA = fieldsAt fixed dc aTy
            xs  <- zipWithM (\n ft -> freshId ft ("x" ++ show n)) [0 :: Int ..] ftsA
            mss <- sequence (zipWith3 step [0 :: Int ..] xs ftsA)
            case sequence mss of
              Nothing    -> pure Nothing
              Just steps -> do
                let (fns, wss) = unzip steps
                    s0 = case mTagEv of
                           Just ev -> mkApps (Var hwsSel)
                                        [Type intTy, ctEvExpr ev, Var saltId, mkUncheckedIntExpr (fromIntegral i)]
                           Nothing -> Var saltId
                    body = foldl (\s fn -> fn s) s0 fns
                pure (Just (Alt (DataAlt dc) xs body, concat wss))
          case sequence malts of
            Nothing     -> pure Nothing
            Just altWss -> do
              let (alts, wss) = unzip altWss
                  tagW        = maybe [] (pure . mkNonCanonical) mTagEv
                  impl = mkLams [atv, gId, saltId, faId]
                           (destructInner fTc (fixed ++ [aTy]) (Cast (Var faId) (coAt aTy)) cb intTy alts)
                  subst   = case classTyVars h1Cls of
                              (tv : _) -> zipTvSubst [tv] [wrappedTy]
                              _        -> emptySubst
                  scPreds = map (substTy subst) (classSCTheta h1Cls)
              scEvs <- forM scPreds (newWanted loc)
              pure (Just ( classDict h1Cls wrappedTy (map ctEvExpr scEvs ++ [impl])
                         , map mkNonCanonical scEvs ++ tagW ++ concat wss ))
      _ -> pure Nothing

-- | Recover a base class @C@ from a lifted class @C1@'s quantified superclass
-- @forall a. C a => C (f a)@ (scanning all superclasses; @C1@ may have others
-- such as @Eq1@).  Avoids depending on @C@'s defining module.
baseClassOf :: Class -> Maybe Class
baseClassOf c1 = listToMaybe
  [ c | sc <- classSCTheta c1
      , ForAllPred _ _ hd <- [classifyPredType sc]
      , ClassPred c _      <- [classifyPredType hd] ]

-- | The base classes (@Hashable@, @Hashable1@, @Hashable2@) read off the
-- constraints of 'hashableWitness' — version-independent, no module lookup.
witnessClasses :: TcPluginM [Class]
witnessClasses = do
  mw <- lookupIdMaybe "Stock.Hashable" "hashableWitness"
  pure $ case mw of
    Just wId -> [ c | p <- map scaledThing (fst (splitFunTys (snd (splitForAllTyCoVars (idType wId)))))
                    , ClassPred c _ <- [classifyPredType p] ]
    Nothing  -> []

-- | 'baseClassOf', falling back to the named class from 'witnessClasses' — for
-- older @hashable@ where the quantified @Hashable@\/@Hashable1@ superclass is
-- absent.
baseOrWitness :: Class -> String -> TcPluginM (Maybe Class)
baseOrWitness c nm = case baseClassOf c of
  Just b  -> pure (Just b)
  Nothing -> do cs <- witnessClasses
                pure (listToMaybe [ k | k <- cs, occNameString (getOccName k) == nm ])

-- | @liftHashWithSalt2 gA gB@ threads the salt through the fields: first-param
-- fields via @gA@, second via @gB@, constants via their own @hashWithSalt@,
-- @h a@\/@h b@ fields via @liftHashWithSalt@ of @h@; sums mix in the tag.
-- Superclasses (@Eq2 t@, @forall a. Hashable a => Hashable1 (t a)@) are
-- requested and discharged by the plugin (the @Eq2@ built-in / the passthrough).
instance DeriveStock2 Hashable2 where
  deriveStock2 :: Deriver2
  deriveStock2 = Deriver2 \h2Cls loc wrappedTy p ->
    baseOrWitness h2Cls "Hashable1" >>= \mH1 ->
    (case mH1 of Just h1 -> baseOrWitness h1 "Hashable"
                 Nothing -> pure Nothing) >>= \mHash ->
    lookupOvTcs "Override2" >>= \tcs ->
    let mOv2 = ovWrap tcs ; mKeep = ovKeep tcs
        (realP, mMods) = peelOverride2With tcs p in
    case (tyConAppTyCon_maybe wrappedTy, tyConAppTyCon_maybe realP, mH1, mHash) of
      (Just st2Tc, Just pTc, Just h1Cls, Just hashCls) -> do
          let fixed       = tyConAppArgs realP
              dcons       = tyConDataCons pTc
              nCons       = length dcons
              liftHwsSel  = classMethod "liftHashWithSalt" h1Cls
              hwsSel      = classMethod "hashWithSalt" hashCls
              coAt2 t1 t2 = coDown2With mOv2 st2Tc wrappedTy p realP t1 t2
          atv <- freshTyVar "a" ; btv <- freshTyVar "b"
          let aTy = mkTyVarTy atv ; bTy = mkTyVarTy btv
              innerAB = mkTyConApp pTc (fixed ++ [aTy, bTy])
          gA     <- freshId (mkVisFunTyMany intTy (mkVisFunTyMany aTy intTy)) "gA"
          gB     <- freshId (mkVisFunTyMany intTy (mkVisFunTyMany bTy intTy)) "gB"
          saltId <- freshId intTy "salt"
          tId    <- freshId (mkAppTy (mkAppTy wrappedTy aTy) bTy) "t"
          cb     <- freshId innerAB "cb"
          mTagEv <- if nCons > 1 then Just <$> newWanted loc (mkClassPred hashCls [intTy])
                                 else pure Nothing
          let step i x ft = case classifyBiField atv btv aTy bTy ft of
                Nothing          -> pure Nothing
                Just BFA         -> pure (Just (\s -> mkApps (Var gA) [s, Var x], []))
                Just BFB         -> pure (Just (\s -> mkApps (Var gB) [s, Var x], []))
                Just BFConst     -> do ev <- newWanted loc (mkClassPred hashCls [ft])
                                       pure (Just ( \s -> mkApps (Var hwsSel) [Type ft, ctEvExpr ev, s, Var x]
                                                  , [mkNonCanonical ev] ))
                Just (BFFoldA h) -> hashApp i x h aTy gA
                Just (BFFoldB h) -> hashApp i x h bTy gB
              -- under @Override2@, hash the @h pTy@ field via the modifier @m@'s
              -- liftHashWithSalt, coercing the field value @h pTy ~R m pTy@ first.
              hashApp i x h pTy g = do
                let mMod = override1ModWith mKeep mMods i
                    m    = fromMaybe h mMod
                    xv   = maybe (Var x) (const (Cast (Var x) (mkStockCo (PluginProv "stock")
                             Representational (mkAppTy h pTy) (mkAppTy m pTy)))) mMod
                ev <- newWanted loc (mkClassPred h1Cls [m])
                pure (Just ( \s -> mkApps (Var liftHwsSel) [Type m, ctEvExpr ev, Type pTy, Var g, s, xv]
                           , [mkNonCanonical ev] ))
          malts <- forM (zip [0 :: Int ..] dcons) \(i, dc) -> do
            let fts = map scaledThing (dataConInstOrigArgTys dc (fixed ++ [aTy, bTy]))
            xs  <- zipWithM (\n ft -> freshId ft ("x" ++ show n)) [0 :: Int ..] fts
            mss <- sequence (zipWith3 step [0 :: Int ..] xs fts)
            case sequence mss of
              Nothing    -> pure Nothing
              Just steps -> do
                let (fns, wss) = unzip steps
                    s0 = case mTagEv of
                           Just ev -> mkApps (Var hwsSel)
                                        [Type intTy, ctEvExpr ev, Var saltId, mkUncheckedIntExpr (fromIntegral i)]
                           Nothing -> Var saltId
                    body = foldl (\s fn -> fn s) s0 fns
                pure (Just (Alt (DataAlt dc) xs body, concat wss))
          case sequence malts of
            Nothing     -> pure Nothing
            Just altWss -> do
              let (alts, wss) = unzip altWss
                  tagW        = maybe [] (pure . mkNonCanonical) mTagEv
                  impl = mkLams [atv, btv, gA, gB, saltId, tId]
                           (destructInner pTc (fixed ++ [aTy, bTy]) (Cast (Var tId) (coAt2 aTy bTy)) cb intTy alts)
                  subst   = case classTyVars h2Cls of
                              (tv : _) -> zipTvSubst [tv] [wrappedTy]
                              _        -> emptySubst
                  scPreds = map (substTy subst) (classSCTheta h2Cls)
              scEvs <- forM scPreds (newWanted loc)
              pure (Just ( classDict h2Cls wrappedTy (map ctEvExpr scEvs ++ [impl])
                         , map mkNonCanonical scEvs ++ tagW ++ concat wss ))
      _ -> pure Nothing
