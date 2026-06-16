{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE InstanceSigs #-}
{-# OPTIONS_GHC -Wno-orphans #-}   -- the @DeriveStock@ registration is necessarily an orphan

-- | A companion \"solver\" package teaching the @stock@ plugin to derive
-- @Arbitrary@ (from @QuickCheck@) without being a plugin itself, by registering
-- an @instance DeriveStock Arbitrary@ on the "Stock.Derive" SDK.
--
-- @arbitrary@ is structural and /size-aware/, in the style of
-- @Test.QuickCheck.Arbitrary.Generic@: pick a constructor (preferring the
-- terminal ones once the size budget runs out, which guarantees termination on
-- recursive types), and fill each field with its own @arbitrary@ sequenced
-- through @Gen@'s @Applicative@ — dividing the remaining size among a
-- constructor's recursive fields so generation shrinks along every recursion
-- path.  @shrink@ comes from the class default.
--
-- All the size\/choice logic lives in the ordinary Haskell combinators
-- 'stockChoose' \/ 'stockShrinkBy' below, so the synthesized Core just wires
-- constructors and these helpers together (and @QuickCheck@'s @HasCallStack@ on
-- @oneof@ is handled by GHC at their call sites, not in generated Core).
--
-- Downstream: @data T = … deriving Arbitrary via Stock T@; just depend on
-- @stock-quickcheck@, no extra @-fplugin@.
-- These @stock*@ helpers are NOT a public API: the generated @Arbitrary@ \/
-- @CoArbitrary@ Core calls them by name (@lookupIdMaybe "Stock.QuickCheck"
-- "stockChoose"@ below).  They must be exported so GHC keeps them (an
-- unexported, Haskell-unused top binding is dead-code-eliminated, and the
-- generated instance would fail to link).
module Stock.QuickCheck
  ( stockChoose
  , stockShrinkBy
  , stockCoarbitrary
  , stockShrinks
  , Arbitrary(..)
  , Arbitrary1(..)
  , Arbitrary2(..)
  , CoArbitrary(..)
  ) where

import GHC.Plugins
import GHC.Core.Class (Class, classMethods)
import GHC.Builtin.Names (applicativeClassName, mapName)
import GHC.Tc.Plugin (tcLookupClass, tcLookupId, newWanted)
import GHC.Tc.Types.Constraint (ctEvExpr, mkNonCanonical)
import GHC.Tc.Types.Evidence (EvTerm(EvExpr))
import GHC.Core.Predicate (mkClassPred)
import Control.Monad (forM, zipWithM)
import Data.Maybe (fromMaybe)
import GHC.Core.TyCo.Rep (UnivCoProvenance(PluginProv))
import GHC.Core.Multiplicity (scaledThing)
import Test.QuickCheck (Arbitrary(..), CoArbitrary(..), Arbitrary1(..), Arbitrary2(..))
import Test.QuickCheck.Gen (Gen, oneof, scale, sized, variant)
import Stock.Derive
import Stock.Internal
import Stock.Bifunctor (BiField(..), classifyBiField)

-- | Choose a constructor uniformly, but once the size budget is exhausted
-- (@n <= 0@) restrict to the /terminal/ (non-recursive) constructors when any
-- exist — the bias that makes recursive types terminate.
stockChoose :: [Gen a] -> [Gen a] -> Gen a
stockChoose terminals allcons = sized \n ->
  oneof (if n <= 0 && not (null terminals) then terminals else allcons)

-- | Divide the size budget by @k@ (the number of recursive fields in the
-- constructor) before generating a recursive field, so the budget shrinks along
-- every recursion path.
stockShrinkBy :: Int -> Gen a -> Gen a
stockShrinkBy k = scale (`div` max 1 k)

-- | @coarbitrary@ for one constructor: perturb the generator by the constructor
-- tag ('variant') and by each field's own @coarbitrary@.
stockCoarbitrary :: Int -> [Gen b -> Gen b] -> Gen b -> Gen b
stockCoarbitrary tag fs g = variant tag (foldr ($) g fs)

-- | Concatenate the per-field shrink lists of one constructor.
stockShrinks :: [[a]] -> [a]
stockShrinks = concat

-- | Does @ty@ mention @tc@ (the type being derived) — i.e. is the field
-- recursive (directly or under @[]@\/@Maybe@\/…)?
mentionsTyCon :: TyCon -> Type -> Bool
mentionsTyCon tc = go
  where
    go ty
      | Just (tc', args) <- splitTyConApp_maybe ty = tc' == tc || any go args
      | Just (_, _, s, r) <- splitFunTy_maybe ty   = go s || go r
      | Just (f, a) <- splitAppTy_maybe ty         = go f || go a
      | otherwise                                  = False

instance DeriveStock Arbitrary where
  deriveStock :: Deriver
  deriveStock = Deriver \arbCls dt -> do
    mGen     <- liftTc (lookupTyConMaybe "Test.QuickCheck.Gen" "Gen")
    mChoose  <- liftTc (lookupIdMaybe "Stock.QuickCheck" "stockChoose")
    mShrink  <- liftTc (lookupIdMaybe "Stock.QuickCheck" "stockShrinkBy")
    mShrinks <- liftTc (lookupIdMaybe "Stock.QuickCheck" "stockShrinks")
    mapId    <- liftTc (tcLookupId mapName)
    appCls   <- liftTc (tcLookupClass applicativeClassName)
    case (mGen, mChoose, mShrink, mShrinks) of
      (Just genTc, Just chooseId, Just shrinkId, Just shrinksId) -> do
        let viaTy   = dtVia dt
            genTy   = mkTyConTy genTc
            genOf t = mkAppTy genTy t
            arbSel  = classMethod "arbitrary" arbCls
            pureSel = classMethod "pure" appCls
            apSel   = classMethod "<*>"  appCls
            funChain fts res = foldr mkVisFunTyMany res fts     -- f₀ -> … -> res
            selfTc  = tyConAppTyCon (dtType dt)
        dApp <- field appCls genTy                              -- Applicative Gen
        -- one (isTerminal, generator) per constructor
        consGens <- forM (dtCons dt) \con -> do
          let fts      = conFields con
              recFlags = map (mentionsTyCon selfTc) fts
              recCount = length (filter id recFlags)
          dArbs <- mapM (field arbCls) fts                      -- Arbitrary fⱼ
          xs    <- zipWithM (\n ft -> fresh ft ("x" ++ show n)) [0 :: Int ..] fts
          let -- a field's generator, size-divided when the field is recursive
              gField ft d isR =
                let a = mkApps (Var arbSel) [Type ft, d]
                in if isR
                     then mkApps (Var shrinkId)
                            [Type ft, mkUncheckedIntExpr (fromIntegral recCount), a]
                     else a
              gFields = zipWith3 gField fts dArbs recFlags
              lam     = mkLams xs (injectSOP dt con (map Var xs))   -- fts -> viaTy
              pureLam = mkApps (Var pureSel) [Type genTy, dApp, Type (funChain fts viaTy), lam]
              step (acc, j) g =
                let a = fts !! j
                    b = funChain (drop (j + 1) fts) viaTy
                in (mkApps (Var apSel) [Type genTy, dApp, Type a, Type b, acc, g], j + 1)
          pure (not (or recFlags), fst (foldl step (pureLam, 0 :: Int) gFields))
        let arbExpr = case consGens of
              [(_, g)] -> g                                     -- single ctor: no choice
              _ -> let allL  = mkListExpr (genOf viaTy) (map snd consGens)
                       termL = mkListExpr (genOf viaTy) [ g | (True, g) <- consGens ]
                   in mkApps (Var chooseId) [Type viaTy, termL, allL]
            arbIdx    = methodIndex "arbitrary" arbCls
            shrinkIdx = methodIndex "shrink" arbCls
            shrinkSel = classMethod "shrink" arbCls
            listVia   = mkListTy viaTy
        -- structural shrink: shrink one field at a time, recombining (the
        -- @recursivelyShrink@ half of @genericShrink@)
        sx <- fresh viaTy "s"
        shrinkBody <- matchSOP dt listVia (Var sx) \_ con fields -> do
          let fts = conFields con
          perField <- forM (zip [0 :: Int ..] fts) \(j, ft) -> do
            d   <- field arbCls ft
            fj' <- fresh ft ("s" ++ show j)
            let rebuilt   = injectSOP dt con (take j fields ++ [Var fj'] ++ drop (j + 1) fields)
                shrinkFj  = mkApps (Var shrinkSel) [Type ft, d, fields !! j]    -- [ft]
            pure (mkApps (Var mapId) [Type ft, Type viaTy, Lam fj' rebuilt, shrinkFj])  -- [viaTy]
          pure (mkApps (Var shrinksId) [Type viaTy, mkListExpr listVia perField])
        classDictWith arbCls viaTy [] [(arbIdx, arbExpr), (shrinkIdx, mkLams [sx] shrinkBody)]
      _ -> pprPanic "stock-quickcheck: Test.QuickCheck.Gen / Stock.QuickCheck lookups failed" empty

-- | @coarbitrary x = stockCoarbitrary tag [coarbitrary f₀, …]@ — a consumer:
-- perturb the generator by the constructor tag and each field.
instance DeriveStock CoArbitrary where
  deriveStock :: Deriver
  deriveStock = Deriver \cls dt -> do
    mCo  <- liftTc (lookupIdMaybe "Stock.QuickCheck" "stockCoarbitrary")
    mGen <- liftTc (lookupTyConMaybe "Test.QuickCheck.Gen" "Gen")
    case (mCo, mGen) of
      (Just coId, Just genTc) -> do
        let via      = dtVia dt
            coarbSel = classMethod "coarbitrary" cls    -- coarbitrary :: a -> Gen b -> Gen b
        bTv <- liftTc (freshTyVar "b")
        let bTy       = mkTyVarTy bTv
            genB      = mkAppTy (mkTyConTy genTc) bTy   -- Gen b
            perturbTy = mkVisFunTyMany genB genB        -- Gen b -> Gen b
        x <- fresh via "x"
        g <- fresh genB "g"
        body <- matchSOP dt genB (Var x) \i con fields -> do
          perturbs <- forM (zip (conFields con) fields) \(ft, fe) -> do
            d <- field cls ft
            pure (mkApps (Var coarbSel) [Type ft, d, Type bTy, fe])   -- :: Gen b -> Gen b
          pure (mkApps (Var coId)
                  [ Type bTy, mkUncheckedIntExpr (fromIntegral i)
                  , mkListExpr perturbTy perturbs, Var g ])
        pure (classDict cls via [mkLams [bTv, x, g] body])
      _ -> pprPanic "stock-quickcheck: CoArbitrary lookups failed" empty

-- | @liftArbitrary g@: like @arbitrary@, but parameter fields draw from the
-- supplied @g :: Gen a@, an @h a@ field from @liftArbitrary@ of @h@, and a
-- constant from its own @arbitrary@ — size-controlled exactly like 'arbitrary'.
-- @liftShrink@ comes from the class default.
instance DeriveStock1 Arbitrary1 where
  deriveStock1 :: Deriver1
  deriveStock1 = Deriver1 \a1Cls loc wrappedTy f -> do
    mGen      <- lookupTyConMaybe "Test.QuickCheck.Gen" "Gen"
    mChoose   <- lookupIdMaybe "Stock.QuickCheck" "stockChoose"
    mShrinkBy <- lookupIdMaybe "Stock.QuickCheck" "stockShrinkBy"
    mArb      <- lookupClassMaybe "Test.QuickCheck.Arbitrary" "Arbitrary"
    tcs       <- lookupOvTcs "Override1"
    appCls    <- tcLookupClass applicativeClassName
    -- @f@ may be @Override1 cfg realF@ (positional or field-keyed): peel it; @coAt@
    -- then unwraps /both/ newtypes (see 'coDown1With').
    let mOv1 = ovWrap tcs ; mKeep = ovKeep tcs
        (realF, mMods) = peelOverride1With tcs f
    case (tyConAppTyCon_maybe wrappedTy, tyConAppTyCon_maybe realF, mGen, mChoose, mShrinkBy, mArb) of
      (Just st1Tc, Just fTc, Just genTc, Just chooseId, Just shrinkById, Just arbCls) -> do
        let fixed      = tyConAppArgs realF
            dcons      = tyConDataCons fTc
            genTy      = mkTyConTy genTc
            arbSel     = classMethod "arbitrary"     arbCls
            liftArbSel = classMethod "liftArbitrary" a1Cls
            pureSel    = classMethod "pure" appCls
            apSel      = classMethod "<*>"  appCls
            funChain ts res = foldr mkVisFunTyMany res ts
            coAt t = coDown1With mOv1 st1Tc wrappedTy f realF t
        atv <- freshTyVar "a"
        let aTy    = mkTyVarTy atv
            viaA   = mkAppTy wrappedTy aTy        -- Stock1 F a
            genOfV = mkAppTy genTy viaA           -- Gen (Stock1 F a)
        gA     <- freshId (mkAppTy genTy aTy) "gA"
        dAppEv <- newWanted loc (mkClassPred appCls [genTy])
        let dApp = ctEvExpr dAppEv
        consGens <- forM dcons \dc -> do
          let ftsA = fieldsAt fixed dc aTy
          mField <- zipWithM (\i ftA ->
            case classifyField atv aTy ftA of
              Nothing       -> pure Nothing
              Just FParam   -> pure (Just (Var gA, []))                       -- Gen a
              Just FConst   -> do ev <- newWanted loc (mkClassPred arbCls [ftA])
                                  pure (Just ( mkApps (Var arbSel) [Type ftA, ctEvExpr ev]
                                             , [mkNonCanonical ev] ))          -- Gen ftA
              -- @h a@ field; under @Override1@ generate via the modifier @m@'s
              -- @Arbitrary1@ (e.g. a non-empty/sized/sorted @m@ coercible to @h@)
              -- then coerce @Gen (m a) ~R Gen (h a)@ — the runtime field stays @h a@.
              Just (FApp h) -> do let mMod = override1ModWith mKeep mMods i
                                      m    = fromMaybe h mMod
                                  ev <- newWanted loc (mkClassPred a1Cls [m])
                                  let gm = mkApps (Var liftArbSel) [Type m, ctEvExpr ev, Type aTy, Var gA]
                                      g  = case mMod of
                                             Nothing -> gm                    -- Gen (h a)
                                             Just _  ->                       -- reshape m → h
                                               Cast gm (mkStockCo (PluginProv "stock") Representational
                                                          (mkAppTy genTy (mkAppTy m aTy))
                                                          (mkAppTy genTy (mkAppTy h aTy)))
                                      g' | mentionsTyCon fTc ftA =            -- recursive ⇒ shrink size
                                             mkApps (Var shrinkById)
                                               [Type (mkAppTy h aTy), mkUncheckedIntExpr 1, g]
                                         | otherwise = g
                                  pure (Just (g', [mkNonCanonical ev]))       -- Gen (h a)
            ) [0 :: Int ..] ftsA
          case sequence mField of
            Nothing  -> pure Nothing
            Just fgw -> do
              let (gens, wss) = unzip fgw
              xs <- zipWithM (\n t -> freshId t ("x" ++ show n)) [0 :: Int ..] ftsA
              let lam = mkLams xs (Cast (mkCoreConApps dc (map Type (fixed ++ [aTy]) ++ map Var xs))
                                        (mkSymCo (coAt aTy)))                  -- fts -> Stock1 F a
                  pureLam = mkApps (Var pureSel) [Type genTy, dApp, Type (funChain ftsA viaA), lam]
                  step (acc, j) g =
                    ( mkApps (Var apSel) [ Type genTy, dApp, Type (ftsA !! j)
                                         , Type (funChain (drop (j + 1) ftsA) viaA), acc, g ]
                    , j + 1 )
                  isTerm = not (any (mentionsTyCon fTc) ftsA)
              pure (Just (isTerm, fst (foldl step (pureLam, 0 :: Int) gens), concat wss))
        case sequence consGens of
          Nothing  -> pure Nothing
          Just cgs -> do
            let body = case cgs of
                  [(_, g, _)] -> g
                  _ -> mkApps (Var chooseId)
                         [ Type viaA
                         , mkListExpr genOfV [ g | (True, g, _) <- cgs ]
                         , mkListExpr genOfV [ g | (_, g, _) <- cgs ] ]
                impl = mkLams [atv, gA] body
                liftArbIdx = methodIndex "liftArbitrary" a1Cls
            dict <- recDictWith a1Cls wrappedTy [] [(liftArbIdx, impl)]
            pure (Just (EvExpr dict, mkNonCanonical dAppEv : concatMap (\(_, _, w) -> w) cgs))
      _ -> pure Nothing

-- | The position of a class method by source name (total; methods always exist).
methodIndex :: String -> Class -> Int
methodIndex nm cls =
  case [ i | (i, m) <- zip [0 :: Int ..] (classMethods cls)
           , occNameString (occName m) == nm ] of
    (i : _) -> i
    []      -> 0

-- | @liftArbitrary2 gA gB@: the two-parameter analogue of 'liftArbitrary' (the
-- same 'Stock2' constructor walk as @Bifunctor@ \/ @Bifoldable@).  An @a@ field
-- draws from @gA@, a @b@ field from @gB@, an @h a@ \/ @h b@ field from
-- @liftArbitrary@ of @h@ (its 'Arbitrary1'), and a constant from its own
-- @arbitrary@; size is controlled exactly as in 'arbitrary'.  @liftShrink2@
-- comes from the class default.
--
-- @Override2@ is honoured exactly as @Override1@ is for 'liftArbitrary': a
-- modifier @m@ on an @h a@ \/ @h b@ field generates via @m@'s 'Arbitrary1' and
-- coerces @Gen (m a) ~R Gen (h a)@ (the runtime field stays @h a@).  Out of
-- scope (the synthesis bails cleanly, so the plugin reports it): a nested
-- two-parameter @g a b@ field, including direct recursion.
instance DeriveStock2 Arbitrary2 where
  deriveStock2 :: Deriver2
  deriveStock2 = Deriver2 \a2Cls loc wrappedTy p -> do
    mGen      <- lookupTyConMaybe "Test.QuickCheck.Gen" "Gen"
    mChoose   <- lookupIdMaybe "Stock.QuickCheck" "stockChoose"
    mShrinkBy <- lookupIdMaybe "Stock.QuickCheck" "stockShrinkBy"
    mArb      <- lookupClassMaybe "Test.QuickCheck.Arbitrary" "Arbitrary"
    mArb1     <- lookupClassMaybe "Test.QuickCheck.Arbitrary" "Arbitrary1"
    tcs       <- lookupOvTcs "Override2"
    appCls    <- tcLookupClass applicativeClassName
    let mKeep = ovKeep tcs ; mOv2 = ovWrap tcs
        (realP, mMods) = peelOverride2With tcs p
    case (tyConAppTyCon_maybe wrappedTy, tyConAppTyCon_maybe realP, mGen, mChoose, mShrinkBy, mArb, mArb1) of
      (Just st2Tc, Just pTc, Just genTc, Just chooseId, Just shrinkById, Just arbCls, Just arb1Cls) -> do
        let fixed       = tyConAppArgs realP
            dcons       = tyConDataCons pTc
            genTy       = mkTyConTy genTc
            arbSel      = classMethod "arbitrary"      arbCls
            liftArbSel  = classMethod "liftArbitrary"  arb1Cls
            pureSel     = classMethod "pure" appCls
            apSel       = classMethod "<*>"  appCls
            funChain ts res = foldr mkVisFunTyMany res ts
            coAt t1 t2  = coDown2With mOv2 st2Tc wrappedTy p realP t1 t2
            -- an @h a@ \/ @h b@ field at index @i@; under @Override2@ a modifier
            -- @m@ reshapes the functor (generate @m@, coerce @Gen (m e) ~R Gen (h e)@).
            liftField i h elemTy gElem ft = do
              let mMod = override1ModWith mKeep mMods i
                  m    = fromMaybe h mMod
              ev <- newWanted loc (mkClassPred arb1Cls [m])
              let gm = mkApps (Var liftArbSel) [Type m, ctEvExpr ev, Type elemTy, Var gElem]  -- Gen (m e)
                  g0 = case mMod of
                         Nothing -> gm
                         Just _  -> Cast gm (mkStockCo (PluginProv "stock") Representational
                                               (mkAppTy genTy (mkAppTy m elemTy))
                                               (mkAppTy genTy (mkAppTy h elemTy)))            -- Gen (h e)
                  g  | mentionsTyCon pTc ft =                    -- recursive ⇒ shrink size
                         mkApps (Var shrinkById) [Type ft, mkUncheckedIntExpr 1, g0]
                     | otherwise = g0
              pure (Just (g, [mkNonCanonical ev]))
        atv <- freshTyVar "a" ; btv <- freshTyVar "b"
        let aTy = mkTyVarTy atv ; bTy = mkTyVarTy btv
            viaAB  = mkAppTy (mkAppTy wrappedTy aTy) bTy          -- Stock2 P a b
            genOfV = mkAppTy genTy viaAB
        gA <- freshId (mkAppTy genTy aTy) "gA"
        gB <- freshId (mkAppTy genTy bTy) "gB"
        dAppEv <- newWanted loc (mkClassPred appCls [genTy])
        let dApp = ctEvExpr dAppEv
        consGens <- forM dcons \dc -> do
          let fts = map scaledThing (dataConInstOrigArgTys dc (fixed ++ [aTy, bTy]))
          mField <- zipWithM (\i ft ->
            case classifyBiField atv btv aTy bTy ft of
              Just BFA         -> pure (Just (Var gA, []))                  -- Gen a
              Just BFB         -> pure (Just (Var gB, []))                  -- Gen b
              Just BFConst     -> do ev <- newWanted loc (mkClassPred arbCls [ft])
                                     pure (Just ( mkApps (Var arbSel) [Type ft, ctEvExpr ev]
                                                , [mkNonCanonical ev] ))    -- Gen ft
              Just (BFFoldA h) -> liftField i h aTy gA ft                   -- Gen (h a)
              Just (BFFoldB h) -> liftField i h bTy gB ft                   -- Gen (h b)
              Nothing          -> pure Nothing                             -- g a b / recursion: bail
            ) [0 :: Int ..] fts
          case sequence mField of
            Nothing  -> pure Nothing
            Just fgw -> do
              let (gens, wss) = unzip fgw
              xs <- zipWithM (\n t -> freshId t ("x" ++ show n)) [0 :: Int ..] fts
              let lam = mkLams xs (Cast (mkCoreConApps dc (map Type (fixed ++ [aTy, bTy]) ++ map Var xs))
                                        (mkSymCo (coAt aTy bTy)))           -- fts -> Stock2 P a b
                  pureLam = mkApps (Var pureSel) [Type genTy, dApp, Type (funChain fts viaAB), lam]
                  step (acc, j) g =
                    ( mkApps (Var apSel) [ Type genTy, dApp, Type (fts !! j)
                                         , Type (funChain (drop (j + 1) fts) viaAB), acc, g ]
                    , j + 1 )
                  isTerm = not (any (mentionsTyCon pTc) fts)
              pure (Just (isTerm, fst (foldl step (pureLam, 0 :: Int) gens), concat wss))
        case sequence consGens of
          Nothing  -> pure Nothing
          Just cgs -> do
            let body = case cgs of
                  [(_, g, _)] -> g
                  _ -> mkApps (Var chooseId)
                         [ Type viaAB
                         , mkListExpr genOfV [ g | (True, g, _) <- cgs ]
                         , mkListExpr genOfV [ g | (_, g, _) <- cgs ] ]
                impl = mkLams [atv, btv, gA, gB] body
                liftArb2Idx = methodIndex "liftArbitrary2" a2Cls
            dict <- recDictWith a2Cls wrappedTy [] [(liftArb2Idx, impl)]
            pure (Just (EvExpr dict, mkNonCanonical dAppEv : concatMap (\(_, _, w) -> w) cgs))
      _ -> pure Nothing
