{-# LANGUAGE CPP #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DerivingVia #-}
{-# OPTIONS_GHC -Wno-x-partial -Wno-incomplete-uni-patterns -Wno-unused-imports #-}
-- | @Generic@ \/ @Generic1@ synthesizers: @Rep@ as a balanced @:+:@ \/ @:*:@ tree.
module Stock.Generic where
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

-- | Field types with @Override1@ modifiers applied: an @h a@ field whose config
-- names a modifier @m@ becomes @m a@ (so its @Rep1@ leaf is @Rec1 m@); all other
-- fields are unchanged.  Used by /both/ 'rewriteRep1' (the @Rep1@ type) and
-- 'synthGeneric1' (the @from1@\/@to1@ values), keeping them in lock-step.
reshape1Ftys :: GenEnv -> Maybe [Type] -> TyVar -> Type -> [Type] -> [Type]
reshape1Ftys gen mMods atv aTy fts =
  -- Any overridden field's @Rep1@ leaf is @m a@ — so the @Override1@ config leaks
  -- into @Rep1 (Overriding1 F cfg)@ uniformly, for a functorial @h a@ field AND a
  -- constant one (e.g. an @Int@ field via @Const (Sum Int)@ becomes @Const (Sum
  -- Int) a@, which @Generically1@ then sees as an applicative @Rec1@ leaf).
  [ case override1Mod gen mMods i of
      Just m  -> mkAppTy m aTy
      Nothing -> ft
  | (i, ft) <- zip [0 :: Int ..] fts ]

rewriteRep :: GenEnv -> RewriteEnv -> [Ct] -> [Type] -> TcPluginM TcPluginRewriteResult
rewriteRep gen _env _given [arg]
  -- @Rep (Stock (Override T cfg))@: the leaves carry the /modifier/ types, so
  -- @Generically (Stock (Override T cfg))@ derives over the overridden fields.
  -- (Checked first; the plain branch would otherwise treat @Override@ as a data
  -- type.)  @synthGeneric@'s @from@\/@to@ coerce to match.
  | Just (realInner, cons) <- overrideFieldTypes gen arg = do
      fixOf <- mkFixOf (geMeta gen) (map fst cons)
      let struct = repMetaFts gen fixOf realInner cons
          lhs    = mkTyConApp (geRepTc gen) [arg]
          co     = mkStockCo (PluginProv "stock") Nominal lhs struct
      pure (TcPluginRewriteTo (mkReduction co struct) [])
  | Just repr <- mkRepr (geStock gen) arg, not (null (rCons repr)) = do
      fixOf <- mkFixOf (geMeta gen) (map ciCon (rCons repr))
      let struct = repMeta gen fixOf (rInner repr) (map ciCon (rCons repr))
          lhs    = mkTyConApp (geRepTc gen) [arg]
          co     = mkStockCo (PluginProv "stock") Nominal lhs struct
      pure (TcPluginRewriteTo (mkReduction co struct) [])
rewriteRep _ _ _ _ = pure TcPluginNoRewrite

-- | Rewrite @Rep1 (Stock1 F)@ to the parameter-aware structure (@Par1@\/@Rec1@\/
-- @Rec0@ leaves under the @M1@ metadata).  No rewrite if any field is an
-- unsupported shape (composition etc.).
rewriteRep1 :: GenEnv -> RewriteEnv -> [Ct] -> [Type] -> TcPluginM TcPluginRewriteResult
rewriteRep1 gen _env _given args
  | (arg : _)  <- reverse args             -- @Rep1@ is poly-kinded: drop the kind arg
  , Just st1Tc <- geStock1 gen
  , Just stTc  <- tyConAppTyCon_maybe arg, stTc == st1Tc
  , (_ : f : _) <- tyConAppArgs arg
    -- @f@ may be @Override1 cfg realF@: peel it, then reshape @h a@ fields to
    -- @m a@ so the @Rep1@ leaves use the modifier (in lock-step with 'synthGeneric1').
  , let (realF, mMods) = peelOverride1 gen f
  , Just fTc   <- tyConAppTyCon_maybe realF = do
      a0 <- freshTyVar "a"
      let aT0   = mkTyVarTy a0
          fixed = tyConAppArgs realF
          dcons = tyConDataCons fTc
          innerF = mkTyConApp fTc (fixed ++ [aT0])
          ftysOf dc = reshape1Ftys gen mMods a0 aT0
                        (map scaledThing (dataConInstOrigArgTys dc (fixed ++ [aT0])))
          ok = all (all (isJust . rep1Field gen a0) . ftysOf) dcons
      if not ok then pure TcPluginNoRewrite else do
        fixOf <- mkFixOf (geMeta gen) dcons
        let struct = repMetaWith gen fixOf (fromJust . rep1Field gen a0) innerF
                       [ (dc, ftysOf dc) | dc <- dcons ]
            lhs    = mkTyConApp (g1RepTc (geGen1 gen)) args
            co     = mkStockCo (PluginProv "stock") Nominal lhs struct
        pure (TcPluginRewriteTo (mkReduction co struct) [])
rewriteRep1 _ _ _ _ = pure TcPluginNoRewrite

-- | The structural @Rep@ for a whole datatype: a single constructor is just its
-- product 'repStruct'; several constructors form a /balanced/ @:+:@ tree of
-- their product structs (mirroring GHC's @foldBal@).
-- @cons@ carries each constructor's /modifier/ field types ('ciFields') and the
-- per-cell coercions ('ciFieldCos', @realFieldType ~R modifierType@; 'Refl'
-- without an @Override@).  The @Rep@ leaves use the modifier types (matching
-- 'rewriteRep'); @from@ coerces the real field /into/ the leaf, @to@ coerces
-- /back/ before rebuilding.  Refl everywhere ⇒ byte-identical Core to plain.
synthGeneric :: GenEnv -> Type -> Type -> Coercion -> [ConInfo] -> TcPluginM EvTerm
synthGeneric gen wrappedTy innerTy co cons = do
  fixOf <- mkFixOf (geMeta gen) (map ciCon cons)
  let genCls = geGen gen
      k1Tc   = geK1Tc gen
      prodTc = geProdTc gen ; prodDc = geProdDc gen
      sumTc  = geSumTc gen
      [l1Dc, r1Dc] = tyConDataCons sumTc
      u1Dc   = head (tyConDataCons (geU1Tc gen))
      rTy    = geRTy gen
      kTy    = liftedTypeKind
      dcons    = map ciCon cons
      modFtss  = map ciFields cons                    -- Rep leaves (modifier types)
      cosss    = map ciFieldCos cons                  -- realFt ~R modFt per field
      realFtss = map (fieldTysAt innerTy) dcons        -- bound (pattern) types
      mfcss    = zipWith zip modFtss cosss             -- per con: [(modFt, fco)]
      structMeta = repMetaFts gen fixOf innerTy (zip dcons modFtss)   -- faithful (rewrite-target) Rep
      structBare = repData gen modFtss                          -- the un-M1 value structure
      lhs    = mkTyConApp (geRepTc gen) [wrappedTy]
      coRep  = mkStockCo (PluginProv "stock") Nominal lhs structMeta
      -- the M1 layers are newtypes, so structMeta ~R structBare (asserted, true)
      coStrip = mkStockCo (PluginProv "stock") Representational structMeta structBare

  ux <- unsafeTcPluginTcM getUniqueM
  let xtv = mkTyVar (mkSystemName ux (mkTyVarOcc "x")) liftedTypeKind
      xty = mkTyVarTy xtv
      prodTy f g = mkTyConApp prodTc [kTy, f, g]
      sumTy  f g = mkTyConApp sumTc  [kTy, f, g]
      -- Rep x ~R structMeta x ~R structBare x  (and back)
      castDn = mkSubCo (mkAppCo coRep (mkNomReflCo xty))             -- Rep x ~R structMeta x
                 `mkTransCo` mkAppCo coStrip (mkNomReflCo xty)       -- structMeta x ~R structBare x
      castUp = mkSymCo castDn                                        -- structBare x ~R Rep x
      k1Co ft     = mkUnbranchedAxInstCo Representational
                      (newTyConCo k1Tc) [kTy, rTy, ft, xty] []   -- K1 R ft x ~R ft
      -- from: real field value (fi :: realFt) coerced to its modifier type, into K1 modFt
      k1ValOv fco mft fi = Cast (castInto (Var fi) fco) (mkSymCo (k1Co mft))
      -- to: a K1 modFt projection back to the real field type
      unK1Ov  fco mft scr = castInto (Cast scr (k1Co mft)) (mkSymCo fco)
      -- balanced product VALUE (+ its type), mirroring 'repStruct'/'foldBal'
      buildV [(v, t)] = (v, t)
      buildV vs = let (l, r)  = splitAt (length vs `div` 2) vs
                      (lv, lt) = buildV l ; (rv, rt) = buildV r
                  in ( mkCoreConApps prodDc [Type kTy, Type lt, Type rt, Type xty, lv, rv]
                     , prodTy lt rt )
      -- product value for one constructor's fields (per field: its (modFt, fco) + binder)
      prodValOf mfcs fis
        | null mfcs = mkCoreConApps u1Dc [Type kTy, Type xty]
        | otherwise = fst (buildV [ (k1ValOv fco mft fi, mkTyConApp k1Tc [kTy, rTy, mft])
                                  | ((mft, fco), fi) <- zip mfcs fis ])
      -- balanced @:+:@ injectors (one per constructor) + the sum type
      injectors [fts] = ([id], repStruct gen fts)
      injectors fss   =
        let (l, r)   = splitAt (length fss `div` 2) fss
            (li, lt) = injectors l ; (ri, rt) = injectors r
            wrapL v  = mkCoreConApps l1Dc [Type kTy, Type lt, Type rt, Type xty, v]
            wrapR v  = mkCoreConApps r1Dc [Type kTy, Type lt, Type rt, Type xty, v]
        in (map (wrapL .) li ++ map (wrapR .) ri, sumTy lt rt)
      (injs, _) = injectors modFtss

  -- from = /\x. \v -> case (v |> co) of  Cᵢ f.. -> injᵢ <product> |> castUp
  vId <- freshId wrappedTy "v"
  cbV <- freshId innerTy "cb"
  fromAlts <- forM (zip dcons (zip3 realFtss mfcss injs)) \(dc, (realFts, mfcs, inj)) -> do
    fis <- zipWithM (\n ft -> freshId ft ("f" ++ show n)) [0 :: Int ..] realFts
    pure (Alt (DataAlt dc) fis (Cast (inj (prodValOf mfcs fis)) castUp))
  let fromImpl = Lam xtv (Lam vId
                   (Case (Cast (Var vId) co) cbV (mkAppTy lhs xty) fromAlts))

  -- to = /\x. \r -> <project (r |> castDn) through :+: / :*:, rebuild Cᵢ>
  rId <- freshId (mkAppTy lhs xty) "r"
  let -- take apart a balanced :*: product (typed by the modifier types), returning the
      -- real-typed field exprs (each projected then coerced back) + a case-nesting wrapper
      destruct scr [(mft, fco)] = pure ([unK1Ov fco mft scr], id)
      destruct scr mfs = do
        let (lT, rT) = splitAt (length mfs `div` 2) mfs
            lt = repStruct gen (map fst lT) ; rt = repStruct gen (map fst rT)
        lv <- freshId (mkAppTy lt xty) "l"
        rv <- freshId (mkAppTy rt xty) "rr"
        cb <- freshId (mkAppTy (prodTy lt rt) xty) "pc"
        (lfs, lwrap) <- destruct (Var lv) lT
        (rfs, rwrap) <- destruct (Var rv) rT
        let wrap body = Case scr cb wrappedTy
                          [Alt (DataAlt prodDc) [lv, rv] (lwrap (rwrap body))]
        pure (lfs ++ rfs, wrap)
      -- rebuild one constructor from its product struct
      rebuildCon scr mfs dc
        | null mfs  = pure (Cast (conAppAt innerTy dc []) (mkSymCo co))
        | otherwise = do (fields, wrap) <- destruct scr mfs
                         pure (wrap (Cast (conAppAt innerTy dc fields) (mkSymCo co)))
      -- project through the balanced :+: tree, rebuilding at each leaf
      destructSum scr [mfs] [dc] = rebuildCon scr mfs dc
      destructSum scr mfss  dcs  = do
        let h          = length mfss `div` 2
            (lfs, rfs) = splitAt h mfss ; (ldc, rdc) = splitAt h dcs
            lt = repData gen (map (map fst) lfs) ; rt = repData gen (map (map fst) rfs)
        lv <- freshId (mkAppTy lt xty) "sl"
        rv <- freshId (mkAppTy rt xty) "sr"
        cb <- freshId (mkAppTy (sumTy lt rt) xty) "sc"
        lbody <- destructSum (Var lv) lfs ldc
        rbody <- destructSum (Var rv) rfs rdc
        pure (Case scr cb wrappedTy
                [ Alt (DataAlt l1Dc) [lv] lbody, Alt (DataAlt r1Dc) [rv] rbody ])
  toBody <- destructSum (Cast (Var rId) castDn) mfcss dcons
  let toImpl = Lam xtv (Lam rId toBody)

  pure $ EvExpr $ mkClassDict genCls wrappedTy [fromImpl, toImpl]

-- | Synthesize @Generic1 (Stock1 F)@: like 'synthGeneric' but the field
-- representation is parameter-aware — the last type variable @a@ becomes
-- @Par1@, @g a@ becomes @Rec1 g@, a constant becomes @Rec0@ (see 'rep1Field').
-- @from1@\/@to1@ wrap\/unwrap each field through the corresponding newtype.
-- 'Nothing' for shapes 'rep1Field' rejects (e.g. composition @f (g a)@).
synthGeneric1 :: GenEnv -> Class -> CtLoc -> Type -> Type
              -> TcPluginM (Maybe (EvTerm, [Ct]))
synthGeneric1 gen cls loc wrappedTy f =
  case (geStock1 gen, tyConAppTyCon_maybe realF) of
    (Just st1Tc, Just fTc) -> do
      functorCls <- tcLookupClass functorClassName
      let g1     = geGen1 gen
          fixed  = tyConAppArgs realF
          dcons  = tyConDataCons fTc
          k1Tc   = geK1Tc gen ; rTy = geRTy gen ; kTy = liftedTypeKind
          par1Tc = g1Par1Tc g1 ; rec1Tc = g1Rec1Tc g1 ; compTc = g1CompTc g1
          fmapSel = classMethod "fmap" functorCls
          prodTc = geProdTc gen ; prodDc = geProdDc gen
          sumTc  = geSumTc gen ; [l1Dc, r1Dc] = tyConDataCons sumTc
          u1Dc   = head (tyConDataCons (geU1Tc gen))
          coAt t = coDown1 gen st1Tc wrappedTy f realF t
      atv <- freshTyVar "a"
      let aTy    = mkTyVarTy atv
          innerA = mkTyConApp fTc (fixed ++ [aTy])
          prodTy a b = mkTyConApp prodTc [kTy, a, b]
          sumTy  a b = mkTyConApp sumTc  [kTy, a, b]
          u1Ty   = mkTyConApp (geU1Tc gen) [kTy]
          par1Co   = mkUnbranchedAxInstCo Representational (newTyConCo par1Tc) [aTy] []
          rec1Co h = mkUnbranchedAxInstCo Representational (newTyConCo rec1Tc) [kTy, h, aTy] []
          k1Co t   = mkUnbranchedAxInstCo Representational (newTyConCo k1Tc) [kTy, rTy, t, aTy] []
          fieldsOf dc = map scaledThing (dataConInstOrigArgTys dc (fixed ++ [aTy]))
          -- classify a field → (bare leaf type, wrap, unwrap, emitted wanteds).
          -- wrap\/unwrap are value transforms; composition emits a @Functor@
          -- wanted and uses @Comp1 . fmap innerWrap@ (matching GHC's DeriveGeneric1).
          classify1 mMod ft
            | ft `eqType` aTy =
                pure (Just (mkTyConTy par1Tc, \e -> Cast e (mkSymCo par1Co), \e -> Cast e par1Co, []))
            | not (atv `elemVarSet` tyCoVarsOfType ft) = case mMod of
                -- a constant field with an @Override1@ modifier @m@ reshapes to a
                -- @Rec1 m@ leaf (so the config leaks into @Rep1@ for constant fields
                -- too, e.g. @Int@ via @Const (Sum Int)@): wrap coerces @ft ~R m a@
                -- then into @Rec1 m a@; unwrap reverses.
                Just m  -> let co = mkStockCo (PluginProv "stock") Representational ft (mkAppTy m aTy)
                           in pure (Just ( mkTyConApp rec1Tc [kTy, m]
                                         , \e -> Cast e (co `mkTransCo` mkSymCo (rec1Co m))
                                         , \e -> Cast e (rec1Co m `mkTransCo` mkSymCo co), [] ))
                Nothing -> pure (Just (mkTyConApp k1Tc [kTy, rTy, ft], \e -> Cast e (mkSymCo (k1Co ft)), \e -> Cast e (k1Co ft), []))
            | Just (h, larg) <- splitAppTy_maybe ft
            , not (atv `elemVarSet` tyCoVarsOfType h) =
                if larg `eqType` aTy
                  -- @h a@ leaf, reshaped to @Rec1 m@ under @Override1@: wrap coerces
                  -- the field value @h a ~R m a@ then into @Rec1 m a@; unwrap reverses.
                  then let m  = fromMaybe h mMod
                           co = reshapeCo h m aTy
                       in pure (Just ( mkTyConApp rec1Tc [kTy, m]
                                     , \e -> Cast e (co `mkTransCo` mkSymCo (rec1Co m))
                                     , \e -> Cast e (rec1Co m `mkTransCo` mkSymCo co), [] ))
                  else do
                    minner <- classify1 Nothing larg
                    case minner of
                      Nothing -> pure Nothing
                      Just (innerRep, innerWrap, innerUnwrap, iws) -> do
                        ev  <- newWanted loc (mkClassPred functorCls [h])
                        yId <- freshId larg "y"
                        zId <- freshId (mkAppTy innerRep aTy) "z"
                        let dict      = ctEvExpr ev
                            compTy    = mkTyConApp compTc [kTy, kTy, h, innerRep]
                            comp1Co   = mkUnbranchedAxInstCo Representational
                                          (newTyConCo compTc) [kTy, kTy, h, innerRep, aTy] []
                            innerAppA = mkAppTy innerRep aTy
                            fmapAt aT bT fn x = mkApps (Var fmapSel) [Type h, dict, Type aT, Type bT, fn, x]
                            -- Comp1 (fmap innerWrap e)        :: (h :.: innerRep) a
                            wrapE e   = Cast (fmapAt larg innerAppA (mkLams [yId] (innerWrap (Var yId))) e)
                                             (mkSymCo comp1Co)
                            -- fmap innerUnwrap (unComp1 e)    :: h larg
                            unwrapE e = fmapAt innerAppA larg (mkLams [zId] (innerUnwrap (Var zId))) (Cast e comp1Co)
                        pure (Just (compTy, wrapE, unwrapE, mkNonCanonical ev : iws))
            | otherwise = pure Nothing
      classifiedM <- forM dcons \dc ->
        zipWithM (\i ft -> classify1 (override1Mod gen mMods i) ft) [0 :: Int ..] (fieldsOf dc)
      case traverse sequence classifiedM of
        Nothing -> pure Nothing
        Just classified -> do
          fixOf <- mkFixOf (geMeta gen) dcons
          let fieldWanteds = concatMap (concatMap (\(_, _, _, ws) -> ws)) classified
              leafTys con = [ lt | (lt, _, _, _) <- con ]
              bareCon con = case leafTys con of { [] -> u1Ty; lts -> foldBal prodTy lts }
              structBare  = case map bareCon classified of { [s] -> s; ss -> foldBal sumTy ss }
              structMeta  = repMetaWith gen fixOf (fromJust . rep1Field gen atv) innerA
                              [ (dc, reshape1Ftys gen mMods atv aTy (fieldTysAt innerA dc)) | dc <- dcons ]
              lhs1   = mkTyConApp (g1RepTc g1) [liftedTypeKind, wrappedTy]
              coRep  = mkStockCo (PluginProv "stock") Nominal lhs1 structMeta
              coStrip = mkStockCo (PluginProv "stock") Representational structMeta structBare
              castDn = mkSubCo (mkAppCo coRep (mkNomReflCo aTy))
                         `mkTransCo` mkAppCo coStrip (mkNomReflCo aTy)   -- Rep1..a ~R structBare a
              castUp = mkSymCo castDn
              -- balanced :*: VALUE for one constructor (over the leaf values/types)
              buildV [(v, t)] = (v, t)
              buildV vs = let (l, r) = splitAt (length vs `div` 2) vs
                              (lv, lt) = buildV l ; (rv, rt) = buildV r
                          in ( mkCoreConApps prodDc [Type kTy, Type lt, Type rt, Type aTy, lv, rv]
                             , prodTy lt rt )
              prodValOf con fis
                | null con  = mkCoreConApps u1Dc [Type kTy, Type aTy]
                | otherwise = fst (buildV [ (wrap (Var fi), lt) | ((lt, wrap, _, _), fi) <- zip con fis ])
              -- balanced :+: injectors, by the bare struct types
              injectors [con] = ([id], bareCon con)
              injectors cs =
                let (l, r) = splitAt (length cs `div` 2) cs
                    (li, lt) = injectors l ; (ri, rt) = injectors r
                    wrapL v = mkCoreConApps l1Dc [Type kTy, Type lt, Type rt, Type aTy, v]
                    wrapR v = mkCoreConApps r1Dc [Type kTy, Type lt, Type rt, Type aTy, v]
                in (map (wrapL .) li ++ map (wrapR .) ri, sumTy lt rt)
              (injs, _) = injectors classified

          vId <- freshId (mkAppTy wrappedTy aTy) "v"
          cbV <- freshId innerA "cb"
          fromAlts <- forM (zip3 dcons classified injs) \(dc, con, inj) -> do
            fis <- zipWithM (\n ft -> freshId ft ("f" ++ show n)) [0 :: Int ..] (fieldsOf dc)
            pure (Alt (DataAlt dc) fis (Cast (inj (prodValOf con fis)) castUp))
          let fromImpl = Lam atv (Lam vId
                           (Case (Cast (Var vId) (coAt aTy)) cbV (mkAppTy lhs1 aTy) fromAlts))

          rId <- freshId (mkAppTy lhs1 aTy) "r"
          let destruct scr [(_, _, unwrap, _)] = pure ([unwrap scr], id)
              destruct scr con = do
                let (lc, rc) = splitAt (length con `div` 2) con
                    lt = bareCon lc ; rt = bareCon rc
                lv <- freshId (mkAppTy lt aTy) "l"
                rv <- freshId (mkAppTy rt aTy) "rr"
                cb <- freshId (mkAppTy (prodTy lt rt) aTy) "pc"
                (lfs, lw) <- destruct (Var lv) lc
                (rfs, rw) <- destruct (Var rv) rc
                pure (lfs ++ rfs, \body -> Case scr cb (mkAppTy wrappedTy aTy)
                        [Alt (DataAlt prodDc) [lv, rv] (lw (rw body))])
              rebuildCon scr con dc
                | null con  = pure (Cast (conAppAt innerA dc []) (mkSymCo (coAt aTy)))
                | otherwise = do (fields, wrap) <- destruct scr con
                                 pure (wrap (Cast (conAppAt innerA dc fields) (mkSymCo (coAt aTy))))
              destructSum scr [con] [dc] = rebuildCon scr con dc
              destructSum scr cs    dcs  = do
                let h = length cs `div` 2
                    (lc, rc) = splitAt h cs ; (ldc, rdc) = splitAt h dcs
                    lt = case lc of { [c] -> bareCon c; _ -> foldBal sumTy (map bareCon lc) }
                    rt = case rc of { [c] -> bareCon c; _ -> foldBal sumTy (map bareCon rc) }
                lv <- freshId (mkAppTy lt aTy) "sl"
                rv <- freshId (mkAppTy rt aTy) "sr"
                cb <- freshId (mkAppTy (sumTy lt rt) aTy) "sc"
                lb <- destructSum (Var lv) lc ldc
                rb <- destructSum (Var rv) rc rdc
                pure (Case scr cb (mkAppTy wrappedTy aTy)
                        [Alt (DataAlt l1Dc) [lv] lb, Alt (DataAlt r1Dc) [rv] rb])
          toBody <- destructSum (Cast (Var rId) castDn) classified dcons
          let toImpl = Lam atv (Lam rId toBody)
              -- Generic1 is poly-kinded: its dictionary constructor takes the
              -- kind argument before the type argument.
              dict = mkApps (Var (dataConWorkId (classDataCon cls)))
                       [Type liftedTypeKind, Type wrappedTy, fromImpl, toImpl]
          pure (Just (EvExpr dict, fieldWanteds))
    _ -> pure Nothing
  where (realF, mMods) = peelOverride1 gen f

-- | Variance of an occurrence of the type parameter.
