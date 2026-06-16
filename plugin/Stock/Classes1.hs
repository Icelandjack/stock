{-# LANGUAGE CPP #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wno-x-partial -Wno-incomplete-uni-patterns -Wno-unused-imports #-}

-- | The lifted @Data.Functor.Classes@ hierarchy over @Stock1 F@: @Eq1@,
-- @Ord1@, @Show1@, @Read1@.  Each is the structural synthesizer of its unlifted twin
-- (@Eq@\/@Ord@) with one change: a field that /is/ the functor parameter @a@
-- is handled by the supplied function argument (@liftEq@'s @eq@,
-- @liftCompare@'s @cmp@) instead of the field's own instance, and a field of
-- shape @H a@ recurses through @H@'s own lifted method.
--
-- Since base-4.18 these classes carry a /quantified/ superclass — @Eq1 f@
-- requires @forall a. Eq a => Eq (f a)@ and @Ord1 f@ likewise for @Ord@ — so
-- we synthesize those superclass dictionaries too (from the same lifted
-- method, instantiated at @eq = (==)@ \/ @cmp = compare@).
module Stock.Classes1 (synthEq1, synthOrd1, synthShow1, synthRead1) where

import GHC.Plugins hiding (TcPlugin)
import GHC.Tc.Plugin
import GHC.Tc.Types.Constraint
#if MIN_VERSION_ghc(9,12,0)
import GHC.Tc.Types.CtLoc (CtLoc)
#else
import GHC.Tc.Types.Constraint (CtLoc)
#endif
import GHC.Tc.Types.Evidence
import GHC.Core.Class (Class, className, classSCTheta, classSCSelId)
import GHC.Core.Predicate (mkClassPred, isClassPred)
import GHC.Builtin.Names (eqClassName, ordClassName, appendName, eqStringName)
import GHC.Core.Multiplicity (scaledThing)
import GHC.Core.TyCo.Rep (UnivCoProvenance(PluginProv))
import Stock.Compat (gHC_INTERNAL_SHOW, gHC_INTERNAL_READ, gHC_INTERNAL_LIST)
import Control.Monad (forM, zipWithM)
import Stock.Derive (classMethod, castInto)
import Stock.Internal  -- 'castReshape' (skip-Refl cast) comes from here
import Data.Maybe (fromJust)

-- ----- the structural lifted methods --------------------------------------

-- | Build the @liftEq@ method body @\\\@a \@b eq fa fb -> …@ for @Stock1 F@,
-- or 'Nothing' if some field shape is unsupported.  Returns the field-instance
-- wanteds (@Eq H@ for constant fields, @Eq1 H@ for @H a@ fields).
buildLiftEq :: GenEnv -> Class -> Class -> CtLoc -> Type -> Type
            -> TcPluginM (Maybe (CoreExpr, [Ct]))
buildLiftEq gen eq1Cls eqCls loc wrappedTy f =
  case (geStock1 gen, tyConAppTyCon_maybe realF) of
    (Just st1Tc, Just fTc) -> do
      let liftEqSel = classMethod "liftEq" eq1Cls
          eqSel     = classMethod "==" eqCls
          fixed     = tyConAppArgs realF
          true_     = Var (dataConWorkId trueDataCon)
          false_    = Var (dataConWorkId falseDataCon)
          coAt t    = coDown1 gen st1Tc wrappedTy f realF t
      aTv <- freshTyVar "a" ; bTv <- freshTyVar "b"
      let aTy = mkTyVarTy aTv ; bTy = mkTyVarTy bTv
          eqFnTy = mkVisFunTyMany aTy (mkVisFunTyMany bTy boolTy)
      eqId <- freshId eqFnTy "eq"
      faId <- freshId (mkAppTy wrappedTy aTy) "fa"
      fbId <- freshId (mkAppTy wrappedTy bTy) "fb"

      -- one field-pair becomes a Bool: the parameter via @eq@, a constant via
      -- its own @(==)@, an @H a@ field via @liftEq \@m eq@ (the @Override1@
      -- modifier @m@; the field values cast @h ~R m@ via @coB@).
      let fieldEq i ft x y = interpField eqCls eq1Cls aTv aTy loc (override1Mod gen mMods i) Walk
            { wLeaf  = Var eqId
            , wLift  = \ev h elt inner -> mkApps (Var liftEqSel)
                [ Type h, ctEvExpr ev, Type (substTyWith [aTv] [aTy] elt)
                , Type (substTyWith [aTv] [bTy] elt), inner ]
            , wConst = \ev t -> mkApps (Var eqSel) [Type t, ctEvExpr ev, Var x, Var y]
            , wApply = \op _ coB -> mkApps op [castReshape (Var x) (coB aTy), castReshape (Var y) (coB bTy)]
            } ft
          -- conjunction with short-circuit: @case e of False -> False; True -> …@
          conj []         = pure true_
          conj (e : more) = do
            rest <- conj more
            scr  <- freshId boolTy "c"
            pure (Case e scr boolTy [ Alt (DataAlt falseDataCon) [] false_
                                    , Alt (DataAlt trueDataCon)  [] rest ])

      mBody <- zipLift2 fTc fixed coAt aTy bTy boolTy faId fbId
                        (\_ _ -> false_) conj fieldEq
      pure (fmap (\(body, ws) -> (mkLams [aTv, bTv, eqId, faId, fbId] body, ws)) mBody)
    _ -> pure Nothing
  where (realF, mMods) = peelOverride1 gen f

-- | Build the @liftCompare@ method body for @Stock1 F@: tag order between
-- constructors, lexicographic within.  Wanteds: @Ord H@ \/ @Ord1 H@ per field.
buildLiftCompare :: GenEnv -> Class -> Class -> CtLoc -> Type -> Type
                 -> TcPluginM (Maybe (CoreExpr, [Ct]))
buildLiftCompare gen ord1Cls ordCls loc wrappedTy f =
  case (geStock1 gen, tyConAppTyCon_maybe realF) of
    (Just st1Tc, Just fTc) -> do
      let liftCmpSel = classMethod "liftCompare" ord1Cls
          cmpSel     = classMethod "compare" ordCls
          fixed      = tyConAppArgs realF
          ordTy      = mkTyConTy orderingTyCon
          [ltC, eqC, gtC] = tyConDataCons orderingTyCon
          ltE = Var (dataConWorkId ltC)
          eqE = Var (dataConWorkId eqC)
          gtE = Var (dataConWorkId gtC)
          coAt t = coDown1 gen st1Tc wrappedTy f realF t
      aTv <- freshTyVar "a" ; bTv <- freshTyVar "b"
      let aTy = mkTyVarTy aTv ; bTy = mkTyVarTy bTv
          cmpFnTy = mkVisFunTyMany aTy (mkVisFunTyMany bTy ordTy)
      cmpId <- freshId cmpFnTy "cmp"
      faId  <- freshId (mkAppTy wrappedTy aTy) "fa"
      fbId  <- freshId (mkAppTy wrappedTy bTy) "fb"

      -- one field-pair becomes an Ordering: the parameter via @cmp@, a constant
      -- via its own @compare@, an @H a@ field via @liftCompare \@m cmp@.
      let fieldCmp i ft x y = interpField ordCls ord1Cls aTv aTy loc (override1Mod gen mMods i) Walk
            { wLeaf  = Var cmpId
            , wLift  = \ev h elt inner -> mkApps (Var liftCmpSel)
                [ Type h, ctEvExpr ev, Type (substTyWith [aTv] [aTy] elt)
                , Type (substTyWith [aTv] [bTy] elt), inner ]
            , wConst = \ev t -> mkApps (Var cmpSel) [Type t, ctEvExpr ev, Var x, Var y]
            , wApply = \op _ coB -> mkApps op [castReshape (Var x) (coB aTy), castReshape (Var y) (coB bTy)]
            } ft
          -- lexicographic: @case e of LT -> LT; GT -> GT; EQ -> …@
          lexCmp []         = pure eqE
          lexCmp (e : more) = do
            rest <- lexCmp more
            scr  <- freshId ordTy "o"
            pure (Case e scr ordTy [ Alt (DataAlt ltC) [] ltE
                                   , Alt (DataAlt eqC) [] rest
                                   , Alt (DataAlt gtC) [] gtE ])

      mBody <- zipLift2 fTc fixed coAt aTy bTy ordTy faId fbId
                        (\i j -> if i < j then ltE else gtE) lexCmp fieldCmp
      pure (fmap (\(body, ws) -> (mkLams [aTv, bTv, cmpId, faId, fbId] body, ws)) mBody)
    _ -> pure Nothing
  where (realF, mMods) = peelOverride1 gen f

-- ----- quantified-superclass dictionaries ---------------------------------

-- | A quantified superclass @forall a. C a => D (g a)@ as evidence: bind @a@
-- and its @C a@ dictionary, then build the @D (g a)@ dictionary.  The callback
-- receives @a@, @g a@, and the @C a@ dictionary binder.  This is the shape
-- shared by every @Eq1@\/@Ord1@\/@Show1@\/@Read1@ superclass.
buildQuantSuper :: Class -> Type
                -> (Type -> Type -> Id -> TcPluginM CoreExpr)
                -> TcPluginM CoreExpr
buildQuantSuper baseCls gTy mk = do
  aTv <- freshTyVar "a"
  let aTy = mkTyVarTy aTv ; gaTy = mkAppTy gTy aTy
  dA <- freshId (mkClassPred baseCls [aTy]) "d"
  inner <- mk aTy gaTy dA
  pure (mkLams [aTv, dA] inner)

-- | @Eq T@ dictionary from an equality test @eqImpl :: T -> T -> Bool@.
mkEqDict :: Class -> Type -> CoreExpr -> TcPluginM CoreExpr
mkEqDict eqCls tT eqImpl = do
  x <- freshId tT "x" ; y <- freshId tT "y" ; s <- freshId boolTy "c"
  let neq = mkLams [x, y] (Case (mkApps eqImpl [Var x, Var y]) s boolTy
              [ Alt (DataAlt falseDataCon) [] (Var (dataConWorkId trueDataCon))
              , Alt (DataAlt trueDataCon)  [] (Var (dataConWorkId falseDataCon)) ])
  pure (mkClassDict eqCls tT [eqImpl, neq])

-- | The quantified @Eq@ superclass @forall a. Eq a => Eq (g a)@, built from
-- the @liftEq@ method instantiated at @eq = (==) \@a@.
buildQuantEq :: Class -> Type -> CoreExpr -> TcPluginM CoreExpr
buildQuantEq eqCls gTy liftEqImpl =
  buildQuantSuper eqCls gTy \aTy gaTy dEqA -> do
    let eqA  = mkApps (Var (classMethod "==" eqCls)) [Type aTy, Var dEqA]
        eqGA = mkApps liftEqImpl [Type aTy, Type aTy, eqA]
    mkEqDict eqCls gaTy eqGA

-- | The quantified @Ord@ superclass @forall a. Ord a => Ord (g a)@, built from
-- @liftCompare@ (instantiated at @compare \@a@) plus the @Eq (g a)@ it needs as
-- its own superclass (from @liftEq@ instantiated at the @Eq a@ inside @Ord a@).
buildQuantOrd :: Class -> Class -> Type -> CoreExpr -> CoreExpr -> TcPluginM CoreExpr
buildQuantOrd ordCls eqCls gTy liftCmpImpl liftEqImpl =
  buildQuantSuper ordCls gTy \aTy gaTy dOrdA -> do
    let cmpA  = mkApps (Var (classMethod "compare" ordCls)) [Type aTy, Var dOrdA]
        cmpGA = mkApps liftCmpImpl [Type aTy, Type aTy, cmpA]
        dEqA  = mkApps (Var (classSCSelId ordCls 0)) [Type aTy, Var dOrdA]  -- Eq a from Ord a
        eqA   = mkApps (Var (classMethod "==" eqCls)) [Type aTy, dEqA]
        eqGA  = mkApps liftEqImpl [Type aTy, Type aTy, eqA]
    eqDictGa <- mkEqDict eqCls gaTy eqGA
    recDictWith ordCls gaTy [eqDictGa] [(0, cmpGA)]

-- ----- the two entry points -----------------------------------------------

synthEq1 :: GenEnv -> Class -> CtLoc -> Type -> Type
         -> TcPluginM (Maybe (EvTerm, [Ct]))
synthEq1 gen eq1Cls loc wrappedTy f = do
  eqCls <- tcLookupClass eqClassName
  m <- buildLiftEq gen eq1Cls eqCls loc wrappedTy f
  case m of
    Nothing -> pure Nothing
    Just (liftEqImpl, ws) -> do
      supers <- forM (classSCTheta eq1Cls) \_ -> buildQuantEq eqCls wrappedTy liftEqImpl
      pure (Just (EvExpr (mkClassDict eq1Cls wrappedTy (supers ++ [liftEqImpl])), ws))

-- ----- Show1 --------------------------------------------------------------

-- | Build @liftShowsPrec@'s body @\\\@a sp sl d v -> …@ for @Stock1 F@,
-- mirroring derived @showsPrec@ (prefix / infix / record / nullary, with the
-- @d > prec@ parenthesisation) but rendering the parameter field with the
-- supplied @sp@, an @H a@ field with @liftShowsPrec \@H sp sl@ (a @Show1 H@
-- wanted), and any other field with its own @showsPrec@ (a @Show H@ wanted).
buildLiftShowsPrec :: GenEnv -> Class -> Class -> Class -> Id -> CtLoc -> Type -> Type
                   -> TcPluginM (Maybe (CoreExpr, [Ct]))
buildLiftShowsPrec gen show1Cls showCls ordCls appendId loc wrappedTy f =
  case (geStock1 gen, tyConAppTyCon_maybe realF) of
    (Just st1Tc, Just fTc) -> do
      let liftSpSel    = classMethod "liftShowsPrec" show1Cls
          liftSlSel    = classMethod "liftShowList"  show1Cls
          showsPrecSel = classMethod "showsPrec" showCls
          gtSel        = classMethod ">" ordCls
          fixed        = tyConAppArgs realF
          dcons        = tyConDataCons fTc
          showSTy      = mkVisFunTyMany stringTy stringTy
          coAt t       = coDown1 gen st1Tc wrappedTy f realF t
          cons c t     = mkCoreConApps consDataCon [Type charTy, c, t]
          append s t   = mkApps (Var appendId) [Type charTy, s, t]
          str s        = unsafeTcPluginTcM (mkStringExprFS (fsLit s))
      ordIntEv <- newWanted loc (mkClassPred ordCls [intTy])
      let ordIntDict = ctEvExpr ordIntEv
      aTv <- freshTyVar "a"
      let aTy    = mkTyVarTy aTv
          innerA = mkTyConApp fTc (fixed ++ [aTy])
          spTy   = mkVisFunTyMany intTy (mkVisFunTyMany aTy showSTy)
          slTy   = mkVisFunTyMany (mkListTy aTy) showSTy
      spId <- freshId spTy "sp" ; slId <- freshId slTy "sl"
      dId  <- freshId intTy "d" ; vId  <- freshId (mkAppTy wrappedTy aTy) "v"

      -- one field becomes a precedence-parameterised ShowS renderer (@p -> ShowS@):
      -- the parameter via @sp@, a constant via its own @showsPrec@, an @H a@
      -- field via @liftShowsPrec \@H sp sl@.
      let mkRenderer i ftA xi = interpField showCls show1Cls aTv aTy loc (override1Mod gen mMods i) Walk
            { wLeaf  = (Var spId, Var slId)
            , wLift  = \ev h elt (sp, sl) ->
                ( mkApps (Var liftSpSel) [Type h, ctEvExpr ev, Type (substTyWith [aTv] [aTy] elt), sp, sl]
                , mkApps (Var liftSlSel) [Type h, ctEvExpr ev, Type (substTyWith [aTv] [aTy] elt), sp, sl] )
            , wConst = \ev t -> \p -> mkApps (Var showsPrecSel)
                                    [Type t, ctEvExpr ev, mkUncheckedIntExpr p, Var xi]
            , wApply = \(sp, _) _ coB -> \p -> mkApps sp
                                    [ mkUncheckedIntExpr p, castReshape (Var xi) (coB aTy) ]
            } ftA

      mAltWss <- forM dcons \dc -> do
        let fts    = map scaledThing (dataConInstOrigArgTys dc (fixed ++ [aTy]))
            name   = occNameString (getOccName dc)
            labels = map (occNameString . nameOccName . flSelector) (dataConFieldLabels dc)
        nameStr <- str name
        xs      <- zipWithM (\n ft -> freshId ft ("x" ++ show n)) [0 :: Int ..] fts
        rest    <- freshId stringTy "r"
        gtBndr  <- freshId boolTy "p"
        prec    <- conPrec dc
        mRends  <- sequence (zipWith3 mkRenderer [0 :: Int ..] fts xs)
        case sequence mRends of
          Nothing    -> pure Nothing
          Just rends -> do
            let (renderers, wss) = unzip rends
                parenAt thr mk t =
                  Case (mkApps (Var gtSel) [Type intTy, ordIntDict, Var dId, mkUncheckedIntExpr thr])
                       gtBndr stringTy
                    [ Alt (DataAlt falseDataCon) [] (mk t)
                    , Alt (DataAlt trueDataCon)  []
                        (cons (mkCharExpr '(') (mk (cons (mkCharExpr ')') t))) ]
                goPrefix t = foldr (\r acc -> cons (mkCharExpr ' ') (App (r 11) acc)) t renderers
                prefixBody t = append nameStr (goPrefix t)
            body <-
              if dataConIsInfix dc
                then do
                  opStr <- str (" " ++ name ++ " ")
                  let [l, r] = renderers
                      mk t = App (l (prec + 1)) (append opStr (App (r (prec + 1)) t))
                  pure (parenAt prec mk (Var rest))
                else if not (null labels)
                  then do
                    openB <- str " {"; eqB <- str " = "; commaB <- str ", "; closeB <- str "}"
                    lblStrs <- mapM str labels
                    let recF = zip lblStrs renderers
                        goRec [(lbl, r)] c    = append lbl (append eqB (App (r 0) (append closeB c)))
                        goRec ((lbl, r) : m) c = append lbl (append eqB (App (r 0) (append commaB (goRec m c))))
                        goRec [] c            = append closeB c
                        recBody t = append nameStr (append openB (goRec recF t))
                    pure (parenAt 10 recBody (Var rest))
                  else if null xs
                    then pure (append nameStr (Var rest))
                    else pure (parenAt 10 prefixBody (Var rest))
            pure (Just (Alt (DataAlt dc) xs (Lam rest body), concat wss))

      case sequence mAltWss of
        Nothing     -> pure Nothing
        Just altWss -> do
          let (alts, wss) = unzip altWss
          cb <- freshId innerA "cb"
          let spImpl = mkLams [aTv, spId, slId, dId, vId]
                (destructInner fTc (fixed ++ [aTy]) (Cast (Var vId) (coAt aTy)) cb showSTy alts)
          pure (Just (spImpl, mkNonCanonical ordIntEv : concat wss))
    _ -> pure Nothing
  where (realF, mMods) = peelOverride1 gen f

-- | A @Show T@ dictionary from a @showsPrec@ implementation.
mkShowDict :: Class -> Id -> Type -> CoreExpr -> TcPluginM CoreExpr
mkShowDict showCls showList__Id tT spImpl = do
  vS <- freshId tT "v" ; vL <- freshId tT "v"
  let showImpl     = Lam vS (mkApps spImpl [mkUncheckedIntExpr 0, Var vS, mkNilExpr charTy])
      sp0          = Lam vL (mkApps spImpl [mkUncheckedIntExpr 0, Var vL])
      showListImpl = mkApps (Var showList__Id) [Type tT, sp0]
  pure (mkClassDict showCls tT [spImpl, showImpl, showListImpl])

-- | The quantified @Show@ superclass @forall a. Show a => Show (g a)@, from
-- @liftShowsPrec@ instantiated at @sp = showsPrec \@a@, @sl = showList \@a@.
buildQuantShow :: Class -> Id -> Type -> CoreExpr -> TcPluginM CoreExpr
buildQuantShow showCls showList__Id gTy liftSpImpl =
  buildQuantSuper showCls gTy \aTy gaTy dShowA -> do
    let spA  = mkApps (Var (classMethod "showsPrec" showCls))   [Type aTy, Var dShowA]
        slA  = mkApps (Var (classMethod "showList" showCls))     [Type aTy, Var dShowA]
        spGA = mkApps liftSpImpl [Type aTy, spA, slA]
    mkShowDict showCls showList__Id gaTy spGA

synthShow1 :: GenEnv -> Class -> CtLoc -> Type -> Type
           -> TcPluginM (Maybe (EvTerm, [Ct]))
synthShow1 gen show1Cls loc wrappedTy f = do
  showCls      <- lookupOrig gHC_INTERNAL_SHOW (mkTcOcc "Show") >>= tcLookupClass
  ordCls       <- tcLookupClass ordClassName
  appendId     <- tcLookupId appendName
  showList__Id <- lookupOrig gHC_INTERNAL_SHOW (mkVarOcc "showList__") >>= tcLookupId
  m <- buildLiftShowsPrec gen show1Cls showCls ordCls appendId loc wrappedTy f
  case m of
    Nothing -> pure Nothing
    Just (liftSpImpl, ws) -> do
      supers <- forM (classSCTheta show1Cls) \_ ->
                  buildQuantShow showCls showList__Id wrappedTy liftSpImpl
      dict <- recDictWith show1Cls wrappedTy supers [(0, liftSpImpl)]
      pure (Just (EvExpr dict, ws))

synthOrd1 :: GenEnv -> Class -> CtLoc -> Type -> Type
          -> TcPluginM (Maybe (EvTerm, [Ct]))
synthOrd1 gen ord1Cls loc wrappedTy f = do
  ordCls  <- tcLookupClass ordClassName
  eqCls   <- tcLookupClass eqClassName
  mEq1Cls <- lookupClassMaybe "Data.Functor.Classes" "Eq1"
  case mEq1Cls of
    Nothing -> pure Nothing
    Just eq1Cls -> do
      mCmp <- buildLiftCompare gen ord1Cls ordCls loc wrappedTy f
      mEq  <- buildLiftEq gen eq1Cls eqCls loc wrappedTy f
      case (mCmp, mEq) of
        (Just (liftCmpImpl, wsC), Just (liftEqImpl, wsE)) -> do
          -- the full Eq1 superclass dictionary (with its own quantified Eq super)
          eqSupers <- forM (classSCTheta eq1Cls) \_ -> buildQuantEq eqCls wrappedTy liftEqImpl
          let eq1Dict = mkClassDict eq1Cls wrappedTy (eqSupers ++ [liftEqImpl])
          -- Ord1's superclasses, in declaration order: the plain @Eq1 f@ and the
          -- quantified @forall a. Ord a => Ord (f a)@.
          supers <- forM (classSCTheta ord1Cls) \p ->
            if isClassPred p
              then pure eq1Dict
              else buildQuantOrd ordCls eqCls wrappedTy liftCmpImpl liftEqImpl
          dict <- recDictWith ord1Cls wrappedTy supers [(0, liftCmpImpl)]
          pure (Just (EvExpr dict, wsC ++ wsE))
        _ -> pure Nothing

-- ----- Read1 --------------------------------------------------------------

-- | Build @liftReadPrec@'s body @\@a rp rl -> ...@ for @Stock1 F@, by reusing
-- the shared GHC-faithful @readPrec@ assembler ('buildReadPrecBody'): the
-- parameter field reads with the supplied @rp@, a constant field with its own
-- @readPrec@, and an @H a@ field with @liftReadPrec \@H rp rl@ (cast back to the
-- real field type when @Override1@ reshapes the functor).
buildLiftReadPrec :: GenEnv -> Class -> Class -> CtLoc -> Type -> Type
                  -> TcPluginM (Maybe (CoreExpr, [Ct]))
buildLiftReadPrec gen read1Cls readCls loc wrappedTy f =
  case (geStock1 gen, tyConAppTyCon_maybe realF) of
    (Just st1Tc, Just fTc) -> do
      (env, monadCt) <- lookupReadPrecEnv loc
      let liftRpSel   = classMethod "liftReadPrec"     read1Cls
          liftRlSel   = classMethod "liftReadListPrec" read1Cls
          readPrecSel = classMethod "readPrec" readCls
          fixed       = tyConAppArgs realF
          dcons       = tyConDataCons fTc
          coAt t      = coDown1 gen st1Tc wrappedTy f realF t
          rpcOf t     = mkTyConApp (rpReadPrecTc env) [t]
      aTv <- freshTyVar "a"
      let aTy    = mkTyVarTy aTv
          innerA = mkTyConApp fTc (fixed ++ [aTy])
          gaTy   = mkAppTy wrappedTy aTy
          toWrapped e = Cast e (mkSymCo (coAt aTy))
      rpId <- freshId (rpcOf aTy) "rp"
      rlId <- freshId (rpcOf (mkListTy aTy)) "rl"
      -- each field's raw reader, plus the coercion casting the read type back to
      -- the real field type (Refl unless Override1 reshaped an @H a@ field).
      let mkFieldReader i ftA = interpField readCls read1Cls aTv aTy loc (override1Mod gen mMods i) Walk
            { wLeaf  = (Var rpId, Var rlId)
            , wLift  = \ev h elt (rp, rl) ->
                ( mkApps (Var liftRpSel) [Type h, ctEvExpr ev, Type (substTyWith [aTv] [aTy] elt), rp, rl]
                , mkApps (Var liftRlSel) [Type h, ctEvExpr ev, Type (substTyWith [aTv] [aTy] elt), rp, rl] )
            , wConst = \ev t -> (t, mkApps (Var readPrecSel) [Type t, ctEvExpr ev], mkReflCo Representational t)
            , wApply = \(rp, _) opTy coB ->
                ( opTy, rp
                , if isReflCo (coB aTy) then mkReflCo Representational opTy else mkSymCo (coB aTy) )
            } ftA
      mConsWss <- forM dcons \dc -> do
        let fts = map scaledThing (dataConInstOrigArgTys dc (fixed ++ [aTy]))
        mRdrs <- zipWithM mkFieldReader [0 :: Int ..] fts
        case sequence mRdrs of
          Nothing    -> pure Nothing
          Just trips -> let (rdrs, wss) = unzip trips in pure (Just (dc, rdrs, concat wss))
      case sequence mConsWss of
        Nothing   -> pure Nothing
        Just cons -> do
          let consForAsm = [ (dc, [ (ty, rd) | (ty, rd, _) <- rdrs ]) | (dc, rdrs, _) <- cons ]
              castMap    = [ (getUnique dc, [ co | (_, _, co) <- rdrs ]) | (dc, rdrs, _) <- cons ]
              mkConVal dc argIds =
                let castCos = fromJust (lookup (getUnique dc) castMap)
                in toWrapped (conAppAt innerA dc (zipWith (\a c -> castInto (Var a) c) argIds castCos))
          body <- buildReadPrecBody env gaTy mkConVal consForAsm
          let liftRpImpl = mkLams [aTv, rpId, rlId] body
          pure (Just (liftRpImpl, monadCt : concatMap (\(_, _, w) -> w) cons))
    _ -> pure Nothing
  where (realF, mMods) = peelOverride1 gen f

-- | A @Read T@ dictionary from a @readPrec@ implementation (other methods come
-- from the class defaults via a recursive dictionary).
mkReadDict :: Class -> Type -> CoreExpr -> TcPluginM CoreExpr
mkReadDict readCls tT rpImpl = recDictWith readCls tT [] [(2, rpImpl)]

-- | The quantified @Read@ superclass @forall a. Read a => Read (g a)@, from
-- @liftReadPrec@ instantiated at @rp = readPrec \@a@, @rl = readListPrec \@a@.
buildQuantRead :: Class -> Type -> CoreExpr -> TcPluginM CoreExpr
buildQuantRead readCls gTy liftRpImpl =
  buildQuantSuper readCls gTy \aTy gaTy dReadA -> do
    let rpA  = mkApps (Var (classMethod "readPrec" readCls))     [Type aTy, Var dReadA]
        rlpA = mkApps (Var (classMethod "readListPrec" readCls)) [Type aTy, Var dReadA]
        rpGA = mkApps liftRpImpl [Type aTy, rpA, rlpA]
    mkReadDict readCls gaTy rpGA

synthRead1 :: GenEnv -> Class -> CtLoc -> Type -> Type
           -> TcPluginM (Maybe (EvTerm, [Ct]))
synthRead1 gen read1Cls loc wrappedTy f = do
  readCls <- lookupOrig gHC_INTERNAL_READ (mkTcOcc "Read") >>= tcLookupClass
  m <- buildLiftReadPrec gen read1Cls readCls loc wrappedTy f
  case m of
    Nothing -> pure Nothing
    Just (liftRpImpl, ws) -> do
      supers <- forM (classSCTheta read1Cls) \_ -> buildQuantRead readCls wrappedTy liftRpImpl
      dict <- recDictWith read1Cls wrappedTy supers [(2, liftRpImpl)]
      pure (Just (EvExpr dict, ws))

