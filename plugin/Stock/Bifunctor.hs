{-# LANGUAGE CPP #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DerivingVia #-}
{-# OPTIONS_GHC -Wno-x-partial -Wno-incomplete-uni-patterns -Wno-unused-imports #-}
-- | All @Stock2@ synthesizers (classes over a two-parameter type @P@):
--
--   * @Bifunctor@ \/ @Bifoldable@ — map\/fold the last two parameters.
--   * @Eq2@ \/ @Ord2@ \/ @Show2@ \/ @Read2@ — the lifted "two-parameter"
--     'Data.Functor.Classes' (mirroring "Stock.Classes1" one level up).
--   * @Bitraversable@ — synthesized directly (usable at the wrapper \/ via the
--     one-liner; a bare @deriving via@ can't, abstract-applicative role).
--   * @Category@ — pointwise @id@\/@(.)@ for a single-constructor product
--     whose fields are each a 'Control.Category.Category' in the two params.
--
-- Field shapes: each of the two parameters, constants, or a (covariant) functor
-- applied to one (the flat 'classifyBiField'); @Bifunctor@ also goes through the
-- n-ary variance engine for nested\/self-applied fields like @Either a b@.
module Stock.Bifunctor where
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
import GHC.Core.Class (Class, className, classMethods, classOpItems, classTyCon, classTyVars, classSCTheta)
import GHC.Core.Predicate (classifyPredType, Pred(ClassPred), mkClassPred)
import GHC.Core.TyCo.Subst (substTy, emptySubst)
import GHC.Builtin.Types (orderingTyCon)
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
                         , semigroupClassName, applicativeClassName, traversableClassName )
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
import Control.Monad (zipWithM)
import Data.List (zip4, zip5, zipWith4)
import Data.Maybe (listToMaybe)
import Stock.Internal
-- field reshape: 'reshapeCo' (@h t ~R m t@) + 'castReshape' live in "Stock.Internal".

data BiField
  = BFA | BFB                 -- ^ the field /is/ @a@ resp. @b@
  | BFConst                   -- ^ mentions neither
  | BFFoldA Type | BFFoldB Type   -- ^ @h a@ / @h b@ (covariant, @h@ over one param)

classifyBiField :: TyVar -> TyVar -> Type -> Type -> Type -> Maybe BiField
classifyBiField atv btv aTy bTy ft
  | ft `eqType` aTy                            = Just BFA
  | ft `eqType` bTy                            = Just BFB
  | not (inFt atv) && not (inFt btv)           = Just BFConst
  | Just (h, larg) <- splitAppTy_maybe ft
  , larg `eqType` bTy, clean h                 = Just (BFFoldB h)
  | Just (h, larg) <- splitAppTy_maybe ft
  , larg `eqType` aTy, clean h                 = Just (BFFoldA h)
  | otherwise                                  = Nothing
  where inFt v = v `elemVarSet` tyCoVarsOfType ft
        clean h = not (atv `elemVarSet` tyCoVarsOfType h)
               && not (btv `elemVarSet` tyCoVarsOfType h)

-- | For @Category@: a field must be exactly @h a b@ — a (poly-kinded)
-- two-parameter constructor @h@ applied to /both/ datatype parameters, in
-- order.  @h@ is the per-field @Category@ (e.g. @(->)@, @(:~:)@, @Kleisli m@,
-- or a @Basic m@ from an @Override@).  Returns @h@ (which must not mention the
-- parameters).  Constants and one-parameter shapes have no @id@\/@(.)@, so they
-- yield 'Nothing' and the whole synthesis bails.
classifyCatField :: TyVar -> TyVar -> Type -> Maybe Type
classifyCatField atv btv ft
  | Just (hp, qarg) <- splitAppTy_maybe ft
  , qarg `eqType` mkTyVarTy btv
  , Just (h, parg)  <- splitAppTy_maybe hp
  , parg `eqType` mkTyVarTy atv
  , not (atv `elemVarSet` tyCoVarsOfType h)
  , not (btv `elemVarSet` tyCoVarsOfType h)  = Just h
  | otherwise                                = Nothing

-- | How one field of a @Category@ product is handled: it is a @Category@ @h@
-- (with a @realFt(t1,t2) ~R h t1 t2@ coercion builder — 'Refl' unless reshaped
-- by an @Override2@), or a /constant/ @m@ handled Const-style via its @Monoid@
-- (@id = mempty@, @(.) = (\<>)@) — the automatic, @Basic@-free version.
data CatFld = CatF Type (Type -> Type -> Coercion) | MonF Type

-- | Synthesize @Category (Stock2 P)@ for a single-constructor product whose
-- every field is a @Category@ in the two parameters (shape @h a b@).  @id@ and
-- @(.)@ are pointwise — @id = P id .. id@, @P g.. . P h.. = P (g.h)..@ — exactly
-- the @Semigroup@ pattern lifted to two parameters.  @Category@ is poly-kinded
-- (@cat :: k -> k -> Type@), so the kind @k@ (here always @Type@) is threaded
-- through the dictionary and through every @id@\/@(.)@ at the field categories.
--
-- @P@ may be wrapped in @Override2 cfg P@: then each positional modifier @m@
-- reshapes its field to @m a b@ (the modifier applied to both parameters), with
-- a per-field @realFt ~R m a b@ coercion, so fields that are not yet categories
-- (an @Int@, an @a -> Maybe b@) become ones (@Basic (Sum Int)@, @Kleisli Maybe@).
synthCategory :: GenEnv -> Class -> CtLoc -> Type -> Type -> TcPluginM (Maybe (EvTerm, [Ct]))
synthCategory gen catCls loc wrappedTy p0 =
  case geStock2 gen of
    Just st2Tc
      -- peel an optional @Override2 cfg P@: @realP@ is the genuine constructor,
      -- @mMods@ the per-field modifiers (Keep-filled).  Use the shared decoder
      -- ('peelOverride2With' -> 'decodeOvCfg') so it accepts the field-keyed
      -- forms (@Con at i via M@, @name via M@) and not only the dense
      -- positional @'[ '[ .. ] ]@ list.
      | let (realP, mMods) = peelOverride2With (ovTcsGen "Override2" gen) p0
      , Just pTc <- tyConAppTyCon_maybe realP
      , [dc] <- tyConDataCons pTc, not (isNewTyCon pTc) -> do
          monoidCls <- tcLookupClass monoidClassName
          let fixed   = tyConAppArgs realP
              idSel   = classMethod "id" catCls
              compSel = classMethod "." catCls
              memptySel  = classMethod "mempty"  monoidCls
              mappendSel = classMethod "mappend" monoidCls
              wargs   = tyConAppArgs wrappedTy          -- [k, k, P]  (P may be Override2 …)
              kTy     = head wargs                      -- the kind k (Type here)
              dictCon = dataConWorkId (classDataCon catCls)
              app2 m t1 t2 = mkAppTy (mkAppTy m t1) t2
              instAt t1 t2 = map scaledThing (dataConInstOrigArgTys dc (fixed ++ [t1, t2]))
              isKeep m = maybe False (\k -> tyConAppTyCon_maybe m == Just k) (geKeep gen)
              -- @Stock2 P a b ~R P a b@, then (if present) @Override2 cfg rp a b ~R rp a b@
              coDown t1 t2 = mkTransCo
                (mkUnbranchedAxInstCo Representational (newTyConCo st2Tc) (wargs ++ [t1, t2]) [])
                (case geOverride2 gen of
                   Just ov2Tc | tyConAppTyCon_maybe p0 == Just ov2Tc ->
                     mkUnbranchedAxInstCo Representational (newTyConCo ov2Tc)
                                          (tyConAppArgs p0 ++ [t1, t2]) []
                   _ -> mkRepReflCo (app2 realP t1 t2))
              cast' e co = if isReflCo co then e else Cast e co
          pTv <- freshTyVar "p" ; qTv <- freshTyVar "q"
          let realFtsPQ = instAt (mkTyVarTy pTv) (mkTyVarTy qTv)
              inPQ t = pTv `elemVarSet` tyCoVarsOfType t || qTv `elemVarSet` tyCoVarsOfType t
              -- per field: a Category @h@ (+ coercion), or a constant @m@ handled
              -- Const-style via its Monoid (the automatic, @Basic@-free path).
              resolve i ftPQ = case mMods of
                Just mods | Just m0 <- safeIdx mods i, not (isKeep m0) ->
                  -- A modifier decoded from the field-keyed @At Con i := M@ form
                  -- can carry skolem /kind/ variables for phantom parameters
                  -- (e.g. @Basic m a b@'s @a@\/@b@), unlike the dense list form
                  -- which pins them to the datatype's param kind.  'fixMod2Kind'
                  -- re-kinds those to @k@ (so @Category (m a b)@ is solvable) while
                  -- preserving a genuine value variable (a polymorphic @Op cat@).
                  let m = fixMod2Kind kTy m0
                  in Just (CatF m (\t1 t2 -> mkStockCo (PluginProv "stock") Representational
                                                    (instAt t1 t2 !! i) (app2 m t1 t2)))
                _ -> case classifyCatField pTv qTv ftPQ of
                       Just h                    -> Just (CatF h (\t1 t2 -> mkRepReflCo (instAt t1 t2 !! i)))
                       Nothing | not (inPQ ftPQ) -> Just (MonF ftPQ)   -- constant ⇒ Monoid
                               | otherwise        -> Nothing           -- mentions a/b but not @h a b@
              badLen = maybe False ((/= length realFtsPQ) . length) mMods
          case if badLen then Nothing
               else traverse (uncurry resolve) (zip [0 :: Int ..] realFtsPQ) of
            Nothing   -> pure Nothing
            Just flds -> do
              -- per-field dictionary: @Category h@, or @Monoid m@ for a constant
              dws <- traverse (\fld -> case fld of
                       CatF h _ -> do ev <- newWanted loc (mkClassPred catCls [kTy, h])
                                      pure (ctEvExpr ev, mkNonCanonical ev)
                       MonF m   -> do ev <- newWanted loc (mkClassPred monoidCls [m])
                                      pure (ctEvExpr ev, mkNonCanonical ev)) flds
              let (dEs, dWs) = unzip dws
              -- validate each override reshape (@realField ~R m a b@) with a GHC
              -- wanted, so the unchecked @mkStockCo@ axioms can't smuggle in an
              -- unsound coercion (reject @Int via Op@, @a->b via Op@, …).
              ovWs <- case mMods of
                Nothing   -> pure []
                Just mods -> fmap concat $ forM (zip [0 :: Int ..] realFtsPQ) \(i, ftPQ) ->
                  case safeIdx mods i of
                    Just m0 | not (isKeep m0) -> do
                      let m = fixMod2Kind kTy m0
                      -- validate at closed types (see Stock.Functor) so the
                      -- evidence stays free of @pTv@\/@qTv@.  The two params get
                      -- DISTINCT closed types (@()@ and @Bool@): collapsing both to
                      -- the same type would hide an order-swap (@a->b@ vs @b->a@ via
                      -- @Op@ both become @()->()@), wrongly accepting it.
                      vw <- newWanted loc (mkStockReprEq
                              (substTyWith [pTv, qTv] [unitTy, boolTy] ftPQ)
                              (app2 m unitTy boolTy))
                      pure [mkNonCanonical vw]
                    _ -> pure []
              -- id = /\a. (P <id of each field>..) |> sym (Stock2(..) a a ~ P a a)
              aTv <- freshTyVar "a"
              let aTy = mkTyVarTy aTv
                  idVal (CatF h coFn) dE = cast' (mkApps (Var idSel) [Type kTy, Type h, dE, Type aTy])
                                                 (mkSymCo (coFn aTy aTy))
                  idVal (MonF m)      dE = mkApps (Var memptySel) [Type m, dE]   -- id = mempty
                  idImpl = Lam aTv (Cast (mkCoreConApps dc (map Type (fixed ++ [aTy, aTy])
                                                            ++ zipWith idVal flds dEs))
                                         (mkSymCo (coDown aTy aTy)))
              -- (.) = /\b c a. \g h. case g|>co of P g.. -> case h|>co of P h.. -> (P (g.h)..)|>sym
              bTv <- freshTyVar "b" ; cTv <- freshTyVar "c" ; a2Tv <- freshTyVar "a"
              let bTy = mkTyVarTy bTv ; cTy = mkTyVarTy cTv ; a2Ty = mkTyVarTy a2Tv
                  resTy = mkAppTy (mkAppTy wrappedTy a2Ty) cTy   -- Stock2(..) a c
              gId <- freshId (mkAppTy (mkAppTy wrappedTy bTy) cTy) "g"
              hId <- freshId (mkAppTy (mkAppTy wrappedTy a2Ty) bTy) "h"
              gIds <- zipWithM (\n t -> freshId t ("g" ++ show n)) [0 :: Int ..] (instAt bTy cTy)
              hIds <- zipWithM (\n t -> freshId t ("h" ++ show n)) [0 :: Int ..] (instAt a2Ty bTy)
              gCb <- freshId (mkTyConApp pTc (fixed ++ [bTy, cTy]))  "gcb"
              hCb <- freshId (mkTyConApp pTc (fixed ++ [a2Ty, bTy])) "hcb"
              let compVal (CatF h coFn) dE gi hi =
                    cast' (mkApps (Var compSel)
                             [ Type kTy, Type h, dE, Type bTy, Type cTy, Type a2Ty
                             , cast' (Var gi) (coFn bTy cTy), cast' (Var hi) (coFn a2Ty bTy) ])
                          (mkSymCo (coFn a2Ty cTy))
                  compVal (MonF m)      dE gi hi =
                    mkApps (Var mappendSel) [Type m, dE, Var gi, Var hi]   -- g . h = g <> h
                  comps = zipWith4 compVal flds dEs gIds hIds
                  resCast = Cast (mkCoreConApps dc (map Type (fixed ++ [a2Ty, cTy]) ++ comps))
                                 (mkSymCo (coDown a2Ty cTy))
                  inner = Case (Cast (Var hId) (coDown a2Ty bTy)) hCb resTy [Alt (DataAlt dc) hIds resCast]
                  body  = Case (Cast (Var gId) (coDown bTy cTy))  gCb resTy [Alt (DataAlt dc) gIds inner]
                  compImpl = mkLams [bTv, cTv, a2Tv, gId, hId] body
                  dict = mkApps (Var dictCon) [Type kTy, Type wrappedTy, idImpl, compImpl]
              pure (Just (EvExpr dict, dWs ++ ovWs))
    _ -> pure Nothing

-- | Total list indexing.
safeIdx :: [a] -> Int -> Maybe a
safeIdx xs i = if i >= 0 && i < length xs then Just (xs !! i) else Nothing


-- | Synthesize @Bifoldable (Stock2 P)@.  @bifoldMap@ maps @a@-fields with the
-- first function, @b@-fields with the second, folds @h a@/@h b@ fields with
-- @h@'s own @foldMap@, drops constants, and combines with @(<>)@; all other
-- methods come from the class defaults.  No superclass (unlike @Bifunctor@).
synthBifoldable :: GenEnv -> Class -> CtLoc -> Type -> Type
                -> TcPluginM (Maybe (EvTerm, [Ct]))
synthBifoldable gen cls loc wrappedTy p =
  case (geStock2 gen, tyConAppTyCon_maybe realP) of
    (Just st2Tc, Just pTc) -> do
      monoidCls   <- tcLookupClass monoidClassName
      foldableCls <- tcLookupClass foldableClassName
      let fixed       = tyConAppArgs realP
          dcons       = tyConDataCons pTc
          foldMapSel   = classMethod "foldMap" foldableCls
          memptySel    = classMethod "mempty" monoidCls
          mappendSel   = classMethod "mappend" monoidCls
          coAt t1 t2   = coDown2With (geOverride2 gen) st2Tc wrappedTy p realP t1 t2
      mtv <- freshTyVar "m" ; atv <- freshTyVar "a" ; btv <- freshTyVar "b"
      let mTy = mkTyVarTy mtv ; aTy = mkTyVarTy atv ; bTy = mkTyVarTy btv
          innerAB = mkTyConApp pTc (fixed ++ [aTy, bTy])
      dM  <- freshId (mkClassPred monoidCls [mTy]) "dM"
      gA  <- freshId (mkVisFunTyMany aTy mTy) "gA"
      gB  <- freshId (mkVisFunTyMany bTy mTy) "gB"
      tId <- freshId (mkAppTy (mkAppTy wrappedTy aTy) bTy) "t"
      cb  <- freshId innerAB "cb"
      let memptyE      = mkApps (Var memptySel) [Type mTy, Var dM]
          mappendE x y = mkApps (Var mappendSel) [Type mTy, Var dM, x, y]
          -- fold an @h pTy@ field via the modifier @m@'s @foldMap@, casting the
          -- field value @h pTy ~R m pTy@ first.
          foldOver i h g pTy x = do
            let m = fromMaybe h (override1Mod gen mMods i)
            ev <- newWanted loc (mkClassPred foldableCls [m])
            pure (Just (Just ( mkApps (Var foldMapSel)
                                 [Type m, ctEvExpr ev, Type mTy, Type pTy, Var dM, Var g
                                 , castReshape (Var x) (reshapeCo h m pTy)]
                             , [mkNonCanonical ev] )))
          contrib i x ft = case classifyBiField atv btv aTy bTy ft of
            Nothing          -> pure Nothing
            Just BFConst     -> pure (Just Nothing)
            Just BFA         -> pure (Just (Just (App (Var gA) (Var x), [])))
            Just BFB         -> pure (Just (Just (App (Var gB) (Var x), [])))
            Just (BFFoldA h) -> foldOver i h gA aTy x
            Just (BFFoldB h) -> foldOver i h gB bTy x
      malts <- forM dcons \dc -> do
        let fts = map scaledThing (dataConInstOrigArgTys dc (fixed ++ [aTy, bTy]))
        xs  <- zipWithM (\n ft -> freshId ft ("x" ++ show n)) [0 :: Int ..] fts
        mcs <- sequence (zipWith3 contrib [0 :: Int ..] xs fts)
        case sequence mcs of
          Nothing       -> pure Nothing
          Just contribs ->
            let (es, wss) = unzip (catMaybes contribs)
                body = if null es then memptyE else foldr1 mappendE es
            in pure (Just (Alt (DataAlt dc) xs body, concat wss))
      -- @bifoldr@ (so a lazy bi-fold does not fall back to the @Endo@ default,
      -- which drags the @Stock2@ coercion along).  @bifoldr f g z (Con .. xi ..)@
      -- nests a contribution per field around @z@: a constant passes the
      -- accumulator through; an @a@\/@b@ field is @f xi rest@\/@g xi rest@; an
      -- @h a@\/@h b@ field is @(\\b1 b2 -> foldr f b2 b1) xi rest@ (GHC's flip
      -- shape).  @bifoldr@'s forall order is @a c b@.  Skipped under @Override2@.
      let foldrSel = classMethod "foldr" foldableCls
          bidxOf nm = head [ i | (i, m) <- zip [0 :: Int ..] (classMethods cls)
                               , occNameString (occName m) == nm ]
      rcTv <- freshTyVar "c" ; raTv <- freshTyVar "a" ; rbTv <- freshTyVar "b"
      let rcTy = mkTyVarTy rcTv ; raTy = mkTyVarTy raTv ; rbTy = mkTyVarTy rbTv
      rfId <- freshId (mkVisFunTyMany raTy (mkVisFunTyMany rcTy rcTy)) "f"
      rgId <- freshId (mkVisFunTyMany rbTy (mkVisFunTyMany rcTy rcTy)) "g"
      rzId <- freshId rcTy "z"
      rtId <- freshId (mkAppTy (mkAppTy wrappedTy raTy) rbTy) "t"
      rcb  <- freshId (mkTyConApp pTc (fixed ++ [raTy, rbTy])) "cb"
      let foldrField h fn elemTy x k = do
            ev <- newWanted loc (mkClassPred foldableCls [h])
            b1 <- freshId (mkAppTy h elemTy) "b1" ; b2 <- freshId rcTy "b2"
            let flipLam = mkLams [b1, b2] (mkApps (Var foldrSel)
                  [Type h, ctEvExpr ev, Type elemTy, Type rcTy, Var fn, Var b2, Var b1])
            pure (Just (mkApps flipLam [Var x, k], [mkNonCanonical ev]))
          contribBR x ft k = case classifyBiField raTv rbTv raTy rbTy ft of
            Nothing          -> pure Nothing
            Just BFConst     -> pure (Just (k, []))
            Just BFA         -> pure (Just (mkApps (Var rfId) [Var x, k], []))
            Just BFB         -> pure (Just (mkApps (Var rgId) [Var x, k], []))
            Just (BFFoldA h) -> foldrField h rfId raTy x k
            Just (BFFoldB h) -> foldrField h rgId rbTy x k
          combineBR []            k = pure (Just (k, []))
          combineBR ((ft, x) : r) k = do
            mr <- combineBR r k
            case mr of
              Nothing       -> pure Nothing
              Just (k', w') -> do mc <- contribBR x ft k'
                                  pure (fmap (\(e, w) -> (e, w ++ w')) mc)
      mBiFoldrAlts <- if isJust mMods then pure Nothing else fmap sequence $ forM dcons \dc -> do
        let fts = map scaledThing (dataConInstOrigArgTys dc (fixed ++ [raTy, rbTy]))
        xs <- zipWithM (\n ft -> freshId ft ("x" ++ show n)) [0 :: Int ..] fts
        mb <- combineBR (zip fts xs) (Var rzId)
        pure (fmap (\(body, w) -> (Alt (DataAlt dc) xs body, w)) mb)
      case sequence malts of
        Nothing     -> pure Nothing
        Just altWss -> do
          let (alts, wss) = unzip altWss
              biFoldMapImpl = mkLams [mtv, atv, btv, dM, gA, gB, tId]
                (destructInner pTc (fixed ++ [aTy, bTy])
                               (Cast (Var tId) (coAt aTy bTy)) cb mTy alts)
              (biFoldrMethods, biFoldrWs) = case mBiFoldrAlts of
                Just altWs ->
                  let (rAlts, rWss) = unzip altWs
                      biFoldrImpl = mkLams [raTv, rcTv, rbTv, rfId, rgId, rzId, rtId]
                        (destructInner pTc (fixed ++ [raTy, rbTy])
                                       (Cast (Var rtId) (coAt raTy rbTy)) rcb rcTy rAlts)
                  in ([(bidxOf "bifoldr", biFoldrImpl)], concat rWss)
                Nothing -> ([], [])
          dict <- recDictWith cls wrappedTy []
                    ((bidxOf "bifoldMap", biFoldMapImpl) : biFoldrMethods)
          pure (Just (EvExpr dict, concat wss ++ biFoldrWs))
    _ -> pure Nothing
  where (realP, mMods) = peelOverride2With (ovTcsGen "Override2" gen) p

-- | Synthesize @Bitraversable (Stock2 P)@, directly (not by coercion — like
-- @Traversable@, @bitraverse@'s result @f (t c d)@ puts the wrapper under an
-- abstract applicative, so DerivingVia can't coerce it onto @P@; the instance
-- is usable at @Stock2 P@ / via the one-liner).  Per constructor,
-- @pure mkCon \<*\> f1 \<*\> …@: an @a@\/@b@ field uses the supplied function,
-- a constant uses @pure@, and an @h a@\/@h b@ field uses @traverse \@h@ (an
-- @Override2@-reshaped functor goes through the modifier, re-wrapped with
-- @pure coerce \<*\> _@).  @Bifunctor@ and @Bifoldable@ superclasses come from
-- their own synthesizers.
synthBitraversable :: GenEnv -> Class -> CtLoc -> Type -> Type
                   -> TcPluginM (Maybe (EvTerm, [Ct]))
synthBitraversable gen bitravCls loc wrappedTy p =
  case (geStock2 gen, tyConAppTyCon_maybe realP) of
    (Just st2Tc, Just pTc) -> do
      appCls  <- tcLookupClass applicativeClassName
      travCls <- tcLookupClass traversableClassName
      let fixed = tyConAppArgs realP
          dcons = tyConDataCons pTc
          traverseSel = classMethod "traverse" travCls
          pureSel     = classMethod "pure" appCls
          apSel       = classMethod "<*>"  appCls
          coAt t1 t2  = coDown2With (geOverride2 gen) st2Tc wrappedTy p realP t1 t2
      fTv <- freshTyVarK (mkVisFunTyMany liftedTypeKind liftedTypeKind) "f"   -- f :: Type -> Type
      aTv <- freshTyVar "a" ; cTv <- freshTyVar "c"
      bTv <- freshTyVar "b" ; dTv <- freshTyVar "d"           -- bitraverse: forall f a c b d
      let fTy = mkTyVarTy fTv
          aTy = mkTyVarTy aTv ; cTy = mkTyVarTy cTv
          bTy = mkTyVarTy bTv ; dTy = mkTyVarTy dTv
          fOf t   = mkAppTy fTy t
          innerAB = mkTyConApp pTc (fixed ++ [aTy, bTy])
          stcdTy  = mkAppTy (mkAppTy wrappedTy cTy) dTy        -- Stock2 P c d
      dApp <- freshId (mkClassPred appCls [fTy]) "dApp"
      gA   <- freshId (mkVisFunTyMany aTy (fOf cTy)) "gA"      -- a -> f c
      gB   <- freshId (mkVisFunTyMany bTy (fOf dTy)) "gB"      -- b -> f d
      tId  <- freshId (mkAppTy (mkAppTy wrappedTy aTy) bTy) "t"
      cb   <- freshId innerAB "cb"
      let pureE ty e        = mkApps (Var pureSel) [Type fTy, Var dApp, Type ty, e]
          apE tyA tyB ac fe = mkApps (Var apSel)   [Type fTy, Var dApp, Type tyA, Type tyB, ac, fe]
          -- traverse a sub-functor @h@ field at (inParam → outParam) with @g@;
          -- under Override2 reshape @h → m@, re-wrap @m out -> h out@.
          travField i h g inTy outTy x = case override1Mod gen mMods i of
            Nothing -> do
              ev <- newWanted loc (mkClassPred travCls [h])
              pure (Just ( mkApps (Var traverseSel)
                             [Type h, ctEvExpr ev, Type fTy, Type inTy, Type outTy
                             , Var dApp, Var g, Var x]                       -- :: f (h out)
                         , [mkNonCanonical ev] ))
            Just m -> do
              ev <- newWanted loc (mkClassPred travCls [m])
              let trav = mkApps (Var traverseSel)
                           [Type m, ctEvExpr ev, Type fTy, Type inTy, Type outTy
                           , Var dApp, Var g, castReshape (Var x) (reshapeCo h m inTy)]  -- f (m out)
                  hOut = mkAppTy h outTy ; mOut = mkAppTy m outTy
              mo <- freshId mOut "mo"
              let coerceFn = Lam mo (castReshape (Var mo) (reshapeCo m h outTy))          -- m out -> h out
              pure (Just ( apE mOut hOut (pureE (mkVisFunTyMany mOut hOut) coerceFn) trav
                         , [mkNonCanonical ev] ))
          fieldOf i x ftA = case classifyBiField aTv bTv aTy bTy ftA of
            Nothing          -> pure Nothing
            Just BFConst     -> pure (Just (pureE ftA (Var x), []))
            Just BFA         -> pure (Just (App (Var gA) (Var x), []))
            Just BFB         -> pure (Just (App (Var gB) (Var x), []))
            Just (BFFoldA h) -> travField i h gA aTy cTy x
            Just (BFFoldB h) -> travField i h gB bTy dTy x
      malts <- forM dcons \dc -> do
        let fts   = map scaledThing (dataConInstOrigArgTys dc (fixed ++ [aTy, bTy]))
            rvFts = map scaledThing (dataConInstOrigArgTys dc (fixed ++ [cTy, dTy]))
        xs   <- zipWithM (\n ft -> freshId ft ("x" ++ show n)) [0 :: Int ..] fts
        mfes <- sequence (zipWith3 fieldOf [0 :: Int ..] xs fts)
        case sequence mfes of
          Nothing  -> pure Nothing
          Just fes -> do
            let (fieldExprs, wss) = unzip fes
            ys <- zipWithM (\n ft -> freshId ft ("y" ++ show n)) [0 :: Int ..] rvFts
            let mkCon = mkLams ys (Cast (mkCoreConApps dc (map Type (fixed ++ [cTy, dTy]) ++ map Var ys))
                                        (mkSymCo (coAt cTy dTy)))
                rs    = scanr mkVisFunTyMany stcdTy rvFts
                body  = foldl (\ac (k, fe, rvFt) -> apE rvFt (rs !! (k + 1)) ac fe)
                              (pureE (head rs) mkCon)
                              (zip3 [0 :: Int ..] fieldExprs rvFts)
            pure (Just (Alt (DataAlt dc) xs body, concat wss))
      case sequence malts of
        Nothing     -> pure Nothing
        Just altWss -> do
          let (alts, wss) = unzip altWss
              bitraverseImpl = mkLams [fTv, aTv, cTv, bTv, dTv, dApp, gA, gB, tId]
                (destructInner pTc (fixed ++ [aTy, bTy]) (Cast (Var tId) (coAt aTy bTy)) cb (fOf stcdTy) alts)
              -- superclasses (Bifunctor, Bifoldable) in classSCTheta order
              superClss = [ c | pr <- classSCTheta bitravCls, ClassPred c _ <- [classifyPredType pr] ]
          superDictsM <- forM superClss \c ->
            case occNameString (nameOccName (className c)) of
              "Bifunctor"  -> synthBifunctor  gen c loc wrappedTy p
              "Bifoldable" -> synthBifoldable gen c loc wrappedTy p
              _            -> pure Nothing
          case sequence superDictsM of
            Nothing  -> pure Nothing
            Just sds -> do
              dict <- recDictWith bitravCls wrappedTy (map (unwrapEv . fst) sds) [(0, bitraverseImpl)]
              pure (Just (EvExpr dict, concatMap snd sds ++ concat wss))
    _ -> pure Nothing
  where (realP, mMods) = peelOverride2With (ovTcsGen "Override2" gen) p

-- | Synthesize @Bifunctor (Stock2 P)@.  @bimap@ maps @a@-fields with the first
-- function and @b@-fields with the second; @first@/@second@ come from the class
-- defaults.  @Bifunctor@ has a quantified superclass @forall a. Functor (p a)@,
-- which we supply by synthesizing the @Functor (Stock2 P a)@ dictionary under a
-- type-lambda (the @Functor@ maps the second parameter).
synthBifunctor :: GenEnv -> Class -> CtLoc -> Type -> Type
               -> TcPluginM (Maybe (EvTerm, [Ct]))
synthBifunctor gen cls loc wrappedTy p =
  case (geStock2 gen, tyConAppTyCon_maybe realP) of
    (Just st2Tc, Just pTc) -> do
      functorCls <- tcLookupClass functorClassName
      let fixed     = tyConAppArgs realP
          dcons     = tyConDataCons pTc
          bimapSel  = classMethod "bimap" cls             -- bimap
          coAt t1 t2 = coDown2With (geOverride2 gen) st2Tc wrappedTy p realP t1 t2
      apTv <- freshTyVar "a'" ; aTv <- freshTyVar "a"
      bpTv <- freshTyVar "b'" ; bTv <- freshTyVar "b"
      let apTy = mkTyVarTy apTv ; aTy = mkTyVarTy aTv
          bpTy = mkTyVarTy bpTv ; bTy = mkTyVarTy bTv
          innerAB = mkTyConApp pTc (fixed ++ [aTy, bTy])
      gA  <- freshId (mkVisFunTyMany aTy apTy) "gA"        -- a -> a'
      gB  <- freshId (mkVisFunTyMany bTy bpTy) "gB"        -- b -> b'
      sf  <- freshId (mkAppTy (mkAppTy wrappedTy aTy) bTy) "sf"
      cb  <- freshId innerAB "cb"
      -- map one field (instantiated at [a,b]) to its [a',b'] image — the
      -- n-ary variance engine at [Co, Co], so it also descends through arrows
      -- and nested functors (e.g. @[Either Int b]@) that the flat
      -- 'classifyBiField' cannot.  Contravariant occurrences of a (covariant)
      -- parameter have no mapper, so they fail cleanly (no @mContra@).
      let bimapParams = [ (aTv, apTy, Just (Var gA), Nothing)
                        , (bTv, bpTy, Just (Var gB), Nothing) ]
          -- a nested @q a b@ field: recurse via @q@'s own @bimap@ (so e.g.
          -- @Either a b@ / @(a, b)@ fields work, beyond the flat classifier).
          selfBi q = do
            ev <- newWanted loc (mkClassPred cls [q])
            pure (Just ( mkApps (Var bimapSel)
                           [ Type q, ctEvExpr ev, Type aTy, Type apTy, Type bTy, Type bpTy
                           , Var gA, Var gB ]
                       , [mkNonCanonical ev] ))
          -- a plain field: map it pointwise with the n-ary engine.
          mapPlain x ft = do
            m <- varMapN functorCls Nothing loc bimapParams (Just selfBi) Cov ft
            pure (fmap (\(e, ws) -> (App e (Var x), ws)) m)
          -- under @Override2@, an @h a@/@h b@ field is reshaped to @mod a@/@mod b@:
          -- map via @mod@'s @fmap@ on the coerced value, then coerce the result back.
          mapField i x ft = case (override1Mod gen mMods i, classifyBiField aTv bTv aTy bTy ft) of
            (Just mod_, Just (BFFoldA h)) -> mapVia mod_ h x aTy apTy
            (Just mod_, Just (BFFoldB h)) -> mapVia mod_ h x bTy bpTy
            _                             -> mapPlain x ft
          mapVia mod_ h x inTy outTy = do
            m <- varMapN functorCls Nothing loc bimapParams (Just selfBi) Cov (mkAppTy mod_ inTy)
            pure $ flip fmap m \(e, ws) ->
              ( Cast (App e (castReshape (Var x) (reshapeCo h mod_ inTy))) (mkSymCo (reshapeCo h mod_ outTy)), ws )
      malts <- forM dcons \dc -> do
        let fts = map scaledThing (dataConInstOrigArgTys dc (fixed ++ [aTy, bTy]))
        xs  <- zipWithM (\n ft -> freshId ft ("x" ++ show n)) [0 :: Int ..] fts
        mfs <- sequence (zipWith3 mapField [0 :: Int ..] xs fts)
        case sequence mfs of
          Nothing    -> pure Nothing
          Just pairs ->
            let (vals, wss) = unzip pairs
                body = Cast (mkCoreConApps dc (map Type (fixed ++ [apTy, bpTy]) ++ vals))
                            (mkSymCo (coAt apTy bpTy))
            in pure (Just (Alt (DataAlt dc) xs body, concat wss))
      case sequence malts of
        Nothing     -> pure Nothing
        Just altWss -> do
          let (alts, wss) = unzip altWss
              -- bimap quantifies @forall a b c d@: (a->b) maps the first param,
              -- (c->d) the second.  So the binder order is input1,output1,input2,output2.
              bimapImpl = mkLams [aTv, apTv, bTv, bpTv, gA, gB, sf]
                (destructInner pTc (fixed ++ [aTy, bTy]) (Cast (Var sf) (coAt aTy bTy))
                               cb (mkAppTy (mkAppTy wrappedTy apTy) bpTy) alts)
          dmFirst  <- defMethId cls 1                       -- first
          dmSecond <- defMethId cls 2                       -- second
          fdmConst <- defMethId functorCls 1                -- Functor's (<$)
          -- The superclass  forall a. Functor (Stock2 P a)  is just @fmap = bimap
          -- id@ (a Bifunctor law): under @/\sc@ we build a @Functor (Stock2 P sc)@
          -- dictionary whose @fmap g = bimap id g@, reusing the Bifunctor dict.
          sctv  <- freshTyVar "sc"
          b2tv  <- freshTyVar "b" ; b2ptv <- freshTyVar "b'"
          zId   <- freshId (mkTyVarTy sctv) "z"
          g2Id  <- freshId (mkVisFunTyMany (mkTyVarTy b2tv) (mkTyVarTy b2ptv)) "g2"
          x2Id  <- freshId (mkAppTy wrappedTy (mkTyVarTy sctv) `mkAppTy` mkTyVarTy b2tv) "x2"
          dict <- recClassDict cls wrappedTy \dvar -> do
            let scTy   = mkTyVarTy sctv
                idA    = Lam zId (Var zId)                  -- id @sc
                -- fmap g x = bimap @(Stock2 P) dvar @sc @sc @b @b' id g x
                fmapSC = mkLams [b2tv, b2ptv, g2Id, x2Id] $
                  mkApps (Var bimapSel)
                    [ Type wrappedTy, Var dvar
                    , Type scTy, Type scTy, Type (mkTyVarTy b2tv), Type (mkTyVarTy b2ptv)
                    , idA, Var g2Id, Var x2Id ]
            supDict <- recClassDict functorCls (mkAppTy wrappedTy scTy) \fdvar ->
                         pure [ fmapSC
                              , mkApps (Var fdmConst) [Type (mkAppTy wrappedTy scTy), Var fdvar] ]
            pure [ Lam sctv supDict
                 , bimapImpl
                 , mkApps (Var dmFirst)  [Type wrappedTy, Var dvar]
                 , mkApps (Var dmSecond) [Type wrappedTy, Var dvar] ]
          pure (Just (EvExpr dict, concat wss))
    _ -> pure Nothing
  where (realP, mMods) = peelOverride2With (ovTcsGen "Override2" gen) p

-- | A fresh kind-@Type@ type variable (for the @forall a b@ in @fmap@).

-- | The @Stock2@ counterpart of 'zipLift2': walk two values of the same
-- @Stock2 P@ shape (@fa :: P a c@, @fb :: P b d@) in lock-step, combining the
-- per-field-pair results of matching constructors.  Shared by @liftEq2@
-- (short-circuit conjunction) and @liftCompare2@ (lexicographic).
zipLiftBi :: TyCon -> [Type] -> (Type -> Type -> Coercion)
          -> (Type, Type) -> (Type, Type) -> Type   -- (a,c) for fa, (b,d) for fb, result
          -> Id -> Id                                -- the two scrutinees
          -> (Int -> Int -> CoreExpr)                -- mismatched-constructor result
          -> ([CoreExpr] -> TcPluginM CoreExpr)      -- combine field results
          -> (Int -> Type -> Id -> Id -> TcPluginM (Maybe (CoreExpr, [Ct])))  -- per field pair (with index)
          -> TcPluginM (Maybe (CoreExpr, [Ct]))
zipLiftBi pTc fixed coAt2 (aTy, cTy) (bTy, dTy) resTy faId fbId mismatch combine fieldOp = do
  let dcons         = tyConDataCons pTc
      fieldsBi dc t1 t2 = map scaledThing (dataConInstOrigArgTys dc (fixed ++ [t1, t2]))
      freshF dc t1 t2   = zipWithM (\n ft -> freshId ft ("x" ++ show n)) [0 :: Int ..] (fieldsBi dc t1 t2)
      indexed       = zip [0 :: Int ..] dcons
  mInner <- forM indexed \(i, dci) -> do
    xs    <- freshF dci aTy cTy
    mAlts <- forM indexed \(j, dcj) -> do
      ys <- freshF dcj bTy dTy
      if i /= j
        then pure (Just (Alt (DataAlt dcj) ys (mismatch i j), []))
        else do
          mops <- sequence (zipWith4 fieldOp [0 :: Int ..] (fieldsBi dci aTy cTy) xs ys)
          case sequence mops of
            Nothing  -> pure Nothing
            Just ows -> do body <- combine (map fst ows)
                           pure (Just (Alt (DataAlt dcj) ys body, concatMap snd ows))
    case sequence mAlts of
      Nothing     -> pure Nothing
      Just altWss -> do
        let (alts, wss) = unzip altWss
        cbB <- freshId (mkTyConApp pTc (fixed ++ [bTy, dTy])) "cbb"
        pure (Just ( Alt (DataAlt dci) xs
                       (destructInner pTc (fixed ++ [bTy, dTy]) (Cast (Var fbId) (coAt2 bTy dTy)) cbB resTy alts)
                   , concat wss ))
  case sequence mInner of
    Nothing     -> pure Nothing
    Just altWss -> do
      let (alts, wss) = unzip altWss
      cbA <- freshId (mkTyConApp pTc (fixed ++ [aTy, cTy])) "cba"
      pure (Just ( destructInner pTc (fixed ++ [aTy, cTy]) (Cast (Var faId) (coAt2 aTy cTy)) cbA resTy alts
                 , concat wss ))

-- | The superclass evidence for @C2 (Stock2 P)@: each entry of @C2@'s
-- @classSCTheta@ instantiated at the via-target and requested as a wanted
-- (discharged by the plugin: lifted built-ins, or the @Stock2@ passthrough).
stock2Supers :: Class -> Type -> CtLoc -> TcPluginM ([CoreExpr], [Ct])
stock2Supers cls wrappedTy loc = do
  let subst = case classTyVars cls of
                (tv : _) -> zipTvSubst [tv] [wrappedTy]
                _        -> emptySubst
  evs <- forM (map (substTy subst) (classSCTheta cls)) (newWanted loc)
  pure (map ctEvExpr evs, map mkNonCanonical evs)

-- | Synthesize @Eq2 (Stock2 P)@: @liftEq2@ is same-constructor-and-all-fields,
-- with @a@-fields compared by the first function, @b@-fields by the second,
-- @h a@\/@h b@ fields by @liftEq@, constants by @(==)@.
-- Override2 is transparent for Eq2: a hashing/forcing modifier does not change
-- structural equality, so peel the wrapper and compare the real fields.  (This
-- makes @deriving Hashable2 via Overriding2 …@ work: its @Eq2@ superclass is
-- dragged through the same config.)
synthEq2 :: GenEnv -> Class -> CtLoc -> Type -> Type -> TcPluginM (Maybe (EvTerm, [Ct]))
synthEq2 gen eq2Cls loc wrappedTy p0 =
  case (geStock2 gen, tyConAppTyCon_maybe realP) of
    (Just st2Tc, Just pTc) -> do
      eqCls <- tcLookupClass eqClassName
      mEq1  <- lookupClassMaybe "Data.Functor.Classes" "Eq1"
      case mEq1 of
        Nothing     -> pure Nothing
        Just eq1Cls -> do
          let fixed      = tyConAppArgs realP
              liftEqSel  = classMethod "liftEq" eq1Cls
              eqSel      = classMethod "==" eqCls
              true_      = Var (dataConWorkId trueDataCon)
              false_     = Var (dataConWorkId falseDataCon)
              coAt2 t1 t2 = coDown2With (geOverride2 gen) st2Tc wrappedTy p0 realP t1 t2
          aTv <- freshTyVar "a" ; bTv <- freshTyVar "b" ; cTv <- freshTyVar "c" ; dTv <- freshTyVar "d"
          let aTy = mkTyVarTy aTv ; bTy = mkTyVarTy bTv ; cTy = mkTyVarTy cTv ; dTy = mkTyVarTy dTv
          eqAB <- freshId (mkVisFunTyMany aTy (mkVisFunTyMany bTy boolTy)) "eqAB"
          eqCD <- freshId (mkVisFunTyMany cTy (mkVisFunTyMany dTy boolTy)) "eqCD"
          faId <- freshId (mkAppTy (mkAppTy wrappedTy aTy) cTy) "fa"
          fbId <- freshId (mkAppTy (mkAppTy wrappedTy bTy) dTy) "fb"
          let conj []         = pure true_
              conj (e : more)  = do rest <- conj more
                                    scr  <- freshId boolTy "c"
                                    pure (Case e scr boolTy [ Alt (DataAlt falseDataCon) [] false_
                                                            , Alt (DataAlt trueDataCon)  [] rest ])
              fieldOp i ft x y = case classifyBiField aTv cTv aTy cTy ft of
                Nothing          -> pure Nothing
                Just BFA         -> pure (Just (mkApps (Var eqAB) [Var x, Var y], []))
                Just BFB         -> pure (Just (mkApps (Var eqCD) [Var x, Var y], []))
                Just BFConst     -> do ev <- newWanted loc (mkClassPred eqCls [ft])
                                       pure (Just (mkApps (Var eqSel) [Type ft, ctEvExpr ev, Var x, Var y], [mkNonCanonical ev]))
                Just (BFFoldA h) -> do let m = fromMaybe h (override1Mod gen mMods i)
                                       ev <- newWanted loc (mkClassPred eq1Cls [m])
                                       pure (Just (mkApps (Var liftEqSel) [Type m, ctEvExpr ev, Type aTy, Type bTy, Var eqAB, castReshape (Var x) (reshapeCo h m aTy), castReshape (Var y) (reshapeCo h m bTy)], [mkNonCanonical ev]))
                Just (BFFoldB h) -> do let m = fromMaybe h (override1Mod gen mMods i)
                                       ev <- newWanted loc (mkClassPred eq1Cls [m])
                                       pure (Just (mkApps (Var liftEqSel) [Type m, ctEvExpr ev, Type cTy, Type dTy, Var eqCD, castReshape (Var x) (reshapeCo h m cTy), castReshape (Var y) (reshapeCo h m dTy)], [mkNonCanonical ev]))
          mBody <- zipLiftBi pTc fixed coAt2 (aTy, cTy) (bTy, dTy) boolTy faId fbId (\_ _ -> false_) conj fieldOp
          case mBody of
            Nothing        -> pure Nothing
            Just (body, ws) -> do
              (supers, scWs) <- stock2Supers eq2Cls wrappedTy loc
              let impl = mkLams [aTv, bTv, cTv, dTv, eqAB, eqCD, faId, fbId] body
              pure (Just (EvExpr (mkClassDict eq2Cls wrappedTy (supers ++ [impl])), scWs ++ ws))
    _ -> pure Nothing
  where (realP, mMods) = peelOverride2With (ovTcsGen "Override2" gen) p0

-- | Synthesize @Ord2 (Stock2 P)@: @liftCompare2@ orders by constructor tag,
-- then lexicographically by fields (first-param fields by the first function,
-- second by the second, @h a@\/@h b@ by @liftCompare@, constants by @compare@).
synthOrd2 :: GenEnv -> Class -> CtLoc -> Type -> Type -> TcPluginM (Maybe (EvTerm, [Ct]))
synthOrd2 gen ord2Cls loc wrappedTy p =
  case (geStock2 gen, tyConAppTyCon_maybe realP) of
    (Just st2Tc, Just pTc) -> do
      ordCls <- tcLookupClass ordClassName
      mOrd1  <- lookupClassMaybe "Data.Functor.Classes" "Ord1"
      case mOrd1 of
        Nothing      -> pure Nothing
        Just ord1Cls -> do
          let fixed       = tyConAppArgs realP
              liftCmpSel  = classMethod "liftCompare" ord1Cls
              cmpSel      = classMethod "compare" ordCls
              ordTy       = mkTyConTy orderingTyCon
              [ltC, eqC, gtC] = tyConDataCons orderingTyCon
              ltE = Var (dataConWorkId ltC) ; eqE = Var (dataConWorkId eqC) ; gtE = Var (dataConWorkId gtC)
              coAt2 t1 t2 = coDown2With (geOverride2 gen) st2Tc wrappedTy p realP t1 t2
          aTv <- freshTyVar "a" ; bTv <- freshTyVar "b" ; cTv <- freshTyVar "c" ; dTv <- freshTyVar "d"
          let aTy = mkTyVarTy aTv ; bTy = mkTyVarTy bTv ; cTy = mkTyVarTy cTv ; dTy = mkTyVarTy dTv
          cmpAB <- freshId (mkVisFunTyMany aTy (mkVisFunTyMany bTy ordTy)) "cmpAB"
          cmpCD <- freshId (mkVisFunTyMany cTy (mkVisFunTyMany dTy ordTy)) "cmpCD"
          faId  <- freshId (mkAppTy (mkAppTy wrappedTy aTy) cTy) "fa"
          fbId  <- freshId (mkAppTy (mkAppTy wrappedTy bTy) dTy) "fb"
          let lexCmp []         = pure eqE
              lexCmp (e : more)  = do rest <- lexCmp more
                                      scr  <- freshId ordTy "o"
                                      pure (Case e scr ordTy [ Alt (DataAlt ltC) [] ltE
                                                             , Alt (DataAlt eqC) [] rest
                                                             , Alt (DataAlt gtC) [] gtE ])
              fieldOp i ft x y = case classifyBiField aTv cTv aTy cTy ft of
                Nothing          -> pure Nothing
                Just BFA         -> pure (Just (mkApps (Var cmpAB) [Var x, Var y], []))
                Just BFB         -> pure (Just (mkApps (Var cmpCD) [Var x, Var y], []))
                Just BFConst     -> do ev <- newWanted loc (mkClassPred ordCls [ft])
                                       pure (Just (mkApps (Var cmpSel) [Type ft, ctEvExpr ev, Var x, Var y], [mkNonCanonical ev]))
                Just (BFFoldA h) -> do let m = fromMaybe h (override1Mod gen mMods i)
                                       ev <- newWanted loc (mkClassPred ord1Cls [m])
                                       pure (Just (mkApps (Var liftCmpSel) [Type m, ctEvExpr ev, Type aTy, Type bTy, Var cmpAB, castReshape (Var x) (reshapeCo h m aTy), castReshape (Var y) (reshapeCo h m bTy)], [mkNonCanonical ev]))
                Just (BFFoldB h) -> do let m = fromMaybe h (override1Mod gen mMods i)
                                       ev <- newWanted loc (mkClassPred ord1Cls [m])
                                       pure (Just (mkApps (Var liftCmpSel) [Type m, ctEvExpr ev, Type cTy, Type dTy, Var cmpCD, castReshape (Var x) (reshapeCo h m cTy), castReshape (Var y) (reshapeCo h m dTy)], [mkNonCanonical ev]))
          mBody <- zipLiftBi pTc fixed coAt2 (aTy, cTy) (bTy, dTy) ordTy faId fbId
                             (\i j -> if i < j then ltE else gtE) lexCmp fieldOp
          case mBody of
            Nothing        -> pure Nothing
            Just (body, ws) -> do
              (supers, scWs) <- stock2Supers ord2Cls wrappedTy loc
              let impl = mkLams [aTv, bTv, cTv, dTv, cmpAB, cmpCD, faId, fbId] body
              pure (Just (EvExpr (mkClassDict ord2Cls wrappedTy (supers ++ [impl])), scWs ++ ws))
    _ -> pure Nothing
  where (realP, mMods) = peelOverride2With (ovTcsGen "Override2" gen) p

-- | Synthesize @Show2 (Stock2 P)@: @liftShowsPrec2@ renders like derived @Show@
-- (prefix / infix / record, precedence-parenthesised) but shows a first-param
-- field with @spA@, a second with @spB@, an @h a@\/@h b@ field with
-- @liftShowsPrec@, a constant with its own @showsPrec@.
synthShow2 :: GenEnv -> Class -> CtLoc -> Type -> Type -> TcPluginM (Maybe (EvTerm, [Ct]))
synthShow2 gen show2Cls loc wrappedTy p =
  case (geStock2 gen, tyConAppTyCon_maybe realP) of
    (Just st2Tc, Just pTc) -> do
      mShow1 <- lookupClassMaybe "Data.Functor.Classes" "Show1"
      case mShow1 of
        Nothing       -> pure Nothing
        Just show1Cls -> do
          showCls  <- lookupOrig gHC_INTERNAL_SHOW (mkTcOcc "Show") >>= tcLookupClass
          ordCls   <- tcLookupClass ordClassName
          appendId <- tcLookupId appendName
          let fixed       = tyConAppArgs realP
              dcons       = tyConDataCons pTc
              showSTy     = mkVisFunTyMany stringTy stringTy
              liftSpSel   = classMethod "liftShowsPrec" show1Cls
              showsPrecSel = classMethod "showsPrec" showCls
              gtSel       = classMethod ">" ordCls
              coAt2 t1 t2 = coDown2With (geOverride2 gen) st2Tc wrappedTy p realP t1 t2
              cons c t    = mkCoreConApps consDataCon [Type charTy, c, t]
              append s t  = mkApps (Var appendId) [Type charTy, s, t]
              str s       = unsafeTcPluginTcM (mkStringExprFS (fsLit s))
          ordIntEv <- newWanted loc (mkClassPred ordCls [intTy])
          let ordIntDict = ctEvExpr ordIntEv
          aTv <- freshTyVar "a" ; bTv <- freshTyVar "b"
          let aTy = mkTyVarTy aTv ; bTy = mkTyVarTy bTv
              spTyOf t = mkVisFunTyMany intTy (mkVisFunTyMany t showSTy)
              slTyOf t = mkVisFunTyMany (mkListTy t) showSTy
          spA <- freshId (spTyOf aTy) "spA" ; slA <- freshId (slTyOf aTy) "slA"
          spB <- freshId (spTyOf bTy) "spB" ; slB <- freshId (slTyOf bTy) "slB"
          dId <- freshId intTy "d" ; vId <- freshId (mkAppTy (mkAppTy wrappedTy aTy) bTy) "v"
          let mkRenderer i ft xi = case classifyBiField aTv bTv aTy bTy ft of
                Nothing          -> pure Nothing
                Just BFA         -> pure (Just (\pr -> mkApps (Var spA) [mkUncheckedIntExpr pr, Var xi], []))
                Just BFB         -> pure (Just (\pr -> mkApps (Var spB) [mkUncheckedIntExpr pr, Var xi], []))
                Just BFConst     -> do ev <- newWanted loc (mkClassPred showCls [ft])
                                       pure (Just (\pr -> mkApps (Var showsPrecSel) [Type ft, ctEvExpr ev, mkUncheckedIntExpr pr, Var xi], [mkNonCanonical ev]))
                Just (BFFoldA h) -> do let m = fromMaybe h (override1Mod gen mMods i)
                                       ev <- newWanted loc (mkClassPred show1Cls [m])
                                       pure (Just (\pr -> mkApps (Var liftSpSel) [Type m, ctEvExpr ev, Type aTy, Var spA, Var slA, mkUncheckedIntExpr pr, castReshape (Var xi) (reshapeCo h m aTy)], [mkNonCanonical ev]))
                Just (BFFoldB h) -> do let m = fromMaybe h (override1Mod gen mMods i)
                                       ev <- newWanted loc (mkClassPred show1Cls [m])
                                       pure (Just (\pr -> mkApps (Var liftSpSel) [Type m, ctEvExpr ev, Type bTy, Var spB, Var slB, mkUncheckedIntExpr pr, castReshape (Var xi) (reshapeCo h m bTy)], [mkNonCanonical ev]))
          mAltWss <- forM dcons \dc -> do
            let fts    = map scaledThing (dataConInstOrigArgTys dc (fixed ++ [aTy, bTy]))
                name   = occNameString (getOccName dc)
                labels = map (occNameString . nameOccName . flSelector) (dataConFieldLabels dc)
            nameStr <- str name
            xs      <- zipWithM (\n ft -> freshId ft ("x" ++ show n)) [0 :: Int ..] fts
            rest    <- freshId stringTy "r"
            gtBndr  <- freshId boolTy "pb"
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
                        , Alt (DataAlt trueDataCon)  [] (cons (mkCharExpr '(') (mk (cons (mkCharExpr ')') t))) ]
                    goPrefix t   = foldr (\r acc -> cons (mkCharExpr ' ') (App (r 11) acc)) t renderers
                    prefixBody t = append nameStr (goPrefix t)
                body <-
                  if dataConIsInfix dc
                    then do opStr <- str (" " ++ name ++ " ")
                            let [l, r] = renderers
                                mk t = App (l (prec + 1)) (append opStr (App (r (prec + 1)) t))
                            pure (parenAt prec mk (Var rest))
                    else if not (null labels)
                      then do openB <- str " {" ; eqB <- str " = " ; commaB <- str ", " ; closeB <- str "}"
                              lblStrs <- mapM str labels
                              let recF = zip lblStrs renderers
                                  goRec [(lbl, r)] c     = append lbl (append eqB (App (r 0) (append closeB c)))
                                  goRec ((lbl, r) : m) c = append lbl (append eqB (App (r 0) (append commaB (goRec m c))))
                                  goRec [] c             = append closeB c
                                  recBody t = append nameStr (append openB (goRec recF t))
                              pure (parenAt 10 recBody (Var rest))
                      else if null xs then pure (append nameStr (Var rest))
                                      else pure (parenAt 10 prefixBody (Var rest))
                pure (Just (Alt (DataAlt dc) xs (Lam rest body), concat wss))
          case sequence mAltWss of
            Nothing     -> pure Nothing
            Just altWss -> do
              let (alts, wss) = unzip altWss
              cb <- freshId (mkTyConApp pTc (fixed ++ [aTy, bTy])) "cb"
              let impl = mkLams [aTv, bTv, spA, slA, spB, slB, dId, vId]
                           (destructInner pTc (fixed ++ [aTy, bTy]) (Cast (Var vId) (coAt2 aTy bTy)) cb showSTy alts)
              (supers, scWs) <- stock2Supers show2Cls wrappedTy loc
              dict <- recDictWith show2Cls wrappedTy supers [(0, impl)]
              pure (Just (EvExpr dict, mkNonCanonical ordIntEv : scWs ++ concat wss))
    _ -> pure Nothing
  where (realP, mMods) = peelOverride2With (ovTcsGen "Override2" gen) p

-- | Synthesize @Read2 (Stock2 P)@: @liftReadsPrec2@ parses like derived @Read@
-- (prefix / infix / record, precedence-aware) but reads a first-param field
-- with @rp1@, a second with @rp2@, an @h a@\/@h b@ field with @liftReadsPrec@,
-- a constant with its own @readsPrec@.  The bivariate counterpart of
-- 'Stock.Classes1.synthRead1'; quantified superclasses come via 'stock2Supers'.
synthRead2 :: GenEnv -> Class -> CtLoc -> Type -> Type -> TcPluginM (Maybe (EvTerm, [Ct]))
synthRead2 gen read2Cls loc wrappedTy p =
  case (geStock2 gen, tyConAppTyCon_maybe realP) of
    (Just st2Tc, Just pTc) -> do
      mRead1 <- lookupClassMaybe "Data.Functor.Classes" "Read1"
      case mRead1 of
        Nothing       -> pure Nothing
        Just read1Cls -> do
          readCls     <- lookupOrig gHC_INTERNAL_READ (mkTcOcc "Read") >>= tcLookupClass
          ordCls      <- tcLookupClass ordClassName
          appendId    <- tcLookupId appendName
          eqStringId  <- tcLookupId eqStringName
          lexId       <- lookupOrig gHC_INTERNAL_READ (mkVarOcc "lex")       >>= tcLookupId
          readParenId <- lookupOrig gHC_INTERNAL_READ (mkVarOcc "readParen") >>= tcLookupId
          concatMapId <- lookupOrig gHC_INTERNAL_LIST (mkVarOcc "concatMap") >>= tcLookupId
          let liftRpSel    = classMethod "liftReadsPrec" read1Cls
              readsPrecSel = classMethod "readsPrec" readCls
              gtSel        = classMethod ">" ordCls
              fixed        = tyConAppArgs realP
              dcons        = tyConDataCons pTc
              coAt2 t1 t2  = coDown2With (geOverride2 gen) st2Tc wrappedTy p realP t1 t2
          ordIntEv <- newWanted loc (mkClassPred ordCls [intTy])
          let ordIntDict = ctEvExpr ordIntEv
          aTv <- freshTyVar "a" ; bTv <- freshTyVar "b"
          let aTy = mkTyVarTy aTv ; bTy = mkTyVarTy bTv
              innerAB   = mkTyConApp pTc (fixed ++ [aTy, bTy])
              gabTy     = mkAppTy (mkAppTy wrappedTy aTy) bTy
              readSOf t = mkVisFunTyMany stringTy (mkListTy (mkBoxedTupleTy [t, stringTy]))
              rpTyOf t  = mkVisFunTyMany intTy (readSOf t)       -- Int -> ReadS t
              rlTyOf t  = readSOf (mkListTy t)                   -- ReadS [t]
              pairTy    = mkBoxedTupleTy [gabTy, stringTy]
              strPairTy = mkBoxedTupleTy [stringTy, stringTy]
              listPair  = mkListTy pairTy
              tup2      = tupleDataCon Boxed 2
              nilPair   = mkNilExpr pairTy
              false_    = Var (dataConWorkId falseDataCon)
              toWrapped e = Cast e (mkSymCo (coAt2 aTy bTy))
              mkPairW v r = mkCoreConApps tup2 [Type gabTy, Type stringTy, v, r]
              concatMapTo srcElem fn src = mkApps (Var concatMapId) [Type srcElem, Type pairTy, fn, src]
              str s = unsafeTcPluginTcM (mkStringExprFS (fsLit s))
          rp1Id <- freshId (rpTyOf aTy) "rp1" ; rl1Id <- freshId (rlTyOf aTy) "rl1"
          rp2Id <- freshId (rpTyOf bTy) "rp2" ; rl2Id <- freshId (rlTyOf bTy) "rl2"
          dId   <- freshId intTy "d" ; rId <- freshId stringTy "r"

          -- one field's reader @prec -> restString -> [(ft, String)]@.
          let resOf t = mkListTy (mkBoxedTupleTy [t, stringTy])   -- [(t, String)]
              -- read an @h a@/@h b@ field via the modifier @m@, then cast the
              -- parsed @[(m a,String)]@ back to the real @[(h a,String)]@.
              readFold tArg rpI rlI i h = do
                let mMod = override1Mod gen mMods i
                    m    = fromMaybe h mMod
                ev <- newWanted loc (mkClassPred read1Cls [m])
                let rdr prec rest =
                      let parsed = mkApps (Var liftRpSel)
                            [Type m, ctEvExpr ev, Type tArg, Var rpI, Var rlI
                            , mkUncheckedIntExpr prec, rest]
                      in case mMod of
                           Nothing -> parsed
                           Just _  -> Cast parsed (mkStockCo (PluginProv "stock") Representational
                                        (resOf (mkAppTy m tArg)) (resOf (mkAppTy h tArg)))
                pure (Just (rdr, [mkNonCanonical ev]))
              mkFieldReader i ft = case classifyBiField aTv bTv aTy bTy ft of
                Nothing          -> pure Nothing
                Just BFA         -> pure (Just ((\prec rest -> mkApps (Var rp1Id) [mkUncheckedIntExpr prec, rest]), []))
                Just BFB         -> pure (Just ((\prec rest -> mkApps (Var rp2Id) [mkUncheckedIntExpr prec, rest]), []))
                Just BFConst     -> do ev <- newWanted loc (mkClassPred readCls [ft])
                                       pure (Just ((\prec rest -> mkApps (Var readsPrecSel)
                                              [Type ft, ctEvExpr ev, mkUncheckedIntExpr prec, rest]), [mkNonCanonical ev]))
                Just (BFFoldA h) -> readFold aTy rp1Id rl1Id i h
                Just (BFFoldB h) -> readFold bTy rp2Id rl2Id i h

          let buildChain dc [] accRev restE =
                pure $ mkCoreConApps consDataCon
                  [ Type pairTy
                  , mkPairW (toWrapped (conAppAt innerAB dc (map Var (reverse accRev)))) restE
                  , nilPair ]
              buildChain dc ((ft, rdr) : more) accRev restE = do
                a  <- freshId ft "a" ; r' <- freshId stringTy "r"
                pc <- freshId (mkBoxedTupleTy [ft, stringTy]) "p"
                cb <- freshId (mkBoxedTupleTy [ft, stringTy]) "pc"
                rest <- buildChain dc more (a : accRev) (Var r')
                let parsed = rdr (11 :: Integer) restE
                    lam = Lam pc (Case (Var pc) cb listPair [Alt (DataAlt tup2) [a, r'] rest])
                pure (concatMapTo (mkBoxedTupleTy [ft, stringTy]) lam parsed)

              expectTok expStr restE k = do
                pp <- freshId strPairTy "p"; cb <- freshId strPairTy "pc"
                tk <- freshId stringTy "t"; r' <- freshId stringTy "r"; ecb <- freshId boolTy "b"
                body <- k (Var r')
                let lam = Lam pp (Case (Var pp) cb listPair
                      [Alt (DataAlt tup2) [tk, r']
                         (Case (mkApps (Var eqStringId) [Var tk, expStr]) ecb listPair
                            [ Alt (DataAlt falseDataCon) [] nilPair
                            , Alt (DataAlt trueDataCon)  [] body ])])
                pure (concatMapTo strPairTy lam (App (Var lexId) restE))

              parseFieldP prec ft rdr restE k = do
                pp <- freshId (mkBoxedTupleTy [ft, stringTy]) "p"
                cb <- freshId (mkBoxedTupleTy [ft, stringTy]) "pc"
                v <- freshId ft "v"; r' <- freshId stringTy "r"
                body <- k (Var v) (Var r')
                let lam = Lam pp (Case (Var pp) cb listPair [Alt (DataAlt tup2) [v, r'] body])
                pure (concatMapTo (mkBoxedTupleTy [ft, stringTy]) lam (rdr prec restE))

              recChain dc fields restAfterName = do
                openB <- str "{"; closeB <- str "}"; eqB <- str "="; commaB <- str ","
                let result accRev rEnd = mkCoreConApps consDataCon
                      [ Type pairTy
                      , mkPairW (toWrapped (conAppAt innerAB dc (reverse accRev))) rEnd
                      , nilPair ]
                    go restE accRev [] _ = expectTok closeB restE (\rEnd -> pure (result accRev rEnd))
                    go restE accRev ((lbl, ft, rdr) : more) isFirst = do
                      lblStr <- str lbl
                      let after rr = expectTok lblStr rr \r1 ->
                                     expectTok eqB r1 \r2 ->
                                     parseFieldP (0 :: Integer) ft rdr r2 \v r3 ->
                                     go r3 (v : accRev) more False
                      if isFirst then after restE else expectTok commaB restE after
                expectTok openB restAfterName (\r0 -> go r0 [] fields True)

          mParserWss <- forM dcons \dc -> do
            let fts    = map scaledThing (dataConInstOrigArgTys dc (fixed ++ [aTy, bTy]))
                name   = occNameString (getOccName dc)
                labels = map (occNameString . nameOccName . flSelector) (dataConFieldLabels dc)
            nameStr <- str name
            mRdrs   <- zipWithM mkFieldReader [0 :: Int ..] fts
            case sequence mRdrs of
              Nothing      -> pure Nothing
              Just rdrPrs  -> do
                let (rdrs, wss) = unzip rdrPrs
                    gtThr thr = mkApps (Var gtSel) [Type intTy, ordIntDict, Var dId, mkUncheckedIntExpr thr]
                    mkParser flag inner =
                      App (mkApps (Var readParenId) [Type gabTy, flag, inner]) (Var rId)
                parserApp <-
                  if dataConIsInfix dc
                    then do
                      prec <- conPrec dc
                      let [(ft0, rdr0), (ft1, rdr1)] = zip fts rdrs
                      r0 <- freshId stringTy "r0"
                      body <- parseFieldP (prec + 1) ft0 rdr0 (Var r0) \x rA ->
                              expectTok nameStr rA \rB ->
                              parseFieldP (prec + 1) ft1 rdr1 rB \y rC ->
                              pure $ mkCoreConApps consDataCon
                                [ Type pairTy
                                , mkPairW (toWrapped (conAppAt innerAB dc [x, y])) rC
                                , nilPair ]
                      pure (mkParser (gtThr prec) (Lam r0 body))
                    else do
                      r0   <- freshId stringTy "r0"
                      ptok <- freshId strPairTy "pt"; tcb <- freshId strPairTy "ptc"
                      tok  <- freshId stringTy "tok"; r1 <- freshId stringTy "r1"; ecb <- freshId boolTy "bc"
                      chain <- if null labels
                                 then buildChain dc (zip fts rdrs) [] (Var r1)
                                 else recChain dc (zip3 labels fts rdrs) (Var r1)
                      let tokBody = Case (mkApps (Var eqStringId) [Var tok, nameStr]) ecb listPair
                            [ Alt (DataAlt falseDataCon) [] nilPair
                            , Alt (DataAlt trueDataCon)  [] chain ]
                          tokLam = Lam ptok (Case (Var ptok) tcb listPair
                            [Alt (DataAlt tup2) [tok, r1] tokBody])
                          inner = Lam r0 (concatMapTo strPairTy tokLam (App (Var lexId) (Var r0)))
                          -- record syntax never needs surrounding parens (see Stock.Read)
                          flag  = if null fts || not (null labels) then false_ else gtThr (10 :: Integer)
                      pure (mkParser flag inner)
                pure (Just (parserApp, concat wss))

          case sequence mParserWss of
            Nothing        -> pure Nothing
            Just parserWss -> do
              let (parserApps, wss) = unzip parserWss
                  liftRp2Impl = mkLams [aTv, bTv, rp1Id, rl1Id, rp2Id, rl2Id, dId, rId] $
                    foldr (\e acc -> mkApps (Var appendId) [Type pairTy, e, acc]) nilPair parserApps
              (supers, scWs) <- stock2Supers read2Cls wrappedTy loc
              dict <- recDictWith read2Cls wrappedTy supers [(0, liftRp2Impl)]
              pure (Just (EvExpr dict, mkNonCanonical ordIntEv : scWs ++ concat wss))
    _ -> pure Nothing
  where (realP, mMods) = peelOverride2With (ovTcsGen "Override2" gen) p
