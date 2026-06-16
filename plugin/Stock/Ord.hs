{-# LANGUAGE CPP #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DerivingVia #-}
{-# OPTIONS_GHC -Wno-x-partial -Wno-incomplete-uni-patterns -Wno-unused-imports #-}
-- | @Ord@ synthesizer: tag order between constructors, lexicographic within.
module Stock.Ord where
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
import Stock.Eq

buildCompare :: CtLoc -> Type -> Type -> Coercion -> [(DataCon, [Coercion])]
             -> TcPluginM (CoreExpr, [Ct])
buildCompare loc wrappedTy innerTy co dcons = do
  ordCls <- tcLookupClass ordClassName
  let ordTy = mkTyConTy orderingTyCon
      [ltC, eqC, gtC] = tyConDataCons orderingTyCon
      ltE = Var (dataConWorkId ltC); eqE = Var (dataConWorkId eqC); gtE = Var (dataConWorkId gtC)
      cmpSel = classMethod "compare" ordCls            -- compare
      scrut v = Cast (Var v) co
      indexed = zip [0 :: Int ..] dcons
      -- bind the field at its real type; compare it at the (override) modifier
      -- type, coercing the value — 'Refl' (no override) makes this a no-op.
      realFts dc = fieldTysAt innerTy dc

      -- lexicographic compare of equally-tagged fields (per field: its
      -- override coercion + the two bound field ids)
      lexCmp [] = pure (eqE, [])
      lexCmp ((fco, x, y) : more) = do
        let ft = coercionRKind fco                     -- modifier type (real type if Refl)
        ev          <- newWanted loc (mkClassPred ordCls [ft])
        (restE, ws) <- lexCmp more
        scr         <- freshId ordTy "o"
        let cmp = mkApps (Var cmpSel) [Type ft, ctEvExpr ev, castInto (Var x) fco, castInto (Var y) fco]
            e   = Case cmp scr ordTy
                    [ Alt (DataAlt ltC) [] ltE
                    , Alt (DataAlt eqC) [] restE
                    , Alt (DataAlt gtC) [] gtE ]
        pure (e, mkNonCanonical ev : ws)

  aId <- freshId wrappedTy "a"
  bId <- freshId wrappedTy "b"
  (outerAlts, wss) <- fmap unzip $ forM indexed \(i, (dci, cosI)) -> do
    xs <- zipWithM (\n ft -> freshId ft ("x" ++ show n)) [0 :: Int ..] (realFts dci)
    (innerAlts, iwss) <- fmap unzip $ forM indexed \(j, (dcj, _)) -> do
      ys <- zipWithM (\n ft -> freshId ft ("y" ++ show n)) [0 :: Int ..] (realFts dcj)
      (body, ws) <- if i == j
                      then lexCmp (zip3 cosI xs ys)
                      else pure (if i < j then ltE else gtE, [])
      pure (Alt (DataAlt dcj) ys body, ws)
    innerBndr <- freshId innerTy "cb"
    pure (Alt (DataAlt dci) xs (Case (scrut bId) innerBndr ordTy innerAlts), concat iwss)
  outerBndr <- freshId innerTy "ca"
  let cmpImpl = mkLams [aId, bId] (Case (scrut aId) outerBndr ordTy outerAlts)
  pure (cmpImpl, concat wss)

-- | A direct relational op @a -> b -> Bool@, matching GHC's derived
-- @\<@\/@\<=@\/@\>@\/@\>=@ for small types (it does NOT build an @Ordering@):
-- different constructors compare by tag, equal constructors lexicographically
-- @x1 \`fop\` y1 || (x1 == y1 && rest)@.  @asc@ = ascending (@\<@\/@\<=@); @refl@
-- = reflexive (@\<=@\/@\>=@, so the final field and the nullary case include
-- equality).  The non-final fields use the strict op (@\<@\/@\>@) + @==@; the
-- final field uses the actual op.
buildRel :: Class -> Class -> CtLoc -> Type -> Type -> Coercion -> [(DataCon, [Coercion])]
         -> Bool -> Bool -> TcPluginM (CoreExpr, [Ct])
buildRel ordCls eqCls loc wrappedTy innerTy co dcons asc refl = do
  let boolE b   = Var (dataConWorkId (if b then trueDataCon else falseDataCon))
      ltName    = if asc then "<" else ">"
      lastName  | asc && not refl = "<" | asc = "<=" | not refl = ">" | otherwise = ">="
      scrut v   = Cast (Var v) co
      realFts dc = fieldTysAt innerTy dc
      indexed   = zip [0 :: Int ..] dcons
      fieldRel nm fco x y = do
        let ft = coercionRKind fco
        ev <- newWanted loc (mkClassPred ordCls [ft])
        pure ( mkApps (Var (classMethod nm ordCls))
                 [Type ft, ctEvExpr ev, castInto (Var x) fco, castInto (Var y) fco]
             , [mkNonCanonical ev] )
      fieldEq fco x y = do
        let ft = coercionRKind fco
        ev <- newWanted loc (mkClassPred eqCls [ft])
        pure ( mkApps (Var (classMethod "==" eqCls))
                 [Type ft, ctEvExpr ev, castInto (Var x) fco, castInto (Var y) fco]
             , [mkNonCanonical ev] )
      orE p q  = do s <- freshId boolTy "o"
                    pure (Case p s boolTy [ Alt (DataAlt falseDataCon) [] q
                                          , Alt (DataAlt trueDataCon)  [] (boolE True) ])
      andE2 p q = do s <- freshId boolTy "n"
                     pure (Case p s boolTy [ Alt (DataAlt falseDataCon) [] (boolE False)
                                           , Alt (DataAlt trueDataCon)  [] q ])
      lexRel []              = pure (boolE refl, [])
      lexRel [(fco, x, y)]   = fieldRel lastName fco x y
      lexRel ((fco, x, y) : more) = do
        (ltE, w1) <- fieldRel ltName fco x y
        (eqE, w2) <- fieldEq fco x y
        (rest, w3) <- lexRel more
        ae <- andE2 eqE rest
        oe <- orE ltE ae
        pure (oe, w1 ++ w2 ++ w3)
  aId <- freshId wrappedTy "a" ; bId <- freshId wrappedTy "b"
  (outerAlts, wss) <- fmap unzip $ forM indexed \(i, (dci, cosI)) -> do
    xs <- zipWithM (\n ft -> freshId ft ("x" ++ show n)) [0 :: Int ..] (realFts dci)
    (innerAlts, iwss) <- fmap unzip $ forM indexed \(j, (dcj, _)) -> do
      ys <- zipWithM (\n ft -> freshId ft ("y" ++ show n)) [0 :: Int ..] (realFts dcj)
      (body, ws) <- if i == j then lexRel (zip3 cosI xs ys)
                              else pure (boolE (if asc then i < j else i > j), [])
      pure (Alt (DataAlt dcj) ys body, ws)
    cb <- freshId innerTy "cb"
    pure (Alt (DataAlt dci) xs (Case (scrut bId) cb boolTy innerAlts), concat iwss)
  cb2 <- freshId innerTy "ca"
  pure (mkLams [aId, bId] (Case (scrut aId) cb2 boolTy outerAlts), concat wss)

-- | Synthesize a structural @Eq (Stock Inner)@ dictionary for any single-level
-- algebraic @Inner@.  Two values are equal iff they share a constructor and all
-- corresponding fields are equal; field equality uses each field type's own
-- @Eq@ dictionary, requested as a fresh wanted constraint.
-- | Bridge the internal @Repr@ EDSL to the public @Datatype@ view handed to
-- SDK derivers.
synthOrd :: Class -> CtLoc -> Type -> Type -> Coercion -> [(DataCon, [Coercion])]
         -> TcPluginM (EvTerm, [Ct])
synthOrd ordCls loc wrappedTy innerTy co dcons = do
  (cmpImpl, cmpWs) <- buildCompare loc wrappedTy innerTy co dcons

  -- Eq superclass dictionary (also field-aware).
  eqCls         <- tcLookupClass eqClassName
  (eqDict0, eqWs) <- synthEq eqCls loc wrappedTy innerTy co dcons
  let eqDict = unwrapEv eqDict0

  -- Override only @compare@ (the minimal complete definition) and let the
  -- class default methods supply @(<)@, @(<=)@, @(>)@, @(>=)@, @max@, @min@ —
  -- exactly as a hand-written @instance Ord T where compare = …@ would.  We
  -- give @compare@ an INLINE (stable) unfolding so GHC can inline it into the
  -- derived operators (and into specialising consumers), matching how it treats
  -- a source-written instance method.
  --
  -- Note on performance: when the consumer can specialise to the type (the
  -- common case, and everything that inlines — @map (fmap …)@, a user
  -- @sortBy@, etc.) this is byte-for-byte identical to stock @deriving@.  A
  -- residual ~15-20% remains only when feeding comparisons to a *pre-compiled,
  -- non-specialising* consumer such as @Data.List.sort@, which calls the @Ord@
  -- method indirectly; that overhead is inherent to GHC's dictionary handling,
  -- not to the synthesized comparison (its worker is identical to stock's).
  -- With an Override the field coercions are still-unsolved holes; running the
  -- simple optimiser (inside 'mkInlineUnfoldingWithArity') over Core that
  -- mentions them panics @optCoercion@.  So give @compare@ the INLINE unfolding
  -- only in the (common) non-override case — there the Core is identical to
  -- before; overridden types get the plain inlined method (no eager opt).
  let overridden = any (not . isReflCo) (concatMap snd dcons)
      -- GHC's "game plan": for small types (<=3 constructors, or an
      -- enumeration) define <,<=,>,>= DIRECTLY (not via compare), closing the
      -- ~15-20% residual on non-specialising consumers like Data.List.sort.
      small = length dcons <= 3 || all (null . snd) dcons
      idxOf nm = head [ i | (i, m) <- zip [0 :: Int ..] (classMethods ordCls)
                          , occNameString (occName m) == nm ]
  (relOverrides, relWs) <-
    if not small then pure ([], [])
    else do
      let mk asc refl = buildRel ordCls eqCls loc wrappedTy innerTy co dcons asc refl
      (ltI, w1) <- mk True  False ; (leI, w2) <- mk True  True
      (gtI, w3) <- mk False False ; (geI, w4) <- mk False True
      pure ( [(idxOf "<", ltI), (idxOf "<=", leI), (idxOf ">", gtI), (idxOf ">=", geI)]
           , w1 ++ w2 ++ w3 ++ w4 )
  if overridden
    then do
      dict <- recDictWith ordCls wrappedTy [eqDict] ([(0, cmpImpl)] ++ relOverrides)
      pure (EvExpr dict, cmpWs ++ eqWs ++ relWs)
    else do
      let cmpTy  = mkVisFunTyMany wrappedTy (mkVisFunTyMany wrappedTy (mkTyConTy orderingTyCon))
          cmpUnf = mkInlineUnfoldingWithArity defaultSimpleOpts StableSystemSrc 2 cmpImpl
      cmpId0 <- freshId cmpTy "vvCompare"
      let cmpId = cmpId0 `setIdUnfolding` cmpUnf
      dictInner <- recDictWith ordCls wrappedTy [eqDict] ([(0, Var cmpId)] ++ relOverrides)
      let dict = Let (NonRec cmpId cmpImpl) dictInner
      pure (EvExpr dict, cmpWs ++ eqWs ++ relWs)

-- | Synthesize a @Show@ dictionary matching GHC's derived @Show@, for prefix
-- (non-record, non-infix) constructors.  Per the Haskell Report algorithm:
--
--   nullary:  showsPrec _ K       = showString "K"
--   n-ary:    showsPrec d (K a..) = showParen (d > 10)
--                ( showString "K" . showSpace . showsPrec 11 a . showSpace . ... )
--
-- Field rendering is delegated to each field's own @showsPrec@ at precedence
-- 11, so nesting, negative numbers, etc. match exactly.
