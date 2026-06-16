{-# LANGUAGE CPP #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DerivingVia #-}
{-# OPTIONS_GHC -Wno-x-partial -Wno-incomplete-uni-patterns -Wno-unused-imports #-}
-- | @Enum@ and @Ix@ synthesizers.  @Enum@ is for enumerations (all-nullary
-- constructors); its @toEnum@ range-checks like GHC.  @Ix@ covers both
-- enumerations ('synthIx') and single-constructor products ('synthIxProduct',
-- Cartesian range \/ mixed-radix index).  (@Bounded@ lives in "Stock.Bounded".)
module Stock.Enum where
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
import GHC.Core.Make (mkRuntimeErrorApp, pAT_ERROR_ID)
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
import Stock.Ord

-- | A constructor's fixity precedence (default 9), used for @Show@/@Read@ of
-- infix constructors (@showParen (d > prec)@, args at @prec+1@).
synthEnum :: Class -> CtLoc -> Type -> Type -> Coercion -> [(DataCon, [Coercion])]
          -> TcPluginM (EvTerm, [Ct])
synthEnum cls loc wrappedTy innerTy co dcons0 = do
  ordCls <- tcLookupClass ordClassName
  mapId  <- tcLookupId mapName
  eftId  <- tcLookupId enumFromToName        -- enumFromTo  (class method)
  efttId <- tcLookupId enumFromThenToName    -- enumFromThenTo (class method)
  let dcons       = map fst dcons0           -- enumerations have no fields to override
      tagToEnumId = primOpId TagToEnumOp
      geSel       = classMethod ">=" ordCls   -- (>=)
      maxTag      = mkUncheckedIntExpr (fromIntegral (length dcons - 1))
      toWrapped e = Cast e (mkSymCo co)
      fromInner v = Cast (Var v) co

  enumIntEv <- newWanted loc (mkClassPred cls    [intTy])
  ordIntEv  <- newWanted loc (mkClassPred ordCls [intTy])
  let enumIntDict = ctEvExpr enumIntEv
      ordIntDict  = ctEvExpr ordIntEv

  -- fromEnum v = <tag of v>
  fv  <- freshId wrappedTy "v"
  fcb <- freshId innerTy "cb"
  let fromEnumImpl = mkLams [fv] $
        Case (fromInner fv) fcb intTy
          [ Alt (DataAlt dc) [] (mkUncheckedIntExpr (fromIntegral i))
          | (i, dc) <- zip [0 :: Int ..] dcons ]

  -- toEnum i: GHC's derived toEnum RANGE-CHECKS and errors when out of range.
  -- Without the check, @tagToEnum#@ on a bad tag is undefined behaviour (it
  -- segfaults), so we replicate the guard: @if 0 <= i && i <= maxTag then
  -- tagToEnum# i else error@.
  ti  <- freshId intTy "i"
  tcb <- freshId intTy "ib"
  tip <- freshId intPrimTy "i#"
  bLo <- freshId boolTy "blo"
  bHi <- freshId boolTy "bhi"
  let leSel  = classMethod "<=" ordCls
      okCon  = Case (Var ti) tcb wrappedTy
                 [ Alt (DataAlt intDataCon) [tip]
                     (toWrapped (mkApps (Var tagToEnumId) [Type innerTy, Var tip])) ]
      errOut = mkRuntimeErrorApp pAT_ERROR_ID wrappedTy
                 "toEnum: argument out of range (derived via Stock)"
      toEnumImpl = mkLams [ti] $
        Case (mkApps (Var geSel) [Type intTy, ordIntDict, Var ti, mkUncheckedIntExpr 0]) bLo wrappedTy
          [ Alt (DataAlt falseDataCon) [] errOut
          , Alt (DataAlt trueDataCon)  []
              (Case (mkApps (Var leSel) [Type intTy, ordIntDict, Var ti, maxTag]) bHi wrappedTy
                 [ Alt (DataAlt falseDataCon) [] errOut
                 , Alt (DataAlt trueDataCon)  [] okCon ]) ]

  -- enumFrom x = map toEnum (enumFromTo (fromEnum x) maxTag)
  ex <- freshId wrappedTy "x"
  let mapToCon es = mkApps (Var mapId) [Type intTy, Type wrappedTy, toEnumImpl, es]
      enumFromImpl = mkLams [ex] $ mapToCon $
        mkApps (Var eftId) [Type intTy, enumIntDict, mkApps fromEnumImpl [Var ex], maxTag]

  -- enumFromThen x y = map toEnum (enumFromThenTo (fromEnum x) (fromEnum y) lim)
  --   where lim = if fromEnum y >= fromEnum x then maxTag else 0
  etx <- freshId wrappedTy "x"
  ety <- freshId wrappedTy "y"
  lbn <- freshId boolTy "b"
  let fx = mkApps fromEnumImpl [Var etx]
      fy = mkApps fromEnumImpl [Var ety]
      lim = Case (mkApps (Var geSel) [Type intTy, ordIntDict, fy, fx]) lbn intTy
              [ Alt (DataAlt falseDataCon) [] (mkUncheckedIntExpr 0)
              , Alt (DataAlt trueDataCon)  [] maxTag ]
      enumFromThenImpl = mkLams [etx, ety] $ mapToCon $
        mkApps (Var efttId) [Type intTy, enumIntDict, fx, fy, lim]

  -- succ / pred / enumFromTo / enumFromThenTo via class defaults (recursive dict)
  dmSucc <- defMethId cls 0
  dmPred <- defMethId cls 1
  dmEFT  <- defMethId cls 6
  dmEFTT <- defMethId cls 7
  dict <- recClassDict cls wrappedTy \dvar ->
    let useDef dm = mkApps (Var dm) [Type wrappedTy, Var dvar]
    in pure [ useDef dmSucc, useDef dmPred
            , toEnumImpl, fromEnumImpl
            , enumFromImpl, enumFromThenImpl
            , useDef dmEFT, useDef dmEFTT ]
  pure (EvExpr dict, [mkNonCanonical enumIntEv, mkNonCanonical ordIntEv])

-- | Synthesize an @Ix@ dictionary for an enumeration.  @range@/@unsafeIndex@/
-- @inRange@ work on constructor tags; @index@/@rangeSize@/@unsafeRangeSize@
-- come from the class defaults; the @Ord@ superclass is synthesized too.
synthIx :: Class -> CtLoc -> Type -> Type -> Coercion -> [(DataCon, [Coercion])]
        -> TcPluginM (EvTerm, [Ct])
synthIx cls loc wrappedTy innerTy co dcons0 = do
  ordCls  <- tcLookupClass ordClassName
  numCls  <- tcLookupClass numClassName
  enumCls <- tcLookupClass enumClassName
  mapId   <- tcLookupId mapName
  eftId   <- tcLookupId enumFromToName
  let dcons       = map fst dcons0           -- enumerations have no fields to override
      tagToEnumId = primOpId TagToEnumOp
      leSel  = classMethod "<=" ordCls          -- (<=)
      subSel = classMethod "-" numCls          -- (-)
      pairTy = mkBoxedTupleTy [wrappedTy, wrappedTy]
      tupCon = tupleDataCon Boxed 2
      toWrapped e = Cast e (mkSymCo co)
      fromInner v = Cast (Var v) co

  enumIntEv <- newWanted loc (mkClassPred enumCls [intTy])
  ordIntEv  <- newWanted loc (mkClassPred ordCls  [intTy])
  numIntEv  <- newWanted loc (mkClassPred numCls  [intTy])
  let enumIntDict = ctEvExpr enumIntEv
      ordIntDict  = ctEvExpr ordIntEv
      numIntDict  = ctEvExpr numIntEv

  -- tag function (fromEnum) and tagToEnum (toEnum), as in synthEnum
  fv <- freshId wrappedTy "v"; fcb <- freshId innerTy "cb"
  let fromEnumImpl = mkLams [fv] $ Case (fromInner fv) fcb intTy
        [ Alt (DataAlt dc) [] (mkUncheckedIntExpr (fromIntegral i))
        | (i, dc) <- zip [0 :: Int ..] dcons ]
      tagOf e = mkApps fromEnumImpl [e]
  ti <- freshId intTy "i"; tcb <- freshId intTy "ib"; tip <- freshId intPrimTy "i#"
  let toEnumImpl = mkLams [ti] $ Case (Var ti) tcb wrappedTy
        [ Alt (DataAlt intDataCon) [tip]
            (toWrapped (mkApps (Var tagToEnumId) [Type innerTy, Var tip])) ]

  -- range (l,u) = map toEnum (enumFromTo (tag l) (tag u))
  rlu <- freshId pairTy "lu"; rcb <- freshId pairTy "cb"
  rl  <- freshId wrappedTy "l"; ru <- freshId wrappedTy "u"
  let rangeImpl = mkLams [rlu] $ Case (Var rlu) rcb (mkListTy wrappedTy)
        [ Alt (DataAlt tupCon) [rl, ru]
            (mkApps (Var mapId) [Type intTy, Type wrappedTy, toEnumImpl,
               mkApps (Var eftId) [Type intTy, enumIntDict, tagOf (Var rl), tagOf (Var ru)]]) ]

  -- unsafeIndex (l,u) i = tag i - tag l
  ulu <- freshId pairTy "lu"; ucb <- freshId pairTy "cb"
  ul  <- freshId wrappedTy "l"; uu <- freshId wrappedTy "u"; ui <- freshId wrappedTy "i"
  let unsafeIndexImpl = mkLams [ulu, ui] $ Case (Var ulu) ucb intTy
        [ Alt (DataAlt tupCon) [ul, uu]
            (mkApps (Var subSel) [Type intTy, numIntDict, tagOf (Var ui), tagOf (Var ul)]) ]

  -- inRange (l,u) i = tag l <= tag i && tag i <= tag u
  ilu <- freshId pairTy "lu"; icb <- freshId pairTy "cb"
  il  <- freshId wrappedTy "l"; iu <- freshId wrappedTy "u"; ii <- freshId wrappedTy "i"
  ib  <- freshId boolTy "b"
  let le a b = mkApps (Var leSel) [Type intTy, ordIntDict, a, b]
      inRangeImpl = mkLams [ilu, ii] $ Case (Var ilu) icb boolTy
        [ Alt (DataAlt tupCon) [il, iu]
            (Case (le (tagOf (Var il)) (tagOf (Var ii))) ib boolTy
               [ Alt (DataAlt falseDataCon) [] (Var (dataConWorkId falseDataCon))
               , Alt (DataAlt trueDataCon)  [] (le (tagOf (Var ii)) (tagOf (Var iu))) ]) ]

  ordSuper <- unwrapEv . fst <$> synthOrd ordCls loc wrappedTy innerTy co dcons0
  dmIndex  <- defMethId cls 1
  dmRSize  <- defMethId cls 4
  dmURSize <- defMethId cls 5
  dict <- recClassDict cls wrappedTy \dvar ->
    let useDef dm = mkApps (Var dm) [Type wrappedTy, Var dvar]
    in pure [ ordSuper
            , rangeImpl, useDef dmIndex, unsafeIndexImpl, inRangeImpl
            , useDef dmRSize, useDef dmURSize ]
  pure (EvExpr dict, map mkNonCanonical [enumIntEv, ordIntEv, numIntEv])

-- | Synthesize @Ix (Stock P)@ for a single-constructor PRODUCT (like GHC):
-- @range@ is the Cartesian product of the per-field ranges (row-major nested
-- @concatMap@\/@map@), @unsafeIndex@ the mixed-radix index
-- (@acc * unsafeRangeSize fj + unsafeIndex fj@), @inRange@ the conjunction of
-- per-field @inRange@.  @index@\/@rangeSize@\/@unsafeRangeSize@ come from the
-- class defaults; the @Ord@ superclass is synthesized.
synthIxProduct :: Class -> CtLoc -> Type -> Type -> Coercion -> [(DataCon, [Coercion])]
               -> TcPluginM (EvTerm, [Ct])
synthIxProduct cls loc wrappedTy innerTy co dcons0 = do
  ordCls      <- tcLookupClass ordClassName
  numCls      <- tcLookupClass numClassName
  mapId       <- tcLookupId mapName
  concatMapId <- lookupOrig gHC_INTERNAL_LIST (mkVarOcc "concatMap") >>= tcLookupId
  let dc  = fst (head dcons0)
      fts = fieldTysAt innerTy dc
      rangeSel   = classMethod "range"           cls
      uIndexSel  = classMethod "unsafeIndex"     cls
      inRangeSel = classMethod "inRange"         cls
      uRSizeSel  = classMethod "unsafeRangeSize" cls
      mulSel     = classMethod "*" numCls
      addSel     = classMethod "+" numCls
      pairW      = mkBoxedTupleTy [wrappedTy, wrappedTy]
      tup2       = tupleDataCon Boxed 2
      listW      = mkListTy wrappedTy
      toWrapped e = Cast e (mkSymCo co)
      fromInner e = Cast e co
      conApp args = toWrapped (conAppAt innerTy dc args)
  fieldEvs <- mapM (\ft -> newWanted loc (mkClassPred cls [ft])) fts
  numIntEv <- newWanted loc (mkClassPred numCls [intTy])
  let dicts      = map ctEvExpr fieldEvs
      numIntDict = ctEvExpr numIntEv
      pairOf ft l u    = mkCoreConApps tup2 [Type ft, Type ft, l, u]      -- (l,u)::(ft,ft)
      rangeFE  ft d l u   = mkApps (Var rangeSel)   [Type ft, d, pairOf ft l u]
      uIdxFE   ft d l u i = mkApps (Var uIndexSel)  [Type ft, d, pairOf ft l u, i]
      inRngFE  ft d l u i = mkApps (Var inRangeSel) [Type ft, d, pairOf ft l u, i]
      uRSzFE   ft d l u   = mkApps (Var uRSizeSel)  [Type ft, d, pairOf ft l u]
      mul a b = mkApps (Var mulSel) [Type intTy, numIntDict, a, b]
      add a b = mkApps (Var addSel) [Type intTy, numIntDict, a, b]

  -- destructure a @wrappedTy@ bound into its field binders, wrapping a body
  let destr v binders resTy body = do
        cb <- freshId innerTy "cb"
        pure (Case (fromInner (Var v)) cb resTy [Alt (DataAlt dc) binders body])

  -- range (lo,hi) = [ P x.. | xj <- range (lj,uj) ]  (nested concatMap/map)
  luR <- freshId pairW "lu"; lcb <- freshId pairW "lcb"
  loR <- freshId wrappedTy "lo"; hiR <- freshId wrappedTy "hi"
  lsR <- mapM (`freshId` "l") fts; usR <- mapM (`freshId` "u") fts
  let mkRange []                 chosen = pure (mkListExpr wrappedTy [conApp (map Var chosen)])
      mkRange [(ft, d, l, u)]    chosen = do
        x <- freshId ft "x"
        pure (mkApps (Var mapId) [Type ft, Type wrappedTy
               , Lam x (conApp (map Var (chosen ++ [x]))), rangeFE ft d (Var l) (Var u)])
      mkRange ((ft, d, l, u) : r) chosen = do
        x  <- freshId ft "x"
        bd <- mkRange r (chosen ++ [x])
        pure (mkApps (Var concatMapId) [Type ft, Type wrappedTy, Lam x bd, rangeFE ft d (Var l) (Var u)])
  rangeInner <- mkRange (zip4 fts dicts lsR usR) []
  rangeUs    <- destr hiR usR listW rangeInner
  rangeLs    <- destr loR lsR listW rangeUs
  let rangeImpl = mkLams [luR] $ Case (Var luR) lcb listW
        [ Alt (DataAlt tup2) [loR, hiR] rangeLs ]

  -- unsafeIndex (lo,hi) i = mixed-radix: foldl (\a (l,u,i) -> a*urs(l,u) + uidx(l,u) i) 0
  luI <- freshId pairW "lu"; icb <- freshId pairW "icb"; iV <- freshId wrappedTy "i"
  loI <- freshId wrappedTy "lo"; hiI <- freshId wrappedTy "hi"
  lsI <- mapM (`freshId` "l") fts; usI <- mapM (`freshId` "u") fts; isI <- mapM (`freshId` "i") fts
  let idxBody = foldl (\acc (ft, d, l, u, i) -> add (mul acc (uRSzFE ft d (Var l) (Var u)))
                                                    (uIdxFE ft d (Var l) (Var u) (Var i)))
                      (mkUncheckedIntExpr 0) (zipWith5q fts dicts lsI usI isI)
  idxIs <- destr iV  isI intTy idxBody
  idxUs <- destr hiI usI intTy idxIs
  idxLs <- destr loI lsI intTy idxUs
  let uIndexImpl = mkLams [luI, iV] $ Case (Var luI) icb intTy
        [ Alt (DataAlt tup2) [loI, hiI] idxLs ]
        -- note: iV is the second lambda arg; destr on iV is inside (uses iV bound above)

  -- inRange (lo,hi) i = and [ inRange (lj,uj) ij ]
  luN <- freshId pairW "lu"; ncb <- freshId pairW "ncb"; nV <- freshId wrappedTy "i"
  loN <- freshId wrappedTy "lo"; hiN <- freshId wrappedTy "hi"
  lsN <- mapM (`freshId` "l") fts; usN <- mapM (`freshId` "u") fts; isN <- mapM (`freshId` "i") fts
  let conj []                  = pure (Var (dataConWorkId trueDataCon))
      conj ((ft, d, l, u, i) : more) = do
        b    <- freshId boolTy "b"
        rest <- conj more
        pure (Case (inRngFE ft d (Var l) (Var u) (Var i)) b boolTy
               [ Alt (DataAlt falseDataCon) [] (Var (dataConWorkId falseDataCon))
               , Alt (DataAlt trueDataCon)  [] rest ])
  inRBody <- conj (zipWith5q fts dicts lsN usN isN)
  inRIs   <- destr nV  isN boolTy inRBody
  inRUs   <- destr hiN usN boolTy inRIs
  inRLs   <- destr loN lsN boolTy inRUs
  let inRangeImpl = mkLams [luN, nV] $ Case (Var luN) ncb boolTy
        [ Alt (DataAlt tup2) [loN, hiN] inRLs ]

  (ordEv, ordWs) <- synthOrd ordCls loc wrappedTy innerTy co dcons0
  let ordSuper = unwrapEv ordEv
  dmIndex  <- defMethId cls 1
  dmRSize  <- defMethId cls 4
  dmURSize <- defMethId cls 5
  dict <- recClassDict cls wrappedTy \dvar ->
    let useDef dm = mkApps (Var dm) [Type wrappedTy, Var dvar]
    in pure [ ordSuper, rangeImpl, useDef dmIndex, uIndexImpl, inRangeImpl
            , useDef dmRSize, useDef dmURSize ]
  pure (EvExpr dict, map mkNonCanonical (fieldEvs ++ [numIntEv]) ++ ordWs)

-- 4-/5-way zips into tuples (local; avoid Data.List name clutter)
zip4 :: [a] -> [b] -> [c] -> [d] -> [(a, b, c, d)]
zip4 (a:as) (b:bs) (c:cs) (d:ds) = (a,b,c,d) : zip4 as bs cs ds
zip4 _ _ _ _ = []
zipWith5q :: [Type] -> [CoreExpr] -> [Id] -> [Id] -> [Id] -> [(Type, CoreExpr, Id, Id, Id)]
zipWith5q (a:as) (b:bs) (c:cs) (d:ds) (e:es) = (a,b,c,d,e) : zipWith5q as bs cs ds es
zipWith5q _ _ _ _ _ = []

-- | Synthesize a @Read@ dictionary for prefix (non-record, non-infix)
-- constructors, mirroring the Report's derived @readsPrec@:
--
--   readsPrec d = foldr (++) [] [ readParen (paren K) (parse K) | K <- cons ]
--   parse K r = [ (K a1..an, rn) | (tok,r1) <- lex r, tok == "K"
--                                , (a1,r2) <- readsPrec 11 r1, ... ]
--
-- @readList@/@readPrec@/@readListPrec@ come from the class default methods via
-- a recursive dictionary, so @read@ (which goes through @readPrec@) works too.
