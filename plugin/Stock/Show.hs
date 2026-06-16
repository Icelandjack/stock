{-# LANGUAGE CPP #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DerivingVia #-}
{-# OPTIONS_GHC -Wno-x-partial -Wno-incomplete-uni-patterns -Wno-unused-imports #-}
-- | @Show@ synthesizer: GHC-faithful @showsPrec@ (prefix \/ infix \/ record, with parens).
module Stock.Show where
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

synthShow :: Class -> CtLoc -> Type -> Type -> Coercion -> [(DataCon, [Coercion])]
          -> TcPluginM (EvTerm, [Ct])
synthShow showCls loc wrappedTy innerTy co dcons = do
  appendId     <- tcLookupId appendName
  showListName <- lookupOrig gHC_INTERNAL_SHOW (mkVarOcc "showList__")
  showList__Id <- tcLookupId showListName
  ordCls       <- tcLookupClass ordClassName

  let showsPrecSel = classMethod "showsPrec" showCls         -- showsPrec
      geSel        = classMethod ">=" ordCls           -- (>=) — GHC parenthesises with @d >= prec+1@
      showSTy      = mkVisFunTyMany stringTy stringTy     -- ShowS
      scrut v      = Cast (Var v) co
      cons c t     = mkCoreConApps consDataCon [Type charTy, c, t]   -- c : t
      append s t   = mkApps (Var appendId) [Type charTy, s, t]       -- s ++ t
      str s        = unsafeTcPluginTcM (mkStringExprFS (fsLit s))     -- string literal

  ordIntEv <- newWanted loc (mkClassPred ordCls [intTy])
  let ordIntDict = ctEvExpr ordIntEv

  dId <- freshId intTy "d"
  vId <- freshId wrappedTy "v"

  (alts, fieldWss) <- fmap unzip $ forM dcons \(dc, cosI) -> do
    let realFts = fieldTysAt innerTy dc           -- real (bind) types
        modFts  = map coercionRKind cosI          -- modifier (show-at) types; real when Refl
        name   = occNameString (getOccName dc)
        labels = map (occNameString . nameOccName . flSelector) (dataConFieldLabels dc)
    nameStr  <- str name
    nameSp   <- str (name ++ " ")   -- name + the separating space, baked into one literal (as GHC does)
    xs       <- zipWithM (\n ft -> freshId ft ("x" ++ show n)) [0 :: Int ..] realFts
    fieldEvs <- mapM (\ft -> newWanted loc (mkClassPred showCls [ft])) modFts
    rest     <- freshId stringTy "r"
    gtBndr   <- freshId boolTy "p"
    prec     <- conPrec dc

    -- each field shown at its modifier type, with its bound value coerced
    let triples = zip3 modFts fieldEvs (zipWith castInto (map Var xs) cosI)
        spField p (ft, ev, v) =
          mkApps (Var showsPrecSel) [Type ft, ctEvExpr ev, mkUncheckedIntExpr p, v]
        -- prefix: "K " ++ sp 11 x0 (' ' : sp 11 x1 (… t)) — GHC bakes the first
        -- space into the constructor-name literal, then separates the rest.
        goPrefix :: CoreExpr -> CoreExpr
        goPrefix t = case triples of
          []          -> t
          (f0 : more) -> App (spField 11 f0)
                             (foldr (\fld acc -> cons (mkCharExpr ' ') (App (spField 11 fld) acc)) t more)
        -- parenthesise the body when @d >= thr+1@ (i.e. @d > thr@), matching the
        -- @showParen (d >= appPrec1) p@ that GHC's stock @deriving@ emits.  The
        -- shared continuation @g = \\s -> mk s@ is built once (a single join
        -- point, not duplicated inline); an optional @lead@ literal (the
        -- constructor name) is prepended /outside/ @g@ in each branch, exactly
        -- as GHC floats @showString name@ out of the shared part.
        parenAt :: Integer -> Maybe CoreExpr -> (CoreExpr -> CoreExpr) -> CoreExpr -> TcPluginM CoreExpr
        parenAt thr lead mk t = do
          pId <- freshId showSTy "p"
          sId <- freshId stringTy "s"
          let test :: CoreExpr
              test = mkApps (Var geSel) [Type intTy, ordIntDict, Var dId, mkUncheckedIntExpr (thr + 1)]
              p :: CoreExpr -> CoreExpr   -- lead ++ g t' (lead prepended outside the shared g)
              p t' = maybe id append lead (App (Var pId) t')
          pure $ Let (NonRec pId (Lam sId (mk (Var sId)))) $
            Case test gtBndr stringTy
              [ Alt (DataAlt falseDataCon) [] (p t)
              , Alt (DataAlt trueDataCon)  []
                  (cons (mkCharExpr '(') (p (cons (mkCharExpr ')') t))) ]

    showsBody <-
      if dataConIsInfix dc                                 -- infix: x `op` y at prec
        then do
          opStr <- str (" " ++ name ++ " ")
          let [l, r] = triples
              body t = App (spField (prec + 1) l) (append opStr (App (spField (prec + 1) r) t))
          parenAt prec Nothing body (Var rest)
        else if not (null labels)
          then do                                          -- record: K {l1 = v1, l2 = v2}
            openB  <- str " {"; eqB <- str " = "; commaB <- str ", "; closeB <- str "}"
            lblStrs <- mapM str labels
            let recF = zip lblStrs triples
                goRec [(lbl, fld)] c = append lbl (append eqB (App (spField 0 fld) (append closeB c)))
                goRec ((lbl, fld) : more) c =
                  append lbl (append eqB (App (spField 0 fld) (append commaB (goRec more c))))
                goRec [] c = append closeB c               -- unreachable (record has fields)
                recBody t = append nameStr (append openB (goRec recF t))
            parenAt 10 Nothing recBody (Var rest)
          else if null xs
            then pure (append nameStr (Var rest))          -- nullary: never parenthesised
            else parenAt 10 (Just nameSp) goPrefix (Var rest)  -- prefix: share fields, prepend name

    pure (Alt (DataAlt dc) xs (Lam rest showsBody), fieldEvs)

  caseBndr <- freshId innerTy "cb"
  let spImpl = mkLams [dId, vId] (Case (scrut vId) caseBndr showSTy alts)

  -- show x      = showsPrec 0 x ""
  -- showList    = showList__ (showsPrec 0)
  vShow <- freshId wrappedTy "v"
  vList <- freshId wrappedTy "v"
  let showImpl = Lam vShow (mkApps spImpl [mkUncheckedIntExpr 0, Var vShow, mkNilExpr charTy])
      sp0      = Lam vList (mkApps spImpl [mkUncheckedIntExpr 0, Var vList])
      showListImpl = mkApps (Var showList__Id) [Type wrappedTy, sp0]
      dict = mkClassDict showCls wrappedTy [spImpl, showImpl, showListImpl]
      wanteds = mkNonCanonical ordIntEv
              : map mkNonCanonical (concat fieldWss)
  pure (EvExpr dict, wanteds)

-- | Synthesize a @Bounded@ dictionary.  For an enumeration, @minBound@/@maxBound@
-- are the first/last constructors.  For a single-constructor product, they are
-- that constructor applied to the field types' own @minBound@/@maxBound@.
