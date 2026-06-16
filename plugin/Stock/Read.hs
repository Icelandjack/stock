{-# LANGUAGE CPP #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DerivingVia #-}
{-# OPTIONS_GHC -Wno-x-partial -Wno-incomplete-uni-patterns -Wno-unused-imports #-}
-- | @Read@ synthesizer: builds @readPrec@ exactly as GHC's derived @Read@ does
-- (the @ReadPrec@ combinators via "Stock.Internal"'s 'buildReadPrecBody'), so
-- @readsPrec@ — from the class default — is byte-faithful, including the order
-- of ambiguous infix parses.
module Stock.Read where
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
                         , semigroupClassName, monadClassName )
import Stock.Compat ( gHC_INTERNAL_SHOW, gHC_INTERNAL_READ
                    , gHC_INTERNAL_LIST, gHC_INTERNAL_GENERICS
                    , tEXT_READPREC, tEXT_READ_LEX )
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

synthRead :: Class -> CtLoc -> Type -> Type -> Coercion -> [(DataCon, [Coercion])]
          -> TcPluginM (EvTerm, [Ct])
synthRead cls loc wrappedTy innerTy co dcons = do
  (env, monadCt) <- lookupReadPrecEnv loc
  let readPrecSel = classMethod "readPrec" cls
      toWrapped e = Cast e (mkSymCo co)
  -- each field is read at its modifier type @ft@ (= coercionRKind of its
  -- coercion) via that type's own @readPrec@, then coerced back to the real
  -- field type when the constructor is built.
  (cons, evss) <- fmap unzip $ forM dcons \(dc, cosI) -> do
    let fts = map coercionRKind cosI
    fieldEvs <- mapM (\ft -> newWanted loc (mkClassPred cls [ft])) fts
    let readers = [ (ft, mkApps (Var readPrecSel) [Type ft, ctEvExpr ev])
                  | (ft, ev) <- zip fts fieldEvs ]
    pure ((dc, readers, cosI), fieldEvs)
  let cosMap = [ (getUnique dc, cosI) | (dc, _, cosI) <- cons ]
      mkConVal dc argIds =
        let cosI = fromJust (lookup (getUnique dc) cosMap)
        in toWrapped (conAppAt innerTy dc
             (zipWith (\a c -> castInto (Var a) (mkSymCo c)) argIds cosI))
  body <- buildReadPrecBody env wrappedTy mkConVal [ (dc, rs) | (dc, rs, _) <- cons ]
  dict <- recDictWith cls wrappedTy [] [(2, body)]
  pure (EvExpr dict, monadCt : map mkNonCanonical (concat evss))

-- | Synthesize @Generic (Stock T)@ for any single-level ADT.  @Rep@ is a
-- balanced @:+:@ tree of constructors (one constructor ⇒ no @:+:@), each a
-- balanced @:*:@ tree of @Rec0 field@ (or @U1@ if no fields).  @from@ matches
-- the real constructor, builds its product value and injects it into the sum
-- with @L1@\/@R1@; @to@ projects through the @:+:@\/@:*:@ structure and
-- rebuilds.  All casts go through the same plugin coercion the rewriter
-- asserts.  @K1@\/@:+:@\/@:*:@ layers: @K1@ is a newtype (coercion), @:+:@ and
-- @:*:@ are real data (constructed/matched).
