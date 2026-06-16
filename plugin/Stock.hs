{-# LANGUAGE CPP #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DerivingVia #-}
-- We use a few partial selectors on values whose shape is guaranteed by GHC
-- invariants — @head (classMethods c)@ (a class always has its methods),
-- @head (tyConDataCons tc)@ (guarded non-empty), and the @[lt,eq,gt]@ pattern
-- on @Ordering@'s three constructors — so we silence the corresponding noise.
{-# OPTIONS_GHC -Wno-x-partial -Wno-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}

-- | Synthesize class instances for the 'Stock' \/ 'Stock1' \/
-- 'Stock2' newtype wrappers directly from a datatype's structure,
-- same as hand-written without @Generic@. This one module both
-- provides the wrappers and /is/ the plugin, so a single name does
-- everything:
--
-- > {-# options_ghc -fplugin Stock #-}
-- >
-- > import Stock
-- > 
-- > data Colour = Red | Green | Blue 
-- >   deriving (Eq, Ord, Show) 
-- >   via Stock Colour
--
-- Supported classes:
--
-- * 'Stock': 'Eq', 'Ord', 'Show', 'Read', 'Semigroup', 'Monoid', 'Enum',
--   'Bounded', 'Ix', 'Generic'.
-- * 'Stock1': 'Functor' \/ 'Contravariant', 'Foldable', 'Applicative',
--   'Generic1', 'Eq1', 'Ord1', 'Show1', 'Read1', 'Traversable',
--   'TestEquality', 'TestCoercion'.
-- * 'Stock2': 'Bifunctor', 'Bifoldable', 'Eq2', 'Ord2', 'Show2', 'Read2',
--   'Category', 'Bitraversable'.
--
-- @Traversable@\/@Bitraversable@ are synthesized at the wrapper (@Stock1
-- F@\/@Stock2 P@) and used directly, or put on your type with the one-liner
-- @traverse g = fmap unStock1 . traverse g . Stock1@.  A bare @deriving via@
-- can't coerce them onto your type: @traverse@'s result @f (t b)@ places the
-- wrapper under an abstract applicative (nominal role), which is unsound to
-- coerce — but the instance itself is ordinary, so the one-liner works.
--
-- The set is open: a satellite package adds a brand-new class with no
-- configuration change (just a dependency) by writing a @DeriveStock@
-- instance. See "Stock.Derive".
--
-- Individual fields can be reshaped during synthesis (per-field
-- @DerivingVia@) with @deriving Cls via Stock (Override T cfg)@; see
-- "Stock.Override".
--
-- /When does it run?/ All synthesis happens at __compile time__,
-- while the plugin type-checks your @deriving@ clause: it emits
-- ordinary Core — the same a hand-written instance would.  At runtime
-- there is no @Rep@, no reflection, no instance lookup; you pay
-- exactly the usual dictionary plumbing (including any dictionaries
-- that polymorphic or polymorphically-recursive code builds at
-- runtime), and never anything extra for having used 'Stock'.

module Stock
  ( Stock(..), Stock1(..), Stock2(..), plugin
    -- Re-exported derivable classes that are /not/ already in Prelude, so
    -- @import Stock@ alone suffices for any @deriving C via Stock T@ clause.
    -- (Class names only: the methods live in their home modules, and
    -- re-exporting @Category@'s @id@\/@.@ would clash with Prelude.)
  , Contravariant
  , Eq1, Ord1, Show1, Read1
  , Eq2, Ord2, Show2, Read2
  , Bifunctor, Bifoldable
  , Category
  , Ix
  , Generic, Generic1
    -- The per-field modifier surface, so @import Stock@ alone suffices for
    -- @deriving C via Overriding T '[ field via M, … ]@ (the surface @via@ /
    -- @_@ lower to these @:=@ / @Keep@ markers).
  , module Stock.Override
  ) where

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
import Stock.Override
import Data.Maybe (catMaybes, fromJust, isJust, fromMaybe)
import Data.Traversable (for)
import qualified Data.Monoid as Mon (Alt(..))
import Stock.Trans (MaybeT(..))
import Control.Monad (zipWithM, unless, guard)
import Data.IORef (IORef, newIORef, readIORef, modifyIORef')
import Stock.Type (Stock(..), Stock1(..), Stock2(..))
-- Re-exported (class names only) so @import Stock@ covers every derivable class.
import Data.Functor.Contravariant (Contravariant)
import Data.Functor.Classes (Eq1, Ord1, Show1, Read1, Eq2, Ord2, Show2, Read2)
import Data.Bifunctor (Bifunctor)
import Data.Bifoldable (Bifoldable)
import Control.Category (Category)
import Data.Ix (Ix)
import GHC.Generics (Generic, Generic1)
-- Imported only so Haddock can resolve the @'TestEquality'@ etc. identifier
-- links in this module's documentation (the plugin itself looks these classes
-- up by name via the GHC API).  '-Wno-unused-imports' (above) silences them.
import Data.Bitraversable (Bitraversable)
import Data.Type.Equality (TestEquality)
import Data.Type.Coercion (TestCoercion)
import Stock.Surface (lowerOverrides)
import Stock.Internal
import Stock.Bounded
import Stock.Eq
import Stock.Ord
import Stock.Semigroup
import Stock.Show
import Stock.Enum
import Stock.Read
import Stock.Functor
import Stock.Applicative
import Stock.Traversable (synthTraversable)
import Stock.TestEquality (synthTestEquality, synthTestCoercion)
import Stock.Bifunctor
import Stock.Generic
import Stock.Classes1

-- | The Stock type-checker plugin. Enable with @-fplugin Stock@.
-- 
-- > {-# options_ghc -fplugin Stock #-}
plugin :: Plugin
plugin = defaultPlugin
  { tcPlugin           = \_ -> Just stockPlugin
    -- same @-fplugin Stock@ also lowers the @Override@ surface sugar at parse time
  , parsedResultAction = \_ _ -> pure . lowerOverrides
  , pluginRecompile    = purePlugin
  }

-- | Present a raw @CtLoc -> TcPluginM (EvTerm, [Ct])@ synthesizer (@Ord@,
-- @Show@, @Read@, @Enum@, @Ix@) as a @Deriver@, so every built-in 'Stock'
-- class dispatches uniformly through 'runDeriverAttempt' — exactly like the
-- SDK-native ones (@Eq@, @Bounded@, @Semigroup@, …).
-- Each constructor is paired with its per-field override coercions
-- (@realFieldType ~R modifierType@, 'Refl' when not overridden) so the raw
-- synthesizers can honour @Override@ — using the modifier type for the field's
-- instance and coercing the bound value — exactly as 'matchSOP' does for the
-- SDK derivers.  'Refl' everywhere ⇒ byte-identical Core to before.
viaSynth :: (Class -> CtLoc -> Type -> Type -> Coercion -> [(DataCon, [Coercion])] -> TcPluginM (EvTerm, [Ct]))
         -> Deriver
viaSynth f = Deriver \cls dt -> synthTc \loc ->
  f cls loc (dtVia dt) (dtType dt) (dtUnwrap dt)
    (map (\c -> (conDataCon c, conFieldCos c)) (dtCons dt))

stockPlugin :: TcPlugin
stockPlugin = TcPlugin
  { tcPluginInit = do
      seen   <- tcPluginIO (newIORef [])
      stock  <- lookupTyConMaybe "Stock.Type" "Stock"
      stock1 <- lookupTyConMaybe "Stock.Type" "Stock1"
      stock2 <- lookupTyConMaybe "Stock.Type" "Stock2"
      witCls <- lookupClassMaybe "Stock.Derive" "DeriveStock"
      k1Tc   <- tcLookupTyCon k1TyConName
      prodTc <- tcLookupTyCon prodTyConName
      rTc    <- lookupOrig gHC_INTERNAL_GENERICS (mkTcOcc "R") >>= tcLookupTyCon
      gen    <- GenEnv stock stock1 stock2 witCls
                       <$> tcLookupClass genClassName
                       <*> tcLookupTyCon repTyConName
                       <*> tcLookupTyCon u1TyConName
                       <*> pure k1Tc
                       <*> pure prodTc <*> pure (head (tyConDataCons prodTc))
                       <*> tcLookupTyCon sumTyConName
                       <*> lookupMetaEnv
                       <*> lookupGen1Env
                       <*> pure (mkTyConTy rTc)
                       <*> lookupTyConMaybe "Stock.Override" "Override"
                       <*> lookupTyConMaybe "Stock.Override" ":="
                       <*> lookupTyConMaybe "Stock.Override" "At"
                       <*> lookupTyConMaybe "Stock.Override" "Keep"
                       <*> lookupTyConMaybe "Stock.Override" "-->"
                       <*> lookupClassMaybe "Stock.Derive" "DeriveStock1"
                       <*> lookupClassMaybe "Stock.Derive" "DeriveStock2"
                       <*> lookupTyConMaybe "Stock.Override" "Override2"
                       <*> lookupTyConMaybe "Stock.Override" "Override1"
      pure (PluginState seen gen)
  , tcPluginSolve = solveStock
  , tcPluginRewrite = \st -> listToUFM
      [ (geRepTc (psGen st),          rewriteRep  (psGen st))
      , (g1RepTc (geGen1 (psGen st)), rewriteRep1 (psGen st)) ]
  , tcPluginStop = \_ -> pure ()
  }

-- | Look up a 'TyCon' by module and name, returning 'Nothing' if the module
-- is not in scope — so the plugin stays inert instead of erroring when our
-- 'Stock' wrapper isn't imported.
solveStock :: PluginState -> EvBindsVar -> [Ct] -> [Ct] -> TcPluginM TcPluginSolveResult
solveStock st _ev _given wanted = do
  results <- for wanted (trySolve st)
  let solutions  = catMaybes [ s | (s, _, _) <- results ]
      newWanteds = concat    [ w | (_, w, _) <- results ]
      insolubles = concat    [ i | (_, _, i) <- results ]
  pure TcPluginSolveResult
    { tcPluginInsolubleCts = insolubles
    , tcPluginSolvedCts    = solutions
    , tcPluginNewCts       = newWanteds
    }

-- | Result of attempting one constraint: an optional solution, any new wanted
-- constraints to emit, and any constraints we declare insoluble (after
-- reporting a custom error for them).
trySolve :: PluginState -> Ct -> TcPluginM Attempt
trySolve st ct =
  case classifyPredType (ctPred ct) of
    -- unary class over a type/constructor; @clsArgs@ may carry a leading
    -- (invisible) kind argument (poly-kinded classes like @Generic1@), so the
    -- type we act on is the /last/ argument.
    ClassPred cls (reverse -> (wrappedTy : _)) ->
      fromMaybe (Nothing, [], [])
        <$> runSolver (mconcat [stockSolver, stock1Solver, stock2Solver]) st ct cls wrappedTy
    _ -> pure (Nothing, [], [])

-- | @Cls (Stock T)@ — build the dictionary from @T@'s constructors.
stockSolver :: Solver
stockSolver = Solver \st ct cls wrappedTy -> do
  -- @Stock (Override T cfg)@ takes priority; its decode emits per-cell coercion
  -- wanteds (@extraCts@) that ride alongside the deriver's own.
  mOver <- mkOverrideRepr (psGen st) (ctLoc ct) wrappedTy
  case mOver of
    Just (Left err)               -> Just <$> notImplemented st ct err
    Just (Right (repr, extraCts)) -> Just . addCts extraCts <$> dispatchStock st ct cls wrappedTy repr
    Nothing -> case mkRepr (geStock (psGen st)) wrappedTy of
      Nothing   -> pure Nothing
      Just repr -> Just <$> dispatchStock st ct cls wrappedTy repr

-- | Append extra wanted constraints to a solve attempt.
addCts :: [Ct] -> Attempt -> Attempt
addCts extra (sol, ws, ins) = (sol, extra ++ ws, ins)

-- | Dispatch a recognised 'Stock'(-@Override@) representation to the right
-- built-in deriver (or a discovered companion via 'tryWitness').
dispatchStock :: PluginState -> Ct -> Class -> Type -> Repr -> TcPluginM Attempt
dispatchStock st ct cls wrappedTy repr
      | reprUnpacked repr =
          notImplemented st ct $
            text "stock: cannot derive via Stock for a type whose"
            <+> text "constructors have UNPACKed or unboxed strict fields"
            <+> text "(their runtime representation differs from their source type)"
            $$ nest 2 (text "in the derived instance for"
                       <+> quotes (ppr (className cls) <+> ppr wrappedTy))
      | reprFamilyField repr =
          notImplemented st ct $
            text "stock: cannot derive via Stock for a type with a field whose"
            <+> text "type is a data/type family instance (e.g. a cardano-crypto"
            <+> text "key); its representation differs from its source type"
            $$ nest 2 (text "in the derived instance for"
                       <+> quotes (ppr (className cls) <+> ppr wrappedTy))
      | otherwise = do
          let innerTy = rInner repr
              co      = rCo repr
          case occNameString (nameOccName (className cls)) of
            "Eq" -> runDeriverAttempt eqDeriver ct cls (toDatatype wrappedTy repr)
            "Ord"  -> runDeriverAttempt (viaSynth synthOrd)  ct cls (toDatatype wrappedTy repr)
            "Show" -> runDeriverAttempt (viaSynth synthShow) ct cls (toDatatype wrappedTy repr)
            "Read" -> runDeriverAttempt (viaSynth synthRead) ct cls (toDatatype wrappedTy repr)
            "Enum"
              | reprIsEnum repr -> runDeriverAttempt (viaSynth synthEnum) ct cls (toDatatype wrappedTy repr)
              | otherwise ->
                  notImplemented st ct $
                    text "stock: deriving Enum via Stock requires an"
                    <+> text "enumeration (constructors without fields)"
                    $$ nest 2 (text "in the derived instance for"
                               <+> quotes (ppr (className cls) <+> ppr wrappedTy))
            "Ix"
              | reprIsEnum repr -> runDeriverAttempt (viaSynth synthIx) ct cls (toDatatype wrappedTy repr)
              | reprSingleCon repr -> runDeriverAttempt (viaSynth synthIxProduct) ct cls (toDatatype wrappedTy repr)
              | otherwise ->
                  notImplemented st ct $
                    text "stock: deriving Ix via Stock requires an enumeration"
                    <+> text "or a single-constructor product"
                    $$ nest 2 (text "in the derived instance for"
                               <+> quotes (ppr (className cls) <+> ppr wrappedTy))
            "Bounded"
              | reprIsEnum repr || reprSingleCon repr ->
                  runDeriverAttempt boundedDeriver ct cls (toDatatype wrappedTy repr)
              | otherwise ->
                  notImplemented st ct $
                    text "stock: deriving Bounded via Stock requires an"
                    <+> text "enumeration or a single-constructor type"
                    $$ nest 2 (text "in the derived instance for"
                               <+> quotes (ppr (className cls) <+> ppr wrappedTy))
            "Generic" -> do
              ev <- synthGeneric (psGen st) wrappedTy innerTy co (rCons repr)
              pure (Just (ev, ct), [], [])
            "Semigroup"
              | reprSingleCon repr -> runDeriverAttempt semigroupDeriver ct cls (toDatatype wrappedTy repr)
              | otherwise -> notImplemented st ct $
                  text "stock: Semigroup via Stock requires a single-constructor"
                  <+> text "(product) type" $$ nest 2 (text "in the derived instance for"
                  <+> quotes (ppr (className cls) <+> ppr wrappedTy))
            "Monoid"
              | reprSingleCon repr -> runDeriverAttempt monoidDeriver ct cls (toDatatype wrappedTy repr)
              | otherwise -> notImplemented st ct $
                  text "stock: Monoid via Stock requires a single-constructor"
                  <+> text "(product) type" $$ nest 2 (text "in the derived instance for"
                  <+> quotes (ppr (className cls) <+> ppr wrappedTy))
            other -> do
              -- not a built-in: try a companion-provided @instance DeriveStock Cls@
              mw <- tryWitness st ct cls (toDatatype wrappedTy repr)
              case mw of
                Just attempt -> pure attempt
                Nothing ->
                  notImplemented st ct $
                    text "stock: deriving" <+> quotes (text other)
                    <+> text "via Stock is not supported, and no"
                    <+> text "'instance DeriveStock' was found for it"
                    $$ nest 2 (text "in the derived instance for"
                               <+> quotes (ppr (className cls) <+> ppr wrappedTy))
-- | @Cls (Stock1 F)@ — a class over a (poly-kinded) type constructor.
stock1Solver :: Solver
stock1Solver = Solver \st ct cls wrappedTy ->
  case (geStock1 (psGen st), tyConAppTyCon_maybe wrappedTy) of
    (Just ourTc, Just stTc) | stTc == ourTc
      , [_, f] <- tyConAppArgs wrappedTy
      -- TestEquality/TestCoercion handle GADTs directly (whose constructors
      -- carry coercion fields that trip 'dcUnpacked'); let them through.
      , occNameString (nameOccName (className cls)) `notElem` ["TestEquality", "TestCoercion"]
      , maybe False (any (\d -> dcUnpacked d || dcFamilyField d) . tyConDataCons) (tyConAppTyCon_maybe f) ->
          fmap Just $ notImplemented st ct $
            text "stock: cannot derive via Stock1 for a type whose constructors have"
            <+> text "UNPACKed/unboxed strict fields or a data/type-family-instance field"
            <+> text "(their runtime representation differs from their source type)"
            $$ nest 2 (text "in the derived instance for"
                       <+> quotes (ppr (className cls) <+> ppr wrappedTy))
    (Just ourTc, Just stTc) | stTc == ourTc
      , [_, f] <- tyConAppArgs wrappedTy ->
          fmap Just $
          let runStock1 synth = do
                m <- synth (psGen st) cls (ctLoc ct) wrappedTy f
                case m of
                  Just (ev, ws) -> pure (Just (ev, ct), ws, [])
                  Nothing ->
                    notImplemented st ct $
                      text "stock: deriving" <+> ppr (className cls)
                      <+> text "via Stock1 supports only covariant fields (the"
                      <+> text "parameter, constants, or a functor applied to it)"
                      $$ nest 2 (text "in the derived instance for"
                                 <+> quotes (ppr (className cls) <+> ppr wrappedTy))
          in case occNameString (nameOccName (className cls)) of
               "Functor"       -> runStock1 synthFunctor
               "Applicative"   -> runStock1 synthApplicative
               "Foldable"      -> runStock1 synthFoldable
               "Contravariant" -> runStock1 synthContravariant
               "Generic1"      -> runStock1 synthGeneric1
               "Eq1"           -> runStock1 synthEq1
               "Ord1"          -> runStock1 synthOrd1
               "Show1"         -> runStock1 synthShow1
               "Read1"         -> runStock1 synthRead1
               -- The instance IS synthesized (and usable at @Stock1 F@, or on your
               -- type via @traverse g = fmap unStock1 . traverse g . Stock1@); only
               -- the DerivingVia coercion onto @F@ is impossible — @traverse@'s
               -- result @f (t b)@ puts the wrapper under an abstract applicative
               -- (nominal role), so a bare @deriving via Stock1@ still fails there.
               "Traversable"   -> runStock1 synthTraversable
               "TestEquality"  -> runStock1 synthTestEquality
               "TestCoercion"  -> runStock1 synthTestCoercion
               _ -> do
                 -- not a built-in: try a companion @instance DeriveStock1 Cls@
                 mw <- tryWitness1 st ct cls wrappedTy f
                 case mw of
                   Just attempt -> pure attempt
                   Nothing -> notImplemented st ct $
                     text "stock: deriving" <+> quotes (ppr (className cls))
                     <+> text "via Stock1 is not supported, and no"
                     <+> text "'instance DeriveStock1' was found for it"
                     $$ nest 2 (text "in the derived instance for"
                                <+> quotes (ppr (className cls) <+> ppr wrappedTy))
    -- @Cls (Stock1 F a..)@ /fully applied/ (kind Type): Stock1 is a
    -- transparent newtype, so solve from @Cls (F a..)@ and coerce.
    -- This discharges the quantified superclass @forall a. Cls a =>
    -- Cls (Stock1 F a)@ that lifted classes (Eq1, NFData1, Hashable1,
    -- …) carry, straight from the user's own @Cls (F a)@ instance,
    -- for any class.
    (Just ourTc, Just stTc) | stTc == ourTc
      , (_ : f : rest@(_ : _)) <- tyConAppArgs wrappedTy ->
          fmap Just $ do
            -- @f@ may itself be @Override1 cfg realF@; peel it so the sub-wanted
            -- lands on the user's real @Cls (realF a..)@ instance, not the
            -- instance-less @Override1@ wrapper.  (One univ coercion spans both hops.)
            let realF   = fst (peelOverride1With (ovTcsGen "Override1" (psGen st)) f)
                innerTy = mkAppTys realF rest                      -- F a..
                -- @Cls (F a..) ~R Cls (Stock1 F a..)@, plugin-asserted: the dicts
                -- share a representation (Stock1 is a newtype).  We assert it
                -- directly rather than lift the newtype coercion through the class
                -- TyCon — whose parameter is /nominal/, so a representational arg
                -- coercion there is role-incorrect (-dcore-lint rejects it).
                dictCo = mkStockCo (PluginProv "stock") Representational
                           (mkClassPred cls [innerTy]) (mkClassPred cls [wrappedTy])
            ev <- newWanted (ctLoc ct) (mkClassPred cls [innerTy])
            pure (Just (EvExpr (Cast (ctEvExpr ev) dictCo), ct), [mkNonCanonical ev], [])
    _ -> pure Nothing

-- | @Cls (Stock2 P)@ — a class over a (poly-kinded) two-parameter constructor.
stock2Solver :: Solver
stock2Solver = Solver \st ct cls wrappedTy ->
  case (geStock2 (psGen st), tyConAppTyCon_maybe wrappedTy) of
    (Just ourTc, Just stTc) | stTc == ourTc
      , [_, _, p] <- tyConAppArgs wrappedTy
      , maybe False (any (\d -> dcUnpacked d || dcFamilyField d) . tyConDataCons) (tyConAppTyCon_maybe p) ->
          fmap Just $ notImplemented st ct $
            text "stock: cannot derive via Stock2 for a type whose constructors have"
            <+> text "UNPACKed/unboxed strict fields or a data/type-family-instance field"
            $$ nest 2 (text "in the derived instance for"
                       <+> quotes (ppr (className cls) <+> ppr wrappedTy))
    (Just ourTc, Just stTc) | stTc == ourTc
      , [_, _, p] <- tyConAppArgs wrappedTy ->
          fmap Just $
          let runStock2 synth = do
                m <- synth (psGen st) cls (ctLoc ct) wrappedTy p
                case m of
                  Just (ev, ws) -> pure (Just (ev, ct), ws, [])
                  Nothing ->
                    notImplemented st ct $
                      text "stock: deriving" <+> ppr (className cls)
                      <+> text "via Stock2 supports only covariant fields in the last"
                      <+> text "two parameters (each parameter, constants, or a functor"
                      <+> text "applied to one)"
                      $$ nest 2 (text "in the derived instance for"
                                 <+> quotes (ppr (className cls) <+> ppr wrappedTy))
          in case occNameString (nameOccName (className cls)) of
               "Bifunctor"  -> runStock2 synthBifunctor
               "Bifoldable" -> runStock2 synthBifoldable
               "Eq2"        -> runStock2 synthEq2
               "Ord2"       -> runStock2 synthOrd2
               "Show2"      -> runStock2 synthShow2
               "Read2"      -> runStock2 synthRead2
               "Category"   -> runStock2 synthCategory
               -- synthesized at Stock2 (usable directly / via the one-liner
               -- @bitraverse f g = fmap unStock2 . bitraverse f g . Stock2@); a
               -- bare @deriving via Stock2@ still fails — bitraverse's result
               -- @f (t c d)@ puts the wrapper under an abstract applicative.
               "Bitraversable" -> runStock2 synthBitraversable
               _ -> do
                 -- not a built-in: try a companion @instance DeriveStock2 Cls@
                 mw <- tryWitness2 st ct cls wrappedTy p
                 case mw of
                   Just attempt -> pure attempt
                   Nothing -> notImplemented st ct $
                     text "stock: deriving" <+> quotes (ppr (className cls))
                     <+> text "via Stock2 is not supported, and no"
                     <+> text "'instance DeriveStock2' was found for it"
                     $$ nest 2 (text "in the derived instance for"
                                <+> quotes (ppr (className cls) <+> ppr wrappedTy))
    -- @Cls (Stock2 P a..)@ /further applied/: Stock2 is a transparent
    -- newtype, so solve from @Cls (P a..)@ and coerce (discharges the
    -- quantified superclass @forall a. Cls a => Cls1 (Stock2 P a)@ of
    -- bi-lifted classes from the user's own @Cls1 (P a)@ instance).
    (Just ourTc, Just stTc) | stTc == ourTc
      , (_ : _ : p : rest@(_ : _)) <- tyConAppArgs wrappedTy ->
          fmap Just $ do
            -- as in the Stock1 passthrough: peel an @Override2 cfg realP@ wrapper
            -- so the sub-wanted lands on the user's real @Cls (realP a..)@ instance.
            let realP   = fst (peelOverride2With (ovTcsGen "Override2" (psGen st)) p)
                innerTy = mkAppTys realP rest                     -- P a..
                -- as in the Stock1 passthrough: assert @Cls (P a..) ~R
                -- Cls (Stock2 P a..)@ directly (role-correct under -dcore-lint),
                -- rather than lift the newtype coercion through the nominal class param.
                dictCo = mkStockCo (PluginProv "stock") Representational
                           (mkClassPred cls [innerTy]) (mkClassPred cls [wrappedTy])
            ev <- newWanted (ctLoc ct) (mkClassPred cls [innerTy])
            pure (Just (EvExpr (Cast (ctEvExpr ev) dictCo), ct), [mkNonCanonical ev], [])
    _ -> pure Nothing

-- | Report a custom error for a constraint and mark it insoluble, so the user
-- sees exactly why synthesis failed instead of a generic "No instance".  The
-- message is reported at most once (the solver may retry the same constraint).
