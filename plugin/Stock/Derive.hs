{-# LANGUAGE CPP #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DerivingVia #-}
{-# OPTIONS_GHC -Wno-x-partial #-}              -- 'prodCon' head: guarded by the product contract
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-} -- 'classDict' always returns @EvExpr@

-- | The Stock extension SDK.
--
-- A /synthesizer/ for a class @Cls@ is a function @Class -> Datatype
-- -> Synth EvTerm@: given a structural view of the wrapped type,
-- build the class dictionary as Core — the same static, zero-cost
-- evidence the built-in synthesizers produce (no @Generic@, no
-- runtime @Rep@).
--
-- The only non-trivial primitive a synthesizer needs beyond the
-- structure is 'field': request the dictionary for a field's type and
-- continue with its evidence.  This is the \"continuation\" that lets
-- a synthesizer pause, have GHC solve a sub-constraint, and resume —
-- so @Eq@ (consumer), @Functor@ (transformer) and @Arbitrary@
-- (producer) are all just monadic programs over the same structure.
--
-- Companion packages register support for a new class by writing an
-- instance of 'DeriveStock'; the plugin discovers and runs it.  This
-- module deliberately depends only on @ghc@ + @base@, so companions
-- stay light.
module Stock.Derive
  ( -- * Structural view
    Datatype(..)
  , Constructor(..)
    -- * The synthesis monad
  , Synth
  , runSynth
  , synthTc
  , liftTc
  , field
  , fresh
  , castInto
  , classDict
  , classDictWith
  , classMethod
    -- * SOP-style sum-of-products combinators (generics-sop flavour)
  , productCon
  , matchSOP
  , injectSOP
  , fromProduct
  , toProduct
  , pureFields
  , cpureFields
  , mapFields
  , cmapFields
  , zipFields
  , czipFields
  , foldlFields
  , cfoldlFields
  , traverseFields
  , ctraverseFields
    -- * The witness interface
  , Deriver(..)
  , DeriveStock(..)
  , Deriver1(..)
  , DeriveStock1(..)
  , Deriver2(..)
  , DeriveStock2(..)
  ) where

import GHC.Plugins
import GHC.Tc.Plugin (TcPluginM, newWanted, unsafeTcPluginTcM, tcLookupId)
import GHC.Tc.Types.Constraint (Ct, mkNonCanonical, ctEvExpr)
#if MIN_VERSION_ghc(9,12,0)
import GHC.Tc.Types.CtLoc (CtLoc)
#else
import GHC.Tc.Types.Constraint (CtLoc)
#endif
import GHC.Tc.Types.Evidence (EvTerm(EvExpr))
import GHC.Core.Predicate (mkClassPred)
import GHC.Core.Class (Class, classMethods, classOpItems)
import GHC.Types.Fixity (Fixity)
import Control.Monad (forM, foldM)
import Stock.Trans (ReaderT(..), WriterT(..))
-- The kinds for the witness-class indices.  (GHC.Plugins' unqualified @Type@ is
-- the compiler's AST type; here we need the /kind/ @Data.Kind.Type@.)
import qualified Data.Kind as K

-- ---------------------------------------------------------------------------
-- Structural view of the wrapped type
-- ---------------------------------------------------------------------------

-- | What a synthesizer sees when solving @C (Stock T)@: the via-target it is
-- building the instance for (@Stock T@), the underlying analysed type (@T@),
-- the newtype-unwrap coercion between them, and @T@'s constructors.  Field
-- types are already instantiated at @T@'s actual arguments.
data Datatype = Datatype
  { dtVia    :: Type            -- ^ the via-target, e.g. @Stock T@ — what the instance is /for/
  , dtUnwrap :: Coercion        -- ^ @dtVia ~R dtType@ (newtype unwrap)
  , dtType   :: Type            -- ^ the underlying type, e.g. @T@ (or @T a@)
  , dtCons   :: [Constructor]
  }

-- | One constructor of the analysed type: its 'DataCon', field types
-- (instantiated at @T@'s arguments), fixity, and record labels if any.
data Constructor = Constructor
  { conDataCon :: DataCon
  , conFields  :: [Type]        -- ^ field types the synthesizer sees, instantiated at
                                --   @T@'s arguments — the /modifier/ types where a field
                                --   is overridden (see "Stock.Override"), else the real ones
  , conFixity  :: Fixity        -- ^ for infix constructors (default @defaultFixity@)
  , conLabels  :: Maybe [FieldLabel]  -- ^ record selectors, if a record
  , conFieldCos :: [Coercion]   -- ^ per field, @realFieldType ~R conFields!!i@; 'Refl' when
                                --   the field is not overridden.  'matchSOP'\/'injectSOP'
                                --   apply these so synthesizers see only 'conFields'.
  }

-- ---------------------------------------------------------------------------
-- The synthesis monad: a writer of emitted wanteds over a reader of the CtLoc
-- ---------------------------------------------------------------------------

-- | A Core-building computation that may request sub-instances (emitting
-- wanted constraints) and allocate fresh binders.  Structurally this is a
-- reader of the 'CtLoc' over a writer of emitted 'Ct's over 'TcPluginM', so we
-- derive the monad instances straight from that stack (the representations are
-- coercible).
newtype Synth a = Synth (CtLoc -> TcPluginM (a, [Ct]))
  deriving (Functor, Applicative, Monad)
    via ReaderT CtLoc (WriterT [Ct] TcPluginM)

-- | Run a synthesizer at a constraint location, collecting the wanteds it
-- emitted (to be returned to GHC alongside the solution).
runSynth :: CtLoc -> Synth a -> TcPluginM (a, [Ct])
runSynth loc (Synth g) = g loc

-- | Build a @Synth@ from a location-dependent, wanted-emitting action — the
-- inverse of 'runSynth'.  Lets a raw @CtLoc -> TcPluginM (EvTerm, [Ct])@
-- synthesizer be presented as a @Deriver@ (see @viaSynth@ in the plugin).
synthTc :: (CtLoc -> TcPluginM (a, [Ct])) -> Synth a
synthTc = Synth

-- | Lift a plugin action.
liftTc :: TcPluginM a -> Synth a
liftTc m = Synth \_ -> do a <- m; pure (a, [])

-- | The continuation: request the dictionary for @C ty@ and resume with its
-- evidence.  Emits the wanted so GHC solves it (possibly via this very plugin,
-- enabling recursion into the field's own instance).
field :: Class -> Type -> Synth CoreExpr
field cls ty = Synth \loc -> do
  ev <- newWanted loc (mkClassPred cls [ty])
  pure (ctEvExpr ev, [mkNonCanonical ev])

-- | A fresh local binder of the given type.
fresh :: Type -> String -> Synth Id
fresh ty s = liftTc $ do
  u <- unsafeTcPluginTcM getUniqueM
  pure (mkLocalId (mkSystemName u (mkVarOcc s)) manyDataConTy ty)

-- | A class method selected by its source name — order-independent, unlike
-- indexing @classMethods@ positionally (whose order can differ across GHC
-- versions).  Panics if the class has no such method (a plugin bug).
classMethod :: String -> Class -> Id
classMethod name cls =
  case filter ((== name) . occNameString . occName) (classMethods cls) of
    (m : _) -> m
    []      -> pprPanic "stock: classMethod: no method" (text name <+> ppr cls)

-- | Apply a class's dictionary constructor: @C:Cls \@ty m1 .. mn@.
classDict :: Class -> Type -> [CoreExpr] -> EvTerm
classDict cls ty methods =
  EvExpr (mkApps (Var (dataConWorkId (classDataCon cls))) (Type ty : methods))

-- | Build a (recursive) dictionary giving explicit superclass dictionaries and
-- implementations for the listed method indices; every other method is taken
-- from the class's own default (applied to the recursive dictionary).  Lets a
-- synthesizer fill a many-method class from a few key methods — e.g.
-- @Hashable@ from just @hashWithSalt@ (its @hash@ has a default), with its
-- @Eq@ superclass supplied as @[field eqCls ty]@.
classDictWith :: Class -> Type -> [CoreExpr] -> [(Int, CoreExpr)] -> Synth EvTerm
classDictWith cls ty supers overrides = do
  dvar    <- fresh (mkClassPred cls [ty]) "dict"
  methods <- forM (zip [0 ..] (classMethods cls)) \(i, _) ->
    case lookup i overrides of
      Just e  -> pure e
      Nothing -> case snd (classOpItems cls !! i) of
        Just (nm, _) -> do dm <- liftTc (tcLookupId nm)
                           pure (mkApps (Var dm) [Type ty, Var dvar])
        Nothing      -> error "stock: classDictWith: method has no default and no override"
  let EvExpr con = classDict cls ty (supers ++ methods)
  pure (EvExpr (Let (Rec [(dvar, con)]) (Var dvar)))

-- ---------------------------------------------------------------------------
-- SOP-style sum-of-products combinators
-- ---------------------------------------------------------------------------
--
-- A thin @generics-sop@ flavour over the structural view.  The correspondence:
--
-- @
--   generics-sop          role             Stock.Derive
--   ────────────          ────             ────────────
--   from x  (NS elim, ∃)  sum   dispatch    matchSOP   dt r x (\\i con fs -> …)
--   to . inj (NS intro)   sum   build       injectSOP  dt con fs
--   cpure_NP  (NP, Π)     field tabulate    cpureFields C k con
--   hcmap     (NP)        field map          cmapFields  C k con xs
--   cliftA2_NP (NP)       field zip          czipFields  C k con xs ys
--   hcfoldl   (NP)        field collapse     cfoldlFields C step z con xs
-- @
--
-- The split mirrors @SOP f = NS (NP f)@: 'matchSOP'\/'injectSOP' handle the
-- /sum/ (the @NS@, an existential over constructors); the @cpure@\/@cmap@\/
-- @czip@\/@cfoldl@ family handle one constructor's /product/ (its @NP@, the
-- representable @Fin n -> f@).  Because the @NP@ combinators take a
-- @Constructor@, they compose inside 'matchSOP' for any constructor of a sum,
-- not just the sole product one.  The @All c xs@ constraint is implicit: the
-- @c@-prefixed combinators call 'field' per field for the @cls@ dictionary.
-- So @eqDeriver@ (sum), @semigroupDeriver@\/@monoidDeriver@ (product) and
-- companions like @stock-hashable@\/@NFData@ read like their generic kin.

-- | The constructor of a product (the sole one).  Exported so product
-- synthesizers can feed it to the per-@Constructor@ NP combinators below.
productCon :: Datatype -> Constructor
productCon = head . dtCons

-- | The SOP eliminator (@from@ + @case@): scrutinise a value of the via-type
-- and dispatch on its constructor.  @k idx con fields@ builds the @resTy@-typed
-- branch body for constructor @con@ (index @idx@ in 'dtCons') with its bound
-- field expressions.  One alternative per constructor — so this is the
-- sum-of-products generalisation of 'fromProduct'.
matchSOP :: Datatype -> Type -> CoreExpr
         -> (Int -> Constructor -> [CoreExpr] -> Synth CoreExpr) -> Synth CoreExpr
matchSOP dt resTy v k = do
  cb   <- fresh (dtType dt) "s"
  alts <- forM (zip [0 ..] (dtCons dt)) \(i, c) -> do
    -- bind each pattern var at the /real/ field type (the coercion's LHS),
    -- then present the continuation the value coerced to the modifier type.
    xs   <- mapM (\co -> fresh (coercionLKind co) "x") (conFieldCos c)
    body <- k i c (zipWith castInto (map Var xs) (conFieldCos c))
    pure (Alt (DataAlt (conDataCon c)) xs body)
  pure (Case (Cast v (dtUnwrap dt)) cb resTy alts)

-- | @x |> co@, skipping the cast entirely when @co@ is reflexive (the
-- not-overridden case) so the generated Core stays byte-identical.
castInto :: CoreExpr -> Coercion -> CoreExpr
castInto e co = if isReflCo co then e else Cast e co

-- | The SOP introducer (@inj@ + @to@): build a value of the via-type from a
-- chosen constructor and one expression per its fields.
injectSOP :: Datatype -> Constructor -> [CoreExpr] -> CoreExpr
injectSOP dt c es =
  Cast (mkCoreConApps (conDataCon c) (map Type (tyConAppArgs (dtType dt)) ++ es'))
       (mkSymCo (dtUnwrap dt))
  where -- each result comes back at the modifier type; coerce it to the real
        -- field type before reapplying the constructor (no-op when reflexive).
        es' = zipWith (\e co -> castInto e (mkSymCo co)) es (conFieldCos c)

-- | @productTypeFrom@ + a continuation: the single-constructor case of
-- 'matchSOP'.
fromProduct :: Datatype -> Type -> CoreExpr -> ([CoreExpr] -> Synth CoreExpr)
            -> Synth CoreExpr
fromProduct dt resTy v k = matchSOP dt resTy v \_ _ fields -> k fields

-- | @productTypeTo@: the single-constructor case of 'injectSOP'.
toProduct :: Datatype -> [CoreExpr] -> CoreExpr
toProduct dt = injectSOP dt (productCon dt)

-- The NP combinators below all operate on ONE @Constructor@ (≅ one @NP@), so
-- they compose directly inside 'matchSOP' for /any/ constructor of a sum — not
-- just the sole product one.  An @NP@ is the representable functor @Fin n ->
-- f@: 'pureFields' tabulates it, 'mapFields'\/'zipFields' act positionwise, and
-- 'foldlFields' collapses it.  Each has a @c@onstrained sibling that requests
-- the field's @cls@ dictionary (the implicit @All c xs@).

-- | @pure_NP@ \/ @cpure_NP@: one result per field, produced from its type
-- (@cpure@ also from its @cls@ dictionary, e.g. @k ft d = mempty \@ft d@).
pureFields :: (Type -> Synth a) -> Constructor -> Synth [a]
pureFields k con = mapM k (conFields con)

-- | 'pureFields' that also hands each field its own @cls@ dictionary.
cpureFields :: Class -> (Type -> CoreExpr -> CoreExpr) -> Constructor -> Synth [CoreExpr]
cpureFields cls k = pureFields \ft -> do d <- field cls ft; pure (k ft d)

-- | @hmap@ \/ @hcmap@: map over the fields positionwise (the basic @NP@ action;
-- @cmap@ also hands each field's @cls@ dictionary to the step).
mapFields :: (Type -> CoreExpr -> Synth a) -> Constructor -> [CoreExpr] -> Synth [a]
mapFields k con xs = sequence (zipWith k (conFields con) xs)

-- | 'mapFields' that also hands each field its own @cls@ dictionary.
cmapFields :: Class -> (Type -> CoreExpr -> CoreExpr -> CoreExpr) -> Constructor -> [CoreExpr] -> Synth [CoreExpr]
cmapFields cls k = mapFields \ft x -> do d <- field cls ft; pure (k ft d x)

-- | @liftA2_NP@ \/ @cliftA2_NP@: combine two field-lists positionwise (@czip@
-- via each field's @cls@ dictionary, e.g. @k ft d x y = (\<>) \@ft d x y@).
zipFields :: (Type -> CoreExpr -> CoreExpr -> Synth a)
          -> Constructor -> [CoreExpr] -> [CoreExpr] -> Synth [a]
zipFields k con xs ys = sequence (zipWith3 k (conFields con) xs ys)

-- | 'zipFields' that also hands each field its own @cls@ dictionary.
czipFields :: Class -> (Type -> CoreExpr -> CoreExpr -> CoreExpr -> CoreExpr)
           -> Constructor -> [CoreExpr] -> [CoreExpr] -> Synth [CoreExpr]
czipFields cls k = zipFields \ft x y -> do d <- field cls ft; pure (k ft d x y)

-- | @hfoldl@ \/ @cfoldl_NP@: collapse the fields left-to-right through an
-- accumulator @a@ (any host value — a 'CoreExpr', a list, …).  The step of the
-- unconstrained 'foldlFields' has full @Synth@ access (request any/no/several
-- dictionaries); 'cfoldlFields' hands it each field's @cls@ dictionary.  Needed
-- by accumulating classes, e.g. @Hashable@'s @hashWithSalt@ threading the salt.
foldlFields :: (a -> Type -> CoreExpr -> Synth a) -> a -> Constructor -> [CoreExpr] -> Synth a
foldlFields step z con fields =
  foldM (\acc (ft, e) -> step acc ft e) z (zip (conFields con) fields)

-- | 'foldlFields' that also hands each field its own @cls@ dictionary.
cfoldlFields :: Class
             -> (CoreExpr -> Type -> CoreExpr -> CoreExpr -> Synth CoreExpr)  -- ^ @acc ft dict field@
             -> CoreExpr            -- ^ initial accumulator
             -> Constructor -> [CoreExpr] -> Synth CoreExpr
cfoldlFields cls step =
  foldlFields \acc ft e -> do d <- field cls ft; step acc ft d e

-- | @htraverse@ over a list of fields: produce one @a@ per field in @Synth@.
-- The most general traversal-shaped combinator — used for applicative-effectful
-- work like generating `Gen a` values (for @Arbitrary@).  'traverseFields' has
-- full @Synth@ access; 'ctraverseFields' hands each field's @cls@ dictionary
-- to the step.
traverseFields :: (Type -> CoreExpr -> Synth a) -> Constructor -> [CoreExpr] -> Synth [a]
traverseFields k con xs = sequence (zipWith k (conFields con) xs)

-- | @hctraverse@: the @c@onstrained 'traverseFields' — requests each field's
-- @cls@ dictionary and hands it to the step (alongside the field value).
-- Used by @Arbitrary@ (request `Arbitrary ft` per field, emit `Gen ft`),
-- @CoArbitrary@ (request `CoArbitrary ft`, emit function generator),
-- and @Shrink@ (request `Shrink ft`, emit shrink list).
ctraverseFields :: Class
                -> (Type -> CoreExpr -> CoreExpr -> Synth CoreExpr)  -- ^ @ft dict field@
                -> Constructor -> [CoreExpr] -> Synth [CoreExpr]
ctraverseFields cls k = traverseFields \ft e -> do d <- field cls ft; k ft d e

-- ---------------------------------------------------------------------------
-- The witness interface
-- ---------------------------------------------------------------------------

-- | A class's synthesizer, keyed by the wrapper arity it works through.
newtype Deriver = Deriver { runDeriver :: Class -> Datatype -> Synth EvTerm }

-- | Register synthesis of a class @cls@ derived @via Stock@.  The method does
-- not mention @cls@, so the plugin selects the instance by looking it up in the
-- instance environment rather than by ordinary dispatch.
class DeriveStock (cls :: K.Type -> K.Constraint) where
  deriveStock :: Deriver

-- | A @Stock1@ synthesizer for a @(Type -> Type)@ class: given the class, the
-- constraint location, the via-target @Stock1 F@ and the inner @F@, build the
-- dictionary — or 'Nothing' if a field shape is unsupported.  (Lifted classes
-- need the parameter-variance walk, so they get the raw form rather than the
-- 'Datatype'-based 'Deriver'; the @Stock1@ 'TyCon' is recoverable as
-- @tyConAppTyCon@ of the via-target.)
newtype Deriver1 = Deriver1
  { runDeriver1 :: Class -> CtLoc -> Type -> Type -> TcPluginM (Maybe (EvTerm, [Ct])) }

-- | Register synthesis of a @(Type -> Type)@ class derived @via Stock1@ (the
-- lifted counterpart of 'DeriveStock' — e.g. @NFData1@, @Hashable1@).
class DeriveStock1 (cls :: (K.Type -> K.Type) -> K.Constraint) where
  deriveStock1 :: Deriver1

-- | The @Stock2@ analogue of 'Deriver1': given the class, the location, the
-- via-target @Stock2 P@ and the inner @P@, build the dictionary.
newtype Deriver2 = Deriver2
  { runDeriver2 :: Class -> CtLoc -> Type -> Type -> TcPluginM (Maybe (EvTerm, [Ct])) }

-- | Register synthesis of a @(Type -> Type -> Type)@ class derived @via Stock2@
-- (e.g. @NFData2@).
class DeriveStock2 (cls :: (K.Type -> K.Type -> K.Type) -> K.Constraint) where
  deriveStock2 :: Deriver2
