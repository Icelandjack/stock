{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE StandaloneKindSignatures #-}
-- | Per-field deriving modifiers for the Stock plugin.
--
-- @Override a cfg@ wraps @a@ with a type-level configuration @cfg@ that the
-- plugin reads while it synthesizes the instance: each entry names a field and
-- the modifier to run on it (per-field @DerivingVia@).  At runtime @Override@ is
-- just @a@ (a newtype), so there is no cost.
--
-- > data Coord = Coord { x :: Int, y :: Int }
-- >   deriving Semigroup
-- >     via Stock (Override Coord '[ "x" ':= Sum, "y" ':= Product ])
--
-- The config is an uninterpreted, poly-kinded marker the solver decodes off the
-- type — never reduced.  See @docs\/override-design.md@.
--
-- == Addressing a field
--
-- A field is addressed by name (@\"x\" ':= m@), by type (@Int ':= m@, every
-- @Int@ field), or by position (@'At' Coord 0 ':= m@).  A modifier is /pinned/
-- (@Sum Int@) or /broadcast/ to the field's own type (@Sum@).  A whole entry
-- may instead be positional — one inner list per constructor, one cell per
-- field — where 'Keep' (written @_@) leaves a field untouched:
--
-- > deriving Semigroup via Stock (Override Coord '[ [Sum, Keep] ])  -- field 0 via Sum
--
-- == Surface sugar (the @-fplugin Stock@ source pass, "Stock.Surface")
--
-- The honest marker form is verbose, so the same plugin lowers a quote-free
-- surface at parse time, /scoped to @Override@ applications/:
--
-- > Override Coord [ x via Sum, Coord at 0 via Sum, _ ]     -- what you write
-- > Override Coord '[ "x" := Sum, At Coord 0 := Sum, Keep ] -- what the solver reads
--
-- namely: a bare lowercase selector becomes a @Symbol@ (@x@ ⟶ @\"x\"@), @via@
-- becomes ':=', @at@ becomes 'At', and a wildcard @_@ becomes 'Keep'.
--
-- == Higher order
--
-- 'Override1' \/ 'Override2' reshape the /functor/ of a field rather than its
-- element type (an @h a@ field becomes @m a@), so the lifted instance
-- (@Functor@, @Eq1@, @Applicative@, …) uses @m@'s method.  See 'Override1'.
module Stock.Override
  ( Override(..)
  , Overriding
  , Override1(..)
  , Overriding1
  , Override2(..)
  , Overriding2
  , type (:=)
  , type (-->)
  , At
  , Keep
  ) where

import Data.Kind (Type)
import GHC.TypeLits (Nat)
import Stock.Type (Stock, Stock1, Stock2)

-- | @Overriding a cfg = Stock (Override a cfg)@ — the per-field wrapper read
-- through @Generically@.  Because the plugin makes @Generic@ honour @Override@
-- (the @Rep@ carries the modifier field types), @deriving C via Generically
-- (Overriding A cfg)@ derives /any/ @Generic@-based class over @A@ with the
-- per-field modifiers applied.  The Generic-facing twin of using 'Stock' +
-- 'Override' directly with the built-in synthesizers.
type Overriding :: forall k. Type -> k -> Type
type Overriding a cfg = Stock (Override a cfg)

-- | The one-parameter analogue of 'Override': @Override1 f cfg@ wraps a
-- one-parameter constructor @f@ for use through @Stock1@.  Each positional
-- modifier @m@ (a @k -> Type@) reshapes the /functor/ of an @h a@ field to
-- @m a@ — so e.g. a @[a]@ field becomes @ZipList a@ and the derived
-- @Applicative@ zips instead of taking the cartesian product.  A newtype, so
-- @Coercible (Override1 f cfg a) (f a)@.
type Override1 :: forall k j. (j -> Type) -> k -> (j -> Type)
newtype Override1 f cfg a = Override1 (f a)

-- | @Overriding1 f cfg = Stock1 (Override1 f cfg)@ — the @Stock1@-facing
-- per-field wrapper.  @deriving Applicative via Overriding1 F '[ '[ZipList] ]@
-- reshapes @F@'s @[a]@ field into @ZipList a@ before deriving.
type Overriding1 :: forall k j. (j -> Type) -> k -> (j -> Type)
type Overriding1 f cfg = Stock1 (Override1 f cfg)

-- | The two-parameter analogue of 'Override': @Override2 p cfg@ wraps a
-- two-parameter constructor @p@ for use through @Stock2@.  Each positional
-- modifier @m@ (a @Type -> Type -> Type@) reshapes its field to @m a b@ — the
-- modifier applied to /both/ datatype parameters — turning the field into a
-- per-field @Category@.  A newtype, so @Coercible (Override2 p cfg a b) (p a b)@.
type Override2 :: forall k. (Type -> Type -> Type) -> k -> (Type -> Type -> Type)
newtype Override2 p cfg a b = Override2 (p a b)

-- | @Overriding2 p cfg = Stock2 (Override2 p cfg)@ — the @Stock2@-facing
-- per-field wrapper.  @deriving Category via Overriding2 '[ '[Basic (Sum Int),
-- Basic String, Kleisli Maybe] ] Foo@ reshapes each field of @Foo a b@ into a
-- @Category@ and derives @Category@ pointwise over them.
type Overriding2 :: forall k. (Type -> Type -> Type) -> k -> (Type -> Type -> Type)
type Overriding2 p cfg = Stock2 (Override2 p cfg)

-- | @a@ with a per-field override configuration @cfg@.  A newtype, so
-- @Coercible (Override a cfg) a@; @cfg@ is phantom (read by the plugin only).
-- Poly-kinded in @cfg@ so it accepts both config shapes (see
-- @docs\/override-design.md@ §5a): the /entry list/ @'[ "x" ':= Sum, … ]@
-- (@cfg :: [Type]@) and the /positional/ @'[ '[Sum Int, Keep, Keep] ]@ — one
-- inner list per constructor, one element per field (@cfg :: [[Type]]@).
type Override :: forall k. Type -> k -> Type
newtype Override a cfg = Override a

-- | The positional no-op modifier: a field whose slot is @Keep@ is left at its
-- own type.  Written @_@ in source (the @-fplugin Stock@ surface pass lowers the
-- type wildcard to @Keep@), so @'[ '[Sum Int, _, _] ]@ overrides only the first
-- field.  Poly-kinded (a free-result-kind 'data family') so it sits in a list
-- beside modifiers of /any/ kind — @Sum Int :: Type@ or @Sum :: Type -> Type@ —
-- without breaking the list's kind homogeneity.  An uninterpreted marker the
-- plugin reads; never reduced.
type Keep :: forall k. k
data family Keep

-- | A single config entry: the field @name@ (a 'Symbol') gets modifier @m@.
-- Poly-kinded in @m@, so a saturated modifier (@Sum Int :: Type@) and an
-- unsaturated one (@Sum :: Type -> Type@) both fit; the plugin dispatches on
-- @m@'s kind (pin vs. broadcast).  An uninterpreted 'data family' — generative,
-- injective, never reduced — so the solver reads it back verbatim.
type (:=) :: forall sel k. sel -> k -> Type
data family (:=) sel m

-- | A positional selector: field @pos@ of constructor @con@.  Used /prefix/ on
-- the left of @(:=)@ — @At Con 0 := m@ — so the surface keeps a single infix
-- operator.  Like '(:=)' it is an uninterpreted, poly-kinded marker.
type At :: forall kc sel. kc -> Nat -> sel
data family At con pos

-- | A path hop: @h '--> rest@.  Each non-terminal hop selects a node — a
-- promoted constructor (that constructor), a 'Nat' (field by position) or a
-- 'Symbol' (field by label) — and the terminal hop is the modifier; the
-- modifier applies to every field under the prefix.  So @'P '--> m@ overrides
-- every field of @P@ and @'P '--> 0 '--> m@ overrides only its first field
-- (design §4).  Poly-kinded, uninterpreted, never reduced.
type (-->) :: forall k1 k2 j. k1 -> k2 -> j
data family (-->) a b
infixr 5 -->
