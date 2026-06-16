# Changelog

## 0.1.0.3

* Reject a field whose type is a *data/type-family instance* (e.g.
  `cardano-crypto`'s `VerificationKey HydraKey`) with a clear error instead of
  a GHC codegen panic (`StgToCmm: variable not found`). Such a field's
  representation tycon differs from its source type — the same class as
  `UNPACK`ed/unboxed strict fields. Full support is future work; until then the
  rejection is clean rather than a crash.
* Fix `Applicative` via `Overriding1`: a per-field modifier now reshapes *any*
  field (e.g. a nested `[[a]]` via `Compose [] []`), matching
  `Functor`/`Foldable`/`Traversable`. Previously the modifier was consulted only
  for fields already of shape `h a`, so nested fields were wrongly rejected as
  "supports only covariant fields".
* New `overrides` test-suite: derive each class through a modifier newtype
  (`Sum`/`Product`/`Any`/`All`/`Min`/`Max`/`Down`/`Compose`/`ZipList`/`Op`/
  `Basic`/`Kleisli`/…) with runtime assertions that the reshape took effect.
* `Eq1`, `Ord1`, `Show1` and `Read1` now walk *nested* functor fields (e.g.
  `[[a]]` becomes `liftEq (liftEq f)`), matching `Functor`/`Foldable`/
  `Traversable`; previously they were one-level only and rejected nested fields
  as "supports only covariant fields". A per-field `Override1` now also reshapes
  a nested field for these classes (and the reshape is validated, rejecting an
  unsound override). A value-polymorphic `Stock2`/`Category` modifier (e.g.
  `Op cat` with `cat` free) is no longer clobbered by the modifier re-kinding.
* Fix a per-field `Override1` modifier whose kind is polymorphic (e.g. `Const`,
  whose second argument is kind-polymorphic): a constant field reshaped via
  `Const (Sum Int)` was requested at a skolem kind and found no instance
  (`No instance for Functor (Const (Sum Int))`). The modifier's kind is now
  defaulted to `Type -> Type`, so `deriving (Functor, Applicative) via
  Overriding1 T '[ T at 0 via Const (Sum Int), … ]` works (the `Const` field
  contributes its `Monoid` to `Applicative`). Genuine functor variables (a
  polymorphic `Compose f g`) are left untouched.
* `Generic1 (Overriding1 F cfg)` now reshapes *constant* fields too, so an
  `Override1` config leaks into `Rep1` uniformly. Previously only functorial
  (`h a`) fields were reshaped in `Rep1`; a constant field (e.g. `Int`) kept its
  original leaf, so `deriving (Functor, Applicative) via Generically1 (Overriding1
  F '[ F at 0 via Const (Sum Int), … ])` failed with `No instance for Monoid Int`.
  Now `Generically1 (Overriding1 …)` sees the reshaped leaves (the `Int` field
  becomes a `Rec1 (Const (Sum Int))`).
* Fix ill-scoped Core from a per-field reshape over an *abstract* functor (e.g.
  a nested `Compose f (Compose g …)` with `Representational1` constraints). The
  reshape-validation constraint carried the method's own type variable and was
  emitted at instance scope, so its (dictionary-shaped) evidence referenced a
  variable that was out of scope — `-dcore-lint` rejected it though it ran at
  `-O0`. The validation now runs at a closed type, keeping the evidence
  well-scoped while still rejecting unsound overrides. Applies to `Functor`,
  `Foldable`, `Traversable`, `Applicative`, `Bifunctor`/`Bifoldable` and
  `Category`.

## 0.1.0.1

* `Category` via `Overriding2`: accept the field-keyed override forms
  (`Con at i via M`, `name via M`), not only the dense `'[ '[ .. ] ]`
  positional list; and fix a kind bug where a modifier's phantom
  parameters (e.g. `Basic m a b`) were left at skolem kinds.
* Per-field override reshapes are now validated: an override that maps a
  field to a non-coercible modifier (e.g. `Maybe via []`, `Int via Op`)
  is rejected with a clear error instead of silently emitting an unsound
  coercion. Applies to `Functor`, `Foldable`, `Traversable`,
  `Applicative` (`Stock1`) and `Category` (`Stock2`); the other classes
  already validated.
* Documentation: fixed the package-description rendering (cabal-version
  3.0 needs real blank lines, not the `.` convention) and made the class
  / wrapper / companion links resolve.

## 0.1.0.0

Initial release.

* A GHC type-checker plugin that synthesizes class instances for the
  `Stock` / `Stock1` / `Stock2` newtype wrappers, used through `DerivingVia`
  — no `Generic`, no hand-written boilerplate.
* Built-in classes — `Stock`: `Eq`, `Ord`, `Show`, `Read`, `Semigroup`,
  `Monoid`, `Enum`, `Bounded`, `Ix`, `Generic`; `Stock1`: `Functor`,
  `Contravariant`, `Foldable`, `Applicative`, `Generic1`, `Eq1`, `Ord1`,
  `Show1`, `Read1`, `Traversable`, `TestEquality`, `TestCoercion`;
  `Stock2`: `Bifunctor`, `Bifoldable`,
  `Eq2`, `Ord2`, `Show2`, `Read2`, `Category`, `Bitraversable`.
  `Traversable`/`Bitraversable` are synthesized at the wrapper and used
  directly or via the one-liner `traverse g = fmap unStock1 . traverse g
  . Stock1` (a bare `deriving via` can't coerce them onto your type — the
  result `f (t b)` puts the wrapper under an abstract applicative).
* Extensible: satellite packages add new classes with no configuration
  change, via `DeriveStock` instances on the `Stock.Derive` SDK.
* Per-field deriving modifiers via `Stock.Override`: `deriving C via Stock
  (Override T cfg)` (or the type-first synonym `Overriding T cfg`) rewrites
  individual fields' types during synthesis (per-field `DerivingVia`,
  zero-cost). Fields are addressed by name, type, or position (`At`); each
  modifier is pinned (`Sum Int`) or broadcast to the field's own type (`Sum`).
  The same `-fplugin Stock` also lowers a lowercase surface —
  `Override T [ x via Sum, C at 0 via Product ]` — to that marker form at
  parse time.
* Synthesized instances verified against GHC's stock-derived twins and
  benchmarked to identical performance; all evidence passes `-dcore-lint`.
  `Eq`/`Ord`/`Enum`/`Functor`/`Bounded`/`Foldable` optimise to
  byte-identical Core (machine-checked with `inspection-testing`);
  `Traversable`/`Bitraversable` are byte-identical to the natural
  hand-written definition. `Read` (and `Read1`) build `readPrec` as GHC's
  derived `Read` does, so they are byte-faithful including the order of
  ambiguous infix parses.
* Tested on GHC 9.6, 9.8, 9.10, 9.12 and 9.14 (`stock-deepseq`: 9.8+).
