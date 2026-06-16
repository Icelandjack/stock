# `Stock.Override` — per-field deriving modifiers (design)

Status: design, pre-implementation. Scope: the first concrete step toward
per-field / per-position `DerivingVia` for the `stock` plugin.

## 1. Goal

Today `via Stock T` derives the plain structural instance. We want to attach
**modifiers to individual fields**, applied during synthesis — per-field
`DerivingVia`. The modifier map is part of the via-target type, so the plugin
reads it while it type-checks the `deriving` clause; at runtime there is still
only `coerce` plumbing, zero cost.

This mimics `Generically` locally: `Generically (Override A cfg)` would swap
`Rep A` for a `New_Rep_A` with new field types. We have no `Rep`; the
"structure" the synthesizer walks is the implicit field-type list, so
`Override` rewrites *that* list and splices a `coerce` at each touched leaf.

## 2. Surface

```haskell
newtype Override a cfg = Override a            -- Coercible (Override a cfg) a
type Overriding a cfg = Stock (Override a cfg) -- so users write one wrapper

-- name-keyed, flat:
deriving Monoid via Stock (Override Coord [ "x" := Sum Int, "y" := Sum Int ])

-- path-addressed (constructor / position / label), via -->:
data Person = P String Int
deriving Show via Overriding
  [ P --> 0 --> UpperCase
  , P --> 1 --> Sum
  ] Person
```

With `NoListTuplePuns` (GHC 9.10+, in range) the `'` on the list is dropped;
without it, write `'[ … ]`. The plugin sees the identical type either way.

## 3. Encoding — uninterpreted, poly-kinded `data family` markers

Markers the plugin *reads* and GHC *never reduces*. A `type` synonym would be
expanded before the plugin runs and a type family could reduce; a **data
family is generative, injective, and irreducible** — the right read-only
carrier — and (a feature of the user's) a data family may have a **free result
kind**, so we poly-kind both the argument and the result.

```haskell
type    (:=)   :: forall k j. Symbol -> k -> j
data family (:=) name m

type    (-->)  :: forall k1 k2 j. k1 -> k2 -> j
data family (-->) a b
infixr 5 -->

data Keep                                   -- identity modifier
data Wild                                   -- the "_" complement token (rest-of-scope)
```

`k` free ⇒ any modifier kind fits one slot: `Sum :: Type -> Type`, `Sum Int ::
Type`, `Choose 0 100` (Nat-indexed), a `Symbol`-ish `UpperCase`. The solver
reads each `(:=)` / `(-->)` application straight off its `TyConApp` by
injectivity; nothing else in the pipeline needs to understand them.

## 4. Addressing algebra

An entry is a **path** `<prefix> --> modifier`. The terminal hop is the
modifier; each earlier hop is interpreted **by its kind**:

| hop kind               | means                 |
|------------------------|-----------------------|
| a promoted constructor | select that ctor      |
| `Nat`                  | field by position     |
| `Symbol`               | field by label        |
| `Wild` (`_`)           | rest-of-scope complement |
| last hop               | the modifier          |

The prefix selects a node in the (constructor, field) tree; the modifier
applies to every leaf under it. **Path length = scope, shortest = broadest:**

| path             | scope                      |
|------------------|----------------------------|
| `Sum`            | every field, every ctor    |
| `P --> Sum`      | every field of `P`         |
| `"x" --> Sum`    | every field labelled `x`   |
| `P --> 0 --> Sum`| exactly that one cell      |

`(:=)` is just the 2-hop label path `"x" := m  ≡  "x" --> m`; the flat
name-keyed list in §2 is sugar for label-only paths.

Kind-directed dispatch is the same principle as the modifier-saturation rule
(§6): the kind *is* the discriminator throughout.

### 4a. Selecting by field *type* (`As`)

A fourth selector — *by the field's type* — is `generic-override`'s core mode
and the one we lacked. A type-kinded hop can't ride the `-->` path, because it
would be indistinguishable from the terminal modifier (also `Type`); so type
selection gets its own operator, `As`, with the selector on the left:

```haskell
Bool   `As` Any          -- every field whose type is Bool
[a]    `As` ListOf a      -- every field of type [a]   (matched up to the datatype's vars)
[]     `As` ListOf        -- every field of shape [_]  (by head constructor; modifier unsaturated)
"baz"  `As` Uptext        -- a Symbol selector ⇒ by name (same as :=)
```

`As`'s left operand is a **kind-dispatched selector**: `Symbol` ⇒ by name,
`Type` ⇒ by exact type, `Type -> Type` (a bare constructor) ⇒ by head
constructor. Matching a type selector containing the datatype's own variables
(`[a]`) is a one-way match of the field type against the selector, up to those
vars; the modifier may mention them. So one operator covers
`generic-override`'s `As`/`With`, and `At "C" n` is our `C --> n` path. The
per-cell `Coercible` check (§6) still validates every match.

## 5. No-overlap law (and coverage)

**No cell is claimed by more than one entry.** Overlap — across *any* selector
kinds (a type rule and a name rule landing on the same cell) — is not
arbitrated, it is **rejected**. There is no precedence order to learn, so each
cell's modifier is unambiguous by construction. This is the one integrity
guarantee, and it holds uniformly over `As` / `:=` / `-->` entries.

**Coverage is sparse by default**: a cell matched by no entry keeps its type
unchanged (identity). This is what `generic-override` does, and it's the right
default for type rules — `String \`As\` CharArray` is meant to leave non-String
fields alone, and it *auto-covers a newly added String field* for free. An
optional **total** mode (a distinct wrapper, or requiring a trailing `_`)
re-imposes "every cell must be claimed", for the add-a-field-get-told safety;
note type rules already give partial coverage-robustness without it.

The complement token `_` (`Wild`) means *"the cells in this scope not claimed
by a sibling"* — set difference, so it can never overlap. It refines without
overlapping and is the explicit "everything else":

```haskell
[ P --> 0 --> Product   -- this one cell
, P --> _ --> Sum        -- the rest of P, disjoint by definition (also discharges totality)
]
```

The solver knows the constructors and fields, computes each entry's cell-set,
resolves `_` last as the complement, rejects any overlap, and (in total mode)
any gap — with precise errors (§7).

## 5a. Two config shapes — entry-list vs positional Code

Both decode to the same internal per-cell modifier map; they are two views.

**Entry-list** (§3–§5) — `[ "x" := Sum, [] \`As\` ListOf, P --> 0 --> M ]`.
Sparse, selector-addressed, heterogeneous selectors *and* modifiers. It stays a
homogeneous promoted list because each entry is wrapped in a poly-kinded `data
family` marker (`:=` / `As` / `-->`) whose **result** kind is uniform — the
marker absorbs the inner kind, so the list never sees it.

**Positional SOP Code** — the full sum-of-products shape, lightly edited:

```haskell
[[ Sum, Identity ], [ Const (Sum Int) ]]   -- mirrors the datatype's [[field]] structure
```

Here the elements *are* the modifiers, with no wrapper, so the list must be
**homogeneous in element kind** — and that is the crux the user flagged: you
cannot mix a saturated `Sum Int :: Type` and an unsaturated `Sum :: Type ->
Type` in one bare list. So a positional Code must commit to one element kind:

- **`[[Maybe Type]]`** (`Nothing` = no change, `Just T` = replace): simple and
  naturally partial, but **saturated-only** — it cannot hold a higher-kinded
  `Sum`, because `Sum :: Type -> Type` doesn't fit element kind `Type`.
- **`[[Type -> Type]]`** (a *field-transformer* per cell): higher-kinded-native
  and still partial — **`Identity` is the no-op** (no `Maybe` needed), `Sum`
  wraps the field at its own type, a const-transformer pins a fixed type. To
  admit higher-kinded modifiers in the positional shape you must indeed write
  **everything as `k -> Type`** (the field's type → the new type), with
  `Identity` standing in for "leave alone".

So the answer to "must everything be `k -> Type`?" is: **yes, for the bare
positional Code under plain `Stock`** — uniform element kind forces a
transformer kind, and `Identity`/`Const`-style transformers recover identity
and pinning. The entry-list form escapes this only because its `data family`
markers hide the kind; drop the wrapper and write the raw `[[…]]`, and
homogeneity makes the `Type -> Type` normal form mandatory. `[[Maybe Type]]`
remains the simpler saturated-only positional form.

### 5a-i. `Stock1`/`Stock2`: the parameter buys back the `Type` lane

`Stock` derives at kind `Type`, with no parameter to apply — that's *why* it's
forced to `Type -> Type`. But `Stock1`/`Stock2` derive for a type constructor
(`Foo :: Type -> Type`), so the parameter `a` is in scope, and a higher-kinded
modifier can **always be fully applied** to it. So both lanes are available:

```haskell
data Foo a = MkFoo (List a) (List a)
deriving Functor via Overriding1 Foo [ [ List a, Reverse List a ] ]  -- elements :: Type
deriving Functor via Overriding1 Foo [ [ List,   Reverse List   ] ]  -- elements :: Type -> Type
```

The two are equivalent **by eta**: `\a -> g a ≡ g`, so `[[ f a, g a ]]` and
`[[ f, g ]]` are the same swap, one applied and one bare. And eta-reducibility
is not incidental — it's the *precondition*. The parameter `a` must occur
eta-reducibly (last variable, in applied tail position) for the field to be
functorial at all; that is exactly GHC's `DeriveFunctor`/`Generic1` rule, and
in our `Stock1` internals it is exactly the `FApp` field classification (`f a`,
i.e. `Rec1 f`/`(:.:)`), versus `FParam` (`a`, `Par1`) and `FConst` (no `a`). An
`Override1` cell only swaps the functor inside an `FApp`. So the solver
eta-normalises (peel the trailing parameter) and a non-eta-reducible field —
`a` in a non-tail position, e.g. `a -> a` — is rejected for the very same
reason stock `deriving Functor` rejects it.

This is also why the missing type-level lambda (§ the `\a -> …` experiment)
costs nothing here: the *only* dependence a lambda could express that eta
cannot is precisely the non-functorial one that's already illegal. Every valid
Functor override eta-reduces to a *named* functor — no lambda ever needed. The `Override` wrappers
therefore come in the same arities as the newtypes — `Override`/`Override1`/
`Override2` for `Stock`/`Stock1`/`Stock2` — and each extra parameter is one
more thing you may saturate against.

Residual constraints unchanged: you still cannot *mix* `Type` and `Type ->
Type` in one positional list, and a field that doesn't mention the parameter
(a constant `Int` field) gains nothing from saturation — it stays `Identity`/
`Const`, because there's no `a` in it to apply.

## 6. Modifier semantics — saturation decides pin vs broadcast

A cell at type `τ` with modifier `m`:

- `m :: Type -> Type` (unsaturated) — **broadcast**: the cell becomes `m τ`,
  adapting to each leaf's own type. `P --> Sum` makes every field of `P` a
  `Sum` *of its own type* (`Sum Int`, `Sum Bool`, …). Always well-typed across
  heterogeneous fields.
- `m :: Type` (saturated) — **pin**: the cell must already be that type. `"x"
  := Sum Int` is legal only where `x :: Int`.

Both verdicts fall out of a per-cell `Coercible τ (m τ)` / `Coercible τ m`
check — `Coercible Bool (Sum Int)` fails, `Coercible Bool (Sum Bool)` holds.
The saturation of the modifier *is* the broadcast-vs-pin switch; the type
checker enforces it for free. `Keep` is the identity (no coercion).

## 7. Well-formedness rules (with error messages)

1. **single constructor not required** — multi-constructor is allowed; `-->`
   names the constructor, and label broadcast spans constructors. But a field
   with **no label addressed only by name** in an ambiguous multi-ctor type is
   rejected — use a `-->` path. (v1 may start single-ctor; see §9.)
2. every concrete address resolves to ≥1 real cell — else
   `"Override: P has no field at position 3"` / `"unknown field x"`.
3. **disjoint**: no two entries claim the same cell —
   `"cell (P, 0) is claimed by both  P --> Sum  and  P --> 0 --> Product;`
   `make them disjoint (e.g. P --> _ --> Sum)."`
4. **total**: every cell is claimed (after resolving `_`) — else
   `"field (P, 1) has no modifier (add an entry or a _ --> Keep default)."`
5. per cell `Coercible τ modifier` (saturated) or `Coercible τ (modifier τ)`
   (unsaturated) must hold — else the usual coercion error, surfaced against
   the cell.

## 8. Implementation plan

The structure-extraction point is `mkRepr :: Maybe TyCon -> Type -> Maybe
Repr` (`Stock.Internal`), which destructures `Stock T` into a `Repr` (inner
type, unwrap coercion, constructors + field types). `toDatatype` packages it
for the `Deriver`s, which walk it via `matchSOP` / `injectSOP` / `field`
(`Stock.Derive`). Everything keys off `conFields` (field types) and the field
values bound by `matchSOP`.

Hook — one pre-pass, no new synthesis machinery:

1. **Recognise** `Stock (Override T cfg)` in `mkRepr` (match the `Override`
   TyCon; fall through to the plain path otherwise). Build the ordinary `Repr`
   for `T`.
2. **Decode** `cfg`: walk the promoted list, each element a `-->`/`:=` chain,
   into `[(Path, ModifierType)]`. Read each hop by kind (§4).
3. **Resolve** each path to its set of cells `(ctorIndex, fieldIndex)` against
   the `Repr`; resolve `Wild` to the in-scope complement; **check the partition
   law** (§5, §7) and emit precise errors.
4. **Rewrite** the `Repr`/`Datatype` per cell: replace the field type `τ` with
   the modifier type (`m` or `m τ`) and record the per-cell coercion `τ ↔
   modifier` (a newtype `coerce`, both directions).
5. **Apply transparently**: `matchSOP` binds the real field, then hands the
   continuation the value *coerced to the modifier type*; `injectSOP` coerces
   the synthesizer's modifier-typed result *back* before reapplying the data
   constructor. So `field cls ft` naturally requests `C modifier`, and **every
   existing `Deriver` (Eq, Ord, Show, Monoid, …) works unchanged** — it only
   ever sees modifier types and coerced values.

Thus per-field override is purely a `Datatype`-rewrite + coercions in the two
SOP eliminators; the synthesizers are untouched. This is the same homogeneous
`Deriver` path as today.

## 9. v1 boundaries / deferred

- **v1** may restrict to single-constructor types (bare names unambiguous,
  one cell per name) to defer constructor-axis addressing; `-->` paths and
  multi-ctor broadcast are the immediate follow-up since the cell machinery is
  identical.
- **via-fields** (`x :: Int via Sum Int` on the declaration) desugar into these
  entries; a single-modifier field-via is trivial, a multi-modifier one needs a
  `@Class` key (the genuinely irreducible case). Sugar over this backend.
- **bare constructor/label names** (`P`, `x` without ticks/quotes) need a
  parse-stage source plugin (`HsTyVar → HsTyLit`/promoted con) to beautify;
  `'P` / `"x"` work today. `=`-not-`:=` is preprocessor-only and not worth it.
- **target-type inference** (`Overriding ` [ … ] without the trailing `T`) is
  possible from a constructor in the path (`'P :: … -> Person`) but only when
  one is named; keep the explicit `T` as the robust default.

## 10. Open questions

- Resolution order of `_` when nested at different scopes (`P --> _` vs a
  global `_`): define complement relative to the *narrowest* enclosing scope.
- Should `Keep`-only configs (all identity) be allowed as a no-op, or warned as
  pointless?
- Do we want `_` to be spellable as the actual underscore via `NoListTuplePuns`
  /source plugin, or keep the named `Wild`/`_` token?
