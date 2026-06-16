# Iterating through play

A method for stress-testing a deriving plugin (or any generic machinery): take
a working example and **turn the knobs** — nest it deeper, make its pieces
polymorphic, and substitute algebraically-equal forms — then sort each outcome
into one of three bins.  The point is that a *rejection* is information: it is
either correct mathematics, a correct soundness check, or a genuine bug, and the
play tells you which.

All examples below derive with `-fplugin Stock`; nothing is hand-written.

## The knobs

1. **Iterate depth.**  `Compose [] []` is just depth 2.  What about depth 3,
   6, an arbitrary association tree `((f . g) . h) . (i . (j . k))`?
2. **Make it polymorphic.**  Replace the concrete `[]` with an abstract functor
   variable `f`.  This forces the derivation to *produce a constraint*
   (`Functor f`) instead of discharging a concrete instance — it tests the
   machinery, not one instantiation.
3. **Test identities.**  `Compose Identity [] ≅ [] ≅ Compose [] Identity`; and
   `Compose` is associative.  Replacing a field's modifier with an
   algebraically-equal form must leave behaviour invariant.

## What the knobs revealed

### Depth iterates freely (for `Compose`)

Overriding a nested field via a nested `Compose` works at any depth — the `+1`
reaches the bottom of a six-deep list:

```haskell
data D6 a = D6 [[[[[[a]]]]]] a
  deriving Functor via Overriding1 D6
    '[ '[ Compose (Compose [] (Compose [] [])) (Compose (Compose [] []) []), Keep ] ]
-- fmap (+1) (D6 [[[[[[1]]]]]] 9)  ==  D6 [[[[[[2]]]]]] 10
```

Because `Compose` of `Functor`s is always a `Functor`, the reshape recursion is
total.

### Identities hold

`[]`, `Compose Identity []`, and `Compose [] Identity` all derive the *same*
`Functor` for a `[a]` field; the two associations of a three-deep `Compose`
agree.  The plugin respects the functor-composition monoid laws — verifiable by
deriving via each form and checking equal behaviour.

### Variance does **not** iterate freely (for the function-nest `Foo`)

```haskell
newtype Foo i o = Foo ((((o -> i) -> o) -> i) -> (((i -> o) -> i) -> o))
  deriving Functor    via Stock1 (Foo i)
  deriving Profunctor via Stock2 Foo
```

`Foo` derives both.  Deepening the towers by a *balanced* amount (keeping each
tower's net variance) still derives.  Deepening them *unbalanced* is **rejected**
with "supports only covariant fields" — because `o` then genuinely sits in a
contravariant position, so there is no lawful `Functor`.  The plugin computes
net variance and is correct in both directions.

### Polymorphism surfaces a role wall — which a constraint dissolves

One level of abstract `Compose` is fine:

```haskell
data Dfg f g a = Dfg (f (g a)) a
  deriving Functor via Overriding1 (Dfg f g) '[ '[ Compose f g, Keep ] ]
-- (Functor f, Functor g) => Functor (Dfg f g)
```

A *nested* `Compose`-tree over abstract functors is rejected **by default**:
unwrapping it forces coercing *under* an abstract functor (`f (Compose … a) ~R
f (…)`), and a bare type variable `f :: Type -> Type` has a nominal argument
role.  The first instinct — *"is this really a wall, or a missing constraint?"*
— is the right one.  It is a missing constraint, at the *surface*: add the
quantified `Representational1 f = (forall x y. Coercible x y => Coercible (f x)
(f y))` for each abstract functor and the *same* nested-abstract tree
type-checks:

```haskell
data Tree f g h i j k a = Tree (f (g (h (i (j (k a)))))) a
deriving via Overriding1 (Tree f g h i j k)
              '[ '[ Compose (Compose (Compose f g) h) (Compose i (Compose j k)), Keep ] ]
  instance ( Functor f, {- … -} Functor k
           , (forall x y. Coercible x y => Coercible (f x) (f y)) {- … one per functor -} )
        => Functor (Tree f g h i j k)
-- type-checks; fmap (+1) runs at -O0 and gives the right answer
```

But this is exactly where the *next* instinct earns its keep: **run it under
`-dcore-lint`, not just `-O0`.**  As first written, the synthesized `fmap` for
the nested-abstract case was *ill-scoped Core* — an out-of-scope type variable —
which lint rejected even though it ran fine at `-O0` (the offending variable is
type-level, erased before runtime):

```
*** Core Lint errors : in result of Desugar (before optimization) ***
    The type variable @a_… is out of scope
```

The root cause was the *reshape-validation* wanted.  Every override emits a
GHC-checked `field a ~R modifier a` so an unsound reshape is rejected — but it
was phrased with the **method's own** type variable `a` free in it, while the
plugin emits it at the *instance* `CtLoc`.  For a single newtype unwrap GHC
inlines the proof and nothing leaks; but here GHC discharged it via
`Representational1` into let-bound `Coercible` *dictionaries*, and bound them at
instance scope — where the method-local `a` is out of scope.  The fix: validate
the reshape at the **closed** type `()` instead of the method binder (the check
is parametric in the element, so it still rejects bad overrides — two-parameter
classes use *distinct* closed types so an order-swap like `a->b` vs `b->a` stays
visible).  The evidence then mentions only instance-level variables, and the
nested-abstract reshape now derives, runs, *and* is lint-clean.  Single-level
abstract `Compose` (`Dfg` above) and any *concrete* nesting (depth-6 `[]`) were
lint-clean throughout; the leak was specific to the nested-*abstract* path, found
only because the identity/polymorphism play pushed into it *and* lint was on.

`Representational1 f` itself holds for essentially every real `Functor`:

 + concrete functors (`[]`, `Maybe`) have representational argument roles, so it
   is discharged for free — which is why a *concrete* nested tree worked all
   along with no constraint written;
 + even a newtype annotated `type role N nominal` satisfies it as long as its
   *constructor is in scope* (`Coercible` unwraps the newtype, sidestepping the
   annotation).

The one place it is honestly unprovable is an *abstract* type — constructor
hidden behind a module boundary — whose role is nominal (*"couldn't match `x`
with `y` … the head of a quantified constraint"*).  That is a real
library-design nominal boundary, not a plugin artefact — the same nominal-role
wall that stops `Traversable` from a bare `deriving via`.

## The three bins

| outcome | example | verdict |
|---------|---------|---------|
| **expected mathematics** | unbalanced `Foo` rejected; `Traversable` not bare-derivable; a *constructor-hidden* nominal functor | genuinely no lawful instance |
| **expected soundness**   | `Compose [] []` needs `Compose(..)` in scope (the validated reshape asks GHC for `Coercible`) | a feature, not a bug |
| **actual bug (found, fixed)** | (1) `Applicative` consulted the override only for fields already shaped `h a`, so a nested `[[a]]` was wrongly rejected; (2) the nested-abstract `Compose` reshape emitted ill-scoped Core because the validation carried a method-local type variable | both real, both found by this play, both fixed (the validation now runs at a closed type) |

A naive plugin would *accept* the unbalanced `Foo` and the nested-abstract
`Compose` by emitting an unchecked `coerce`, and miscompile.  The validation
guard turns every reshape into a GHC-checked `Coercible` obligation, so the
rejections are principled and the error messages are GHC's own.

## Why it pays

Each knob either **confirms a principle** (depth-6 still reaches the bottom ⇒
the recursion is total; both associations agree ⇒ the laws hold) or **exposes an
asymmetry** (`Functor` accepts what `Applicative` rejected ⇒ a bug; one-level
abstract `Compose` works but nested doesn't ⇒ the role wall).  The test-suite is
instrumented for exactly this: `overrides` encodes the "confirm a principle"
cases, `negative` encodes the "this must be rejected" cases.
