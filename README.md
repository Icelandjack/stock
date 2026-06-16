# stock

Constraint solving plugin that enables extensible, composable deriving
without `GHC.Generics`.

It enables deriving through a `Stock(1,2)` newtype that the plugin
generates instances for at compile-time: `Cls (Stock A)`. This
synthesises class instances directly in GHC Core, same as
hand-written, with no `Generic` deriving.

The classes each wrapper synthesises:

+ `Stock`: `Eq`, `Ord`, `Show`, `Read`, `Semigroup`, `Monoid`, `Enum`, `Bounded`, `Ix`, `Generic` (that's right)
+ `Stock1`: `Functor` / `Contravariant`, `Foldable`, `Applicative`, `Generic1`, `Eq1`, `Ord1`, `Show1`, `Read1`, `Traversable`†, `TestEquality`, `TestCoercion`
+ `Stock2`: `Bifunctor`, `Bifoldable`, `Eq2`, `Ord2`, `Show2`, `Read2`, `Category`, `Bitraversable`†

(`unpack` / unboxed-strict fields are rejected, with a clear error)

† `Traversable` / `Bitraversable` are synthesized at the wrapper (`Stock1
F` / `Stock2 P`) and usable directly, or put on your own type with a
one-liner:

```haskell
instance Traversable F where
  traverse g = fmap unStock1 . traverse g . Stock1
```

A bare `deriving via Stock1 F` can't reach them: `traverse`'s result `f
(t b)` puts the wrapper under an *abstract* applicative `f`, and
coercing under an abstract `f` (nominal role) is unsound — the same wall
that stops `GeneralizedNewtypeDeriving`. The instance itself is perfectly
ordinary (it's what GHC's own `DeriveTraversable` builds), so the
one-liner — which re-wraps with a real `fmap`, not a coercion — gives you
the instance, and it honours `Override1` / `Override2` (which
`deriving stock Traversable` can't).

```haskell
{-# options_ghc -fplugin Stock #-}

{-# language DerivingVia #-}

import Stock

data Colour = Red | Green | Blue
  deriving (Eq, Ord, Show, Read, Enum, Bounded, Ix) via 
    Stock Colour

data Tree a = Leaf | Node (Tree a) a (Tree a)
  deriving (Eq, Ord, Show) via 
    Stock (Tree a)

data Trio a = Trio Int a [a]
  deriving (Functor, Foldable) via 
    Stock1 Trio
```

The plugin must be enabled (`-fplugin Stock`, in `ghc-options` or a
per-file `options_ghc`). 

## How it works

For a wanted `Cls (Stock T)` the plugin unwraps the newtype with its
coercion, matches `T`'s constructors and builds the _Cls_-class
dictionary directly as Core, requesting each field's own instance as a
fresh wanted (GHC solves `Eq Int` etc. itself). It's direct synthesis
of the wrapped constraint, not delegation.

## Per-field modifiers

```haskell
newtype Override a config = Override a
```

`Override` reshapes individual fields during synthesis by specifying
their behaviour (zero-cost).

```haskell
data One = One { x :: Int, y :: Int }
  deriving (Semigroup, Monoid)
  via Overriding One
    [ x via Sum, y via Product ]
```

combines `x` additively and `y` multiplicatively.

There are a few methods of addressing a field, the plugin allows minor
notational conveniences.

+ `x via F` (`"x" := F`), modifies the field with the `F` wrapper
+ `Int via F` (`Int := F`), modifies every `Int` field
+ `Con at 0 via F` (`At Con 0 := F`), modifies field 0 of constructor
+ `'Con --> F`, a path: modifies every field of `Con`; `'Con --> 0 --> F`
  only its field 0. Each non-terminal hop is a constructor, a position
  (`Nat`) or a label (`Symbol`); the terminal hop is the modifier
+ `'[ [F, _] ]` (`'[ [F, Keep] ]`), modifies field 0 only, `_` keeps field

Each modifier is either particular via field `F Int`, a constructor to
modify `F` or a blank `_` (or `Keep`) which leaves a field untouched.
A function-typed modifier needs no parentheses: `x via a -> f b` reads as
`x := (a -> f b)`, since `via` binds looser than `->`.

**The surface plugin.** The lowercase, quote-free surface (`x via Sum`,
`Con at 0`, the `_` blank) is lowered to the honest marker form the
solver reads (`"x" := Sum`, `At Con 0`, `Keep`) by the same `-fplugin
Stock` at parse time (`Stock.Surface`). The generated markers (`:=`,
`At`, `Keep`) are qualified to match however you imported
`Stock.Override`, so `import Stock.Override qualified as O` with
`O.Override … '[ … via Sum, _ ]` resolves too.

### Higher-order

`Override1` / `Override2` lift the same idea over type constructors
instead of types.

```haskell
data Zip a = Zip [a]
  deriving 
    (Functor, Applicative, Foldable) 
  via
  Overriding1 Zip '[ '[ZipList] ]
```

## Adding a class

A companion package introduces a new class _Cls_ for synthesis by
writing a `DeriveStock Cls` instance.

The `-fplugin Stock` plugin discovers it: looks up the instance, loads
the deriver with GHC's own plugin loader, and runs it for `deriving
Cls via Stock T`.

```haskell
instance DeriveStock Semigroup where 
  deriveStock :: Deriver
  deriveStock = Deriver \cls datatype -> do
    let (<+>) = head (classMethods cls)
    a <- fresh (dtVia datatype) "a"
    b <- fresh (dtVia datatype) "b"
    body <- fromProduct datatype (dtVia datatype) (Var a) \xs ->    -- (match)  a = C x..
            fromProduct datatype (dtVia datatype) (Var b) \ys ->    -- (match)  b = C y..
            toProduct datatype <$> czipFields cls                   -- (build)  C (x <> y)..
              (\ft d x y -> mkApps (Var (<+>)) [Type ft, d, x, y]) (productCon datatype) xs ys
    EvExpr <$> classDictWith cls (dtVia datatype) [] [(0, mkLams [a, b] body)]
```

The deriver must live in a different module from where it's used.  The
plugin loads it as *compiled* code, same-module instances won't
work. A normal dependency (separate package, or just a separate module
built with `-dynamic-too`) works.

## Performance

`cabal bench bench` runs identical workloads against a type defined three ways:
`via Stock`, GHC's stock `deriving`, and hand-written. All three give matching
checksums and run within noise of each other — verified by rebuilding and
re-running on GHC 9.8 – 9.14:

```
Ord: sort 100000 3-field records      via Stock 0.075s  stock 0.074s  hand 0.073s
Functor: fmap (+1) x50 over 100000    via Stock 0.136s  stock 0.136s  hand 0.137s
```

## Conclusions / realizations

Every claim here is machine-checked with _inspection-testing_ (it
compares optimised Core, not behaviour):

+ `Eq`, `Ord`, `Enum`, `Functor`, `Bounded`, `Foldable` optimise to
  Core *byte-identical* to GHC's own `deriving` on a twin type.
+ `Traversable` / `Bitraversable` — which GHC can't stock-derive at all
  — produce a `traverse` / `bitraverse` byte-identical to the natural
  hand-written definition.
+ every other class provably erases the `Stock` wrapper and its
  coercions completely (so it is exactly as fast as hand-written).

In short: where GHC derives the class, you get the same Core GHC emits;
where it doesn't, you get the Core you would have written by hand.

`Read` (and `Read1`) build `readPrec` exactly as GHC's derived `Read`
does — the same `ReadPrec` combinators — and let `readsPrec` come from
the class default, so the result is byte-faithful *including* the order
of ambiguous infix parses. A parity harness (`test/Twin.hs`) checks the
full `readsPrec` output against GHC's own derived `Read` on a
name-identical twin, over valid / whitespace / parenthesised / negative
/ garbage inputs at several precedences.

## Acknowledgments

Developed with substantial assistance from Claude (Anthropic).

## License

BSD-3-Clause.
