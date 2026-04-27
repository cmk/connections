# Design

This document describes the design of `connections`, a Rust library encoding
[Galois connections](https://ncatlab.org/nlab/show/Galois+connection) as
first-class values. It is a port of the Haskell library of the same name.

## Mathematical background

A **Galois connection** between two preordered sets `(A, ≤)` and `(B, ≤)` is a
pair of monotone functions `f: A → B` and `g: B → A` satisfying:

    f(a) ≤ b  ⟺  a ≤ g(b)

We write `f ⊣ g` and call `f` the **lower adjoint** (ceiling) and `g` the
**upper adjoint**. This is an adjunction in the category of preorders.

An **adjoint triple** is a chain `f ⊣ g ⊣ h` where `g` serves as the upper
adjoint of `f` and the lower adjoint of `h`. From an adjoint triple we can
extract two Galois connections — `(f, g)` and `(g, h)` — that share a middle
function.

Adjoint triples arise naturally in numerical conversion: given a lossy
embedding `g: B → A` (e.g. `f32 → f64`), the ceiling `f: A → B` rounds up
and the floor `h: A → B` rounds down. Functions like `round` and `truncate`
require access to both `f` and `h`, which is why the triple is the right
primitive.

### Key properties

Every Galois connection `f ⊣ g` satisfies:

- **Adjointness**: `f(a) ≤ b ⟺ a ≤ g(b)`
- **Closure**: `a ≤ g(f(a))` (unit)
- **Kernel**: `f(g(b)) ≤ b` (counit)
- **Monotonicity**: `f` and `g` are monotone
- **Idempotence**: `g ∘ f` and `f ∘ g` are idempotent

These properties are the test suite contract. Every connection value must
satisfy all five.

### Triple-only properties and the role of injectivity

In an adjoint *triple* `f ⊣ g ⊣ h` (with `g` shared as the middle
adjoint), both `f` and `h` have type `A → B`, so it becomes meaningful
to compare them pointwise:

- **Rounding sandwich**: `h(a) ≤ f(a)` for all `a`.

This is *not* derivable from the adjoint axioms alone. From the two
halves of the triple you can derive the inner-image sandwich

```
g(h(a)) ≤ a ≤ g(f(a))
```

To strip the outer `g` and recover `h(a) ≤ f(a)`, you need `g` to
*reflect* the order — `g(x) ≤ g(y) ⟹ x ≤ y` — which, for a monotone
embedding into a totally ordered set, is the same as saying `g` is
injective (no plateaus where multiple `b`'s collapse to the same `a`).

So `floor ≤ ceil` is two things at once:

- **Structurally** triple-only: a plain adjoint pair `f ⊣ g` has no
  second function `A → B` to compare against, so the property has no
  statement.
- **Logically** an extra side condition on the triple, namely that
  `g` is injective.

For lossless-embedding connections (any `inner` that is an exact
bit-shift into a target with sufficient precision — e.g. the within-
ladder `FD12 → FD12` identity, or any cross-width `FixedI<W1><F1>` →
`FixedI<W2><F2>` where the Coarse value range is a strict subset of
Fine's), `inner` is injective and the rounding sandwich holds for
free. For *saturating* `inner` (e.g. distinct fixed-point types where
Coarse value range exceeds Fine's, forcing `inner(c) = Fine::MAX` for
a plateau of large `c`), `floor(a) ≤ ceil(a)` fails at the plateau —
multiple `c`'s map to the same `inner(c)`, so the smallest such `c`
(returned by `ceil`) and the largest (returned by `floor`) differ in
the wrong direction.

Property-test consequence: the test suite asserts the five Galois
axioms above for **every** connection. The rounding sandwich is
asserted only for connections where `inner` is documented-injective.
Per-connection module headers note which case they are in.

## Core type

The [Haskell library](https://github.com/cmk/connections/) uses a phantom
`Side` kind index on `Cast k a b` to present a single runtime representation
as either a left connection (`CastL`), a right connection (`CastR`), or 
in [certain cases](https://ncatlab.org/nlab/show/adjoint+string) a full 
triple (`Cast`). Rust lacks the type-level machinery to replicate this directly
(no data kinds, no pattern synonyms, no rank-2 polymorphism).

Instead, this library uses **one connection type that always carries the full
triple**:

```rust
pub struct Conn<A, B> {
    ceil: fn(A) -> B,   // f: lower adjoint (ceiling, rounds up)
    inner: fn(B) -> A,  // g: shared middle adjoint (embedding)
    floor: fn(A) -> B,  // h: upper adjoint (floor, rounds down)
}
```

When a connection is only one-sided (e.g. only `f ⊣ g` is known, with no
meaningful `h`), `floor` is set equal to `ceil`. This is the same internal
representation the Haskell library uses for `CastL` — both slots hold the
same function.

### Why one type

- **Composition is uniform.** Composing two `Conn` values composes all three
  components independently. If both inputs are full triples, the result is a
  full triple. If either is one-sided (floor == ceil), the result is naturally
  one-sided by the same mechanism. No type-level bookkeeping needed.

- **Functions that need the full triple** (`round`, `truncate`, `midpoint`,
  `interval`, `median`) accept `Conn<A, B>` directly — no rank-2 type
  required. When called on a one-sided connection, `round` degrades to
  `truncate`, which is semantically correct.

- **Simpler API surface.** One type, one set of combinators. Users don't need
  to understand `Side` to use the library.

### Trade-off

The Haskell version uses the `Side` index to prevent accessing `floor` on a
`CastL` at compile time. This library does not enforce that — calling `floor`
on a one-sided connection silently returns the same result as `ceil`. This is
safe (the result is a valid monotone function that satisfies the adjointness
law) but it does not distinguish "this connection supports rounding" from
"this connection only supports ceiling" at the type level. If this becomes a
source of confusion, a future version could introduce marker types.

## Composition

Composition is provided by the `compose!` macro. It expands a chain of
compile-time-known `Conn` consts into a single fresh
`Conn<Src, Dst>` whose `ceil` / `inner` / `floor` are nested calls
into the parent consts. The result is `Copy` and `const`-constructible
— same shape as a hand-written `Conn`.

```rust
const FD12FD00_BIS: Conn<FD12, FD00> =
    compose!(FD12FD09, FD09FD06, FD06FD03, FD03FD00);
```

Ceiling and floor compose covariantly (left-to-right); the inner
adjoint composes contravariantly (right-to-left). This matches the
Haskell `Category` instance. If every parent is one-sided
(`self.ceil == self.floor`), the composed `ceil` and `floor` are also
equal — the one-sided property is preserved.

### Why not a runtime `Conn::then`?

`Conn`'s fields are bare `fn` pointers:

```rust
pub struct Conn<A, B> {
    pub(crate) ceil:  fn(A) -> B,
    pub(crate) inner: fn(B) -> A,
    pub(crate) floor: fn(A) -> B,
}
```

A `fn` pointer is a single code address — there is no slot to stash
captured state. A runtime `then` method would have to construct
something like `|a| other.ceil(self.ceil(a))`, which captures `self`
and `other`. That's a closure with state, not a `fn` pointer; it can't
be stored in a `Conn` field as defined.

Two viable shape changes exist if a future consumer needs runtime
composition:

1. **Generic type parameters with `fn`-pointer defaults:**
   `pub struct Conn<A, B, F = fn(A) -> B, G = fn(B) -> A, H = fn(A) -> B>`.
   Existing call sites stay source-compatible; `then` returns a
   `Conn<A, C, impl Fn ..., impl Fn ..., impl Fn ...>` — a different
   concrete type from the fn-pointer instantiation, but one that still
   satisfies the same accessor surface. Preserves `Copy` (closures
   capturing only `Copy` data are themselves `Copy`).
2. **Boxed trait objects:** `ceil: Box<dyn Fn(A) -> B>`. Loses `Copy`
   and `const`; adds heap allocation per `then`.

Both add real complexity that the macro avoids. The macro is preferred
because the parents being composed are virtually always module-scope
`const`s (the `F??F??` ladder, `S???S???` rate pairs, `F12S??`
cross-tier conns), so the composition is fully known at compile time
and pays no runtime cost.

### Combinators

The Haskell library defines several ways to lift connections into product,
coproduct, and functor structures. The following translate directly:

| Haskell      | Rust                  | Status                                |
|--------------|-----------------------|---------------------------------------|
| `>>>`        | `compose!(F, G, …)`   | **Implemented** — code-gen macro      |
| `>>>`        | `Conn::then`          | *Deferred* — see "Why not …" above    |
| `strong`     | `product`             | *Deferred* — same shape constraint    |
| `choice`     | `coproduct`           | *Deferred* — same shape constraint    |
| `identity`   | `Conn::identity()`    | Implemented                           |
| `bounded`    | `Conn::bounded()`     | Future                                |
| `ordered`    | `Conn::ordered()`     | Future                                |
| `mapped`     | *(omitted)*           | Requires HKT; specialize per container |

## Float lattice: `ExtendedFloat<T>`

IEEE 754 floats under Rust's `PartialOrd` form a partial order where NaN is
incomparable with all values including itself. This is almost the right
structure for Galois connections, but it lacks a top and bottom element, and
NaN's self-incomparability (`NaN ≤ NaN` is false) breaks reflexivity.

The Haskell library addresses this with an
[N5 lattice](https://en.wikipedia.org/wiki/Modular_lattice#Examples)
ordering where NaN sits between ±∞:

```
     +∞
    / \
  NaN  finites
    \ /
     -∞
```

Rather than fighting Rust's float `PartialOrd`, this library introduces
`ExtendedFloat<T>` — an extension that adds synthetic top and bottom elements
outside the float range:

```rust
pub enum ExtendedFloat<T> {
    Bot,        // synthetic bottom, below -∞
    Extend(T),  // the float value (including NaN, ±∞)
    Top,        // synthetic top, above +∞
}
```

The wrapped variant is named `Extend` rather than `Finite` because
the wrapped value can be `NaN` or `±∞`, neither of which is finite.
The variant name reflects the lattice-theoretic role (the *extension*
slot between `Bot` and `Top`) instead of a numeric property of the
inhabitant. Sister type `Extended<T>` keeps `Finite` since its
wrapped values really are finite.

With `PartialOrd` defined as:

- `Bot ≤ x` and `x ≤ Top` for all `x` (by construction)
- `Extend(a).partial_cmp(Extend(b))` delegates to `T::partial_cmp`
  **except** when both values are NaN, where it returns `Some(Equal)`

This recovers the N5 lattice shape:

```
        Top
       / | \
    +∞  NaN  finites
    |        
  finites    
    |        
    -∞  NaN
       \ | /
        Bot
```

The key properties:

- **Bounded**: `Bot` is bottom, `Top` is top
- **NaN is comparable** to `Bot` and `Top` (via the synthetic bounds)
- **NaN is incomparable** with all finite values and ±∞ (via float `PartialOrd`)
- **NaN is reflexive**: `NaN ≤ NaN` (patched in the `PartialOrd` impl)
- **No wrapper on bare floats**: `ExtendedFloat` is only used at the boundary
  of connections involving floats; internal arithmetic uses bare `f32`/`f64`

### Why `Eq + PartialOrd` suffices

Rust's standard library separates `PartialEq` (a *partial* equivalence
relation: symmetric + transitive, **reflexivity not required**) from
`Eq: PartialEq` (a marker trait whose only requirement is that the
underlying `PartialEq` is reflexive). `PartialOrd`'s contract is to
be consistent with `PartialEq`. Once a type satisfies `Eq` (i.e. its
`PartialEq` is reflexive), its `PartialOrd` encodes a genuine partial
order in the mathematical sense — reflexive, transitive, antisymmetric
on the comparable subset.

The IEEE-float "broken" comparison story sits at the `PartialEq`
level, not `PartialOrd`: raw `f64::PartialEq` says `NaN ≠ NaN`, which
prevents `f64` from impl'ing `Eq`, which is exactly why raw floats
cannot be used as Conn endpoints. The fix lives at the wrapper
boundary: `ExtendedFloat<T>` patches `PartialEq` so `Extend(NaN) ==
Extend(NaN)` (synthetic `Bot` / `Top` are also reflexive), and
therefore impls `Eq`. `ExtendedFloat<f32>` / `ExtendedFloat<f64>` are
genuine partial orders and flow through every law predicate that
demands `T: Eq + PartialOrd`.

The Haskell upstream `connections` library defines its own `Preorder`
class because Haskell `base` has no partial-order class. Rust does —
the lawful framework here is just `Eq + PartialOrd`, with no
crate-local trait surface for ordering.

### Connections involving floats

Connections between float types are typed over `ExtendedFloat`:

- `F064F032: Conn<ExtendedFloat<f64>, ExtendedFloat<f32>>` — not `Conn<f64, f32>`

The `inner` function embeds `ExtendedFloat<f32>` into `ExtendedFloat<f64>` preserving
`Bot`/`Top`/`NaN`/finite structure. The `ceil` and `floor` functions convert
in the other direction with appropriate rounding. Both endpoints satisfy
`Eq + PartialOrd` and flow through the law machinery directly.

Connections between integer types do not need `ExtendedFloat` — integer `Ord` is
total and well-behaved. The `Extended<T>` enum (with `NegInf`, `Finite(T)`,
`PosInf`) from the Haskell library is only needed for connections where the
target type cannot represent the full range of the source (e.g. `f32 →
Extended<u8>`). This is a separate type from `ExtendedFloat`.

## Float conversion performance

The Haskell library's `f64f32`, `ratf32`, and `ratf64` connections use a
linear ULP-walk to find the correct floor/ceiling: get an initial estimate
via `double2Float` or `fromRational`, then step one ULP at a time until the
adjointness condition holds.

This is correct but unnecessarily general. IEEE 754 `round-to-nearest-even`
guarantees the initial estimate is within a small, statically knowable
number of ULPs from the true floor/ceiling. The exact bound depends on the
precision relationship between source and target types and is at most a
few steps.

The Rust port should replace the `until` loop with a bounded adjustment:

1. Get the round-to-nearest estimate (`x as f32`, or equivalent)
2. Check which side of the target it landed on
3. Apply a bounded number of `shift` steps (ULP increments/decrements)

The library already requires the bit-level machinery for `shift` and `ulp`
(`f32::to_bits`, `f32::from_bits`, sign-magnitude ↔ two's-complement
conversion), so the O(1) version uses the same primitives as the loop.

Determining the exact ULP bounds for each connection pair is deferred to
implementation. The test suite's adjointness properties will verify
correctness regardless of the implementation strategy.

## Module structure

```
src/
├── lib.rs              — crate-level API docs, module declarations
├── conn.rs             — Conn type, composition, combinators + `conn::*` submodule decls
├── extended.rs         — Extended<T> type for integer range extension
├── lattice.rs          — Join/Meet/Heyting/Coheyting/Symmetric/Boolean lattice traits
├── property.rs         — shared proptest strategies and property helpers (Sprint C)
└── conn/
    ├── int.rs          — integer ↔ integer connections (stub)
    ├── word.rs         — word ↔ word connections (stub)
    ├── float.rs        — ExtendedFloat type + PartialOrd impl + float ↔ float connections
    ├── fixed.rs        — decimal fixed-point ladder (FD00..FD12) with tier-pair connections
    └── sample.rs       — rate-typed sample-indexed time; rate ↔ rate and rate ↔ FD12 connections
```

Why no `float_ext.rs` at the crate root: the `ExtendedFloat` wrapper
is only useful *in combination with* the float connections, so
keeping its definition alongside those connections in
`src/conn/float.rs` keeps related code together.

## Lattice hierarchy

The Haskell library's `Side`-indexed `Semilattice k a` and `Algebra k a`
become separate traits in Rust:

```rust
trait Join: PartialOrd {
    fn bot() -> Self;
    fn join(&self, other: &Self) -> Self;
}

trait Meet: PartialOrd {
    fn top() -> Self;
    fn meet(&self, other: &Self) -> Self;
}

trait Heyting: Join + Meet {
    fn imp(&self, other: &Self) -> Self;   // Heyting implication
}

trait Coheyting: Join + Meet {
    fn sub(&self, other: &Self) -> Self;   // co-Heyting subtraction
}

trait Symmetric: Heyting + Coheyting {
    fn not(&self) -> Self;
}

trait Boolean: Symmetric {}
```

This is arguably clearer than the Haskell version — the `Side` index is
elegant but requires understanding data kinds to read. Separate traits are
idiomatic Rust and self-documenting.

The lattice traits are defined in terms of connections where possible
(e.g. `join` is the ceiling of the semilattice connection
`Conn<(A, A), A>`), preserving the Haskell library's insight that lattice
operations derive from adjunction structure.

## Testing

Property-based tests using `proptest`, mirroring the Haskell library's
Hedgehog suite. Every connection must satisfy:

| Property       | Statement                               |
|----------------|-----------------------------------------|
| `adjoint`      | `ceil(a) ≤ b ⟺ a ≤ inner(b)`          |
| `closure`      | `a ≤ inner(ceil(a))`                    |
| `kernel`       | `ceil(inner(b)) ≤ b`                    |
| `monotone_ceil`| `a₁ ≤ a₂ ⟹ ceil(a₁) ≤ ceil(a₂)`       |
| `monotone_inner`| `b₁ ≤ b₂ ⟹ inner(b₁) ≤ inner(b₂)`   |
| `idempotent`   | `inner(ceil(inner(ceil(a)))) = inner(ceil(a))` |

Float generators must include NaN, ±∞, ±0, denormals, and max/min
finite values with elevated frequency.

## Cast: L/R as a naming axis, not a type axis

The Haskell library exposes operations on a connection through two
mirror APIs: `ceiling`/`upper`/`upper1`/`upper2`/`maximize` (L-side,
takes `Cast 'L a b`) and `floor`/`lower`/`lower1`/`lower2`/`minimize`
(R-side, takes `Cast 'R a b`). The phantom `Side` index `'L` / `'R`
prevents accessing the wrong arm at compile time even though both
sides of a connection share one runtime representation.

This port collapses both sides onto the unified
[`Conn<A, B>`](crate::conn::Conn). Because `Conn` carries the full
adjoint triple (`ceil ⊣ inner ⊣ floor`) in three `fn` pointers, the
L-side and R-side accessors and lifters can both be defined as free
functions over the same value, distinguished only by *name* and
*documented contract*. They live alongside each other in
[`crate::conn::cast`].

The asymmetry between the two sides in the Haskell library is also
worth noting: an audit of `Data.Connection.{Class,Int,Word,Float,
Fixed,Time,Ratio}` finds 122 `Cast 'L`-only concrete connections and
**zero** `Cast 'R`-only connections — every named connection that
isn't polymorphic over `k` is an L-pair. There is no use case in the
upstream library for an R-only constructor, so this port deliberately
does not expose one. Constructors are: [`Conn::new`](crate::conn::
Conn::new) (full triple) and [`Conn::new_left`](crate::conn::Conn::
new_left) (length-2; sets `floor = ceil`).

Two consequences of this design:

- **No `swapL` / `swapR`.** In the Haskell library these convert
  between `Cast 'L a b` and `Cast 'R b a`. In this representation
  there is nothing to convert: the same `Conn` already exposes both
  names.
- **Two-sided helpers (`round`, `truncate`, `midpoint`, `interval`,
  `median`) need no rank-2 polymorphism.** The Haskell signature
  `forall k. Cast k a b` was a workaround for not having both `f` and
  `h` in a single value; here every `Conn` already has both, so the
  helpers (Sprint B) take `&Conn<A, B>` directly.
