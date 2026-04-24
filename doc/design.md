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

```rust
impl<A, B> Conn<A, B> {
    pub fn then<C>(self, other: Conn<B, C>) -> Conn<A, C> {
        Conn {
            ceil:  |a| (other.ceil)((self.ceil)(a)),
            inner: |c| (self.inner)((other.inner)(c)),
            floor: |a| (other.floor)((self.floor)(a)),
        }
    }
}
```

Ceiling and floor compose covariantly; the inner adjoint composes
contravariantly (in the opposite direction). This matches the Haskell
`Category` instance.

The result of composing a one-sided connection with a two-sided connection is
a one-sided connection — because if `self.ceil == self.floor`, then the
composed `ceil` and `floor` are also equal.

### `.then()` vs. `compose_conn!`

The `.then()` method above is the aspirational API; `Conn<A, B>`
currently stores three bare `fn(_) -> _` pointers (not closures), so a
generic `.then()` would need to capture both inputs and can't —
a bare `fn` has no captures. Until a closure-capturing
[`DynConn`](#runtime-composition-future) lands, compile-time
composition uses the [`compose_conn!`] declarative macro, which takes
two `const Conn`s and expands to a fresh `const Conn` whose
`ceil`/`inner`/`floor` fn-items invoke the inputs by name:

```rust
compose_conn! {
    pub const F12F00_VIA_MICRO: Conn<Pico, Uni> = F12F06, F06F00;
}
```

The intermediate type (`Micro` here) is inferred and never appears
in the emitted source. This covers the compile-time-known case that
accounts for ~95 % of real usage; runtime composition remains
deferred.

### Combinators

The Haskell library defines several ways to lift connections into product,
coproduct, and functor structures. The following translate directly:

| Haskell      | Rust         | Description                              |
|--------------|--------------|------------------------------------------|
| `>>>`        | `.then()`    | Sequential composition                   |
| `strong`     | `product`    | Lift into product order `(A, C) → (B, D)`|
| `choice`     | `coproduct`  | Lift into `Result<A, C> → Result<B, D>`  |
| `identity`   | `Conn::id()` | Identity connection                      |
| `bounded`    | `Conn::bounded()` | Bounded type → unit                 |
| `ordered`    | `Conn::ordered()` | `(A, A) → A` via min/max            |
| `mapped`     | *(omitted)*  | Requires HKT; specialize per container   |

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
    Finite(T),  // the float value (including NaN, ±∞)
    Top,        // synthetic top, above +∞
}
```

With `PartialOrd` defined as:

- `Bot ≤ x` and `x ≤ Top` for all `x` (by construction)
- `Finite(a).partial_cmp(Finite(b))` delegates to `T::partial_cmp`
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

### Why not a custom `Preorder` trait?

The Haskell library defines a `Preorder` class to work around the broken
`Ord` instance for floats. Rust's `PartialOrd` already captures partial
orders correctly — the problem is only NaN self-incomparability, which is
localized to the `ExtendedFloat` impl. Introducing a separate `Preorder` trait
would duplicate the ecosystem's `PartialOrd` for no additional expressiveness.

### Connections involving floats

Connections between float types are typed over `ExtendedFloat`:

- `f64_f32: Conn<ExtendedFloat<f64>, ExtendedFloat<f32>>` — not `Conn<f64, f32>`

The `inner` function embeds `ExtendedFloat<f32>` into `ExtendedFloat<f64>` preserving
`Bot`/`Top`/`NaN`/finite structure. The `ceil` and `floor` functions convert
in the other direction with appropriate rounding.

> **Status (2026-04-23):** This shape is aspirational — the current
> `f64_f32()` function in `src/conn/float.rs` still returns
> `Conn<f64, f32>` over bare floats and ULP-walks under the N5
> preorder from `lattice::Ple`. Switching to `ExtendedFloat`-typed
> connections is its own sprint; `ExtendedFloat` lives alongside
> the bare-float connections in `src/conn/float.rs` waiting to be
> used.

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
├── lattice.rs          — Ple trait (N5 preorder) + Join/Meet/Heyting/Coheyting/Symmetric/Boolean stubs
├── property.rs         — shared proptest strategies and property helpers (Sprint C)
└── conn/
    ├── int.rs          — integer ↔ integer connections (stub)
    ├── word.rs         — word ↔ word connections (stub)
    ├── float.rs        — ExtendedFloat type + PartialOrd impl + float ↔ float connections
    ├── fixed.rs        — decimal fixed-point ladder (Uni..Pico) with tier-pair connections
    └── sample.rs       — rate-typed sample-indexed time; rate ↔ rate and rate ↔ pico connections
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
