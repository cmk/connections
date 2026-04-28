# connections

[![CI](https://gitlab.com/cmk/connections/badges/main/pipeline.svg)](https://gitlab.com/cmk/connections/-/pipelines)

Galois connections as first-class Rust values. Use them to cast lawfully
between numeric types, expose ceiling/floor/inner alongside each other on
the same value, and compose ladders of conversions whose round-trip
behavior is property-tested rather than left to chance.

**MSRV: Rust 1.85.** Bumps to the MSRV will be treated as minor-version
changes — pin `connections = "0.1"` and an MSRV upgrade will surface as
a 0.2 release rather than a silent break on a patch update.

## What are Galois connections?

A [Galois connection](https://en.wikipedia.org/wiki/Galois_connection)
between preorders P and Q is a pair of monotone maps `f: P → Q` and
`g: Q → P` such that `f(x) ≤ y ⇔ x ≤ g(y)`. We say `f` is the *left*
or *lower* adjoint, and `g` is the *right* or *upper* adjoint of the
connection.

Drawn between two 3-element chains
(adapted from [7 Sketches](https://math.mit.edu/~dspivak/teaching/sp18/7Sketches.pdf)):

```text
P  ←  Q
   g

3  ↔  3


2  ←  2
   ↰
   ↳
1  →  1

   f
P  →  Q
```

Each row is a `(p, q)` pair; arrows show the action of `f` (P → Q,
bottom legend) and `g` (Q → P, top legend). Lone arrows mark
single-direction maps (`f(1) = 1`, `g(2) = 2`); the `↔` marks a
matched pair where both adjoints agree (`f(3) = 3`, `g(3) = 3`); the
adjacent `↰ ↳` glyphs depict the *lens* `f(2) ↔ g(1)` — two
non-crossing curves between rows 2 and 1, the geometric signature of
adjointness.

Connections are useful for **lawful conversions** between types: every
operation derived from a `Conn` (rounding, saturation, midpoint,
median, ...) carries a property-tested invariant, so round-trips
behave the way the math says.

## How connections work

Let's build the simplest possible connection in Rust — between
[`Ordering`](https://doc.rust-lang.org/core/cmp/enum.Ordering.html)
and `bool` — three different ways, each illustrating one more piece
of the structure that the unified `Conn<A, B>` type carries.

### Example 1: a one-sided connection

```rust
use connections::conn::Conn;
use std::cmp::Ordering;

fn ceil(o: Ordering) -> bool {
    !matches!(o, Ordering::Less)
}
fn inner(b: bool) -> Ordering {
    if b { Ordering::Greater } else { Ordering::Less }
}
const ORDBIN: Conn<Ordering, bool> = Conn::new_left(ceil, inner);

assert_eq!(ORDBIN.ceil(Ordering::Less),    false);
assert_eq!(ORDBIN.ceil(Ordering::Greater), true);
assert_eq!(ORDBIN.inner(false),            Ordering::Less);
assert_eq!(ORDBIN.inner(true),             Ordering::Greater);
```

Each function is monotone (`x₁ ≤ x₂ ⇒ f(x₁) ≤ f(x₂)`) and the pair is
*adjoint*: for every input we have `ceil(x) ≤ y ⇔ x ≤ inner(y)`. We
can verify this by hand. Each cell shows the relation between
`ceil(x)` and `y` (left of the slash) and between `x` and `inner(y)`
(right of the slash). The two relations always agree on whether `≤`
holds:

| ceil/inner   | `false` | `true`  |
|--------------|---------|---------|
| `Less`       | `=`/`=` | `<`/`<` |
| `Equal`      | `>`/`>` | `=`/`<` |
| `Greater`    | `>`/`>` | `=`/`=` |

A cell with `=`/`>` or `>`/`=` (or arrows facing in opposite
directions) would be a counterexample to adjointness. There are none.

### Example 2: the same `inner`, flipped

Notice that `inner` from Example 1 — the `bool → Ordering` function —
is itself *also* the lower adjoint of a different pair. Define a new
upper adjoint `h` going the other way:

```rust
use connections::conn::Conn;
use std::cmp::Ordering;

fn ceil(b: bool) -> Ordering {
    if b { Ordering::Greater } else { Ordering::Less }
}
fn inner(o: Ordering) -> bool {
    matches!(o, Ordering::Greater)
}
const BINORD: Conn<bool, Ordering> = Conn::new_left(ceil, inner);

assert_eq!(BINORD.ceil(false),              Ordering::Less);
assert_eq!(BINORD.ceil(true),               Ordering::Greater);
assert_eq!(BINORD.inner(Ordering::Less),    false);
assert_eq!(BINORD.inner(Ordering::Equal),   false);
assert_eq!(BINORD.inner(Ordering::Greater), true);
```

The verification table is consistent again:

| ceil/inner | `Less`  | `Equal` | `Greater` |
|------------|---------|---------|-----------|
| `false`    | `=`/`=` | `<`/`=` | `<`/`<`   |
| `true`     | `>`/`>` | `>`/`>` | `=`/`=`   |

The same function (`bool → Ordering`) plays two roles: the *upper*
adjoint of Example 1's pair, and the *lower* adjoint of Example 2's
pair. Together with Example 1's `ceil` and Example 2's `inner`, the
three functions form an *adjoint string of length 3*: `f ⊣ g ⊣ h`.
The two adjoint pairs (`f`/`g` and `g`/`h`) give *two routes* back
from `Ordering` to `bool` — and that two-route choice is exactly what
enables lawful `ceiling`, `floor`, `round`, and `truncate` on
arbitrary `Conn`s.

### Example 3: the full triple

A small change to Example 1 — supplying both the upper and lower
adjoints on the L side — packs the whole chain into a single value:

```rust
use connections::conn::Conn;
use std::cmp::Ordering;

fn ceil(o: Ordering) -> bool {
    !matches!(o, Ordering::Less)
}
fn inner(b: bool) -> Ordering {
    if b { Ordering::Greater } else { Ordering::Less }
}
fn floor(o: Ordering) -> bool {
    matches!(o, Ordering::Greater)
}
const ORDBIN: Conn<Ordering, bool> = Conn::new(ceil, inner, floor);

// `ceil` reads the L-pair (ceil ⊣ inner); `floor` reads the R-pair
// (inner ⊣ floor). They differ on `Equal`, where the bracket is open:
assert_eq!(ORDBIN.ceil(Ordering::Equal),  true);
assert_eq!(ORDBIN.floor(Ordering::Equal), false);
```

Each cell is now a triple: `ceil(x) ⋈ y` / `x ⋈ inner(y)` /
`floor(x) ⋈ y`. Columns 1–2 verify the `f ⊣ g` pair; columns 2–3
verify the `g ⊣ h` pair (with the appropriate reversal):

| ceil/inner/floor | `false`     | `true`      |
|------------------|-------------|-------------|
| `Less`           | `=`/`=`/`=` | `<`/`<`/`<` |
| `Equal`          | `>`/`>`/`=` | `=`/`<`/`<` |
| `Greater`        | `>`/`>`/`>` | `=`/`=`/`=` |

This is the shape `Conn<A, B>` carries: three function pointers in
one value. The crate-root `ceiling` / `floor` / `upper` / `lower` free
functions select which adjoint pair you read off per call.

The two-sided combinators (`round`, `truncate`, `midpoint`,
`interval`, `median`) are defined on every `Conn<A, B>` — not just
full triples. On a one-sided connection (Examples 1 and 2,
constructed via `Conn::new_left`) they still type-check and run; they
just don't return anything interesting because the bracket between
`floor` and `ceil` collapses to a single point. `interval` returns
`Some(Ordering::Equal)`, `round` and `truncate` both pick that point,
and `midpoint` lands on it too. The API surface is uniform — you
don't track 'one-sided vs two-sided' at the type level; a one-sided
conn passed into a function expecting `round` behavior just
degenerates gracefully into the trivial case.

For the structural mirror to the Haskell library's `Cast 'L` / `Cast 'R`
data-kind split, see [Relationship to the Haskell `connections`
library](#relationship-to-the-haskell-connections-library) below.

## Why this crate

The standard cast operators `as`, `From`, and `Into` give you exactly one
direction at a time — and `as` in particular is silent on rounding,
saturation, and lossy conversion. Three concrete things this crate gives
you that the standard tools don't:

1. **Both arms of a cast on one value.** A `Conn<A, B>` exposes
   `ceil: A → B`, `floor: A → B`, *and* the embedding `inner: B → A` as
   three function pointers on one value. You don't pick "ceiling cast" vs
   "floor cast" up front — you carry both and call whichever you need
   per-call.

2. **Round-trip identities that hold.** `(x as f32) as f64 != x` for many
   `x: f64`. With a `Conn`, the closure law `a ≤ inner(ceil(a))` and
   kernel law `ceil(inner(b)) ≤ b` are property-tested for *every*
   shipped connection. If you compose two connections with `compose!`,
   the result is property-tested too.

3. **Conversions composed by `compose!` are property-tested too.**
   The `compose!` macro folds a chain of pairwise Conns into one
   fresh `Conn<Src, Dst>` at compile time — type-flow comes from
   the binding annotation, intermediates are inferred. Domain-
   specific ladders (decimal time rungs, audio sample rates) live
   in downstream crates; this crate ships the algebra.

## Installation

```sh
cargo add connections
```

| | |
|--|--|
| **MSRV** | Rust 1.85 (matches `rust-toolchain.toml`) |
| **Edition** | 2024 |
| **License** | MIT (see [`LICENSE-MIT`](LICENSE-MIT)) |

Optional cargo features:

| Feature | What it enables | Toolchain |
|---------|-----------------|-----------|
| `testing` | Re-exports `connections::prop::arb` (proptest strategies) for downstream test suites | stable |
| `f16` | IEEE binary16 connections (`F016`, `F032F016`, `F064F016`) and their proptest strategies | nightly (uses `#![feature(f16)]` — tracking [#116909](https://github.com/rust-lang/rust/issues/116909)) |

The `connections::prop::conn` and `connections::prop::lattice`
predicate modules are *always* public — they're pure `bool`-returning
functions over this crate's own types and don't depend on `proptest`.
The `testing` feature only adds `prop::arb`, the strategy module that
does pull `proptest` in as a regular dependency.

## The core type

```rust,no_run
pub struct Conn<A, B> {
    ceil:  fn(A) -> B,   // lower adjoint (rounds up)
    inner: fn(B) -> A,   // shared middle adjoint (embedding)
    floor: fn(A) -> B,   // upper adjoint (rounds down)
}
```

A `Conn<A, B>` is an [adjoint
triple](https://ncatlab.org/nlab/show/adjoint+triple) `ceil ⊣ inner ⊣
floor` between two preordered sets — exactly the `f ⊣ g ⊣ h` chain
that Example 3 above derived. A length-2 (one-sided) connection sets
`floor = ceil`. The struct is `Copy`, `const`-constructible,
heap-free, and the crate is `#![forbid(unsafe_code)]`.

For the math and the rationale behind a single unified `Conn` type
(rather than a Haskell-style `Cast 'L` / `Cast 'R` split), see
[`doc/design.md`](doc/design.md).

## Quick tour

Integer widening through `Extended<T>` (so values *outside* the source
range have somewhere to land — `floor` saturates to the target bounds,
`ceil` lands on a synthetic point one past the source range):

```rust
use connections::int::i16::U008I016;
use connections::extended::Extended;

// Finite passes through.
assert_eq!(U008I016.ceil(Extended::Finite(200_u8)), 200_i16);

// `floor` saturates the infinities to target bounds.
assert_eq!(U008I016.floor(Extended::PosInf), i16::MAX);
assert_eq!(U008I016.ceil(Extended::NegInf),  i16::MIN);

// `ceil(PosInf)` and `floor(NegInf)` land on the "one past source"
// markers — distinct from the target bounds, so `inner` can recover
// PosInf/NegInf round-trip.
assert_eq!(U008I016.ceil(Extended::PosInf),  256_i16);   // u8::MAX + 1
assert_eq!(U008I016.floor(Extended::NegInf), -1_i16);    // u8::MIN - 1
```

`Cast` API — accessors and lifters operating on any `Conn`:

```rust
use connections::{ceiling, upper1};
use connections::int::i16::U008I016;
use connections::extended::Extended;

// `ceiling` is the named alias of `c.ceil` under the L-side reading.
assert_eq!(
    ceiling(&U008I016, Extended::Finite(200_u8)),
    U008I016.ceil(Extended::Finite(200_u8)),
);

// `upper1` lifts an endofunction over the target type back to the source:
//   upper1(c, f, a) = inner(f(ceil(a)))
let bumped = upper1(&U008I016, |n| n, Extended::Finite(200_u8));
assert_eq!(
    bumped,
    U008I016.inner(U008I016.ceil(Extended::Finite(200_u8))),
);
```

A sub-second `Duration` bracketed via the `time`-crate ladder (the same
code block is mirrored verbatim into the `time` module-level
rustdoc, so `cargo test --doc` keeps the two in sync):

```rust
use connections::time::DURNSECS;
use connections::extended::Extended;
use time::Duration;

let half = Duration::seconds(5) + Duration::nanoseconds(1);
assert_eq!(DURNSECS.ceil(half),  Extended::Finite(6));
assert_eq!(DURNSECS.floor(half), Extended::Finite(5));
assert_eq!(DURNSECS.inner(Extended::Finite(42)), Duration::seconds(42));
```

Round-tripping a unix-timestamp through `OffsetDateTime`:

```rust
use connections::time::OFDTNANO;
use connections::extended::Extended;
use time::OffsetDateTime;

assert_eq!(OFDTNANO.inner(0), Extended::Finite(OffsetDateTime::UNIX_EPOCH));
assert_eq!(OFDTNANO.ceil(Extended::Finite(OffsetDateTime::UNIX_EPOCH)), 0);
```

Bracketing an IEEE-float number of seconds with `Duration`:

```rust
use connections::float::ExtendedFloat;
use connections::time::F064DURN;
use connections::extended::Extended;
use time::Duration;

let half_sec = ExtendedFloat::Extend(0.5_f64);
assert_eq!(F064DURN.ceil(half_sec),  Extended::Finite(Duration::milliseconds(500)));
assert_eq!(F064DURN.floor(half_sec), Extended::Finite(Duration::milliseconds(500)));

// f64 NaN: ceil → +∞, floor → -∞ (forced by `Top > Extend(NaN) > Bot`).
let nan = ExtendedFloat::Extend(f64::NAN);
assert_eq!(F064DURN.ceil(nan),  Extended::PosInf);
assert_eq!(F064DURN.floor(nan), Extended::NegInf);
```

A direct `f64 → f16` narrowing — wrapped with `ExtendedFloat` so it
satisfies `Eq + PartialOrd` and flows through the law machinery.
**Requires the `f16` cargo feature** (and a nightly toolchain, since
`f16` is currently a nightly-only primitive — tracking
[#116909](https://github.com/rust-lang/rust/issues/116909)). Default
stable builds skip the f16 path entirely:

```rust,ignore
// Build with `--features f16` on nightly to enable F064F016.
use connections::float::f16::F064F016;
use connections::float::ExtendedFloat::Extend;

// π narrows to f16. The two-sided round-trip brackets π.
let pi = Extend(std::f64::consts::PI);
let pi_up   = F064F016.ceil(pi);
let pi_down = F064F016.floor(pi);
assert!(F064F016.inner(pi_down) <= pi);
assert!(pi <= F064F016.inner(pi_up));

// f64::MAX saturates to f16::INFINITY.
let huge = Extend(f64::MAX);
assert_eq!(F064F016.ceil(huge), Extend(f16::INFINITY));
```

The set of float-narrowing Conns ships as three named constants:

| Constant | Source | Target | Module | Feature |
|----------|--------|--------|--------|---------|
| `F064F032` | `ExtendedFloat<f64>` | `ExtendedFloat<f32>` | [`float::f32`] | always |
| `F064F016` | `ExtendedFloat<f64>` | `ExtendedFloat<f16>` | `float::f16` | `f16` |
| `F032F016` | `ExtendedFloat<f32>` | `ExtendedFloat<f16>` | `float::f16` | `f16` |

Each goes f64/f32 → narrower with RNE rounding, walks ≤ 2 ULPs on the
target side to find the exact ceiling/floor, and saturates extreme
magnitudes to ±∞.

## What's lawful

Every connection ships with proptest coverage of the following laws — the
predicates live in `prop::conn` and are re-runnable by downstream
crates against their own connections:

| Law | Statement |
|-----|-----------|
| `conn_galois_l` | `ceil(a) ≤ b ⟺ a ≤ inner(b)` |
| `conn_galois_r` | `inner(b) ≤ a ⟺ b ≤ floor(a)` |
| `conn_closure_l` | `a ≤ inner(ceil(a))` (unit) |
| `conn_closure_r` | `inner(floor(a)) ≤ a` |
| `conn_kernel_l` | `ceil(inner(b)) ≤ b` (counit) |
| `conn_kernel_r` | `b ≤ floor(inner(b))` |
| `conn_monotone_l` | `a₁ ≤ a₂ ⟹ ceil(a₁) ≤ ceil(a₂) ∧ floor(a₁) ≤ floor(a₂)` |
| `conn_monotone_r` | `b₁ ≤ b₂ ⟹ inner(b₁) ≤ inner(b₂)` |
| `conn_idempotent` | `inner ∘ ceil` is idempotent on its image |

A tenth law, `conn_floor_le_ceil` (`floor(a) ≤ ceil(a)`), is asserted
only on connections whose `inner` is a documented injective embedding —
on saturating connections it fails at the saturation plateau by design.
See [`doc/design.md`](doc/design.md) §"Triple-only properties and the
role of injectivity".

For float-bearing types, the `≤` is a [N5 lattice](https://en.wikipedia.org/wiki/Distributive_lattice#Characteristic_properties). 
In particular, NaN is reflexive, NaN sits between ±∞ in the synthetic lattice, 
and finite values are strictly ordered. `ExtendedFloat` carries these semantics.

## What's shipped vs deferred

**Connection families (named consts):**

| Family | Module | Status |
|--------|--------|--------|
| Binary fixed-point (`I###I###`, i8/i16/i32/i64/i128 backing) | `fixed::{i8,i16,i32,i64,i128}` | shipped |
| Std-int widening + narrowing + cross-sign (`I###I###`, `U###I###`, `U###U###`, `I###U###`) | `int::{i8,i16,i32,i64,i128,u8,u16,u32,u64,u128}` | shipped |
| Float `f64 ↔ f32 ↔ f16` under N5 | `float` (`f16` cargo feature for f16) | shipped |
| `time` crate types (`DATEJDAY`, `TIMENANO`, `TIMESECS`, `DURNSECS`, `F032DURN`, `F064DURN`, `PDTMDATE`, `OFDTNANO`, `OFDTSECS`) | `time` | shipped |
| Domain-specific ladders (decimal time rungs, audio sample rates) | downstream crates ([`agogo`](https://gitlab.com/cmk/agogo) for audio) | moved |

**Cast operations** (Haskell `Data.Connection.Cast`):

| API | Status |
|-----|--------|
| L-side accessors + lifters: `upper`, `upper1`, `upper2`, `ceiling`, `ceiling1`, `ceiling2` | shipped (Sprint A) |
| R-side accessors + lifters: `lower`, `lower1`, `lower2`, `floor`, `floor1`, `floor2` | shipped (Sprint A) |
| Two-sided helpers: `interval`, `midpoint`, `round`/`round1`/`round2`, `truncate`/`truncate1`/`truncate2`, `median` | shipped (Sprint B) |
| Combinators: `bounded`, `ordered` (as macros) | planned (Sprint C) |
| `Down<T>` newtype + `filterL`/`filterR` | planned (Sprint D) |

**Intentionally not ported:**

- The `Side` data kind (`Cast 'L` / `Cast 'R`) — Rust lacks data kinds,
  and a single unified `Conn` carries both sides without compile-time
  bookkeeping. See [`doc/design.md`](doc/design.md) §"Core type" and
  §"Cast: L/R as a naming axis, not a type axis".
- `mapped` (lift a Conn through a `Functor f`) — needs HKTs. Specialize
  per container at the call site if needed.
- A standalone `Preorder` trait — Rust's `PartialOrd` covers most cases;
  the localized `Ple` handles the float-N5 corner. See
  [`doc/design.md`](doc/design.md) §"Why not a custom `Preorder` trait".

## Layout

```text
src/
├── lib.rs             — crate root + Cast API re-exports
├── conn.rs            — Conn struct, compose! macro, identity, Cast API
├── conn/              — supporting helpers split out of conn.rs
├── extended.rs        — Extended<T> with NegInf/Finite/PosInf
├── lattice.rs         — Join, Meet, Heyting, Coheyting, Symmetric, Boolean
├── int.rs   + int/    — i8..i128, u8..u128 widening / narrowing / cross-sign
├── fixed.rs + fixed/  — fixed-crate-backed binary Q-format ladders
├── float.rs + float/  — ExtendedFloat<T> + f64↔f32↔f16 (f16 nightly-gated)
├── time.rs  + time/   — Date, Time, Duration, OffsetDateTime conns
└── prop.rs  + prop/   — proptest strategies + law predicates
```

## Relationship to the Haskell `connections` library

This crate is a port of the Haskell library
[`connections`](https://github.com/cmk/connections/) (same author, same
mathematical content, different ergonomic trade-offs). The faithful
parts:

- The lattice trait hierarchy (`Join`, `Meet`, `Heyting`, `Coheyting`,
  `Symmetric`, `Boolean`).
- The N5 ordering on float-bearing types via `Ple` and
  `ExtendedFloat<T>`.
- The connection families (decimal/binary fixed-point, sample rates,
  integer widening, float pairs).
- The Cast API (Sprint A onward).

The deliberate divergences:

- One `Conn<A, B>` type instead of `Cast (k :: Side) a b`. Both
  L-side and R-side accessors are free functions on the unified type.
- Composition is a `compose!` macro over module-scope `const`s, not a
  generic `Category` instance. The trade-off is documented in
  [`doc/design.md`](doc/design.md) §"Composition".
- No `Preorder` class; `PartialOrd` + the localized `Ple` trait covers
  the cases that matter.

## Testing

```sh
cargo test --workspace
```

Every connection runs its `proptest` law suite on every commit (the
pre-commit hook in `.claude/settings.json` enforces this). Float
generators are biased toward NaN, ±∞, ±0, denormals, and ULP-boundary
values. Fixed-point generators are biased toward `0`, `±PREC`, and
`±i64::MAX/PREC` so saturation boundaries are exercised on every run.

Runtime dependencies are the [`fixed`](https://crates.io/crates/fixed)
crate (binary fixed-point ladder) and the
[`time`](https://crates.io/crates/time) crate (calendar / clock /
duration types in `time`). Proptest is a dev-dependency, exposed
publicly behind the `testing` feature for downstream test suites.

## Links

- [API docs on docs.rs](https://docs.rs/connections) — published
  releases, rendered from the crate metadata.
- [Latest docs on GitLab Pages](https://cmk.gitlab.io/connections/) —
  always tracks `main`; useful between releases.
- [`doc/design.md`](doc/design.md) — full design rationale, including
  the math, the N5 lattice, and the per-axis trade-offs.
- [`LICENSE-MIT`](LICENSE-MIT) — MIT license text.
- [GitLab project](https://gitlab.com/cmk/connections) — issues, MRs,
  and CI.
- [Haskell `connections`](https://github.com/cmk/connections/) — the
  upstream library this port mirrors.
- [nLab: Galois connection](https://ncatlab.org/nlab/show/Galois+connection) —
  background reading.
