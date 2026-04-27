# connections

[![CI](https://gitlab.com/cmk/connections/badges/main/pipeline.svg)](https://gitlab.com/cmk/connections/-/pipelines)

Galois connections as first-class Rust values. Use them to cast lawfully
between numeric types, expose ceiling/floor/inner alongside each other on
the same value, and compose ladders of conversions whose round-trip
behavior is property-tested rather than left to chance.

## Why this exists in Rust

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

3. **Ladders for time and rate work without hand-rolled multipliers.**
   Pico ↔ Nano ↔ Micro ↔ Milli ↔ Uni and S44.1 ↔ S48 ↔ S88.2 ↔ S96 ↔ S176
   ↔ S192 ladders ship as named constants. Composing across them is one
   `compose!` invocation, not a chain of multiply-divides where one
   off-by-one breaks the whole pipeline.

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
floor` between two preordered sets. A length-2 (one-sided) connection
sets `floor = ceil`. The struct is `Copy`, `const`-constructible,
heap-free, and the crate is `#![forbid(unsafe_code)]`.

For the math and the rationale behind a single unified `Conn` type
(rather than a Haskell-style `Cast 'L` / `Cast 'R` split), see
[`doc/design.md`](doc/design.md).

## Quick tour

A decimal-ladder cast:

```rust,no_run
use connections::conn::fixed::decimal::{F12F09, Pico, Nano};

let p = Pico(1_500);                    // 1500 picoseconds
assert_eq!(F12F09.ceil(p),  Nano(2));   // round up   → 2 ns
assert_eq!(F12F09.floor(p), Nano(1));   // round down → 1 ns
```

Composing four pair-conns into one `Pico → Uni` (seconds) cast:

```rust,no_run
use connections::compose;
use connections::conn::Conn;
use connections::conn::fixed::decimal::{F12F09, F09F06, F06F03, F03F00, Pico, Uni};

const F12F00: Conn<Pico, Uni> = compose!(F12F09, F09F06, F06F03, F03F00);
assert_eq!(F12F00.floor(Pico(1_500_000_000_000)), Uni(1));  // 1.5 s → 1 s
```

A sample-rate cast (88.2 kHz → 44.1 kHz, 2:1 ratio):

```rust,no_run
use connections::conn::sample::{S44, S88, S88S44};

assert_eq!(S88S44.ceil(S88::from_sample(14)), S44::from_sample(7));
assert_eq!(S88S44.inner(S44::from_sample(7)), S88::from_sample(14));
```

Integer widening through `Extended<T>` (so values *outside* the source
range have somewhere to land):

```rust,no_run
use connections::conn::int::U08I16;
use connections::extended::Extended;

assert_eq!(U08I16.ceil(Extended::Finite(200_u8)), 200_i16);
assert_eq!(U08I16.ceil(Extended::PosInf),         i16::MAX);
assert_eq!(U08I16.ceil(Extended::NegInf),         i16::MIN);
```

The Sprint A `Cast` API — accessors and lifters operating on any `Conn`:

```rust,no_run
use connections::{ceiling, upper1, maximize};
use connections::conn::Conn;
use connections::conn::fixed::decimal::{F12F09, Pico};

// `ceiling` is the named alias of `c.ceil` under the L-side reading.
assert_eq!(ceiling(&F12F09, Pico(1_500)), F12F09.ceil(Pico(1_500)));

// `upper1` lifts an endofunction over the target type back to the source:
//   upper1(c, f, a) = inner(f(ceil(a)))
let bumped = upper1(&F12F09, |n| n, Pico(1_500));
assert_eq!(bumped, F12F09.inner(F12F09.ceil(Pico(1_500))));

// `maximize` is the curried form of `ceiling` over a `Conn<(A, B), C>`.
fn pair_max(p: (i32, i32)) -> i32 { p.0.max(p.1) }
fn diag(x: i32) -> (i32, i32) { (x, x) }
fn pair_min(p: (i32, i32)) -> i32 { p.0.min(p.1) }
let ord: Conn<(i32, i32), i32> = Conn::new(pair_max, diag, pair_min);
assert_eq!(maximize(&ord, 3, 5), 5);
```

## What's lawful

Every connection ships with proptest coverage of the following laws — the
predicates live in `property::laws` and are re-runnable by downstream
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

For float-bearing types, the `≤` is N5-aware: NaN is reflexive, NaN sits
between ±∞ in the synthetic lattice, and finite values are strictly
ordered. The `Ple` trait at `src/lattice.rs` carries this semantics.

## What's shipped vs deferred

**Connection families (named consts):**

| Family | Module | Status |
|--------|--------|--------|
| Decimal fixed-point ladder (`F??F??`, F00–F12) | `conn::fixed::decimal` | shipped |
| Binary fixed-point (`fixed`-crate native, `i08`/`i16`/`i32`/`i64`) | `conn::fixed::{i08,i16,i32,i64}` | shipped |
| Sample-rate pairs (`S???S???`, 6 audio rates) | `conn::sample` | shipped |
| Pico ↔ rate cross-tier (`F12S???`) | `conn::sample` | shipped |
| Signed widening over `Extended<T>` (`I??I??`, `U??I??`) | `conn::int` | shipped |
| Unsigned widening / sign change (`U??U??`, `I??U??`) | `conn::uint` | shipped |
| Float `f64 ↔ f32` under N5 | `conn::float` | shipped |
| Float ↔ rung over `ExtendedFloat<T>` (`F64F??`) | `conn::fixed::decimal` | shipped |

**Cast operations** (Haskell `Data.Connection.Cast`):

| API | Status |
|-----|--------|
| L-side accessors + lifters: `upper`, `upper1`, `upper2`, `ceiling`, `ceiling1`, `ceiling2`, `maximize` | shipped (Sprint A) |
| R-side accessors + lifters: `lower`, `lower1`, `lower2`, `floor`, `floor1`, `floor2`, `minimize` | shipped (Sprint A) |
| Two-sided helpers: `interval`, `midpoint`, `round`/`round1`/`round2`, `truncate`/`truncate1`/`truncate2`, `median` | planned (Sprint B) |
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

## Layout

```text
src/
├── lib.rs              — crate root + Cast API re-exports
├── conn/
│   ├── mod.rs          — Conn struct, compose! macro, identity
│   ├── cast.rs         — L/R accessors + lifters (Sprint A)
│   ├── fixed/          — decimal & binary fixed-point ladders
│   ├── float.rs        — ExtendedFloat<T> + f64↔f32
│   ├── int.rs          — signed-widening via Extended<T>
│   ├── sample.rs       — sample-rate ladders + Pico↔rate
│   └── uint.rs         — unsigned widening, sign change
├── extended.rs         — Extended<T> with NegInf/Finite/PosInf
├── lattice.rs          — Ple, Join, Meet, Heyting, Coheyting, Symmetric, Boolean
└── property/           — proptest strategies + law predicates
```

## Testing

```sh
cargo test --workspace
```

Every connection runs its `proptest` law suite on every commit (the
pre-commit hook in `.claude/settings.json` enforces this). Float
generators are biased toward NaN, ±∞, ±0, denormals, and ULP-boundary
values. Fixed-point generators are biased toward `0`, `±PREC`, and
`±i64::MAX/PREC` so saturation boundaries are exercised on every run.

The only required runtime dependency is the
[`fixed`](https://crates.io/crates/fixed) crate (for the binary
fixed-point ladder); proptest is a dev-dependency and is exposed
publicly behind the `testing` feature for downstream test suites.

## Links

- [`doc/design.md`](doc/design.md) — full design rationale, including
  the math, the N5 lattice, and the per-axis trade-offs.
- [GitLab project](https://gitlab.com/cmk/connections) — issues, MRs,
  and CI.
- [Haskell `connections`](https://github.com/cmk/connections/) — the
  upstream library this port mirrors.
- [nLab: Galois connection](https://ncatlab.org/nlab/show/Galois+connection) —
  background reading.
