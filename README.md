<!-- TODO: on first crates.io publish, swap badges back to dynamic
     shields.io/crates/v/connections.svg + shields.io/docsrs/connections -->
[![crates.io](https://img.shields.io/badge/crates.io-unreleased-lightgrey.svg)](https://crates.io/crates/connections)
[![docs](https://img.shields.io/badge/docs-github.io-blue.svg)](https://cmk.github.io/connections/)
[![MSRV](https://img.shields.io/badge/MSRV-1.88-blue.svg)](https://github.com/cmk/connections)
[![CI](https://github.com/cmk/connections/actions/workflows/ci.yml/badge.svg)](https://github.com/cmk/connections/actions/workflows/ci.yml)

Read the docs [here](https://cmk.github.io/connections/).

# Overview

Galois connections as first-class Rust values. Use them to cast lawfully
between numeric types, and compose ladders of conversions whose round-trip
behavior is determined by simple inequalities rather than left to chance.
Every operation derived from a `Conn` (rounding, saturation, median, ...)
carries a property-tested invariant, so chains of conversions and round-
trips behave predictably according to simple inequalities that are both
property tested and **SMT-proven** over the full bit-width domain via
[Kani](https://model-checking.github.io/kani/) (see
[Testing → SMT verification](#smt-verification-kani)).

**MSRV: Rust 1.88.** Bumps to the MSRV will be treated as minor-version
changes — pin `connections = "0.1"` and an MSRV upgrade will surface as
a 0.2 release rather than a silent break on a patch update.

This crate is a Rust-native port of the Haskell library
[`connections`](https://github.com/cmk/connections-haskell).

## Why this crate

Galois connections are the right shape for *static, lawful*
conversions between partially ordered types (e.g. `f64 → f32`,
`Duration → seconds`, `f32 → u32 → IpAddr`, etc) where each link in
the chain is specifiable at compile time.

The standard cast operators `as`, `From`, and `Into` give you exactly one
direction at a time — and `as` in particular is silent on rounding,
saturation, and lossy conversion. Three concrete things this crate gives
you that the standard tools don't:

1. **Both arms of a cast on one value.** An adjoint-triple marker
   exposes `ceil: A → B`, `floor: A → B`, *and* the embedding (`upper`
   / `lower`) as a unit struct implementing both `ConnL` and `ConnR`
   — you don't pick "ceiling cast" vs "floor cast" up front, you carry
   the marker and call whichever you need per-call. (One-sided
   connections — where only one law holds — ship as kind-tagged
   `Conn<A, B>` (L) / `Conn<A, B, R>` values, exposing only the
   methods of their kind.)

2. **Round-trip identities that hold.** `(x as f32) as f64 != x` for many
   `x: f64`. With a `Conn`, the closure law `a ≤ inner(ceil(a))` and
   kernel law `ceil(inner(b)) ≤ b` are property-tested for *every*
   shipped connection. If you compose two connections with `compose!`,
   the result is property-tested too.

   A `Conn` is `Copy`, `const`-constructible, heap-free, and the crate 
   is `#![forbid(unsafe_code)]`.

3. **Conversions composed by `compose!` are property-tested too.**
   The `compose!` macro folds a chain of pairwise Conns into one
   fresh `Conn<Src, Dst>` at compile time — type-flow comes from
   the binding annotation, intermediates are inferred. Domain-
   specific ladders (decimal time rungs, audio sample rates) live
   in downstream crates; this crate ships the algebra.

## Quick start

```rust
use connections::prelude::*;
use connections::core::B2;
use connections::core::i016::I016BE02;

let bytes = B2([0x01, 0x02]);
assert_eq!(I016BE02.ceil(258_i16), bytes);
assert_eq!(I016BE02.floor(258_i16), bytes);
assert_eq!(I016BE02.upper(bytes), 258_i16);
assert_eq!(I016BE02.lower(bytes), 258_i16);
```

See [EXAMPLES.md](https://github.com/cmk/connections/blob/main/EXAMPLES.md)
for a sequence of ten worked examples in various domains.

## What are connections?

A [Galois connection](https://en.wikipedia.org/wiki/Galois_connection)
between preorders A and B is a pair of monotone maps `f: A → B` and
`g: B → A` such that `f(x) ≤ y ⇔ x ≤ g(y)`. We say `f` is the *left*
or *lower* adjoint, and `g` is the *right* or *upper* adjoint of the
connection.

Here is a simple connection between two 3-element sets:

![](https://github.com/cmk/connections/raw/main/img/example.png)

(image courtesy of [7 Sketches in Compositionality](https://math.mit.edu/~dspivak/teaching/sp18/7Sketches.pdf)).

Each row is a `(a, b)` pair; arrows show the action of `f` (A → B,
bottom legend) and `g` (B → A, top legend). Lone arrows mark
single-direction maps (`f(1) = 1`, `g(2) = 2`); the `↔` marks a
matched pair where both adjoints agree (`f(3) = 3`, `g(3) = 3`); the
adjacent `↰ ↳` glyphs depict the *lens* `f(2) ↔ g(1)` — two
non-crossing curves between rows 2 and 1, the geometric signature of
adjointness.

## How to use connections

Galois connections compose: (f₁ ⊣ g₁) ∘ (f₂ ⊣ g₂) is again an
adjunction, and `compose!` builds that composite statically,
law-checked as a whole. The moment you apply a destructor (e.g.
`upper` , `lower`, `ceil`, `floor`, etc) you've left the Conn algebra
and produced a concrete value that can no longer be composed. So early
destructuring throws away the static guarantees that the full
chain would have otherwise enjoyed. Therefore you will get the most
bang for your buck if you follow two heuristics.

**Lift through the Conn.** A Conn is a little black box: the higher-
arity helpers (e.g. `ceil*`, `floor*`, `round*`, `truncate*`, etc)
take your arguments, do something with them in the Conn's other
(usually higher-fidelity) domain, and return the result back in
your original domain. `ceil2(t, h, b1, b2)` is `f(h(g(b1), g(b2)))`:
embed `b1`/`b2` into the wider domain via `g`, run the closure `h`
there, round back via `f`. Use this for domain arithmetic that would
overflow or lose precision in your own type - do it in the wider
domain and round back. Never hand-roll saturating math.

**Compose at the site.** Export Conns at the library level and use
the `ConnL`/`ConnR`/`ConnK` API instead of get/set functions. When
client code needs a multi-hop conversion, build the exact Conn with
the compose macros (`compose`, `compose_l`, `compose_r`, `compose_k`)
statically at the call site. Do not thread intermediates by hand.
If the client code takes a runtime parameter then it's best to keep the
helper as a normal named function whose body *visibly composes* with
the lawful Conns it depends on.
   
The discipline of pushing runtime parameters and conversion policy
choices close to the static Conn call site means that the policy and
the static cast are both visible in the same body. The results is code
that is visibly correct, easy to test, and extensible to future use
cases.

# Library

## L & R kind connections

The basic type in this library is:

```text
pub struct Conn<A, B, K: Kind = L> {
    f: fn(A) -> B,   // L-kind: ceil; R-kind: floor
    g: fn(B) -> A,   // L-kind: upper, R-kind: lower
    // plus a phantom kind tag K ∈ {L, R}
}
```

A `Conn<A, B, K>` is exactly a Galois connection — a pair of monotone
functions `(f, g)` whose adjoint role depends on the kind tag. An
L-kind Conn satisfies `f(a) ≤ b ⟺ a ≤ g(b)`; an R-kind Conn
satisfies `g(b) ≤ a ⟺ b ≤ f(a)`.

The kind `K = {L, R}` determines the API. `L`/`ConnL` exposes `.ceil()`
and `.upper()`, while `R`/`ConnR` exposes `.floor()` and `.lower()`.

- **Direction names** — `ceil` (rounds up) and `floor` (rounds down) —
  match downstream intuition. "Give me a ceiling cast" doesn't require
  the caller to know which side of an adjunction they're on. However
  calling `.floor()` on an L-kind connection, or `ceil` on an R-kind
  connection results in a compiler error.
- **Position names** — `upper` (the upper adjoint of the L-pair) and
  `lower` (the lower adjoint of the R-pair) — match the math: a
  generic `T: ConnK` bound exposes both because a triple has both
  adjunctions, regardless of which way each one rounds in any concrete
  instance.
- **Consts vs markers** - Regular connections are `pub const`s of type
  `Conn<A, B, L>` or `Conn<A, B, R>`. Two-sided `ConnK` connections
  ship as `pub struct`s — zero-sized marker types implementing both
  `ConnL` and `ConnR`. The const-vs-struct shape tells you which kind
  a name refers to at a glance.

## API

- L-side methods on `Conn<_, _, L>` (and on any `ConnL` implementor
  via default-method dispatch): `ceil`, `upper`, plus `ceil1`/`2`,
  `upper1`/`2` lifters.
- R-side methods on `Conn<_, _, R>` (and on any `ConnR` implementor):
  `floor`, `lower`, plus `floor1`/`2`, `lower1`/`2` lifters.
- Two-sided helpers (re-exported at the crate root): `interval`,
  `round`/`round1`/`round2`,
  `truncate`/`truncate1`/`truncate2`, `median`. All bind on
  `T: ConnK` (super-trait of `ConnL + ConnR` over the same `(A, B)`),
  so they're callable only on triple markers — not on one-sided Conns.

Kind discipline is structural: calling `.floor(...)` on an L-kind
Conn is a compile error (the method only exists on `Conn<_, _, R>`),
and likewise `.ceil(...)` on R. Two-sided helpers similarly reject
one-sided operands at compile time because a one-sided `Conn` doesn't
implement `ConnK`.

## Modules

| Family | Module |
|--------|--------|
| IEEE-754 types | `float` | 
| Q-format binary fixed-point (`Q###Q###`, i8/u8 … i128/u128 backing) | `fixed::{i008,…,i128, u008,…,u128}` (`fixed` cargo feature) |
| Std-int widening + narrowing + cross-sign (`I###I###`, `U###I###`, `U###U###`, `I###U###`) | `core::{i008,…,i128, u008,…,u128}` |
| `iN`/`uN` ↔ `NonZero<{i,u}N>` (`I###N###`, `U###N###`) | `core::{i008,…,i128, u008,…,u128}` |
| Cross-crate iso `Fixed{I,U}<U0> ↔ {i,u}{N}` (`Q000I###`, `Q000U###`) and signed normalized bit isos (`Q007I008` … `Q127I128`) | `fixed::{i008,…,i128, u008,…,u128}` (`fixed` cargo feature) |
| Float `f64 ↔ f32 ↔ f16` under N5 | `float` (`f16` cargo feature for f16) |
| `time` crate types (`DATEJDAY`, `TIMENANO`, `TIMESECS`, `TDURSECS`, `F032TDUR`, `F064TDUR`, `PDTMDATE`, `ODTMNANO`, `ODTMSECS`) and the `std::time::Duration` family (`SDURU064`, `SDURU128`, `F064SDUR`, `F032SDUR`) for users on `std::time` | `time` cargo feature |
| `std::net` addresses (`U032IPV4`, `U128IPV6`, `IPV6IPV4`, `IPVXIPV4`, `IPVXIPV6`, `SOVXSOV4`, `SOVXSOV6`) | `addr` |
| `char` codepoint projection (`U032CHAR`, surrogate-gap-aware) | `char` |
| Pointer-width `usize` saturating casts (`USZEU008`, `USZEU016`, `USZEU032`, `USZEU064`, `USZEU128`) | `core::usize` |
| Pointer-width `isize` casts (`ISZEI008`, `ISZEI016`, `ISZEI128`; `→ i32`/`→ i64` deferred) | `core::isize` |
| Sortable byte encodings (`U008BE01`, `U008LE01`, `I008BE01`, `I008LE01`, `BOOLBE01`, `BOOLLE01`, through `U128BE16`, `U128LE16`, `I128BE16`, `I128LE16`) | `core::{bool, i008,…,i128, u008,…,u128}` |

Constant-name prefixes are letter-disambiguated: `Q` for Q-format
wrappers (sign and host bit-width come from the module path), `I`/`U`
for std primitives (digits = bit-width), `N` for `NonZero<*>`, `F` for
IEEE floats. Cross-module name collisions are allowed and resolved by
qualified import (e.g. `fixed::i008::Q008Q000` and
`fixed::i064::Q008Q000` co-exist).

# `ConnK` connections

When the same `inner` function can serve as both `upper` and `lower`
*and* satisfies an additional order-reflecting property (see 
[Sandwich inequality](#sandwich-inequality)), the library combines
the two resulting connections into a zero-sized marker struct that
gains a third group of 'ambidextrous' helpers via a super-trait that
ties the `L` and `R` sides together:

- **`ConnL`** — capability trait with associated types `type A: Copy;
  type B: Copy;` and a `conn_l()` projection to the L-view
  `Conn<A, B, L>`. Default methods expose `.ceil()` and `.upper()`.
- **`ConnR`** — symmetric capability trait whose `conn_r()` projects
  to the R-view `Conn<A, B, R>`. Default methods expose `.floor()`
  and `.lower()`.
- **`ConnK`** — super-trait `ConnL + ConnR` over the same `(A, B)`
  pair; the two-sided helpers (`round`, `truncate`, …) bind on
  `ConnK` and reach through both views.

The trait names match the value-type spellings on purpose: a blanket
`impl ConnL for Conn<A, B, L>` (and the R-side analogue) makes every
one-sided value also satisfy the trait, so a generic `T: ConnL` bound
accepts triple markers and raw `Conn<A, B, L>` values uniformly, and
`inner` is defined as a free function in module scope, referenced
from the marker's trait impls; no struct in the crate stores three
function pointers.

## Adjoint triples

You construct a `ConnK` marker out of three functions: `ceil`, `inner`, 
and `floor` using one of the crate's provided macros. Note that both
`ceil`/`inner` and `inner`/`floor` must satisfy the connection
inequalities given above. In addition `ceil`/`floor` must satisfy
the following 'sandwich' inequality: for every `a`, `floor(a) ≤ ceil(a)`

Triples `ceil`/`inner`/`floor` that satisfy all three properties are known
as [adjoint triples](https://ncatlab.org/nlab/show/adjoint+triple) — the
`ceil ⊣ inner ⊣ floor` shape outlined in
[Example 3](https://github.com/cmk/connections/blob/main/EXAMPLES.md#example-3).

The sandwich inequality is equivalent to the earlier requirement that
`inner` be [order-reflecting](https://en.wikipedia.org/wiki/Order_theory#Functions_between_orders).
The `prop::conn::law_battery!` `full` subset enforces both [`floor_le_ceil`]
as well as [`order_reflecting`]:

[`floor_le_ceil`]: https://docs.rs/connections/latest/connections/prop/conn/fn.floor_le_ceil.html
[`order_reflecting`]: https://docs.rs/connections/latest/connections/prop/conn/fn.order_reflecting.html

Proof of equivalence is outlined in the following section.

## Sandwich inequality

Both directions of the equivalence follow from applications of the
adjunction laws. Both proofs use only L-Galois `f ⊣ g`, R-Galois
`g ⊣ h`, monotonicity, and transitivity — no extra assumptions.

**Sufficiency** (`inner` order-reflecting ⟹ `floor(a) ≤ ceil(a)`).
Take any `a ∈ A`. The two closure laws give

```text
inner(floor(a)) ≤ a ≤ inner(ceil(a))
```

so by transitivity `inner(floor(a)) ≤ inner(ceil(a))`. Since `inner`
is order-reflecting, this lifts to `floor(a) ≤ ceil(a)`. ∎

**Necessity** (`floor(a) ≤ ceil(a)` everywhere ⟹ `inner` order-reflecting).
Take `x, y ∈ B` with `inner(x) ≤ inner(y)`. Chain:

```text
x ≤ floor(inner(x))     -- kernel of inner ⊣ floor, with b = x
  ≤ ceil(inner(x))      -- assumption at a = inner(x)
  ≤ y                   -- L-Galois ceil(a) ≤ b ⟺ a ≤ inner(b),
                           with a = inner(x), b = y; the RHS
                           inner(x) ≤ inner(y) is given
```

So `x ≤ y`. ∎

(Categorically: in an adjoint triple `f ⊣ g ⊣ h` over posets, `g`
fully faithful ⟺  the counit of `g ⊣ h` is iso ⟺  the unit of `f ⊣ g` 
is iso ⟺ `h ≤ f`. The two displays above are that equivalence written for
posets, where "fully faithful" reduces to "order-reflecting" and "iso" to
"equality".)

**Counterexample** — necessity is sharp. Let `A = {a}` (one element)
and `B = {b₁ < b₂ < b₃}`, with `inner: B → A` the constant map
(`inner(b) = a` for every `b` — monotone but maximally non-injective).
Watch what the per-side Galois laws force:

- L-Galois `ceil(a) ≤ b ⟺ a ≤ inner(b)`. The RHS reduces to `a ≤ a`,
  which is always true, so `ceil(a) ≤ b` for *every* `b ∈ B`. The
  smallest such `b` is `b₁`, so **`ceil(a) = b₁`**.
- R-Galois `inner(b) ≤ a ⟺ b ≤ floor(a)`. The LHS reduces to `a ≤ a`,
  always true, so `b ≤ floor(a)` for *every* `b`, giving
  **`floor(a) = b₃`**.

Both per-side adjunctions hold, every monotonicity check passes — and
yet `floor(a) = b₃ > b₁ = ceil(a)`. The "triple" type-checks and the
per-side laws are satisfied, but the rounding sandwich is *inverted*.

The two-sided helpers inherit the inversion. `round(a)` compares
`inner(floor(a)) = a` with `inner(ceil(a)) = a` to pick the closer
endpoint, finds them equal, and falls through to `truncate`, which
returns whichever side the source-zero rule selects — a value with no
in-band signal that anything is wrong. **A connection that fails the
sandwich inequality isn't an academic foul; the two-sided helpers
actively misbehave on it.**

# Installation

```sh
cargo add connections
```

| | |
|--|--|
| **MSRV** | Rust 1.88 (matches `rust-toolchain.toml`) |
| **Edition** | 2024 |
| **License** | MIT (see [`LICENSE-MIT`](LICENSE-MIT)) |

Optional cargo features:

| Feature | What it enables | Toolchain |
|---------|-----------------|-----------|
| `fixed` | `connections::fixed::{i008,…,u128}` Q-format ladders, float→Q bridges, Q.0 primitive isos, and signed normalized bit isos | stable |
| `proptest` | Re-exports `connections::prop::arb` (proptest strategies) for downstream test suites | stable |
| `macros` | Re-exports the internal codegen macro families under `connections::macros` / crate-root macro paths | stable |
| `time` | Civil-calendar and time-span Conns backed by the `time` crate | stable |
| `hifi` | Nanosecond-precision `hifitime::Duration` / `Epoch` Conns | stable |
| `f16` | IEEE binary16 connections (`F016`, `F032F016`, `F064F016`) and their proptest strategies | nightly (uses `#![feature(f16)]` — tracking [#116909](https://github.com/rust-lang/rust/issues/116909)) |
| `try_trait` | `?`-operator (`Try` / `FromResidual`) support on `Interval`, `Extended`, `ExtendedFloat` — extracts the success payload, short-circuits on the boundary variants | nightly (uses `#![feature(try_trait_v2)]` — tracking [#84277](https://github.com/rust-lang/rust/issues/84277)) |

The `connections::prop::conn` and `connections::prop::lattice`
predicate modules are *always* public — they're pure `bool`-returning
functions over this crate's own types and don't depend on `proptest`.
The `testing` feature only adds `prop::arb`, the strategy module that
does pull `proptest` in as a regular dependency.

# Testing

```sh
cargo test --workspace
```

Every connection runs its `proptest` law suite on every commit (the
pre-commit hook in `.claude/settings.json` enforces this). Float
generators are biased toward NaN, ±∞, ±0, denormals, and ULP-boundary
values. Fixed-point generators are biased toward `0`, `±PREC`, and
`±i64::MAX/PREC` so saturation boundaries are exercised on every run.

Runtime dependencies are feature-gated. The
[`fixed`](https://crates.io/crates/fixed) crate backs the optional
binary fixed-point ladder, [`time`](https://crates.io/crates/time)
backs the optional civil-calendar / clock surface, and
[`hifitime`](https://crates.io/crates/hifitime) backs the optional
high-precision time surface. Proptest is a dev-dependency, exposed
publicly behind the `testing` feature for downstream test suites.

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
only on `ConnK` connections whose `inner` is an injective embedding. See
[above](#sandwich-inequality).

For float-bearing types, the `≤` is a [N5 lattice](https://en.wikipedia.org/wiki/Distributive_lattice#Characteristic_properties). 
In particular, NaN is reflexive, NaN sits between ±∞ in the synthetic lattice, 
and finite values are strictly ordered. `ExtendedFloat` carries these semantics.

## SMT verification (Kani)

Beyond the proptest law suite — which samples — every Galois law on
every fixed-width integer / Q-format / NonZero / iso connection is
**SMT-proven** over the full bit-width domain via
[Kani](https://model-checking.github.io/kani/). The pointer-width
`usize` / `isize` families (`core::usize` / `core::isize`) are the
exception: CBMC models a single concrete pointer width per run, so
those Conns are covered by the proptest battery on the host target
rather than a width-agnostic SMT proof. The proof tree lives at
[`src/kani_proofs/`](https://github.com/cmk/connections/tree/main/src/kani_proofs)
and is gated behind `#[cfg(kani)]` so it compiles only under
`cargo kani` — release builds, `cargo test`, and downstream consumers
see no proof code. No new runtime dependency: Kani injects its own
crate at proof time.

The main result is on the float side, where the IEEE bit space is
too large for full-Galois proofs to be tractable: the f64 → f32
ULP-walk in `src/float/f064.rs` (`ceil_f64_f32` / `floor_f64_f32`) is
proven to converge in **≤ 2 iterations for every finite non-NaN
f64**, not just the proptest sample. Three tiered harnesses
(`float_walk::t0_*` for the full domain, `t1_*` for `|x| ≤ 1e6`,
`t2_*` for the `[1, 2)` binade) each verify the bound under
progressively tighter input restrictions.

Run with:

```sh
cargo install --locked kani-verifier
cargo kani setup
cargo kani                                   # full proof tree
cargo kani --harness 'float_walk::t0_'       # the headline
cargo kani --harness 'int_narrow::'          # one family
```

Per-harness wall times are in the milliseconds-to-seconds range; the
full tree runs in well under two minutes.
