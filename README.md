[![CI](https://gitlab.com/cmk/connections/badges/main/pipeline.svg)](https://gitlab.com/cmk/connections/-/pipelines)

Read the docs [here](https://cmk.gitlab.io/connections/).

Galois connections as first-class Rust values. Use them to cast lawfully
between numeric types, and compose ladders of conversions whose round-trip
behavior is determined by simple inequalities rather than left to chance.
The connection laws are not just sampled by proptest — every Galois law
on every integer / Q-format / NonZero / iso connection is
**SMT-proven** over the full bit-width domain via
[Kani](https://model-checking.github.io/kani/) (see
[Testing → SMT verification](#smt-verification-kani)).

**MSRV: Rust 1.85.** Bumps to the MSRV will be treated as minor-version
changes — pin `connections = "0.1"` and an MSRV upgrade will surface as
a 0.2 release rather than a silent break on a patch update.

This crate is a Rust-native port of the Haskell library [`connections`](https://github.com/cmk/connections/).

# Quick start

Most users only need `.ceil`, `.floor`, and the embedding (`.upper` for
an L-side or triple Conn, `.lower` for an R-side Conn). The rest of
this doc explains how those names get earned.

```rust
use connections::conn::{ConnL, ConnR};
use connections::time::DURNSECS;
use connections::extended::Extended;
use time::Duration;

let pos = Duration::seconds(5) + Duration::nanoseconds(1);
assert_eq!(DURNSECS.ceil(pos),  Extended::Finite(6));   // round up
assert_eq!(DURNSECS.floor(pos), Extended::Finite(5));   // round down

let neg = Duration::seconds(-5) - Duration::nanoseconds(1);
assert_eq!(DURNSECS.ceil(neg),  Extended::Finite(-5));  // round up
assert_eq!(DURNSECS.floor(neg), Extended::Finite(-6));  // round down
```

See [EXAMPLES.md](https://gitlab.com/cmk/connections/-/blob/main/EXAMPLES.md)
for a sequence of ten worked examples in various domains.

# Why this crate

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

# What are connections?

A [Galois connection](https://en.wikipedia.org/wiki/Galois_connection)
between preorders A and B is a pair of monotone maps `f: A → B` and
`g: B → A` such that `f(x) ≤ y ⇔ x ≤ g(y)`. We say `f` is the *left*
or *lower* adjoint, and `g` is the *right* or *upper* adjoint of the
connection.

Here is a simple connection between two 3-element sets:

![](https://gitlab.com/cmk/connections/-/raw/main/img/example.png)

(image courtesy of [7 Sketches in Compositionality](https://math.mit.edu/~dspivak/teaching/sp18/7Sketches.pdf)).

Each row is a `(a, b)` pair; arrows show the action of `f` (A → B,
bottom legend) and `g` (B → A, top legend). Lone arrows mark
single-direction maps (`f(1) = 1`, `g(2) = 2`); the `↔` marks a
matched pair where both adjoints agree (`f(3) = 3`, `g(3) = 3`); the
adjacent `↰ ↳` glyphs depict the *lens* `f(2) ↔ g(1)` — two
non-crossing curves between rows 2 and 1, the geometric signature of
adjointness.

Connections are useful for **lawful conversions** between types: every
operation derived from a `Conn` (rounding, saturation, midpoint,
median, ...) carries a property-tested invariant, so chains of conversions
and round-trips behave predictably according to simple inequalities.

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

The crate keeps two distinct naming axes on purpose:

- **Position names** — `upper` (the upper adjoint of the L-pair) and
  `lower` (the lower adjoint of the R-pair) — match the math: a
  generic `T: ConnK<A,B>` bound exposes both because a triple has both
  adjunctions, regardless of which way each one rounds in any concrete
  instance.
- **Direction names** — `ceil` (rounds up) and `floor` (rounds down) —
  match downstream intuition. "Give me a ceiling cast" doesn't require
  the caller to know which side of an adjunction they're on. However
  calling `.floor()` on an L-kind connection, or `ceil` on an R-kind
  connection results in a compiler error.

## 2-kinded connections

In many cases it is possible to get **both** sides using the same common
`inner` function. Furthermore if `inner` is order-reflecting (see below)
then a third group of 'ambidextrous' functions (e.g. `round`, `truncate`
, etc.) is available through a zero-sized `ConnK` marker type with
capability traits, `ConnL<A, B>` and `ConnR<A, B>`. These traits `conn_l`
and `conn_r` methods project to the L-view and R-view `Conn`s of the
triple. The trait names match the value-type spellings on purpose:
the blanket `impl ConnL for Conn<A, B, L>` (and the R-side analogue)
makes every one-sided value also satisfy the trait, so a generic
`T: ConnL<A, B>` bound accepts triple markers and raw `Conn<A, B, L>`
values uniformly. The "third function" — the adjoint that distinguishes
a triple from a one-sided Conn — lives as a free function in module
scope, referenced from the marker's trait impls; no struct in the
crate stores three fns. Two-sided helpers (`round`, `truncate`, …)
bind on the `ConnK<A, B>` super-trait (`= ConnL + ConnR`) and reach
through both views.

You construct a `ConnK` marker out of three functions: `ceil`, `inner`, 
and `floor`. Both `ceil`/`inner` and `inner`/`floor` must satisfy the 
connection property given above. In addition `ceil`/`floor` must satisfy
the following 'sandwich' inequality: for every `a`, `floor(a) ≤ ceil(a)`

Triples `ceil`/`inner`/`floor` that satisfy all three properties are known
as [adjoint triples](https://ncatlab.org/nlab/show/adjoint+triple) — the
`ceil ⊣ inner ⊣ floor` shape outlined in
[Example 3](https://gitlab.com/cmk/connections/-/blob/main/EXAMPLES.md#example-3).

The sandwich inequality is equivalent to the requirement that `inner` be
[order-reflecting](https://en.wikipedia.org/wiki/Order_theory#Functions_between_orders).
The `prop::conn::law_battery!` `full` subset enforces both [`floor_le_ceil`]
as well as [`order_reflecting`]. Proof of equivalence is outlined in the 
following section.

[`floor_le_ceil`]: https://docs.rs/connections/latest/connections/prop/conn/fn.floor_le_ceil.html
[`order_reflecting`]: https://docs.rs/connections/latest/connections/prop/conn/fn.order_reflecting.html

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
fully faithful ⟺  the counit of `g ⊣ h` is iso ⟺  the unit of `f ⊣ g` is iso
⟺ `h ≤ f`. The two displays above are that equivalence written for
posets, where "fully faithful" reduces to "order-reflecting" and
"iso" to "equality".)

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

# When to use connections

Galois connections are the right shape for *static, lawful* numeric
conversions: `f64 → f32`, `Duration → seconds`, `f32 → u32 → IpAddr`,
where each link in the chain is specifiable at compile. Connections
are **not** a good fit when:

1. **The conversion validates input.** FFI clamps, sentinel-checking
   wrappers, and "domain restriction" guards belong as named helpers.
   They're not adjunctions — they're partial functions that happen to
   delegate to a Conn after a precondition check. Naming the precondition
   in the helper signature is more useful than forcing it into a Conn.

2. **The conversion needs a domain policy.** "Round to nearest sample,
   ties toward zero, with a clamp at the audio max" is one specific
   policy among several lawful ones; a Conn picks one. If your callers
   need to inject the policy, expose the underlying ceil/floor/upper
   primitives and let them assemble the policy at the call site.

3. **The conversion takes a runtime parameter.** Keep the helper
   as a normal named function whose body *visibly composes* the
   lawful Conns it depends on.

The discipline of pushing runtime parameters and policy choices *close
to the static Conn call site* tends to make conversion code clearer,
not more verbose — the policy and the static cast are both visible in
the same body. A boundary helper that names what it does and visibly
composes lawful Conns is a feature, not a workaround.

# Installation

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

# Testing

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
every integer / Q-format / NonZero / iso connection is **SMT-proven**
over the full bit-width domain via
[Kani](https://model-checking.github.io/kani/). The proof tree lives at
[`src/kani_proofs/`](https://gitlab.com/cmk/connections/-/tree/main/src/kani_proofs)
and is gated behind `#[cfg(kani)]` so it compiles only under
`cargo kani` — release builds, `cargo test`, and downstream consumers
see no proof code. No new runtime dependency: Kani injects its own
crate at proof time.

The headline result is on the float side, where the IEEE bit space is
too large for full-Galois proofs to be tractable: the f64 → f32
ULP-walk in `src/float/f32.rs` (`ceil_f64_f32` / `floor_f64_f32`) is
proven to converge in **≤ 2 iterations for every finite non-NaN
f64**, not just the proptest sample. Three tiered harnesses
(`float_walk::t0_*` for the full domain, `t1_*` for `|x| ≤ 1e6`,
`t2_*` for the `[1, 2)` binade) each verify the bound under
progressively tighter input restrictions.

Coverage as of plan 39 (the introducing sprint): **1154 harnesses
verified, 0 failures** across the integer-narrowing
(`int_int_narrow!`, `uint_uint_narrow!`, `int_uint_narrow!`),
integer-widening (`uint_uint!`, `int_uint!`, `ext_int!`),
non-widening saturating (`uint_int_sat!`), NonZero-bridge
(`nz_int_ext!`, `nz_uint_ext!`), Q-format ladder (`fix_fix_iN!` /
`fix_fix_uN!`), cross-crate iso (`iso!`), and float-walking families.
The `nz_int_ext!` harnesses additionally prove the closures'
`<NonZero<_>>::new(_).unwrap()` calls cannot panic.

Out of scope for now: time and address Conns (would require Kani to
symbolically execute external crate internals), full Galois laws on
float Conns over the unrestricted IEEE bit space (intractable for
CBMC's FP theory; `src/kani_proofs/float_weaker.rs` covers the
productive finite-domain subset), and composed-Conn lattice axioms.

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

# Library

## API

- L-side methods on `Conn<_, _, L>` (and on any `ConnL` implementor
  via default-method dispatch): `ceil`, `upper`, plus `ceil1`/`2`,
  `upper1`/`2` lifters.
- R-side methods on `Conn<_, _, R>` (and on any `ConnR` implementor):
  `floor`, `lower`, plus `floor1`/`2`, `lower1`/`2` lifters.
- Two-sided helpers (re-exported at the crate root): `interval`,
  `midpoint`, `round`/`round1`/`round2`,
  `truncate`/`truncate1`/`truncate2`, `median`. All bind on
  `T: ConnK<A, B>` (= `ConnL + ConnR`), so they're callable only on
  triple markers — not on one-sided Conns.

Kind discipline is structural: calling `.floor(...)` on an L-kind
Conn is a compile error (the method only exists on `Conn<_, _, R>`),
and likewise `.ceil(...)` on R. Two-sided helpers similarly reject
one-sided operands at compile time because a one-sided `Conn` doesn't
implement `ConnK`.

## Modules

| Family | Module |
|--------|--------|
| IEEE-754 types | `float` | 
| Q-format binary fixed-point (`Q###Q###`, i8/u8 … i128/u128 backing) | `fixed::{i8,…,i128, u8,…,u128}` |
| Std-int widening + narrowing + cross-sign (`I###I###`, `U###I###`, `U###U###`, `I###U###`) | `fixed::{i8,…,i128, u8,…,u128}` (alongside the Q-format ladder for the same destination) |
| `iN`/`uN` ↔ `NonZero<{i,u}N>` (`I###N###`, `U###N###`) | `fixed::{i8,…,i128, u8,…,u128}` |
| Cross-crate iso `Fixed{I,U}<U0> ↔ {i,u}{N}` (`Q000I###`, `Q000U###`) | `fixed::{i8,…,i128, u8,…,u128}` |
| Float `f64 ↔ f32 ↔ f16` under N5 | `float` (`f16` cargo feature for f16) |
| `time` crate types (`DATEJDAY`, `TIMENANO`, `TIMESECS`, `DURNSECS`, `F032DURN`, `F064DURN`, `PDTMDATE`, `OFDTNANO`, `OFDTSECS`) and the `std::time::Duration` family (`STDRU064`, `STDRU128`, `F064STDR`, `F032STDR`) for users on `std::time` | `time` |
| `std::net` addresses (`U032IPV4`, `U128IPV6`, `IPV6IPV4`, `IPVXIPV4`, `IPVXIPV6`, `SOVXSOV4`, `SOVXSOV6`) | `addr` |
| `char` codepoint projection (`U032CHAR`, surrogate-gap-aware) | `char` |

Constant-name prefixes are letter-disambiguated: `Q` for Q-format
wrappers (sign and host bit-width come from the module path), `I`/`U`
for std primitives (digits = bit-width), `N` for `NonZero<*>`, `F` for
IEEE floats. Cross-module name collisions are allowed and resolved by
qualified import (e.g. `fixed::i8::Q008Q000` and
`fixed::i64::Q008Q000` co-exist).

