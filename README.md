# connections

[![CI](https://gitlab.com/cmk/connections/badges/main/pipeline.svg)](https://gitlab.com/cmk/connections/-/pipelines)

Read the docs [here](https://cmk.gitlab.io/connections/).

Galois connections as first-class Rust values. Use them to cast lawfully
between numeric types, expose ceiling/floor/inner alongside each other on
the same value, and compose ladders of conversions whose round-trip
behavior is property-tested rather than left to chance.

**MSRV: Rust 1.85.** Bumps to the MSRV will be treated as minor-version
changes — pin `connections = "0.1"` and an MSRV upgrade will surface as
a 0.2 release rather than a silent break on a patch update.

## Why this crate

The standard cast operators `as`, `From`, and `Into` give you exactly one
direction at a time — and `as` in particular is silent on rounding,
saturation, and lossy conversion. Three concrete things this crate gives
you that the standard tools don't:

1. **Both arms of a cast on one value.** An adjoint-triple marker
   exposes `ceil: A → B`, `floor: A → B`, *and* the embedding
   `inner: B → A` as a unit struct with `ViewL` / `ViewR` impls — you
   don't pick "ceiling cast" vs "floor cast" up front, you carry the
   marker and call whichever you need per-call. (One-sided
   connections — where only one law holds — ship as kind-tagged
   `ConnL<A, B>` / `ConnR<A, B>` values, exposing only the methods of
   their kind.)

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

## What are Galois connections?

A [Galois connection](https://en.wikipedia.org/wiki/Galois_connection)
between preorders A and B is a pair of monotone maps `f: A → B` and
`g: B → A` such that `f(x) ≤ y ⇔ x ≤ g(y)`. We say `f` is the *left*
or *lower* adjoint, and `g` is the *right* or *upper* adjoint of the
connection.

Drawn between two 3-element chains
(adapted from [7 Sketches](https://math.mit.edu/~dspivak/teaching/sp18/7Sketches.pdf)):

```text
A  ←  B
   g

3  ↔  3


2  ←  2
   ↰
   ↳
1  →  1

   f
A  →  B
```

Each row is a `(a, b)` pair; arrows show the action of `f` (A → B,
bottom legend) and `g` (B → A, top legend). Lone arrows mark
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

The basic type in this library is:

```text
pub struct Conn<A, B, K: Kind = L> {
    f: fn(A) -> B,   // L-kind: ceil; R-kind: floor
    g: fn(B) -> A,   // shared middle adjoint (embedding)
    // plus a phantom kind tag K ∈ {L, R}
}
```

A `Conn<A, B, K>` is exactly a Galois connection — a pair of monotone
functions `(f, g)` whose adjoint role depends on the kind tag. An
L-kind Conn satisfies `f(a) ≤ b ⟺ a ≤ g(b)`; an R-kind Conn
satisfies `g(b) ≤ a ⟺ b ≤ f(a)`.

[Adjoint triples](https://ncatlab.org/nlab/show/adjoint+triple) — the
`f ⊣ g ⊣ h` shape Example 3 below derives — are *not* a third kind
of `Conn`. They are zero-sized **marker types** implementing two
projection traits, `ViewL<A, B>` and `ViewR<A, B>`, whose associated
consts are the L-view and R-view `Conn`s of the triple. The "third
function" lives as a free function in module scope, referenced from
the marker's trait impls; no struct in the crate stores three fns.
Two-sided helpers (`round`, `truncate`, …) bind on the
`Triple<A, B>` super-trait and reach through both views.

The struct is `Copy`, `const`-constructible, heap-free, and the crate
is `#![forbid(unsafe_code)]`.

### Why one-sided?

A `Conn<A, B, K>` ships with exactly one direction: `ConnL` exposes
`.ceil()` (round up) and `.upper()` (embed); `ConnR` exposes `.floor()`
(round down) and `.lower()` (embed). To get **both** directions plus
the two-sided helpers (`round`, `truncate`, …) you ship a triple
marker. But there's a hard mathematical condition that decides whether
a (source, rung) pair admits a true triple at all:

> **The middle adjoint `inner` must be order-reflecting.**
> Equivalently, `floor(a) ≤ ceil(a)` must hold for every `a`.

Both directions of the equivalence are elementary applications of the
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
fully faithful ⟺ counit of `g ⊣ h` is iso ⟺ unit of `f ⊣ g` is iso
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
rounding sandwich isn't an academic foul; the two-sided helpers
actively misbehave on it.**

Where the underlying types make a true triple impossible (the
`STDRU128`-shaped saturation, the `ext_int!`-shaped Extended<>
collapse, the `fix_fix_*!`-shaped Q-format plateau) this crate ships
`ConnL` (or `ConnR`) instead. Calling `.floor()` on the demoted forms
is a compile error — explicit, not a wrong answer at runtime. The
`prop::conn::law_battery!` `full` subset enforces both
[`order_reflecting`] (the load-bearing predicate) and its corollary
[`floor_le_ceil`] so future triple markers can't silently re-introduce
the flaw — a violation aborts `cargo test`, not a downstream caller.

[`order_reflecting`]: https://docs.rs/connections/latest/connections/prop/conn/fn.order_reflecting.html
[`floor_le_ceil`]: https://docs.rs/connections/latest/connections/prop/conn/fn.floor_le_ceil.html

## Quick tour

**Connection Families:**

The crate's only top-level domain split is **`float/` vs `fixed/`**:
every IEEE-binary type lives in `float/`; everything finite-precision
with integer storage — `fixed`-crate Q-format wrappers, std-int
primitives (interpreted as Q*N*.0), and `core::num::NonZero<T>`
(punctured Q*N*.0) — lives in `fixed/`.

| Family | Module |
|--------|--------|
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

**Conn API**

- L-side methods on `Conn<_, _, L>` (and on any `ViewL` implementor
  via default-method dispatch): `ceiling`, `upper`, `ceiling1`/`2`,
  `upper1`/`2`. Back-compat aliases: `ceil` / `inner`.
- R-side methods on `Conn<_, _, R>` (and on any `ViewR` implementor):
  `floor`, `lower`, `floor1`/`2`, `lower1`/`2`. Back-compat alias for
  `lower`: `inner`.
- Two-sided helpers (re-exported at the crate root): `interval`,
  `midpoint`, `round`/`round1`/`round2`,
  `truncate`/`truncate1`/`truncate2`, `median`. All bind on
  `T: Triple<A, B>` (= `ViewL + ViewR`), so they're callable only on
  triple markers — not on one-sided Conns.

Kind discipline is structural: calling `.floor(...)` on an L-kind
Conn is a compile error (the method only exists on `Conn<_, _, R>`),
and likewise `.ceiling(...)` on R. Two-sided helpers similarly reject
one-sided operands at compile time because a one-sided `Conn` doesn't
implement `Triple`.

## Examples

### Example 1

Let's build the simplest possible connection in Rust — between
[`Ordering`](https://doc.rust-lang.org/core/cmp/enum.Ordering.html)
and `bool` — three different ways, each illustrating one more piece
of the structure that the unified `Conn<A, B>` type carries.

```rust
use connections::conn::{Conn, ConnL};
use std::cmp::Ordering;

fn ceil(o: Ordering) -> bool {
    !matches!(o, Ordering::Less)
}
fn inner(b: bool) -> Ordering {
    if b { Ordering::Greater } else { Ordering::Less }
}
const ORDRBOOL: ConnL<Ordering, bool> = Conn::new_l(ceil, inner);

assert_eq!(ORDRBOOL.ceil(Ordering::Less),    false);
assert_eq!(ORDRBOOL.ceil(Ordering::Greater), true);
assert_eq!(ORDRBOOL.inner(false),            Ordering::Less);
assert_eq!(ORDRBOOL.inner(true),             Ordering::Greater);
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

### Example 2

Notice that `inner` from Example 1 — the `bool → Ordering` function —
is itself *also* the lower adjoint of a different pair. Define a new
upper adjoint `h` going the other way:

```rust
use connections::conn::{Conn, ConnL};
use std::cmp::Ordering;

fn ceil(b: bool) -> Ordering {
    if b { Ordering::Greater } else { Ordering::Less }
}
fn inner(o: Ordering) -> bool {
    matches!(o, Ordering::Greater)
}
const BOOLORDR: ConnL<bool, Ordering> = Conn::new_l(ceil, inner);

assert_eq!(BOOLORDR.ceil(false),              Ordering::Less);
assert_eq!(BOOLORDR.ceil(true),               Ordering::Greater);
assert_eq!(BOOLORDR.inner(Ordering::Less),    false);
assert_eq!(BOOLORDR.inner(Ordering::Equal),   false);
assert_eq!(BOOLORDR.inner(Ordering::Greater), true);
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

### Example 3

A small change to Example 1 — supplying both the upper and lower
adjoints on the L side — packs the whole chain into a single value:

```rust
use connections::conn::{Conn, ConnL, ConnR, ViewL, ViewR};
use connections::triple;
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

// Adjoint triples are unit-struct markers implementing ViewL + ViewR.
triple! { pub ORDRBOOL : Ordering => bool { ceil: ceil, inner: inner, floor: floor } }

// `ceil` reads the L-pair (ceil ⊣ inner); `floor` reads the R-pair
// (inner ⊣ floor). They differ on `Equal`, where the bracket is open:
assert_eq!(ORDRBOOL.ceil(Ordering::Equal),  true);
assert_eq!(ORDRBOOL.floor(Ordering::Equal), false);
```

Each cell is now a triple: `ceil(x) ⋈ y` / `x ⋈ inner(y)` /
`floor(x) ⋈ y`. Columns 1–2 verify the `f ⊣ g` pair; columns 2–3
verify the `g ⊣ h` pair (with the appropriate reversal):

| ceil/inner/floor | `false`     | `true`      |
|------------------|-------------|-------------|
| `Less`           | `=`/`=`/`=` | `<`/`<`/`<` |
| `Equal`          | `>`/`>`/`=` | `=`/`<`/`<` |
| `Greater`        | `>`/`>`/`>` | `=`/`=`/`=` |

This is the shape an adjoint-triple **marker** carries: three free
fns wired through `ViewL` and `ViewR` impls, with `MARKER::L` /
`MARKER::R` projecting to the L-view and R-view `Conn`s respectively.
The default-method dispatch on `ViewL` / `ViewR` lets you call
`.ceiling()` / `.floor()` on the marker directly when both traits are
in scope.

(`triple!` only ships a *true* adjoint triple — many natural cast
families don't admit one. See [*Why one-sided?*](#why-one-sided) above
for the necessary and sufficient condition.)

### Example 4

Integer widening through `Extended<T>` (so values *outside* the source
range have somewhere to land — `ceil` saturates infinities to "one
past the source" sentinels in the target, `inner` rounds back to the
nearest in-range source value or out to a synthetic infinity):

```rust
use connections::conn::ViewL;
use connections::fixed::i16::U008I016;
use connections::extended::Extended;

// Finite passes through.
assert_eq!(U008I016.ceil(Extended::Finite(200_u8)), 200_i16);

// `ceil(NegInf)` saturates to the target's MIN; `ceil(PosInf)` lands
// on the "one past source" marker.
assert_eq!(U008I016.ceil(Extended::NegInf),  i16::MIN);
assert_eq!(U008I016.ceil(Extended::PosInf),  256_i16);   // u8::MAX + 1

// `inner` partitions the target: above-source rung values collapse
// to the synthetic PosInf source.
assert_eq!(U008I016.inner(256_i16),  Extended::PosInf);
assert_eq!(U008I016.inner(i16::MAX), Extended::PosInf);
```

This Conn ships as `ConnL` (left-Galois only) — its `inner` is
non-injective on `[256, i16::MAX]` (the entire above-source plateau
collapses to `Extended::PosInf`), so it can't be a true adjoint
triple. See *Why one-sided?* below for the math.

### Example 5

Saturating an unsigned width-equal cast — the motivating use case
behind a real-world unix PID. `std::process::id()` returns a `u32`,
but `libc::pid_t = i32`, so a naïve `pid_u32 as i32` cast wraps for
any `u32 > i32::MAX` — silently turning a sentinel-shaped value
into a negative PID. `U032I032.floor` saturates to `i32::MAX`
instead, preserving the R-Galois `inner ⊣ floor` law:

```rust
use connections::conn::ViewR;
use connections::fixed::i32::U032I032;

// Mid-range u32 PIDs that fit in i32 pass through.
assert_eq!(U032I032.floor(1_u32),               1_i32);
assert_eq!(U032I032.floor(i32::MAX as u32),     i32::MAX);

// Anything above i32::MAX saturates — never wraps to negative.
assert_eq!(U032I032.floor((i32::MAX as u32) + 1), i32::MAX);
assert_eq!(U032I032.floor(u32::MAX),              i32::MAX);

// Round-trip: i32 → u32 saturates negatives to 0 (the largest
// u32 satisfying inner(b) ≤ a for any a < 0).
assert_eq!(U032I032.inner(-1),       0_u32);
assert_eq!(U032I032.inner(0),        0_u32);
assert_eq!(U032I032.inner(i32::MAX), i32::MAX as u32);
```

### Example 6

`Conn` API — accessors and lifters operating on any `Conn`:

```rust
use connections::conn::{ViewL, ViewR};
use connections::fixed::i16::U008I016;
use connections::extended::Extended;

// `ceiling` is the named alias of `ceil` under the L-side reading.
// Triple markers route via U008I016::L (the L-view ConnL).
assert_eq!(
    U008I016::L.ceiling(Extended::Finite(200_u8)),
    U008I016::L.ceil(Extended::Finite(200_u8)),
);

// `upper1` lifts an endofunction over the target type back to the source:
//   upper1(c, f, a) = inner(f(ceil(a)))
let bumped = U008I016::L.upper1(|n| n, Extended::Finite(200_u8));
assert_eq!(
    bumped,
    U008I016::L.upper(U008I016::L.ceiling(Extended::Finite(200_u8))),
);
```

(`U008I016` here is `ConnL`, not a triple — the `::L` projection is
implicit. See [*Why one-sided?*](#why-one-sided) above for why most
integer-widening casts of this shape can't ship as a triple.)

### Example 7

A sub-second `Duration` bracketed via the `time`-crate ladder (the same
code block is mirrored verbatim into the `time` module-level
rustdoc, so `cargo test --doc` keeps the two in sync):

```rust
use connections::conn::{ViewL, ViewR};
use connections::time::DURNSECS;
use connections::extended::Extended;
use time::Duration;

let half = Duration::seconds(5) + Duration::nanoseconds(1);
assert_eq!(DURNSECS.ceil(half),  Extended::Finite(6));
assert_eq!(DURNSECS.floor(half), Extended::Finite(5));
assert_eq!(DURNSECS.inner(Extended::Finite(42)), Duration::seconds(42));
```

### Example 8

Round-tripping a unix-timestamp through `OffsetDateTime`:

```rust
use connections::time::OFDTNANO;
use connections::extended::Extended;
use time::OffsetDateTime;

// OFDTNANO is a one-sided ConnL; the L-side methods are inherent.
assert_eq!(OFDTNANO.inner(0), Extended::Finite(OffsetDateTime::UNIX_EPOCH));
assert_eq!(OFDTNANO.ceil(Extended::Finite(OffsetDateTime::UNIX_EPOCH)), 0);
```

### Example 9

Rounding an IEEE-float number of seconds up to a `Duration`:

```rust
use connections::conn::ViewL;
use connections::float::ExtendedFloat;
use connections::time::F064DURN;
use connections::extended::Extended;
use time::Duration;

let half_sec = ExtendedFloat::Extend(0.5_f64);
assert_eq!(F064DURN.ceil(half_sec), Extended::Finite(Duration::milliseconds(500)));

// f64 NaN: ceil → +∞ (forced by `Top > Extend(NaN) > Bot`).
let nan = ExtendedFloat::Extend(f64::NAN);
assert_eq!(F064DURN.ceil(nan), Extended::PosInf);
```

`F064DURN` is `ConnL` (left-Galois only) — `inner` collapses every f64
plateau (multiple `Duration`s map to the same `f64`) so it isn't
order-reflecting and no true triple exists. See *Why one-sided?* below.

### Example 10

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

## Relationship to the Haskell library

This crate is a port of the Haskell library
[`connections`](https://github.com/cmk/connections/) (same author, same
mathematical content, different ergonomic trade-offs). The faithful
parts:

- The `Conn` API
- The connection families (decimal/binary fixed-point, sample rates,
  integer widening, float pairs).
- The N5 ordering on float-bearing types via `ExtendedFloat<T>`.
- The lattice trait hierarchy (`Join`, `Meet`, `Heyting`, `Coheyting`,
  `Symmetric`, `Boolean`).

The deliberate divergences:

- One `Conn<A, B>` type instead of `Cast (k :: Side) a b`. Both
  L-side and R-side accessors are free functions on the unified type.
- Composition is a `compose!` macro over module-scope `const`s, not a
  generic `Category` instance. The trade-off is documented in
  [`doc/design.md`](doc/design.md) §"Composition".
- No `Preorder` class; `PartialOrd` + `ExtendedFloat` cover the cases
  that matter.
