# Examples

## Example 1

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
const ORDRBOOL: Conn<Ordering, bool> = Conn::new_l(ceil, inner);

assert_eq!(ORDRBOOL.ceil(Ordering::Less),    false);
assert_eq!(ORDRBOOL.ceil(Ordering::Greater), true);
assert_eq!(ORDRBOOL.upper(false),            Ordering::Less);
assert_eq!(ORDRBOOL.upper(true),             Ordering::Greater);
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

## Example 2

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
const BOOLORDR: Conn<bool, Ordering> = Conn::new_l(ceil, inner);

assert_eq!(BOOLORDR.ceil(false),              Ordering::Less);
assert_eq!(BOOLORDR.ceil(true),               Ordering::Greater);
assert_eq!(BOOLORDR.upper(Ordering::Less),    false);
assert_eq!(BOOLORDR.upper(Ordering::Equal),   false);
assert_eq!(BOOLORDR.upper(Ordering::Greater), true);
```

For one-sided Conns this crate ships the `conn_l!` / `conn_r!`
declaration-form macros — they bottom out at `Conn::new_l` /
`Conn::new_r` but use named-field syntax that matches `conn_k!` /
`iso!` and removes the `(ceil, inner)` vs. `(inner, floor)`
positional-argument footgun. The const above can be written:

```rust,ignore
conn_l! {
    pub BOOLORDR : bool => Ordering {
        ceil:  ceil,
        inner: inner,
    }
}
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
enables lawful `ceil`, `floor`, `round`, and `truncate` on
arbitrary `Conn`s.

## Example 3

A small change to Example 1 — supplying both the upper and lower
adjoints on the L side — packs the whole chain into a single value:

```rust
use connections::conn::{ConnL, ConnR};
use connections::conn_k;
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

// Adjoint triples are unit-struct markers implementing ConnL + ConnR.
conn_k! { pub ORDRBOOL : Ordering => bool { ceil: ceil, inner: inner, floor: floor } }

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
fns wired through `ConnL` and `ConnR` impls, with `MARKER.conn_l()` /
`MARKER.conn_r()` projecting to the L-view and R-view `Conn`s respectively.
The default-method dispatch on `ConnL` / `ConnR` lets you call
`.ceil()` / `.floor()` on the marker directly when both traits are
in scope.

(`conn_k!` only ships a *true* adjoint triple — many natural cast
families don't admit one. See [*Why one-sided?*](#why-one-sided) above
for the necessary and sufficient condition.)

## Example 4

Integer widening through `Extended<T>` (so values *outside* the source
range have somewhere to land — `ceil` saturates infinities to "one
past the source" sentinels in the target, `inner` rounds back to the
nearest in-range source value or out to a synthetic infinity):

```rust
use connections::conn::ConnL;
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
assert_eq!(U008I016.upper(256_i16),  Extended::PosInf);
assert_eq!(U008I016.upper(i16::MAX), Extended::PosInf);
```

This Conn ships as `ConnL` (left-Galois only) — its `inner` is
non-injective on `[256, i16::MAX]` (the entire above-source plateau
collapses to `Extended::PosInf`), so it can't be a true adjoint
triple. See *Why one-sided?* below for the math.

## Example 5

Saturating an unsigned width-equal cast — the motivating use case
behind a real-world unix PID. `std::process::id()` returns a `u32`,
but `libc::pid_t = i32`, so a naïve `pid_u32 as i32` cast wraps for
any `u32 > i32::MAX` — silently turning a sentinel-shaped value
into a negative PID. `U032I032.floor` saturates to `i32::MAX`
instead, preserving the R-Galois `inner ⊣ floor` law:

```rust
use connections::conn::ConnR;
use connections::fixed::i32::U032I032;

// Mid-range u32 PIDs that fit in i32 pass through.
assert_eq!(U032I032.floor(1_u32),               1_i32);
assert_eq!(U032I032.floor(i32::MAX as u32),     i32::MAX);

// Anything above i32::MAX saturates — never wraps to negative.
assert_eq!(U032I032.floor((i32::MAX as u32) + 1), i32::MAX);
assert_eq!(U032I032.floor(u32::MAX),              i32::MAX);

// Round-trip: i32 → u32 saturates negatives to 0 (the largest
// u32 satisfying inner(b) ≤ a for any a < 0).
assert_eq!(U032I032.lower(-1),       0_u32);
assert_eq!(U032I032.lower(0),        0_u32);
assert_eq!(U032I032.lower(i32::MAX), i32::MAX as u32);
```

## Example 6

`Conn` API — accessors and lifters operating on any `Conn`:

```rust
use connections::conn::{ConnL, ConnR};
use connections::fixed::i16::U008I016;
use connections::extended::Extended;

// The blanket `impl ConnL for Conn<A, B, L>` means `marker.ceil(x)`
// (the trait method via default-method dispatch) and
// `marker.conn_l().ceil(x)` (explicit projection then inherent
// method on the value) produce the same result.
assert_eq!(
    U008I016.ceil(Extended::Finite(200_u8)),
    U008I016.conn_l().ceil(Extended::Finite(200_u8)),
);

// `upper1` lifts an endofunction over the target type back to the source:
//   upper1(c, f, a) = upper(f(ceil(a)))
let bumped = U008I016.conn_l().upper1(|n| n, Extended::Finite(200_u8));
assert_eq!(
    bumped,
    U008I016.conn_l().upper(U008I016.conn_l().ceil(Extended::Finite(200_u8))),
);
```

(`U008I016` here is `ConnL`, not a triple — the `::L` projection is
implicit. See [*Why one-sided?*](#why-one-sided) above for why most
integer-widening casts of this shape can't ship as a triple.)

## Example 7

A sub-second `Duration` bracketed via the `time`-crate ladder (the same
code block is mirrored verbatim into the `time` module-level
rustdoc, so `cargo test --doc` keeps the two in sync):

```rust
use connections::conn::{ConnL, ConnR};
use connections::time::DURNSECS;
use connections::extended::Extended;
use time::Duration;

let half = Duration::seconds(5) + Duration::nanoseconds(1);
assert_eq!(DURNSECS.ceil(half),  Extended::Finite(6));
assert_eq!(DURNSECS.floor(half), Extended::Finite(5));
assert_eq!(DURNSECS.upper(Extended::Finite(42)), Duration::seconds(42));
```

## Example 8

Round-tripping a unix-timestamp through `OffsetDateTime`:

```rust
use connections::time::OFDTNANO;
use connections::extended::Extended;
use time::OffsetDateTime;

// OFDTNANO is a one-sided ConnL; the L-side methods are inherent.
assert_eq!(OFDTNANO.upper(0), Extended::Finite(OffsetDateTime::UNIX_EPOCH));
assert_eq!(OFDTNANO.ceil(Extended::Finite(OffsetDateTime::UNIX_EPOCH)), 0);
```

## Example 9

Rounding an IEEE-float number of seconds up to a `Duration`:

```rust
use connections::conn::ConnL;
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

## Example 10

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
assert!(F064F016.upper(pi_down) <= pi);
assert!(pi <= F064F016.upper(pi_up));

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
