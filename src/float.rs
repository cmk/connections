//! `ExtendedFloat<T>` extends an IEEE float type with synthetic `Bot` and
//! `Top` elements outside the float range, recovering the N5 lattice
//! structure the Galois-connection machinery requires.
//!
//! Rust's built-in float `PartialOrd` is a partial order: NaN is
//! incomparable with every value including itself, and there are no
//! canonical top/bottom elements. `ExtendedFloat` addresses both:
//!
//! - `Bot ≤ x` and `x ≤ Top` for every `x` (including `NaN`, `±∞`).
//! - `Extend(NaN)` is reflexive: `Extend(NaN) == Extend(NaN)` and
//!   `Extend(NaN).partial_cmp(&Extend(NaN)) == Some(Equal)`.
//! - `Extend(NaN)` remains incomparable with every other `Extend(_)`
//!   value (including `±∞`) — that comparison returns `None`.
//!
//! The N5 lattice (`-∞ ≤ NaN ≤ +∞`, NaN incomparable with finites) is
//! obtained from this shape: the synthetic `Bot` / `Top` form the
//! lattice's bottom/top; NaN's reflexivity closes the preorder; its
//! incomparability with finites is inherited unchanged from
//! `PartialOrd` on the wrapped `T`.
//!
//! Per-destination-tier Conns live in submodules (right-hand side
//! wins under the placement rule when both endpoints sit at the same
//! specificity tier — see CLAUDE.md § Conn placement):
//!
//! - [`mod@f32`] — Conns whose target is `ExtendedFloat<f32>`
//!   (`F064F032`).
//! - `f16` — Conns whose target is `ExtendedFloat<f16>`
//!   (`F032F016`, `F064F016`) along with the `F016` type alias
//!   and 16-bit ULP machinery. Gated on the `f16` cargo feature
//!   (nightly required); the module name resolves only when the
//!   feature is enabled.

#[cfg(feature = "f16")]
pub mod f16;
pub mod f32;

use std::ops::{Add, Div, Sub};

/// Three-element extension of a (possibly partial) order:
/// `Bot < Extend(_) < Top`.
///
/// The wrapped variant is named `Extend`, not `Finite`, because for
/// IEEE floats the wrapped value can be `NaN` or `±∞` — neither of
/// which is finite. The variant name reflects the lattice-theoretic
/// role (the *extension* slot between `Bot` and `Top`), not a numeric
/// property of the inhabitant. Sister type [`crate::extended::Extended`]
/// keeps `Finite` since its wrapped values really are finite.
#[derive(Copy, Clone, Debug)]
pub enum ExtendedFloat<T> {
    Bot,
    Extend(T),
    Top,
}

macro_rules! impl_float_ext {
    ($T:ty) => {
        impl PartialEq for $crate::float::ExtendedFloat<$T> {
            fn eq(&self, other: &Self) -> bool {
                use $crate::float::ExtendedFloat::*;
                match (self, other) {
                    (Bot, Bot) | (Top, Top) => true,
                    (Extend(a), Extend(b)) => {
                        if a.is_nan() && b.is_nan() {
                            true
                        } else {
                            a == b
                        }
                    }
                    _ => false,
                }
            }
        }

        impl PartialOrd for $crate::float::ExtendedFloat<$T> {
            fn partial_cmp(&self, other: &Self) -> Option<::core::cmp::Ordering> {
                use $crate::float::ExtendedFloat::*;
                match (self, other) {
                    (Bot, Bot) | (Top, Top) => Some(::core::cmp::Ordering::Equal),
                    (Bot, _) => Some(::core::cmp::Ordering::Less),
                    (_, Bot) => Some(::core::cmp::Ordering::Greater),
                    (_, Top) => Some(::core::cmp::Ordering::Less),
                    (Top, _) => Some(::core::cmp::Ordering::Greater),
                    (Extend(a), Extend(b)) => {
                        if a.is_nan() && b.is_nan() {
                            Some(::core::cmp::Ordering::Equal)
                        } else {
                            a.partial_cmp(b)
                        }
                    }
                }
            }
        }

        // The `PartialEq` above is reflexive (`Extend(NaN) == Extend(NaN)`
        // is true), so `Eq`'s contract is satisfied. Adding the marker
        // lets `ExtendedFloat<$T>` flow through any `T: Eq + PartialOrd`
        // bound — which is the lawful framework the Galois-connection
        // laws use.
        impl Eq for $crate::float::ExtendedFloat<$T> {}
    };
}

pub(crate) use impl_float_ext;

impl_float_ext!(f32);
impl_float_ext!(f64);

// ── Numeric impls: minimal surface for `crate::conn` chain
//    combinators (`interval`, `midpoint`, `round`, `truncate`).
//
// These exist *solely* to thread `ExtendedFloat<T>` through the
// arithmetic those helpers do (`hi - lo`, `lo + diff/2`,
// `x >= A::from(0)`). They are **not** a general-purpose numeric
// algebra: `Mul`, `Neg`, `Rem`, `AddAssign`, etc. are deliberately
// omitted. Implemented only for `f32` / `f64` because the chain
// combinators are exercised on those source types in-tree.
// A `half::f16` version can be added later if a caller needs it
// (it requires routing `From<u8>` through `as f16`).
//
// Edge-case semantics for Bot/Top operands. The chain combinators
// pass `(c.inner ∘ c.ceil)(x)` and `(c.inner ∘ c.floor)(x)` to the
// arithmetic, which on a finite `Extend(_)` input always yields
// `Extend(_)` brackets — so the chain-combinator path never reaches
// the Bot/Top arms in practice. The deterministic Bot/Top tests in
// `mod tests` below pin the documented semantics for direct callers
// who do reach them.
//
// | Op | (Bot, Bot)  | (Top, Top)  | mixed Bot/Top   | endpoint, Extend(_) | (Extend(a), Extend(b)) |
// |----|-------------|-------------|-----------------|---------------------|------------------------|
// |  + |  Bot        |  Top        |  Extend(NaN)    |  endpoint absorbs   |  Extend(a + b)         |
// |  - |  Extend(NaN)|  Extend(NaN)|  endpoint of LHS|  endpoint of LHS;   |  Extend(a - b)         |
// |    |             |             |                 |  flipped for Extend |                        |
// |  / |  Extend(NaN)|  Extend(NaN)|  Extend(NaN)    |  Extend(NaN)        |  Extend(a / b)         |
//
// `From<u8>(n)` always returns `Extend(T::from(n))`.

macro_rules! impl_float_arith {
    ($T:ty) => {
        impl Add for ExtendedFloat<$T> {
            type Output = Self;
            fn add(self, other: Self) -> Self {
                use ExtendedFloat::*;
                match (self, other) {
                    (Bot, Bot) => Bot,
                    (Top, Top) => Top,
                    (Bot, Top) | (Top, Bot) => Extend(<$T>::NAN),
                    (Bot, Extend(_)) | (Extend(_), Bot) => Bot,
                    (Top, Extend(_)) | (Extend(_), Top) => Top,
                    (Extend(a), Extend(b)) => Extend(a + b),
                }
            }
        }

        impl Sub for ExtendedFloat<$T> {
            type Output = Self;
            fn sub(self, other: Self) -> Self {
                use ExtendedFloat::*;
                match (self, other) {
                    (Bot, Bot) | (Top, Top) => Extend(<$T>::NAN),
                    (Bot, Top) => Bot,
                    (Top, Bot) => Top,
                    (Bot, Extend(_)) => Bot,
                    (Top, Extend(_)) => Top,
                    (Extend(_), Bot) => Top,
                    (Extend(_), Top) => Bot,
                    (Extend(a), Extend(b)) => Extend(a - b),
                }
            }
        }

        impl Div for ExtendedFloat<$T> {
            type Output = Self;
            fn div(self, other: Self) -> Self {
                use ExtendedFloat::*;
                match (self, other) {
                    (Extend(a), Extend(b)) => Extend(a / b),
                    _ => Extend(<$T>::NAN),
                }
            }
        }

        impl From<u8> for ExtendedFloat<$T> {
            fn from(n: u8) -> Self {
                ExtendedFloat::Extend(<$T>::from(n))
            }
        }
    };
}

impl_float_arith!(f32);
impl_float_arith!(f64);

/// IEEE binary32 wrapped under the N5 lattice.
pub type F032 = ExtendedFloat<f32>;

/// IEEE binary64 wrapped under the N5 lattice.
pub type F064 = ExtendedFloat<f64>;

// ── 32-bit ULP machinery ───────────────────────────────────────────

/// Shift a float by `n` ULPs (units of least precision) in the
/// sign-magnitude total order.
///
/// NaN maps to +∞ for positive shifts and -∞ for negative shifts.
/// ±∞ are clamped (shifting past ±∞ stays at ±∞).
pub(crate) fn shift32(n: i32, x: f32) -> f32 {
    if x.is_nan() {
        return match n.signum() {
            -1 => f32::NEG_INFINITY,
            1 => f32::INFINITY,
            _ => f32::NAN,
        };
    }
    let i = float_to_int32(x);
    int32_to_float(clamp32(i.saturating_add(n)))
}

/// Convert f32 to a sign-magnitude integer where the total order on
/// integers matches the total order on floats (excluding NaN).
///
/// Maps: -∞ → INT_MIN+1, -0 → -1, +0 → 0, +∞ → INT_MAX-1 (approx)
fn float_to_int32(x: f32) -> i32 {
    signed32(x.to_bits())
}

fn int32_to_float(i: i32) -> f32 {
    f32::from_bits(unsigned32(i))
}

/// Word32 (IEEE bit pattern) → sign-magnitude Int32.
///
/// Maps the float bit-space onto integers so that the integer order
/// matches the float total order (excluding NaN):
///   +0 → 0, +inf → 2139095040, -0 → -1, -inf → -2139095041
fn signed32(x: u32) -> i32 {
    if x < 0x80000000 {
        x as i32
    } else {
        // Haskell: fromIntegral (maxBound @Word32 - (x - 0x80000000))
        (u32::MAX - (x - 0x80000000)) as i32
    }
}

/// Sign-magnitude Int32 → Word32 (IEEE bit pattern).
fn unsigned32(x: i32) -> u32 {
    if x >= 0 {
        x as u32
    } else {
        // Haskell: 0x80000000 + (maxBound @Word32 - fromIntegral x)
        0x80000000u32.wrapping_add(u32::MAX - (x as u32))
    }
}

/// Clamp between the int representations of -∞ and +∞.
fn clamp32(x: i32) -> i32 {
    // f32::INFINITY.to_bits()  = 0x7F800000 → signed32 = 2139095040
    // f32::NEG_INFINITY bits   = 0xFF800000 → signed32 = -2139095041
    x.clamp(-2139095041, 2139095040)
}

/// Widen `f32` to `f64`. Used by [`def_walk_helpers!`] to give the
/// `F064F032` Conn a uniform `widen` shape (`as` casts can't be
/// passed as fn pointers, so we wrap in a free fn).
pub(crate) fn widen_f32_f64(x: f32) -> f64 {
    x as f64
}

/// Generate the four ULP-walk helpers (`ascend_to_ceil`,
/// `descend_to_ceil`, `ascend_to_floor`, `descend_to_floor`) for one
/// `Src → Dst` precision-narrowing Conn, packaged in a private
/// submodule named `$mod_name`.
///
/// Each helper returns `(Dst, u32)` — the corrected target value and
/// the number of ULP-shift iterations consumed. Production callers
/// throw the count away (`let (z, _) = …`); the `ulp_steps_bounded`
/// proptest reads it to assert the loop converges in ≤ 2 iterations.
///
/// Parameters:
/// - `$mod_name` — the private submodule wrapping this Conn's
///   helpers, e.g. `f064_f016_walks`.
/// - `$src` — the wider float type (`f32`, `f64`).
/// - `$dst` — the narrower float type (`f32`, or `f16` when the
///   `f16` cargo feature is enabled).
/// - `$shift` — a `fn(i32, $dst) -> $dst` that shifts `n` ULPs in
///   sign-magnitude total order.
/// - `$widen` — a `fn($dst) -> $src` that widens losslessly. Always
///   a free fn wrapper around `as` casts (since `as` casts can't be
///   passed as fn pointers).
///
/// The generated module's helpers are `pub(super)` — visible to the
/// owning Conn's `ceil`/`floor` functions and to `#[cfg(test)]` code
/// in the same parent file, but not exposed beyond.
macro_rules! def_walk_helpers {
    ($mod_name:ident, $src:ty, $dst:ty, $shift:path, $widen:path) => {
        mod $mod_name {
            #[allow(unused_imports)]
            use super::*;

            /// Walk up (toward +∞) until `widen(z) >= x`, returning `(z, steps)`.
            pub(super) fn ascend_to_ceil(start: $dst, x: $src) -> ($dst, u32) {
                let mut z = start;
                let mut steps = 0;
                loop {
                    let next = $shift(1, z);
                    if next <= z {
                        return (z, steps);
                    }
                    steps += 1;
                    z = next;
                    if x <= $widen(z) {
                        return (z, steps);
                    }
                }
            }

            /// Walk down (toward -∞) while `widen(z) >= x` still holds.
            pub(super) fn descend_to_ceil(start: $dst, x: $src) -> ($dst, u32) {
                let mut z = start;
                let mut steps = 0;
                loop {
                    let next = $shift(-1, z);
                    if z <= next {
                        return (z, steps);
                    }
                    let next_up = $widen(next);
                    // Inputs are non-NaN by construction, so `>` is
                    // equivalent to `!(x <= next_up)` here.
                    if x > next_up {
                        return (z, steps);
                    }
                    steps += 1;
                    z = next;
                }
            }

            /// Walk up (toward +∞) while `widen(z) <= x` still holds.
            pub(super) fn ascend_to_floor(start: $dst, x: $src) -> ($dst, u32) {
                let mut z = start;
                let mut steps = 0;
                loop {
                    let next = $shift(1, z);
                    if next <= z {
                        return (z, steps);
                    }
                    let next_up = $widen(next);
                    if next_up > x {
                        return (z, steps);
                    }
                    steps += 1;
                    z = next;
                }
            }

            /// Walk down (toward -∞) until `widen(z) <= x`.
            pub(super) fn descend_to_floor(start: $dst, x: $src) -> ($dst, u32) {
                let mut z = start;
                let mut steps = 0;
                loop {
                    let next = $shift(-1, z);
                    if z <= next {
                        return (z, steps);
                    }
                    steps += 1;
                    z = next;
                    if $widen(z) <= x {
                        return (z, steps);
                    }
                }
            }
        }
    };
}

pub(crate) use def_walk_helpers;

#[cfg(test)]
mod tests {
    use super::*;

    // ── 32-bit ULP sanity ──────────────────────────────────────────

    #[test]
    fn shift32_from_zero() {
        let z = shift32(1, 0.0);
        assert!(z > 0.0);
        assert_eq!(z, f32::from_bits(1));
    }

    #[test]
    fn shift32_nan_to_inf() {
        assert_eq!(shift32(1, f32::NAN), f32::INFINITY);
        assert_eq!(shift32(-1, f32::NAN), f32::NEG_INFINITY);
        assert!(shift32(0, f32::NAN).is_nan());
    }

    #[test]
    fn shift32_inf_clamped() {
        assert_eq!(shift32(1, f32::INFINITY), f32::INFINITY);
        assert_eq!(shift32(-1, f32::NEG_INFINITY), f32::NEG_INFINITY);
    }

    // ── ExtendedFloat tests ────────────────────────────────────────

    #[test]
    fn bot_below_everything_f64() {
        assert!(ExtendedFloat::<f64>::Bot < ExtendedFloat::Extend(0.0));
        assert!(ExtendedFloat::<f64>::Bot < ExtendedFloat::Extend(f64::NEG_INFINITY));
        assert!(ExtendedFloat::<f64>::Bot < ExtendedFloat::Extend(f64::NAN));
        assert!(ExtendedFloat::<f64>::Bot < ExtendedFloat::<f64>::Top);
    }

    #[test]
    fn top_above_everything_f64() {
        assert!(ExtendedFloat::Extend(0.0_f64) < ExtendedFloat::<f64>::Top);
        assert!(ExtendedFloat::Extend(f64::INFINITY) < ExtendedFloat::<f64>::Top);
        assert!(ExtendedFloat::Extend(f64::NAN) < ExtendedFloat::<f64>::Top);
    }

    #[test]
    fn nan_reflexive_f64() {
        let n: ExtendedFloat<f64> = ExtendedFloat::Extend(f64::NAN);
        assert_eq!(n, ExtendedFloat::Extend(f64::NAN));
        assert_eq!(
            n.partial_cmp(&ExtendedFloat::Extend(f64::NAN)),
            Some(core::cmp::Ordering::Equal)
        );
    }

    #[test]
    fn nan_incomparable_with_finite_f64() {
        let n: ExtendedFloat<f64> = ExtendedFloat::Extend(f64::NAN);
        assert!(n.partial_cmp(&ExtendedFloat::Extend(1.0)).is_none());
        assert!(ExtendedFloat::Extend(1.0_f64).partial_cmp(&n).is_none());
    }

    #[test]
    fn nan_incomparable_with_infinity_f64() {
        let n: ExtendedFloat<f64> = ExtendedFloat::Extend(f64::NAN);
        let i: ExtendedFloat<f64> = ExtendedFloat::Extend(f64::INFINITY);
        assert!(n.partial_cmp(&i).is_none());
        assert!(i.partial_cmp(&n).is_none());
    }

    #[test]
    fn standard_order_preserved_f64() {
        assert!(ExtendedFloat::Extend(1.0_f64) < ExtendedFloat::Extend(2.0));
        assert!(ExtendedFloat::Extend(f64::NEG_INFINITY) < ExtendedFloat::Extend(0.0_f64));
        assert!(ExtendedFloat::Extend(0.0_f64) < ExtendedFloat::Extend(f64::INFINITY));
    }

    #[test]
    fn f32_same_shape() {
        let n: ExtendedFloat<f32> = ExtendedFloat::Extend(f32::NAN);
        assert_eq!(n, ExtendedFloat::Extend(f32::NAN));
        assert!(ExtendedFloat::<f32>::Bot < n);
        assert!(n < ExtendedFloat::<f32>::Top);
        assert!(n.partial_cmp(&ExtendedFloat::Extend(1.0_f32)).is_none());
    }

    // ── Numeric impls for ExtendedFloat<f32 | f64> ────────────────

    #[test]
    fn add_extends_passes_through_f64() {
        let a: ExtendedFloat<f64> = ExtendedFloat::Extend(1.5);
        let b: ExtendedFloat<f64> = ExtendedFloat::Extend(2.25);
        assert_eq!(a + b, ExtendedFloat::Extend(3.75));
    }

    #[test]
    fn sub_zero_is_id_f64() {
        let a: ExtendedFloat<f64> = ExtendedFloat::Extend(std::f64::consts::PI);
        let zero: ExtendedFloat<f64> = ExtendedFloat::from(0u8);
        assert_eq!(a - zero, a);
    }

    #[test]
    fn div_by_two_halves_f64() {
        let a: ExtendedFloat<f64> = ExtendedFloat::Extend(8.0);
        let two: ExtendedFloat<f64> = ExtendedFloat::from(2u8);
        assert_eq!(a / two, ExtendedFloat::Extend(4.0));
    }

    #[test]
    fn from_u8_round_trips_f32_f64() {
        for n in [0u8, 1, 2, 7, 42, u8::MAX] {
            assert_eq!(
                ExtendedFloat::<f64>::from(n),
                ExtendedFloat::Extend(n as f64)
            );
            assert_eq!(
                ExtendedFloat::<f32>::from(n),
                ExtendedFloat::Extend(n as f32)
            );
        }
    }

    #[test]
    fn add_endpoints_absorb() {
        let bot: ExtendedFloat<f64> = ExtendedFloat::Bot;
        let top: ExtendedFloat<f64> = ExtendedFloat::Top;
        let one: ExtendedFloat<f64> = ExtendedFloat::Extend(1.0);
        assert_eq!(bot + one, ExtendedFloat::Bot);
        assert_eq!(top + one, ExtendedFloat::Top);
        assert_eq!(bot + bot, ExtendedFloat::Bot);
        assert_eq!(top + top, ExtendedFloat::Top);
        // Mixed Bot/Top is undefined → NaN payload.
        match bot + top {
            ExtendedFloat::Extend(v) => assert!(v.is_nan()),
            other => panic!("expected Extend(NaN), got {other:?}"),
        }
    }

    #[test]
    fn sub_extends_passes_through_f64() {
        let a: ExtendedFloat<f64> = ExtendedFloat::Extend(5.5);
        let b: ExtendedFloat<f64> = ExtendedFloat::Extend(1.25);
        assert_eq!(a - b, ExtendedFloat::Extend(4.25));
    }
}
