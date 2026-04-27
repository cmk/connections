//! `ExtendedFloat<T>` extends an IEEE float type with synthetic `Bot` and
//! `Top` elements outside the float range, recovering the N5 lattice
//! structure the Galois-connection machinery requires.
//!
//! Rust's built-in float `PartialOrd` is a partial order: NaN is
//! incomparable with every value including itself, and there are no
//! canonical top/bottom elements. `ExtendedFloat` addresses both:
//!
//! - `Bot ≤ x` and `x ≤ Top` for every `x` (including `NaN`, `±∞`).
//! - `Finite(NaN)` is reflexive: `Finite(NaN) == Finite(NaN)` and
//!   `Finite(NaN).partial_cmp(&Finite(NaN)) == Some(Equal)`.
//! - `Finite(NaN)` remains incomparable with every other `Finite(_)`
//!   value (including `±∞`) — that comparison returns `None`.
//!
//! The N5 lattice (`-∞ ≤ NaN ≤ +∞`, NaN incomparable with finites) is
//! obtained from this shape: the synthetic `Bot` / `Top` form the
//! lattice's bottom/top; NaN's reflexivity closes the preorder; its
//! incomparability with finites is inherited unchanged from
//! `PartialOrd` on the wrapped `T`.
//!
//! This module also defines the connections between bare float types
//! (`f64 ↔ f32`). Connections involving `ExtendedFloat` wrappers will be
//! added when the design.md §"Connections involving floats" is
//! implemented; for now, the wrapper type lives here alongside the
//! bare-float connections, ready to be used.

use crate::conn::Conn;
use crate::lattice::Ple;
use std::cmp::Ordering;

#[derive(Copy, Clone, Debug)]
pub enum ExtendedFloat<T> {
    Bot,
    Finite(T),
    Top,
}

macro_rules! impl_float_ext {
    ($T:ty) => {
        impl PartialEq for ExtendedFloat<$T> {
            fn eq(&self, other: &Self) -> bool {
                use ExtendedFloat::*;
                match (self, other) {
                    (Bot, Bot) | (Top, Top) => true,
                    (Finite(a), Finite(b)) => {
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

        impl PartialOrd for ExtendedFloat<$T> {
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                use ExtendedFloat::*;
                match (self, other) {
                    (Bot, Bot) | (Top, Top) => Some(Ordering::Equal),
                    (Bot, _) => Some(Ordering::Less),
                    (_, Bot) => Some(Ordering::Greater),
                    (_, Top) => Some(Ordering::Less),
                    (Top, _) => Some(Ordering::Greater),
                    (Finite(a), Finite(b)) => {
                        if a.is_nan() && b.is_nan() {
                            Some(Ordering::Equal)
                        } else {
                            a.partial_cmp(b)
                        }
                    }
                }
            }
        }

        // The `PartialEq` above is reflexive (`Finite(NaN) == Finite(NaN)`
        // is true), so `Eq`'s contract is satisfied. Adding the marker
        // lets `ExtendedFloat<$T>` flow through any `T: Eq + PartialOrd`
        // bound — which is the lawful framework the Galois-connection
        // laws use.
        impl Eq for ExtendedFloat<$T> {}
    };
}

impl_float_ext!(f32);
impl_float_ext!(f64);

/// Connection between `f64` and `f32` under the N5 lattice ordering.
///
/// - `inner`: lossless `f32 → f64` embedding
/// - `ceil`: smallest `f32` whose `f64` embedding is ≥ the input (round up)
/// - `floor`: largest `f32` whose `f64` embedding is ≤ the input (round down)
pub fn f64_f32() -> Conn<f64, f32> {
    Conn::new(ceil_f64_f32, inner_f64_f32, floor_f64_f32)
}

fn inner_f64_f32(y: f32) -> f64 {
    y as f64
}

fn ceil_f64_f32(x: f64) -> f32 {
    if x.is_nan() {
        return f32::NAN;
    }

    let est = x as f32;
    let est_up = est as f64;

    if est_up.ple(&x) && x.ple(&est_up) {
        return est;
    }

    if x.ple(&est_up) {
        descend_to_ceil(est, x)
    } else {
        ascend_to_ceil(est, x)
    }
}

fn floor_f64_f32(x: f64) -> f32 {
    if x.is_nan() {
        return f32::NAN;
    }

    let est = x as f32;
    let est_up = est as f64;

    if est_up.ple(&x) && x.ple(&est_up) {
        return est;
    }

    if est_up.ple(&x) {
        ascend_to_floor(est, x)
    } else {
        descend_to_floor(est, x)
    }
}

// NOTE: The four walk functions below are not O(1). IEEE 754 round-to-nearest
// guarantees the `as f32` estimate is within a small number of ULPs of the true
// answer, so in practice these loops execute 0–2 times for f64→f32. A future
// optimization could replace each loop with a bounded unroll (the exact ULP
// bound depends on the precision gap between source and target types). The
// proptest suite will verify correctness of any such refactor.

/// Walk up (toward +∞) until `inner(z) >= x`, return that z.
fn ascend_to_ceil(start: f32, x: f64) -> f32 {
    let mut z = start;
    loop {
        let next = shift32(1, z);
        if next.ple(&z) {
            return z;
        }
        z = next;
        if x.ple(&(z as f64)) {
            return z;
        }
    }
}

/// Walk down (toward -∞) while `inner(z) >= x` still holds, return the last valid z.
fn descend_to_ceil(start: f32, x: f64) -> f32 {
    let mut z = start;
    loop {
        let next = shift32(-1, z);
        if z.ple(&next) {
            return z;
        }
        let next_up = next as f64;
        if !x.ple(&next_up) {
            return z;
        }
        z = next;
    }
}

/// Walk down (toward -∞) until `inner(z) <= x`, return that z.
fn descend_to_floor(start: f32, x: f64) -> f32 {
    let mut z = start;
    loop {
        let next = shift32(-1, z);
        if z.ple(&next) {
            return z;
        }
        z = next;
        if (z as f64).ple(&x) {
            return z;
        }
    }
}

/// Walk up (toward +∞) while `inner(z) <= x` still holds, return the last valid z.
fn ascend_to_floor(start: f32, x: f64) -> f32 {
    let mut z = start;
    loop {
        let next = shift32(1, z);
        if next.ple(&z) {
            return z;
        }
        let next_up = next as f64;
        if !next_up.ple(&x) {
            return z;
        }
        z = next;
    }
}

// ── ULP machinery ──────────────────────────────────────────────────

/// Shift a float by `n` ULPs (units of least precision) in the
/// sign-magnitude total order.
///
/// NaN maps to +∞ for positive shifts and -∞ for negative shifts.
/// ±∞ are clamped (shifting past ±∞ stays at ±∞).
fn shift32(n: i32, x: f32) -> f32 {
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::property::arb::{arb_f32, arb_f64};
    use crate::property::laws;
    use proptest::prelude::*;

    // ── Helpers ────────────────────────────────────────────────────

    fn conn() -> Conn<f64, f32> {
        f64_f32()
    }

    // ── ULP sanity ─────────────────────────────────────────────────

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

    // ── Spot checks ────────────────────────────────────────────────

    #[test]
    fn ceil_exact_value() {
        let c = conn();
        assert_eq!(c.ceil(0.5_f64), 0.5_f32);
    }

    #[test]
    fn floor_exact_value() {
        let c = conn();
        assert_eq!(c.floor(0.5_f64), 0.5_f32);
    }

    #[test]
    fn ceil_nan() {
        assert!(conn().ceil(f64::NAN).is_nan());
    }

    #[test]
    fn floor_nan() {
        assert!(conn().floor(f64::NAN).is_nan());
    }

    #[test]
    fn inner_nan() {
        assert!(conn().inner(f32::NAN).is_nan());
    }

    #[test]
    fn ceil_ge_floor() {
        let c = conn();
        let x = std::f64::consts::PI;
        assert!(c.floor(x).ple(&c.ceil(x)));
    }

    // ── Property tests ─────────────────────────────────────────────

    proptest! {
        #[test]
        fn galois_l(a in arb_f64(), b in arb_f32()) {
            prop_assert!(laws::conn_galois_l(&conn(), a, b));
        }

        #[test]
        fn galois_r(a in arb_f64(), b in arb_f32()) {
            prop_assert!(laws::conn_galois_r(&conn(), a, b));
        }

        #[test]
        fn closure_l(a in arb_f64()) {
            prop_assert!(laws::conn_closure_l(&conn(), a));
        }

        #[test]
        fn closure_r(a in arb_f64()) {
            prop_assert!(laws::conn_closure_r(&conn(), a));
        }

        #[test]
        fn kernel_l(b in arb_f32()) {
            prop_assert!(laws::conn_kernel_l(&conn(), b));
        }

        #[test]
        fn kernel_r(b in arb_f32()) {
            prop_assert!(laws::conn_kernel_r(&conn(), b));
        }

        #[test]
        fn monotone_l(a1 in arb_f64(), a2 in arb_f64()) {
            prop_assert!(laws::conn_monotone_l(&conn(), a1, a2));
        }

        #[test]
        fn monotone_r(b1 in arb_f32(), b2 in arb_f32()) {
            prop_assert!(laws::conn_monotone_r(&conn(), b1, b2));
        }

        #[test]
        fn idempotent(a in arb_f64()) {
            prop_assert!(laws::conn_idempotent(&conn(), a));
        }
    }

    // ── ExtendedFloat tests (folded in from former src/float_ext.rs) ────

    #[test]
    fn bot_below_everything_f64() {
        assert!(ExtendedFloat::<f64>::Bot < ExtendedFloat::Finite(0.0));
        assert!(ExtendedFloat::<f64>::Bot < ExtendedFloat::Finite(f64::NEG_INFINITY));
        assert!(ExtendedFloat::<f64>::Bot < ExtendedFloat::Finite(f64::NAN));
        assert!(ExtendedFloat::<f64>::Bot < ExtendedFloat::<f64>::Top);
    }

    #[test]
    fn top_above_everything_f64() {
        assert!(ExtendedFloat::Finite(0.0_f64) < ExtendedFloat::<f64>::Top);
        assert!(ExtendedFloat::Finite(f64::INFINITY) < ExtendedFloat::<f64>::Top);
        assert!(ExtendedFloat::Finite(f64::NAN) < ExtendedFloat::<f64>::Top);
    }

    #[test]
    fn nan_reflexive_f64() {
        let n: ExtendedFloat<f64> = ExtendedFloat::Finite(f64::NAN);
        assert_eq!(n, ExtendedFloat::Finite(f64::NAN));
        assert_eq!(
            n.partial_cmp(&ExtendedFloat::Finite(f64::NAN)),
            Some(Ordering::Equal)
        );
    }

    #[test]
    fn nan_incomparable_with_finite_f64() {
        let n: ExtendedFloat<f64> = ExtendedFloat::Finite(f64::NAN);
        assert!(n.partial_cmp(&ExtendedFloat::Finite(1.0)).is_none());
        assert!(ExtendedFloat::Finite(1.0_f64).partial_cmp(&n).is_none());
    }

    #[test]
    fn nan_incomparable_with_infinity_f64() {
        let n: ExtendedFloat<f64> = ExtendedFloat::Finite(f64::NAN);
        let i: ExtendedFloat<f64> = ExtendedFloat::Finite(f64::INFINITY);
        assert!(n.partial_cmp(&i).is_none());
        assert!(i.partial_cmp(&n).is_none());
    }

    #[test]
    fn standard_order_preserved_f64() {
        assert!(ExtendedFloat::Finite(1.0_f64) < ExtendedFloat::Finite(2.0));
        assert!(ExtendedFloat::Finite(f64::NEG_INFINITY) < ExtendedFloat::Finite(0.0_f64));
        assert!(ExtendedFloat::Finite(0.0_f64) < ExtendedFloat::Finite(f64::INFINITY));
    }

    #[test]
    fn f32_same_shape() {
        let n: ExtendedFloat<f32> = ExtendedFloat::Finite(f32::NAN);
        assert_eq!(n, ExtendedFloat::Finite(f32::NAN));
        assert!(ExtendedFloat::<f32>::Bot < n);
        assert!(n < ExtendedFloat::<f32>::Top);
        assert!(n.partial_cmp(&ExtendedFloat::Finite(1.0_f32)).is_none());
    }
}
