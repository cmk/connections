//! Conns whose target is [`F016`] (`ExtendedFloat<f16>`) plus the
//! 16-bit ULP machinery they share.
//!
//! Houses [`F032F016`] (`ExtendedFloat<f32> → ExtendedFloat<f16>`)
//! and [`F064F016`] (`ExtendedFloat<f64> → ExtendedFloat<f16>`).
//!
//! The whole module is gated on the `f16` cargo feature (declared
//! `#[cfg(feature = "f16")] pub mod f16;` in the parent), which
//! requires nightly Rust because std `f16` is currently a
//! nightly-only primitive (`#![feature(f16)]`, tracking issue
//! #116909).

use super::{ExtendedFloat, F032, F064, def_walk_helpers, impl_float_ext};
use crate::conn::Conn;

impl_float_ext!(f16);

/// IEEE binary16 (half-precision) wrapped under the N5 lattice.
pub type F016 = ExtendedFloat<f16>;

// ── 16-bit ULP machinery ───────────────────────────────────────────

/// Word16 (sign-magnitude bit pattern) → sign-magnitude i32.
///
/// Maps the 16-bit float bit-space onto integers so that integer
/// order matches the float total order (excluding NaN):
///   +0 → 0, +inf-bits → small positive, -0 → -1, -inf-bits → large negative.
pub(crate) fn signed16(x: u16) -> i32 {
    if x < 0x8000 {
        x as i32
    } else {
        // Mirror signed32's Haskell-style mapping at 16-bit width.
        // u16::MAX - (x - 0x8000) maps the negative half symmetrically;
        // simpler equivalent: 0x7FFF - x as i32.
        0x7FFF_i32 - (x as i32)
    }
}

/// Sign-magnitude i32 → Word16 (bit pattern).
pub(crate) fn unsigned16(i: i32) -> u16 {
    if i >= 0 {
        i as u16
    } else {
        (0x7FFF_i32 - i) as u16
    }
}

/// Clamp between the i32 representations of f16's ±∞.
pub(crate) fn clamp16_f16(x: i32) -> i32 {
    // f16::INFINITY.to_bits() = 0x7C00 → signed16 = 31744
    // f16::NEG_INFINITY bits  = 0xFC00 → signed16 = -31745
    x.clamp(-31745, 31744)
}

/// Shift an `f16` by `n` ULPs in the sign-magnitude total order.
///
/// NaN maps to ±∞ for non-zero shifts (matches `shift32`); ±∞ are
/// clamped (shifting past stays at ±∞).
pub(crate) fn shift16_f16(n: i32, x: f16) -> f16 {
    if x.is_nan() {
        return match n.signum() {
            -1 => f16::NEG_INFINITY,
            1 => f16::INFINITY,
            _ => f16::NAN,
        };
    }
    let i = signed16(x.to_bits());
    f16::from_bits(unsigned16(clamp16_f16(i.saturating_add(n))))
}

/// Widen `f16` to `f32` via an `as` cast. Wrapped as a free fn so it
/// can be passed as a fn pointer to [`def_walk_helpers!`] (the macro
/// can't take an `as` cast directly).
pub(crate) fn widen_f16_f32(x: f16) -> f32 {
    x as f32
}

/// Widen `f16` to `f64` via an `as` cast. See [`widen_f16_f32`].
pub(crate) fn widen_f16_f64(x: f16) -> f64 {
    x as f64
}

def_walk_helpers!(f32_f16_walks, f32, f16, shift16_f16, widen_f16_f32);
def_walk_helpers!(f64_f16_walks, f64, f16, shift16_f16, widen_f16_f64);

// ── F032F016 ───────────────────────────────────────────────────────

fn f032f016_ceil(x: F032) -> F016 {
    match x {
        ExtendedFloat::Bot => ExtendedFloat::Bot,
        ExtendedFloat::Top => ExtendedFloat::Top,
        ExtendedFloat::Extend(v) => ExtendedFloat::Extend(ceil_f32_f16(v)),
    }
}
fn f032f016_inner(y: F016) -> F032 {
    match y {
        ExtendedFloat::Bot => ExtendedFloat::Bot,
        ExtendedFloat::Top => ExtendedFloat::Top,
        ExtendedFloat::Extend(v) => ExtendedFloat::Extend(v as f32),
    }
}
fn f032f016_floor(x: F032) -> F016 {
    match x {
        ExtendedFloat::Bot => ExtendedFloat::Bot,
        ExtendedFloat::Top => ExtendedFloat::Top,
        ExtendedFloat::Extend(v) => ExtendedFloat::Extend(floor_f32_f16(v)),
    }
}

crate::triple! {
    /// Connection between [`super::F032`] (`ExtendedFloat<f32>`) and
    /// [`F016`] (`ExtendedFloat<f16>`) under the N5 lattice.
    ///
    /// - `inner`: lossless `f16 → f32` widening (`Bot/Top/Extend` pass through;
    ///   `Extend(v)` performs `v as f32`).
    /// - `ceil`: smallest `f16` whose `f32` widening is ≥ the input (round up).
    /// - `floor`: largest `f16` whose `f32` widening is ≤ the input (round down).
    ///
    /// `Bot`/`Top` are preserved on both sides; `Extend(NaN)` flows through
    /// (`x as f16` collapses distinct f32 NaN bit patterns to a canonical
    /// f16 NaN, but our `Eq` impl on `ExtendedFloat<f16>` treats
    /// `Extend(NaN) == Extend(NaN)` regardless of bit pattern). f32
    /// magnitudes outside f16's ±65504 range saturate to
    /// `Extend(±INFINITY)` — RNE narrowing in `x as f16`.
    ///
    /// ```
    /// # #![feature(f16)]
    /// use connections::float::f16::F032F016;
    /// use connections::float::{ExtendedFloat::Extend, F032};
    ///
    /// // π narrows to the nearest f16 above/below π's f32 value.
    /// let pi = Extend(std::f32::consts::PI);
    /// let pi_up   = F032F016.ceil(pi);
    /// let pi_down = F032F016.floor(pi);
    /// assert!(F032F016.inner(pi_down) <= pi);
    /// assert!(pi <= F032F016.inner(pi_up));
    ///
    /// // f32::MAX saturates to f16::INFINITY.
    /// let huge: F032 = Extend(f32::MAX);
    /// assert_eq!(F032F016.ceil(huge), Extend(f16::INFINITY));
    /// ```
    pub F032F016 : F032 => F016 {
        ceil:  f032f016_ceil,
        inner: f032f016_inner,
        floor: f032f016_floor,
    }
}

// `<=` and `==` on the f32 side (after the early NaN filter) is total
// and exact. The walk converges in ≤ 2 ULPs because RNE narrowing
// places `est = x as f16` within 1 ULP of the true target.

fn ceil_f32_f16(x: f32) -> f16 {
    if x.is_nan() {
        return f16::NAN;
    }
    let est = x as f16;
    let est_up = est as f32;
    if est_up == x {
        return est;
    }
    let (z, _steps) = if x <= est_up {
        f32_f16_walks::descend_to_ceil(est, x)
    } else {
        f32_f16_walks::ascend_to_ceil(est, x)
    };
    z
}

fn floor_f32_f16(x: f32) -> f16 {
    if x.is_nan() {
        return f16::NAN;
    }
    let est = x as f16;
    let est_up = est as f32;
    if est_up == x {
        return est;
    }
    let (z, _steps) = if est_up <= x {
        f32_f16_walks::ascend_to_floor(est, x)
    } else {
        f32_f16_walks::descend_to_floor(est, x)
    };
    z
}

// ── F064F016 ───────────────────────────────────────────────────────

fn f064f016_ceil(x: F064) -> F016 {
    match x {
        ExtendedFloat::Bot => ExtendedFloat::Bot,
        ExtendedFloat::Top => ExtendedFloat::Top,
        ExtendedFloat::Extend(v) => ExtendedFloat::Extend(ceil_f64_f16(v)),
    }
}
fn f064f016_inner(y: F016) -> F064 {
    match y {
        ExtendedFloat::Bot => ExtendedFloat::Bot,
        ExtendedFloat::Top => ExtendedFloat::Top,
        ExtendedFloat::Extend(v) => ExtendedFloat::Extend(v as f64),
    }
}
fn f064f016_floor(x: F064) -> F016 {
    match x {
        ExtendedFloat::Bot => ExtendedFloat::Bot,
        ExtendedFloat::Top => ExtendedFloat::Top,
        ExtendedFloat::Extend(v) => ExtendedFloat::Extend(floor_f64_f16(v)),
    }
}

crate::triple! {
    /// Connection between [`super::F064`] and [`F016`] under the
    /// N5 lattice — direct `f64 ↔ f16` narrowing.
    ///
    /// Direct (rather than `compose!(F064F032, F032F016)`) because the
    /// two-stage version rounds twice — RNE-RNE composition can land on
    /// a value 1 ULP off from the true f64 → f16 ceiling/floor on
    /// double-rounding cases. The direct path uses `x as f16` (single
    /// RNE step) and then walks ≤ 2 f16 ULPs to correct.
    ///
    /// ```
    /// # #![feature(f16)]
    /// use connections::float::f16::F064F016;
    /// use connections::float::ExtendedFloat::Extend;
    ///
    /// let pi = Extend(std::f64::consts::PI);
    /// let pi_up = F064F016.ceil(pi);
    /// // Widening f16 back to f64 lands above the original.
    /// assert!(F064F016.inner(pi_up) >= pi);
    /// ```
    pub F064F016 : F064 => F016 {
        ceil:  f064f016_ceil,
        inner: f064f016_inner,
        floor: f064f016_floor,
    }
}

fn ceil_f64_f16(x: f64) -> f16 {
    if x.is_nan() {
        return f16::NAN;
    }
    let est = x as f16;
    let est_up = est as f64;
    if est_up == x {
        return est;
    }
    let (z, _steps) = if x <= est_up {
        f64_f16_walks::descend_to_ceil(est, x)
    } else {
        f64_f16_walks::ascend_to_ceil(est, x)
    };
    z
}

fn floor_f64_f16(x: f64) -> f16 {
    if x.is_nan() {
        return f16::NAN;
    }
    let est = x as f16;
    let est_up = est as f64;
    if est_up == x {
        return est;
    }
    let (z, _steps) = if est_up <= x {
        f64_f16_walks::ascend_to_floor(est, x)
    } else {
        f64_f16_walks::descend_to_floor(est, x)
    };
    z
}

#[cfg(test)]
mod tests {
    use super::*;
    #[allow(unused_imports)]
    use crate::conn::{ViewL, ViewR};
    use crate::prop::arb::{arb_f32, arb_f64, extended_float_f16 as ef16};
    use crate::prop::{conn as conn_laws, lattice as lattice_laws};
    use proptest::prelude::*;

    fn ef32() -> impl Strategy<Value = F032> {
        prop_oneof![
            1 => Just(ExtendedFloat::Bot),
            1 => Just(ExtendedFloat::Top),
            8 => arb_f32().prop_map(ExtendedFloat::Extend),
        ]
    }

    fn ef64() -> impl Strategy<Value = F064> {
        prop_oneof![
            1 => Just(ExtendedFloat::Bot),
            1 => Just(ExtendedFloat::Top),
            8 => arb_f64().prop_map(ExtendedFloat::Extend),
        ]
    }

    // ── 16-bit ULP machinery sanity ────────────────────────────────

    #[test]
    fn signed16_round_trip() {
        // Sweep every u16 → i32 → u16 must be the identity.
        for x in 0u16..=u16::MAX {
            assert_eq!(unsigned16(signed16(x)), x, "round-trip failed at {x:#x}");
        }
    }

    #[test]
    fn signed16_total_order_matches_float_order_f16() {
        // For non-NaN f16 values, signed16(a.to_bits()) <= signed16(b.to_bits())
        // iff a.total_cmp(&b) is Less or Equal.
        let samples: [f16; 11] = [
            f16::NEG_INFINITY,
            f16::MIN,
            -1.0_f16,
            -0.5_f16,
            -0.0_f16,
            0.0_f16,
            f16::MIN_POSITIVE,
            0.5_f16,
            1.0_f16,
            f16::MAX,
            f16::INFINITY,
        ];
        for w in samples.windows(2) {
            let (a, b) = (w[0], w[1]);
            let (ia, ib) = (signed16(a.to_bits()), signed16(b.to_bits()));
            assert!(
                ia < ib,
                "signed16 order broken: {a:?} ({ia}) </ {b:?} ({ib})"
            );
        }
    }

    #[test]
    fn shift16_f16_from_zero() {
        let z = shift16_f16(1, 0.0_f16);
        assert!(z > 0.0_f16);
        assert_eq!(z, f16::from_bits(1));
    }

    #[test]
    fn shift16_f16_nan_to_inf() {
        assert_eq!(shift16_f16(1, f16::NAN), f16::INFINITY);
        assert_eq!(shift16_f16(-1, f16::NAN), f16::NEG_INFINITY);
        assert!(shift16_f16(0, f16::NAN).is_nan());
    }

    #[test]
    fn shift16_f16_inf_clamped() {
        assert_eq!(shift16_f16(1, f16::INFINITY), f16::INFINITY);
        assert_eq!(shift16_f16(-1, f16::NEG_INFINITY), f16::NEG_INFINITY);
    }

    #[test]
    fn clamp16_constants_match_inf_bits() {
        assert_eq!(signed16(f16::INFINITY.to_bits()), 31744);
        assert_eq!(signed16(f16::NEG_INFINITY.to_bits()), -31745);
    }

    #[test]
    fn f16_same_shape() {
        let n: ExtendedFloat<f16> = ExtendedFloat::Extend(f16::NAN);
        assert_eq!(n, ExtendedFloat::Extend(f16::NAN));
        assert!(ExtendedFloat::<f16>::Bot < n);
        assert!(n < ExtendedFloat::<f16>::Top);
        assert!(n.partial_cmp(&ExtendedFloat::Extend(1.0_f16)).is_none());
    }

    // ── F032F016 spot checks ───────────────────────────────────────

    #[test]
    fn f032_ceil_floor_zero() {
        assert_eq!(
            F032F016.ceil(ExtendedFloat::Extend(0.0_f32)),
            ExtendedFloat::Extend(0.0_f16),
        );
        assert_eq!(
            F032F016.floor(ExtendedFloat::Extend(0.0_f32)),
            ExtendedFloat::Extend(0.0_f16),
        );
    }

    #[test]
    fn f032_neg_zero_sign_preserved() {
        let neg = F032F016.ceil(ExtendedFloat::Extend(-0.0_f32));
        match neg {
            ExtendedFloat::Extend(v) => assert!(v.is_sign_negative()),
            _ => panic!("expected Extend(-0)"),
        }
    }

    #[test]
    fn f032_ceil_nan() {
        match F032F016.ceil(ExtendedFloat::Extend(f32::NAN)) {
            ExtendedFloat::Extend(v) => assert!(v.is_nan()),
            _ => panic!("expected Extend(NaN)"),
        }
    }

    #[test]
    fn f032_floor_nan() {
        match F032F016.floor(ExtendedFloat::Extend(f32::NAN)) {
            ExtendedFloat::Extend(v) => assert!(v.is_nan()),
            _ => panic!("expected Extend(NaN)"),
        }
    }

    #[test]
    fn f032_pos_inf_preserved() {
        assert_eq!(
            F032F016.ceil(ExtendedFloat::Extend(f32::INFINITY)),
            ExtendedFloat::Extend(f16::INFINITY),
        );
        assert_eq!(
            F032F016.floor(ExtendedFloat::Extend(f32::INFINITY)),
            ExtendedFloat::Extend(f16::INFINITY),
        );
    }

    #[test]
    fn f032_max_saturates_to_inf() {
        assert_eq!(
            F032F016.ceil(ExtendedFloat::Extend(f32::MAX)),
            ExtendedFloat::Extend(f16::INFINITY),
        );
    }

    #[test]
    fn f032_bot_top_pass_through() {
        assert_eq!(F032F016.ceil(ExtendedFloat::Bot), ExtendedFloat::Bot);
        assert_eq!(F032F016.floor(ExtendedFloat::Bot), ExtendedFloat::Bot);
        assert_eq!(F032F016.ceil(ExtendedFloat::Top), ExtendedFloat::Top);
        assert_eq!(F032F016.floor(ExtendedFloat::Top), ExtendedFloat::Top);
        assert_eq!(F032F016.inner(ExtendedFloat::Bot), ExtendedFloat::Bot);
        assert_eq!(F032F016.inner(ExtendedFloat::Top), ExtendedFloat::Top);
    }

    // ── F064F016 spot checks ───────────────────────────────────────

    #[test]
    fn f064_neg_zero_sign_preserved() {
        let neg = F064F016.ceil(ExtendedFloat::Extend(-0.0_f64));
        match neg {
            ExtendedFloat::Extend(v) => assert!(v.is_sign_negative()),
            _ => panic!("expected Extend(-0)"),
        }
    }

    #[test]
    fn f064_ceil_nan() {
        match F064F016.ceil(ExtendedFloat::Extend(f64::NAN)) {
            ExtendedFloat::Extend(v) => assert!(v.is_nan()),
            _ => panic!("expected Extend(NaN)"),
        }
    }

    #[test]
    fn f064_floor_nan() {
        match F064F016.floor(ExtendedFloat::Extend(f64::NAN)) {
            ExtendedFloat::Extend(v) => assert!(v.is_nan()),
            _ => panic!("expected Extend(NaN)"),
        }
    }

    #[test]
    fn f064_pos_inf_preserved() {
        assert_eq!(
            F064F016.ceil(ExtendedFloat::Extend(f64::INFINITY)),
            ExtendedFloat::Extend(f16::INFINITY),
        );
    }

    #[test]
    fn f064_max_saturates_to_inf() {
        // f64::MAX (≈ 1.8e308) is far above f16::MAX (65504). RNE → ∞.
        assert_eq!(
            F064F016.ceil(ExtendedFloat::Extend(f64::MAX)),
            ExtendedFloat::Extend(f16::INFINITY),
        );
    }

    #[test]
    fn f064_bot_top_pass_through() {
        assert_eq!(F064F016.ceil(ExtendedFloat::Bot), ExtendedFloat::Bot);
        assert_eq!(F064F016.floor(ExtendedFloat::Bot), ExtendedFloat::Bot);
        assert_eq!(F064F016.ceil(ExtendedFloat::Top), ExtendedFloat::Top);
        assert_eq!(F064F016.floor(ExtendedFloat::Top), ExtendedFloat::Top);
        assert_eq!(F064F016.inner(ExtendedFloat::Bot), ExtendedFloat::Bot);
        assert_eq!(F064F016.inner(ExtendedFloat::Top), ExtendedFloat::Top);
    }

    // ── F032F016 property tests ────────────────────────────────────

    proptest! {
        #![proptest_config(ProptestConfig {
            cases: 256,
            max_shrink_iters: 200,
            .. ProptestConfig::default()
        })]

        #[test]
        fn f032_galois_l(a in ef32(), b in ef16()) {
            prop_assert!(conn_laws::galois_l(&F032F016::L, a, b));
        }

        #[test]
        fn f032_galois_r(a in ef32(), b in ef16()) {
            prop_assert!(conn_laws::galois_r(&F032F016::R, a, b));
        }

        #[test]
        fn f032_closure_l(a in ef32()) {
            prop_assert!(conn_laws::closure_l(&F032F016::L, a));
        }

        #[test]
        fn f032_closure_r(a in ef32()) {
            prop_assert!(conn_laws::closure_r(&F032F016::R, a));
        }

        #[test]
        fn f032_kernel_l(b in ef16()) {
            prop_assert!(conn_laws::kernel_l(&F032F016::L, b));
        }

        #[test]
        fn f032_kernel_r(b in ef16()) {
            prop_assert!(conn_laws::kernel_r(&F032F016::R, b));
        }

        #[test]
        fn f032_monotone_l(a1 in ef32(), a2 in ef32()) {
            prop_assert!(conn_laws::monotone_l(&F032F016::L, a1, a2));
        }

        #[test]
        fn f032_monotone_r(b1 in ef16(), b2 in ef16()) {
            prop_assert!(conn_laws::monotone_r(&F032F016::R, b1, b2));
        }

        #[test]
        fn f032_idempotent(a in ef32()) {
            prop_assert!(conn_laws::idempotent(&F032F016::L, a));
        }

        #[test]
        fn f032_floor_le_ceil(a in ef32()) {
            prop_assert!(conn_laws::floor_le_ceil(&F032F016, a));
        }

        #[test]
        fn f032_order_reflecting(b1 in ef16(), b2 in ef16()) {
            prop_assert!(conn_laws::order_reflecting(&F032F016, b1, b2));
        }

        // The four walk helpers must converge in ≤ 2 ULP corrections
        // on the f16 side. RNE narrowing places `est = x as f16`
        // within 1 ULP of the true ceil/floor; saturation boundaries
        // and subnormals can require a second step. More signals a bug.
        #[test]
        fn f032_ulp_steps_bounded(x in arb_f32()) {
            if x.is_nan() {
                return Ok(());
            }
            let est = x as f16;
            let est_up = est as f32;
            if est_up == x {
                return Ok(());
            }
            let (_, steps) = if x <= est_up {
                f32_f16_walks::descend_to_ceil(est, x)
            } else {
                f32_f16_walks::ascend_to_ceil(est, x)
            };
            prop_assert!(steps <= 2, "f32_f16_walks::ascend/descend_to_ceil took {steps} steps on x={x}");

            let (_, steps) = if est_up <= x {
                f32_f16_walks::ascend_to_floor(est, x)
            } else {
                f32_f16_walks::descend_to_floor(est, x)
            };
            prop_assert!(steps <= 2, "f32_f16_walks::ascend/descend_to_floor took {steps} steps on x={x}");
        }

        // ── F064F016 property tests ────────────────────────────────

        #[test]
        fn f064_galois_l(a in ef64(), b in ef16()) {
            prop_assert!(conn_laws::galois_l(&F064F016::L, a, b));
        }

        #[test]
        fn f064_galois_r(a in ef64(), b in ef16()) {
            prop_assert!(conn_laws::galois_r(&F064F016::R, a, b));
        }

        #[test]
        fn f064_closure_l(a in ef64()) {
            prop_assert!(conn_laws::closure_l(&F064F016::L, a));
        }

        #[test]
        fn f064_closure_r(a in ef64()) {
            prop_assert!(conn_laws::closure_r(&F064F016::R, a));
        }

        #[test]
        fn f064_kernel_l(b in ef16()) {
            prop_assert!(conn_laws::kernel_l(&F064F016::L, b));
        }

        #[test]
        fn f064_kernel_r(b in ef16()) {
            prop_assert!(conn_laws::kernel_r(&F064F016::R, b));
        }

        #[test]
        fn f064_monotone_l(a1 in ef64(), a2 in ef64()) {
            prop_assert!(conn_laws::monotone_l(&F064F016::L, a1, a2));
        }

        #[test]
        fn f064_monotone_r(b1 in ef16(), b2 in ef16()) {
            prop_assert!(conn_laws::monotone_r(&F064F016::R, b1, b2));
        }

        #[test]
        fn f064_idempotent(a in ef64()) {
            prop_assert!(conn_laws::idempotent(&F064F016::L, a));
        }

        #[test]
        fn f064_floor_le_ceil(a in ef64()) {
            prop_assert!(conn_laws::floor_le_ceil(&F064F016, a));
        }

        #[test]
        fn f064_order_reflecting(b1 in ef16(), b2 in ef16()) {
            prop_assert!(conn_laws::order_reflecting(&F064F016, b1, b2));
        }

        #[test]
        fn f064_ulp_steps_bounded(x in arb_f64()) {
            if x.is_nan() {
                return Ok(());
            }
            let est = x as f16;
            let est_up = est as f64;
            if est_up == x {
                return Ok(());
            }
            let (_, steps) = if x <= est_up {
                f64_f16_walks::descend_to_ceil(est, x)
            } else {
                f64_f16_walks::ascend_to_ceil(est, x)
            };
            prop_assert!(steps <= 2, "f64_f16_walks::ascend/descend_to_ceil took {steps} steps on x={x}");

            let (_, steps) = if est_up <= x {
                f64_f16_walks::ascend_to_floor(est, x)
            } else {
                f64_f16_walks::descend_to_floor(est, x)
            };
            prop_assert!(steps <= 2, "f64_f16_walks::ascend/descend_to_floor took {steps} steps on x={x}");
        }
    }
}
