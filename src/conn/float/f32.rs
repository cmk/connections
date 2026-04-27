//! Conns originating at [`F032`](super::F032).
//!
//! Currently houses [`F032F016`] (`ExtendedFloat<f32> → ExtendedFloat<half::f16>`).
//! Future direct-precision Conns from f32 (e.g. `F032B016`) land
//! alongside it.

use super::{ExtendedFloat, F016, F032, shift16_f16};
use crate::conn::Conn;
use half::f16;

/// Connection between [`super::F032`] (`ExtendedFloat<f32>`) and
/// [`super::F016`] (`ExtendedFloat<half::f16>`) under the N5 lattice.
///
/// - `inner`: lossless `f16 → f32` widening (`Bot/Top/Extend` pass through;
///   `Extend(v)` calls `v.to_f32()`).
/// - `ceil`: smallest `f16` whose `f32` widening is ≥ the input (round up).
/// - `floor`: largest `f16` whose `f32` widening is ≤ the input (round down).
///
/// `Bot`/`Top` are preserved on both sides; `Extend(NaN)` flows through
/// (half-rs's `from_f32` collapses distinct f32 NaN bit patterns to a
/// canonical f16 NaN, but our `Eq` impl on `ExtendedFloat<half::f16>`
/// treats `Extend(NaN) == Extend(NaN)` regardless of bit pattern).
/// f32 magnitudes outside f16's ±65504 range saturate to `Extend(±INFINITY)`
/// — RNE narrowing in `half::f16::from_f32`.
///
/// ```
/// use connections::conn::float::f32::F032F016;
/// use connections::conn::float::{ExtendedFloat::Extend, F032};
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
/// assert_eq!(F032F016.ceil(huge), Extend(half::f16::INFINITY));
/// ```
pub const F032F016: Conn<F032, F016> = {
    fn ceil(x: F032) -> F016 {
        match x {
            ExtendedFloat::Bot => ExtendedFloat::Bot,
            ExtendedFloat::Top => ExtendedFloat::Top,
            ExtendedFloat::Extend(v) => ExtendedFloat::Extend(ceil_f32_f16(v)),
        }
    }
    fn inner(y: F016) -> F032 {
        match y {
            ExtendedFloat::Bot => ExtendedFloat::Bot,
            ExtendedFloat::Top => ExtendedFloat::Top,
            ExtendedFloat::Extend(v) => ExtendedFloat::Extend(v.to_f32()),
        }
    }
    fn floor(x: F032) -> F016 {
        match x {
            ExtendedFloat::Bot => ExtendedFloat::Bot,
            ExtendedFloat::Top => ExtendedFloat::Top,
            ExtendedFloat::Extend(v) => ExtendedFloat::Extend(floor_f32_f16(v)),
        }
    }
    Conn::new(ceil, inner, floor)
};

// `<=` and `==` on the f32 side (after the early NaN filter) is total
// and exact. The walk converges in ≤ 2 ULPs because RNE narrowing
// places `est = f16::from_f32(x)` within 1 ULP of the true target.

fn ceil_f32_f16(x: f32) -> f16 {
    if x.is_nan() {
        return f16::NAN;
    }
    let est = f16::from_f32(x);
    let est_up = est.to_f32();
    if est_up == x {
        return est;
    }
    let (z, _steps) = if x <= est_up {
        descend_to_ceil_f16(est, x)
    } else {
        ascend_to_ceil_f16(est, x)
    };
    z
}

fn floor_f32_f16(x: f32) -> f16 {
    if x.is_nan() {
        return f16::NAN;
    }
    let est = f16::from_f32(x);
    let est_up = est.to_f32();
    if est_up == x {
        return est;
    }
    let (z, _steps) = if est_up <= x {
        ascend_to_floor_f16(est, x)
    } else {
        descend_to_floor_f16(est, x)
    };
    z
}

/// Walk up (toward +∞) until `inner(z) >= x`, returning `(z, steps)`.
fn ascend_to_ceil_f16(start: f16, x: f32) -> (f16, u32) {
    let mut z = start;
    let mut steps = 0;
    loop {
        let next = shift16_f16(1, z);
        if next <= z {
            return (z, steps);
        }
        steps += 1;
        z = next;
        if x <= z.to_f32() {
            return (z, steps);
        }
    }
}

/// Walk down (toward -∞) while `inner(z) >= x` still holds.
fn descend_to_ceil_f16(start: f16, x: f32) -> (f16, u32) {
    let mut z = start;
    let mut steps = 0;
    loop {
        let next = shift16_f16(-1, z);
        if z <= next {
            return (z, steps);
        }
        let next_up = next.to_f32();
        if x > next_up {
            return (z, steps);
        }
        steps += 1;
        z = next;
    }
}

/// Walk down (toward -∞) until `inner(z) <= x`, returning `(z, steps)`.
fn descend_to_floor_f16(start: f16, x: f32) -> (f16, u32) {
    let mut z = start;
    let mut steps = 0;
    loop {
        let next = shift16_f16(-1, z);
        if z <= next {
            return (z, steps);
        }
        steps += 1;
        z = next;
        if z.to_f32() <= x {
            return (z, steps);
        }
    }
}

/// Walk up (toward +∞) while `inner(z) <= x` still holds.
fn ascend_to_floor_f16(start: f16, x: f32) -> (f16, u32) {
    let mut z = start;
    let mut steps = 0;
    loop {
        let next = shift16_f16(1, z);
        if next <= z {
            return (z, steps);
        }
        let next_up = next.to_f32();
        if next_up > x {
            return (z, steps);
        }
        steps += 1;
        z = next;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::property::arb::{arb_f16, arb_f32};
    use crate::property::laws;
    use proptest::prelude::*;

    fn ef32() -> impl Strategy<Value = F032> {
        prop_oneof![
            1 => Just(ExtendedFloat::Bot),
            1 => Just(ExtendedFloat::Top),
            8 => arb_f32().prop_map(ExtendedFloat::Extend),
        ]
    }

    fn ef16() -> impl Strategy<Value = F016> {
        prop_oneof![
            1 => Just(ExtendedFloat::Bot),
            1 => Just(ExtendedFloat::Top),
            8 => arb_f16().prop_map(ExtendedFloat::Extend),
        ]
    }

    // ── Spot checks ────────────────────────────────────────────────

    #[test]
    fn ceil_floor_zero() {
        assert_eq!(
            F032F016.ceil(ExtendedFloat::Extend(0.0_f32)),
            ExtendedFloat::Extend(f16::ZERO),
        );
        assert_eq!(
            F032F016.floor(ExtendedFloat::Extend(0.0_f32)),
            ExtendedFloat::Extend(f16::ZERO),
        );
    }

    #[test]
    fn neg_zero_sign_preserved() {
        // Sign of zero must not flip on RNE narrowing.
        let neg = F032F016.ceil(ExtendedFloat::Extend(-0.0_f32));
        match neg {
            ExtendedFloat::Extend(v) => assert!(v.is_sign_negative()),
            _ => panic!("expected Extend(-0)"),
        }
    }

    #[test]
    fn ceil_nan() {
        match F032F016.ceil(ExtendedFloat::Extend(f32::NAN)) {
            ExtendedFloat::Extend(v) => assert!(v.is_nan()),
            _ => panic!("expected Extend(NaN)"),
        }
    }

    #[test]
    fn pos_inf_preserved() {
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
    fn f32_max_saturates_to_inf() {
        // f16::MAX = 65504, far below f32::MAX. RNE narrowing rounds to ∞.
        assert_eq!(
            F032F016.ceil(ExtendedFloat::Extend(f32::MAX)),
            ExtendedFloat::Extend(f16::INFINITY),
        );
    }

    #[test]
    fn bot_top_pass_through() {
        assert_eq!(F032F016.ceil(ExtendedFloat::Bot), ExtendedFloat::Bot);
        assert_eq!(F032F016.floor(ExtendedFloat::Bot), ExtendedFloat::Bot);
        assert_eq!(F032F016.ceil(ExtendedFloat::Top), ExtendedFloat::Top);
        assert_eq!(F032F016.floor(ExtendedFloat::Top), ExtendedFloat::Top);
        assert_eq!(F032F016.inner(ExtendedFloat::Bot), ExtendedFloat::Bot);
        assert_eq!(F032F016.inner(ExtendedFloat::Top), ExtendedFloat::Top);
    }

    // ── Property tests ─────────────────────────────────────────────

    proptest! {
        #![proptest_config(ProptestConfig {
            cases: 256,
            max_shrink_iters: 200,
            .. ProptestConfig::default()
        })]

        #[test]
        fn galois_l(a in ef32(), b in ef16()) {
            prop_assert!(laws::conn_galois_l(&F032F016, a, b));
        }

        #[test]
        fn galois_r(a in ef32(), b in ef16()) {
            prop_assert!(laws::conn_galois_r(&F032F016, a, b));
        }

        #[test]
        fn closure_l(a in ef32()) {
            prop_assert!(laws::conn_closure_l(&F032F016, a));
        }

        #[test]
        fn closure_r(a in ef32()) {
            prop_assert!(laws::conn_closure_r(&F032F016, a));
        }

        #[test]
        fn kernel_l(b in ef16()) {
            prop_assert!(laws::conn_kernel_l(&F032F016, b));
        }

        #[test]
        fn kernel_r(b in ef16()) {
            prop_assert!(laws::conn_kernel_r(&F032F016, b));
        }

        #[test]
        fn monotone_l(a1 in ef32(), a2 in ef32()) {
            prop_assert!(laws::conn_monotone_l(&F032F016, a1, a2));
        }

        #[test]
        fn monotone_r(b1 in ef16(), b2 in ef16()) {
            prop_assert!(laws::conn_monotone_r(&F032F016, b1, b2));
        }

        #[test]
        fn idempotent(a in ef32()) {
            prop_assert!(laws::conn_idempotent(&F032F016, a));
        }

        #[test]
        fn floor_le_ceil(a in ef32()) {
            prop_assert!(laws::conn_floor_le_ceil(&F032F016, a));
        }

        // The four walk helpers must converge in ≤ 2 ULP corrections
        // on the f16 side. RNE narrowing places `est = f16::from_f32(x)`
        // within 1 ULP of the true ceil/floor; saturation boundaries
        // and subnormals can require a second step. More signals a bug.
        #[test]
        fn ulp_steps_bounded(x in arb_f32()) {
            if x.is_nan() {
                return Ok(());
            }
            let est = f16::from_f32(x);
            let est_up = est.to_f32();
            if est_up == x {
                return Ok(());
            }
            let (_, steps) = if x <= est_up {
                descend_to_ceil_f16(est, x)
            } else {
                ascend_to_ceil_f16(est, x)
            };
            prop_assert!(steps <= 2, "ascend/descend_to_ceil_f16 took {steps} steps on x={x}");

            let (_, steps) = if est_up <= x {
                ascend_to_floor_f16(est, x)
            } else {
                descend_to_floor_f16(est, x)
            };
            prop_assert!(steps <= 2, "ascend/descend_to_floor_f16 took {steps} steps on x={x}");
        }
    }
}
