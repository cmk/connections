//! Conns originating at [`F064`](super::F064).
//!
//! Currently houses [`F064F032`] (`ExtendedFloat<f64> → ExtendedFloat<f32>`).
//! Future direct-precision Conns from f64 (e.g. `F064F016`, `F064B016`)
//! land alongside it.

use super::{ExtendedFloat, shift32};
use crate::conn::Conn;

/// Connection between [`super::F064`] (i.e. `ExtendedFloat<f64>`) and
/// [`super::F032`] (`ExtendedFloat<f32>`) under the N5 lattice ordering.
///
/// - `inner`: lossless `f32 → f64` embedding (`Bot/Top/Extend` pass through;
///   `Extend(v)` casts `v as f64`).
/// - `ceil`: smallest `f32` whose `f64` embedding is ≥ the input (round up).
/// - `floor`: largest `f32` whose `f64` embedding is ≤ the input (round down).
///
/// `ExtendedFloat::Bot` / `Top` are preserved on both sides;
/// `Extend(NaN)` flows through unchanged because the `Extend(NaN) →
/// Extend(NaN as f32)` cast is bit-preserving for NaN.
pub const F064F032: Conn<ExtendedFloat<f64>, ExtendedFloat<f32>> = {
    fn ceil(x: ExtendedFloat<f64>) -> ExtendedFloat<f32> {
        match x {
            ExtendedFloat::Bot => ExtendedFloat::Bot,
            ExtendedFloat::Top => ExtendedFloat::Top,
            ExtendedFloat::Extend(v) => ExtendedFloat::Extend(ceil_f64_f32(v)),
        }
    }
    fn inner(y: ExtendedFloat<f32>) -> ExtendedFloat<f64> {
        match y {
            ExtendedFloat::Bot => ExtendedFloat::Bot,
            ExtendedFloat::Top => ExtendedFloat::Top,
            ExtendedFloat::Extend(v) => ExtendedFloat::Extend(v as f64),
        }
    }
    fn floor(x: ExtendedFloat<f64>) -> ExtendedFloat<f32> {
        match x {
            ExtendedFloat::Bot => ExtendedFloat::Bot,
            ExtendedFloat::Top => ExtendedFloat::Top,
            ExtendedFloat::Extend(v) => ExtendedFloat::Extend(floor_f64_f32(v)),
        }
    }
    Conn::new(ceil, inner, floor)
};

// All `<=` and `==` comparisons in the helpers below operate on
// values that the early `is_nan()` checks have already filtered to
// non-NaN. Standard `<=` / `==` on non-NaN floats is total and exact;
// the lattice-style preorder patches that `ExtendedFloat` provides
// are not needed here.

fn ceil_f64_f32(x: f64) -> f32 {
    if x.is_nan() {
        return f32::NAN;
    }

    let est = x as f32;
    let est_up = est as f64;

    if est_up == x {
        return est;
    }

    let (z, _steps) = if x <= est_up {
        descend_to_ceil(est, x)
    } else {
        ascend_to_ceil(est, x)
    };
    z
}

fn floor_f64_f32(x: f64) -> f32 {
    if x.is_nan() {
        return f32::NAN;
    }

    let est = x as f32;
    let est_up = est as f64;

    if est_up == x {
        return est;
    }

    let (z, _steps) = if est_up <= x {
        ascend_to_floor(est, x)
    } else {
        descend_to_floor(est, x)
    };
    z
}

// The four walk functions return `(result, steps)`. IEEE 754
// round-to-nearest guarantees the `as f32` estimate is within one ULP
// of the true ceiling/floor, so in practice these loops execute 0–2
// times. The step count is exposed so `ulp_steps_bounded` proptest can
// assert that bound directly.

/// Walk up (toward +∞) until `inner(z) >= x`, returning `(z, steps)`.
fn ascend_to_ceil(start: f32, x: f64) -> (f32, u32) {
    let mut z = start;
    let mut steps = 0;
    loop {
        let next = shift32(1, z);
        if next <= z {
            return (z, steps);
        }
        steps += 1;
        z = next;
        if x <= z as f64 {
            return (z, steps);
        }
    }
}

/// Walk down (toward -∞) while `inner(z) >= x` still holds, returning
/// the last valid `(z, steps)`.
fn descend_to_ceil(start: f32, x: f64) -> (f32, u32) {
    let mut z = start;
    let mut steps = 0;
    loop {
        let next = shift32(-1, z);
        if z <= next {
            return (z, steps);
        }
        let next_up = next as f64;
        // Inputs are non-NaN by construction, so `>` is equivalent to
        // `!(x <= next_up)` here and clearer to clippy.
        if x > next_up {
            return (z, steps);
        }
        steps += 1;
        z = next;
    }
}

/// Walk down (toward -∞) until `inner(z) <= x`, returning `(z, steps)`.
fn descend_to_floor(start: f32, x: f64) -> (f32, u32) {
    let mut z = start;
    let mut steps = 0;
    loop {
        let next = shift32(-1, z);
        if z <= next {
            return (z, steps);
        }
        steps += 1;
        z = next;
        if z as f64 <= x {
            return (z, steps);
        }
    }
}

/// Walk up (toward +∞) while `inner(z) <= x` still holds, returning
/// the last valid `(z, steps)`.
fn ascend_to_floor(start: f32, x: f64) -> (f32, u32) {
    let mut z = start;
    let mut steps = 0;
    loop {
        let next = shift32(1, z);
        if next <= z {
            return (z, steps);
        }
        let next_up = next as f64;
        // Inputs are non-NaN by construction, so `>` is equivalent to
        // `!(next_up <= x)` here and clearer to clippy.
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
    use crate::property::arb::{arb_f32, arb_f64};
    use crate::property::laws;
    use proptest::prelude::*;

    /// Local strategy: `ExtendedFloat<f64>` over `Bot`, `Top`, and full-
    /// range `Extend(_)` (8:1:1 weighting toward the extension slot).
    /// Unlike [`crate::property::arb::extended_float_f64`] which uses
    /// the bounded f64 generator (for connections whose target is a
    /// bounded integer rung), `F064F032`'s target is full-range f32 —
    /// we want unbounded coverage.
    fn ef64() -> impl Strategy<Value = ExtendedFloat<f64>> {
        prop_oneof![
            1 => Just(ExtendedFloat::Bot),
            1 => Just(ExtendedFloat::Top),
            8 => arb_f64().prop_map(ExtendedFloat::Extend),
        ]
    }

    fn ef32() -> impl Strategy<Value = ExtendedFloat<f32>> {
        prop_oneof![
            1 => Just(ExtendedFloat::Bot),
            1 => Just(ExtendedFloat::Top),
            8 => arb_f32().prop_map(ExtendedFloat::Extend),
        ]
    }

    // ── Spot checks ────────────────────────────────────────────────

    #[test]
    fn ceil_exact_value() {
        assert_eq!(
            F064F032.ceil(ExtendedFloat::Extend(0.5_f64)),
            ExtendedFloat::Extend(0.5_f32),
        );
    }

    #[test]
    fn floor_exact_value() {
        assert_eq!(
            F064F032.floor(ExtendedFloat::Extend(0.5_f64)),
            ExtendedFloat::Extend(0.5_f32),
        );
    }

    #[test]
    fn ceil_nan() {
        match F064F032.ceil(ExtendedFloat::Extend(f64::NAN)) {
            ExtendedFloat::Extend(v) => assert!(v.is_nan()),
            _ => panic!("expected Extend(NaN)"),
        }
    }

    #[test]
    fn floor_nan() {
        match F064F032.floor(ExtendedFloat::Extend(f64::NAN)) {
            ExtendedFloat::Extend(v) => assert!(v.is_nan()),
            _ => panic!("expected Extend(NaN)"),
        }
    }

    #[test]
    fn inner_nan() {
        match F064F032.inner(ExtendedFloat::Extend(f32::NAN)) {
            ExtendedFloat::Extend(v) => assert!(v.is_nan()),
            _ => panic!("expected Extend(NaN)"),
        }
    }

    #[test]
    fn ceil_ge_floor() {
        let x = ExtendedFloat::Extend(std::f64::consts::PI);
        assert!(F064F032.floor(x) <= F064F032.ceil(x));
    }

    #[test]
    fn bot_top_pass_through() {
        // `Bot` and `Top` flow through unchanged on every adjoint.
        assert_eq!(F064F032.ceil(ExtendedFloat::Bot), ExtendedFloat::Bot);
        assert_eq!(F064F032.floor(ExtendedFloat::Bot), ExtendedFloat::Bot);
        assert_eq!(F064F032.ceil(ExtendedFloat::Top), ExtendedFloat::Top);
        assert_eq!(F064F032.floor(ExtendedFloat::Top), ExtendedFloat::Top);
        assert_eq!(F064F032.inner(ExtendedFloat::Bot), ExtendedFloat::Bot);
        assert_eq!(F064F032.inner(ExtendedFloat::Top), ExtendedFloat::Top);
    }

    // ── Property tests ─────────────────────────────────────────────

    proptest! {
        #![proptest_config(ProptestConfig {
            cases: 256,
            max_shrink_iters: 200,
            .. ProptestConfig::default()
        })]

        #[test]
        fn galois_l(a in ef64(), b in ef32()) {
            prop_assert!(laws::conn_galois_l(&F064F032, a, b));
        }

        #[test]
        fn galois_r(a in ef64(), b in ef32()) {
            prop_assert!(laws::conn_galois_r(&F064F032, a, b));
        }

        #[test]
        fn closure_l(a in ef64()) {
            prop_assert!(laws::conn_closure_l(&F064F032, a));
        }

        #[test]
        fn closure_r(a in ef64()) {
            prop_assert!(laws::conn_closure_r(&F064F032, a));
        }

        #[test]
        fn kernel_l(b in ef32()) {
            prop_assert!(laws::conn_kernel_l(&F064F032, b));
        }

        #[test]
        fn kernel_r(b in ef32()) {
            prop_assert!(laws::conn_kernel_r(&F064F032, b));
        }

        #[test]
        fn monotone_l(a1 in ef64(), a2 in ef64()) {
            prop_assert!(laws::conn_monotone_l(&F064F032, a1, a2));
        }

        #[test]
        fn monotone_r(b1 in ef32(), b2 in ef32()) {
            prop_assert!(laws::conn_monotone_r(&F064F032, b1, b2));
        }

        #[test]
        fn idempotent(a in ef64()) {
            prop_assert!(laws::conn_idempotent(&F064F032, a));
        }

        #[test]
        fn floor_le_ceil(a in ef64()) {
            prop_assert!(laws::conn_floor_le_ceil(&F064F032, a));
        }

        // The four walk helpers should converge in ≤ 2 ULP corrections
        // for any non-NaN input. RNE narrowing places `est = x as f32`
        // within 1 ULP of the true ceil/floor; saturation boundaries
        // and subnormals can in principle require a second step. More
        // than that signals a bug in the helper.
        #[test]
        fn ulp_steps_bounded(x in arb_f64()) {
            if x.is_nan() {
                return Ok(());
            }
            let est = x as f32;
            let est_up = est as f64;
            if est_up == x {
                return Ok(());
            }
            let (_, steps) = if x <= est_up {
                descend_to_ceil(est, x)
            } else {
                ascend_to_ceil(est, x)
            };
            prop_assert!(steps <= 2, "ascend/descend_to_ceil took {steps} steps on x={x}");

            let (_, steps) = if est_up <= x {
                ascend_to_floor(est, x)
            } else {
                descend_to_floor(est, x)
            };
            prop_assert!(steps <= 2, "ascend/descend_to_floor took {steps} steps on x={x}");
        }

        // `conn_ulp_bound` is intentionally omitted for `F064F032`.
        // The predicate's `rung: F where F: Fn(B) -> i64` extractor
        // is documented (`laws.rs:439-447`) as "specific to integer-
        // tier connections (the rung types have an i64 payload)".
        // For float Conns, ULP is bit-level (mantissa increment), a
        // different concept — and there is no clean i64 mapping for
        // `ExtendedFloat<f32>` (Bot / Top would have to alias to
        // sentinel ints, which isn't a meaningful "rung distance").
    }
}
