//! Conns originating at [`F064`](super::F064).
//!
//! Currently houses [`F064F032`] (`ExtendedFloat<f64> → ExtendedFloat<f32>`).
//! Future direct-precision Conns from f64 (e.g. `F064F016`, `F064B016`)
//! land alongside it.

use super::{
    B016, ExtendedFloat, F016, F064, def_walk_helpers, shift16_bf16, shift16_f16, shift32,
    widen_f32_f64,
};
use crate::conn::Conn;
use half::{bf16, f16};

def_walk_helpers!(f64_f32_walks, f64, f32, shift32, widen_f32_f64);
def_walk_helpers!(f64_f16_walks, f64, f16, shift16_f16, f16::to_f64);
def_walk_helpers!(f64_b16_walks, f64, bf16, shift16_bf16, bf16::to_f64);

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
        f64_f32_walks::descend_to_ceil(est, x)
    } else {
        f64_f32_walks::ascend_to_ceil(est, x)
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
        f64_f32_walks::ascend_to_floor(est, x)
    } else {
        f64_f32_walks::descend_to_floor(est, x)
    };
    z
}

// ── F064F016 ───────────────────────────────────────────────────────

/// Connection between [`super::F064`] and [`super::F016`] under the
/// N5 lattice — direct `f64 ↔ half::f16` narrowing.
///
/// Direct (rather than `compose!(F064F032, F032F016)`) because the
/// two-stage version rounds twice — RNE-RNE composition can land on
/// a value 1 ULP off from the true f64 → f16 ceiling/floor on
/// double-rounding cases. The direct path uses `f16::from_f64`
/// (single RNE step) and then walks ≤ 2 f16 ULPs to correct.
///
/// ```
/// use connections::conn::float::f64::F064F016;
/// use connections::conn::float::ExtendedFloat::Extend;
///
/// let pi = Extend(std::f64::consts::PI);
/// let pi_up = F064F016.ceil(pi);
/// // Widening f16 back to f64 lands above the original.
/// assert!(F064F016.inner(pi_up) >= pi);
/// ```
pub const F064F016: Conn<F064, F016> = {
    fn ceil(x: F064) -> F016 {
        match x {
            ExtendedFloat::Bot => ExtendedFloat::Bot,
            ExtendedFloat::Top => ExtendedFloat::Top,
            ExtendedFloat::Extend(v) => ExtendedFloat::Extend(ceil_f64_f16(v)),
        }
    }
    fn inner(y: F016) -> F064 {
        match y {
            ExtendedFloat::Bot => ExtendedFloat::Bot,
            ExtendedFloat::Top => ExtendedFloat::Top,
            ExtendedFloat::Extend(v) => ExtendedFloat::Extend(v.to_f64()),
        }
    }
    fn floor(x: F064) -> F016 {
        match x {
            ExtendedFloat::Bot => ExtendedFloat::Bot,
            ExtendedFloat::Top => ExtendedFloat::Top,
            ExtendedFloat::Extend(v) => ExtendedFloat::Extend(floor_f64_f16(v)),
        }
    }
    Conn::new(ceil, inner, floor)
};

fn ceil_f64_f16(x: f64) -> f16 {
    if x.is_nan() {
        return f16::NAN;
    }
    let est = f16::from_f64(x);
    let est_up = est.to_f64();
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
    let est = f16::from_f64(x);
    let est_up = est.to_f64();
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

// ── F064B016 ───────────────────────────────────────────────────────

/// Connection between [`super::F064`] and [`super::B016`] under the
/// N5 lattice — direct `f64 ↔ half::bf16` narrowing.
///
/// bf16's exponent matches f32's (8 bits) but is narrower than f64's
/// (11 bits), so f64 magnitudes outside `bf16::MAX` (≈ 3.39e38)
/// saturate to ±∞. The mantissa drop is severe (52 → 7 bits) but
/// `bf16::from_f64` does single-step RNE rounding; the walk
/// converges in ≤ 2 ULPs on the bf16 side.
///
/// **This is the headline new feature of MR !21** — direct f64 →
/// bfloat16 with full Galois-law backing, on stable Rust.
///
/// ```
/// use connections::conn::float::f64::F064B016;
/// use connections::conn::float::ExtendedFloat::Extend;
///
/// // π narrows to bf16. The two-sided round-trip brackets π.
/// let pi = Extend(std::f64::consts::PI);
/// let pi_up   = F064B016.ceil(pi);
/// let pi_down = F064B016.floor(pi);
/// assert!(F064B016.inner(pi_down) <= pi);
/// assert!(pi <= F064B016.inner(pi_up));
///
/// // f64::MAX saturates to bf16::INFINITY.
/// let huge = Extend(f64::MAX);
/// assert_eq!(F064B016.ceil(huge), Extend(half::bf16::INFINITY));
/// ```
pub const F064B016: Conn<F064, B016> = {
    fn ceil(x: F064) -> B016 {
        match x {
            ExtendedFloat::Bot => ExtendedFloat::Bot,
            ExtendedFloat::Top => ExtendedFloat::Top,
            ExtendedFloat::Extend(v) => ExtendedFloat::Extend(ceil_f64_bf16(v)),
        }
    }
    fn inner(y: B016) -> F064 {
        match y {
            ExtendedFloat::Bot => ExtendedFloat::Bot,
            ExtendedFloat::Top => ExtendedFloat::Top,
            ExtendedFloat::Extend(v) => ExtendedFloat::Extend(v.to_f64()),
        }
    }
    fn floor(x: F064) -> B016 {
        match x {
            ExtendedFloat::Bot => ExtendedFloat::Bot,
            ExtendedFloat::Top => ExtendedFloat::Top,
            ExtendedFloat::Extend(v) => ExtendedFloat::Extend(floor_f64_bf16(v)),
        }
    }
    Conn::new(ceil, inner, floor)
};

fn ceil_f64_bf16(x: f64) -> bf16 {
    if x.is_nan() {
        return bf16::NAN;
    }
    let est = bf16::from_f64(x);
    let est_up = est.to_f64();
    if est_up == x {
        return est;
    }
    let (z, _steps) = if x <= est_up {
        f64_b16_walks::descend_to_ceil(est, x)
    } else {
        f64_b16_walks::ascend_to_ceil(est, x)
    };
    z
}

fn floor_f64_bf16(x: f64) -> bf16 {
    if x.is_nan() {
        return bf16::NAN;
    }
    let est = bf16::from_f64(x);
    let est_up = est.to_f64();
    if est_up == x {
        return est;
    }
    let (z, _steps) = if est_up <= x {
        f64_b16_walks::ascend_to_floor(est, x)
    } else {
        f64_b16_walks::descend_to_floor(est, x)
    };
    z
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::property::arb::{arb_bf16, arb_f16, arb_f32, arb_f64};
    use crate::property::laws;
    use proptest::prelude::*;

    fn ef16() -> impl Strategy<Value = F016> {
        prop_oneof![
            1 => Just(ExtendedFloat::Bot),
            1 => Just(ExtendedFloat::Top),
            8 => arb_f16().prop_map(ExtendedFloat::Extend),
        ]
    }

    fn eb16() -> impl Strategy<Value = B016> {
        prop_oneof![
            1 => Just(ExtendedFloat::Bot),
            1 => Just(ExtendedFloat::Top),
            8 => arb_bf16().prop_map(ExtendedFloat::Extend),
        ]
    }

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
                f64_f32_walks::descend_to_ceil(est, x)
            } else {
                f64_f32_walks::ascend_to_ceil(est, x)
            };
            prop_assert!(steps <= 2, "f64_f32_walks::ascend/descend_to_ceil took {steps} steps on x={x}");

            let (_, steps) = if est_up <= x {
                f64_f32_walks::ascend_to_floor(est, x)
            } else {
                f64_f32_walks::descend_to_floor(est, x)
            };
            prop_assert!(steps <= 2, "f64_f32_walks::ascend/descend_to_floor took {steps} steps on x={x}");
        }

        // `conn_ulp_bound` is intentionally omitted for `F064F032`.
        // The predicate's `rung: F where F: Fn(B) -> i64` extractor
        // is documented (`laws.rs:439-447`) as "specific to integer-
        // tier connections (the rung types have an i64 payload)".
        // For float Conns, ULP is bit-level (mantissa increment), a
        // different concept — and there is no clean i64 mapping for
        // `ExtendedFloat<f32>` (Bot / Top would have to alias to
        // sentinel ints, which isn't a meaningful "rung distance").

        // ── F064F016 battery ─────────────────────────────────────

        #[test]
        fn f16_galois_l(a in ef64(), b in ef16()) {
            prop_assert!(laws::conn_galois_l(&F064F016, a, b));
        }

        #[test]
        fn f16_galois_r(a in ef64(), b in ef16()) {
            prop_assert!(laws::conn_galois_r(&F064F016, a, b));
        }

        #[test]
        fn f16_closure_l(a in ef64()) {
            prop_assert!(laws::conn_closure_l(&F064F016, a));
        }

        #[test]
        fn f16_closure_r(a in ef64()) {
            prop_assert!(laws::conn_closure_r(&F064F016, a));
        }

        #[test]
        fn f16_kernel_l(b in ef16()) {
            prop_assert!(laws::conn_kernel_l(&F064F016, b));
        }

        #[test]
        fn f16_kernel_r(b in ef16()) {
            prop_assert!(laws::conn_kernel_r(&F064F016, b));
        }

        #[test]
        fn f16_monotone_l(a1 in ef64(), a2 in ef64()) {
            prop_assert!(laws::conn_monotone_l(&F064F016, a1, a2));
        }

        #[test]
        fn f16_monotone_r(b1 in ef16(), b2 in ef16()) {
            prop_assert!(laws::conn_monotone_r(&F064F016, b1, b2));
        }

        #[test]
        fn f16_idempotent(a in ef64()) {
            prop_assert!(laws::conn_idempotent(&F064F016, a));
        }

        #[test]
        fn f16_floor_le_ceil(a in ef64()) {
            prop_assert!(laws::conn_floor_le_ceil(&F064F016, a));
        }

        #[test]
        fn f16_ulp_steps_bounded(x in arb_f64()) {
            if x.is_nan() {
                return Ok(());
            }
            let est = f16::from_f64(x);
            let est_up = est.to_f64();
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

        // ── F064B016 battery ─────────────────────────────────────

        #[test]
        fn b16_galois_l(a in ef64(), b in eb16()) {
            prop_assert!(laws::conn_galois_l(&F064B016, a, b));
        }

        #[test]
        fn b16_galois_r(a in ef64(), b in eb16()) {
            prop_assert!(laws::conn_galois_r(&F064B016, a, b));
        }

        #[test]
        fn b16_closure_l(a in ef64()) {
            prop_assert!(laws::conn_closure_l(&F064B016, a));
        }

        #[test]
        fn b16_closure_r(a in ef64()) {
            prop_assert!(laws::conn_closure_r(&F064B016, a));
        }

        #[test]
        fn b16_kernel_l(b in eb16()) {
            prop_assert!(laws::conn_kernel_l(&F064B016, b));
        }

        #[test]
        fn b16_kernel_r(b in eb16()) {
            prop_assert!(laws::conn_kernel_r(&F064B016, b));
        }

        #[test]
        fn b16_monotone_l(a1 in ef64(), a2 in ef64()) {
            prop_assert!(laws::conn_monotone_l(&F064B016, a1, a2));
        }

        #[test]
        fn b16_monotone_r(b1 in eb16(), b2 in eb16()) {
            prop_assert!(laws::conn_monotone_r(&F064B016, b1, b2));
        }

        #[test]
        fn b16_idempotent(a in ef64()) {
            prop_assert!(laws::conn_idempotent(&F064B016, a));
        }

        #[test]
        fn b16_floor_le_ceil(a in ef64()) {
            prop_assert!(laws::conn_floor_le_ceil(&F064B016, a));
        }

        #[test]
        fn b16_ulp_steps_bounded(x in arb_f64()) {
            if x.is_nan() {
                return Ok(());
            }
            let est = bf16::from_f64(x);
            let est_up = est.to_f64();
            if est_up == x {
                return Ok(());
            }
            let (_, steps) = if x <= est_up {
                f64_b16_walks::descend_to_ceil(est, x)
            } else {
                f64_b16_walks::ascend_to_ceil(est, x)
            };
            prop_assert!(steps <= 2, "f64_b16_walks::ascend/descend_to_ceil took {steps} steps on x={x}");

            let (_, steps) = if est_up <= x {
                f64_b16_walks::ascend_to_floor(est, x)
            } else {
                f64_b16_walks::descend_to_floor(est, x)
            };
            prop_assert!(steps <= 2, "f64_b16_walks::ascend/descend_to_floor took {steps} steps on x={x}");
        }
    }

    // ── F064F016 spot checks ───────────────────────────────────────

    #[test]
    fn f16_neg_zero_sign_preserved() {
        let neg = F064F016.ceil(ExtendedFloat::Extend(-0.0_f64));
        match neg {
            ExtendedFloat::Extend(v) => assert!(v.is_sign_negative()),
            _ => panic!("expected Extend(-0)"),
        }
    }

    #[test]
    fn f16_ceil_nan() {
        match F064F016.ceil(ExtendedFloat::Extend(f64::NAN)) {
            ExtendedFloat::Extend(v) => assert!(v.is_nan()),
            _ => panic!("expected Extend(NaN)"),
        }
    }

    #[test]
    fn f16_pos_inf_preserved() {
        assert_eq!(
            F064F016.ceil(ExtendedFloat::Extend(f64::INFINITY)),
            ExtendedFloat::Extend(f16::INFINITY),
        );
    }

    #[test]
    fn f16_f64_max_saturates_to_inf() {
        // f64::MAX (≈ 1.8e308) is far above f16::MAX (65504). RNE → ∞.
        assert_eq!(
            F064F016.ceil(ExtendedFloat::Extend(f64::MAX)),
            ExtendedFloat::Extend(f16::INFINITY),
        );
    }

    #[test]
    fn f16_bot_top_pass_through() {
        assert_eq!(F064F016.ceil(ExtendedFloat::Bot), ExtendedFloat::Bot);
        assert_eq!(F064F016.floor(ExtendedFloat::Bot), ExtendedFloat::Bot);
        assert_eq!(F064F016.ceil(ExtendedFloat::Top), ExtendedFloat::Top);
        assert_eq!(F064F016.floor(ExtendedFloat::Top), ExtendedFloat::Top);
        assert_eq!(F064F016.inner(ExtendedFloat::Bot), ExtendedFloat::Bot);
        assert_eq!(F064F016.inner(ExtendedFloat::Top), ExtendedFloat::Top);
    }

    // ── F064B016 spot checks ───────────────────────────────────────

    #[test]
    fn b16_neg_zero_sign_preserved() {
        let neg = F064B016.ceil(ExtendedFloat::Extend(-0.0_f64));
        match neg {
            ExtendedFloat::Extend(v) => assert!(v.is_sign_negative()),
            _ => panic!("expected Extend(-0)"),
        }
    }

    #[test]
    fn b16_ceil_nan() {
        match F064B016.ceil(ExtendedFloat::Extend(f64::NAN)) {
            ExtendedFloat::Extend(v) => assert!(v.is_nan()),
            _ => panic!("expected Extend(NaN)"),
        }
    }

    #[test]
    fn b16_pos_inf_preserved() {
        assert_eq!(
            F064B016.ceil(ExtendedFloat::Extend(f64::INFINITY)),
            ExtendedFloat::Extend(bf16::INFINITY),
        );
    }

    #[test]
    fn b16_f64_max_saturates_to_inf() {
        // f64::MAX (≈ 1.8e308) is far above bf16::MAX (≈ 3.39e38). RNE → ∞.
        assert_eq!(
            F064B016.ceil(ExtendedFloat::Extend(f64::MAX)),
            ExtendedFloat::Extend(bf16::INFINITY),
        );
    }

    #[test]
    fn b16_bot_top_pass_through() {
        assert_eq!(F064B016.ceil(ExtendedFloat::Bot), ExtendedFloat::Bot);
        assert_eq!(F064B016.floor(ExtendedFloat::Bot), ExtendedFloat::Bot);
        assert_eq!(F064B016.ceil(ExtendedFloat::Top), ExtendedFloat::Top);
        assert_eq!(F064B016.floor(ExtendedFloat::Top), ExtendedFloat::Top);
        assert_eq!(F064B016.inner(ExtendedFloat::Bot), ExtendedFloat::Bot);
        assert_eq!(F064B016.inner(ExtendedFloat::Top), ExtendedFloat::Top);
    }
}
