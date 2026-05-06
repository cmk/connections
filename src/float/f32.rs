//! Conns whose target is [`F032`] (`ExtendedFloat<f32>`).
//!
//! Houses [`F064F032`] (`ExtendedFloat<f64> → ExtendedFloat<f32>`).
//!
//! Per the placement rule (CLAUDE.md § Conn placement: same-tier tie
//! → right wins), `F064F032` lives here rather than under `f64`.

use super::{ExtendedFloat, F032, F064, def_walk_helpers, shift32, widen_f32_f64};
#[cfg(test)]
#[allow(unused_imports)]
use crate::conn::Conn;

def_walk_helpers!(f64_f32_walks, f64, f32, shift32, widen_f32_f64);

fn f064f032_ceil(x: F064) -> F032 {
    match x {
        ExtendedFloat::Bot => ExtendedFloat::Bot,
        ExtendedFloat::Top => ExtendedFloat::Top,
        ExtendedFloat::Extend(v) => ExtendedFloat::Extend(ceil_f64_f32(v)),
    }
}
fn f064f032_inner(y: F032) -> F064 {
    match y {
        ExtendedFloat::Bot => ExtendedFloat::Bot,
        ExtendedFloat::Top => ExtendedFloat::Top,
        ExtendedFloat::Extend(v) => ExtendedFloat::Extend(v as f64),
    }
}
fn f064f032_floor(x: F064) -> F032 {
    match x {
        ExtendedFloat::Bot => ExtendedFloat::Bot,
        ExtendedFloat::Top => ExtendedFloat::Top,
        ExtendedFloat::Extend(v) => ExtendedFloat::Extend(floor_f64_f32(v)),
    }
}

crate::conn_k! {
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
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::conn::{ConnL, ConnR};
    /// use connections::float::f32::F064F032;
    /// use connections::float::ExtendedFloat;
    ///
    /// // π is not exactly representable in either f32 or f64.
    /// // ceil walks up to the smallest f32 whose f64 embedding ≥ π;
    /// // floor walks down to the largest f32 whose f64 embedding ≤ π.
    /// let pi_f64 = ExtendedFloat::Extend(core::f64::consts::PI);
    /// let lo = F064F032.floor(pi_f64);
    /// let hi = F064F032.ceil(pi_f64);
    /// assert!(matches!(lo, ExtendedFloat::Extend(_)));
    /// assert!(matches!(hi, ExtendedFloat::Extend(_)));
    /// // Embedding the bracket back to f64 sandwiches the original.
    /// let lo_back = F064F032.upper(lo);
    /// let hi_back = F064F032.upper(hi);
    /// assert!(lo_back <= pi_f64 && pi_f64 <= hi_back);
    ///
    /// // Sentinel pass-through.
    /// assert_eq!(F064F032.ceil(ExtendedFloat::Bot), ExtendedFloat::Bot);
    /// assert_eq!(F064F032.floor(ExtendedFloat::Top), ExtendedFloat::Top);
    /// ```
    pub F064F032 : F064 => F032 {
        ceil:  f064f032_ceil,
        inner: f064f032_inner,
        floor: f064f032_floor,
    }
}

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

// ── Proof-only walk-step probes ─────────────────────────────────────
//
// Mirror `ceil_f64_f32` / `floor_f64_f32` above but return the
// `(z, steps)` tuple from each walk helper instead of dropping
// `_steps`. Used by the Kani harnesses in
// [`crate::kani_proofs::float_walk`] to prove the iteration bound
// is ≤ 2 over the *full* finite-non-NaN domain rather than a
// proptest sample. Gated on `cfg(kani)` so they compile only under
// `cargo kani`.
#[cfg(kani)]
pub(crate) fn ceil_walk_steps_for_proof(x: f64) -> (f32, u32) {
    let est = x as f32;
    let est_up = est as f64;
    if est_up == x {
        return (est, 0);
    }
    if x <= est_up {
        f64_f32_walks::descend_to_ceil(est, x)
    } else {
        f64_f32_walks::ascend_to_ceil(est, x)
    }
}

#[cfg(kani)]
pub(crate) fn floor_walk_steps_for_proof(x: f64) -> (f32, u32) {
    let est = x as f32;
    let est_up = est as f64;
    if est_up == x {
        return (est, 0);
    }
    if est_up <= x {
        f64_f32_walks::ascend_to_floor(est, x)
    } else {
        f64_f32_walks::descend_to_floor(est, x)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[allow(unused_imports)]
    use crate::conn::{ConnL, ConnR};
    use crate::prop::arb::{arb_f32, arb_f64};
    use crate::prop::conn as conn_laws;
    use proptest::prelude::*;

    /// Local strategy: `ExtendedFloat<f64>` over `Bot`, `Top`, and full-
    /// range `Extend(_)` (8:1:1 weighting toward the extension slot).
    /// Unlike [`crate::prop::arb::extended_float_f64`] which uses
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
        match F064F032.upper(ExtendedFloat::Extend(f32::NAN)) {
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
        assert_eq!(F064F032.upper(ExtendedFloat::Bot), ExtendedFloat::Bot);
        assert_eq!(F064F032.upper(ExtendedFloat::Top), ExtendedFloat::Top);
    }

    // ── Property tests ─────────────────────────────────────────────

    crate::law_battery! {
        mod laws,
        conn: F064F032,
        fine:   ef64(),
        coarse: ef32(),
        subset: numeric_only,
    }

    proptest! {
        #[test]
        fn floor_le_ceil(a in ef64()) {
            prop_assert!(conn_laws::floor_le_ceil(&F064F032, a));
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

        // `ulp_bound` is intentionally omitted for `F064F032`.
        // The predicate's `rung: F where F: Fn(B) -> i64` extractor
        // is documented (`laws.rs:439-447`) as "specific to integer-
        // tier connections (the rung types have an i64 payload)".
        // For float Conns, ULP is bit-level (mantissa increment), a
        // different concept — and there is no clean i64 mapping for
        // `ExtendedFloat<f32>` (Bot / Top would have to alias to
        // sentinel ints, which isn't a meaningful "rung distance").
    }
}
