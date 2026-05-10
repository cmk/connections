//! Conns sourced from [`F064`] (`ExtendedFloat<f64>`).
//!
//! Houses:
//!
//! - [`F064F032`] (`ExtendedFloat<f64> → ExtendedFloat<f32>`) and,
//!   with the `f16` cargo feature, `F064F016`.
//! - `F064U032` / `F064I032` — full Galois triples for targets that
//!   fit in the f64 mantissa.
//! - `F064U064` / `F064I064` — L-only Conns where target precision
//!   exceeds the f64 mantissa.
//! - `F064U008` / `F064U016` / `F064I008` / `F064I016` — composed
//!   triples derived from `F032<X> ∘ F064F032` (the small-target
//!   subset where narrowing through f32 is exact).

#[cfg(feature = "f16")]
use super::f016::{F016, ceil_f64_f16, floor_f64_f16};
use super::f032::{F032I008, F032I016, F032U008, F032U016};
use super::{
    ExtendedFloat, F032, F064, def_walk_helpers, float_ext_int, float_ext_int_l, shift32,
    widen_f32_f64,
};
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

#[cfg(feature = "f16")]
fn f064f016_ceil(x: F064) -> F016 {
    match x {
        ExtendedFloat::Bot => ExtendedFloat::Bot,
        ExtendedFloat::Top => ExtendedFloat::Top,
        ExtendedFloat::Extend(v) => ExtendedFloat::Extend(ceil_f64_f16(v)),
    }
}

#[cfg(feature = "f16")]
fn f064f016_inner(y: F016) -> F064 {
    match y {
        ExtendedFloat::Bot => ExtendedFloat::Bot,
        ExtendedFloat::Top => ExtendedFloat::Top,
        ExtendedFloat::Extend(v) => ExtendedFloat::Extend(v as f64),
    }
}

#[cfg(feature = "f16")]
fn f064f016_floor(x: F064) -> F016 {
    match x {
        ExtendedFloat::Bot => ExtendedFloat::Bot,
        ExtendedFloat::Top => ExtendedFloat::Top,
        ExtendedFloat::Extend(v) => ExtendedFloat::Extend(floor_f64_f16(v)),
    }
}

#[cfg(feature = "f16")]
crate::conn_k! {
    /// Connection between [`super::F064`] and [`super::f016::F016`] under
    /// the N5 lattice — direct `f64 <-> f16` narrowing.
    ///
    /// ```
    /// # #![feature(f16)]
    /// use connections::float::f064::F064F016;
    /// use connections::float::ExtendedFloat::Extend;
    ///
    /// let pi = Extend(std::f64::consts::PI);
    /// let pi_up = F064F016.ceil(pi);
    /// assert!(F064F016.upper(pi_up) >= pi);
    /// ```
    pub F064F016 : F064 => F016 {
        ceil:  f064f016_ceil,
        inner: f064f016_inner,
        floor: f064f016_floor,
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
    /// use connections::float::f064::F064F032;
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
//
// The shims **deliberately omit** the production code's
// `if x.is_nan() { return f32::NAN; }` early-return: every harness
// that invokes them precedes the call with
// `kani::assume(x.is_finite() && !x.is_nan())`, which excludes NaN
// inputs at the SMT level. If a future refactor adds NaN-specific
// logic to `ceil_f64_f32` / `floor_f64_f32` (beyond the bare NaN
// pass-through), update the shims to mirror it — otherwise the
// proven bound applies only to the shim, not the production path.
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

// ── §2: Float → Extended<intN> narrowing ─────────────────────────────
//
// Direct: targets where precision exceeds the f32 mantissa
// (i32/u32/i64/u64). f64 mantissa is 53 bits, so i32/u32 ship as
// full triples and i64/u64 as L-only.
//
// Composed: targets ≤ 16 bits (i8/u8/i16/u16) compose
// `F064F032` ∘ `F032<X>` losslessly, since narrowing through f32 first
// is exact for these targets.

float_ext_int!  (
    /// `ExtendedFloat<f64> ↔ Extended<u32>` — full Galois triple
    /// (`u32::MAX` fits in the f64 mantissa).
    pub F064U032, f64, u32
);
float_ext_int_l!(
    /// `ExtendedFloat<f64> → Extended<u64>` — L-only (`u64::MAX`
    /// exceeds the f64 mantissa).
    pub F064U064, f64, u64
);
float_ext_int!  (
    /// `ExtendedFloat<f64> ↔ Extended<i32>` — full Galois triple.
    pub F064I032, f64, i32
);
float_ext_int_l!(
    /// `ExtendedFloat<f64> → Extended<i64>` — L-only.
    pub F064I064, f64, i64
);

crate::compose_k!(
    /// `ExtendedFloat<f64> → Extended<u8>` — composed triple via
    /// `F064F032` ∘ `F032U008`. Narrowing through f32 is exact for
    /// any `u8` value, so the composition has the same Galois shape
    /// as the direct primary.
    pub F064U008 : F064 => F032 => crate::extended::Extended<u8> = F064F032, F032U008
);
crate::compose_k!(
    /// `ExtendedFloat<f64> → Extended<u16>` — composed triple via
    /// `F064F032` ∘ `F032U016`.
    pub F064U016 : F064 => F032 => crate::extended::Extended<u16> = F064F032, F032U016
);
crate::compose_k!(
    /// `ExtendedFloat<f64> → Extended<i8>` — composed triple via
    /// `F064F032` ∘ `F032I008`.
    pub F064I008 : F064 => F032 => crate::extended::Extended<i8> = F064F032, F032I008
);
crate::compose_k!(
    /// `ExtendedFloat<f64> → Extended<i16>` — composed triple via
    /// `F064F032` ∘ `F032I016`.
    pub F064I016 : F064 => F032 => crate::extended::Extended<i16> = F064F032, F032I016
);

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

    // ── §2: Float → Extended<intN> spot checks + law batteries ─────

    use crate::extended::Extended;
    use crate::prop::arb::{
        arb_extended_i8, arb_extended_i16, arb_extended_i32, arb_extended_i64, arb_extended_u8,
        arb_extended_u16, arb_extended_u32, arb_extended_u64, extended_float_f64,
    };

    #[test]
    fn f064i032_exact_int() {
        // i32 fits in f64 mantissa, so the cast round-trips exactly.
        assert_eq!(
            F064I032.ceil(ExtendedFloat::Extend(2.5_f64)),
            Extended::Finite(3_i32),
        );
        assert_eq!(
            F064I032.floor(ExtendedFloat::Extend(2.5_f64)),
            Extended::Finite(2_i32),
        );
    }

    #[test]
    fn f064u064_saturate_high() {
        let huge = ExtendedFloat::Extend(1.0e30_f64);
        assert_eq!(F064U064.ceil(huge), Extended::PosInf);
    }

    #[test]
    fn f064i064_saturate_low() {
        let huge_neg = ExtendedFloat::Extend(-1.0e30_f64);
        assert_eq!(F064I064.ceil(huge_neg), Extended::Finite(i64::MIN));
    }

    // ── Boundary-saturation regression tests ──────────────────────
    //
    // For L-only Conns where `<int>::MAX as f64` rounds up (host
    // bits > 53), the f64 image of `MAX` is the smallest f64 grid
    // step *above* `MAX`. Without the boundary-saturation check in
    // `__float_ext_int_ceil_body!`, the strict `v > hi` guard misses
    // `v == hi`, and the saturating cast pins to `Finite(MAX)` for
    // an out-of-range input. Galois fails because
    // `inner(Finite(MAX))` rounds *down* below the f64 image.
    //
    // These tests pin the post-fix behavior: the f64 image of MAX
    // (and `next_up`) must classify as `PosInf`, not `Finite(MAX)`.

    #[test]
    fn f064u064_at_plateau_to_posinf() {
        // `2^64 = u64::MAX as f64` is already past the legal MAX
        // (u64::MAX = 2^64 - 1). The boundary-saturation check
        // detects the cast overflow and returns `PosInf`.
        let plateau = ExtendedFloat::Extend(2.0_f64.powi(64));
        assert_eq!(F064U064.ceil(plateau), Extended::PosInf);
    }

    #[test]
    fn f064i064_at_plateau_to_posinf() {
        let plateau = ExtendedFloat::Extend(2.0_f64.powi(63));
        assert_eq!(F064I064.ceil(plateau), Extended::PosInf);
    }

    #[test]
    fn f064u064_just_past_plateau_to_posinf() {
        let v = f64::from_bits(2.0_f64.powi(64).to_bits() + 1);
        assert_eq!(F064U064.ceil(ExtendedFloat::Extend(v)), Extended::PosInf,);
    }

    #[test]
    fn f064i064_just_past_plateau_to_posinf() {
        let v = f64::from_bits(2.0_f64.powi(63).to_bits() + 1);
        assert_eq!(F064I064.ceil(ExtendedFloat::Extend(v)), Extended::PosInf,);
    }

    #[test]
    fn f064u008_composed_matches_direct_path() {
        // `F064U008 = F064F032 ∘ F032U008` should agree with
        // narrowing `f64 -> f32` then casting `f32 -> u8`.
        let v = ExtendedFloat::Extend(42.7_f64);
        // ceil chain: F064F032.ceil → F032U008.ceil = Finite(43).
        assert_eq!(F064U008.ceil(v), Extended::Finite(43));
        assert_eq!(F064U008.floor(v), Extended::Finite(42));
    }

    crate::law_battery! {
        mod laws_u032,
        conn: F064U032,
        fine:   extended_float_f64(),
        coarse: arb_extended_u32(),
        cases: 1024,
    }
    crate::law_battery! {
        mod laws_u064,
        conn: F064U064,
        fine:   extended_float_f64(),
        coarse: arb_extended_u64(),
        subset: l_only,
        cases: 1024,
    }
    crate::law_battery! {
        mod laws_i032,
        conn: F064I032,
        fine:   extended_float_f64(),
        coarse: arb_extended_i32(),
        cases: 1024,
    }
    crate::law_battery! {
        mod laws_i064,
        conn: F064I064,
        fine:   extended_float_f64(),
        coarse: arb_extended_i64(),
        subset: l_only,
        cases: 1024,
    }
    crate::law_battery! {
        mod laws_u008_composed,
        conn: F064U008,
        fine:   extended_float_f64(),
        coarse: arb_extended_u8(),
        cases: 1024,
    }
    crate::law_battery! {
        mod laws_u016_composed,
        conn: F064U016,
        fine:   extended_float_f64(),
        coarse: arb_extended_u16(),
        cases: 1024,
    }
    crate::law_battery! {
        mod laws_i008_composed,
        conn: F064I008,
        fine:   extended_float_f64(),
        coarse: arb_extended_i8(),
        cases: 1024,
    }
    crate::law_battery! {
        mod laws_i016_composed,
        conn: F064I016,
        fine:   extended_float_f64(),
        coarse: arb_extended_i16(),
        cases: 1024,
    }
}
