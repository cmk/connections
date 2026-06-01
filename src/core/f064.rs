//! Conns sourced from [`crate::float::F064`] (`ExtendedFloat<f64>`).
//!
//! Houses:
//!
//! - [`F064F032`] and (with `f16` feature) `F064F016` — float narrowing.
//! - `F064U032` / `F064I032` — full Galois triples.
//! - `F064U064` / `F064I064` — L-only.
//! - `F064U008` / `F064U016` / `F064I008` / `F064I016` — composed
//!   triples derived from `F032<X> ∘ F064F032`.

#[cfg(feature = "f16")]
use super::f016::{ceil_f64_f16, floor_f64_f16};
use super::f032::{F032I008, F032I016, F032U008, F032U016};
#[cfg(test)]
#[allow(unused_imports)]
use crate::conn::Conn;
#[cfg(feature = "f16")]
use crate::float::F016;
use crate::float::{
    ExtendedFloat, F032, F064, def_walk_helpers, float_ext_int, float_ext_int_l, shift32,
    widen_f32_f64,
};

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
#[cfg_attr(docsrs, doc(cfg(feature = "f16")))]
crate::conn_k! {
    /// Direct `f64 ↔ f16` narrowing under the N5 lattice.
    ///
    /// ```
    /// # #![feature(f16)]
    /// use connections::core::f064::F064F016;
    /// use connections::float::ExtendedFloat::Extend;
    ///
    /// // PI's f16 ceiling — the next f16 grid point above PI.
    /// let pi_f64 = Extend(std::f64::consts::PI);
    /// let pi_f16_ceil = Extend(3.142_578_125_f16);
    ///
    /// assert_eq!(connections::conn::ceil(&F064F016, pi_f64), pi_f16_ceil);
    /// // Widening back to f64 picks up the f16 grid point exactly:
    /// assert_eq!(connections::conn::upper(&F064F016, pi_f16_ceil), Extend(3.142_578_125_f64));
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
    /// Connection between [`crate::float::F064`] and [`crate::float::F032`]
    /// under the N5 lattice ordering.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::conn::{ConnL, ConnR};
    /// use connections::core::f064::F064F032;
    /// use connections::float::ExtendedFloat::Extend;
    ///
    /// // PI in f64-precision and the two f32 grid points that bracket it.
    /// // The error term `pi32_err ≈ +8.74e-8` is the f32 round-off on PI.
    /// let pi_f64 = Extend(std::f64::consts::PI);
    /// let pi_f32_floor = Extend(3.141_592_502_593_994_f64);
    /// let pi_f32_ceil  = Extend(std::f32::consts::PI as f64);
    ///
    /// assert_eq!(connections::conn::floor(&F064F032, pi_f64), Extend(3.141_592_502_593_994_f64 as f32));
    /// assert_eq!(connections::conn::ceil(&F064F032, pi_f64),  Extend(std::f32::consts::PI));
    /// // Widening lifts each f32 grid point to its exact f64 image.
    /// assert_eq!(connections::conn::upper(&F064F032, connections::conn::floor(&F064F032, pi_f64)), pi_f32_floor);
    /// assert_eq!(connections::conn::upper(&F064F032, connections::conn::ceil(&F064F032, pi_f64)),  pi_f32_ceil);
    ///
    /// // Sentinel pass-through.
    /// use connections::float::ExtendedFloat;
    /// assert_eq!(connections::conn::ceil(&F064F032, ExtendedFloat::Bot),  ExtendedFloat::Bot);
    /// assert_eq!(connections::conn::floor(&F064F032, ExtendedFloat::Top), ExtendedFloat::Top);
    /// ```
    pub F064F032 : F064 => F032 {
        ceil:  f064f032_ceil,
        inner: f064f032_inner,
        floor: f064f032_floor,
    }
}

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

float_ext_int!  (
    /// `ExtendedFloat<f64> ↔ Extended<u32>` — full Galois triple.
    pub F064U032, f64, u32
);
float_ext_int_l!(
    /// `ExtendedFloat<f64> → Extended<u64>` — L-only.
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
    /// `F064F032` ∘ `F032U008`.
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

    #[test]
    fn ceil_exact_value() {
        assert_eq!(
            crate::conn::ceil(&F064F032, ExtendedFloat::Extend(0.5_f64)),
            ExtendedFloat::Extend(0.5_f32)
        );
    }

    #[test]
    fn floor_exact_value() {
        assert_eq!(
            crate::conn::floor(&F064F032, ExtendedFloat::Extend(0.5_f64)),
            ExtendedFloat::Extend(0.5_f32)
        );
    }

    #[test]
    fn ceil_nan() {
        match crate::conn::ceil(&F064F032, ExtendedFloat::Extend(f64::NAN)) {
            ExtendedFloat::Extend(v) => assert!(v.is_nan()),
            _ => panic!("expected Extend(NaN)"),
        }
    }

    #[test]
    fn floor_nan() {
        match crate::conn::floor(&F064F032, ExtendedFloat::Extend(f64::NAN)) {
            ExtendedFloat::Extend(v) => assert!(v.is_nan()),
            _ => panic!("expected Extend(NaN)"),
        }
    }

    #[test]
    fn inner_nan() {
        match crate::conn::upper(&F064F032, ExtendedFloat::Extend(f32::NAN)) {
            ExtendedFloat::Extend(v) => assert!(v.is_nan()),
            _ => panic!("expected Extend(NaN)"),
        }
    }

    #[test]
    fn ceil_ge_floor() {
        let x = ExtendedFloat::Extend(std::f64::consts::PI);
        assert!(crate::conn::floor(&F064F032, x) <= crate::conn::ceil(&F064F032, x));
    }

    #[test]
    fn bot_top_pass_through() {
        assert_eq!(
            crate::conn::ceil(&F064F032, ExtendedFloat::Bot),
            ExtendedFloat::Bot
        );
        assert_eq!(
            crate::conn::floor(&F064F032, ExtendedFloat::Bot),
            ExtendedFloat::Bot
        );
        assert_eq!(
            crate::conn::ceil(&F064F032, ExtendedFloat::Top),
            ExtendedFloat::Top
        );
        assert_eq!(
            crate::conn::floor(&F064F032, ExtendedFloat::Top),
            ExtendedFloat::Top
        );
        assert_eq!(
            crate::conn::upper(&F064F032, ExtendedFloat::Bot),
            ExtendedFloat::Bot
        );
        assert_eq!(
            crate::conn::upper(&F064F032, ExtendedFloat::Top),
            ExtendedFloat::Top
        );
    }

    crate::law_battery! { mod laws, conn: F064F032, fine: ef64(), coarse: ef32(), subset: numeric_only, }

    proptest! {
        #[test]
        fn floor_le_ceil(a in ef64()) {
            prop_assert!(conn_laws::floor_le_ceil(&F064F032, a));
        }

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
    }

    use crate::extended::Extended;
    use crate::prop::arb::{
        arb_extended_i8, arb_extended_i16, arb_extended_i32, arb_extended_i64, arb_extended_u8,
        arb_extended_u16, arb_extended_u32, arb_extended_u64, extended_float_f64,
    };

    #[test]
    fn f064i032_exact_int() {
        assert_eq!(
            crate::conn::ceil(&F064I032, ExtendedFloat::Extend(2.5_f64)),
            Extended::Finite(3_i32)
        );
        assert_eq!(
            crate::conn::floor(&F064I032, ExtendedFloat::Extend(2.5_f64)),
            Extended::Finite(2_i32)
        );
    }

    #[test]
    fn f064u064_saturate_high() {
        let huge = ExtendedFloat::Extend(1.0e30_f64);
        assert_eq!(crate::conn::ceil(&F064U064, huge), Extended::PosInf);
    }

    #[test]
    fn f064i064_saturate_low() {
        let huge_neg = ExtendedFloat::Extend(-1.0e30_f64);
        assert_eq!(
            crate::conn::ceil(&F064I064, huge_neg),
            Extended::Finite(i64::MIN)
        );
    }

    #[test]
    fn f064u064_at_plateau_to_posinf() {
        let plateau = ExtendedFloat::Extend(2.0_f64.powi(64));
        assert_eq!(crate::conn::ceil(&F064U064, plateau), Extended::PosInf);
    }

    #[test]
    fn f064i064_at_plateau_to_posinf() {
        let plateau = ExtendedFloat::Extend(2.0_f64.powi(63));
        assert_eq!(crate::conn::ceil(&F064I064, plateau), Extended::PosInf);
    }

    #[test]
    fn f064u064_just_past_plateau_to_posinf() {
        let v = f64::from_bits(2.0_f64.powi(64).to_bits() + 1);
        assert_eq!(
            crate::conn::ceil(&F064U064, ExtendedFloat::Extend(v)),
            Extended::PosInf,
        );
    }

    #[test]
    fn f064i064_just_past_plateau_to_posinf() {
        let v = f64::from_bits(2.0_f64.powi(63).to_bits() + 1);
        assert_eq!(
            crate::conn::ceil(&F064I064, ExtendedFloat::Extend(v)),
            Extended::PosInf,
        );
    }

    #[test]
    fn f064u008_composed_matches_direct_path() {
        let v = ExtendedFloat::Extend(42.7_f64);
        assert_eq!(crate::conn::ceil(&F064U008, v), Extended::Finite(43));
        assert_eq!(crate::conn::floor(&F064U008, v), Extended::Finite(42));
    }

    crate::law_battery! { mod laws_u032, conn: F064U032, fine: extended_float_f64(), coarse: arb_extended_u32(), cases: 1024, }
    crate::law_battery! { mod laws_u064, conn: F064U064, fine: extended_float_f64(), coarse: arb_extended_u64(), subset: l_only, cases: 1024, }
    crate::law_battery! { mod laws_i032, conn: F064I032, fine: extended_float_f64(), coarse: arb_extended_i32(), cases: 1024, }
    crate::law_battery! { mod laws_i064, conn: F064I064, fine: extended_float_f64(), coarse: arb_extended_i64(), subset: l_only, cases: 1024, }
    crate::law_battery! { mod laws_u008_composed, conn: F064U008, fine: extended_float_f64(), coarse: arb_extended_u8(), cases: 1024, }
    crate::law_battery! { mod laws_u016_composed, conn: F064U016, fine: extended_float_f64(), coarse: arb_extended_u16(), cases: 1024, }
    crate::law_battery! { mod laws_i008_composed, conn: F064I008, fine: extended_float_f64(), coarse: arb_extended_i8(), cases: 1024, }
    crate::law_battery! { mod laws_i016_composed, conn: F064I016, fine: extended_float_f64(), coarse: arb_extended_i16(), cases: 1024, }
}
