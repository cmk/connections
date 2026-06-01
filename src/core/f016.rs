//! [`F016`](crate::float::F016) (`ExtendedFloat<f16>`) plus the 16-bit
//! ULP machinery used by the source-hosted half-precision Conns.
//!
//! [`crate::core::f032::F032F016`] and [`crate::core::f064::F064F016`]
//! live in their source modules; this module supplies the rounding
//! helpers shared between them. The `F016` type alias itself lives in
//! [`crate::float`] alongside [`F032`](crate::float::F032) and
//! [`F064`](crate::float::F064) — keep all three float aliases in one
//! place rather than scattering them across the per-width modules.
//!
//! The whole module is gated on the `f16` cargo feature (declared
//! `#[cfg(feature = "f16")] pub mod f016;` in the parent), which
//! requires nightly Rust.

use crate::float::{
    ExtendedFloat, def_walk_helpers, float_ext_int, float_ext_int_l, impl_float_ext,
};

impl_float_ext!(f16);

// ── 16-bit ULP machinery ───────────────────────────────────────────

pub(crate) fn signed16(x: u16) -> i32 {
    if x < 0x8000 {
        x as i32
    } else {
        0x7FFF_i32 - (x as i32)
    }
}

pub(crate) fn unsigned16(i: i32) -> u16 {
    if i >= 0 {
        i as u16
    } else {
        (0x7FFF_i32 - i) as u16
    }
}

pub(crate) fn clamp16_f16(x: i32) -> i32 {
    x.clamp(-31745, 31744)
}

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

pub(crate) fn widen_f16_f32(x: f16) -> f32 {
    x as f32
}

pub(crate) fn widen_f16_f64(x: f16) -> f64 {
    x as f64
}

def_walk_helpers!(f32_f16_walks, f32, f16, shift16_f16, widen_f16_f32);
def_walk_helpers!(f64_f16_walks, f64, f16, shift16_f16, widen_f16_f64);

pub(crate) fn ceil_f32_f16(x: f32) -> f16 {
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

pub(crate) fn floor_f32_f16(x: f32) -> f16 {
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

pub(crate) fn ceil_f64_f16(x: f64) -> f16 {
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

pub(crate) fn floor_f64_f16(x: f64) -> f16 {
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

// ── §2: f16 → Extended<intN> narrowing ───────────────────────────────

float_ext_int!  (
    /// `ExtendedFloat<f16> ↔ Extended<u8>` — full Galois triple.
    pub F016U008, f16, u8
);
float_ext_int_l!(
    /// `ExtendedFloat<f16> → Extended<u16>` — L-only.
    pub F016U016, f16, u16
);
float_ext_int_l!(
    /// `ExtendedFloat<f16> → Extended<u32>` — L-only.
    pub F016U032, f16, u32
);
float_ext_int_l!(
    /// `ExtendedFloat<f16> → Extended<u64>` — L-only.
    pub F016U064, f16, u64
);
float_ext_int!  (
    /// `ExtendedFloat<f16> ↔ Extended<i8>` — full Galois triple.
    pub F016I008, f16, i8
);
float_ext_int_l!(
    /// `ExtendedFloat<f16> → Extended<i16>` — L-only.
    pub F016I016, f16, i16
);
float_ext_int_l!(
    /// `ExtendedFloat<f16> → Extended<i32>` — L-only.
    pub F016I032, f16, i32
);
float_ext_int_l!(
    /// `ExtendedFloat<f16> → Extended<i64>` — L-only.
    pub F016I064, f16, i64
);

#[cfg(test)]
mod tests {
    use super::*;
    #[allow(unused_imports)]
    use crate::conn::{ConnL, ConnR};
    use crate::core::f032::F032F016;
    use crate::core::f064::F064F016;
    use crate::float::{F032, F064};
    use crate::prop::arb::{arb_f32, arb_f64, extended_float_f16 as ef16};
    use crate::prop::conn as conn_laws;
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

    #[test]
    fn signed16_round_trip() {
        for x in 0u16..=u16::MAX {
            assert_eq!(unsigned16(signed16(x)), x, "round-trip failed at {x:#x}");
        }
    }

    #[test]
    fn signed16_total_order_matches_float_order_f16() {
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

    proptest! {
        #![proptest_config(ProptestConfig {
            cases: 256,
            max_shrink_iters: 200,
            .. ProptestConfig::default()
        })]

        #[test]
        fn f032_galois_l(a in ef32(), b in ef16()) {
            prop_assert!(conn_laws::galois_l(&F032F016.conn_l(), a, b));
        }

        #[test]
        fn f032_galois_r(a in ef32(), b in ef16()) {
            prop_assert!(conn_laws::galois_r(&F032F016.conn_r(), a, b));
        }

        #[test]
        fn f032_floor_le_ceil(a in ef32()) {
            prop_assert!(conn_laws::floor_le_ceil(&F032F016, a));
        }

        #[test]
        fn f064_galois_l(a in ef64(), b in ef16()) {
            prop_assert!(conn_laws::galois_l(&F064F016.conn_l(), a, b));
        }

        #[test]
        fn f064_galois_r(a in ef64(), b in ef16()) {
            prop_assert!(conn_laws::galois_r(&F064F016.conn_r(), a, b));
        }

        #[test]
        fn f064_floor_le_ceil(a in ef64()) {
            prop_assert!(conn_laws::floor_le_ceil(&F064F016, a));
        }
    }

    use crate::extended::Extended;
    use crate::prop::arb::{
        arb_extended_i8, arb_extended_i16, arb_extended_i32, arb_extended_i64, arb_extended_u8,
        arb_extended_u16, arb_extended_u32, arb_extended_u64,
    };

    #[test]
    fn f016u008_exact() {
        assert_eq!(
            crate::conn::ceil(&F016U008, ExtendedFloat::Extend(42.0_f16)),
            Extended::Finite(42_u8),
        );
    }

    #[test]
    fn f016u016_max_finite_f16_in_range() {
        assert_eq!(
            crate::conn::ceil(&F016U016, ExtendedFloat::Extend(f16::MAX)),
            Extended::Finite(65504_u16),
        );
    }

    #[test]
    fn f016i008_saturate() {
        let huge = ExtendedFloat::Extend(1000.0_f16);
        assert_eq!(crate::conn::ceil(&F016I008, huge), Extended::PosInf);
    }

    crate::law_battery! { mod laws_u008, conn: F016U008, fine: ef16(), coarse: arb_extended_u8(), }
    crate::law_battery! { mod laws_u016, conn: F016U016, fine: ef16(), coarse: arb_extended_u16(), subset: l_only, }
    crate::law_battery! { mod laws_u032, conn: F016U032, fine: ef16(), coarse: arb_extended_u32(), subset: l_only, }
    crate::law_battery! { mod laws_u064, conn: F016U064, fine: ef16(), coarse: arb_extended_u64(), subset: l_only, }
    crate::law_battery! { mod laws_i008, conn: F016I008, fine: ef16(), coarse: arb_extended_i8(), }
    crate::law_battery! { mod laws_i016, conn: F016I016, fine: ef16(), coarse: arb_extended_i16(), subset: l_only, }
    crate::law_battery! { mod laws_i032, conn: F016I032, fine: ef16(), coarse: arb_extended_i32(), subset: l_only, }
    crate::law_battery! { mod laws_i064, conn: F016I064, fine: ef16(), coarse: arb_extended_i64(), subset: l_only, }
}
