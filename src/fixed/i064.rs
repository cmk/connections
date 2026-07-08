//! Binary fixed-point ladder over `fixed::FixedI64<Frac>`, plus the
//! cross-crate iso to `i64` and the IEEE-float → `FixedI64<F>` bridges.
//!
//! Pure-`core` Conns sourced from `i64` live next door in
//! [`crate::core::i064`].

use super::float_fixed_l;
use ::fixed::FixedI64;
use ::fixed::types::extra::{U0, U8, U16, U32, U48, U63, U64, Unsigned};

// ── Cross-crate isos: FixedI64<U*> ↔ i64 ──────────────────────────

const fn q000i064_fwd(q: FixedI64<U0>) -> i64 {
    q.to_bits()
}
const fn q000i064_bk(i: i64) -> FixedI64<U0> {
    FixedI64::<U0>::from_bits(i)
}

const fn q063i064_fwd(q: FixedI64<U63>) -> i64 {
    q.to_bits()
}
const fn q063i064_bk(i: i64) -> FixedI64<U63> {
    FixedI64::<U63>::from_bits(i)
}

crate::iso! {
    /// `FixedI64<U0> ↔ i64` — Q64.0 lossless iso. Degenerate Galois.
    pub Q000I064 : FixedI64<U0> => i64 {
        forward: q000i064_fwd,
        back:    q000i064_bk,
    }
}

crate::iso! {
    /// `FixedI64<U63> ↔ i64` — signed normalized Q1.63 lossless bit iso.
    /// Numeric Q values cover `[-1, 1 - 2^-63]`; the primitive carries
    /// the same two's-complement storage bits.
    pub Q063I064 : FixedI64<U63> => i64 {
        forward: q063i064_fwd,
        back:    q063i064_bk,
    }
}

// ── Q-format ladder over `FixedI64<Frac>` ──────────────────────────

pub type I000 = FixedI64<U0>;
pub type I008 = FixedI64<U8>;
pub type I016 = FixedI64<U16>;
pub type I032 = FixedI64<U32>;
pub type I048 = FixedI64<U48>;
pub type I064 = FixedI64<U64>;

macro_rules! fix_fix_i64 {
    ($const_name:ident, $FineFrac:ty, $CoarseFrac:ty) => {
#[rustfmt::skip]
        #[doc = concat!(
            "`FixedI64<",
            stringify!($FineFrac),
            "> → FixedI64<",
            stringify!($CoarseFrac),
            ">` frac-level convert (i64-backed)."
        )]
        pub const $const_name: $crate::conn::Conn<FixedI64<$FineFrac>, FixedI64<$CoarseFrac>> = {
            const SHIFT: u32 = <$FineFrac as Unsigned>::U32 - <$CoarseFrac as Unsigned>::U32;
            const RATIO: i128 = 1_i128 << SHIFT;
            const FINE_MIN: i64 = i64::MIN;
            const FINE_MAX: i64 = i64::MAX;

            fn ceil(x: FixedI64<$FineFrac>) -> FixedI64<$CoarseFrac> {
                if x.to_bits() == FINE_MIN {
                    return FixedI64::<$CoarseFrac>::from_bits(i64::MIN);
                }
                let bits = x.to_bits() as i128;
                let q = bits.div_euclid(RATIO);
                let r = bits.rem_euclid(RATIO);
                let res = if r != 0 { q + 1 } else { q };
                FixedI64::from_bits(res as i64)
            }

            fn inner(x: FixedI64<$CoarseFrac>) -> FixedI64<$FineFrac> {
                let res = (x.to_bits() as i128) * RATIO;
                let saturated = if res > FINE_MAX as i128 {
                    FINE_MAX
                } else if res < FINE_MIN as i128 {
                    FINE_MIN
                } else {
                    res as i64
                };
                FixedI64::from_bits(saturated)
            }

            $crate::conn::Conn::new_l(ceil, inner)
        };
    };
}

fix_fix_i64!(Q008Q000, U8, U0);
fix_fix_i64!(Q016Q000, U16, U0);
fix_fix_i64!(Q032Q000, U32, U0);
fix_fix_i64!(Q048Q000, U48, U0);
fix_fix_i64!(Q064Q000, U64, U0);
fix_fix_i64!(Q016Q008, U16, U8);
fix_fix_i64!(Q032Q008, U32, U8);
fix_fix_i64!(Q048Q008, U48, U8);
fix_fix_i64!(Q064Q008, U64, U8);
fix_fix_i64!(Q032Q016, U32, U16);
fix_fix_i64!(Q048Q016, U48, U16);
fix_fix_i64!(Q064Q016, U64, U16);
fix_fix_i64!(Q048Q032, U48, U32);
fix_fix_i64!(Q064Q032, U64, U32);
fix_fix_i64!(Q064Q048, U64, U48);

// ── f32 / f64 / f16 → FixedI64<U<frac>> narrowing (all L-only) ────

float_fixed_l!(pub F032Q000, f32, FixedI64, U0,  i64);
float_fixed_l!(pub F032Q008, f32, FixedI64, U8,  i64);
float_fixed_l!(pub F032Q016, f32, FixedI64, U16, i64);
float_fixed_l!(pub F032Q032, f32, FixedI64, U32, i64);
float_fixed_l!(pub F032Q048, f32, FixedI64, U48, i64);
float_fixed_l!(pub F032Q064, f32, FixedI64, U64, i64);

float_fixed_l!(pub F064Q000, f64, FixedI64, U0,  i64);
float_fixed_l!(pub F064Q008, f64, FixedI64, U8,  i64);
float_fixed_l!(pub F064Q016, f64, FixedI64, U16, i64);
float_fixed_l!(pub F064Q032, f64, FixedI64, U32, i64);
float_fixed_l!(pub F064Q048, f64, FixedI64, U48, i64);
float_fixed_l!(pub F064Q064, f64, FixedI64, U64, i64);

#[cfg(feature = "f16")]
float_fixed_l!(pub F016Q000, f16, FixedI64, U0,  i64);
#[cfg(feature = "f16")]
float_fixed_l!(pub F016Q008, f16, FixedI64, U8,  i64);
#[cfg(feature = "f16")]
float_fixed_l!(pub F016Q016, f16, FixedI64, U16, i64);
#[cfg(feature = "f16")]
float_fixed_l!(pub F016Q032, f16, FixedI64, U32, i64);
#[cfg(feature = "f16")]
float_fixed_l!(pub F016Q048, f16, FixedI64, U48, i64);
#[cfg(feature = "f16")]
float_fixed_l!(pub F016Q064, f16, FixedI64, U64, i64);

// ────────────────────────────────────────────────────────────────────
// Tests
// ────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    #[allow(unused_imports)]
    use crate::conn::{ConnL, ConnR};
    use proptest::prelude::*;

    #[test]
    fn spot_q032q016_on_grid() {
        let bits_3232: i64 = 3 << 31;
        let q3232 = FixedI64::<U32>::from_bits(bits_3232);
        assert_eq!(Q032Q016.ceil(q3232), FixedI64::<U16>::from_bits(3 << 15));
    }

    #[test]
    fn spot_q064q000_degenerate() {
        assert_eq!(
            Q064Q000.upper(FixedI64::<U0>::from_bits(0)),
            FixedI64::<U64>::from_bits(0),
        );
        assert_eq!(
            Q064Q000.upper(FixedI64::<U0>::from_bits(1)),
            FixedI64::<U64>::from_bits(i64::MAX),
        );
        assert_eq!(
            Q064Q000.upper(FixedI64::<U0>::from_bits(-1)),
            FixedI64::<U64>::from_bits(i64::MIN),
        );
    }

    #[test]
    fn spot_boundary_fixups() {
        let fmin = FixedI64::<U32>::from_bits(i64::MIN);
        assert_eq!(Q032Q016.ceil(fmin), FixedI64::<U16>::from_bits(i64::MIN));
    }

    macro_rules! props_for_pair {
        ($mod_name:ident, $conn:ident, $FineFrac:ty, $CoarseFrac:ty) => {
            $crate::law_battery! {
                mod $mod_name,
                conn: $conn,
                fine:   prop_oneof![
                    1 => Just(FixedI64::<$FineFrac>::from_bits(i64::MIN)),
                    1 => Just(FixedI64::<$FineFrac>::from_bits(i64::MAX)),
                    1 => Just(FixedI64::<$FineFrac>::from_bits(0)),
                    8 => any::<i64>().prop_map(FixedI64::<$FineFrac>::from_bits),
                ],
                coarse: prop_oneof![
                    1 => Just(FixedI64::<$CoarseFrac>::from_bits(i64::MIN)),
                    1 => Just(FixedI64::<$CoarseFrac>::from_bits(i64::MAX)),
                    1 => Just(FixedI64::<$CoarseFrac>::from_bits(0)),
                    8 => any::<i64>().prop_map(FixedI64::<$CoarseFrac>::from_bits),
                ],
                subset: l_only,
                cases: 64,
            }
        };
    }

    props_for_pair!(q008q000, Q008Q000, U8, U0);
    props_for_pair!(q016q000, Q016Q000, U16, U0);
    props_for_pair!(q032q000, Q032Q000, U32, U0);
    props_for_pair!(q048q000, Q048Q000, U48, U0);
    props_for_pair!(q064q000, Q064Q000, U64, U0);
    props_for_pair!(q016q008, Q016Q008, U16, U8);
    props_for_pair!(q032q008, Q032Q008, U32, U8);
    props_for_pair!(q048q008, Q048Q008, U48, U8);
    props_for_pair!(q064q008, Q064Q008, U64, U8);
    props_for_pair!(q032q016, Q032Q016, U32, U16);
    props_for_pair!(q048q016, Q048Q016, U48, U16);
    props_for_pair!(q064q016, Q064Q016, U64, U16);
    props_for_pair!(q048q032, Q048Q032, U48, U32);
    props_for_pair!(q064q032, Q064Q032, U64, U32);
    props_for_pair!(q064q048, Q064Q048, U64, U48);

    #[test]
    fn f064q000_above_max_to_posinf() {
        let above_max = (i64::MAX as f64) * 2.0_f64.powi(0); // = 2^63
        let v = crate::float::N5::new(above_max);
        assert_eq!(F064Q000.ceil(v), crate::extended::Extended::PosInf);
    }

    #[test]
    fn f064q008_above_max_to_posinf() {
        let above_max = (i64::MAX as f64) / 256.0_f64; // = 2^55
        let v = crate::float::N5::new(above_max);
        assert_eq!(F064Q008.ceil(v), crate::extended::Extended::PosInf);
    }
}
