//! Binary fixed-point ladder over `fixed::FixedU64<Frac>`, plus the
//! cross-crate iso to `u64` and the IEEE-float → `FixedU64<F>` bridges.
//!
//! Pure-`core` Conns sourced from `u64` live next door in
//! [`crate::core::u064`]. Frac level set:
//! `{F0, F8, F16, F32, F48, F63, F64}`; `F63` (Q1.63) is the
//! canonical 64-bit normalised-amplitude format.

use super::float_fixed_l;
use ::fixed::FixedU64;
use ::fixed::types::extra::{
    U0 as F0, U8 as F8, U16 as F16, U32 as F32, U48 as F48, U63 as F63, U64 as F64, Unsigned,
};

// ── Cross-crate iso: FixedU64<F0> ↔ u64 ───────────────────────────

const fn q000u064_fwd(q: FixedU64<F0>) -> u64 {
    q.to_bits()
}
const fn q000u064_bk(i: u64) -> FixedU64<F0> {
    FixedU64::<F0>::from_bits(i)
}

crate::iso! {
    /// `FixedU64<F0> ↔ u64` — Q64.0 unsigned lossless iso. Degenerate Galois.
    pub Q000U064 : FixedU64<F0> => u64 {
        forward: q000u064_fwd,
        back:    q000u064_bk,
    }
}

// ── Q-format ladder over `FixedU64<Frac>` ──────────────────────────

pub type U000 = FixedU64<F0>;
pub type U008 = FixedU64<F8>;
pub type U016 = FixedU64<F16>;
pub type U032 = FixedU64<F32>;
pub type U048 = FixedU64<F48>;
pub type U063 = FixedU64<F63>;
pub type U064 = FixedU64<F64>;

macro_rules! fix_fix_u64 {
    ($const_name:ident, $FineFrac:ty, $CoarseFrac:ty) => {
#[rustfmt::skip]
        #[doc = concat!(
            "`FixedU64<",
            stringify!($FineFrac),
            "> → FixedU64<",
            stringify!($CoarseFrac),
            ">` frac-level convert (u64-backed)."
        )]
        pub const $const_name: $crate::conn::Conn<FixedU64<$FineFrac>, FixedU64<$CoarseFrac>> = {
            const SHIFT: u32 = <$FineFrac as Unsigned>::U32 - <$CoarseFrac as Unsigned>::U32;
            const RATIO: u128 = 1_u128 << SHIFT;
            const FINE_MAX: u64 = u64::MAX;

            fn ceil(x: FixedU64<$FineFrac>) -> FixedU64<$CoarseFrac> {
                let bits = x.to_bits() as u128;
                let q = bits / RATIO;
                let r = bits % RATIO;
                let res = if r != 0 { q + 1 } else { q };
                FixedU64::from_bits(res as u64)
            }

            fn inner(x: FixedU64<$CoarseFrac>) -> FixedU64<$FineFrac> {
                let res = (x.to_bits() as u128) * RATIO;
                let saturated = if res > FINE_MAX as u128 {
                    FINE_MAX
                } else {
                    res as u64
                };
                FixedU64::from_bits(saturated)
            }

            $crate::conn::Conn::new_l(ceil, inner)
        };
    };
}

fix_fix_u64!(Q008Q000, F8, F0);
fix_fix_u64!(Q016Q000, F16, F0);
fix_fix_u64!(Q032Q000, F32, F0);
fix_fix_u64!(Q048Q000, F48, F0);
fix_fix_u64!(Q063Q000, F63, F0);
fix_fix_u64!(Q064Q000, F64, F0);
fix_fix_u64!(Q016Q008, F16, F8);
fix_fix_u64!(Q032Q008, F32, F8);
fix_fix_u64!(Q048Q008, F48, F8);
fix_fix_u64!(Q063Q008, F63, F8);
fix_fix_u64!(Q064Q008, F64, F8);
fix_fix_u64!(Q032Q016, F32, F16);
fix_fix_u64!(Q048Q016, F48, F16);
fix_fix_u64!(Q063Q016, F63, F16);
fix_fix_u64!(Q064Q016, F64, F16);
fix_fix_u64!(Q048Q032, F48, F32);
fix_fix_u64!(Q063Q032, F63, F32);
fix_fix_u64!(Q064Q032, F64, F32);
fix_fix_u64!(Q063Q048, F63, F48);
fix_fix_u64!(Q064Q048, F64, F48);
fix_fix_u64!(Q064Q063, F64, F63);

// ── f32 / f64 / f16 → FixedU64<U<frac>> narrowing (all L-only) ────

float_fixed_l!(pub F032Q000, f32, FixedU64, F0,  u64);
float_fixed_l!(pub F032Q008, f32, FixedU64, F8,  u64);
float_fixed_l!(pub F032Q016, f32, FixedU64, F16, u64);
float_fixed_l!(pub F032Q032, f32, FixedU64, F32, u64);
float_fixed_l!(pub F032Q048, f32, FixedU64, F48, u64);
float_fixed_l!(pub F032Q063, f32, FixedU64, F63, u64);
float_fixed_l!(pub F032Q064, f32, FixedU64, F64, u64);

float_fixed_l!(pub F064Q000, f64, FixedU64, F0,  u64);
float_fixed_l!(pub F064Q008, f64, FixedU64, F8,  u64);
float_fixed_l!(pub F064Q016, f64, FixedU64, F16, u64);
float_fixed_l!(pub F064Q032, f64, FixedU64, F32, u64);
float_fixed_l!(pub F064Q048, f64, FixedU64, F48, u64);
float_fixed_l!(pub F064Q063, f64, FixedU64, F63, u64);
float_fixed_l!(pub F064Q064, f64, FixedU64, F64, u64);

#[cfg(feature = "f16")]
float_fixed_l!(pub F016Q000, f16, FixedU64, F0,  u64);
#[cfg(feature = "f16")]
float_fixed_l!(pub F016Q008, f16, FixedU64, F8,  u64);
#[cfg(feature = "f16")]
float_fixed_l!(pub F016Q016, f16, FixedU64, F16, u64);
#[cfg(feature = "f16")]
float_fixed_l!(pub F016Q032, f16, FixedU64, F32, u64);
#[cfg(feature = "f16")]
float_fixed_l!(pub F016Q048, f16, FixedU64, F48, u64);
#[cfg(feature = "f16")]
float_fixed_l!(pub F016Q063, f16, FixedU64, F63, u64);
#[cfg(feature = "f16")]
float_fixed_l!(pub F016Q064, f16, FixedU64, F64, u64);

// ────────────────────────────────────────────────────────────────────
// Tests
// ────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    #[allow(unused_imports)]
    use crate::conn::{ConnL, ConnR};
    #[allow(unused_imports)]
    use proptest::prelude::*;

    #[test]
    fn spot_q63_to_q64() {
        let q63 = FixedU64::<F63>::from_bits(1 << 62);
        let q64 = Q064Q063.upper(q63);
        assert_eq!(q64, FixedU64::<F64>::from_bits(1 << 63));
        assert_eq!(Q064Q063.ceil(q64), q63);
    }

    #[test]
    fn spot_q032q016_on_grid() {
        let q3232 = FixedU64::<F32>::from_bits(6_442_450_944);
        assert_eq!(Q032Q016.ceil(q3232), FixedU64::<F16>::from_bits(98304));
        assert_eq!(Q032Q016.upper(FixedU64::<F16>::from_bits(98304)), q3232);
    }

    #[test]
    fn spot_q064q000_degenerate() {
        assert_eq!(
            Q064Q000.upper(FixedU64::<F0>::from_bits(0)),
            FixedU64::<F64>::from_bits(0),
        );
        assert_eq!(
            Q064Q000.upper(FixedU64::<F0>::from_bits(1)),
            FixedU64::<F64>::from_bits(u64::MAX),
        );
        assert_eq!(
            Q064Q000.ceil(FixedU64::<F64>::from_bits(0)),
            FixedU64::<F0>::from_bits(0),
        );
        assert_eq!(
            Q064Q000.ceil(FixedU64::<F64>::from_bits(1)),
            FixedU64::<F0>::from_bits(1),
        );
    }

    #[test]
    fn spot_boundary_fixups() {
        let fmin = FixedU64::<F32>::from_bits(0);
        assert_eq!(Q032Q016.ceil(fmin), FixedU64::<F16>::from_bits(0));
    }

    #[test]
    fn f064q000_above_max_to_posinf() {
        let above_max = u64::MAX as f64; // = 2^64
        let v = crate::float::N5::new(above_max);
        assert_eq!(F064Q000.ceil(v), crate::extended::Extended::PosInf);
    }

    #[test]
    fn f064q008_above_max_to_posinf() {
        let above_max = (u64::MAX as f64) / 256.0_f64; // = 2^56
        let v = crate::float::N5::new(above_max);
        assert_eq!(F064Q008.ceil(v), crate::extended::Extended::PosInf);
    }
}
