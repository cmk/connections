//! Binary fixed-point ladder over `fixed::FixedU32<Frac>`, plus the
//! cross-crate iso to `u32` and the IEEE-float → `FixedU32<F>` bridges.
//!
//! Pure-`core` Conns sourced from `u32` live next door in
//! [`crate::core::u032`]. Frac level set:
//! `{F0, F4, F8, F16, F24, F31, F32}`; `F31` (Q1.31) is the canonical
//! 32-bit normalised-amplitude format.

use super::{float_fixed, float_fixed_l};
use ::fixed::FixedU32;
use ::fixed::types::extra::{
    U0 as F0, U4 as F4, U8 as F8, U16 as F16, U24 as F24, U31 as F31, U32 as F32, Unsigned,
};

// ── Cross-crate iso: FixedU32<F0> ↔ u32 ───────────────────────────

const fn q000u032_fwd(q: FixedU32<F0>) -> u32 {
    q.to_bits()
}
const fn q000u032_bk(i: u32) -> FixedU32<F0> {
    FixedU32::<F0>::from_bits(i)
}

crate::iso! {
    /// `FixedU32<F0> ↔ u32` — Q32.0 unsigned lossless iso. Degenerate Galois.
    pub Q000U032 : FixedU32<F0> => u32 {
        forward: q000u032_fwd,
        back:    q000u032_bk,
    }
}

// ── Q-format ladder over `FixedU32<Frac>` ──────────────────────────

pub type U000 = FixedU32<F0>;
pub type U004 = FixedU32<F4>;
pub type U008 = FixedU32<F8>;
pub type U016 = FixedU32<F16>;
pub type U024 = FixedU32<F24>;
pub type U031 = FixedU32<F31>;
pub type U032 = FixedU32<F32>;

macro_rules! fix_fix_u32 {
    ($const_name:ident, $FineFrac:ty, $CoarseFrac:ty) => {
#[rustfmt::skip]
        #[doc = concat!(
            "`FixedU32<",
            stringify!($FineFrac),
            "> → FixedU32<",
            stringify!($CoarseFrac),
            ">` frac-level convert (u32-backed)."
        )]
        pub const $const_name: $crate::conn::Conn<FixedU32<$FineFrac>, FixedU32<$CoarseFrac>> = {
            const SHIFT: u32 = <$FineFrac as Unsigned>::U32 - <$CoarseFrac as Unsigned>::U32;
            const RATIO: u64 = 1_u64 << SHIFT;
            const FINE_MAX: u32 = u32::MAX;

            fn ceil(x: FixedU32<$FineFrac>) -> FixedU32<$CoarseFrac> {
                let bits = x.to_bits() as u64;
                let q = bits / RATIO;
                let r = bits % RATIO;
                let res = if r != 0 { q + 1 } else { q };
                FixedU32::from_bits(res as u32)
            }

            fn inner(x: FixedU32<$CoarseFrac>) -> FixedU32<$FineFrac> {
                let res = (x.to_bits() as u64) * RATIO;
                let saturated = if res > FINE_MAX as u64 {
                    FINE_MAX
                } else {
                    res as u32
                };
                FixedU32::from_bits(saturated)
            }

            $crate::conn::Conn::new_l(ceil, inner)
        };
    };
}

fix_fix_u32!(Q004Q000, F4, F0);
fix_fix_u32!(Q008Q000, F8, F0);
fix_fix_u32!(Q016Q000, F16, F0);
fix_fix_u32!(Q024Q000, F24, F0);
fix_fix_u32!(Q031Q000, F31, F0);
fix_fix_u32!(Q032Q000, F32, F0);
fix_fix_u32!(Q008Q004, F8, F4);
fix_fix_u32!(Q016Q004, F16, F4);
fix_fix_u32!(Q024Q004, F24, F4);
fix_fix_u32!(Q031Q004, F31, F4);
fix_fix_u32!(Q032Q004, F32, F4);
fix_fix_u32!(Q016Q008, F16, F8);
fix_fix_u32!(Q024Q008, F24, F8);
fix_fix_u32!(Q031Q008, F31, F8);
fix_fix_u32!(Q032Q008, F32, F8);
fix_fix_u32!(Q024Q016, F24, F16);
fix_fix_u32!(Q031Q016, F31, F16);
fix_fix_u32!(Q032Q016, F32, F16);
fix_fix_u32!(Q031Q024, F31, F24);
fix_fix_u32!(Q032Q024, F32, F24);
fix_fix_u32!(Q032Q031, F32, F31);

// ── f32 → FixedU32<U<frac>> narrowing (L-only) ────────────────────

float_fixed_l!(pub F032Q000, f32, FixedU32, F0,  u32);
float_fixed_l!(pub F032Q004, f32, FixedU32, F4,  u32);
float_fixed_l!(pub F032Q008, f32, FixedU32, F8,  u32);
float_fixed_l!(pub F032Q016, f32, FixedU32, F16, u32);
float_fixed_l!(pub F032Q024, f32, FixedU32, F24, u32);
float_fixed_l!(pub F032Q031, f32, FixedU32, F31, u32);
float_fixed_l!(pub F032Q032, f32, FixedU32, F32, u32);

// ── f64 → FixedU32<U<frac>> narrowing (full triple) ───────────────

float_fixed!(pub F064Q000, f64, FixedU32, F0,  u32);
float_fixed!(pub F064Q004, f64, FixedU32, F4,  u32);
float_fixed!(pub F064Q008, f64, FixedU32, F8,  u32);
float_fixed!(pub F064Q016, f64, FixedU32, F16, u32);
float_fixed!(pub F064Q024, f64, FixedU32, F24, u32);
float_fixed!(pub F064Q031, f64, FixedU32, F31, u32);
float_fixed!(pub F064Q032, f64, FixedU32, F32, u32);

// ── f16 → FixedU32<U<frac>> narrowing (L-only; gated on `f16`) ────

#[cfg(feature = "f16")]
float_fixed_l!(pub F016Q000, f16, FixedU32, F0,  u32);
#[cfg(feature = "f16")]
float_fixed_l!(pub F016Q004, f16, FixedU32, F4,  u32);
#[cfg(feature = "f16")]
float_fixed_l!(pub F016Q008, f16, FixedU32, F8,  u32);
#[cfg(feature = "f16")]
float_fixed_l!(pub F016Q016, f16, FixedU32, F16, u32);
#[cfg(feature = "f16")]
float_fixed_l!(pub F016Q024, f16, FixedU32, F24, u32);
#[cfg(feature = "f16")]
float_fixed_l!(pub F016Q031, f16, FixedU32, F31, u32);
#[cfg(feature = "f16")]
float_fixed_l!(pub F016Q032, f16, FixedU32, F32, u32);

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
    fn spot_q31_to_q32() {
        let q31 = FixedU32::<F31>::from_bits(1 << 30);
        let q32 = crate::conn::upper(&Q032Q031, q31);
        assert_eq!(q32, FixedU32::<F32>::from_bits(1 << 31));
        assert_eq!(crate::conn::ceil(&Q032Q031, q32), q31);
    }

    #[test]
    fn spot_q016q008_on_grid() {
        let q1616 = FixedU32::<F16>::from_bits(98304);
        assert_eq!(
            crate::conn::ceil(&Q016Q008, q1616),
            FixedU32::<F8>::from_bits(384)
        );
        assert_eq!(
            crate::conn::upper(&Q016Q008, FixedU32::<F8>::from_bits(384)),
            q1616
        );
    }

    #[test]
    fn spot_q032q000_degenerate() {
        assert_eq!(
            crate::conn::upper(&Q032Q000, FixedU32::<F0>::from_bits(0)),
            FixedU32::<F32>::from_bits(0),
        );
        assert_eq!(
            crate::conn::upper(&Q032Q000, FixedU32::<F0>::from_bits(1)),
            FixedU32::<F32>::from_bits(u32::MAX),
        );
    }

    #[test]
    fn spot_boundary_fixups() {
        let fmin = FixedU32::<F16>::from_bits(0);
        assert_eq!(
            crate::conn::ceil(&Q016Q008, fmin),
            FixedU32::<F8>::from_bits(0)
        );
    }
}
