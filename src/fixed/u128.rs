//! Binary fixed-point ladder over `fixed::FixedU128<Frac>`, plus the
//! cross-crate iso to `u128` and the IEEE-float → `FixedU128<F>` bridges.
//!
//! Pure-`core` Conns sourced from `u128` live next door in
//! [`crate::core::u128`]. Frac level set:
//! `{F0, F16, F32, F64, F96, F127, F128}`; `F127` (Q1.127) is the
//! canonical 128-bit normalised-amplitude format.
//!
//! Stable Rust has no native `u256` to widen through, so the u64-style
//! `(x.to_bits() as u128) * RATIO` pattern doesn't compose. Instead we
//! use [`u128::checked_mul`] + saturate, and [`u128::checked_shl`] to
//! detect the `SHIFT == 128` degenerate case.

use super::float_fixed_l;
use ::fixed::FixedU128;
use ::fixed::types::extra::{
    U0 as F0, U16 as F16, U32 as F32, U64 as F64, U96 as F96, U127 as F127, U128 as F128, Unsigned,
};

// ── Cross-crate iso: FixedU128<F0> ↔ u128 ─────────────────────────

const fn q000u128_fwd(q: FixedU128<F0>) -> u128 {
    q.to_bits()
}
const fn q000u128_bk(i: u128) -> FixedU128<F0> {
    FixedU128::<F0>::from_bits(i)
}

crate::iso! {
    /// `FixedU128<F0> ↔ u128` — Q128.0 unsigned lossless iso. Degenerate Galois.
    pub Q000U128 : FixedU128<F0> => u128 {
        forward: q000u128_fwd,
        back:    q000u128_bk,
    }
}

// ── Q-format ladder over `FixedU128<Frac>` ─────────────────────────

pub type U000 = FixedU128<F0>;
pub type U016 = FixedU128<F16>;
pub type U032 = FixedU128<F32>;
pub type U064 = FixedU128<F64>;
pub type U096 = FixedU128<F96>;
pub type U127 = FixedU128<F127>;
pub type U128 = FixedU128<F128>;

macro_rules! fix_fix_u128 {
    ($const_name:ident, $FineFrac:ty, $CoarseFrac:ty) => {
#[rustfmt::skip]
        #[doc = concat!(
            "`FixedU128<",
            stringify!($FineFrac),
            "> → FixedU128<",
            stringify!($CoarseFrac),
            ">` frac-level convert (u128-backed)."
        )]
        pub const $const_name: $crate::conn::Conn<FixedU128<$FineFrac>, FixedU128<$CoarseFrac>> = {
            const SHIFT: u32 = <$FineFrac as Unsigned>::U32 - <$CoarseFrac as Unsigned>::U32;
            const RATIO: Option<u128> = 1_u128.checked_shl(SHIFT);
            const FINE_MAX: u128 = u128::MAX;

            fn ceil(x: FixedU128<$FineFrac>) -> FixedU128<$CoarseFrac> {
                let bits = x.to_bits();
                match RATIO {
                    Some(r) => {
                        let q = bits / r;
                        let res = if bits % r != 0 { q + 1 } else { q };
                        FixedU128::from_bits(res)
                    }
                    None => {
                        if bits > 0 {
                            FixedU128::from_bits(1)
                        } else {
                            FixedU128::from_bits(0)
                        }
                    }
                }
            }

            fn inner(x: FixedU128<$CoarseFrac>) -> FixedU128<$FineFrac> {
                let bits = x.to_bits();
                let saturated = match RATIO {
                    Some(r) => match bits.checked_mul(r) {
                        Some(v) => v,
                        None => FINE_MAX,
                    },
                    None => {
                        if bits == 0 { 0 } else { FINE_MAX }
                    }
                };
                FixedU128::from_bits(saturated)
            }

            $crate::conn::Conn::new_l(ceil, inner)
        };
    };
}

fix_fix_u128!(Q016Q000, F16, F0);
fix_fix_u128!(Q032Q000, F32, F0);
fix_fix_u128!(Q064Q000, F64, F0);
fix_fix_u128!(Q096Q000, F96, F0);
fix_fix_u128!(Q127Q000, F127, F0);
fix_fix_u128!(Q128Q000, F128, F0);
fix_fix_u128!(Q032Q016, F32, F16);
fix_fix_u128!(Q064Q016, F64, F16);
fix_fix_u128!(Q096Q016, F96, F16);
fix_fix_u128!(Q127Q016, F127, F16);
fix_fix_u128!(Q128Q016, F128, F16);
fix_fix_u128!(Q064Q032, F64, F32);
fix_fix_u128!(Q096Q032, F96, F32);
fix_fix_u128!(Q127Q032, F127, F32);
fix_fix_u128!(Q128Q032, F128, F32);
fix_fix_u128!(Q096Q064, F96, F64);
fix_fix_u128!(Q127Q064, F127, F64);
fix_fix_u128!(Q128Q064, F128, F64);
fix_fix_u128!(Q127Q096, F127, F96);
fix_fix_u128!(Q128Q096, F128, F96);
fix_fix_u128!(Q128Q127, F128, F127);

// ── f32 / f64 / f16 → FixedU128<U<frac>> narrowing (all L-only) ───

float_fixed_l!(pub F032Q000, f32, FixedU128, F0,   u128);
float_fixed_l!(pub F032Q016, f32, FixedU128, F16,  u128);
float_fixed_l!(pub F032Q032, f32, FixedU128, F32,  u128);
float_fixed_l!(pub F032Q064, f32, FixedU128, F64,  u128);
float_fixed_l!(pub F032Q096, f32, FixedU128, F96,  u128);
float_fixed_l!(pub F032Q127, f32, FixedU128, F127, u128);
float_fixed_l!(pub F032Q128, f32, FixedU128, F128, u128);

float_fixed_l!(pub F064Q000, f64, FixedU128, F0,   u128);
float_fixed_l!(pub F064Q016, f64, FixedU128, F16,  u128);
float_fixed_l!(pub F064Q032, f64, FixedU128, F32,  u128);
float_fixed_l!(pub F064Q064, f64, FixedU128, F64,  u128);
float_fixed_l!(pub F064Q096, f64, FixedU128, F96,  u128);
float_fixed_l!(pub F064Q127, f64, FixedU128, F127, u128);
float_fixed_l!(pub F064Q128, f64, FixedU128, F128, u128);

#[cfg(feature = "f16")]
float_fixed_l!(pub F016Q000, f16, FixedU128, F0,   u128);
#[cfg(feature = "f16")]
float_fixed_l!(pub F016Q016, f16, FixedU128, F16,  u128);
#[cfg(feature = "f16")]
float_fixed_l!(pub F016Q032, f16, FixedU128, F32,  u128);
#[cfg(feature = "f16")]
float_fixed_l!(pub F016Q064, f16, FixedU128, F64,  u128);
#[cfg(feature = "f16")]
float_fixed_l!(pub F016Q096, f16, FixedU128, F96,  u128);
#[cfg(feature = "f16")]
float_fixed_l!(pub F016Q127, f16, FixedU128, F127, u128);
#[cfg(feature = "f16")]
float_fixed_l!(pub F016Q128, f16, FixedU128, F128, u128);

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
    fn degenerate_max_shift() {
        assert_eq!(
            Q128Q000.upper(FixedU128::<F0>::from_bits(0)),
            FixedU128::<F128>::from_bits(0),
        );
        assert_eq!(
            Q128Q000.upper(FixedU128::<F0>::from_bits(1)),
            FixedU128::<F128>::from_bits(u128::MAX),
        );
        assert_eq!(
            Q128Q000.upper(FixedU128::<F0>::from_bits(u128::MAX)),
            FixedU128::<F128>::from_bits(u128::MAX),
        );
        assert_eq!(
            Q128Q000.ceil(FixedU128::<F128>::from_bits(0)),
            FixedU128::<F0>::from_bits(0),
        );
        assert_eq!(
            Q128Q000.ceil(FixedU128::<F128>::from_bits(1)),
            FixedU128::<F0>::from_bits(1),
        );
    }

    #[test]
    fn spot_q127_to_q128() {
        let q127 = FixedU128::<F127>::from_bits(1 << 126);
        let q128 = Q128Q127.upper(q127);
        assert_eq!(q128, FixedU128::<F128>::from_bits(1 << 127));
        assert_eq!(Q128Q127.ceil(q128), q127);
    }

    #[test]
    fn spot_boundary_fixups() {
        let fmin = FixedU128::<F128>::from_bits(0);
        assert_eq!(Q128Q064.ceil(fmin), FixedU128::<F64>::from_bits(0));
    }

    #[test]
    fn inner_saturates_on_overflow() {
        let big_coarse = FixedU128::<F16>::from_bits(u128::MAX);
        assert_eq!(
            Q128Q016.upper(big_coarse),
            FixedU128::<F128>::from_bits(u128::MAX),
        );
    }

    #[test]
    fn ceil_at_fine_max_no_overflow() {
        let fmax = FixedU128::<F128>::from_bits(u128::MAX);
        assert_eq!(
            Q128Q127.ceil(fmax),
            FixedU128::<F127>::from_bits(1_u128 << 127),
        );
    }

    #[test]
    fn f064q000_above_max_to_posinf() {
        let above_max = u128::MAX as f64; // = 2^128
        let v = crate::float::N5::new(above_max);
        assert_eq!(F064Q000.ceil(v), crate::extended::Extended::PosInf);
    }

    #[test]
    fn f064q064_above_max_to_posinf() {
        let above_max = (u128::MAX as f64) / 2.0_f64.powi(64); // = 2^64
        let v = crate::float::N5::new(above_max);
        assert_eq!(F064Q064.ceil(v), crate::extended::Extended::PosInf);
    }
}
