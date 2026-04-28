//! Binary fixed-point ladder over `fixed::FixedI32<Frac>`.
//!
//! Frac level set: `{U0, U4, U8, U16, U24, U32}` → 15 ordered pairs
//! `(Fine, Coarse)` with `Fine > Coarse`. See [`super::i16`] for the
//! design (this module mirrors it with `i32` inner / `i64` widening).

use super::{ext_int, int_int_narrow, uint_int_sat};
use crate::conn::Conn;
use crate::extended::Extended;
use ::fixed::FixedI32;
use ::fixed::types::extra::{U0, U4, U8, U16, U24, U32, Unsigned};

// ── §1 std-int Conns landing on `i32` ───────────────────────────────

ext_int!(I008I032, i8, i32);
ext_int!(I016I032, i16, i32);
ext_int!(U008I032, u8, i32);
ext_int!(U016I032, u16, i32);

int_int_narrow!(I064I032, i64, i32);
int_int_narrow!(I128I032, i128, i32);

uint_int_sat!(U032I032, u32, i32);
uint_int_sat!(U064I032, u64, i32);
uint_int_sat!(U128I032, u128, i32);

// ── §2 Q-format ladder over `FixedI32<Frac>` ────────────────────────

/// `I<frac> = FixedI32<U<frac>>` — i32-backed binary fixed-point.
pub type I000 = FixedI32<U0>;
pub type I004 = FixedI32<U4>;
pub type I008 = FixedI32<U8>;
pub type I016 = FixedI32<U16>;
pub type I024 = FixedI32<U24>;
pub type I032 = FixedI32<U32>;

macro_rules! fix_fix_i32 {
    ($const_name:ident, $FineFrac:ty, $CoarseFrac:ty) => {
#[rustfmt::skip]
        #[doc = concat!(
            "`FixedI32<",
            stringify!($FineFrac),
            "> → FixedI32<",
            stringify!($CoarseFrac),
            ">` frac-level convert (i32-backed)."
        )]
        pub const $const_name: Conn<FixedI32<$FineFrac>, FixedI32<$CoarseFrac>> = {
            const SHIFT: u32 = <$FineFrac as Unsigned>::U32 - <$CoarseFrac as Unsigned>::U32;
            // i64 covers SHIFT ∈ [1, 32]: 1 << 32 fits, and
            // i32::MAX × (1 << 32) ≈ 2^63 < i64::MAX.
            const RATIO: i64 = 1_i64 << SHIFT;
            const FINE_MIN: i32 = i32::MIN;
            const FINE_MAX: i32 = i32::MAX;

            fn ceil(x: FixedI32<$FineFrac>) -> FixedI32<$CoarseFrac> {
                if x.to_bits() == FINE_MIN {
                    return FixedI32::<$CoarseFrac>::from_bits(i32::MIN);
                }
                let bits = x.to_bits() as i64;
                let q = bits.div_euclid(RATIO);
                let r = bits.rem_euclid(RATIO);
                let res = if r != 0 { q + 1 } else { q };
                FixedI32::from_bits(res as i32)
            }

            fn inner(x: FixedI32<$CoarseFrac>) -> FixedI32<$FineFrac> {
                let res = (x.to_bits() as i64) * RATIO;
                let saturated = if res > FINE_MAX as i64 {
                    FINE_MAX
                } else if res < FINE_MIN as i64 {
                    FINE_MIN
                } else {
                    res as i32
                };
                FixedI32::from_bits(saturated)
            }

            fn floor(x: FixedI32<$FineFrac>) -> FixedI32<$CoarseFrac> {
                if x.to_bits() == FINE_MAX {
                    return FixedI32::<$CoarseFrac>::from_bits(i32::MAX);
                }
                let res = (x.to_bits() as i64).div_euclid(RATIO);
                FixedI32::from_bits(res as i32)
            }

            Conn::new(ceil, inner, floor)
        };
    };
}

// 15 ordered pairs from {U0, U4, U8, U16, U24, U32}.
fix_fix_i32!(Q004Q000, U4, U0);
fix_fix_i32!(Q008Q000, U8, U0);
fix_fix_i32!(Q016Q000, U16, U0);
fix_fix_i32!(Q024Q000, U24, U0);
fix_fix_i32!(Q032Q000, U32, U0);
fix_fix_i32!(Q008Q004, U8, U4);
fix_fix_i32!(Q016Q004, U16, U4);
fix_fix_i32!(Q024Q004, U24, U4);
fix_fix_i32!(Q032Q004, U32, U4);
fix_fix_i32!(Q016Q008, U16, U8);
fix_fix_i32!(Q024Q008, U24, U8);
fix_fix_i32!(Q032Q008, U32, U8);
fix_fix_i32!(Q024Q016, U24, U16);
fix_fix_i32!(Q032Q016, U32, U16);
fix_fix_i32!(Q032Q024, U32, U24);

// ────────────────────────────────────────────────────────────────────
// Tests
// ────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::prop::conn as conn_laws;
    use proptest::prelude::*;

    // ── §1 std-int spot checks (merged from former int/i32.rs) ─────

    #[test]
    fn i008i032_round_trip_at_finite_boundaries() {
        assert_eq!(I008I032.ceil(Extended::Finite(i8::MIN)), -128);
        assert_eq!(I008I032.ceil(Extended::Finite(i8::MAX)), 127);
        assert_eq!(I008I032.inner(-128), Extended::Finite(i8::MIN));
        assert_eq!(I008I032.inner(127), Extended::Finite(i8::MAX));
    }

    #[test]
    fn u016i032_inner_partitions() {
        assert_eq!(U016I032.inner(-1), Extended::NegInf);
        assert_eq!(U016I032.inner(0), Extended::Finite(0));
        assert_eq!(U016I032.inner(65_535), Extended::Finite(u16::MAX));
        assert_eq!(U016I032.inner(65_536), Extended::PosInf);
    }

    #[test]
    fn i_to_i32_saturate() {
        assert_eq!(I064I032.ceil(i64::MAX), i32::MAX);
        assert_eq!(I064I032.ceil(i64::MIN), i32::MIN);
        assert_eq!(I128I032.ceil(i128::MAX), i32::MAX);
        assert_eq!(I128I032.ceil(i128::MIN), i32::MIN);
    }

    #[test]
    fn i_to_i32_inner_fine_max_fixup() {
        assert_eq!(I064I032.inner(i32::MAX), i64::MAX);
        assert_eq!(I128I032.inner(i32::MAX), i128::MAX);
    }

    #[test]
    fn u_to_i32_neg_and_high() {
        assert_eq!(U032I032.inner(-1), 0_u32);
        assert_eq!(U064I032.floor(u64::MAX), i32::MAX);
        assert_eq!(U128I032.inner(i32::MIN), 0_u128);
    }

    // ── §2 Q-format spot checks ────────────────────────────────────

    #[test]
    fn spot_q016q008_on_grid() {
        // 1.5 in Q16.16 (bits = 1.5 × 2^16 = 98304); same value in Q24.8
        // is bits 384.
        let q1616 = FixedI32::<U16>::from_bits(98304);
        assert_eq!(Q016Q008.floor(q1616), FixedI32::<U8>::from_bits(384));
        assert_eq!(Q016Q008.ceil(q1616), FixedI32::<U8>::from_bits(384));
        assert_eq!(Q016Q008.inner(FixedI32::<U8>::from_bits(384)), q1616);
    }

    #[test]
    fn spot_q032q000_degenerate() {
        // SHIFT = 32. Only Coarse(0) round-trips; ±1 saturates inner.
        assert_eq!(
            Q032Q000.inner(FixedI32::<U0>::from_bits(0)),
            FixedI32::<U32>::from_bits(0),
        );
        assert_eq!(
            Q032Q000.inner(FixedI32::<U0>::from_bits(1)),
            FixedI32::<U32>::from_bits(i32::MAX),
        );
        assert_eq!(
            Q032Q000.inner(FixedI32::<U0>::from_bits(-1)),
            FixedI32::<U32>::from_bits(i32::MIN),
        );
    }

    #[test]
    fn spot_boundary_fixups() {
        let fmin = FixedI32::<U16>::from_bits(i32::MIN);
        let fmax = FixedI32::<U16>::from_bits(i32::MAX);
        assert_eq!(Q016Q008.ceil(fmin), FixedI32::<U8>::from_bits(i32::MIN));
        assert_eq!(Q016Q008.floor(fmax), FixedI32::<U8>::from_bits(i32::MAX));
    }

    // See `super::i16::tests::props_for_pair!` for the design rationale.
    macro_rules! props_for_pair {
        ($mod_name:ident, $conn:ident, $FineFrac:ty, $CoarseFrac:ty) => {
            mod $mod_name {
                use super::*;

                proptest! {
                    #[test]
                    fn galois_l(f in any::<i32>(), b in any::<i32>()) {
                        let fine = FixedI32::<$FineFrac>::from_bits(f);
                        let coarse = FixedI32::<$CoarseFrac>::from_bits(b);
                        prop_assert!(conn_laws::conn_galois_l(&$conn, fine, coarse));
                    }
                    #[test]
                    fn galois_r(f in any::<i32>(), b in any::<i32>()) {
                        let fine = FixedI32::<$FineFrac>::from_bits(f);
                        let coarse = FixedI32::<$CoarseFrac>::from_bits(b);
                        prop_assert!(conn_laws::conn_galois_r(&$conn, fine, coarse));
                    }
                    #[test]
                    fn monotone_l(f1 in any::<i32>(), f2 in any::<i32>()) {
                        let f1 = FixedI32::<$FineFrac>::from_bits(f1);
                        let f2 = FixedI32::<$FineFrac>::from_bits(f2);
                        prop_assert!(conn_laws::conn_monotone_l(&$conn, f1, f2));
                    }
                    #[test]
                    fn monotone_r(b1 in any::<i32>(), b2 in any::<i32>()) {
                        let b1 = FixedI32::<$CoarseFrac>::from_bits(b1);
                        let b2 = FixedI32::<$CoarseFrac>::from_bits(b2);
                        prop_assert!(conn_laws::conn_monotone_r(&$conn, b1, b2));
                    }
                    #[test]
                    fn closure_l(f in any::<i32>()) {
                        let fine = FixedI32::<$FineFrac>::from_bits(f);
                        prop_assert!(conn_laws::conn_closure_l(&$conn, fine));
                    }
                    #[test]
                    fn closure_r(f in any::<i32>()) {
                        let fine = FixedI32::<$FineFrac>::from_bits(f);
                        prop_assert!(conn_laws::conn_closure_r(&$conn, fine));
                    }
                    #[test]
                    fn kernel_l(b in any::<i32>()) {
                        let c = FixedI32::<$CoarseFrac>::from_bits(b);
                        prop_assert!(conn_laws::conn_kernel_l(&$conn, c));
                    }
                    #[test]
                    fn kernel_r(b in any::<i32>()) {
                        let c = FixedI32::<$CoarseFrac>::from_bits(b);
                        prop_assert!(conn_laws::conn_kernel_r(&$conn, c));
                    }
                    #[test]
                    fn idempotent(f in any::<i32>()) {
                        let fine = FixedI32::<$FineFrac>::from_bits(f);
                        prop_assert!(conn_laws::conn_idempotent(&$conn, fine));
                    }
                }
            }
        };
    }

    // 15 conns × 9 properties = 135 generated proptests.
    props_for_pair!(q004q000, Q004Q000, U4, U0);
    props_for_pair!(q008q000, Q008Q000, U8, U0);
    props_for_pair!(q016q000, Q016Q000, U16, U0);
    props_for_pair!(q024q000, Q024Q000, U24, U0);
    props_for_pair!(q032q000, Q032Q000, U32, U0);
    props_for_pair!(q008q004, Q008Q004, U8, U4);
    props_for_pair!(q016q004, Q016Q004, U16, U4);
    props_for_pair!(q024q004, Q024Q004, U24, U4);
    props_for_pair!(q032q004, Q032Q004, U32, U4);
    props_for_pair!(q016q008, Q016Q008, U16, U8);
    props_for_pair!(q024q008, Q024Q008, U24, U8);
    props_for_pair!(q032q008, Q032Q008, U32, U8);
    props_for_pair!(q024q016, Q024Q016, U24, U16);
    props_for_pair!(q032q016, Q032Q016, U32, U16);
    props_for_pair!(q032q024, Q032Q024, U32, U24);
}
