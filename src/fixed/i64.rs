//! Binary fixed-point ladder over `fixed::FixedI64<Frac>`.
//!
//! Frac level set: `{U0, U8, U16, U32, U48, U64}` → 15 ordered pairs
//! `(Fine, Coarse)` with `Fine > Coarse`. See [`super::i16`] for the
//! design (this module mirrors it with `i64` inner / `i128` widening).

use super::{ext_int, int_int_narrow, uint_int_sat};
use crate::conn::Conn;
use crate::extended::Extended;
use ::fixed::FixedI64;
use ::fixed::types::extra::{U0, U8, U16, U32, U48, U64, Unsigned};

// ── §1 std-int Conns landing on `i64` ───────────────────────────────

ext_int!(I008I064, i8, i64);
ext_int!(I016I064, i16, i64);
ext_int!(I032I064, i32, i64);
ext_int!(U008I064, u8, i64);
ext_int!(U016I064, u16, i64);
ext_int!(U032I064, u32, i64);

int_int_narrow!(I128I064, i128, i64);

uint_int_sat!(U064I064, u64, i64);
uint_int_sat!(U128I064, u128, i64);

// ── §2 Q-format ladder over `FixedI64<Frac>` ────────────────────────

/// `I<frac> = FixedI64<U<frac>>` — i64-backed binary fixed-point.
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
        pub const $const_name: Conn<FixedI64<$FineFrac>, FixedI64<$CoarseFrac>> = {
            const SHIFT: u32 = <$FineFrac as Unsigned>::U32 - <$CoarseFrac as Unsigned>::U32;
            // i128 covers SHIFT ∈ [1, 64]: 1 << 64 = 2^64 fits, and
            // i64::MAX × 2^64 ≈ 2^127 < i128::MAX.
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

            fn floor(x: FixedI64<$FineFrac>) -> FixedI64<$CoarseFrac> {
                if x.to_bits() == FINE_MAX {
                    return FixedI64::<$CoarseFrac>::from_bits(i64::MAX);
                }
                let res = (x.to_bits() as i128).div_euclid(RATIO);
                FixedI64::from_bits(res as i64)
            }

            Conn::new(ceil, inner, floor)
        };
    };
}

// 15 ordered pairs from {U0, U8, U16, U32, U48, U64}.
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

// ────────────────────────────────────────────────────────────────────
// Tests
// ────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::prop::conn as conn_laws;
    use proptest::prelude::*;

    // ── §1 std-int spot checks (merged from former int/i64.rs) ─────

    #[test]
    fn i032i064_extends_to_one_below_above() {
        assert_eq!(I032I064.floor(Extended::NegInf), (i32::MIN as i64) - 1);
        assert_eq!(I032I064.ceil(Extended::PosInf), (i32::MAX as i64) + 1);
    }

    #[test]
    fn u032i064_extends_to_one_above() {
        assert_eq!(U032I064.ceil(Extended::PosInf), 4_294_967_296);
        assert_eq!(U032I064.floor(Extended::NegInf), -1);
    }

    #[test]
    fn i128i064_saturate_and_fixup() {
        assert_eq!(I128I064.ceil(i128::MAX), i64::MAX);
        assert_eq!(I128I064.ceil(i128::MIN), i64::MIN);
        assert_eq!(I128I064.inner(i64::MAX), i128::MAX);
        assert_eq!(I128I064.inner(i64::MIN), i64::MIN as i128);
    }

    #[test]
    fn u_to_i64_neg_and_high() {
        assert_eq!(U064I064.inner(-1), 0_u64);
        assert_eq!(U064I064.floor(u64::MAX), i64::MAX);
        assert_eq!(U128I064.inner(i64::MIN), 0_u128);
        assert_eq!(U128I064.floor(u128::MAX), i64::MAX);
    }

    // ── §2 Q-format spot checks ────────────────────────────────────

    #[test]
    fn spot_q032q016_on_grid() {
        // 1.5 in Q32.32 (bits = 1.5 × 2^32) round-trips through Q48.16.
        let bits_3232: i64 = 3 << 31;
        let q3232 = FixedI64::<U32>::from_bits(bits_3232);
        assert_eq!(Q032Q016.floor(q3232), FixedI64::<U16>::from_bits(3 << 15));
        assert_eq!(Q032Q016.ceil(q3232), FixedI64::<U16>::from_bits(3 << 15));
    }

    #[test]
    fn spot_q064q000_degenerate() {
        // SHIFT = 64. Only Coarse(0) round-trips; ±1 saturates inner.
        assert_eq!(
            Q064Q000.inner(FixedI64::<U0>::from_bits(0)),
            FixedI64::<U64>::from_bits(0),
        );
        assert_eq!(
            Q064Q000.inner(FixedI64::<U0>::from_bits(1)),
            FixedI64::<U64>::from_bits(i64::MAX),
        );
        assert_eq!(
            Q064Q000.inner(FixedI64::<U0>::from_bits(-1)),
            FixedI64::<U64>::from_bits(i64::MIN),
        );
    }

    #[test]
    fn spot_boundary_fixups() {
        let fmin = FixedI64::<U32>::from_bits(i64::MIN);
        let fmax = FixedI64::<U32>::from_bits(i64::MAX);
        assert_eq!(Q032Q016.ceil(fmin), FixedI64::<U16>::from_bits(i64::MIN));
        assert_eq!(Q032Q016.floor(fmax), FixedI64::<U16>::from_bits(i64::MAX));
    }

    // See `super::i16::tests::props_for_pair!` for design rationale.
    // i64 generators are expensive; cap proptest case count to 64.
    macro_rules! props_for_pair {
        ($mod_name:ident, $conn:ident, $FineFrac:ty, $CoarseFrac:ty) => {
            mod $mod_name {
                use super::*;

                proptest! {
                    #![proptest_config(ProptestConfig::with_cases(64))]

                    #[test]
                    fn galois_l(f in any::<i64>(), b in any::<i64>()) {
                        let fine = FixedI64::<$FineFrac>::from_bits(f);
                        let coarse = FixedI64::<$CoarseFrac>::from_bits(b);
                        prop_assert!(conn_laws::conn_galois_l(&$conn, fine, coarse));
                    }
                    #[test]
                    fn galois_r(f in any::<i64>(), b in any::<i64>()) {
                        let fine = FixedI64::<$FineFrac>::from_bits(f);
                        let coarse = FixedI64::<$CoarseFrac>::from_bits(b);
                        prop_assert!(conn_laws::conn_galois_r(&$conn, fine, coarse));
                    }
                    #[test]
                    fn monotone_l(f1 in any::<i64>(), f2 in any::<i64>()) {
                        let f1 = FixedI64::<$FineFrac>::from_bits(f1);
                        let f2 = FixedI64::<$FineFrac>::from_bits(f2);
                        prop_assert!(conn_laws::conn_monotone_l(&$conn, f1, f2));
                    }
                    #[test]
                    fn monotone_r(b1 in any::<i64>(), b2 in any::<i64>()) {
                        let b1 = FixedI64::<$CoarseFrac>::from_bits(b1);
                        let b2 = FixedI64::<$CoarseFrac>::from_bits(b2);
                        prop_assert!(conn_laws::conn_monotone_r(&$conn, b1, b2));
                    }
                    #[test]
                    fn closure_l(f in any::<i64>()) {
                        let fine = FixedI64::<$FineFrac>::from_bits(f);
                        prop_assert!(conn_laws::conn_closure_l(&$conn, fine));
                    }
                    #[test]
                    fn closure_r(f in any::<i64>()) {
                        let fine = FixedI64::<$FineFrac>::from_bits(f);
                        prop_assert!(conn_laws::conn_closure_r(&$conn, fine));
                    }
                    #[test]
                    fn kernel_l(b in any::<i64>()) {
                        let c = FixedI64::<$CoarseFrac>::from_bits(b);
                        prop_assert!(conn_laws::conn_kernel_l(&$conn, c));
                    }
                    #[test]
                    fn kernel_r(b in any::<i64>()) {
                        let c = FixedI64::<$CoarseFrac>::from_bits(b);
                        prop_assert!(conn_laws::conn_kernel_r(&$conn, c));
                    }
                    #[test]
                    fn idempotent(f in any::<i64>()) {
                        let fine = FixedI64::<$FineFrac>::from_bits(f);
                        prop_assert!(conn_laws::conn_idempotent(&$conn, fine));
                    }
                }
            }
        };
    }

    // 15 conns × 9 properties = 135 generated proptests (64 cases each).
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
}
