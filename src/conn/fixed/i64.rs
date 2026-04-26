//! Binary fixed-point ladder over `fixed::FixedI64<Frac>`.
//!
//! Frac level set: `{U0, U8, U16, U32, U48, U64}` → 15 ordered pairs
//! `(Fine, Coarse)` with `Fine > Coarse`. See [`super::i16`] for the
//! design (this module mirrors it with `i64` inner / `i128` widening).

use crate::conn::Conn;
use ::fixed::FixedI64;
use ::fixed::types::extra::{U0, U8, U16, U32, U48, U64, Unsigned};

macro_rules! fix_fix_i64 {
    ($const_name:ident, $FineFrac:ty, $CoarseFrac:ty) => {
        pub const $const_name: Conn<FixedI64<$FineFrac>, FixedI64<$CoarseFrac>> = {
            const SHIFT: u32 = <$FineFrac as Unsigned>::U32 - <$CoarseFrac as Unsigned>::U32;
            // i128 covers SHIFT ∈ [1, 64]: 1 << 64 = 2^64 fits, and
            // i64::MAX × 2^64 ≈ 2^127 < i128::MAX.
            const RATIO: i128 = 1_i128 << SHIFT;
            const FINE_MIN: i64 = i64::MIN;
            const FINE_MAX: i64 = i64::MAX;

            fn ceil(x: FixedI64<$FineFrac>) -> FixedI64<$CoarseFrac> {
                if x.to_bits() == FINE_MIN {
                    return FixedI64::from_bits(FINE_MIN);
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
                    return FixedI64::from_bits(FINE_MAX);
                }
                let res = (x.to_bits() as i128).div_euclid(RATIO);
                FixedI64::from_bits(res as i64)
            }

            Conn::new(ceil, inner, floor)
        };
    };
}

// 15 ordered pairs from {U0, U8, U16, U32, U48, U64}.
fix_fix_i64!(F08F00, U8,  U0);
fix_fix_i64!(F16F00, U16, U0);
fix_fix_i64!(F32F00, U32, U0);
fix_fix_i64!(F48F00, U48, U0);
fix_fix_i64!(F64F00, U64, U0);
fix_fix_i64!(F16F08, U16, U8);
fix_fix_i64!(F32F08, U32, U8);
fix_fix_i64!(F48F08, U48, U8);
fix_fix_i64!(F64F08, U64, U8);
fix_fix_i64!(F32F16, U32, U16);
fix_fix_i64!(F48F16, U48, U16);
fix_fix_i64!(F64F16, U64, U16);
fix_fix_i64!(F48F32, U48, U32);
fix_fix_i64!(F64F32, U64, U32);
fix_fix_i64!(F64F48, U64, U48);

// ────────────────────────────────────────────────────────────────────
// Tests
// ────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::property::laws;
    use proptest::prelude::*;

    #[test]
    fn spot_f32f16_on_grid() {
        // 1.5 in Q32.32 (bits = 1.5 × 2^32) round-trips through Q48.16.
        let bits_3232: i64 = 3 << 31;
        let q3232 = FixedI64::<U32>::from_bits(bits_3232);
        assert_eq!(F32F16.floor(q3232), FixedI64::<U16>::from_bits(3 << 15));
        assert_eq!(F32F16.ceil(q3232), FixedI64::<U16>::from_bits(3 << 15));
    }

    #[test]
    fn spot_f64f00_degenerate() {
        // SHIFT = 64. Only Coarse(0) round-trips.
        assert_eq!(
            F64F00.inner(FixedI64::<U0>::from_bits(0)),
            FixedI64::<U64>::from_bits(0),
        );
        assert_eq!(
            F64F00.inner(FixedI64::<U0>::from_bits(1)),
            FixedI64::<U64>::from_bits(i64::MAX),
        );
    }

    #[test]
    fn spot_boundary_fixups() {
        let fmin = FixedI64::<U32>::from_bits(i64::MIN);
        let fmax = FixedI64::<U32>::from_bits(i64::MAX);
        assert_eq!(F32F16.ceil(fmin), FixedI64::<U16>::from_bits(i64::MIN));
        assert_eq!(F32F16.floor(fmax), FixedI64::<U16>::from_bits(i64::MAX));
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
                        prop_assert!(laws::conn_galois_l(&$conn, fine, coarse));
                    }
                    #[test]
                    fn galois_r(f in any::<i64>(), b in any::<i64>()) {
                        let fine = FixedI64::<$FineFrac>::from_bits(f);
                        let coarse = FixedI64::<$CoarseFrac>::from_bits(b);
                        prop_assert!(laws::conn_galois_r(&$conn, fine, coarse));
                    }
                    #[test]
                    fn monotone_l(f1 in any::<i64>(), f2 in any::<i64>()) {
                        let f1 = FixedI64::<$FineFrac>::from_bits(f1);
                        let f2 = FixedI64::<$FineFrac>::from_bits(f2);
                        prop_assert!(laws::conn_monotone_l(&$conn, f1, f2));
                    }
                    #[test]
                    fn monotone_r(b1 in any::<i64>(), b2 in any::<i64>()) {
                        let b1 = FixedI64::<$CoarseFrac>::from_bits(b1);
                        let b2 = FixedI64::<$CoarseFrac>::from_bits(b2);
                        prop_assert!(laws::conn_monotone_r(&$conn, b1, b2));
                    }
                    #[test]
                    fn closure_l(f in any::<i64>()) {
                        let fine = FixedI64::<$FineFrac>::from_bits(f);
                        prop_assert!(laws::conn_closure_l(&$conn, fine));
                    }
                    #[test]
                    fn closure_r(f in any::<i64>()) {
                        let fine = FixedI64::<$FineFrac>::from_bits(f);
                        prop_assert!(laws::conn_closure_r(&$conn, fine));
                    }
                    #[test]
                    fn kernel_l(b in any::<i64>()) {
                        let c = FixedI64::<$CoarseFrac>::from_bits(b);
                        prop_assert!(laws::conn_kernel_l(&$conn, c));
                    }
                    #[test]
                    fn kernel_r(b in any::<i64>()) {
                        let c = FixedI64::<$CoarseFrac>::from_bits(b);
                        prop_assert!(laws::conn_kernel_r(&$conn, c));
                    }
                    #[test]
                    fn idempotent(f in any::<i64>()) {
                        let fine = FixedI64::<$FineFrac>::from_bits(f);
                        prop_assert!(laws::conn_idempotent(&$conn, fine));
                    }
                }
            }
        };
    }

    // 15 conns × 9 properties = 135 generated proptests (64 cases each).
    props_for_pair!(f08f00, F08F00, U8,  U0);
    props_for_pair!(f16f00, F16F00, U16, U0);
    props_for_pair!(f32f00, F32F00, U32, U0);
    props_for_pair!(f48f00, F48F00, U48, U0);
    props_for_pair!(f64f00, F64F00, U64, U0);
    props_for_pair!(f16f08, F16F08, U16, U8);
    props_for_pair!(f32f08, F32F08, U32, U8);
    props_for_pair!(f48f08, F48F08, U48, U8);
    props_for_pair!(f64f08, F64F08, U64, U8);
    props_for_pair!(f32f16, F32F16, U32, U16);
    props_for_pair!(f48f16, F48F16, U48, U16);
    props_for_pair!(f64f16, F64F16, U64, U16);
    props_for_pair!(f48f32, F48F32, U48, U32);
    props_for_pair!(f64f32, F64F32, U64, U32);
    props_for_pair!(f64f48, F64F48, U64, U48);
}
