//! Binary fixed-point ladder over `fixed::FixedI32<Frac>`.
//!
//! Frac level set: `{U0, U4, U8, U16, U24, U32}` → 15 ordered pairs
//! `(Fine, Coarse)` with `Fine > Coarse`. See [`super::i16`] for the
//! design (this module mirrors it with `i32` inner / `i64` widening).

use crate::conn::Conn;
use ::fixed::FixedI32;
use ::fixed::types::extra::{U0, U4, U8, U16, U24, U32, Unsigned};

macro_rules! fix_fix_i32 {
    ($const_name:ident, $FineFrac:ty, $CoarseFrac:ty) => {
        pub const $const_name: Conn<FixedI32<$FineFrac>, FixedI32<$CoarseFrac>> = {
            const SHIFT: u32 = <$FineFrac as Unsigned>::U32 - <$CoarseFrac as Unsigned>::U32;
            // i64 covers SHIFT ∈ [1, 32]: 1 << 32 fits, and
            // i32::MAX × (1 << 32) ≈ 2^63 < i64::MAX.
            const RATIO: i64 = 1_i64 << SHIFT;
            const FINE_MIN: i32 = i32::MIN;
            const FINE_MAX: i32 = i32::MAX;

            fn ceil(x: FixedI32<$FineFrac>) -> FixedI32<$CoarseFrac> {
                if x.to_bits() == FINE_MIN {
                    return FixedI32::from_bits(FINE_MIN);
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
                    return FixedI32::from_bits(FINE_MAX);
                }
                let res = (x.to_bits() as i64).div_euclid(RATIO);
                FixedI32::from_bits(res as i32)
            }

            Conn::new(ceil, inner, floor)
        };
    };
}

// 15 ordered pairs from {U0, U4, U8, U16, U24, U32}.
fix_fix_i32!(F04F00, U4,  U0);
fix_fix_i32!(F08F00, U8,  U0);
fix_fix_i32!(F16F00, U16, U0);
fix_fix_i32!(F24F00, U24, U0);
fix_fix_i32!(F32F00, U32, U0);
fix_fix_i32!(F08F04, U8,  U4);
fix_fix_i32!(F16F04, U16, U4);
fix_fix_i32!(F24F04, U24, U4);
fix_fix_i32!(F32F04, U32, U4);
fix_fix_i32!(F16F08, U16, U8);
fix_fix_i32!(F24F08, U24, U8);
fix_fix_i32!(F32F08, U32, U8);
fix_fix_i32!(F24F16, U24, U16);
fix_fix_i32!(F32F16, U32, U16);
fix_fix_i32!(F32F24, U32, U24);

// ────────────────────────────────────────────────────────────────────
// Tests
// ────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::property::laws;
    use proptest::prelude::*;

    #[test]
    fn spot_f16f08_on_grid() {
        // 1.5 in Q16.16 (bits = 1.5 × 2^16 = 98304); same value in Q24.8
        // is bits 384.
        let q1616 = FixedI32::<U16>::from_bits(98304);
        assert_eq!(F16F08.floor(q1616), FixedI32::<U8>::from_bits(384));
        assert_eq!(F16F08.ceil(q1616), FixedI32::<U8>::from_bits(384));
        assert_eq!(F16F08.inner(FixedI32::<U8>::from_bits(384)), q1616);
    }

    #[test]
    fn spot_f32f00_degenerate() {
        // SHIFT = 32. Only Coarse(0) round-trips.
        assert_eq!(
            F32F00.inner(FixedI32::<U0>::from_bits(0)),
            FixedI32::<U32>::from_bits(0),
        );
        assert_eq!(
            F32F00.inner(FixedI32::<U0>::from_bits(1)),
            FixedI32::<U32>::from_bits(i32::MAX),
        );
    }

    #[test]
    fn spot_boundary_fixups() {
        let fmin = FixedI32::<U16>::from_bits(i32::MIN);
        let fmax = FixedI32::<U16>::from_bits(i32::MAX);
        assert_eq!(F16F08.ceil(fmin), FixedI32::<U8>::from_bits(i32::MIN));
        assert_eq!(F16F08.floor(fmax), FixedI32::<U8>::from_bits(i32::MAX));
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
                        prop_assert!(laws::conn_galois_l(&$conn, fine, coarse));
                    }
                    #[test]
                    fn galois_r(f in any::<i32>(), b in any::<i32>()) {
                        let fine = FixedI32::<$FineFrac>::from_bits(f);
                        let coarse = FixedI32::<$CoarseFrac>::from_bits(b);
                        prop_assert!(laws::conn_galois_r(&$conn, fine, coarse));
                    }
                    #[test]
                    fn monotone_l(f1 in any::<i32>(), f2 in any::<i32>()) {
                        let f1 = FixedI32::<$FineFrac>::from_bits(f1);
                        let f2 = FixedI32::<$FineFrac>::from_bits(f2);
                        prop_assert!(laws::conn_monotone_l(&$conn, f1, f2));
                    }
                    #[test]
                    fn monotone_r(b1 in any::<i32>(), b2 in any::<i32>()) {
                        let b1 = FixedI32::<$CoarseFrac>::from_bits(b1);
                        let b2 = FixedI32::<$CoarseFrac>::from_bits(b2);
                        prop_assert!(laws::conn_monotone_r(&$conn, b1, b2));
                    }
                    #[test]
                    fn closure_l(f in any::<i32>()) {
                        let fine = FixedI32::<$FineFrac>::from_bits(f);
                        prop_assert!(laws::conn_closure_l(&$conn, fine));
                    }
                    #[test]
                    fn closure_r(f in any::<i32>()) {
                        let fine = FixedI32::<$FineFrac>::from_bits(f);
                        prop_assert!(laws::conn_closure_r(&$conn, fine));
                    }
                    #[test]
                    fn kernel_l(b in any::<i32>()) {
                        let c = FixedI32::<$CoarseFrac>::from_bits(b);
                        prop_assert!(laws::conn_kernel_l(&$conn, c));
                    }
                    #[test]
                    fn kernel_r(b in any::<i32>()) {
                        let c = FixedI32::<$CoarseFrac>::from_bits(b);
                        prop_assert!(laws::conn_kernel_r(&$conn, c));
                    }
                    #[test]
                    fn idempotent(f in any::<i32>()) {
                        let fine = FixedI32::<$FineFrac>::from_bits(f);
                        prop_assert!(laws::conn_idempotent(&$conn, fine));
                    }
                }
            }
        };
    }

    // 15 conns × 9 properties = 135 generated proptests.
    props_for_pair!(f04f00, F04F00, U4,  U0);
    props_for_pair!(f08f00, F08F00, U8,  U0);
    props_for_pair!(f16f00, F16F00, U16, U0);
    props_for_pair!(f24f00, F24F00, U24, U0);
    props_for_pair!(f32f00, F32F00, U32, U0);
    props_for_pair!(f08f04, F08F04, U8,  U4);
    props_for_pair!(f16f04, F16F04, U16, U4);
    props_for_pair!(f24f04, F24F04, U24, U4);
    props_for_pair!(f32f04, F32F04, U32, U4);
    props_for_pair!(f16f08, F16F08, U16, U8);
    props_for_pair!(f24f08, F24F08, U24, U8);
    props_for_pair!(f32f08, F32F08, U32, U8);
    props_for_pair!(f24f16, F24F16, U24, U16);
    props_for_pair!(f32f16, F32F16, U32, U16);
    props_for_pair!(f32f24, F32F24, U32, U24);
}
