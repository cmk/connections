//! Binary fixed-point ladder over `fixed::FixedI8<Frac>`.
//!
//! Frac level set: `{U0, U1, U2, U3, U4, U6, U8}` → 21 ordered pairs
//! `(Fine, Coarse)` with `Fine > Coarse`. See [`super::i16`] for the
//! design (this module mirrors it with `i8` inner / `i16` widening).
//! Same totality + Galois-axiom guarantees; same saturation plateau,
//! and the same boundary fixups in `ceil` / `floor`.

use crate::conn::Conn;
use ::fixed::FixedI8;
use ::fixed::types::extra::{U0, U1, U2, U3, U4, U6, U8, Unsigned};

macro_rules! fix_fix_i08 {
    ($const_name:ident, $FineFrac:ty, $CoarseFrac:ty) => {
        pub const $const_name: Conn<FixedI8<$FineFrac>, FixedI8<$CoarseFrac>> = {
            const SHIFT: u32 = <$FineFrac as Unsigned>::U32 - <$CoarseFrac as Unsigned>::U32;
            // i16 covers SHIFT ∈ [1, 8]: 1 << 8 = 256 fits, and
            // i8::MAX × 256 = 32 512 < i16::MAX.
            const RATIO: i16 = 1_i16 << SHIFT;
            const FINE_MIN: i8 = i8::MIN;
            const FINE_MAX: i8 = i8::MAX;

            fn ceil(x: FixedI8<$FineFrac>) -> FixedI8<$CoarseFrac> {
                if x.to_bits() == FINE_MIN {
                    return FixedI8::<$CoarseFrac>::from_bits(i8::MIN);
                }
                let bits = x.to_bits() as i16;
                let q = bits.div_euclid(RATIO);
                let r = bits.rem_euclid(RATIO);
                let res = if r != 0 { q + 1 } else { q };
                FixedI8::from_bits(res as i8)
            }

            fn inner(x: FixedI8<$CoarseFrac>) -> FixedI8<$FineFrac> {
                let res = (x.to_bits() as i16) * RATIO;
                let saturated = if res > FINE_MAX as i16 {
                    FINE_MAX
                } else if res < FINE_MIN as i16 {
                    FINE_MIN
                } else {
                    res as i8
                };
                FixedI8::from_bits(saturated)
            }

            fn floor(x: FixedI8<$FineFrac>) -> FixedI8<$CoarseFrac> {
                if x.to_bits() == FINE_MAX {
                    return FixedI8::<$CoarseFrac>::from_bits(i8::MAX);
                }
                let res = (x.to_bits() as i16).div_euclid(RATIO);
                FixedI8::from_bits(res as i8)
            }

            Conn::new(ceil, inner, floor)
        };
    };
}

// 21 ordered pairs from {U0, U1, U2, U3, U4, U6, U8}.
fix_fix_i08!(F01F00, U1, U0);
fix_fix_i08!(F02F00, U2, U0);
fix_fix_i08!(F03F00, U3, U0);
fix_fix_i08!(F04F00, U4, U0);
fix_fix_i08!(F06F00, U6, U0);
fix_fix_i08!(F08F00, U8, U0);
fix_fix_i08!(F02F01, U2, U1);
fix_fix_i08!(F03F01, U3, U1);
fix_fix_i08!(F04F01, U4, U1);
fix_fix_i08!(F06F01, U6, U1);
fix_fix_i08!(F08F01, U8, U1);
fix_fix_i08!(F03F02, U3, U2);
fix_fix_i08!(F04F02, U4, U2);
fix_fix_i08!(F06F02, U6, U2);
fix_fix_i08!(F08F02, U8, U2);
fix_fix_i08!(F04F03, U4, U3);
fix_fix_i08!(F06F03, U6, U3);
fix_fix_i08!(F08F03, U8, U3);
fix_fix_i08!(F06F04, U6, U4);
fix_fix_i08!(F08F04, U8, U4);
fix_fix_i08!(F08F06, U8, U6);

// ────────────────────────────────────────────────────────────────────
// Tests
// ────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::property::laws;
    use proptest::prelude::*;

    #[test]
    fn spot_f04f00_on_grid() {
        // 1.5 in Q4.4 (bits 24) — exactly representable in Q8.0 by 1 or 2.
        let q44 = FixedI8::<U4>::from_bits(24);
        assert_eq!(F04F00.floor(q44), FixedI8::<U0>::from_bits(1));
        assert_eq!(F04F00.ceil(q44), FixedI8::<U0>::from_bits(2));
        assert_eq!(F04F00.inner(FixedI8::<U0>::from_bits(1)), FixedI8::<U4>::from_bits(16));
    }

    #[test]
    fn spot_f04f00_negative() {
        let q44 = FixedI8::<U4>::from_bits(-24);
        assert_eq!(F04F00.floor(q44), FixedI8::<U0>::from_bits(-2));
        assert_eq!(F04F00.ceil(q44), FixedI8::<U0>::from_bits(-1));
    }

    #[test]
    fn spot_f08f00_degenerate() {
        // SHIFT = 8, RATIO = 256. Only Coarse(0) round-trips; |bits| ≥ 1
        // saturates inner.
        assert_eq!(
            F08F00.inner(FixedI8::<U0>::from_bits(0)),
            FixedI8::<U8>::from_bits(0),
        );
        assert_eq!(
            F08F00.inner(FixedI8::<U0>::from_bits(1)),
            FixedI8::<U8>::from_bits(i8::MAX),
        );
        assert_eq!(
            F08F00.inner(FixedI8::<U0>::from_bits(-1)),
            FixedI8::<U8>::from_bits(i8::MIN),
        );
    }

    #[test]
    fn spot_boundary_fixups() {
        // Fine::MIN/MAX boundary fixups exercised on F04F00 (RATIO = 16).
        let fmin = FixedI8::<U4>::from_bits(i8::MIN);
        let fmax = FixedI8::<U4>::from_bits(i8::MAX);
        assert_eq!(F04F00.ceil(fmin), FixedI8::<U0>::from_bits(i8::MIN));
        assert_eq!(F04F00.floor(fmax), FixedI8::<U0>::from_bits(i8::MAX));
    }

    // See `super::i16::tests::props_for_pair!` for the design rationale.
    macro_rules! props_for_pair {
        ($mod_name:ident, $conn:ident, $FineFrac:ty, $CoarseFrac:ty) => {
            mod $mod_name {
                use super::*;

                proptest! {
                    #[test]
                    fn galois_l(f in any::<i8>(), b in any::<i8>()) {
                        let fine = FixedI8::<$FineFrac>::from_bits(f);
                        let coarse = FixedI8::<$CoarseFrac>::from_bits(b);
                        prop_assert!(laws::conn_galois_l(&$conn, fine, coarse));
                    }
                    #[test]
                    fn galois_r(f in any::<i8>(), b in any::<i8>()) {
                        let fine = FixedI8::<$FineFrac>::from_bits(f);
                        let coarse = FixedI8::<$CoarseFrac>::from_bits(b);
                        prop_assert!(laws::conn_galois_r(&$conn, fine, coarse));
                    }
                    #[test]
                    fn monotone_l(f1 in any::<i8>(), f2 in any::<i8>()) {
                        let f1 = FixedI8::<$FineFrac>::from_bits(f1);
                        let f2 = FixedI8::<$FineFrac>::from_bits(f2);
                        prop_assert!(laws::conn_monotone_l(&$conn, f1, f2));
                    }
                    #[test]
                    fn monotone_r(b1 in any::<i8>(), b2 in any::<i8>()) {
                        let b1 = FixedI8::<$CoarseFrac>::from_bits(b1);
                        let b2 = FixedI8::<$CoarseFrac>::from_bits(b2);
                        prop_assert!(laws::conn_monotone_r(&$conn, b1, b2));
                    }
                    #[test]
                    fn closure_l(f in any::<i8>()) {
                        let fine = FixedI8::<$FineFrac>::from_bits(f);
                        prop_assert!(laws::conn_closure_l(&$conn, fine));
                    }
                    #[test]
                    fn closure_r(f in any::<i8>()) {
                        let fine = FixedI8::<$FineFrac>::from_bits(f);
                        prop_assert!(laws::conn_closure_r(&$conn, fine));
                    }
                    #[test]
                    fn kernel_l(b in any::<i8>()) {
                        let c = FixedI8::<$CoarseFrac>::from_bits(b);
                        prop_assert!(laws::conn_kernel_l(&$conn, c));
                    }
                    #[test]
                    fn kernel_r(b in any::<i8>()) {
                        let c = FixedI8::<$CoarseFrac>::from_bits(b);
                        prop_assert!(laws::conn_kernel_r(&$conn, c));
                    }
                    #[test]
                    fn idempotent(f in any::<i8>()) {
                        let fine = FixedI8::<$FineFrac>::from_bits(f);
                        prop_assert!(laws::conn_idempotent(&$conn, fine));
                    }
                }
            }
        };
    }

    // 21 conns × 9 properties = 189 generated proptests.
    props_for_pair!(f01f00, F01F00, U1, U0);
    props_for_pair!(f02f00, F02F00, U2, U0);
    props_for_pair!(f03f00, F03F00, U3, U0);
    props_for_pair!(f04f00, F04F00, U4, U0);
    props_for_pair!(f06f00, F06F00, U6, U0);
    props_for_pair!(f08f00, F08F00, U8, U0);
    props_for_pair!(f02f01, F02F01, U2, U1);
    props_for_pair!(f03f01, F03F01, U3, U1);
    props_for_pair!(f04f01, F04F01, U4, U1);
    props_for_pair!(f06f01, F06F01, U6, U1);
    props_for_pair!(f08f01, F08F01, U8, U1);
    props_for_pair!(f03f02, F03F02, U3, U2);
    props_for_pair!(f04f02, F04F02, U4, U2);
    props_for_pair!(f06f02, F06F02, U6, U2);
    props_for_pair!(f08f02, F08F02, U8, U2);
    props_for_pair!(f04f03, F04F03, U4, U3);
    props_for_pair!(f06f03, F06F03, U6, U3);
    props_for_pair!(f08f03, F08F03, U8, U3);
    props_for_pair!(f06f04, F06F04, U6, U4);
    props_for_pair!(f08f04, F08F04, U8, U4);
    props_for_pair!(f08f06, F08F06, U8, U6);
}
