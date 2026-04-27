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

/// `I<frac> = FixedI8<U<frac>>` — i8-backed binary fixed-point with
/// `<frac>` fractional bits. Frac digits are zero-padded to 3 chars
/// to fit the X123Y456 conn-name shape.
pub type I000 = FixedI8<U0>;
pub type I001 = FixedI8<U1>;
pub type I002 = FixedI8<U2>;
pub type I003 = FixedI8<U3>;
pub type I004 = FixedI8<U4>;
pub type I006 = FixedI8<U6>;
pub type I008 = FixedI8<U8>;

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
fix_fix_i08!(I001I000, U1, U0);
fix_fix_i08!(I002I000, U2, U0);
fix_fix_i08!(I003I000, U3, U0);
fix_fix_i08!(I004I000, U4, U0);
fix_fix_i08!(I006I000, U6, U0);
fix_fix_i08!(I008I000, U8, U0);
fix_fix_i08!(I002I001, U2, U1);
fix_fix_i08!(I003I001, U3, U1);
fix_fix_i08!(I004I001, U4, U1);
fix_fix_i08!(I006I001, U6, U1);
fix_fix_i08!(I008I001, U8, U1);
fix_fix_i08!(I003I002, U3, U2);
fix_fix_i08!(I004I002, U4, U2);
fix_fix_i08!(I006I002, U6, U2);
fix_fix_i08!(I008I002, U8, U2);
fix_fix_i08!(I004I003, U4, U3);
fix_fix_i08!(I006I003, U6, U3);
fix_fix_i08!(I008I003, U8, U3);
fix_fix_i08!(I006I004, U6, U4);
fix_fix_i08!(I008I004, U8, U4);
fix_fix_i08!(I008I006, U8, U6);

// ────────────────────────────────────────────────────────────────────
// Tests
// ────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::property::laws;
    use proptest::prelude::*;

    #[test]
    fn spot_i004i000_on_grid() {
        // 1.5 in Q4.4 (bits 24) — exactly representable in Q8.0 by 1 or 2.
        let q44 = FixedI8::<U4>::from_bits(24);
        assert_eq!(I004I000.floor(q44), FixedI8::<U0>::from_bits(1));
        assert_eq!(I004I000.ceil(q44), FixedI8::<U0>::from_bits(2));
        assert_eq!(I004I000.inner(FixedI8::<U0>::from_bits(1)), FixedI8::<U4>::from_bits(16));
    }

    #[test]
    fn spot_i004i000_negative() {
        let q44 = FixedI8::<U4>::from_bits(-24);
        assert_eq!(I004I000.floor(q44), FixedI8::<U0>::from_bits(-2));
        assert_eq!(I004I000.ceil(q44), FixedI8::<U0>::from_bits(-1));
    }

    #[test]
    fn spot_i008i000_degenerate() {
        // SHIFT = 8, RATIO = 256. Only Coarse(0) round-trips; |bits| ≥ 1
        // saturates inner.
        assert_eq!(
            I008I000.inner(FixedI8::<U0>::from_bits(0)),
            FixedI8::<U8>::from_bits(0),
        );
        assert_eq!(
            I008I000.inner(FixedI8::<U0>::from_bits(1)),
            FixedI8::<U8>::from_bits(i8::MAX),
        );
        assert_eq!(
            I008I000.inner(FixedI8::<U0>::from_bits(-1)),
            FixedI8::<U8>::from_bits(i8::MIN),
        );
    }

    #[test]
    fn spot_boundary_fixups() {
        // Fine::MIN/MAX boundary fixups exercised on I004I000 (RATIO = 16).
        let fmin = FixedI8::<U4>::from_bits(i8::MIN);
        let fmax = FixedI8::<U4>::from_bits(i8::MAX);
        assert_eq!(I004I000.ceil(fmin), FixedI8::<U0>::from_bits(i8::MIN));
        assert_eq!(I004I000.floor(fmax), FixedI8::<U0>::from_bits(i8::MAX));
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
    props_for_pair!(i001i000, I001I000, U1, U0);
    props_for_pair!(i002i000, I002I000, U2, U0);
    props_for_pair!(i003i000, I003I000, U3, U0);
    props_for_pair!(i004i000, I004I000, U4, U0);
    props_for_pair!(i006i000, I006I000, U6, U0);
    props_for_pair!(i008i000, I008I000, U8, U0);
    props_for_pair!(i002i001, I002I001, U2, U1);
    props_for_pair!(i003i001, I003I001, U3, U1);
    props_for_pair!(i004i001, I004I001, U4, U1);
    props_for_pair!(i006i001, I006I001, U6, U1);
    props_for_pair!(i008i001, I008I001, U8, U1);
    props_for_pair!(i003i002, I003I002, U3, U2);
    props_for_pair!(i004i002, I004I002, U4, U2);
    props_for_pair!(i006i002, I006I002, U6, U2);
    props_for_pair!(i008i002, I008I002, U8, U2);
    props_for_pair!(i004i003, I004I003, U4, U3);
    props_for_pair!(i006i003, I006I003, U6, U3);
    props_for_pair!(i008i003, I008I003, U8, U3);
    props_for_pair!(i006i004, I006I004, U6, U4);
    props_for_pair!(i008i004, I008I004, U8, U4);
    props_for_pair!(i008i006, I008I006, U8, U6);
}
