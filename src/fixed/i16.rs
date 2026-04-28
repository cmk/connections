//! Binary fixed-point ladder over `fixed::FixedI16<Frac>`.
//!
//! For each ordered pair `(FineFrac, CoarseFrac)` from the level set
//! `{0, 2, 4, 8, 12, 16}` with `FineFrac > CoarseFrac`, a
//! [`Conn`]`<FixedI16<U_fine>, FixedI16<U_coarse>>` constant
//! `F<dd>F<dd>` (zero-padded) provides the adjoint triple
//! `ceil ⊣ inner ⊣ floor`:
//!
//! - `ceil:  Fine → Coarse` smallest `c` with `inner(c) ≥ f`
//! - `inner: Coarse → Fine`  bit-shift left by `(FineFrac − CoarseFrac)`,
//!   saturating at `Fine::{MIN, MAX}`
//! - `floor: Fine → Coarse` largest `c` with `inner(c) ≤ f`
//!
//! All three are **total** (every input has a defined output) and the
//! five Galois axioms — adjointness in both halves, closure, kernel,
//! `inner` monotonicity — hold for every input. See `doc/design.md`
//! § "Triple-only properties and the role of injectivity" for the
//! reasoning behind the design.
//!
//! `inner` is **not** injective: any Coarse value where `|c.bits *
//! RATIO|` exceeds `i16::MAX` saturates to `Fine::{MIN, MAX}`,
//! collapsing a plateau of Coarse values onto a single Fine value.
//! As a consequence the
//! triple-only rounding sandwich `floor(a) ≤ ceil(a)` does not hold at
//! the saturation boundary, and is not asserted by the test suite.
//! `ceil` and `floor` carry the matching boundary fixups: `ceil(Fine::MIN)
//! = Coarse::MIN` and `floor(Fine::MAX) = Coarse::MAX`, ensuring the
//! Galois laws hold at the extremes.

use crate::conn::Conn;
use ::fixed::FixedI16;
use ::fixed::types::extra::{U0, U2, U4, U8, U12, U16, Unsigned};

/// `I<frac> = FixedI16<U<frac>>` — i16-backed binary fixed-point.
pub type I000 = FixedI16<U0>;
pub type I002 = FixedI16<U2>;
pub type I004 = FixedI16<U4>;
pub type I008 = FixedI16<U8>;
pub type I012 = FixedI16<U12>;
pub type I016 = FixedI16<U16>;

macro_rules! fix_fix_i16 {
    ($const_name:ident, $FineFrac:ty, $CoarseFrac:ty) => {
        pub const $const_name: Conn<FixedI16<$FineFrac>, FixedI16<$CoarseFrac>> = {
            const SHIFT: u32 = <$FineFrac as Unsigned>::U32 - <$CoarseFrac as Unsigned>::U32;
            // i32 covers SHIFT ∈ [1, 16]: 1 << 16 = 65 536 fits, and
            // i16::MAX × (1 << 16) = 2 147 418 112 < i32::MAX, so the
            // multiplication in `inner` cannot overflow i32 before the
            // saturating clamp.
            const RATIO: i32 = 1_i32 << SHIFT;
            const FINE_MIN: i16 = i16::MIN;
            const FINE_MAX: i16 = i16::MAX;

            fn ceil(x: FixedI16<$FineFrac>) -> FixedI16<$CoarseFrac> {
                // Boundary fixup: every Coarse value c ≤ -i16::MAX/RATIO
                // − 1 saturates inner to Fine::MIN. The Galois law
                // requires ceil(Fine::MIN) = Coarse::MIN.
                if x.to_bits() == FINE_MIN {
                    return FixedI16::<$CoarseFrac>::from_bits(i16::MIN);
                }
                let bits = x.to_bits() as i32;
                let q = bits.div_euclid(RATIO);
                let r = bits.rem_euclid(RATIO);
                let res = if r != 0 { q + 1 } else { q };
                FixedI16::from_bits(res as i16)
            }

            fn inner(x: FixedI16<$CoarseFrac>) -> FixedI16<$FineFrac> {
                let res = (x.to_bits() as i32) * RATIO;
                let saturated = if res > FINE_MAX as i32 {
                    FINE_MAX
                } else if res < FINE_MIN as i32 {
                    FINE_MIN
                } else {
                    res as i16
                };
                FixedI16::from_bits(saturated)
            }

            fn floor(x: FixedI16<$FineFrac>) -> FixedI16<$CoarseFrac> {
                // Mirror of the ceil fixup: every Coarse value c ≥
                // i16::MAX/RATIO + 1 saturates inner to Fine::MAX. The
                // Galois law requires floor(Fine::MAX) = Coarse::MAX.
                if x.to_bits() == FINE_MAX {
                    return FixedI16::<$CoarseFrac>::from_bits(i16::MAX);
                }
                let res = (x.to_bits() as i32).div_euclid(RATIO);
                FixedI16::from_bits(res as i16)
            }

            Conn::new(ceil, inner, floor)
        };
    };
}

// All ordered (Fine, Coarse) pairs from {U0, U2, U4, U8, U12, U16}
// with Fine > Coarse. 15 conns total.
fix_fix_i16!(I002I000, U2, U0);
fix_fix_i16!(I004I000, U4, U0);
fix_fix_i16!(I008I000, U8, U0);
fix_fix_i16!(I012I000, U12, U0);
fix_fix_i16!(I016I000, U16, U0);
fix_fix_i16!(I004I002, U4, U2);
fix_fix_i16!(I008I002, U8, U2);
fix_fix_i16!(I012I002, U12, U2);
fix_fix_i16!(I016I002, U16, U2);
fix_fix_i16!(I008I004, U8, U4);
fix_fix_i16!(I012I004, U12, U4);
fix_fix_i16!(I016I004, U16, U4);
fix_fix_i16!(I012I008, U12, U8);
fix_fix_i16!(I016I008, U16, U8);
fix_fix_i16!(I016I012, U16, U12);

// ────────────────────────────────────────────────────────────────────
// Tests
// ────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::property::laws;
    use proptest::prelude::*;

    // Spot checks: hand-computed rounding at exact, off-grid, and
    // saturation-boundary inputs.

    #[test]
    fn spot_i008i004_on_grid() {
        // 1.5 in Q8.8 (bits 0x0180 = 384) — exactly representable in Q12.4.
        let q88 = FixedI16::<U8>::from_bits(384);
        assert_eq!(I008I004.floor(q88), FixedI16::<U4>::from_bits(24));
        assert_eq!(I008I004.ceil(q88), FixedI16::<U4>::from_bits(24));
        assert_eq!(I008I004.inner(FixedI16::<U4>::from_bits(24)), q88);
    }

    #[test]
    fn spot_i008i004_off_grid_positive() {
        // 1.3984375 (bits 358) — between Q12.4 grid points 22 and 23.
        let off = FixedI16::<U8>::from_bits(358);
        assert_eq!(I008I004.floor(off), FixedI16::<U4>::from_bits(22));
        assert_eq!(I008I004.ceil(off), FixedI16::<U4>::from_bits(23));
    }

    #[test]
    fn spot_i008i004_off_grid_negative() {
        // -1.3984375 (bits -358). div_euclid rounds toward −∞;
        // rem_euclid is non-negative, so ceil = floor + 1.
        let neg = FixedI16::<U8>::from_bits(-358);
        assert_eq!(I008I004.floor(neg), FixedI16::<U4>::from_bits(-23));
        assert_eq!(I008I004.ceil(neg), FixedI16::<U4>::from_bits(-22));
    }

    #[test]
    fn spot_i008i004_saturation_boundary() {
        // Fine::MAX (bits 32767) ceils up to Coarse(2048) = value 128.0
        // — fits in Coarse i16 range. inner(2048) saturates to Fine::MAX.
        let fmax = FixedI16::<U8>::from_bits(i16::MAX);
        assert_eq!(I008I004.ceil(fmax), FixedI16::<U4>::from_bits(2048));
        assert_eq!(I008I004.inner(FixedI16::<U4>::from_bits(2048)), fmax);

        // Fine::MAX is in the saturation plateau: floor returns Coarse::MAX,
        // not the bit-math value 2047.
        assert_eq!(I008I004.floor(fmax), FixedI16::<U4>::from_bits(i16::MAX));

        // Symmetric on the negative side: Fine::MIN is itself a plateau
        // member; ceil returns Coarse::MIN, not bit-math -2048.
        let fmin = FixedI16::<U8>::from_bits(i16::MIN);
        assert_eq!(I008I004.ceil(fmin), FixedI16::<U4>::from_bits(i16::MIN));
        assert_eq!(I008I004.floor(fmin), FixedI16::<U4>::from_bits(-2048));
    }

    #[test]
    fn spot_i016i000_degenerate() {
        // SHIFT = 16, RATIO = 65 536. Every Coarse value with |bits| ≥ 1
        // saturates inner. Only Coarse(0) round-trips.
        assert_eq!(
            I016I000.inner(FixedI16::<U0>::from_bits(0)),
            FixedI16::<U16>::from_bits(0),
        );
        assert_eq!(
            I016I000.inner(FixedI16::<U0>::from_bits(1)),
            FixedI16::<U16>::from_bits(i16::MAX),
        );
        assert_eq!(
            I016I000.inner(FixedI16::<U0>::from_bits(-1)),
            FixedI16::<U16>::from_bits(i16::MIN),
        );
    }

    // Generator macro: nine universally-quantified Galois predicates per
    // Conn, delegating to `crate::property::laws`. All inputs span the
    // full i16 range — the connection is total and lawful for every
    // value, so no bounded strategies are needed.
    //
    // `conn_floor_le_ceil` is intentionally NOT asserted: it requires
    // injective `inner`, which fails at the saturation plateau (see
    // doc/design.md § Triple-only properties).
    macro_rules! props_for_pair {
        ($mod_name:ident, $conn:ident, $FineFrac:ty, $CoarseFrac:ty) => {
            mod $mod_name {
                use super::*;

                proptest! {
                    #[test]
                    fn galois_l(f in any::<i16>(), b in any::<i16>()) {
                        let fine = FixedI16::<$FineFrac>::from_bits(f);
                        let coarse = FixedI16::<$CoarseFrac>::from_bits(b);
                        prop_assert!(laws::conn_galois_l(&$conn, fine, coarse));
                    }

                    #[test]
                    fn galois_r(f in any::<i16>(), b in any::<i16>()) {
                        let fine = FixedI16::<$FineFrac>::from_bits(f);
                        let coarse = FixedI16::<$CoarseFrac>::from_bits(b);
                        prop_assert!(laws::conn_galois_r(&$conn, fine, coarse));
                    }

                    #[test]
                    fn monotone_l(f1 in any::<i16>(), f2 in any::<i16>()) {
                        let f1 = FixedI16::<$FineFrac>::from_bits(f1);
                        let f2 = FixedI16::<$FineFrac>::from_bits(f2);
                        prop_assert!(laws::conn_monotone_l(&$conn, f1, f2));
                    }

                    #[test]
                    fn monotone_r(b1 in any::<i16>(), b2 in any::<i16>()) {
                        let b1 = FixedI16::<$CoarseFrac>::from_bits(b1);
                        let b2 = FixedI16::<$CoarseFrac>::from_bits(b2);
                        prop_assert!(laws::conn_monotone_r(&$conn, b1, b2));
                    }

                    #[test]
                    fn closure_l(f in any::<i16>()) {
                        let fine = FixedI16::<$FineFrac>::from_bits(f);
                        prop_assert!(laws::conn_closure_l(&$conn, fine));
                    }

                    #[test]
                    fn closure_r(f in any::<i16>()) {
                        let fine = FixedI16::<$FineFrac>::from_bits(f);
                        prop_assert!(laws::conn_closure_r(&$conn, fine));
                    }

                    #[test]
                    fn kernel_l(b in any::<i16>()) {
                        let c = FixedI16::<$CoarseFrac>::from_bits(b);
                        prop_assert!(laws::conn_kernel_l(&$conn, c));
                    }

                    #[test]
                    fn kernel_r(b in any::<i16>()) {
                        let c = FixedI16::<$CoarseFrac>::from_bits(b);
                        prop_assert!(laws::conn_kernel_r(&$conn, c));
                    }

                    #[test]
                    fn idempotent(f in any::<i16>()) {
                        let fine = FixedI16::<$FineFrac>::from_bits(f);
                        prop_assert!(laws::conn_idempotent(&$conn, fine));
                    }
                }
            }
        };
    }

    // 15 conns × 9 properties = 135 generated proptests.
    props_for_pair!(i002i000, I002I000, U2, U0);
    props_for_pair!(i004i000, I004I000, U4, U0);
    props_for_pair!(i008i000, I008I000, U8, U0);
    props_for_pair!(i012i000, I012I000, U12, U0);
    props_for_pair!(i016i000, I016I000, U16, U0);
    props_for_pair!(i004i002, I004I002, U4, U2);
    props_for_pair!(i008i002, I008I002, U8, U2);
    props_for_pair!(i012i002, I012I002, U12, U2);
    props_for_pair!(i016i002, I016I002, U16, U2);
    props_for_pair!(i008i004, I008I004, U8, U4);
    props_for_pair!(i012i004, I012I004, U12, U4);
    props_for_pair!(i016i004, I016I004, U16, U4);
    props_for_pair!(i012i008, I012I008, U12, U8);
    props_for_pair!(i016i008, I016I008, U16, U8);
    props_for_pair!(i016i012, I016I012, U16, U12);
}
