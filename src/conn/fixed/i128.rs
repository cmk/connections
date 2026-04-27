//! Binary fixed-point ladder over `fixed::FixedI128<Frac>`.
//!
//! Frac level set: `{U0, U16, U32, U64, U96, U128}` → 15 ordered pairs
//! `(Fine, Coarse)` with `Fine > Coarse`. See [`super::i64`] for the
//! design template; this module differs in one substantive way:
//!
//! Stable Rust has no native `i256` to widen through, so the i64-style
//! `(x.to_bits() as i128) * RATIO` pattern doesn't compose. Instead we
//! use [`i128::checked_mul`] + saturate, and [`i128::checked_shl`] to
//! detect the `SHIFT == 128` degenerate case (`I128I000`, where
//! `RATIO = 2^128` doesn't fit in `i128` at all).
//!
//! Bit-identical outputs to a hypothetical i256-widening implementation
//! at every input: both saturate at `i128::MIN` / `i128::MAX` whenever
//! the product would overflow; `checked_mul` is the smaller, SMT-cleaner
//! encoding (`Some(x*y) iff fits, else None`). Galois laws hold by the
//! same construction as the smaller modules.

use crate::conn::Conn;
use ::fixed::FixedI128;
use ::fixed::types::extra::{U0, U16, U32, U64, U96, U128, Unsigned};

/// `I<frac> = FixedI128<U<frac>>` — i128-backed binary fixed-point.
pub type I000 = FixedI128<U0>;
pub type I016 = FixedI128<U16>;
pub type I032 = FixedI128<U32>;
pub type I064 = FixedI128<U64>;
pub type I096 = FixedI128<U96>;
pub type I128 = FixedI128<U128>;

macro_rules! fix_fix_i128 {
    ($const_name:ident, $FineFrac:ty, $CoarseFrac:ty) => {
        pub const $const_name: Conn<FixedI128<$FineFrac>, FixedI128<$CoarseFrac>> = {
            const SHIFT: u32 = <$FineFrac as Unsigned>::U32 - <$CoarseFrac as Unsigned>::U32;
            // For SHIFT < 128, RATIO = 2^SHIFT fits in i128 as a positive
            // value (max 2^126; one below i128::MAX = 2^127 − 1). For
            // SHIFT == 128 the shift is degenerate — `1_i128.checked_shl(128)`
            // returns None, and we route through the `None` arms below
            // for the I128I000 endpoint.
            const RATIO: Option<i128> = 1_i128.checked_shl(SHIFT);
            const FINE_MIN: i128 = i128::MIN;
            const FINE_MAX: i128 = i128::MAX;

            fn ceil(x: FixedI128<$FineFrac>) -> FixedI128<$CoarseFrac> {
                if x.to_bits() == FINE_MIN {
                    return FixedI128::<$CoarseFrac>::from_bits(i128::MIN);
                }
                let bits = x.to_bits();
                match RATIO {
                    Some(r) => {
                        let q = bits.div_euclid(r);
                        let res = if bits.rem_euclid(r) != 0 { q + 1 } else { q };
                        FixedI128::from_bits(res)
                    }
                    None => {
                        // SHIFT == 128 (I128I000). For any bits ∈ i128,
                        // |bits| < 2^127, so |bits / 2^128| < 0.5.
                        // ceil: bits > 0 → 1; bits ≤ 0 → 0 (FINE_MIN
                        // is already short-circuited above).
                        if bits > 0 {
                            FixedI128::from_bits(1)
                        } else {
                            FixedI128::from_bits(0)
                        }
                    }
                }
            }

            fn inner(x: FixedI128<$CoarseFrac>) -> FixedI128<$FineFrac> {
                let bits = x.to_bits();
                let saturated = match RATIO {
                    Some(r) => match bits.checked_mul(r) {
                        Some(v) => v,
                        None => {
                            if bits > 0 {
                                FINE_MAX
                            } else {
                                FINE_MIN
                            }
                        }
                    },
                    None => {
                        // SHIFT == 128: bits × 2^128 only fits when bits = 0.
                        if bits == 0 {
                            0
                        } else if bits > 0 {
                            FINE_MAX
                        } else {
                            FINE_MIN
                        }
                    }
                };
                FixedI128::from_bits(saturated)
            }

            fn floor(x: FixedI128<$FineFrac>) -> FixedI128<$CoarseFrac> {
                if x.to_bits() == FINE_MAX {
                    return FixedI128::<$CoarseFrac>::from_bits(i128::MAX);
                }
                let bits = x.to_bits();
                match RATIO {
                    Some(r) => FixedI128::from_bits(bits.div_euclid(r)),
                    None => {
                        // SHIFT == 128. floor(bits / 2^128):
                        //   bits ≥ 0 → 0; bits < 0 → -1 (FINE_MAX
                        //   already short-circuited).
                        if bits < 0 {
                            FixedI128::from_bits(-1)
                        } else {
                            FixedI128::from_bits(0)
                        }
                    }
                }
            }

            Conn::new(ceil, inner, floor)
        };
    };
}

// 15 ordered pairs from {U0, U16, U32, U64, U96, U128}.
fix_fix_i128!(I016I000, U16, U0);
fix_fix_i128!(I032I000, U32, U0);
fix_fix_i128!(I064I000, U64, U0);
fix_fix_i128!(I096I000, U96, U0);
fix_fix_i128!(I128I000, U128, U0);
fix_fix_i128!(I032I016, U32, U16);
fix_fix_i128!(I064I016, U64, U16);
fix_fix_i128!(I096I016, U96, U16);
fix_fix_i128!(I128I016, U128, U16);
fix_fix_i128!(I064I032, U64, U32);
fix_fix_i128!(I096I032, U96, U32);
fix_fix_i128!(I128I032, U128, U32);
fix_fix_i128!(I096I064, U96, U64);
fix_fix_i128!(I128I064, U128, U64);
fix_fix_i128!(I128I096, U128, U96);

// ────────────────────────────────────────────────────────────────────
// Tests
// ────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::property::laws;
    use proptest::prelude::*;

    /// Regression for the SHIFT=128 endpoint: RATIO doesn't fit i128;
    /// only Coarse(0) round-trips.
    #[test]
    fn degenerate_max_shift() {
        // inner: only 0 stays in range; everything else saturates.
        assert_eq!(
            I128I000.inner(FixedI128::<U0>::from_bits(0)),
            FixedI128::<U128>::from_bits(0),
        );
        assert_eq!(
            I128I000.inner(FixedI128::<U0>::from_bits(1)),
            FixedI128::<U128>::from_bits(i128::MAX),
        );
        assert_eq!(
            I128I000.inner(FixedI128::<U0>::from_bits(-1)),
            FixedI128::<U128>::from_bits(i128::MIN),
        );
        // ceil: positive inputs round up to 1; non-positive (and non-MIN)
        // round to 0; MIN takes the i128::MIN boundary fixup.
        assert_eq!(
            I128I000.ceil(FixedI128::<U128>::from_bits(0)),
            FixedI128::<U0>::from_bits(0),
        );
        assert_eq!(
            I128I000.ceil(FixedI128::<U128>::from_bits(1)),
            FixedI128::<U0>::from_bits(1),
        );
        assert_eq!(
            I128I000.ceil(FixedI128::<U128>::from_bits(-1)),
            FixedI128::<U0>::from_bits(0),
        );
        assert_eq!(
            I128I000.ceil(FixedI128::<U128>::from_bits(i128::MIN)),
            FixedI128::<U0>::from_bits(i128::MIN),
        );
        // floor: negative inputs round down to -1; non-negative (and
        // non-MAX) round to 0; MAX takes the i128::MAX boundary fixup.
        assert_eq!(
            I128I000.floor(FixedI128::<U128>::from_bits(0)),
            FixedI128::<U0>::from_bits(0),
        );
        assert_eq!(
            I128I000.floor(FixedI128::<U128>::from_bits(1)),
            FixedI128::<U0>::from_bits(0),
        );
        assert_eq!(
            I128I000.floor(FixedI128::<U128>::from_bits(-1)),
            FixedI128::<U0>::from_bits(-1),
        );
        assert_eq!(
            I128I000.floor(FixedI128::<U128>::from_bits(i128::MAX)),
            FixedI128::<U0>::from_bits(i128::MAX),
        );
        // Per the truth table, `floor(FINE_MIN)` falls into the
        // degenerate `bits < 0` branch (the FINE_MAX guard does not
        // fire) and returns -1. Pin this explicitly so the regression
        // is exhaustive across all 9 truth-table rows.
        assert_eq!(
            I128I000.floor(FixedI128::<U128>::from_bits(i128::MIN)),
            FixedI128::<U0>::from_bits(-1),
        );
    }

    #[test]
    fn spot_i128i064_on_grid() {
        // 1.5 in Q64.64 (bits = 1.5 × 2^64) round-trips through Q64.64
        // (no, the Coarse side has Frac=64, so Q64.64). Pick a value
        // where the Fine bits are an exact multiple of 2^(128-64) = 2^64.
        // bits_fine = 3 × 2^63 represents 1.5 in Q0.128. inner(coarse=3<<63)
        // multiplies through 2^64 — overflow, saturate.
        // Instead use a small value: coarse = 1 represents 2^-64.
        // inner(1) = 1 × 2^64 = 2^64, fits.
        let coarse_one = FixedI128::<U64>::from_bits(1);
        let fine_via_inner = I128I064.inner(coarse_one);
        assert_eq!(fine_via_inner, FixedI128::<U128>::from_bits(1_i128 << 64));
    }

    #[test]
    fn spot_boundary_fixups() {
        // Fine::MIN/MAX boundary fixups — exercised on I128I064 (SHIFT=64).
        let fmin = FixedI128::<U128>::from_bits(i128::MIN);
        let fmax = FixedI128::<U128>::from_bits(i128::MAX);
        assert_eq!(I128I064.ceil(fmin), FixedI128::<U64>::from_bits(i128::MIN));
        assert_eq!(I128I064.floor(fmax), FixedI128::<U64>::from_bits(i128::MAX));
    }

    /// Inner-saturation regression: for non-degenerate pairs where the
    /// SHIFT is large enough that a non-zero coarse bit overflows the
    /// fine i128 range, inner saturates rather than wrapping.
    #[test]
    fn inner_saturates_on_overflow() {
        // I128I016: SHIFT=112. Coarse = i128::MAX → product = i128::MAX
        // × 2^112 ≫ i128::MAX, so checked_mul returns None and we
        // saturate to FINE_MAX.
        let big_coarse = FixedI128::<U16>::from_bits(i128::MAX);
        assert_eq!(
            I128I016.inner(big_coarse),
            FixedI128::<U128>::from_bits(i128::MAX),
        );
        let neg_coarse = FixedI128::<U16>::from_bits(i128::MIN);
        assert_eq!(
            I128I016.inner(neg_coarse),
            FixedI128::<U128>::from_bits(i128::MIN),
        );
    }

    // See `super::i16::tests::props_for_pair!` for the design rationale.
    // i128 generators are expensive; cap proptest case count to 64.
    macro_rules! props_for_pair {
        ($mod_name:ident, $conn:ident, $FineFrac:ty, $CoarseFrac:ty) => {
            mod $mod_name {
                use super::*;

                proptest! {
                    #![proptest_config(ProptestConfig::with_cases(64))]

                    #[test]
                    fn galois_l(f in any::<i128>(), b in any::<i128>()) {
                        let fine = FixedI128::<$FineFrac>::from_bits(f);
                        let coarse = FixedI128::<$CoarseFrac>::from_bits(b);
                        prop_assert!(laws::conn_galois_l(&$conn, fine, coarse));
                    }
                    #[test]
                    fn galois_r(f in any::<i128>(), b in any::<i128>()) {
                        let fine = FixedI128::<$FineFrac>::from_bits(f);
                        let coarse = FixedI128::<$CoarseFrac>::from_bits(b);
                        prop_assert!(laws::conn_galois_r(&$conn, fine, coarse));
                    }
                    #[test]
                    fn monotone_l(f1 in any::<i128>(), f2 in any::<i128>()) {
                        let f1 = FixedI128::<$FineFrac>::from_bits(f1);
                        let f2 = FixedI128::<$FineFrac>::from_bits(f2);
                        prop_assert!(laws::conn_monotone_l(&$conn, f1, f2));
                    }
                    #[test]
                    fn monotone_r(b1 in any::<i128>(), b2 in any::<i128>()) {
                        let b1 = FixedI128::<$CoarseFrac>::from_bits(b1);
                        let b2 = FixedI128::<$CoarseFrac>::from_bits(b2);
                        prop_assert!(laws::conn_monotone_r(&$conn, b1, b2));
                    }
                    #[test]
                    fn closure_l(f in any::<i128>()) {
                        let fine = FixedI128::<$FineFrac>::from_bits(f);
                        prop_assert!(laws::conn_closure_l(&$conn, fine));
                    }
                    #[test]
                    fn closure_r(f in any::<i128>()) {
                        let fine = FixedI128::<$FineFrac>::from_bits(f);
                        prop_assert!(laws::conn_closure_r(&$conn, fine));
                    }
                    #[test]
                    fn kernel_l(b in any::<i128>()) {
                        let c = FixedI128::<$CoarseFrac>::from_bits(b);
                        prop_assert!(laws::conn_kernel_l(&$conn, c));
                    }
                    #[test]
                    fn kernel_r(b in any::<i128>()) {
                        let c = FixedI128::<$CoarseFrac>::from_bits(b);
                        prop_assert!(laws::conn_kernel_r(&$conn, c));
                    }
                    #[test]
                    fn idempotent(f in any::<i128>()) {
                        let fine = FixedI128::<$FineFrac>::from_bits(f);
                        prop_assert!(laws::conn_idempotent(&$conn, fine));
                    }
                }
            }
        };
    }

    // 15 conns × 9 properties = 135 generated proptests (64 cases each).
    props_for_pair!(i016i000, I016I000, U16, U0);
    props_for_pair!(i032i000, I032I000, U32, U0);
    props_for_pair!(i064i000, I064I000, U64, U0);
    props_for_pair!(i096i000, I096I000, U96, U0);
    props_for_pair!(i128i000, I128I000, U128, U0);
    props_for_pair!(i032i016, I032I016, U32, U16);
    props_for_pair!(i064i016, I064I016, U64, U16);
    props_for_pair!(i096i016, I096I016, U96, U16);
    props_for_pair!(i128i016, I128I016, U128, U16);
    props_for_pair!(i064i032, I064I032, U64, U32);
    props_for_pair!(i096i032, I096I032, U96, U32);
    props_for_pair!(i128i032, I128I032, U128, U32);
    props_for_pair!(i096i064, I096I064, U96, U64);
    props_for_pair!(i128i064, I128I064, U128, U64);
    props_for_pair!(i128i096, I128I096, U128, U96);
}
