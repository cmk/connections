//! Conns landing on `i128` and `FixedI128<Frac>`. Per the right-side-wins
//! module rule, this file hosts every Conn whose destination is `i128`
//! (signed widening from narrower primitives, U→I non-widening from
//! `u128`) or a `FixedI128<U_M>` Q-format wrapper (intra-fixed
//! Fine→Coarse).
//!
//! ## §1 std-int Conns landing on `i128`
//!
//! Signed and unsigned widenings (`I??I128`, `U??I128`) and the
//! same-width unsigned-to-signed clip (`U128I128`) — see [`super`]
//! for the macro family.
//!
//! ## §2 `i128` ↔ `NonZeroI128`
//!
//! Asymmetric-adjoint at zero: `floor(0) = NonZero(-1)`,
//! `ceil(0) = NonZero(+1)`. Both Galois laws hold.
//!
//! ## §3 Cross-crate iso `FixedI128<U0>` ↔ `i128`
//!
//! Q128.0 lossless bridge between the Q-format and std-int views of
//! the same 128-bit signed integer storage; `Q000I128` uses
//! [`Conn::new_iso`](crate::conn::Conn::new_iso).
//!
//! ## §4 Q-format ladder over `FixedI128<Frac>`
//!
//! Frac level set: `{U0, U16, U32, U64, U96, U128}` → 15 ordered pairs
//! `(Fine, Coarse)` with `Fine > Coarse`. See [`super::i64`] for the
//! design template; this module differs in one substantive way:
//!
//! Stable Rust has no native `i256` to widen through, so the i64-style
//! `(x.to_bits() as i128) * RATIO` pattern doesn't compose. Instead we
//! use [`i128::checked_mul`] + saturate, and [`i128::checked_shl`] to
//! detect the `SHIFT == 128` degenerate case (`Q128Q000`, where
//! `RATIO = 2^128` doesn't fit in `i128` at all).
//!
//! Bit-identical outputs to a hypothetical i256-widening implementation
//! at every input: both saturate at `i128::MIN` / `i128::MAX` whenever
//! the product would overflow; `checked_mul` is the smaller, SMT-cleaner
//! encoding (`Some(x*y) iff fits, else None`). Galois laws hold by the
//! same construction as the smaller modules.

use super::{ext_int, nz_int_ext, uint_int_sat};
use crate::conn::Conn;
use crate::extended::Extended;
use ::fixed::FixedI128;
use ::fixed::types::extra::{U0, U16, U32, U64, U96, U128, Unsigned};
use core::num::NonZeroI128;

// ── §1 std-int Conns landing on `i128` ─────────────────────────────

ext_int!(I008I128, i8, i128);
ext_int!(I016I128, i16, i128);
ext_int!(I032I128, i32, i128);
ext_int!(I064I128, i64, i128);
ext_int!(U008I128, u8, i128);
ext_int!(U016I128, u16, i128);
ext_int!(U032I128, u32, i128);
ext_int!(U064I128, u64, i128);
uint_int_sat!(U128I128, u128, i128);

// ── §2 i128 ↔ NonZeroI128 ────────────────────────────────

nz_int_ext!(I128N128, i128, NonZeroI128);

// ── §3 cross-crate iso: FixedI128<U0> ↔ i128 ───────────────────────

/// `FixedI128<U0> ↔ i128` — Q128.0 lossless iso. Degenerate Galois.
pub struct Q000I128;

impl Q000I128 {
    const fn forward(q: FixedI128<U0>) -> i128 {
        q.to_bits()
    }
    const fn back(i: i128) -> FixedI128<U0> {
        FixedI128::<U0>::from_bits(i)
    }
}

impl crate::conn::ViewL<FixedI128<U0>, i128> for Q000I128 {
    const L: crate::conn::ConnL<FixedI128<U0>, i128> =
        crate::conn::Conn::new_l(Q000I128::forward, Q000I128::back);
}
impl crate::conn::ViewR<FixedI128<U0>, i128> for Q000I128 {
    const R: crate::conn::ConnR<FixedI128<U0>, i128> =
        crate::conn::Conn::new_r(Q000I128::back, Q000I128::forward);
}

// ── §4 Q-format ladder over `FixedI128<Frac>` ──────────────────────

/// `I<frac> = FixedI128<U<frac>>` — i128-backed binary fixed-point.
pub type I000 = FixedI128<U0>;
pub type I016 = FixedI128<U16>;
pub type I032 = FixedI128<U32>;
pub type I064 = FixedI128<U64>;
pub type I096 = FixedI128<U96>;
pub type I128 = FixedI128<U128>;

macro_rules! fix_fix_i128 {
    ($const_name:ident, $FineFrac:ty, $CoarseFrac:ty) => {
#[rustfmt::skip]
        #[doc = concat!(
            "`FixedI128<",
            stringify!($FineFrac),
            "> → FixedI128<",
            stringify!($CoarseFrac),
            ">` frac-level convert (i128-backed)."
        )]
        pub struct $const_name;

        impl $const_name {
            const SHIFT: u32 = <$FineFrac as Unsigned>::U32 - <$CoarseFrac as Unsigned>::U32;
            // For SHIFT < 128, Self::RATIO = 2^SHIFT fits in i128 as a positive
            // value (max 2^126; one below i128::MAX = 2^127 − 1). For
            // SHIFT == 128 the shift is degenerate — `1_i128.checked_shl(128)`
            // returns None, and we route through the `None` arms below
            // for the Q128Q000 endpoint.
            const RATIO: Option<i128> = 1_i128.checked_shl(Self::SHIFT);
            const FINE_MIN: i128 = i128::MIN;
            const FINE_MAX: i128 = i128::MAX;

            const fn _ceil(x: FixedI128<$FineFrac>) -> FixedI128<$CoarseFrac> {
                if x.to_bits() == Self::FINE_MIN {
                    return FixedI128::<$CoarseFrac>::from_bits(i128::MIN);
                }
                let bits = x.to_bits();
                match Self::RATIO {
                    Some(r) => {
                        let q = bits.div_euclid(r);
                        let res = if bits.rem_euclid(r) != 0 { q + 1 } else { q };
                        FixedI128::from_bits(res)
                    }
                    None => {
                        // SHIFT == 128 (Q128Q000). For any bits ∈ i128,
                        // |bits| < 2^127, so |bits / 2^128| < 0.5.
                        // ceil: bits > 0 → 1; bits ≤ 0 → 0 (Self::FINE_MIN
                        // is already short-circuited above).
                        if bits > 0 {
                            FixedI128::from_bits(1)
                        } else {
                            FixedI128::from_bits(0)
                        }
                    }
                }
            }

            const fn _inner(x: FixedI128<$CoarseFrac>) -> FixedI128<$FineFrac> {
                let bits = x.to_bits();
                let saturated = match Self::RATIO {
                    Some(r) => match bits.checked_mul(r) {
                        Some(v) => v,
                        None => {
                            if bits > 0 {
                                Self::FINE_MAX
                            } else {
                                Self::FINE_MIN
                            }
                        }
                    },
                    None => {
                        // SHIFT == 128: bits × 2^128 only fits when bits = 0.
                        if bits == 0 {
                            0
                        } else if bits > 0 {
                            Self::FINE_MAX
                        } else {
                            Self::FINE_MIN
                        }
                    }
                };
                FixedI128::from_bits(saturated)
            }

            const fn _floor(x: FixedI128<$FineFrac>) -> FixedI128<$CoarseFrac> {
                if x.to_bits() == Self::FINE_MAX {
                    return FixedI128::<$CoarseFrac>::from_bits(i128::MAX);
                }
                let bits = x.to_bits();
                match Self::RATIO {
                    Some(r) => FixedI128::from_bits(bits.div_euclid(r)),
                    None => {
                        // SHIFT == 128. floor(bits / 2^128):
                        //   bits ≥ 0 → 0; bits < 0 → -1 (Self::FINE_MAX
                        //   already short-circuited).
                        if bits < 0 {
                            FixedI128::from_bits(-1)
                        } else {
                            FixedI128::from_bits(0)
                        }
                    }
                }
            }
        }

        impl $crate::conn::ViewL<FixedI128<$FineFrac>, FixedI128<$CoarseFrac>> for $const_name {
            const L: $crate::conn::ConnL<FixedI128<$FineFrac>, FixedI128<$CoarseFrac>> =
                $crate::conn::Conn::new_l($const_name::_ceil, $const_name::_inner);
        }

        impl $crate::conn::ViewR<FixedI128<$FineFrac>, FixedI128<$CoarseFrac>> for $const_name {
            const R: $crate::conn::ConnR<FixedI128<$FineFrac>, FixedI128<$CoarseFrac>> =
                $crate::conn::Conn::new_r($const_name::_inner, $const_name::_floor);
        }
    };
}

// 15 ordered pairs from {U0, U16, U32, U64, U96, U128}.
fix_fix_i128!(Q016Q000, U16, U0);
fix_fix_i128!(Q032Q000, U32, U0);
fix_fix_i128!(Q064Q000, U64, U0);
fix_fix_i128!(Q096Q000, U96, U0);
fix_fix_i128!(Q128Q000, U128, U0);
fix_fix_i128!(Q032Q016, U32, U16);
fix_fix_i128!(Q064Q016, U64, U16);
fix_fix_i128!(Q096Q016, U96, U16);
fix_fix_i128!(Q128Q016, U128, U16);
fix_fix_i128!(Q064Q032, U64, U32);
fix_fix_i128!(Q096Q032, U96, U32);
fix_fix_i128!(Q128Q032, U128, U32);
fix_fix_i128!(Q096Q064, U96, U64);
fix_fix_i128!(Q128Q064, U128, U64);
fix_fix_i128!(Q128Q096, U128, U96);

// ────────────────────────────────────────────────────────────────────
// Tests
// ────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    #[allow(unused_imports)]
    use crate::conn::{ViewL, ViewR};
    use crate::prop::conn as conn_laws;
    use proptest::prelude::*;

    // ── §1 std-int spot checks (merged from former int/i128.rs) ────

    #[test]
    fn i064i128_extends_to_one_below_above() {
        assert_eq!(I064I128.floor(Extended::NegInf), (i64::MIN as i128) - 1);
        assert_eq!(I064I128.ceil(Extended::PosInf), (i64::MAX as i128) + 1);
    }

    #[test]
    fn u064i128_extends_to_one_above() {
        assert_eq!(U064I128.ceil(Extended::PosInf), (u64::MAX as i128) + 1);
        assert_eq!(U064I128.floor(Extended::NegInf), -1);
    }

    #[test]
    fn u128i128_neg_and_high() {
        assert_eq!(U128I128.inner(-1), 0_u128);
        assert_eq!(U128I128.inner(i128::MIN), 0_u128);
        assert_eq!(U128I128.floor(u128::MAX), i128::MAX);
        assert_eq!(U128I128.floor(U128I128.inner(50)), 50);
        assert_eq!(U128I128.floor(U128I128.inner(i128::MAX)), i128::MAX);
    }

    // ── §4 Q-format spot checks ────────────────────────────────────

    /// Regression for the SHIFT=128 endpoint: RATIO doesn't fit i128;
    /// only Coarse(0) round-trips.
    #[test]
    fn degenerate_max_shift() {
        // inner: only 0 stays in range; everything else saturates.
        assert_eq!(
            Q128Q000.inner(FixedI128::<U0>::from_bits(0)),
            FixedI128::<U128>::from_bits(0),
        );
        assert_eq!(
            Q128Q000.inner(FixedI128::<U0>::from_bits(1)),
            FixedI128::<U128>::from_bits(i128::MAX),
        );
        assert_eq!(
            Q128Q000.inner(FixedI128::<U0>::from_bits(-1)),
            FixedI128::<U128>::from_bits(i128::MIN),
        );
        // ceil: positive inputs round up to 1; non-positive (and non-MIN)
        // round to 0; MIN takes the i128::MIN boundary fixup.
        assert_eq!(
            Q128Q000.ceil(FixedI128::<U128>::from_bits(0)),
            FixedI128::<U0>::from_bits(0),
        );
        assert_eq!(
            Q128Q000.ceil(FixedI128::<U128>::from_bits(1)),
            FixedI128::<U0>::from_bits(1),
        );
        assert_eq!(
            Q128Q000.ceil(FixedI128::<U128>::from_bits(-1)),
            FixedI128::<U0>::from_bits(0),
        );
        assert_eq!(
            Q128Q000.ceil(FixedI128::<U128>::from_bits(i128::MIN)),
            FixedI128::<U0>::from_bits(i128::MIN),
        );
        // floor: negative inputs round down to -1; non-negative (and
        // non-MAX) round to 0; MAX takes the i128::MAX boundary fixup.
        assert_eq!(
            Q128Q000.floor(FixedI128::<U128>::from_bits(0)),
            FixedI128::<U0>::from_bits(0),
        );
        assert_eq!(
            Q128Q000.floor(FixedI128::<U128>::from_bits(1)),
            FixedI128::<U0>::from_bits(0),
        );
        assert_eq!(
            Q128Q000.floor(FixedI128::<U128>::from_bits(-1)),
            FixedI128::<U0>::from_bits(-1),
        );
        assert_eq!(
            Q128Q000.floor(FixedI128::<U128>::from_bits(i128::MAX)),
            FixedI128::<U0>::from_bits(i128::MAX),
        );
        // Per the truth table, `floor(FINE_MIN)` falls into the
        // degenerate `bits < 0` branch (the FINE_MAX guard does not
        // fire) and returns -1. Pin this explicitly so the regression
        // is exhaustive across all 9 truth-table rows.
        assert_eq!(
            Q128Q000.floor(FixedI128::<U128>::from_bits(i128::MIN)),
            FixedI128::<U0>::from_bits(-1),
        );
    }

    #[test]
    fn spot_q128q064_on_grid() {
        // 1.5 in Q64.64 (bits = 1.5 × 2^64) round-trips through Q64.64
        // (no, the Coarse side has Frac=64, so Q64.64). Pick a value
        // where the Fine bits are an exact multiple of 2^(128-64) = 2^64.
        // bits_fine = 3 × 2^63 represents 1.5 in Q0.128. inner(coarse=3<<63)
        // multiplies through 2^64 — overflow, saturate.
        // Instead use a small value: coarse = 1 represents 2^-64.
        // inner(1) = 1 × 2^64 = 2^64, fits.
        let coarse_one = FixedI128::<U64>::from_bits(1);
        let fine_via_inner = Q128Q064.inner(coarse_one);
        assert_eq!(fine_via_inner, FixedI128::<U128>::from_bits(1_i128 << 64));
    }

    #[test]
    fn spot_boundary_fixups() {
        // Fine::MIN/MAX boundary fixups — exercised on Q128Q064 (SHIFT=64).
        let fmin = FixedI128::<U128>::from_bits(i128::MIN);
        let fmax = FixedI128::<U128>::from_bits(i128::MAX);
        assert_eq!(Q128Q064.ceil(fmin), FixedI128::<U64>::from_bits(i128::MIN));
        assert_eq!(Q128Q064.floor(fmax), FixedI128::<U64>::from_bits(i128::MAX));
    }

    /// Inner-saturation regression: for non-degenerate pairs where the
    /// SHIFT is large enough that a non-zero coarse bit overflows the
    /// fine i128 range, inner saturates rather than wrapping.
    #[test]
    fn inner_saturates_on_overflow() {
        // Q128Q016: SHIFT=112. Coarse = i128::MAX → product = i128::MAX
        // × 2^112 ≫ i128::MAX, so checked_mul returns None and we
        // saturate to FINE_MAX.
        let big_coarse = FixedI128::<U16>::from_bits(i128::MAX);
        assert_eq!(
            Q128Q016.inner(big_coarse),
            FixedI128::<U128>::from_bits(i128::MAX),
        );
        let neg_coarse = FixedI128::<U16>::from_bits(i128::MIN);
        assert_eq!(
            Q128Q016.inner(neg_coarse),
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
                        prop_assert!(conn_laws::galois_l(&$conn::L, fine, coarse));
                    }
                    #[test]
                    fn galois_r(f in any::<i128>(), b in any::<i128>()) {
                        let fine = FixedI128::<$FineFrac>::from_bits(f);
                        let coarse = FixedI128::<$CoarseFrac>::from_bits(b);
                        prop_assert!(conn_laws::galois_r(&$conn::R, fine, coarse));
                    }
                    #[test]
                    fn monotone_l(f1 in any::<i128>(), f2 in any::<i128>()) {
                        let f1 = FixedI128::<$FineFrac>::from_bits(f1);
                        let f2 = FixedI128::<$FineFrac>::from_bits(f2);
                        prop_assert!(conn_laws::monotone_l(&$conn::L, f1, f2));
                    }
                    #[test]
                    fn monotone_r(b1 in any::<i128>(), b2 in any::<i128>()) {
                        let b1 = FixedI128::<$CoarseFrac>::from_bits(b1);
                        let b2 = FixedI128::<$CoarseFrac>::from_bits(b2);
                        prop_assert!(conn_laws::monotone_r(&$conn::R, b1, b2));
                    }
                    #[test]
                    fn closure_l(f in any::<i128>()) {
                        let fine = FixedI128::<$FineFrac>::from_bits(f);
                        prop_assert!(conn_laws::closure_l(&$conn::L, fine));
                    }
                    #[test]
                    fn closure_r(f in any::<i128>()) {
                        let fine = FixedI128::<$FineFrac>::from_bits(f);
                        prop_assert!(conn_laws::closure_r(&$conn::R, fine));
                    }
                    #[test]
                    fn kernel_l(b in any::<i128>()) {
                        let c = FixedI128::<$CoarseFrac>::from_bits(b);
                        prop_assert!(conn_laws::kernel_l(&$conn::L, c));
                    }
                    #[test]
                    fn kernel_r(b in any::<i128>()) {
                        let c = FixedI128::<$CoarseFrac>::from_bits(b);
                        prop_assert!(conn_laws::kernel_r(&$conn::R, c));
                    }
                    #[test]
                    fn idempotent(f in any::<i128>()) {
                        let fine = FixedI128::<$FineFrac>::from_bits(f);
                        prop_assert!(conn_laws::idempotent(&$conn::L, fine));
                    }
                }
            }
        };
    }

    // 15 conns × 9 properties = 135 generated proptests (64 cases each).
    props_for_pair!(q016q000, Q016Q000, U16, U0);
    props_for_pair!(q032q000, Q032Q000, U32, U0);
    props_for_pair!(q064q000, Q064Q000, U64, U0);
    props_for_pair!(q096q000, Q096Q000, U96, U0);
    props_for_pair!(q128q000, Q128Q000, U128, U0);
    props_for_pair!(q032q016, Q032Q016, U32, U16);
    props_for_pair!(q064q016, Q064Q016, U64, U16);
    props_for_pair!(q096q016, Q096Q016, U96, U16);
    props_for_pair!(q128q016, Q128Q016, U128, U16);
    props_for_pair!(q064q032, Q064Q032, U64, U32);
    props_for_pair!(q096q032, Q096Q032, U96, U32);
    props_for_pair!(q128q032, Q128Q032, U128, U32);
    props_for_pair!(q096q064, Q096Q064, U96, U64);
    props_for_pair!(q128q064, Q128Q064, U128, U64);
    props_for_pair!(q128q096, Q128Q096, U128, U96);
}
