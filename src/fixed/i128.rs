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
//! the [`conn_k!`](crate::conn_k) macro.
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

const fn q000i128_fwd(q: FixedI128<U0>) -> i128 {
    q.to_bits()
}
const fn q000i128_bk(i: i128) -> FixedI128<U0> {
    FixedI128::<U0>::from_bits(i)
}

crate::iso! {
    /// `FixedI128<U0> ↔ i128` — Q128.0 lossless iso. Degenerate Galois.
    pub Q000I128 : FixedI128<U0> => i128 {
        forward: q000i128_fwd,
        back:    q000i128_bk,
    }
}

// ── §4 Q-format ladder over `FixedI128<Frac>` ──────────────────────

/// `I<frac> = FixedI128<U<frac>>` — i128-backed binary fixed-point.
pub type I0 = FixedI128<U0>;
pub type I16 = FixedI128<U16>;
pub type I32 = FixedI128<U32>;
pub type I64 = FixedI128<U64>;
pub type I96 = FixedI128<U96>;
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
        }

        // (Plan 32) ConnL only — `_inner` non-injective at saturation.
        impl $crate::conn::ConnL<FixedI128<$FineFrac>, FixedI128<$CoarseFrac>> for $const_name {
            #[inline]
            fn conn_l(
                &self,
            ) -> $crate::conn::Conn<FixedI128<$FineFrac>, FixedI128<$CoarseFrac>, $crate::conn::L>
            {
                $crate::conn::Conn::new_l($const_name::_ceil, $const_name::_inner)
            }
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
    use crate::conn::{ConnL, ConnR};
    use crate::extended::Extended;
    use proptest::prelude::*;

    // ── §1 std-int spot checks (merged from former int/i128.rs) ────

    // (Plan 32) `floor` arms removed; `ext_int!` is now ConnL.
    #[test]
    fn i064i128_extends_to_one_above() {
        assert_eq!(I064I128.ceil(Extended::PosInf), (i64::MAX as i128) + 1);
        assert_eq!(I064I128.ceil(Extended::NegInf), i128::MIN);
    }

    #[test]
    fn u064i128_extends_to_one_above() {
        assert_eq!(U064I128.ceil(Extended::PosInf), (u64::MAX as i128) + 1);
        assert_eq!(U064I128.ceil(Extended::NegInf), i128::MIN);
    }

    #[test]
    fn u128i128_neg_and_high() {
        assert_eq!(U128I128.lower(-1), 0_u128);
        assert_eq!(U128I128.lower(i128::MIN), 0_u128);
        assert_eq!(U128I128.floor(u128::MAX), i128::MAX);
        assert_eq!(U128I128.floor(U128I128.lower(50)), 50);
        assert_eq!(U128I128.floor(U128I128.lower(i128::MAX)), i128::MAX);
    }

    // ── §4 Q-format spot checks ────────────────────────────────────

    /// Regression for the SHIFT=128 endpoint: RATIO doesn't fit i128;
    /// only Coarse(0) round-trips.
    #[test]
    fn degenerate_max_shift() {
        // inner: only 0 stays in range; everything else saturates.
        assert_eq!(
            Q128Q000.upper(FixedI128::<U0>::from_bits(0)),
            FixedI128::<U128>::from_bits(0),
        );
        assert_eq!(
            Q128Q000.upper(FixedI128::<U0>::from_bits(1)),
            FixedI128::<U128>::from_bits(i128::MAX),
        );
        assert_eq!(
            Q128Q000.upper(FixedI128::<U0>::from_bits(-1)),
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
        // (Plan 32) `floor` truth-table rows removed: ConnL only.
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
        let fine_via_inner = Q128Q064.upper(coarse_one);
        assert_eq!(fine_via_inner, FixedI128::<U128>::from_bits(1_i128 << 64));
    }

    #[test]
    fn spot_boundary_fixups() {
        // Fine::MIN ceil fixup. (Plan 32: floor removed.)
        let fmin = FixedI128::<U128>::from_bits(i128::MIN);
        assert_eq!(Q128Q064.ceil(fmin), FixedI128::<U64>::from_bits(i128::MIN));
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
            Q128Q016.upper(big_coarse),
            FixedI128::<U128>::from_bits(i128::MAX),
        );
        let neg_coarse = FixedI128::<U16>::from_bits(i128::MIN);
        assert_eq!(
            Q128Q016.upper(neg_coarse),
            FixedI128::<U128>::from_bits(i128::MIN),
        );
    }

    // 15 conns × 9 properties = 135 generated proptests (64 cases each)
    // — i128 generators are expensive, so cap via `cases: 64`.
    macro_rules! props_for_pair {
        ($mod_name:ident, $conn:ident, $FineFrac:ty, $CoarseFrac:ty) => {
            $crate::law_battery! {
                mod $mod_name,
                conn: $conn,
                fine:   prop_oneof![
                    1 => Just(FixedI128::<$FineFrac>::from_bits(i128::MIN)),
                    1 => Just(FixedI128::<$FineFrac>::from_bits(i128::MAX)),
                    1 => Just(FixedI128::<$FineFrac>::from_bits(0)),
                    8 => any::<i128>().prop_map(FixedI128::<$FineFrac>::from_bits),
                ],
                coarse: prop_oneof![
                    1 => Just(FixedI128::<$CoarseFrac>::from_bits(i128::MIN)),
                    1 => Just(FixedI128::<$CoarseFrac>::from_bits(i128::MAX)),
                    1 => Just(FixedI128::<$CoarseFrac>::from_bits(0)),
                    8 => any::<i128>().prop_map(FixedI128::<$CoarseFrac>::from_bits),
                ],
                subset: l_only,
                cases: 64,
            }
        };
    }

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
