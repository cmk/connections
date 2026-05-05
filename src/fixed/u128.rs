//! Binary fixed-point ladder over `fixed::FixedU128<Frac>`.
//!
//! Frac level set: `{U0, U16, U32, U64, U96, U127, U128}` → 21 ordered
//! pairs. Mirrors [`super::i128`] with `FixedU128` backing and adds
//! `U127` (Q1.127), the canonical 128-bit normalised-amplitude format.
//!
//! Stable Rust has no native `u256` to widen through, so the u64-style
//! `(x.to_bits() as u128) * RATIO` pattern doesn't compose. Instead we
//! use [`u128::checked_mul`] + saturate, and [`u128::checked_shl`] to
//! detect the `SHIFT == 128` degenerate case (`Q128Q000`, where
//! `RATIO = 2^128` doesn't fit in `u128` at all).

use super::{int_uint, nz_uint_ext, uint_uint};
use ::fixed::FixedU128;
use ::fixed::types::extra::{U0, U16, U32, U64, U96, U127, U128, Unsigned};
use core::num::NonZeroU128;

// ── §1 std-int Conns landing on `u128` ──────────────────────────────

uint_uint!(U008U128, u8, u128);
uint_uint!(U016U128, u16, u128);
uint_uint!(U032U128, u32, u128);
uint_uint!(U064U128, u64, u128);
int_uint!(I008U128, i8, u128);
int_uint!(I016U128, i16, u128);
int_uint!(I032U128, i32, u128);
int_uint!(I064U128, i64, u128);
int_uint!(I128U128, i128, u128);

// ── §2 u128 ↔ NonZeroU128 ────────────────────────────────

nz_uint_ext!(U128N128, u128, NonZeroU128);

// ── §3 cross-crate iso: FixedU128<U0> ↔ u128 ───────────────────────

const fn q000u128_fwd(q: FixedU128<U0>) -> u128 {
    q.to_bits()
}
const fn q000u128_bk(i: u128) -> FixedU128<U0> {
    FixedU128::<U0>::from_bits(i)
}

crate::iso! {
    /// `FixedU128<U0> ↔ u128` — Q128.0 unsigned lossless iso. Degenerate Galois.
    pub Q000U128 : FixedU128<U0> => u128 {
        forward: q000u128_fwd,
        back:    q000u128_bk,
    }
}

// ── §4 Q-format ladder over `FixedU128<Frac>` ───────────────────────

// No `pub type U<frac>` aliases here: the module's frac levels include
// `U127` and `U128`, which are also the typenum `extra::U127` /
// `extra::U128` names imported above. Using a 4-digit padded form
// (`U0127`/`U0128`) would side-step the collision but break uniformity
// with the rest of the unsigned ladder; downstream callers can spell
// `FixedU128<typenum::U127>` directly when they need a level alias.

macro_rules! fix_fix_u128 {
    ($const_name:ident, $FineFrac:ty, $CoarseFrac:ty) => {
#[rustfmt::skip]
        #[doc = concat!(
            "`FixedU128<",
            stringify!($FineFrac),
            "> → FixedU128<",
            stringify!($CoarseFrac),
            ">` frac-level convert (u128-backed)."
        )]
        pub struct $const_name;

        impl $const_name {
            const SHIFT: u32 = <$FineFrac as Unsigned>::U32 - <$CoarseFrac as Unsigned>::U32;
            // For SHIFT < 128, Self::RATIO = 2^SHIFT fits in u128. For
            // SHIFT == 128 the shift is degenerate — `1_u128.checked_shl(128)`
            // returns None, and we route through the `None` arms below
            // for the Q128Q000 endpoint.
            const RATIO: Option<u128> = 1_u128.checked_shl(Self::SHIFT);
            const FINE_MAX: u128 = u128::MAX;

            const fn _ceil(x: FixedU128<$FineFrac>) -> FixedU128<$CoarseFrac> {
                let bits = x.to_bits();
                match Self::RATIO {
                    Some(r) => {
                        let q = bits / r;
                        // `q + 1` cannot overflow u128: `r ≥ 2` (the
                        // `Some` arm requires SHIFT ∈ [1, 127], so
                        // Self::RATIO ∈ [2, 2^127]), and `bits ≤ u128::MAX`,
                        // so `q ≤ ⌊u128::MAX / 2⌋ = 2^127 − 1`. Hence
                        // `q + 1 ≤ 2^127 < u128::MAX`.
                        let res = if bits % r != 0 { q + 1 } else { q };
                        FixedU128::from_bits(res)
                    }
                    None => {
                        // SHIFT == 128 (Q128Q000). For any bits ∈ u128,
                        // bits < 2^128, so bits / 2^128 < 1.
                        // ceil: bits > 0 → 1; bits == 0 → 0.
                        if bits > 0 {
                            FixedU128::from_bits(1)
                        } else {
                            FixedU128::from_bits(0)
                        }
                    }
                }
            }

            const fn _inner(x: FixedU128<$CoarseFrac>) -> FixedU128<$FineFrac> {
                let bits = x.to_bits();
                let saturated = match Self::RATIO {
                    Some(r) => match bits.checked_mul(r) {
                        Some(v) => v,
                        None => Self::FINE_MAX,
                    },
                    None => {
                        // SHIFT == 128: bits × 2^128 only fits when bits = 0.
                        if bits == 0 { 0 } else { Self::FINE_MAX }
                    }
                };
                FixedU128::from_bits(saturated)
            }
        }

        // (Plan 32) ConnL only — `_inner` non-injective at saturation.
        impl $crate::conn::ConnL<FixedU128<$FineFrac>, FixedU128<$CoarseFrac>> for $const_name {
            #[inline]
            fn conn_l(
                &self,
            ) -> $crate::conn::Conn<FixedU128<$FineFrac>, FixedU128<$CoarseFrac>, $crate::conn::L>
            {
                $crate::conn::Conn::new_l($const_name::_ceil, $const_name::_inner)
            }
        }
    };
}

// 21 ordered pairs from {U0, U16, U32, U64, U96, U127, U128}.
fix_fix_u128!(Q016Q000, U16, U0);
fix_fix_u128!(Q032Q000, U32, U0);
fix_fix_u128!(Q064Q000, U64, U0);
fix_fix_u128!(Q096Q000, U96, U0);
fix_fix_u128!(Q127Q000, U127, U0);
fix_fix_u128!(Q128Q000, U128, U0);
fix_fix_u128!(Q032Q016, U32, U16);
fix_fix_u128!(Q064Q016, U64, U16);
fix_fix_u128!(Q096Q016, U96, U16);
fix_fix_u128!(Q127Q016, U127, U16);
fix_fix_u128!(Q128Q016, U128, U16);
fix_fix_u128!(Q064Q032, U64, U32);
fix_fix_u128!(Q096Q032, U96, U32);
fix_fix_u128!(Q127Q032, U127, U32);
fix_fix_u128!(Q128Q032, U128, U32);
fix_fix_u128!(Q096Q064, U96, U64);
fix_fix_u128!(Q127Q064, U127, U64);
fix_fix_u128!(Q128Q064, U128, U64);
fix_fix_u128!(Q127Q096, U127, U96);
fix_fix_u128!(Q128Q096, U128, U96);
fix_fix_u128!(Q128Q127, U128, U127);

// ────────────────────────────────────────────────────────────────────
// Tests
// ────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    #[allow(unused_imports)]
    use crate::conn::{ConnL, ConnR};

    // ── §1 std-int spot checks (merged from former int/u128.rs) ────

    #[test]
    fn u064u128_inner_saturates_at_source_max() {
        assert_eq!(U064U128.upper(u128::MAX), u64::MAX);
    }

    #[test]
    fn i128u128_at_extremes() {
        assert_eq!(I128U128.ceil(i128::MIN), 0);
        assert_eq!(I128U128.ceil(i128::MAX), i128::MAX as u128);
        assert_eq!(I128U128.upper(u128::MAX), i128::MAX);
    }

    // ── §4 Q-format spot checks ────────────────────────────────────

    /// Regression for the SHIFT=128 endpoint: RATIO doesn't fit u128;
    /// only Coarse(0) round-trips.
    #[test]
    fn degenerate_max_shift() {
        // inner: only 0 stays in range; everything else saturates to MAX.
        assert_eq!(
            Q128Q000.upper(FixedU128::<U0>::from_bits(0)),
            FixedU128::<U128>::from_bits(0),
        );
        assert_eq!(
            Q128Q000.upper(FixedU128::<U0>::from_bits(1)),
            FixedU128::<U128>::from_bits(u128::MAX),
        );
        assert_eq!(
            Q128Q000.upper(FixedU128::<U0>::from_bits(u128::MAX)),
            FixedU128::<U128>::from_bits(u128::MAX),
        );
        // ceil: positive inputs round up to 1; zero → 0.
        assert_eq!(
            Q128Q000.ceil(FixedU128::<U128>::from_bits(0)),
            FixedU128::<U0>::from_bits(0),
        );
        assert_eq!(
            Q128Q000.ceil(FixedU128::<U128>::from_bits(1)),
            FixedU128::<U0>::from_bits(1),
        );
        // (Plan 32: floor truth-table rows removed.)
    }

    /// Q1.127 (the canonical 128-bit normalised amplitude) → Q0.128:
    /// the value 1<<126 in Q1.127 (= 0.5) embeds via Q128Q127.inner
    /// to 1<<127 in Q0.128 (= 0.5).
    #[test]
    fn spot_q127_to_q128() {
        let q127 = FixedU128::<U127>::from_bits(1 << 126);
        let q128 = Q128Q127.upper(q127);
        assert_eq!(q128, FixedU128::<U128>::from_bits(1 << 127));
        assert_eq!(Q128Q127.ceil(q128), q127);
    }

    #[test]
    fn spot_boundary_fixups() {
        // (Plan 32: floor removed.)
        let fmin = FixedU128::<U128>::from_bits(0);
        assert_eq!(Q128Q064.ceil(fmin), FixedU128::<U64>::from_bits(0));
    }

    /// Inner-saturation regression: for non-degenerate pairs where the
    /// SHIFT is large enough that a non-zero coarse bit overflows the
    /// fine u128 range, inner saturates rather than wrapping.
    #[test]
    fn inner_saturates_on_overflow() {
        // Q128Q016: SHIFT=112. Coarse = u128::MAX → product = u128::MAX
        // × 2^112 ≫ u128::MAX, so checked_mul returns None and we
        // saturate to FINE_MAX.
        let big_coarse = FixedU128::<U16>::from_bits(u128::MAX);
        assert_eq!(
            Q128Q016.upper(big_coarse),
            FixedU128::<U128>::from_bits(u128::MAX),
        );
    }

    /// `ceil`'s `q + 1` step in the `Some(r)` branch must not overflow
    /// u128 at the worst-case input `bits = u128::MAX`. The proptest
    /// battery runs only 64 cases per pair (u128 generators are
    /// expensive), so this regression pins the worst case explicitly:
    /// SHIFT=1 (RATIO=2) gives `q = ⌊(2^128-1)/2⌋ = 2^127 - 1`, and
    /// with `r = 1` the branch computes `q + 1 = 2^127`, which fits.
    #[test]
    fn ceil_at_fine_max_no_overflow() {
        // Q128Q127: SHIFT=1, the smallest RATIO and therefore the
        // largest `q` for any given `bits`.
        let fmax = FixedU128::<U128>::from_bits(u128::MAX);
        // bits = 2^128 - 1, RATIO = 2. q = 2^127 - 1, r = 1, q+1 = 2^127.
        assert_eq!(
            Q128Q127.ceil(fmax),
            FixedU128::<U127>::from_bits(1_u128 << 127),
        );
    }

    // The Galois proptest battery (189 generated tests across 21
    // ordered pairs, capped to 64 cases each — u128 generators are
    // expensive) lives in `tests/fixed_u128_galois.rs`.
    // Hosting it as an integration test keeps the lib-test rustc
    // invocation under CI's container memory budget.
}
