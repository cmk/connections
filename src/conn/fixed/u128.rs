//! Binary fixed-point ladder over `fixed::FixedU128<Frac>`.
//!
//! Frac level set: `{U0, U16, U32, U64, U96, U127, U128}` → 21 ordered
//! pairs. Mirrors [`super::i128`] with `FixedU128` backing and adds
//! `U127` (Q1.127), the canonical 128-bit normalised-amplitude format.
//!
//! Stable Rust has no native `u256` to widen through, so the u64-style
//! `(x.to_bits() as u128) * RATIO` pattern doesn't compose. Instead we
//! use [`u128::checked_mul`] + saturate, and [`u128::checked_shl`] to
//! detect the `SHIFT == 128` degenerate case (`U128U000`, where
//! `RATIO = 2^128` doesn't fit in `u128` at all).

use crate::conn::Conn;
use ::fixed::FixedU128;
use ::fixed::types::extra::{U0, U16, U32, U64, U96, U127, U128, Unsigned};

// No `pub type U<frac>` aliases here: the module's frac levels include
// `U127` and `U128`, which are also the typenum `extra::U127` /
// `extra::U128` names imported above. Using a 4-digit padded form
// (`U0127`/`U0128`) would side-step the collision but break uniformity
// with the rest of the unsigned ladder; downstream callers can spell
// `FixedU128<typenum::U127>` directly when they need a level alias.

macro_rules! fix_fix_u128 {
    ($const_name:ident, $FineFrac:ty, $CoarseFrac:ty) => {
        pub const $const_name: Conn<FixedU128<$FineFrac>, FixedU128<$CoarseFrac>> = {
            const SHIFT: u32 = <$FineFrac as Unsigned>::U32 - <$CoarseFrac as Unsigned>::U32;
            // For SHIFT < 128, RATIO = 2^SHIFT fits in u128. For
            // SHIFT == 128 the shift is degenerate — `1_u128.checked_shl(128)`
            // returns None, and we route through the `None` arms below
            // for the U128U000 endpoint.
            const RATIO: Option<u128> = 1_u128.checked_shl(SHIFT);
            const FINE_MAX: u128 = u128::MAX;

            fn ceil(x: FixedU128<$FineFrac>) -> FixedU128<$CoarseFrac> {
                let bits = x.to_bits();
                match RATIO {
                    Some(r) => {
                        let q = bits / r;
                        let res = if bits % r != 0 { q + 1 } else { q };
                        FixedU128::from_bits(res)
                    }
                    None => {
                        // SHIFT == 128 (U128U000). For any bits ∈ u128,
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

            fn inner(x: FixedU128<$CoarseFrac>) -> FixedU128<$FineFrac> {
                let bits = x.to_bits();
                let saturated = match RATIO {
                    Some(r) => match bits.checked_mul(r) {
                        Some(v) => v,
                        None => FINE_MAX,
                    },
                    None => {
                        // SHIFT == 128: bits × 2^128 only fits when bits = 0.
                        if bits == 0 { 0 } else { FINE_MAX }
                    }
                };
                FixedU128::from_bits(saturated)
            }

            fn floor(x: FixedU128<$FineFrac>) -> FixedU128<$CoarseFrac> {
                if x.to_bits() == FINE_MAX {
                    return FixedU128::<$CoarseFrac>::from_bits(u128::MAX);
                }
                let bits = x.to_bits();
                match RATIO {
                    Some(r) => FixedU128::from_bits(bits / r),
                    None => {
                        // SHIFT == 128. floor(bits / 2^128) = 0 for all
                        // bits ∈ u128 (FINE_MAX already short-circuited).
                        FixedU128::from_bits(0)
                    }
                }
            }

            Conn::new(ceil, inner, floor)
        };
    };
}

// 21 ordered pairs from {U0, U16, U32, U64, U96, U127, U128}.
fix_fix_u128!(U016U000, U16, U0);
fix_fix_u128!(U032U000, U32, U0);
fix_fix_u128!(U064U000, U64, U0);
fix_fix_u128!(U096U000, U96, U0);
fix_fix_u128!(U127U000, U127, U0);
fix_fix_u128!(U128U000, U128, U0);
fix_fix_u128!(U032U016, U32, U16);
fix_fix_u128!(U064U016, U64, U16);
fix_fix_u128!(U096U016, U96, U16);
fix_fix_u128!(U127U016, U127, U16);
fix_fix_u128!(U128U016, U128, U16);
fix_fix_u128!(U064U032, U64, U32);
fix_fix_u128!(U096U032, U96, U32);
fix_fix_u128!(U127U032, U127, U32);
fix_fix_u128!(U128U032, U128, U32);
fix_fix_u128!(U096U064, U96, U64);
fix_fix_u128!(U127U064, U127, U64);
fix_fix_u128!(U128U064, U128, U64);
fix_fix_u128!(U127U096, U127, U96);
fix_fix_u128!(U128U096, U128, U96);
fix_fix_u128!(U128U127, U128, U127);

// ────────────────────────────────────────────────────────────────────
// Tests
// ────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    /// Regression for the SHIFT=128 endpoint: RATIO doesn't fit u128;
    /// only Coarse(0) round-trips.
    #[test]
    fn degenerate_max_shift() {
        // inner: only 0 stays in range; everything else saturates to MAX.
        assert_eq!(
            U128U000.inner(FixedU128::<U0>::from_bits(0)),
            FixedU128::<U128>::from_bits(0),
        );
        assert_eq!(
            U128U000.inner(FixedU128::<U0>::from_bits(1)),
            FixedU128::<U128>::from_bits(u128::MAX),
        );
        assert_eq!(
            U128U000.inner(FixedU128::<U0>::from_bits(u128::MAX)),
            FixedU128::<U128>::from_bits(u128::MAX),
        );
        // ceil: positive inputs round up to 1; zero → 0.
        assert_eq!(
            U128U000.ceil(FixedU128::<U128>::from_bits(0)),
            FixedU128::<U0>::from_bits(0),
        );
        assert_eq!(
            U128U000.ceil(FixedU128::<U128>::from_bits(1)),
            FixedU128::<U0>::from_bits(1),
        );
        // floor: every non-MAX bit pattern → 0; MAX takes the boundary fixup.
        assert_eq!(
            U128U000.floor(FixedU128::<U128>::from_bits(0)),
            FixedU128::<U0>::from_bits(0),
        );
        assert_eq!(
            U128U000.floor(FixedU128::<U128>::from_bits(1)),
            FixedU128::<U0>::from_bits(0),
        );
        assert_eq!(
            U128U000.floor(FixedU128::<U128>::from_bits(u128::MAX)),
            FixedU128::<U0>::from_bits(u128::MAX),
        );
    }

    /// Q1.127 (the canonical 128-bit normalised amplitude) → Q0.128:
    /// the value 1<<126 in Q1.127 (= 0.5) embeds via U128U127.inner
    /// to 1<<127 in Q0.128 (= 0.5).
    #[test]
    fn spot_q127_to_q128() {
        let q127 = FixedU128::<U127>::from_bits(1 << 126);
        let q128 = U128U127.inner(q127);
        assert_eq!(q128, FixedU128::<U128>::from_bits(1 << 127));
        assert_eq!(U128U127.ceil(q128), q127);
        assert_eq!(U128U127.floor(q128), q127);
    }

    #[test]
    fn spot_boundary_fixups() {
        let fmax = FixedU128::<U128>::from_bits(u128::MAX);
        assert_eq!(U128U064.floor(fmax), FixedU128::<U64>::from_bits(u128::MAX),);
        let fmin = FixedU128::<U128>::from_bits(0);
        assert_eq!(U128U064.ceil(fmin), FixedU128::<U64>::from_bits(0));
    }

    /// Inner-saturation regression: for non-degenerate pairs where the
    /// SHIFT is large enough that a non-zero coarse bit overflows the
    /// fine u128 range, inner saturates rather than wrapping.
    #[test]
    fn inner_saturates_on_overflow() {
        // U128U016: SHIFT=112. Coarse = u128::MAX → product = u128::MAX
        // × 2^112 ≫ u128::MAX, so checked_mul returns None and we
        // saturate to FINE_MAX.
        let big_coarse = FixedU128::<U16>::from_bits(u128::MAX);
        assert_eq!(
            U128U016.inner(big_coarse),
            FixedU128::<U128>::from_bits(u128::MAX),
        );
    }

    // The Galois proptest battery (189 generated tests across 21
    // ordered pairs, capped to 64 cases each — u128 generators are
    // expensive) lives in `tests/conn_fixed_u128_galois.rs`.
    // Hosting it as an integration test keeps the lib-test rustc
    // invocation under CI's container memory budget.
}
