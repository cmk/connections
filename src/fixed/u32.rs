//! Binary fixed-point ladder over `fixed::FixedU32<Frac>`.
//!
//! Frac level set: `{U0, U4, U8, U16, U24, U31, U32}` → 21 ordered
//! pairs. Mirrors [`super::i32`] with `FixedU32` backing and adds
//! `U31` (Q1.31), the canonical 32-bit normalised-amplitude format.

use super::{int_uint, int_uint_narrow, nz_uint_ext, uint_uint, uint_uint_narrow};
use crate::conn::Conn;
use crate::extended::Extended;
use core::num::NonZeroU32;
use ::fixed::FixedU32;
use ::fixed::types::extra::{U0, U4, U8, U16, U24, U31, U32, Unsigned};

// ── §1 std-int Conns landing on `u32` ───────────────────────────────

uint_uint!(U008U032, u8, u32);
uint_uint!(U016U032, u16, u32);
int_uint!(I008U032, i8, u32);
int_uint!(I016U032, i16, u32);
int_uint!(I032U032, i32, u32);

uint_uint_narrow!(U064U032, u64, u32);
uint_uint_narrow!(U128U032, u128, u32);

int_uint_narrow!(I064U032, i64, u32);
int_uint_narrow!(I128U032, i128, u32);

// ── §3 NonZeroU32 ↔ Extended<u32> ──────────────────────────────────

nz_uint_ext!(N032U032, u32, NonZeroU32);

// ── §2 Q-format ladder over `FixedU32<Frac>` ────────────────────────

/// `U<frac> = FixedU32<U<frac>>` — u32-backed binary fixed-point.
pub type U000 = FixedU32<U0>;
pub type U004 = FixedU32<U4>;
pub type U008 = FixedU32<U8>;
pub type U016 = FixedU32<U16>;
pub type U024 = FixedU32<U24>;
pub type U031 = FixedU32<U31>;
pub type U032 = FixedU32<U32>;

macro_rules! fix_fix_u32 {
    ($const_name:ident, $FineFrac:ty, $CoarseFrac:ty) => {
#[rustfmt::skip]
        #[doc = concat!(
            "`FixedU32<",
            stringify!($FineFrac),
            "> → FixedU32<",
            stringify!($CoarseFrac),
            ">` frac-level convert (u32-backed)."
        )]
        pub const $const_name: Conn<FixedU32<$FineFrac>, FixedU32<$CoarseFrac>> = {
            const SHIFT: u32 = <$FineFrac as Unsigned>::U32 - <$CoarseFrac as Unsigned>::U32;
            // u64 covers SHIFT ∈ [1, 32]: 1 << 32 fits, and
            // u32::MAX × (1 << 32) ≈ 2^64 − 2^32 < u64::MAX.
            const RATIO: u64 = 1_u64 << SHIFT;
            const FINE_MAX: u32 = u32::MAX;

            fn ceil(x: FixedU32<$FineFrac>) -> FixedU32<$CoarseFrac> {
                let bits = x.to_bits() as u64;
                let q = bits / RATIO;
                let r = bits % RATIO;
                // `res ≤ ⌈u32::MAX / 2⌉ = 2_147_483_648` since
                // RATIO ≥ 2; the `as u32` cast is lossless.
                let res = if r != 0 { q + 1 } else { q };
                FixedU32::from_bits(res as u32)
            }

            fn inner(x: FixedU32<$CoarseFrac>) -> FixedU32<$FineFrac> {
                let res = (x.to_bits() as u64) * RATIO;
                let saturated = if res > FINE_MAX as u64 {
                    FINE_MAX
                } else {
                    res as u32
                };
                FixedU32::from_bits(saturated)
            }

            fn floor(x: FixedU32<$FineFrac>) -> FixedU32<$CoarseFrac> {
                if x.to_bits() == FINE_MAX {
                    return FixedU32::<$CoarseFrac>::from_bits(u32::MAX);
                }
                let res = (x.to_bits() as u64) / RATIO;
                FixedU32::from_bits(res as u32)
            }

            Conn::new(ceil, inner, floor)
        };
    };
}

// 21 ordered pairs from {U0, U4, U8, U16, U24, U31, U32}.
fix_fix_u32!(Q004Q000, U4, U0);
fix_fix_u32!(Q008Q000, U8, U0);
fix_fix_u32!(Q016Q000, U16, U0);
fix_fix_u32!(Q024Q000, U24, U0);
fix_fix_u32!(Q031Q000, U31, U0);
fix_fix_u32!(Q032Q000, U32, U0);
fix_fix_u32!(Q008Q004, U8, U4);
fix_fix_u32!(Q016Q004, U16, U4);
fix_fix_u32!(Q024Q004, U24, U4);
fix_fix_u32!(Q031Q004, U31, U4);
fix_fix_u32!(Q032Q004, U32, U4);
fix_fix_u32!(Q016Q008, U16, U8);
fix_fix_u32!(Q024Q008, U24, U8);
fix_fix_u32!(Q031Q008, U31, U8);
fix_fix_u32!(Q032Q008, U32, U8);
fix_fix_u32!(Q024Q016, U24, U16);
fix_fix_u32!(Q031Q016, U31, U16);
fix_fix_u32!(Q032Q016, U32, U16);
fix_fix_u32!(Q031Q024, U31, U24);
fix_fix_u32!(Q032Q024, U32, U24);
fix_fix_u32!(Q032Q031, U32, U31);

// ────────────────────────────────────────────────────────────────────
// Tests
// ────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    // ── §1 std-int spot checks (merged from former int/u32.rs) ─────

    #[test]
    fn u016u032_inner_saturates_at_source_max() {
        assert_eq!(U016U032.inner(u32::MAX), u16::MAX);
        assert_eq!(U016U032.inner(60_000), 60_000);
    }

    #[test]
    fn i016u032_clips_negatives() {
        assert_eq!(I016U032.ceil(-32_768), 0);
        assert_eq!(I016U032.ceil(32_767), 32_767);
    }

    #[test]
    fn i032u032_inner_saturates() {
        assert_eq!(I032U032.inner(u32::MAX), i32::MAX);
        assert_eq!(I032U032.inner(20_000), 20_000);
    }

    #[test]
    fn u_to_u32_saturate_and_fixup() {
        assert_eq!(U064U032.ceil(u64::MAX), u32::MAX);
        assert_eq!(U128U032.ceil(u128::MAX), u32::MAX);
        assert_eq!(U064U032.inner(u32::MAX), u64::MAX);
        assert_eq!(U128U032.inner(u32::MAX), u128::MAX);
    }

    #[test]
    fn i_to_u32_neg_high_fixup() {
        assert_eq!(I064U032.ceil(-1), 0);
        assert_eq!(I064U032.ceil(i64::MAX), u32::MAX);
        assert_eq!(I128U032.ceil(i128::MIN), 0);
        assert_eq!(I064U032.inner(u32::MAX), i64::MAX);
        assert_eq!(I128U032.inner(u32::MAX), i128::MAX);
    }

    // ── §2 Q-format spot checks ────────────────────────────────────

    /// Q1.31 (the canonical 32-bit normalised amplitude) → Q0.32:
    /// the value 1<<30 in Q1.31 (= 0.5) embeds via Q032Q031.inner
    /// to 1<<31 in Q0.32 (= 0.5).
    #[test]
    fn spot_q31_to_q32() {
        let q31 = FixedU32::<U31>::from_bits(1 << 30);
        let q32 = Q032Q031.inner(q31);
        assert_eq!(q32, FixedU32::<U32>::from_bits(1 << 31));
        assert_eq!(Q032Q031.ceil(q32), q31);
        assert_eq!(Q032Q031.floor(q32), q31);
    }

    #[test]
    fn spot_q016q008_on_grid() {
        // 1.5 in Q16.16 (bits = 1.5 × 2^16 = 98304); same in Q24.8 is bits 384.
        let q1616 = FixedU32::<U16>::from_bits(98304);
        assert_eq!(Q016Q008.floor(q1616), FixedU32::<U8>::from_bits(384));
        assert_eq!(Q016Q008.ceil(q1616), FixedU32::<U8>::from_bits(384));
        assert_eq!(Q016Q008.inner(FixedU32::<U8>::from_bits(384)), q1616);
    }

    #[test]
    fn spot_q032q000_degenerate() {
        // SHIFT = 32. Only Coarse(0) round-trips; bits ≥ 1 saturates inner.
        assert_eq!(
            Q032Q000.inner(FixedU32::<U0>::from_bits(0)),
            FixedU32::<U32>::from_bits(0),
        );
        assert_eq!(
            Q032Q000.inner(FixedU32::<U0>::from_bits(1)),
            FixedU32::<U32>::from_bits(u32::MAX),
        );
    }

    #[test]
    fn spot_boundary_fixups() {
        let fmax = FixedU32::<U16>::from_bits(u32::MAX);
        assert_eq!(Q016Q008.floor(fmax), FixedU32::<U8>::from_bits(u32::MAX));
        let fmin = FixedU32::<U16>::from_bits(0);
        assert_eq!(Q016Q008.ceil(fmin), FixedU32::<U8>::from_bits(0));
    }

    // The Galois proptest battery (189 generated tests across 21
    // ordered pairs) lives in `tests/conn_fixed_u32_galois.rs` —
    // hosting it as an integration test keeps the lib-test rustc
    // invocation under CI's container memory budget.
}
