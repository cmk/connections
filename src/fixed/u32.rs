//! Binary fixed-point ladder over `fixed::FixedU32<Frac>`.
//!
//! Frac level set: `{U0, U4, U8, U16, U24, U31, U32}` → 21 ordered
//! pairs. Mirrors [`super::i32`] with `FixedU32` backing and adds
//! `U31` (Q1.31), the canonical 32-bit normalised-amplitude format.

use crate::conn::Conn;
use ::fixed::FixedU32;
use ::fixed::types::extra::{U0, U4, U8, U16, U24, U31, U32, Unsigned};

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
fix_fix_u32!(U004U000, U4, U0);
fix_fix_u32!(U008U000, U8, U0);
fix_fix_u32!(U016U000, U16, U0);
fix_fix_u32!(U024U000, U24, U0);
fix_fix_u32!(U031U000, U31, U0);
fix_fix_u32!(U032U000, U32, U0);
fix_fix_u32!(U008U004, U8, U4);
fix_fix_u32!(U016U004, U16, U4);
fix_fix_u32!(U024U004, U24, U4);
fix_fix_u32!(U031U004, U31, U4);
fix_fix_u32!(U032U004, U32, U4);
fix_fix_u32!(U016U008, U16, U8);
fix_fix_u32!(U024U008, U24, U8);
fix_fix_u32!(U031U008, U31, U8);
fix_fix_u32!(U032U008, U32, U8);
fix_fix_u32!(U024U016, U24, U16);
fix_fix_u32!(U031U016, U31, U16);
fix_fix_u32!(U032U016, U32, U16);
fix_fix_u32!(U031U024, U31, U24);
fix_fix_u32!(U032U024, U32, U24);
fix_fix_u32!(U032U031, U32, U31);

// ────────────────────────────────────────────────────────────────────
// Tests
// ────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    /// Q1.31 (the canonical 32-bit normalised amplitude) → Q0.32:
    /// the value 1<<30 in Q1.31 (= 0.5) embeds via U032U031.inner
    /// to 1<<31 in Q0.32 (= 0.5).
    #[test]
    fn spot_q31_to_q32() {
        let q31 = FixedU32::<U31>::from_bits(1 << 30);
        let q32 = U032U031.inner(q31);
        assert_eq!(q32, FixedU32::<U32>::from_bits(1 << 31));
        assert_eq!(U032U031.ceil(q32), q31);
        assert_eq!(U032U031.floor(q32), q31);
    }

    #[test]
    fn spot_u016u008_on_grid() {
        // 1.5 in Q16.16 (bits = 1.5 × 2^16 = 98304); same in Q24.8 is bits 384.
        let q1616 = FixedU32::<U16>::from_bits(98304);
        assert_eq!(U016U008.floor(q1616), FixedU32::<U8>::from_bits(384));
        assert_eq!(U016U008.ceil(q1616), FixedU32::<U8>::from_bits(384));
        assert_eq!(U016U008.inner(FixedU32::<U8>::from_bits(384)), q1616);
    }

    #[test]
    fn spot_u032u000_degenerate() {
        // SHIFT = 32. Only Coarse(0) round-trips; bits ≥ 1 saturates inner.
        assert_eq!(
            U032U000.inner(FixedU32::<U0>::from_bits(0)),
            FixedU32::<U32>::from_bits(0),
        );
        assert_eq!(
            U032U000.inner(FixedU32::<U0>::from_bits(1)),
            FixedU32::<U32>::from_bits(u32::MAX),
        );
    }

    #[test]
    fn spot_boundary_fixups() {
        let fmax = FixedU32::<U16>::from_bits(u32::MAX);
        assert_eq!(U016U008.floor(fmax), FixedU32::<U8>::from_bits(u32::MAX));
        let fmin = FixedU32::<U16>::from_bits(0);
        assert_eq!(U016U008.ceil(fmin), FixedU32::<U8>::from_bits(0));
    }

    // The Galois proptest battery (189 generated tests across 21
    // ordered pairs) lives in `tests/conn_fixed_u32_galois.rs` —
    // hosting it as an integration test keeps the lib-test rustc
    // invocation under CI's container memory budget.
}
