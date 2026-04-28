//! Binary fixed-point ladder over `fixed::FixedU64<Frac>`.
//!
//! Frac level set: `{U0, U8, U16, U32, U48, U63, U64}` → 21 ordered
//! pairs. Mirrors [`super::i64`] with `FixedU64` backing and adds
//! `U63` (Q1.63), the canonical 64-bit normalised-amplitude format.

use crate::conn::Conn;
use ::fixed::FixedU64;
use ::fixed::types::extra::{U0, U8, U16, U32, U48, U63, U64, Unsigned};

/// `U<frac> = FixedU64<U<frac>>` — u64-backed binary fixed-point.
pub type U000 = FixedU64<U0>;
pub type U008 = FixedU64<U8>;
pub type U016 = FixedU64<U16>;
pub type U032 = FixedU64<U32>;
pub type U048 = FixedU64<U48>;
pub type U063 = FixedU64<U63>;
pub type U064 = FixedU64<U64>;

macro_rules! fix_fix_u64 {
    ($const_name:ident, $FineFrac:ty, $CoarseFrac:ty) => {
        pub const $const_name: Conn<FixedU64<$FineFrac>, FixedU64<$CoarseFrac>> = {
            const SHIFT: u32 = <$FineFrac as Unsigned>::U32 - <$CoarseFrac as Unsigned>::U32;
            // u128 covers SHIFT ∈ [1, 64]: 1 << 64 fits, and
            // u64::MAX × (1 << 64) ≈ 2^128 − 2^64 < u128::MAX.
            const RATIO: u128 = 1_u128 << SHIFT;
            const FINE_MAX: u64 = u64::MAX;

            fn ceil(x: FixedU64<$FineFrac>) -> FixedU64<$CoarseFrac> {
                let bits = x.to_bits() as u128;
                let q = bits / RATIO;
                let r = bits % RATIO;
                // `res ≤ ⌈u64::MAX / 2⌉ = 2^63` since RATIO ≥ 2;
                // the `as u64` cast is lossless.
                let res = if r != 0 { q + 1 } else { q };
                FixedU64::from_bits(res as u64)
            }

            fn inner(x: FixedU64<$CoarseFrac>) -> FixedU64<$FineFrac> {
                let res = (x.to_bits() as u128) * RATIO;
                let saturated = if res > FINE_MAX as u128 {
                    FINE_MAX
                } else {
                    res as u64
                };
                FixedU64::from_bits(saturated)
            }

            fn floor(x: FixedU64<$FineFrac>) -> FixedU64<$CoarseFrac> {
                if x.to_bits() == FINE_MAX {
                    return FixedU64::<$CoarseFrac>::from_bits(u64::MAX);
                }
                let res = (x.to_bits() as u128) / RATIO;
                FixedU64::from_bits(res as u64)
            }

            Conn::new(ceil, inner, floor)
        };
    };
}

// 21 ordered pairs from {U0, U8, U16, U32, U48, U63, U64}.
fix_fix_u64!(U008U000, U8, U0);
fix_fix_u64!(U016U000, U16, U0);
fix_fix_u64!(U032U000, U32, U0);
fix_fix_u64!(U048U000, U48, U0);
fix_fix_u64!(U063U000, U63, U0);
fix_fix_u64!(U064U000, U64, U0);
fix_fix_u64!(U016U008, U16, U8);
fix_fix_u64!(U032U008, U32, U8);
fix_fix_u64!(U048U008, U48, U8);
fix_fix_u64!(U063U008, U63, U8);
fix_fix_u64!(U064U008, U64, U8);
fix_fix_u64!(U032U016, U32, U16);
fix_fix_u64!(U048U016, U48, U16);
fix_fix_u64!(U063U016, U63, U16);
fix_fix_u64!(U064U016, U64, U16);
fix_fix_u64!(U048U032, U48, U32);
fix_fix_u64!(U063U032, U63, U32);
fix_fix_u64!(U064U032, U64, U32);
fix_fix_u64!(U063U048, U63, U48);
fix_fix_u64!(U064U048, U64, U48);
fix_fix_u64!(U064U063, U64, U63);

// ────────────────────────────────────────────────────────────────────
// Tests
// ────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    /// Q1.63 (the canonical 64-bit normalised amplitude) → Q0.64:
    /// the value 1<<62 in Q1.63 (= 0.5) embeds via U064U063.inner
    /// to 1<<63 in Q0.64 (= 0.5).
    #[test]
    fn spot_q63_to_q64() {
        let q63 = FixedU64::<U63>::from_bits(1 << 62);
        let q64 = U064U063.inner(q63);
        assert_eq!(q64, FixedU64::<U64>::from_bits(1 << 63));
        assert_eq!(U064U063.ceil(q64), q63);
        assert_eq!(U064U063.floor(q64), q63);
    }

    #[test]
    fn spot_u032u016_on_grid() {
        // 1.5 in Q32.32 (bits = 1.5 × 2^32 = 6442450944);
        // same in Q48.16 is bits 98304.
        let q3232 = FixedU64::<U32>::from_bits(6_442_450_944);
        assert_eq!(U032U016.floor(q3232), FixedU64::<U16>::from_bits(98304));
        assert_eq!(U032U016.ceil(q3232), FixedU64::<U16>::from_bits(98304));
        assert_eq!(U032U016.inner(FixedU64::<U16>::from_bits(98304)), q3232);
    }

    #[test]
    fn spot_u064u000_degenerate() {
        // SHIFT = 64. Only Coarse(0) round-trips; bits ≥ 1 saturates inner.
        assert_eq!(
            U064U000.inner(FixedU64::<U0>::from_bits(0)),
            FixedU64::<U64>::from_bits(0),
        );
        assert_eq!(
            U064U000.inner(FixedU64::<U0>::from_bits(1)),
            FixedU64::<U64>::from_bits(u64::MAX),
        );
        // ceil: any nonzero Fine bit pattern → 1 (the smallest
        // representable Coarse value above zero); zero → 0.
        assert_eq!(
            U064U000.ceil(FixedU64::<U64>::from_bits(0)),
            FixedU64::<U0>::from_bits(0),
        );
        assert_eq!(
            U064U000.ceil(FixedU64::<U64>::from_bits(1)),
            FixedU64::<U0>::from_bits(1),
        );
        // floor: any Fine bit pattern below FINE_MAX → 0; FINE_MAX
        // takes the boundary fixup and returns Coarse::MAX.
        assert_eq!(
            U064U000.floor(FixedU64::<U64>::from_bits(0)),
            FixedU64::<U0>::from_bits(0),
        );
        assert_eq!(
            U064U000.floor(FixedU64::<U64>::from_bits(1)),
            FixedU64::<U0>::from_bits(0),
        );
        assert_eq!(
            U064U000.floor(FixedU64::<U64>::from_bits(u64::MAX)),
            FixedU64::<U0>::from_bits(u64::MAX),
        );
    }

    #[test]
    fn spot_boundary_fixups() {
        let fmax = FixedU64::<U32>::from_bits(u64::MAX);
        assert_eq!(U032U016.floor(fmax), FixedU64::<U16>::from_bits(u64::MAX));
        let fmin = FixedU64::<U32>::from_bits(0);
        assert_eq!(U032U016.ceil(fmin), FixedU64::<U16>::from_bits(0));
    }

    // The Galois proptest battery (189 generated tests across 21
    // ordered pairs) lives in `tests/conn_fixed_u64_galois.rs` —
    // hosting it as an integration test keeps the lib-test rustc
    // invocation under CI's container memory budget.
}
