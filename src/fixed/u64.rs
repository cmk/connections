//! Binary fixed-point ladder over `fixed::FixedU64<Frac>`.
//!
//! Frac level set: `{U0, U8, U16, U32, U48, U63, U64}` → 21 ordered
//! pairs. Mirrors [`super::i64`] with `FixedU64` backing and adds
//! `U63` (Q1.63), the canonical 64-bit normalised-amplitude format.

use super::{int_uint, int_uint_narrow, nz_uint_ext, uint_uint, uint_uint_narrow};
use crate::conn::Conn;
use crate::extended::Extended;
use core::num::NonZeroU64;
use ::fixed::FixedU64;
use ::fixed::types::extra::{U0, U8, U16, U32, U48, U63, U64, Unsigned};

// ── §1 std-int Conns landing on `u64` ───────────────────────────────

uint_uint!(U008U064, u8, u64);
uint_uint!(U016U064, u16, u64);
uint_uint!(U032U064, u32, u64);
int_uint!(I008U064, i8, u64);
int_uint!(I016U064, i16, u64);
int_uint!(I032U064, i32, u64);
int_uint!(I064U064, i64, u64);

uint_uint_narrow!(U128U064, u128, u64);

int_uint_narrow!(I128U064, i128, u64);

// ── §3 NonZeroU64 ↔ Extended<u64> ──────────────────────────────────

nz_uint_ext!(N064U064, u64, NonZeroU64);

// ── §2 Q-format ladder over `FixedU64<Frac>` ────────────────────────

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
#[rustfmt::skip]
        #[doc = concat!(
            "`FixedU64<",
            stringify!($FineFrac),
            "> → FixedU64<",
            stringify!($CoarseFrac),
            ">` frac-level convert (u64-backed)."
        )]
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
fix_fix_u64!(Q008Q000, U8, U0);
fix_fix_u64!(Q016Q000, U16, U0);
fix_fix_u64!(Q032Q000, U32, U0);
fix_fix_u64!(Q048Q000, U48, U0);
fix_fix_u64!(Q063Q000, U63, U0);
fix_fix_u64!(Q064Q000, U64, U0);
fix_fix_u64!(Q016Q008, U16, U8);
fix_fix_u64!(Q032Q008, U32, U8);
fix_fix_u64!(Q048Q008, U48, U8);
fix_fix_u64!(Q063Q008, U63, U8);
fix_fix_u64!(Q064Q008, U64, U8);
fix_fix_u64!(Q032Q016, U32, U16);
fix_fix_u64!(Q048Q016, U48, U16);
fix_fix_u64!(Q063Q016, U63, U16);
fix_fix_u64!(Q064Q016, U64, U16);
fix_fix_u64!(Q048Q032, U48, U32);
fix_fix_u64!(Q063Q032, U63, U32);
fix_fix_u64!(Q064Q032, U64, U32);
fix_fix_u64!(Q063Q048, U63, U48);
fix_fix_u64!(Q064Q048, U64, U48);
fix_fix_u64!(Q064Q063, U64, U63);

// ────────────────────────────────────────────────────────────────────
// Tests
// ────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    // ── §1 std-int spot checks (merged from former int/u64.rs) ─────

    #[test]
    fn u032u064_inner_saturates_at_source_max() {
        assert_eq!(U032U064.inner(u64::MAX), u32::MAX);
    }

    #[test]
    fn i064u064_at_extremes() {
        assert_eq!(I064U064.ceil(i64::MIN), 0);
        assert_eq!(I064U064.ceil(i64::MAX), i64::MAX as u64);
        assert_eq!(I064U064.inner(u64::MAX), i64::MAX);
    }

    #[test]
    fn u128u064_saturate_and_fixup() {
        assert_eq!(U128U064.ceil(u128::MAX), u64::MAX);
        assert_eq!(U128U064.inner(u64::MAX), u128::MAX);
        assert_eq!(U128U064.inner(0), 0_u128);
    }

    #[test]
    fn i128u064_neg_high_fixup() {
        assert_eq!(I128U064.ceil(i128::MIN), 0);
        assert_eq!(I128U064.ceil(i128::MAX), u64::MAX);
        assert_eq!(I128U064.inner(u64::MAX), i128::MAX);
    }

    // ── §2 Q-format spot checks ────────────────────────────────────

    /// Q1.63 (the canonical 64-bit normalised amplitude) → Q0.64:
    /// the value 1<<62 in Q1.63 (= 0.5) embeds via Q064Q063.inner
    /// to 1<<63 in Q0.64 (= 0.5).
    #[test]
    fn spot_q63_to_q64() {
        let q63 = FixedU64::<U63>::from_bits(1 << 62);
        let q64 = Q064Q063.inner(q63);
        assert_eq!(q64, FixedU64::<U64>::from_bits(1 << 63));
        assert_eq!(Q064Q063.ceil(q64), q63);
        assert_eq!(Q064Q063.floor(q64), q63);
    }

    #[test]
    fn spot_q032q016_on_grid() {
        // 1.5 in Q32.32 (bits = 1.5 × 2^32 = 6442450944);
        // same in Q48.16 is bits 98304.
        let q3232 = FixedU64::<U32>::from_bits(6_442_450_944);
        assert_eq!(Q032Q016.floor(q3232), FixedU64::<U16>::from_bits(98304));
        assert_eq!(Q032Q016.ceil(q3232), FixedU64::<U16>::from_bits(98304));
        assert_eq!(Q032Q016.inner(FixedU64::<U16>::from_bits(98304)), q3232);
    }

    #[test]
    fn spot_q064q000_degenerate() {
        // SHIFT = 64. Only Coarse(0) round-trips; bits ≥ 1 saturates inner.
        assert_eq!(
            Q064Q000.inner(FixedU64::<U0>::from_bits(0)),
            FixedU64::<U64>::from_bits(0),
        );
        assert_eq!(
            Q064Q000.inner(FixedU64::<U0>::from_bits(1)),
            FixedU64::<U64>::from_bits(u64::MAX),
        );
        // ceil: any nonzero Fine bit pattern → 1 (the smallest
        // representable Coarse value above zero); zero → 0.
        assert_eq!(
            Q064Q000.ceil(FixedU64::<U64>::from_bits(0)),
            FixedU64::<U0>::from_bits(0),
        );
        assert_eq!(
            Q064Q000.ceil(FixedU64::<U64>::from_bits(1)),
            FixedU64::<U0>::from_bits(1),
        );
        // floor: any Fine bit pattern below FINE_MAX → 0; FINE_MAX
        // takes the boundary fixup and returns Coarse::MAX.
        assert_eq!(
            Q064Q000.floor(FixedU64::<U64>::from_bits(0)),
            FixedU64::<U0>::from_bits(0),
        );
        assert_eq!(
            Q064Q000.floor(FixedU64::<U64>::from_bits(1)),
            FixedU64::<U0>::from_bits(0),
        );
        assert_eq!(
            Q064Q000.floor(FixedU64::<U64>::from_bits(u64::MAX)),
            FixedU64::<U0>::from_bits(u64::MAX),
        );
    }

    #[test]
    fn spot_boundary_fixups() {
        let fmax = FixedU64::<U32>::from_bits(u64::MAX);
        assert_eq!(Q032Q016.floor(fmax), FixedU64::<U16>::from_bits(u64::MAX));
        let fmin = FixedU64::<U32>::from_bits(0);
        assert_eq!(Q032Q016.ceil(fmin), FixedU64::<U16>::from_bits(0));
    }

    // The Galois proptest battery (189 generated tests across 21
    // ordered pairs) lives in `tests/conn_fixed_u64_galois.rs` —
    // hosting it as an integration test keeps the lib-test rustc
    // invocation under CI's container memory budget.
}
