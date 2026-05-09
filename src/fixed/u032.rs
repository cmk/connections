//! Binary fixed-point ladder over `fixed::FixedU32<Frac>`.
//!
//! Frac level set: `{F0, F4, F8, F16, F24, F31, F32}` → 21 ordered
//! pairs. Mirrors [`super::i032`] with `FixedU32` backing and adds
//! `F31` (Q1.31), the canonical 32-bit normalised-amplitude format.

#[allow(unused_imports)]
use super::{LE, ext_int, nz_uint_ext, uint_int_sat, uint_uint, uint_uint_narrow};
#[cfg(test)]
#[allow(unused_imports)]
use crate::fixed::{
    i008::I008U032, i016::I016U032, i032::I032U032, i064::I064U032, i128::I128U032, u008::U008U032,
    u016::U016U032, u064::U064U032, u128::U128U032,
};
use ::fixed::FixedU32;
use ::fixed::types::extra::{
    U0 as F0, U4 as F4, U8 as F8, U16 as F16, U24 as F24, U31 as F31, U32 as F32, Unsigned,
};
use core::num::NonZeroU32;

// - std-int Conns sourced from `u32` -------------------------------

ext_int!(U032I064, u32, i64);
ext_int!(U032I128, u32, i128);
uint_int_sat!(U032I008, u32, i8);
uint_int_sat!(U032I016, u32, i16);
uint_int_sat!(U032I032, u32, i32);

uint_uint_narrow!(U032U008, u32, u8);
uint_uint_narrow!(U032U016, u32, u16);
uint_uint!(U032U064, u32, u64);
uint_uint!(U032U128, u32, u128);

// ── §2 u32 ↔ NonZeroU32 ──────────────────────────────────

nz_uint_ext!(U032N032, u32, NonZeroU32);

// ── §3 cross-crate iso: u32 ↔ FixedU32<F0> ─────────────────────────

const fn u032q000_fwd(i: u32) -> FixedU32<F0> {
    FixedU32::<F0>::from_bits(i)
}
const fn u032q000_bk(q: FixedU32<F0>) -> u32 {
    q.to_bits()
}

crate::iso! {
    /// `u32 ↔ FixedU32<F0>` — Q32.0 unsigned lossless iso. Degenerate Galois.
    pub U032Q000 : u32 => FixedU32<F0> {
        forward: u032q000_fwd,
        back:    u032q000_bk,
    }
}

// ── Sortable big-endian byte encodings ─────────────────────

const fn u32_to_be04(x: u32) -> [u8; 4] {
    x.to_be_bytes()
}
const fn be04_to_u32(b: [u8; 4]) -> u32 {
    u32::from_be_bytes(b)
}

crate::iso! {
    /// `u32 ↔ [u8; 4]` — big-endian iso. Byte-lex order matches u32 order.
    pub U032BE04 : u32 => [u8; 4] {
        forward: u32_to_be04,
        back:    be04_to_u32,
    }
}

// ── Sortable little-endian byte encodings ──────────────────

const fn u32_to_le04(x: u32) -> LE<4> {
    LE(x.to_le_bytes())
}
const fn le04_to_u32(b: LE<4>) -> u32 {
    u32::from_le_bytes(b.0)
}

crate::iso! {
    /// `u32 ↔ LE<4>` — little-endian iso with numeric-sort ordering.
    pub U032LE04 : u32 => LE<4> {
        forward: u32_to_le04,
        back:    le04_to_u32,
    }
}

// ── §4 Q-format ladder over `FixedU32<Frac>` ────────────────────────

/// `U### = FixedU32<U<frac>>` — u32-backed binary fixed-point.
pub type U000 = FixedU32<F0>;
pub type U004 = FixedU32<F4>;
pub type U008 = FixedU32<F8>;
pub type U016 = FixedU32<F16>;
pub type U024 = FixedU32<F24>;
pub type U031 = FixedU32<F31>;
pub type U032 = FixedU32<F32>;

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
        pub const $const_name: $crate::conn::Conn<FixedU32<$FineFrac>, FixedU32<$CoarseFrac>> = {
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

            // (Plan 32) ConnL only — `_inner` non-injective at saturation.
            $crate::conn::Conn::new_l(ceil, inner)
        };
    };
}

// 21 ordered pairs from {F0, F4, F8, F16, F24, F31, F32}.
fix_fix_u32!(Q004Q000, F4, F0);
fix_fix_u32!(Q008Q000, F8, F0);
fix_fix_u32!(Q016Q000, F16, F0);
fix_fix_u32!(Q024Q000, F24, F0);
fix_fix_u32!(Q031Q000, F31, F0);
fix_fix_u32!(Q032Q000, F32, F0);
fix_fix_u32!(Q008Q004, F8, F4);
fix_fix_u32!(Q016Q004, F16, F4);
fix_fix_u32!(Q024Q004, F24, F4);
fix_fix_u32!(Q031Q004, F31, F4);
fix_fix_u32!(Q032Q004, F32, F4);
fix_fix_u32!(Q016Q008, F16, F8);
fix_fix_u32!(Q024Q008, F24, F8);
fix_fix_u32!(Q031Q008, F31, F8);
fix_fix_u32!(Q032Q008, F32, F8);
fix_fix_u32!(Q024Q016, F24, F16);
fix_fix_u32!(Q031Q016, F31, F16);
fix_fix_u32!(Q032Q016, F32, F16);
fix_fix_u32!(Q031Q024, F31, F24);
fix_fix_u32!(Q032Q024, F32, F24);
fix_fix_u32!(Q032Q031, F32, F31);

// ────────────────────────────────────────────────────────────────────
// Tests
// ────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    #[allow(unused_imports)]
    use crate::conn::{ConnL, ConnR};
    use crate::prop::conn as conn_laws;
    use proptest::prelude::*;

    // ── §1 std-int spot checks (merged from former int/u32.rs) ─────

    #[test]
    fn u016u032_inner_saturates_at_source_max() {
        assert_eq!(U016U032.upper(u32::MAX), u16::MAX);
        assert_eq!(U016U032.upper(60_000), 60_000);
    }

    #[test]
    fn i016u032_clips_negatives() {
        assert_eq!(I016U032.ceil(-32_768), 0);
        assert_eq!(I016U032.ceil(32_767), 32_767);
    }

    #[test]
    fn i032u032_inner_saturates() {
        assert_eq!(I032U032.upper(u32::MAX), i32::MAX);
        assert_eq!(I032U032.upper(20_000), 20_000);
    }

    #[test]
    fn u_to_u32_saturate_and_fixup() {
        assert_eq!(U064U032.ceil(u64::MAX), u32::MAX);
        assert_eq!(U128U032.ceil(u128::MAX), u32::MAX);
        assert_eq!(U064U032.upper(u32::MAX), u64::MAX);
        assert_eq!(U128U032.upper(u32::MAX), u128::MAX);
    }

    #[test]
    fn i_to_u32_neg_high_fixup() {
        assert_eq!(I064U032.ceil(-1), 0);
        assert_eq!(I064U032.ceil(i64::MAX), u32::MAX);
        assert_eq!(I128U032.ceil(i128::MIN), 0);
        assert_eq!(I064U032.upper(u32::MAX), i64::MAX);
        assert_eq!(I128U032.upper(u32::MAX), i128::MAX);
    }

    // ── §4 Q-format spot checks ────────────────────────────────────

    /// Q1.31 (the canonical 32-bit normalised amplitude) → Q0.32:
    /// the value 1<<30 in Q1.31 (= 0.5) embeds via Q032Q031.upper
    /// to 1<<31 in Q0.32 (= 0.5).
    #[test]
    fn spot_q31_to_q32() {
        let q31 = FixedU32::<F31>::from_bits(1 << 30);
        let q32 = Q032Q031.upper(q31);
        assert_eq!(q32, FixedU32::<F32>::from_bits(1 << 31));
        assert_eq!(Q032Q031.ceil(q32), q31);
    }

    #[test]
    fn spot_q016q008_on_grid() {
        // 1.5 in Q16.16 (bits = 98304); same in Q24.8 is bits 384.
        let q1616 = FixedU32::<F16>::from_bits(98304);
        assert_eq!(Q016Q008.ceil(q1616), FixedU32::<F8>::from_bits(384));
        assert_eq!(Q016Q008.upper(FixedU32::<F8>::from_bits(384)), q1616);
    }

    #[test]
    fn spot_q032q000_degenerate() {
        // SHIFT = 32. Only Coarse(0) round-trips; bits ≥ 1 saturates inner.
        assert_eq!(
            Q032Q000.upper(FixedU32::<F0>::from_bits(0)),
            FixedU32::<F32>::from_bits(0),
        );
        assert_eq!(
            Q032Q000.upper(FixedU32::<F0>::from_bits(1)),
            FixedU32::<F32>::from_bits(u32::MAX),
        );
    }

    #[test]
    fn spot_boundary_fixups() {
        // (Plan 32: floor removed.)
        let fmin = FixedU32::<F16>::from_bits(0);
        assert_eq!(Q016Q008.ceil(fmin), FixedU32::<F8>::from_bits(0));
    }

    // ── BE byte-encoding tests ─────────────────────────────

    fn arb_byte4() -> impl Strategy<Value = [u8; 4]> {
        prop_oneof![Just([0; 4]), Just([0xFF; 4]), any::<[u8; 4]>()]
    }

    fn arb_lebyte4() -> impl Strategy<Value = LE<4>> {
        arb_byte4().prop_map(LE)
    }

    proptest! {
        #[test]
        fn u32_be_iso_roundtrip_l(a in prop_oneof![Just(0u32), Just(u32::MAX), any::<u32>()]) {
            prop_assert!(conn_laws::iso_roundtrip_l(&U032BE04.conn_l(), a));
        }
        #[test]
        fn u32_be_roundtrip_ceil(b in arb_byte4()) {
            prop_assert!(conn_laws::roundtrip_ceil(&U032BE04.conn_l(), b));
        }
        #[test]
        fn u32_be_galois_l(a in any::<u32>(), b in arb_byte4()) {
            prop_assert!(conn_laws::galois_l(&U032BE04.conn_l(), a, b));
        }
        #[test]
        fn u32_be_galois_r(a in any::<u32>(), b in arb_byte4()) {
            prop_assert!(conn_laws::galois_r(&U032BE04.conn_r(), a, b));
        }
        #[test]
        fn u32_be_floor_le_ceil(a in any::<u32>()) {
            prop_assert!(conn_laws::floor_le_ceil(&U032BE04, a));
        }
        #[test]
        fn u32_be_order_preserving(a in any::<u32>(), b in any::<u32>()) {
            prop_assert_eq!(a.cmp(&b), U032BE04.ceil(a).cmp(&U032BE04.ceil(b)));
        }

        #[test]
        fn u032_le_iso_roundtrip_l(a in prop_oneof![Just(0u32), Just(u32::MAX), any::<u32>()]) {
            prop_assert!(conn_laws::iso_roundtrip_l(&U032LE04.conn_l(), a));
        }

        #[test]
        fn u032_le_roundtrip_ceil(b in arb_lebyte4()) {
            prop_assert!(conn_laws::roundtrip_ceil(&U032LE04.conn_l(), b));
        }

        #[test]
        fn u032_le_galois_l(a in any::<u32>(), b in arb_lebyte4()) {
            prop_assert!(conn_laws::galois_l(&U032LE04.conn_l(), a, b));
        }

        #[test]
        fn u032_le_galois_r(a in any::<u32>(), b in arb_lebyte4()) {
            prop_assert!(conn_laws::galois_r(&U032LE04.conn_r(), a, b));
        }

        #[test]
        fn u032_le_floor_le_ceil(a in any::<u32>()) {
            prop_assert!(conn_laws::floor_le_ceil(&U032LE04, a));
        }

        #[test]
        fn u032_le_order_preserving(a in any::<u32>(), b in any::<u32>()) {
            prop_assert_eq!(a.cmp(&b), U032LE04.ceil(a).cmp(&U032LE04.ceil(b)));
        }
    }

    // The Galois proptest battery (189 generated tests across 21
    // ordered pairs) lives in `tests/fixed_u32_galois.rs` —
    // hosting it as an integration test keeps the lib-test rustc
    // invocation under CI's container memory budget.
}
