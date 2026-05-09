//! Binary fixed-point ladder over `fixed::FixedU64<Frac>`.
//!
//! Frac level set: `{F0, F8, F16, F32, F48, F63, F64}` → 21 ordered
//! pairs. Mirrors [`super::i064`] with `FixedU64` backing and adds
//! `F63` (Q1.63), the canonical 64-bit normalised-amplitude format.

#[allow(unused_imports)]
use super::{LE, ext_int, nz_uint_ext, uint_int_sat, uint_uint, uint_uint_narrow};
#[cfg(test)]
#[allow(unused_imports)]
use crate::fixed::{
    i008::I008U064, i016::I016U064, i032::I032U064, i064::I064U064, i128::I128U064, u008::U008U064,
    u016::U016U064, u032::U032U064, u128::U128U064,
};
use ::fixed::FixedU64;
use ::fixed::types::extra::{
    U0 as F0, U8 as F8, U16 as F16, U32 as F32, U48 as F48, U63 as F63, U64 as F64, Unsigned,
};
use core::num::NonZeroU64;

// - std-int Conns sourced from `u64` -------------------------------

ext_int!(U064I128, u64, i128);
uint_int_sat!(U064I008, u64, i8);
uint_int_sat!(U064I016, u64, i16);
uint_int_sat!(U064I032, u64, i32);
uint_int_sat!(U064I064, u64, i64);

uint_uint_narrow!(U064U008, u64, u8);
uint_uint_narrow!(U064U016, u64, u16);
uint_uint_narrow!(U064U032, u64, u32);
uint_uint!(U064U128, u64, u128);

// ── §2 u64 ↔ NonZeroU64 ──────────────────────────────────

nz_uint_ext!(U064N064, u64, NonZeroU64);

// ── §3 cross-crate iso: u64 ↔ FixedU64<F0> ─────────────────────────

const fn u064q000_fwd(i: u64) -> FixedU64<F0> {
    FixedU64::<F0>::from_bits(i)
}
const fn u064q000_bk(q: FixedU64<F0>) -> u64 {
    q.to_bits()
}

crate::iso! {
    /// `u64 ↔ FixedU64<F0>` — Q64.0 unsigned lossless iso. Degenerate Galois.
    pub U064Q000 : u64 => FixedU64<F0> {
        forward: u064q000_fwd,
        back:    u064q000_bk,
    }
}

// ── Sortable big-endian byte encodings ─────────────────────

const fn u64_to_be08(x: u64) -> [u8; 8] {
    x.to_be_bytes()
}
const fn be08_to_u64(b: [u8; 8]) -> u64 {
    u64::from_be_bytes(b)
}

crate::iso! {
    /// `u64 ↔ [u8; 8]` — big-endian iso. Byte-lex order matches u64 order.
    pub U064BE08 : u64 => [u8; 8] {
        forward: u64_to_be08,
        back:    be08_to_u64,
    }
}

// ── Sortable little-endian byte encodings ──────────────────

const fn u64_to_le08(x: u64) -> LE<8> {
    LE(x.to_le_bytes())
}
const fn le08_to_u64(b: LE<8>) -> u64 {
    u64::from_le_bytes(b.0)
}

crate::iso! {
    /// `u64 ↔ LE<8>` — little-endian iso with numeric-sort ordering.
    pub U064LE08 : u64 => LE<8> {
        forward: u64_to_le08,
        back:    le08_to_u64,
    }
}

// ── §4 Q-format ladder over `FixedU64<Frac>` ────────────────────────

/// `U### = FixedU64<U<frac>>` — u64-backed binary fixed-point.
pub type U000 = FixedU64<F0>;
pub type U008 = FixedU64<F8>;
pub type U016 = FixedU64<F16>;
pub type U032 = FixedU64<F32>;
pub type U048 = FixedU64<F48>;
pub type U063 = FixedU64<F63>;
pub type U064 = FixedU64<F64>;

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
        pub const $const_name: $crate::conn::Conn<FixedU64<$FineFrac>, FixedU64<$CoarseFrac>> = {
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

            // (Plan 32) ConnL only — `_inner` non-injective at saturation.
            $crate::conn::Conn::new_l(ceil, inner)
        };
    };
}

// 21 ordered pairs from {F0, F8, F16, F32, F48, F63, F64}.
fix_fix_u64!(Q008Q000, F8, F0);
fix_fix_u64!(Q016Q000, F16, F0);
fix_fix_u64!(Q032Q000, F32, F0);
fix_fix_u64!(Q048Q000, F48, F0);
fix_fix_u64!(Q063Q000, F63, F0);
fix_fix_u64!(Q064Q000, F64, F0);
fix_fix_u64!(Q016Q008, F16, F8);
fix_fix_u64!(Q032Q008, F32, F8);
fix_fix_u64!(Q048Q008, F48, F8);
fix_fix_u64!(Q063Q008, F63, F8);
fix_fix_u64!(Q064Q008, F64, F8);
fix_fix_u64!(Q032Q016, F32, F16);
fix_fix_u64!(Q048Q016, F48, F16);
fix_fix_u64!(Q063Q016, F63, F16);
fix_fix_u64!(Q064Q016, F64, F16);
fix_fix_u64!(Q048Q032, F48, F32);
fix_fix_u64!(Q063Q032, F63, F32);
fix_fix_u64!(Q064Q032, F64, F32);
fix_fix_u64!(Q063Q048, F63, F48);
fix_fix_u64!(Q064Q048, F64, F48);
fix_fix_u64!(Q064Q063, F64, F63);

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

    // ── §1 std-int spot checks (merged from former int/u64.rs) ─────

    #[test]
    fn u032u064_inner_saturates_at_source_max() {
        assert_eq!(U032U064.upper(u64::MAX), u32::MAX);
    }

    #[test]
    fn i064u064_at_extremes() {
        assert_eq!(I064U064.ceil(i64::MIN), 0);
        assert_eq!(I064U064.ceil(i64::MAX), i64::MAX as u64);
        assert_eq!(I064U064.upper(u64::MAX), i64::MAX);
    }

    #[test]
    fn u128u064_saturate_and_fixup() {
        assert_eq!(U128U064.ceil(u128::MAX), u64::MAX);
        assert_eq!(U128U064.upper(u64::MAX), u128::MAX);
        assert_eq!(U128U064.upper(0), 0_u128);
    }

    #[test]
    fn i128u064_neg_high_fixup() {
        assert_eq!(I128U064.ceil(i128::MIN), 0);
        assert_eq!(I128U064.ceil(i128::MAX), u64::MAX);
        assert_eq!(I128U064.upper(u64::MAX), i128::MAX);
    }

    // ── §4 Q-format spot checks ────────────────────────────────────

    /// Q1.63 (the canonical 64-bit normalised amplitude) → Q0.64:
    /// the value 1<<62 in Q1.63 (= 0.5) embeds via Q064Q063.upper
    /// to 1<<63 in Q0.64 (= 0.5).
    #[test]
    fn spot_q63_to_q64() {
        let q63 = FixedU64::<F63>::from_bits(1 << 62);
        let q64 = Q064Q063.upper(q63);
        assert_eq!(q64, FixedU64::<F64>::from_bits(1 << 63));
        assert_eq!(Q064Q063.ceil(q64), q63);
    }

    #[test]
    fn spot_q032q016_on_grid() {
        // 1.5 in Q32.32; same in Q48.16 is bits 98304.
        let q3232 = FixedU64::<F32>::from_bits(6_442_450_944);
        assert_eq!(Q032Q016.ceil(q3232), FixedU64::<F16>::from_bits(98304));
        assert_eq!(Q032Q016.upper(FixedU64::<F16>::from_bits(98304)), q3232);
    }

    #[test]
    fn spot_q064q000_degenerate() {
        // SHIFT = 64. Only Coarse(0) round-trips; bits ≥ 1 saturates inner.
        assert_eq!(
            Q064Q000.upper(FixedU64::<F0>::from_bits(0)),
            FixedU64::<F64>::from_bits(0),
        );
        assert_eq!(
            Q064Q000.upper(FixedU64::<F0>::from_bits(1)),
            FixedU64::<F64>::from_bits(u64::MAX),
        );
        // ceil: any nonzero Fine bit pattern → 1 (the smallest
        // representable Coarse value above zero); zero → 0.
        assert_eq!(
            Q064Q000.ceil(FixedU64::<F64>::from_bits(0)),
            FixedU64::<F0>::from_bits(0),
        );
        assert_eq!(
            Q064Q000.ceil(FixedU64::<F64>::from_bits(1)),
            FixedU64::<F0>::from_bits(1),
        );
        // (Plan 32: floor truth-table rows removed.)
    }

    #[test]
    fn spot_boundary_fixups() {
        // (Plan 32: floor removed.)
        let fmin = FixedU64::<F32>::from_bits(0);
        assert_eq!(Q032Q016.ceil(fmin), FixedU64::<F16>::from_bits(0));
    }

    // ── BE byte-encoding tests ─────────────────────────────

    fn arb_byte8() -> impl Strategy<Value = [u8; 8]> {
        prop_oneof![Just([0; 8]), Just([0xFF; 8]), any::<[u8; 8]>()]
    }

    fn arb_lebyte8() -> impl Strategy<Value = LE<8>> {
        arb_byte8().prop_map(LE)
    }

    proptest! {
        #[test]
        fn u64_be_iso_roundtrip_l(a in prop_oneof![Just(0u64), Just(u64::MAX), any::<u64>()]) {
            prop_assert!(conn_laws::iso_roundtrip_l(&U064BE08.conn_l(), a));
        }
        #[test]
        fn u64_be_roundtrip_ceil(b in arb_byte8()) {
            prop_assert!(conn_laws::roundtrip_ceil(&U064BE08.conn_l(), b));
        }
        #[test]
        fn u64_be_galois_l(a in any::<u64>(), b in arb_byte8()) {
            prop_assert!(conn_laws::galois_l(&U064BE08.conn_l(), a, b));
        }
        #[test]
        fn u64_be_galois_r(a in any::<u64>(), b in arb_byte8()) {
            prop_assert!(conn_laws::galois_r(&U064BE08.conn_r(), a, b));
        }
        #[test]
        fn u64_be_floor_le_ceil(a in any::<u64>()) {
            prop_assert!(conn_laws::floor_le_ceil(&U064BE08, a));
        }
        #[test]
        fn u64_be_order_preserving(a in any::<u64>(), b in any::<u64>()) {
            prop_assert_eq!(a.cmp(&b), U064BE08.ceil(a).cmp(&U064BE08.ceil(b)));
        }

        #[test]
        fn u064_le_iso_roundtrip_l(a in prop_oneof![Just(0u64), Just(u64::MAX), any::<u64>()]) {
            prop_assert!(conn_laws::iso_roundtrip_l(&U064LE08.conn_l(), a));
        }

        #[test]
        fn u064_le_roundtrip_ceil(b in arb_lebyte8()) {
            prop_assert!(conn_laws::roundtrip_ceil(&U064LE08.conn_l(), b));
        }

        #[test]
        fn u064_le_galois_l(a in any::<u64>(), b in arb_lebyte8()) {
            prop_assert!(conn_laws::galois_l(&U064LE08.conn_l(), a, b));
        }

        #[test]
        fn u064_le_galois_r(a in any::<u64>(), b in arb_lebyte8()) {
            prop_assert!(conn_laws::galois_r(&U064LE08.conn_r(), a, b));
        }

        #[test]
        fn u064_le_floor_le_ceil(a in any::<u64>()) {
            prop_assert!(conn_laws::floor_le_ceil(&U064LE08, a));
        }

        #[test]
        fn u064_le_order_preserving(a in any::<u64>(), b in any::<u64>()) {
            prop_assert_eq!(a.cmp(&b), U064LE08.ceil(a).cmp(&U064LE08.ceil(b)));
        }
    }

    // The Galois proptest battery (189 generated tests across 21
    // ordered pairs) lives in `tests/fixed_u64_galois.rs` —
    // hosting it as an integration test keeps the lib-test rustc
    // invocation under CI's container memory budget.
}
