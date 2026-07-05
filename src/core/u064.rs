//! `u64`-source std-int Conns plus the `u64 ↔ NonZeroU64` adjoint and
//! sortable big- / little-endian byte encodings.
//!
//! Q-format / cross-crate isos to `FixedU64<F>` live next door in
//! `crate::fixed::u064`.

#[allow(unused_imports)]
use crate::core::LE;
use crate::core::{
    ext_int, nz_uint_ext, nz_uint_narrow, nz_uint_widen, uint_int_sat, uint_uint, uint_uint_narrow,
};
use ::core::num::{NonZeroU8, NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU128};

// ── §1 std-int Conns sourced from `u64` ───────────────────────────

ext_int!(U064I128, u64, i128);
uint_int_sat!(U064I008, u64, i8);
uint_int_sat!(U064I016, u64, i16);
uint_int_sat!(U064I032, u64, i32);
uint_int_sat!(U064I064, u64, i64);

uint_uint_narrow!(U064U008, u64, u8);
uint_uint_narrow!(U064U016, u64, u16);
uint_uint_narrow!(U064U032, u64, u32);
uint_uint!(U064U128, u64, u128);

// ── §3 u64 ↔ NonZeroU64 ───────────────────────────────────────────

nz_uint_ext!(U064N064, u64, NonZeroU64);

// ── NonZero unsigned narrowings ───────────────────────────────────

nz_uint_narrow!(N064N008, NonZeroU64, u64, NonZeroU8, u8);
nz_uint_narrow!(N064N016, NonZeroU64, u64, NonZeroU16, u16);
nz_uint_narrow!(N064N032, NonZeroU64, u64, NonZeroU32, u32);

// ── NonZero unsigned widenings ────────────────────────────────────

nz_uint_widen!(N064N128, NonZeroU64, u64, NonZeroU128, u128);

// ── Sortable big-endian byte encodings ────────────────────────────

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

// ── Sortable little-endian byte encodings ─────────────────────────

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

// ────────────────────────────────────────────────────────────────────
// Tests
// ────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    #[allow(unused_imports)]
    use crate::conn::{ConnL, ConnR};
    #[allow(unused_imports)]
    use crate::core::{
        i008::I008U064, i016::I016U064, i032::I032U064, i064::I064U064, i128::I128U064,
        u008::U008U064, u016::U016U064, u032::U032U064, u128::U128U064,
    };
    use crate::prop::conn as conn_laws;
    use proptest::prelude::*;

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

    // ── NonZero unsigned narrowing (N064N###) spot + property ─────

    fn arb_nz_u8() -> impl Strategy<Value = NonZeroU8> {
        any::<u8>().prop_filter_map("non-zero u8", NonZeroU8::new)
    }
    fn arb_nz_u16() -> impl Strategy<Value = NonZeroU16> {
        any::<u16>().prop_filter_map("non-zero u16", NonZeroU16::new)
    }
    fn arb_nz_u32() -> impl Strategy<Value = NonZeroU32> {
        any::<u32>().prop_filter_map("non-zero u32", NonZeroU32::new)
    }
    fn arb_nz_u64() -> impl Strategy<Value = NonZeroU64> {
        any::<u64>().prop_filter_map("non-zero u64", NonZeroU64::new)
    }

    proptest! {
        #[test]
        fn n064n008_galois_l(a in arb_nz_u64(), b in arb_nz_u8()) {
            prop_assert!(conn_laws::galois_l(&N064N008, a, b));
        }
        #[test]
        fn n064n016_galois_l(a in arb_nz_u64(), b in arb_nz_u16()) {
            prop_assert!(conn_laws::galois_l(&N064N016, a, b));
        }
        #[test]
        fn n064n032_galois_l(a in arb_nz_u64(), b in arb_nz_u32()) {
            prop_assert!(conn_laws::galois_l(&N064N032, a, b));
        }
    }

    fn arb_byte8() -> impl Strategy<Value = [u8; 8]> {
        prop_oneof![Just([0; 8]), Just([0xFF; 8]), any::<[u8; 8]>()]
    }

    fn arb_lebyte8() -> impl Strategy<Value = LE<8>> {
        arb_byte8().prop_map(LE)
    }

    proptest! {
        #[test]
        fn u64_be_iso_roundtrip_l(a in prop_oneof![Just(0u64), Just(u64::MAX), any::<u64>()]) {
            prop_assert!(conn_laws::iso_roundtrip_l(&U064BE08.view_l(), a));
        }
        #[test]
        fn u64_be_roundtrip_ceil(b in arb_byte8()) {
            prop_assert!(conn_laws::roundtrip_ceil(&U064BE08.view_l(), b));
        }
        #[test]
        fn u64_be_galois_l(a in any::<u64>(), b in arb_byte8()) {
            prop_assert!(conn_laws::galois_l(&U064BE08.view_l(), a, b));
        }
        #[test]
        fn u64_be_galois_r(a in any::<u64>(), b in arb_byte8()) {
            prop_assert!(conn_laws::galois_r(&U064BE08.view_r(), a, b));
        }
        #[test]
        fn u64_be_floor_le_ceil(a in any::<u64>()) {
            prop_assert!(conn_laws::floor_le_ceil(&U064BE08, a));
        }
        #[test]
        fn u64_be_order_preserving(a in any::<u64>(), b in any::<u64>()) {
            prop_assert_eq!(a.cmp(&b), U064BE08.view_l().ceil(a).cmp(&U064BE08.view_l().ceil(b)));
        }

        #[test]
        fn u064_le_iso_roundtrip_l(a in prop_oneof![Just(0u64), Just(u64::MAX), any::<u64>()]) {
            prop_assert!(conn_laws::iso_roundtrip_l(&U064LE08.view_l(), a));
        }

        #[test]
        fn u064_le_roundtrip_ceil(b in arb_lebyte8()) {
            prop_assert!(conn_laws::roundtrip_ceil(&U064LE08.view_l(), b));
        }

        #[test]
        fn u064_le_galois_l(a in any::<u64>(), b in arb_lebyte8()) {
            prop_assert!(conn_laws::galois_l(&U064LE08.view_l(), a, b));
        }

        #[test]
        fn u064_le_galois_r(a in any::<u64>(), b in arb_lebyte8()) {
            prop_assert!(conn_laws::galois_r(&U064LE08.view_r(), a, b));
        }

        #[test]
        fn u064_le_floor_le_ceil(a in any::<u64>()) {
            prop_assert!(conn_laws::floor_le_ceil(&U064LE08, a));
        }

        #[test]
        fn u064_le_order_preserving(a in any::<u64>(), b in any::<u64>()) {
            prop_assert_eq!(a.cmp(&b), U064LE08.view_l().ceil(a).cmp(&U064LE08.view_l().ceil(b)));
        }
    }
}
