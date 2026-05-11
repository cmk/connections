//! `u32`-source std-int Conns plus the `u32 ↔ NonZeroU32` adjoint and
//! sortable big- / little-endian byte encodings.
//!
//! Q-format / cross-crate isos to `FixedU32<F>` live next door in
//! `crate::fixed::u032`.

#[allow(unused_imports)]
use crate::core::LE;
use crate::core::{ext_int, nz_uint_ext, uint_int_sat, uint_uint, uint_uint_narrow};
use ::core::num::NonZeroU32;

// ── §1 std-int Conns sourced from `u32` ───────────────────────────

ext_int!(U032I064, u32, i64);
ext_int!(U032I128, u32, i128);
uint_int_sat!(U032I008, u32, i8);
uint_int_sat!(U032I016, u32, i16);
uint_int_sat!(U032I032, u32, i32);

uint_uint_narrow!(U032U008, u32, u8);
uint_uint_narrow!(U032U016, u32, u16);
uint_uint!(U032U064, u32, u64);
uint_uint!(U032U128, u32, u128);

// ── §3 u32 ↔ NonZeroU32 ───────────────────────────────────────────

nz_uint_ext!(U032N032, u32, NonZeroU32);

// ── Sortable big-endian byte encodings ────────────────────────────

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

// ── Sortable little-endian byte encodings ─────────────────────────

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
        i008::I008U032, i016::I016U032, i032::I032U032, i064::I064U032, i128::I128U032,
        u008::U008U032, u016::U016U032, u064::U064U032, u128::U128U032,
    };
    use crate::prop::conn as conn_laws;
    use proptest::prelude::*;

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
}
