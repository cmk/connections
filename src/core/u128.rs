//! `u128`-source std-int Conns plus the `u128 ↔ NonZeroU128` adjoint and
//! sortable big- / little-endian byte encodings.
//!
//! Q-format / cross-crate isos to `FixedU128<F>` live next door in
//! [`crate::fixed::u128`].

#[allow(unused_imports)]
use crate::core::LE;
use crate::core::{nz_uint_ext, uint_int_sat, uint_uint_narrow};
use ::core::num::NonZeroU128;

// ── §1 std-int Conns sourced from `u128` ──────────────────────────

uint_int_sat!(U128I008, u128, i8);
uint_int_sat!(U128I016, u128, i16);
uint_int_sat!(U128I032, u128, i32);
uint_int_sat!(U128I064, u128, i64);
uint_int_sat!(U128I128, u128, i128);

uint_uint_narrow!(U128U008, u128, u8);
uint_uint_narrow!(U128U016, u128, u16);
uint_uint_narrow!(U128U032, u128, u32);
uint_uint_narrow!(U128U064, u128, u64);

// ── §3 u128 ↔ NonZeroU128 ─────────────────────────────────────────

nz_uint_ext!(U128N128, u128, NonZeroU128);

// ── Sortable big-endian byte encodings ────────────────────────────

const fn u128_to_be16(x: u128) -> [u8; 16] {
    x.to_be_bytes()
}
const fn be16_to_u128(b: [u8; 16]) -> u128 {
    u128::from_be_bytes(b)
}

crate::iso! {
    /// `u128 ↔ [u8; 16]` — big-endian iso. Byte-lex order matches u128 order.
    pub U128BE16 : u128 => [u8; 16] {
        forward: u128_to_be16,
        back:    be16_to_u128,
    }
}

// ── Sortable little-endian byte encodings ─────────────────────────

const fn u128_to_le16(x: u128) -> LE<16> {
    LE(x.to_le_bytes())
}
const fn le16_to_u128(b: LE<16>) -> u128 {
    u128::from_le_bytes(b.0)
}

crate::iso! {
    /// `u128 ↔ LE<16>` — little-endian iso with numeric-sort ordering.
    pub U128LE16 : u128 => LE<16> {
        forward: u128_to_le16,
        back:    le16_to_u128,
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
        i008::I008U128, i016::I016U128, i032::I032U128, i064::I064U128, i128::I128U128,
        u008::U008U128, u016::U016U128, u032::U032U128, u064::U064U128,
    };
    use crate::prop::conn as conn_laws;
    use proptest::prelude::*;

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

    fn arb_byte16() -> impl Strategy<Value = [u8; 16]> {
        prop_oneof![Just([0; 16]), Just([0xFF; 16]), any::<[u8; 16]>()]
    }

    fn arb_lebyte16() -> impl Strategy<Value = LE<16>> {
        arb_byte16().prop_map(LE)
    }

    proptest! {
        #[test]
        fn u128_be_iso_roundtrip_l(a in prop_oneof![Just(0u128), Just(u128::MAX), any::<u128>()]) {
            prop_assert!(conn_laws::iso_roundtrip_l(&U128BE16.conn_l(), a));
        }
        #[test]
        fn u128_be_roundtrip_ceil(b in arb_byte16()) {
            prop_assert!(conn_laws::roundtrip_ceil(&U128BE16.conn_l(), b));
        }
        #[test]
        fn u128_be_galois_l(a in any::<u128>(), b in arb_byte16()) {
            prop_assert!(conn_laws::galois_l(&U128BE16.conn_l(), a, b));
        }
        #[test]
        fn u128_be_galois_r(a in any::<u128>(), b in arb_byte16()) {
            prop_assert!(conn_laws::galois_r(&U128BE16.conn_r(), a, b));
        }
        #[test]
        fn u128_be_floor_le_ceil(a in any::<u128>()) {
            prop_assert!(conn_laws::floor_le_ceil(&U128BE16, a));
        }
        #[test]
        fn u128_be_order_preserving(a in any::<u128>(), b in any::<u128>()) {
            prop_assert_eq!(a.cmp(&b), U128BE16.ceil(a).cmp(&U128BE16.ceil(b)));
        }

        #[test]
        fn u128_le_iso_roundtrip_l(a in prop_oneof![Just(0u128), Just(u128::MAX), any::<u128>()]) {
            prop_assert!(conn_laws::iso_roundtrip_l(&U128LE16.conn_l(), a));
        }
        #[test]
        fn u128_le_roundtrip_ceil(b in arb_lebyte16()) {
            prop_assert!(conn_laws::roundtrip_ceil(&U128LE16.conn_l(), b));
        }
        #[test]
        fn u128_le_galois_l(a in any::<u128>(), b in arb_lebyte16()) {
            prop_assert!(conn_laws::galois_l(&U128LE16.conn_l(), a, b));
        }
        #[test]
        fn u128_le_galois_r(a in any::<u128>(), b in arb_lebyte16()) {
            prop_assert!(conn_laws::galois_r(&U128LE16.conn_r(), a, b));
        }
        #[test]
        fn u128_le_floor_le_ceil(a in any::<u128>()) {
            prop_assert!(conn_laws::floor_le_ceil(&U128LE16, a));
        }
        #[test]
        fn u128_le_order_preserving(a in any::<u128>(), b in any::<u128>()) {
            prop_assert_eq!(a.cmp(&b), U128LE16.ceil(a).cmp(&U128LE16.ceil(b)));
        }
    }
}
