//! `i128`-source std-int Conns plus the `i128 ↔ NonZeroI128` adjoint and
//! two's-complement big- / little-endian byte encodings.
//!
//! Q-format / cross-crate isos to `FixedI128<F>` live next door in
//! `crate::fixed::i128`.

#[allow(unused_imports)]
use crate::core::{B2, L2};
use crate::core::{int_int_narrow, int_uint, int_uint_narrow, nz_int_ext};
use ::core::num::NonZeroI128;

// ── §1 std-int Conns sourced from `i128` ──────────────────────────

int_int_narrow!(I128I008, i128, i8);
int_int_narrow!(I128I016, i128, i16);
int_int_narrow!(I128I032, i128, i32);
int_int_narrow!(I128I064, i128, i64);

int_uint_narrow!(I128U008, i128, u8);
int_uint_narrow!(I128U016, i128, u16);
int_uint_narrow!(I128U032, i128, u32);
int_uint_narrow!(I128U064, i128, u64);
int_uint!(I128U128, i128, u128);

// ── §3 i128 ↔ NonZeroI128 ─────────────────────────────────────────

nz_int_ext!(I128N128, i128, NonZeroI128);

// ── Two's-complement big-endian byte encodings ────────────────────

const fn i128_to_be16(x: i128) -> B2<16> {
    B2(x.to_be_bytes())
}
const fn be16_to_i128(b: B2<16>) -> i128 {
    i128::from_be_bytes(b.0)
}

crate::iso! {
    /// `i128 ↔ B2<16>` — raw two's-complement big-endian iso.
    pub I128BE16 : i128 => B2<16> {
        forward: i128_to_be16,
        back:    be16_to_i128,
    }
}

// ── Two's-complement little-endian byte encodings ─────────────────

const fn i128_to_le16(x: i128) -> L2<16> {
    L2(x.to_le_bytes())
}
const fn le16_to_i128(b: L2<16>) -> i128 {
    i128::from_le_bytes(b.0)
}

crate::iso! {
    /// `i128 ↔ L2<16>` — raw two's-complement little-endian iso.
    pub I128LE16 : i128 => L2<16> {
        forward: i128_to_le16,
        back:    le16_to_i128,
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
        i008::I008I128, i016::I016I128, i032::I032I128, i064::I064I128, u008::U008I128,
        u016::U016I128, u032::U032I128, u064::U064I128, u128::U128I128,
    };
    use crate::extended::Extended;
    use crate::prop::conn as conn_laws;
    use proptest::prelude::*;

    #[test]
    fn i064i128_extends_to_one_above() {
        assert_eq!(I064I128.ceil(Extended::PosInf), (i64::MAX as i128) + 1);
        assert_eq!(I064I128.ceil(Extended::NegInf), i128::MIN);
    }

    #[test]
    fn u064i128_extends_to_one_above() {
        assert_eq!(U064I128.ceil(Extended::PosInf), (u64::MAX as i128) + 1);
        assert_eq!(U064I128.ceil(Extended::NegInf), i128::MIN);
    }

    #[test]
    fn u128i128_neg_and_high() {
        assert_eq!(U128I128.lower(-1), 0_u128);
        assert_eq!(U128I128.lower(i128::MIN), 0_u128);
        assert_eq!(U128I128.floor(u128::MAX), i128::MAX);
        assert_eq!(U128I128.floor(U128I128.lower(50)), 50);
        assert_eq!(U128I128.floor(U128I128.lower(i128::MAX)), i128::MAX);
    }

    fn arb_byte16() -> impl Strategy<Value = B2<16>> {
        prop_oneof![Just([0; 16]), Just([0xFF; 16]), any::<[u8; 16]>()].prop_map(B2)
    }

    fn arb_lebyte16() -> impl Strategy<Value = L2<16>> {
        prop_oneof![Just([0; 16]), Just([0xFF; 16]), any::<[u8; 16]>()].prop_map(L2)
    }

    proptest! {
        #[test]
        fn i128_b2_iso_roundtrip_l(a in prop_oneof![Just(i128::MIN), Just(0i128), Just(i128::MAX), any::<i128>()]) {
            prop_assert!(conn_laws::iso_roundtrip_l(&I128BE16.conn_l(), a));
        }
        #[test]
        fn i128_b2_roundtrip_ceil(b in arb_byte16()) {
            prop_assert!(conn_laws::roundtrip_ceil(&I128BE16.conn_l(), b));
        }
        #[test]
        fn i128_b2_galois_l(a in any::<i128>(), b in arb_byte16()) {
            prop_assert!(conn_laws::galois_l(&I128BE16.conn_l(), a, b));
        }
        #[test]
        fn i128_b2_galois_r(a in any::<i128>(), b in arb_byte16()) {
            prop_assert!(conn_laws::galois_r(&I128BE16.conn_r(), a, b));
        }
        #[test]
        fn i128_b2_floor_le_ceil(a in any::<i128>()) {
            prop_assert!(conn_laws::floor_le_ceil(&I128BE16, a));
        }
        #[test]
        fn i128_b2_order_preserving(a in any::<i128>(), b in any::<i128>()) {
            prop_assert_eq!(a.cmp(&b), I128BE16.ceil(a).cmp(&I128BE16.ceil(b)));
        }

        #[test]
        fn i128_l2_iso_roundtrip_l(a in prop_oneof![Just(i128::MIN), Just(0i128), Just(i128::MAX), any::<i128>()]) {
            prop_assert!(conn_laws::iso_roundtrip_l(&I128LE16.conn_l(), a));
        }
        #[test]
        fn i128_l2_roundtrip_ceil(b in arb_lebyte16()) {
            prop_assert!(conn_laws::roundtrip_ceil(&I128LE16.conn_l(), b));
        }
        #[test]
        fn i128_l2_galois_l(a in any::<i128>(), b in arb_lebyte16()) {
            prop_assert!(conn_laws::galois_l(&I128LE16.conn_l(), a, b));
        }
        #[test]
        fn i128_l2_galois_r(a in any::<i128>(), b in arb_lebyte16()) {
            prop_assert!(conn_laws::galois_r(&I128LE16.conn_r(), a, b));
        }
        #[test]
        fn i128_l2_floor_le_ceil(a in any::<i128>()) {
            prop_assert!(conn_laws::floor_le_ceil(&I128LE16, a));
        }
        #[test]
        fn i128_l2_order_preserving(a in any::<i128>(), b in any::<i128>()) {
            prop_assert_eq!(a.cmp(&b), I128LE16.ceil(a).cmp(&I128LE16.ceil(b)));
        }
    }
}
