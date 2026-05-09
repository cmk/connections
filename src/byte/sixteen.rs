//! 16-byte hosts: `u128`, `i128`. Kani-deferred (proptest only).

// ── u128 ────────────────────────────────────────────────────────────

const fn u128_to_be(x: u128) -> [u8; 16] {
    x.to_be_bytes()
}

const fn be_to_u128(b: [u8; 16]) -> u128 {
    u128::from_be_bytes(b)
}

crate::iso! {
    /// `u128 ↔ [u8; 16]` — big-endian iso.
    pub U128BE16 : u128 => [u8; 16] {
        forward: u128_to_be,
        back:    be_to_u128,
    }
}

// ── i128 ────────────────────────────────────────────────────────────

const fn i128_to_be(x: i128) -> [u8; 16] {
    ((x as u128) ^ 0x8000_0000_0000_0000_0000_0000_0000_0000).to_be_bytes()
}

const fn be_to_i128(b: [u8; 16]) -> i128 {
    (u128::from_be_bytes(b) ^ 0x8000_0000_0000_0000_0000_0000_0000_0000) as i128
}

crate::iso! {
    /// `i128 ↔ [u8; 16]` — sign-flipped big-endian iso.
    pub I128BE16 : i128 => [u8; 16] {
        forward: i128_to_be,
        back:    be_to_i128,
    }
}

// ── tests ───────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::conn::{ConnL, ConnR};
    use crate::prop::conn as conn_laws;
    use proptest::prelude::*;

    fn arb_u128() -> impl Strategy<Value = u128> {
        prop_oneof![Just(0u128), Just(u128::MAX), any::<u128>()]
    }
    fn arb_i128() -> impl Strategy<Value = i128> {
        prop_oneof![Just(i128::MIN), Just(0i128), Just(i128::MAX), any::<i128>()]
    }
    fn arb_byte16() -> impl Strategy<Value = [u8; 16]> {
        prop_oneof![
            Just([0; 16]),
            Just([0xFF; 16]),
            Just({
                let mut a = [0u8; 16];
                a[0] = 0x80;
                a
            }),
            any::<[u8; 16]>()
        ]
    }

    proptest! {
        // u128
        #[test]
        fn u128_be_iso_roundtrip_l(a in arb_u128()) {
            prop_assert!(conn_laws::iso_roundtrip_l(&U128BE16.conn_l(), a));
        }
        #[test]
        fn u128_be_roundtrip_ceil(b in arb_byte16()) {
            prop_assert!(conn_laws::roundtrip_ceil(&U128BE16.conn_l(), b));
        }
        #[test]
        fn u128_be_galois_l(a in arb_u128(), b in arb_byte16()) {
            prop_assert!(conn_laws::galois_l(&U128BE16.conn_l(), a, b));
        }
        #[test]
        fn u128_be_galois_r(a in arb_u128(), b in arb_byte16()) {
            prop_assert!(conn_laws::galois_r(&U128BE16.conn_r(), a, b));
        }
        #[test]
        fn u128_be_floor_le_ceil(a in arb_u128()) {
            prop_assert!(conn_laws::floor_le_ceil(&U128BE16, a));
        }
        #[test]
        fn u128_be_order_preserving(a in arb_u128(), b in arb_u128()) {
            prop_assert_eq!(a.cmp(&b), U128BE16.ceil(a).cmp(&U128BE16.ceil(b)));
        }

        // i128
        #[test]
        fn i128_be_iso_roundtrip_l(a in arb_i128()) {
            prop_assert!(conn_laws::iso_roundtrip_l(&I128BE16.conn_l(), a));
        }
        #[test]
        fn i128_be_roundtrip_ceil(b in arb_byte16()) {
            prop_assert!(conn_laws::roundtrip_ceil(&I128BE16.conn_l(), b));
        }
        #[test]
        fn i128_be_galois_l(a in arb_i128(), b in arb_byte16()) {
            prop_assert!(conn_laws::galois_l(&I128BE16.conn_l(), a, b));
        }
        #[test]
        fn i128_be_galois_r(a in arb_i128(), b in arb_byte16()) {
            prop_assert!(conn_laws::galois_r(&I128BE16.conn_r(), a, b));
        }
        #[test]
        fn i128_be_floor_le_ceil(a in arb_i128()) {
            prop_assert!(conn_laws::floor_le_ceil(&I128BE16, a));
        }
        #[test]
        fn i128_be_order_preserving(a in arb_i128(), b in arb_i128()) {
            prop_assert_eq!(a.cmp(&b), I128BE16.ceil(a).cmp(&I128BE16.ceil(b)));
        }
    }
}
