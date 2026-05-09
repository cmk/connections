//! 8-byte hosts: `u64`, `i64`. Kani-deferred (proptest only). (`f64`
//! host deferred — see `src/byte.rs`.)

// ── u64 ─────────────────────────────────────────────────────────────

const fn u64_to_obyt(x: u64) -> [u8; 8] {
    x.to_be_bytes()
}

const fn obyt_to_u64(b: [u8; 8]) -> u64 {
    u64::from_be_bytes(b)
}

crate::iso! {
    /// `u64 ↔ [u8; 8]` — big-endian iso.
    pub U064OBYT : u64 => [u8; 8] {
        forward: u64_to_obyt,
        back:    obyt_to_u64,
    }
}

// ── i64 ─────────────────────────────────────────────────────────────

const fn i64_to_obyt(x: i64) -> [u8; 8] {
    ((x as u64) ^ 0x8000_0000_0000_0000).to_be_bytes()
}

const fn obyt_to_i64(b: [u8; 8]) -> i64 {
    (u64::from_be_bytes(b) ^ 0x8000_0000_0000_0000) as i64
}

crate::iso! {
    /// `i64 ↔ [u8; 8]` — sign-flipped big-endian iso.
    pub I064OBYT : i64 => [u8; 8] {
        forward: i64_to_obyt,
        back:    obyt_to_i64,
    }
}

// `F064OBYT` deferred — see `src/byte.rs` for the NaN/PartialOrd rationale.

// ── tests ───────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::conn::{ConnL, ConnR};
    use crate::prop::conn as conn_laws;
    use proptest::prelude::*;

    fn arb_u64() -> impl Strategy<Value = u64> {
        prop_oneof![Just(0u64), Just(u64::MAX), any::<u64>()]
    }
    fn arb_i64() -> impl Strategy<Value = i64> {
        prop_oneof![Just(i64::MIN), Just(0i64), Just(i64::MAX), any::<i64>()]
    }
    fn arb_byte8() -> impl Strategy<Value = [u8; 8]> {
        prop_oneof![
            Just([0; 8]),
            Just([0xFF; 8]),
            Just([0x80, 0, 0, 0, 0, 0, 0, 0]),
            any::<[u8; 8]>()
        ]
    }

    proptest! {
        // u64
        #[test]
        fn u064_obyt_iso_roundtrip_l(a in arb_u64()) {
            prop_assert!(conn_laws::iso_roundtrip_l(&U064OBYT.conn_l(), a));
        }
        #[test]
        fn u064_obyt_roundtrip_ceil(b in arb_byte8()) {
            prop_assert!(conn_laws::roundtrip_ceil(&U064OBYT.conn_l(), b));
        }
        #[test]
        fn u064_obyt_galois_l(a in arb_u64(), b in arb_byte8()) {
            prop_assert!(conn_laws::galois_l(&U064OBYT.conn_l(), a, b));
        }
        #[test]
        fn u064_obyt_galois_r(a in arb_u64(), b in arb_byte8()) {
            prop_assert!(conn_laws::galois_r(&U064OBYT.conn_r(), a, b));
        }
        #[test]
        fn u064_obyt_floor_le_ceil(a in arb_u64()) {
            prop_assert!(conn_laws::floor_le_ceil(&U064OBYT, a));
        }
        #[test]
        fn u064_obyt_order_preserving(a in arb_u64(), b in arb_u64()) {
            prop_assert_eq!(a.cmp(&b), U064OBYT.ceil(a).cmp(&U064OBYT.ceil(b)));
        }

        // i64
        #[test]
        fn i064_obyt_iso_roundtrip_l(a in arb_i64()) {
            prop_assert!(conn_laws::iso_roundtrip_l(&I064OBYT.conn_l(), a));
        }
        #[test]
        fn i064_obyt_roundtrip_ceil(b in arb_byte8()) {
            prop_assert!(conn_laws::roundtrip_ceil(&I064OBYT.conn_l(), b));
        }
        #[test]
        fn i064_obyt_galois_l(a in arb_i64(), b in arb_byte8()) {
            prop_assert!(conn_laws::galois_l(&I064OBYT.conn_l(), a, b));
        }
        #[test]
        fn i064_obyt_galois_r(a in arb_i64(), b in arb_byte8()) {
            prop_assert!(conn_laws::galois_r(&I064OBYT.conn_r(), a, b));
        }
        #[test]
        fn i064_obyt_floor_le_ceil(a in arb_i64()) {
            prop_assert!(conn_laws::floor_le_ceil(&I064OBYT, a));
        }
        #[test]
        fn i064_obyt_order_preserving(a in arb_i64(), b in arb_i64()) {
            prop_assert_eq!(a.cmp(&b), I064OBYT.ceil(a).cmp(&I064OBYT.ceil(b)));
        }
    }
}
