//! 2-byte hosts: `u16`, `i16`. (`f16` host deferred — see `src/byte.rs`.)

// ── u16 ─────────────────────────────────────────────────────────────

const fn u16_to_obyt(x: u16) -> [u8; 2] {
    x.to_be_bytes()
}

const fn obyt_to_u16(b: [u8; 2]) -> u16 {
    u16::from_be_bytes(b)
}

crate::iso! {
    /// `u16 ↔ [u8; 2]` — big-endian iso. Byte-lex order matches u16 order.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::conn::{ConnL, ConnR};
    /// use connections::byte::U016OBYT;
    ///
    /// assert_eq!(U016OBYT.ceil(0xBEEF_u16), [0xBE, 0xEF]);
    /// assert_eq!(U016OBYT.upper([0xBE, 0xEF]), 0xBEEF_u16);
    /// ```
    pub U016OBYT : u16 => [u8; 2] {
        forward: u16_to_obyt,
        back:    obyt_to_u16,
    }
}

// ── i16 ─────────────────────────────────────────────────────────────

const fn i16_to_obyt(x: i16) -> [u8; 2] {
    ((x as u16) ^ 0x8000).to_be_bytes()
}

const fn obyt_to_i16(b: [u8; 2]) -> i16 {
    (u16::from_be_bytes(b) ^ 0x8000) as i16
}

crate::iso! {
    /// `i16 ↔ [u8; 2]` — sign-flipped big-endian iso.
    ///
    /// `i16::MIN` → `[0x00, 0x00]`, `0` → `[0x80, 0x00]`,
    /// `i16::MAX` → `[0xFF, 0xFF]`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::conn::{ConnL, ConnR};
    /// use connections::byte::I016OBYT;
    ///
    /// assert_eq!(I016OBYT.ceil(i16::MIN), [0x00, 0x00]);
    /// assert_eq!(I016OBYT.ceil(0_i16),    [0x80, 0x00]);
    /// assert_eq!(I016OBYT.ceil(i16::MAX), [0xFF, 0xFF]);
    /// ```
    pub I016OBYT : i16 => [u8; 2] {
        forward: i16_to_obyt,
        back:    obyt_to_i16,
    }
}

// `F016OBYT` deferred — see `src/byte.rs` for the NaN/PartialOrd rationale.

// ── tests ───────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::conn::{ConnL, ConnR};
    use crate::prop::conn as conn_laws;
    use proptest::prelude::*;

    fn arb_u16() -> impl Strategy<Value = u16> {
        prop_oneof![Just(0u16), Just(u16::MAX), any::<u16>()]
    }
    fn arb_i16() -> impl Strategy<Value = i16> {
        prop_oneof![Just(i16::MIN), Just(0i16), Just(i16::MAX), any::<i16>()]
    }
    fn arb_byte2() -> impl Strategy<Value = [u8; 2]> {
        prop_oneof![
            Just([0; 2]),
            Just([0xFF; 2]),
            Just([0x80, 0]),
            any::<[u8; 2]>()
        ]
    }

    proptest! {
        #[test]
        fn u016_obyt_iso_roundtrip_l(a in arb_u16()) {
            prop_assert!(conn_laws::iso_roundtrip_l(&U016OBYT.conn_l(), a));
        }

        #[test]
        fn u016_obyt_roundtrip_ceil(b in arb_byte2()) {
            prop_assert!(conn_laws::roundtrip_ceil(&U016OBYT.conn_l(), b));
        }

        #[test]
        fn u016_obyt_galois_l(a in arb_u16(), b in arb_byte2()) {
            prop_assert!(conn_laws::galois_l(&U016OBYT.conn_l(), a, b));
        }

        #[test]
        fn u016_obyt_galois_r(a in arb_u16(), b in arb_byte2()) {
            prop_assert!(conn_laws::galois_r(&U016OBYT.conn_r(), a, b));
        }

        #[test]
        fn u016_obyt_floor_le_ceil(a in arb_u16()) {
            prop_assert!(conn_laws::floor_le_ceil(&U016OBYT, a));
        }

        #[test]
        fn u016_obyt_order_preserving(a in arb_u16(), b in arb_u16()) {
            prop_assert_eq!(a.cmp(&b), U016OBYT.ceil(a).cmp(&U016OBYT.ceil(b)));
        }

        #[test]
        fn i016_obyt_iso_roundtrip_l(a in arb_i16()) {
            prop_assert!(conn_laws::iso_roundtrip_l(&I016OBYT.conn_l(), a));
        }

        #[test]
        fn i016_obyt_roundtrip_ceil(b in arb_byte2()) {
            prop_assert!(conn_laws::roundtrip_ceil(&I016OBYT.conn_l(), b));
        }

        #[test]
        fn i016_obyt_galois_l(a in arb_i16(), b in arb_byte2()) {
            prop_assert!(conn_laws::galois_l(&I016OBYT.conn_l(), a, b));
        }

        #[test]
        fn i016_obyt_galois_r(a in arb_i16(), b in arb_byte2()) {
            prop_assert!(conn_laws::galois_r(&I016OBYT.conn_r(), a, b));
        }

        #[test]
        fn i016_obyt_floor_le_ceil(a in arb_i16()) {
            prop_assert!(conn_laws::floor_le_ceil(&I016OBYT, a));
        }

        #[test]
        fn i016_obyt_order_preserving(a in arb_i16(), b in arb_i16()) {
            prop_assert_eq!(a.cmp(&b), I016OBYT.ceil(a).cmp(&I016OBYT.ceil(b)));
        }
    }
}
