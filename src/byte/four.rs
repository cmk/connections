//! 4-byte hosts: `u32`, `i32`, `f32`.

// ── u32 ─────────────────────────────────────────────────────────────

const fn u32_to_obyt(x: u32) -> [u8; 4] {
    x.to_be_bytes()
}

const fn obyt_to_u32(b: [u8; 4]) -> u32 {
    u32::from_be_bytes(b)
}

crate::iso! {
    /// `u32 ↔ [u8; 4]` — big-endian iso. Byte-lex order matches u32 order.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::conn::{ConnL, ConnR};
    /// use connections::byte::U032OBYT;
    ///
    /// assert_eq!(U032OBYT.ceil(0xDEADBEEF_u32), [0xDE, 0xAD, 0xBE, 0xEF]);
    /// assert_eq!(U032OBYT.upper([0xDE, 0xAD, 0xBE, 0xEF]), 0xDEADBEEF_u32);
    /// ```
    pub U032OBYT : u32 => [u8; 4] {
        forward: u32_to_obyt,
        back:    obyt_to_u32,
    }
}

// ── i32 ─────────────────────────────────────────────────────────────

const fn i32_to_obyt(x: i32) -> [u8; 4] {
    ((x as u32) ^ 0x8000_0000).to_be_bytes()
}

const fn obyt_to_i32(b: [u8; 4]) -> i32 {
    (u32::from_be_bytes(b) ^ 0x8000_0000) as i32
}

crate::iso! {
    /// `i32 ↔ [u8; 4]` — sign-flipped big-endian iso.
    ///
    /// `i32::MIN` → `[0; 4]`, `0` → `[0x80, 0, 0, 0]`,
    /// `i32::MAX` → `[0xFF; 4]`.
    pub I032OBYT : i32 => [u8; 4] {
        forward: i32_to_obyt,
        back:    obyt_to_i32,
    }
}

// ── f32 ─────────────────────────────────────────────────────────────

/// totalOrder pre-encoding: positive flips sign bit; negative inverts all bits.
/// Same algebra as [`signed32`](crate::float) but emitting bytes instead of i32.
const fn f32_to_obyt(x: f32) -> [u8; 4] {
    let bits = x.to_bits();
    let sortable = if bits & 0x8000_0000 == 0 {
        bits ^ 0x8000_0000
    } else {
        !bits
    };
    sortable.to_be_bytes()
}

const fn obyt_to_f32(b: [u8; 4]) -> f32 {
    let sortable = u32::from_be_bytes(b);
    let bits = if sortable & 0x8000_0000 != 0 {
        sortable ^ 0x8000_0000
    } else {
        !sortable
    };
    f32::from_bits(bits)
}

crate::iso! {
    /// `f32 ↔ [u8; 4]` — IEEE 754 totalOrder iso.
    ///
    /// Pre-encodes via the standard "sortable float" bit trick
    /// (positive: flip sign bit; negative: invert all bits) before
    /// `to_be_bytes`. Result: byte-lex order matches
    /// [`f32::total_cmp`]. Round-trip is bit-exact, including NaN
    /// payloads.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::conn::{ConnL, ConnR};
    /// use connections::byte::F032OBYT;
    ///
    /// // Round-trip preserves bits even for NaN.
    /// let nan = f32::from_bits(0x7FC0_1234);
    /// assert_eq!(F032OBYT.upper(F032OBYT.ceil(nan)).to_bits(), nan.to_bits());
    ///
    /// // Order matches f32::total_cmp.
    /// let neg = -1.5_f32;
    /// let pos =  0.5_f32;
    /// assert!(F032OBYT.ceil(neg) < F032OBYT.ceil(pos));
    /// ```
    pub F032OBYT : f32 => [u8; 4] {
        forward: f32_to_obyt,
        back:    obyt_to_f32,
    }
}

// ── tests ───────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::conn::{ConnL, ConnR};
    use crate::prop::conn as conn_laws;
    use proptest::prelude::*;

    fn arb_u32() -> impl Strategy<Value = u32> {
        prop_oneof![Just(0u32), Just(u32::MAX), any::<u32>()]
    }
    fn arb_i32() -> impl Strategy<Value = i32> {
        prop_oneof![Just(i32::MIN), Just(0i32), Just(i32::MAX), any::<i32>()]
    }
    fn arb_byte4() -> impl Strategy<Value = [u8; 4]> {
        prop_oneof![
            Just([0; 4]),
            Just([0xFF; 4]),
            Just([0x80, 0, 0, 0]),
            any::<[u8; 4]>()
        ]
    }

    proptest! {
        // u32
        #[test]
        fn u032_obyt_iso_roundtrip_l(a in arb_u32()) {
            prop_assert!(conn_laws::iso_roundtrip_l(&U032OBYT.conn_l(), a));
        }
        #[test]
        fn u032_obyt_roundtrip_ceil(b in arb_byte4()) {
            prop_assert!(conn_laws::roundtrip_ceil(&U032OBYT.conn_l(), b));
        }
        #[test]
        fn u032_obyt_galois_l(a in arb_u32(), b in arb_byte4()) {
            prop_assert!(conn_laws::galois_l(&U032OBYT.conn_l(), a, b));
        }
        #[test]
        fn u032_obyt_galois_r(a in arb_u32(), b in arb_byte4()) {
            prop_assert!(conn_laws::galois_r(&U032OBYT.conn_r(), a, b));
        }
        #[test]
        fn u032_obyt_floor_le_ceil(a in arb_u32()) {
            prop_assert!(conn_laws::floor_le_ceil(&U032OBYT, a));
        }
        #[test]
        fn u032_obyt_order_preserving(a in arb_u32(), b in arb_u32()) {
            prop_assert_eq!(a.cmp(&b), U032OBYT.ceil(a).cmp(&U032OBYT.ceil(b)));
        }

        // i32
        #[test]
        fn i032_obyt_iso_roundtrip_l(a in arb_i32()) {
            prop_assert!(conn_laws::iso_roundtrip_l(&I032OBYT.conn_l(), a));
        }
        #[test]
        fn i032_obyt_roundtrip_ceil(b in arb_byte4()) {
            prop_assert!(conn_laws::roundtrip_ceil(&I032OBYT.conn_l(), b));
        }
        #[test]
        fn i032_obyt_galois_l(a in arb_i32(), b in arb_byte4()) {
            prop_assert!(conn_laws::galois_l(&I032OBYT.conn_l(), a, b));
        }
        #[test]
        fn i032_obyt_galois_r(a in arb_i32(), b in arb_byte4()) {
            prop_assert!(conn_laws::galois_r(&I032OBYT.conn_r(), a, b));
        }
        #[test]
        fn i032_obyt_floor_le_ceil(a in arb_i32()) {
            prop_assert!(conn_laws::floor_le_ceil(&I032OBYT, a));
        }
        #[test]
        fn i032_obyt_order_preserving(a in arb_i32(), b in arb_i32()) {
            prop_assert_eq!(a.cmp(&b), I032OBYT.ceil(a).cmp(&I032OBYT.ceil(b)));
        }

        // f32 — test on bits rather than values so NaN!=NaN doesn't break
        // iso_roundtrip_l (NaN payloads ARE preserved through to_bits/from_bits,
        // but the bare `==` comparison rejects NaN).
        #[test]
        fn f032_obyt_iso_roundtrip_bits(bits in any::<u32>()) {
            let a = f32::from_bits(bits);
            prop_assert_eq!(F032OBYT.upper(F032OBYT.ceil(a)).to_bits(), bits);
        }
        #[test]
        fn f032_obyt_roundtrip_ceil(b in arb_byte4()) {
            prop_assert!(conn_laws::roundtrip_ceil(&F032OBYT.conn_l(), b));
        }
        #[test]
        fn f032_obyt_order_preserving(a_bits in any::<u32>(), b_bits in any::<u32>()) {
            let a = f32::from_bits(a_bits);
            let b = f32::from_bits(b_bits);
            prop_assert_eq!(a.total_cmp(&b), F032OBYT.ceil(a).cmp(&F032OBYT.ceil(b)));
        }
        // Total-order Galois analogs (the classical `<=` predicate fails on
        // byte arrays that decode to NaN; `total_cmp` is the order the byte
        // encoding actually implements). Mirrors `byte_four::f032_obyt::galois_*_total`.
        #[test]
        fn f032_obyt_galois_l_total(a_bits in any::<u32>(), b in arb_byte4()) {
            let a = f32::from_bits(a_bits);
            let c = F032OBYT.conn_l();
            let lhs = c.ceil(a) <= b;
            let rhs = a.total_cmp(&c.upper(b)).is_le();
            prop_assert_eq!(lhs, rhs);
        }
        #[test]
        fn f032_obyt_galois_r_total(a_bits in any::<u32>(), b in arb_byte4()) {
            let a = f32::from_bits(a_bits);
            let c = F032OBYT.conn_r();
            let lhs = c.lower(b).total_cmp(&a).is_le();
            let rhs = b <= c.floor(a);
            prop_assert_eq!(lhs, rhs);
        }
    }
}
