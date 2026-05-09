//! 1-byte hosts: `u8`, `i8`, `bool`.

// ── u8 ──────────────────────────────────────────────────────────────

const fn u8_to_be(x: u8) -> [u8; 1] {
    [x]
}

const fn be_to_u8(b: [u8; 1]) -> u8 {
    b[0]
}

crate::iso! {
    /// `u8 ↔ [u8; 1]` — trivial big-endian iso.
    ///
    /// Both directions are bit-exact; byte-lex order is u8 numeric
    /// order at one byte width.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::conn::{ConnL, ConnR};
    /// use connections::byte::U008BE01;
    ///
    /// assert_eq!(U008BE01.ceil(0x42_u8), [0x42]);
    /// assert_eq!(U008BE01.upper([0x42]), 0x42_u8);
    /// ```
    pub U008BE01 : u8 => [u8; 1] {
        forward: u8_to_be,
        back:    be_to_u8,
    }
}

// ── i8 ──────────────────────────────────────────────────────────────

/// Sortable bit-projection: flip the sign bit so `i8::MIN → [0]`,
/// `0 → [0x80]`, `i8::MAX → [0xFF]`.
const fn i8_to_be(x: i8) -> [u8; 1] {
    [(x as u8) ^ 0x80]
}

const fn be_to_i8(b: [u8; 1]) -> i8 {
    (b[0] ^ 0x80) as i8
}

crate::iso! {
    /// `i8 ↔ [u8; 1]` — sign-flipped iso so byte order matches signed order.
    ///
    /// Forward XORs the sign bit so `i8::MIN` maps to `[0x00]` and
    /// `i8::MAX` maps to `[0xFF]`; the reverse XOR recovers the
    /// signed value bit-exactly.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::conn::{ConnL, ConnR};
    /// use connections::byte::I008BE01;
    ///
    /// assert_eq!(I008BE01.ceil(i8::MIN), [0x00]);
    /// assert_eq!(I008BE01.ceil(0_i8),    [0x80]);
    /// assert_eq!(I008BE01.ceil(i8::MAX), [0xFF]);
    /// assert_eq!(I008BE01.upper([0x00]), i8::MIN);
    /// ```
    pub I008BE01 : i8 => [u8; 1] {
        forward: i8_to_be,
        back:    be_to_i8,
    }
}

// ── bool ────────────────────────────────────────────────────────────

const fn bool_to_be(x: bool) -> [u8; 1] {
    [x as u8]
}

/// Lossy back: any non-zero byte is `true`, only `[0]` is `false`.
/// This makes `BOOLBE01` a one-sided `conn_l!` (not an iso) — the
/// `roundtrip_ceil` law fails for bytes `0x02..=0xFF` (they all
/// collapse to `true → [1]`). Galois L still holds: `ceil(true) = [1]`
/// and `inner` returns `true` exactly for `b ≥ [1]`, so the threshold
/// `b ≥ ceil(a)` matches `inner(b) ≥ a` for both `a` values.
const fn be_to_bool(b: [u8; 1]) -> bool {
    b[0] != 0
}

crate::conn_l! {
    /// `bool → [u8; 1]` — one-sided projection.
    ///
    /// Forward emits `[0]` for `false` and `[1]` for `true`. Back
    /// (`inner`) treats any non-zero byte as `true`, which means
    /// the byte side is non-injective: this Conn is **not** a
    /// full iso. Shipped as a one-sided left-Galois Conn so the
    /// adjoint law `ceil(a) ≤ b ⟺ a ≤ inner(b)` is the only
    /// thing claimed.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::conn::ConnL;
    /// use connections::byte::BOOLBE01;
    ///
    /// assert_eq!(BOOLBE01.ceil(false), [0]);
    /// assert_eq!(BOOLBE01.ceil(true),  [1]);
    /// assert_eq!(BOOLBE01.upper([0]),   false);
    /// assert_eq!(BOOLBE01.upper([1]),   true);
    /// // Non-canonical encodings collapse to true:
    /// assert_eq!(BOOLBE01.upper([0xFF]), true);
    /// ```
    pub BOOLBE01 : bool => [u8; 1] {
        ceil:  bool_to_be,
        inner: be_to_bool,
    }
}

// ── tests ───────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::conn::{ConnL, ConnR};
    use crate::prop::conn as conn_laws;
    use proptest::prelude::*;

    // Per CLAUDE.md: bias integer strategies toward MIN/MAX/0 boundaries.
    fn arb_u8() -> impl Strategy<Value = u8> {
        prop_oneof![Just(0u8), Just(u8::MAX), any::<u8>()]
    }
    fn arb_i8() -> impl Strategy<Value = i8> {
        prop_oneof![Just(i8::MIN), Just(0i8), Just(i8::MAX), any::<i8>()]
    }
    fn arb_byte1() -> impl Strategy<Value = [u8; 1]> {
        prop_oneof![
            Just([0u8]),
            Just([u8::MAX]),
            Just([0x80u8]),
            any::<[u8; 1]>()
        ]
    }

    // ---- u8 -----------------------------------------------------------------

    proptest! {
        #[test]
        fn u008_be_iso_roundtrip_l(a in arb_u8()) {
            prop_assert!(conn_laws::iso_roundtrip_l(&U008BE01.conn_l(), a));
        }

        #[test]
        fn u008_be_roundtrip_ceil(b in arb_byte1()) {
            prop_assert!(conn_laws::roundtrip_ceil(&U008BE01.conn_l(), b));
        }

        #[test]
        fn u008_be_galois_l(a in arb_u8(), b in arb_byte1()) {
            prop_assert!(conn_laws::galois_l(&U008BE01.conn_l(), a, b));
        }

        #[test]
        fn u008_be_galois_r(a in arb_u8(), b in arb_byte1()) {
            prop_assert!(conn_laws::galois_r(&U008BE01.conn_r(), a, b));
        }

        #[test]
        fn u008_be_floor_le_ceil(a in arb_u8()) {
            prop_assert!(conn_laws::floor_le_ceil(&U008BE01, a));
        }

        #[test]
        fn u008_be_order_preserving(a in arb_u8(), b in arb_u8()) {
            // Total bijection that preserves order: ceil monotone iff host order matches byte-lex.
            let ord = a.cmp(&b);
            let bord = U008BE01.ceil(a).cmp(&U008BE01.ceil(b));
            prop_assert_eq!(ord, bord);
        }
    }

    // ---- i8 -----------------------------------------------------------------

    proptest! {
        #[test]
        fn i008_be_iso_roundtrip_l(a in arb_i8()) {
            prop_assert!(conn_laws::iso_roundtrip_l(&I008BE01.conn_l(), a));
        }

        #[test]
        fn i008_be_roundtrip_ceil(b in arb_byte1()) {
            prop_assert!(conn_laws::roundtrip_ceil(&I008BE01.conn_l(), b));
        }

        #[test]
        fn i008_be_galois_l(a in arb_i8(), b in arb_byte1()) {
            prop_assert!(conn_laws::galois_l(&I008BE01.conn_l(), a, b));
        }

        #[test]
        fn i008_be_galois_r(a in arb_i8(), b in arb_byte1()) {
            prop_assert!(conn_laws::galois_r(&I008BE01.conn_r(), a, b));
        }

        #[test]
        fn i008_be_floor_le_ceil(a in arb_i8()) {
            prop_assert!(conn_laws::floor_le_ceil(&I008BE01, a));
        }

        #[test]
        fn i008_be_order_preserving(a in arb_i8(), b in arb_i8()) {
            let ord = a.cmp(&b);
            let bord = I008BE01.ceil(a).cmp(&I008BE01.ceil(b));
            prop_assert_eq!(ord, bord);
        }
    }

    // ---- bool ---------------------------------------------------------------

    proptest! {
        // BOOLBE01 is one-sided conn_l, so iso_roundtrip_l (b → ceil ∘ inner) does NOT
        // hold and is not asserted. Galois L is the only adjoint law.

        #[test]
        fn bool_be_galois_l(a: bool, b in arb_byte1()) {
            prop_assert!(conn_laws::galois_l(&BOOLBE01, a, b));
        }

        #[test]
        fn bool_be_host_roundtrip_l(a: bool) {
            // Host-side round-trip only: `inner ∘ ceil = id`. Byte-side
            // (`ceil ∘ inner = id`) is intentionally absent — see the doc
            // comment on `be_to_bool`. The `iso_roundtrip_l` predicate is
            // misnamed for one-sided Conns; it asserts only the host-side
            // identity, which holds here.
            prop_assert!(conn_laws::iso_roundtrip_l(&BOOLBE01, a));
        }

        #[test]
        fn bool_be_order_preserving(a: bool, b: bool) {
            let ord = a.cmp(&b);
            let bord = BOOLBE01.ceil(a).cmp(&BOOLBE01.ceil(b));
            prop_assert_eq!(ord, bord);
        }
    }
}
