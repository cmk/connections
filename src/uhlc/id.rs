//! `Conn<ID, LX<16>, R>` — right-Galois only. `ID` is a 16-byte
//! LE-stored token whose derived `Ord` is byte-lex from byte 0 of
//! `to_le_bytes()` (i.e., **LSB-first** under LE storage);
//! [`LX<16>`](crate::core::LX) is the identity byte-wrapper with the
//! same derived `Ord`. `LX<16>` carries one value (`LX([0; 16])`)
//! that no `ID` represents — `ID`'s construction enforces a non-zero
//! `u128` invariant (`uhlc-rs/src/id.rs:127-129`).
//!
//! The connection is total-via-saturation: the puncture maps to the
//! lex-min valid `ID` (the byte array `[0,…,0,1]`, equal to
//! `NonZeroU128::new(1 << 120).unwrap()`). L-Galois fails at that
//! boundary; R-Galois holds, so this is a `conn_r!` rather than an
//! `iso!`. See the plan-2026-05-19-03 derivation for the worked
//! corner case.
//!
//! **No panics on reachable inputs.** `ID::try_from(&[u8; 16])`
//! errors only on the all-zero array, which the puncture branch
//! avoids by routing to `LEX_MIN_ID_BYTES`; the `unreachable!()`
//! arm is dead code at every reachable call site, and the Kani
//! `lower_never_panics` harness in `src/kani/uhlc.rs` proves
//! totality over the full `[u8; 16]` domain.

use uhlc::ID;

use crate::core::LX;

/// Lex-min valid `ID` under the byte-lex-from-byte-0 Ord — byte 15
/// = 1, all other bytes 0. Numerically this is `1 << 120`, but
/// under `ID`'s derived `Ord` it is the minimum.
const LEX_MIN_ID_BYTES: [u8; 16] = {
    let mut b = [0u8; 16];
    b[15] = 1;
    b
};

fn id_to_lx16(id: ID) -> LX<16> {
    LX(id.to_le_bytes())
}

fn lx16_to_id(lx: LX<16>) -> ID {
    let bytes: &[u8; 16] = if lx.0 == [0u8; 16] {
        &LEX_MIN_ID_BYTES
    } else {
        &lx.0
    };
    ID::try_from(bytes).unwrap_or_else(|_| unreachable!())
}

crate::conn_r! {
    /// `Conn<ID, LX<16>, R>` — `ID`'s 16-byte representation with
    /// saturating decode at the all-zero byte string.
    ///
    /// - `.floor(id)` (lossless): `id` → its LE-bytes-as-`LX<16>`.
    /// - `.lower(lx)` (saturating): valid bytes round-trip; the
    ///   single all-zero `LX([0; 16])` value saturates *up* to the
    ///   lex-min valid `ID`. R-Galois holds at this boundary;
    ///   L-Galois does not — that's why this is a `conn_r!`, not
    ///   an `iso!`.
    pub HLIDLX16 : ID => LX<16> {
        inner: lx16_to_id,
        floor: id_to_lx16,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::prop::conn as conn_laws;
    use core::num::NonZeroU128;
    use proptest::prelude::*;

    // `ID` doesn't derive `Debug`, so proptest strategies can't
    // yield `ID` directly. Generate non-zero `u128` and construct
    // `ID` in the body.

    fn arb_lx16() -> impl Strategy<Value = LX<16>> {
        prop_oneof![
            Just(LX([0u8; 16])),
            Just(LX([0xFFu8; 16])),
            any::<[u8; 16]>().prop_map(LX),
        ]
    }

    fn arb_nonpuncture_lx16() -> impl Strategy<Value = LX<16>> {
        any::<[u8; 16]>()
            .prop_filter("non-zero bytes", |b| *b != [0u8; 16])
            .prop_map(LX)
    }

    fn arb_nz_u128() -> impl Strategy<Value = NonZeroU128> {
        prop_oneof![
            Just(NonZeroU128::new(1).unwrap()),
            Just(NonZeroU128::MAX),
            any::<u128>().prop_filter_map("non-zero u128", NonZeroU128::new),
        ]
    }

    proptest! {
        #[test]
        fn galois_r(a in arb_nz_u128(), b in arb_lx16()) {
            let id = ID::from(a);
            prop_assert!(conn_laws::galois_r(&HLIDLX16, id, b));
        }
        #[test]
        fn closure_r(a in arb_nz_u128()) {
            let id = ID::from(a);
            prop_assert!(conn_laws::closure_r(&HLIDLX16, id));
        }
        #[test]
        fn kernel_r(b in arb_lx16()) {
            prop_assert!(conn_laws::kernel_r(&HLIDLX16, b));
        }
        #[test]
        fn monotone_r(b1 in arb_lx16(), b2 in arb_lx16()) {
            prop_assert!(conn_laws::monotone_r(&HLIDLX16, b1, b2));
        }
        #[test]
        fn roundtrip_floor_nonpuncture(b in arb_nonpuncture_lx16()) {
            // floor(lower(b)) == b on non-puncture inputs.
            prop_assert_eq!(HLIDLX16.floor(HLIDLX16.lower(b)).0, b.0);
        }
    }

    /// The connection is R-only; this builds an ad-hoc L-Conn from
    /// the same `(ceil, inner)` pair and asserts the L-Galois law
    /// **fails** at the documented puncture corner. If a future
    /// `ID`-Ord change silently makes the L-law hold, this test
    /// will fail and force a revisit of the R-only choice.
    #[test]
    fn l_law_fails_at_puncture() {
        let l: crate::conn::Conn<ID, LX<16>> = crate::conn::Conn::new_l(id_to_lx16, lx16_to_id);
        let a = ID::try_from(&LEX_MIN_ID_BYTES).unwrap();
        let b = LX([0u8; 16]);
        // ceil(a) = LX([0,...,0,1]) > LX([0;16]) (lex), so LHS false.
        // inner(b) = a, so a ≤ inner(b) is true.
        assert!(!conn_laws::galois_l(&l, a, b));
    }

    /// Totality at the puncture — the saturating decode lands on
    /// the lex-min valid `ID`, no panic.
    #[test]
    fn lower_total_at_puncture() {
        let z = LX([0u8; 16]);
        let id = HLIDLX16.lower(z);
        let mut expected = [0u8; 16];
        expected[15] = 1;
        assert_eq!(id.to_le_bytes(), expected);
    }

    /// Floor is lossless; round-trip via `.lower()` returns the
    /// original `ID` for every non-puncture byte string (which is
    /// every byte string that came from a real `ID`).
    #[test]
    fn floor_lower_roundtrip_spot() {
        let id = ID::from(NonZeroU128::new(0x12345678).unwrap());
        let lx = HLIDLX16.floor(id);
        assert_eq!(HLIDLX16.lower(lx).to_le_bytes(), id.to_le_bytes());
    }
}
