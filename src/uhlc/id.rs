//! `Option<ID> ↔ LX<16>` iso. `ID` is a 16-byte LE-stored token whose
//! derived `Ord` is byte-lex from byte 0 of `to_le_bytes()` (i.e.,
//! **LSB-first** under LE storage); [`LX<16>`](crate::core::LX) is the
//! identity byte-wrapper with the same derived `Ord`. `ID`'s
//! construction enforces a non-zero `u128` invariant
//! (`uhlc-rs/src/id.rs:127-129`), so `None` represents the single
//! all-zero puncture and `Some(ID)` represents every non-zero byte
//! string.

use uhlc::ID;

use crate::core::LX;

fn opt_id_to_lx16(id: Option<ID>) -> LX<16> {
    match id {
        None => LX([0u8; 16]),
        Some(id) => LX(id.to_le_bytes()),
    }
}

fn lx16_to_opt_id(lx: LX<16>) -> Option<ID> {
    ID::try_from(&lx.0).ok()
}

crate::iso! {
    /// `Option<ID> ↔ LX<16>` — `None` is the all-zero puncture;
    /// `Some(ID)` is the lossless non-zero byte representation.
    ///
    /// - `floor(&HLIDLX16, None)` and `ceil(&HLIDLX16, None)` both return
    ///   `LX([0; 16])`.
    /// - `lower(&HLIDLX16, LX([0; 16]))` and
    ///   `upper(&HLIDLX16, LX([0; 16]))` both return `None`.
    /// - Every non-zero byte string decodes to `Some(ID)` and round-trips
    ///   exactly.
    pub HLIDLX16 : Option<ID> => LX<16> {
        forward: opt_id_to_lx16,
        back:    lx16_to_opt_id,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::conn::{ConnL, ConnR};
    use crate::prop::conn as conn_laws;
    use core::num::NonZeroU128;
    use proptest::prelude::*;

    // `ID` doesn't derive `Debug`, so proptest strategies can't yield
    // `Option<ID>` directly. Generate `Option<NonZeroU128>` and construct
    // `ID` in the body.

    fn arb_lx16() -> impl Strategy<Value = LX<16>> {
        prop_oneof![
            Just(LX([0u8; 16])),
            Just(LX([0xFFu8; 16])),
            any::<[u8; 16]>().prop_map(LX),
        ]
    }

    fn arb_opt_nz_u128() -> impl Strategy<Value = Option<NonZeroU128>> {
        prop_oneof![
            Just(None),
            Just(Some(NonZeroU128::new(1).unwrap())),
            Just(Some(NonZeroU128::MAX)),
            any::<u128>().prop_map(NonZeroU128::new),
        ]
    }

    proptest! {
        #[test]
        fn iso_roundtrip_l(a in arb_opt_nz_u128()) {
            let id = a.map(ID::from);
            prop_assert!(conn_laws::iso_roundtrip_l(&HLIDLX16.conn_l(), id));
        }
        #[test]
        fn roundtrip_ceil(b in arb_lx16()) {
            prop_assert!(conn_laws::roundtrip_ceil(&HLIDLX16.conn_l(), b));
        }
        #[test]
        fn galois_l(a in arb_opt_nz_u128(), b in arb_lx16()) {
            let id = a.map(ID::from);
            prop_assert!(conn_laws::galois_l(&HLIDLX16.conn_l(), id, b));
        }
        #[test]
        fn galois_r(a in arb_opt_nz_u128(), b in arb_lx16()) {
            let id = a.map(ID::from);
            prop_assert!(conn_laws::galois_r(&HLIDLX16.conn_r(), id, b));
        }
        #[test]
        fn floor_le_ceil(a in arb_opt_nz_u128()) {
            let id = a.map(ID::from);
            prop_assert!(conn_laws::floor_le_ceil(&HLIDLX16, id));
        }
        #[test]
        fn order_reflecting(b1 in arb_lx16(), b2 in arb_lx16()) {
            prop_assert!(conn_laws::order_reflecting(&HLIDLX16, b1, b2));
        }
    }

    #[test]
    fn puncture_is_none() {
        let z = LX([0u8; 16]);
        assert!(crate::conn::lower(&HLIDLX16, z).is_none());
        assert_eq!(crate::conn::floor(&HLIDLX16, None), z);
    }

    #[test]
    fn nonzero_bytes_roundtrip_as_some_id() {
        let mut bytes = [0u8; 16];
        bytes[7] = 42;
        let lx = LX(bytes);
        let id = crate::conn::lower(&HLIDLX16, lx).unwrap();

        assert_eq!(id.to_le_bytes(), bytes);
        assert_eq!(crate::conn::floor(&HLIDLX16, Some(id)).0, bytes);
    }
}
