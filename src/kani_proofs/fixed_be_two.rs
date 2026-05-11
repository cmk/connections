//! Kani harnesses for 2-byte big-endian byte encodings.

use crate::conn::{ConnL, ConnR};
use crate::core::B2;
use crate::prop::conn as conn_laws;

macro_rules! prove_iso_be {
    ($mod_name:ident, $CONN:path, $T:ty) => {
        mod $mod_name {
            use super::*;

            #[kani::proof]
            fn galois_l() {
                let a: $T = kani::any();
                let b: [u8; 2] = kani::any();
                assert!(conn_laws::galois_l(&$CONN.conn_l(), a, b));
            }

            #[kani::proof]
            fn galois_r() {
                let a: $T = kani::any();
                let b: [u8; 2] = kani::any();
                assert!(conn_laws::galois_r(&$CONN.conn_r(), a, b));
            }

            #[kani::proof]
            fn iso_roundtrip_l() {
                let a: $T = kani::any();
                assert!(conn_laws::iso_roundtrip_l(&$CONN.conn_l(), a));
            }

            #[kani::proof]
            fn roundtrip_ceil() {
                let b: [u8; 2] = kani::any();
                assert!(conn_laws::roundtrip_ceil(&$CONN.conn_l(), b));
            }

            #[kani::proof]
            fn floor_le_ceil() {
                let a: $T = kani::any();
                assert!(conn_laws::floor_le_ceil(&$CONN, a));
            }

            #[kani::proof]
            fn order_preserving() {
                let a: $T = kani::any();
                let b: $T = kani::any();
                assert!(a.cmp(&b) == $CONN.ceil(a).cmp(&$CONN.ceil(b)));
            }
        }
    };
}

macro_rules! prove_iso_b2 {
    ($mod_name:ident, $CONN:path, $T:ty) => {
        mod $mod_name {
            use super::*;

            #[kani::proof]
            fn galois_l() {
                let a: $T = kani::any();
                let b = B2(kani::any::<[u8; 2]>());
                assert!(conn_laws::galois_l(&$CONN.conn_l(), a, b));
            }

            #[kani::proof]
            fn galois_r() {
                let a: $T = kani::any();
                let b = B2(kani::any::<[u8; 2]>());
                assert!(conn_laws::galois_r(&$CONN.conn_r(), a, b));
            }

            #[kani::proof]
            fn iso_roundtrip_l() {
                let a: $T = kani::any();
                assert!(conn_laws::iso_roundtrip_l(&$CONN.conn_l(), a));
            }

            #[kani::proof]
            fn roundtrip_ceil() {
                let b = B2(kani::any::<[u8; 2]>());
                assert!(conn_laws::roundtrip_ceil(&$CONN.conn_l(), b));
            }

            #[kani::proof]
            fn floor_le_ceil() {
                let a: $T = kani::any();
                assert!(conn_laws::floor_le_ceil(&$CONN, a));
            }

            #[kani::proof]
            fn order_preserving() {
                let a: $T = kani::any();
                let b: $T = kani::any();
                assert!(a.cmp(&b) == $CONN.ceil(a).cmp(&$CONN.ceil(b)));
            }
        }
    };
}

prove_iso_be!(u016_be, crate::core::u016::U016BE02, u16);
prove_iso_b2!(i016_be, crate::core::i016::I016BE02, i16);
