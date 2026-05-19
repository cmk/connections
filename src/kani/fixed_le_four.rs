//! Kani harnesses for 4-byte little-endian byte-encoding isos.

use crate::conn::{ConnL, ConnR};
use crate::core::{L2, LE};
use crate::prop::conn as conn_laws;

macro_rules! prove_iso_le {
    ($mod_name:ident, $CONN:path, $T:ty) => {
        mod $mod_name {
            use super::*;

            #[kani::proof]
            fn galois_l() {
                let a: $T = kani::any();
                let b = LE(kani::any::<[u8; 4]>());
                assert!(conn_laws::galois_l(&$CONN.conn_l(), a, b));
            }

            #[kani::proof]
            fn galois_r() {
                let a: $T = kani::any();
                let b = LE(kani::any::<[u8; 4]>());
                assert!(conn_laws::galois_r(&$CONN.conn_r(), a, b));
            }

            #[kani::proof]
            fn iso_roundtrip_l() {
                let a: $T = kani::any();
                assert!(conn_laws::iso_roundtrip_l(&$CONN.conn_l(), a));
            }

            #[kani::proof]
            fn roundtrip_ceil() {
                let b = LE(kani::any::<[u8; 4]>());
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

macro_rules! prove_iso_l2 {
    ($mod_name:ident, $CONN:path, $T:ty) => {
        mod $mod_name {
            use super::*;

            #[kani::proof]
            fn galois_l() {
                let a: $T = kani::any();
                let b = L2(kani::any::<[u8; 4]>());
                assert!(conn_laws::galois_l(&$CONN.conn_l(), a, b));
            }

            #[kani::proof]
            fn galois_r() {
                let a: $T = kani::any();
                let b = L2(kani::any::<[u8; 4]>());
                assert!(conn_laws::galois_r(&$CONN.conn_r(), a, b));
            }

            #[kani::proof]
            fn iso_roundtrip_l() {
                let a: $T = kani::any();
                assert!(conn_laws::iso_roundtrip_l(&$CONN.conn_l(), a));
            }

            #[kani::proof]
            fn roundtrip_ceil() {
                let b = L2(kani::any::<[u8; 4]>());
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

prove_iso_le!(u032_le, crate::core::u032::U032LE04, u32);
prove_iso_l2!(i032_le, crate::core::i032::I032LE04, i32);
