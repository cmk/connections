//! Kani harnesses for 2-byte little-endian byte-encoding isos.

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
                let b = LE(kani::any::<[u8; 2]>());
                assert!(conn_laws::galois_l(&$CONN.view_l(), a, b));
            }

            #[kani::proof]
            fn galois_r() {
                let a: $T = kani::any();
                let b = LE(kani::any::<[u8; 2]>());
                assert!(conn_laws::galois_r(&$CONN.view_r(), a, b));
            }

            #[kani::proof]
            fn iso_roundtrip_l() {
                let a: $T = kani::any();
                assert!(conn_laws::iso_roundtrip_l(&$CONN.view_l(), a));
            }

            #[kani::proof]
            fn roundtrip_ceil() {
                let b = LE(kani::any::<[u8; 2]>());
                assert!(conn_laws::roundtrip_ceil(&$CONN.view_l(), b));
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
                let b = L2(kani::any::<[u8; 2]>());
                assert!(conn_laws::galois_l(&$CONN.view_l(), a, b));
            }

            #[kani::proof]
            fn galois_r() {
                let a: $T = kani::any();
                let b = L2(kani::any::<[u8; 2]>());
                assert!(conn_laws::galois_r(&$CONN.view_r(), a, b));
            }

            #[kani::proof]
            fn iso_roundtrip_l() {
                let a: $T = kani::any();
                assert!(conn_laws::iso_roundtrip_l(&$CONN.view_l(), a));
            }

            #[kani::proof]
            fn roundtrip_ceil() {
                let b = L2(kani::any::<[u8; 2]>());
                assert!(conn_laws::roundtrip_ceil(&$CONN.view_l(), b));
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

prove_iso_le!(u016_le, crate::core::u016::U016LE02, u16);
prove_iso_l2!(i016_le, crate::core::i016::I016LE02, i16);
