//! Kani harnesses for `fixed::u16` / `fixed::i16` — 2-byte sortable byte-encoding isos.
//!
//! `U016BE02`, `I016BE02`. (`F016BE02` deferred — see `src/fixed.rs`.)
//!
//! T0 (full domain). Symbolic input is at most 32 bits (a u16 + a
//! [u8; 2]); CBMC handles this within seconds.

use crate::conn::{ConnL, ConnR};
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
                let host_ord = a.cmp(&b);
                let byte_ord = $CONN.ceil(a).cmp(&$CONN.ceil(b));
                assert!(host_ord == byte_ord);
            }
        }
    };
}

prove_iso_be!(u016_be, crate::fixed::u16::U016BE02, u16);
prove_iso_be!(i016_be, crate::fixed::i16::I016BE02, i16);
