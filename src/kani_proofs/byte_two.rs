//! Kani harnesses for [`crate::byte::two`] — 2-byte sortable byte-encoding isos.
//!
//! `U016OBYT`, `I016OBYT`. (`F016OBYT` is gated on the separate `f16`
//! cargo feature and would only run on a nightly toolchain — covered
//! by proptest unconditionally; not added to the Kani battery here.)
//!
//! T0 (full domain). Symbolic input is at most 32 bits (a u16 + a
//! [u8; 2]); CBMC handles this within seconds.

use crate::conn::{ConnL, ConnR};
use crate::prop::conn as conn_laws;

macro_rules! prove_iso_obyt {
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

prove_iso_obyt!(u016_obyt, crate::byte::U016OBYT, u16);
prove_iso_obyt!(i016_obyt, crate::byte::I016OBYT, i16);
