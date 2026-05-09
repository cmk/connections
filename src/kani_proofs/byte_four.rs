//! Kani harnesses for [`crate::byte::four`] — 4-byte sortable byte-encoding isos.
//!
//! `U032BE04`, `I032BE04`. (`F032BE04` deferred — see `src/byte.rs`.)
//! T0 (full domain). The `order_preserving` predicate uses two
//! symbolic inputs — 64 symbolic bits — comparable to the `F064F032`
//! walk-step proofs in `float_walk.rs`.

use crate::conn::{ConnL, ConnR};
use crate::prop::conn as conn_laws;

macro_rules! prove_iso_be {
    ($mod_name:ident, $CONN:path, $T:ty) => {
        mod $mod_name {
            use super::*;

            #[kani::proof]
            fn galois_l() {
                let a: $T = kani::any();
                let b: [u8; 4] = kani::any();
                assert!(conn_laws::galois_l(&$CONN.conn_l(), a, b));
            }

            #[kani::proof]
            fn galois_r() {
                let a: $T = kani::any();
                let b: [u8; 4] = kani::any();
                assert!(conn_laws::galois_r(&$CONN.conn_r(), a, b));
            }

            #[kani::proof]
            fn iso_roundtrip_l() {
                let a: $T = kani::any();
                assert!(conn_laws::iso_roundtrip_l(&$CONN.conn_l(), a));
            }

            #[kani::proof]
            fn roundtrip_ceil() {
                let b: [u8; 4] = kani::any();
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

prove_iso_be!(u032_be, crate::byte::U032BE04, u32);
prove_iso_be!(i032_be, crate::byte::I032BE04, i32);

// `F032BE04` deferred — see `src/byte.rs` for the NaN/PartialOrd rationale.
