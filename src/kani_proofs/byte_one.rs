//! Kani harnesses for [`crate::byte::one`] — 1-byte sortable byte-encoding isos.
//!
//! Two `prove_iso!` invocations (`U008OBYT`, `I008OBYT`) plus
//! `prove_conn_l_with_order!` for `BOOLOBYT` (one-sided). Each
//! macro emits the standard ConnL battery + the new
//! `order_preserving` predicate (host order vs byte-lex order).
//!
//! All harnesses are T0 (full domain). Symbolic input is at most
//! 16 bits (a u8 + a [u8; 1]); CBMC handles this trivially.

use crate::conn::{ConnL, ConnR};
use crate::prop::conn as conn_laws;

macro_rules! prove_iso_obyt {
    ($mod_name:ident, $CONN:path, $T:ty) => {
        mod $mod_name {
            use super::*;

            #[kani::proof]
            fn galois_l() {
                let a: $T = kani::any();
                let b: [u8; 1] = kani::any();
                assert!(conn_laws::galois_l(&$CONN.conn_l(), a, b));
            }

            #[kani::proof]
            fn galois_r() {
                let a: $T = kani::any();
                let b: [u8; 1] = kani::any();
                assert!(conn_laws::galois_r(&$CONN.conn_r(), a, b));
            }

            #[kani::proof]
            fn iso_roundtrip_l() {
                let a: $T = kani::any();
                assert!(conn_laws::iso_roundtrip_l(&$CONN.conn_l(), a));
            }

            #[kani::proof]
            fn roundtrip_ceil() {
                let b: [u8; 1] = kani::any();
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

prove_iso_obyt!(u008_obyt, crate::byte::U008OBYT, u8);
prove_iso_obyt!(i008_obyt, crate::byte::I008OBYT, i8);

// ── BOOLOBYT — one-sided conn_l, no roundtrip_ceil (lossy back) ─────

mod bool_obyt {
    use super::*;

    // Symbolic bool routed through a fully-symbolic byte so the
    // representation stays canonical (`{0, 1}`).
    fn any_bool() -> bool {
        let n: u8 = kani::any();
        n != 0
    }

    // Note: `galois_l` for `BOOLOBYT` is intentionally NOT verified by Kani.
    // Under Kani 0.67 the `(c.ceil(a) <= b) == (a <= c.upper(b))` predicate
    // — comparing a `[u8; 1]` array against a `bool` PartialOrd — produces a
    // spurious counterexample at every concrete-playback example tried
    // (`a=false, b=[0]`, `a=true, b=[255]`, …), all of which evaluate to
    // `true == true` in a hand check and pass under proptest. Reduced
    // pure-byte models of the same predicate verify cleanly, isolating the
    // failure to the `bool` PartialOrd dispatch under symbolic execution.
    // The proptest battery in `src/byte/one.rs` covers this law.

    #[kani::proof]
    fn iso_roundtrip_l() {
        // inner ∘ ceil = id holds on the host side (false → [0] → false; true → [1] → true).
        let a = any_bool();
        assert!(conn_laws::iso_roundtrip_l(&crate::byte::BOOLOBYT, a));
    }

    #[kani::proof]
    fn order_preserving() {
        let a = any_bool();
        let b = any_bool();
        let host_ord = a.cmp(&b);
        let byte_ord = crate::byte::BOOLOBYT.ceil(a).cmp(&crate::byte::BOOLOBYT.ceil(b));
        assert!(host_ord == byte_ord);
    }
}
