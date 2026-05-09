//! Kani harnesses for 1-byte sortable big-endian byte encodings.

use crate::conn::{ConnL, ConnR};
use crate::prop::conn as conn_laws;

macro_rules! prove_iso_be {
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
                assert!(a.cmp(&b) == $CONN.ceil(a).cmp(&$CONN.ceil(b)));
            }
        }
    };
}

prove_iso_be!(u008_be, crate::fixed::u008::U008BE01, u8);
prove_iso_be!(i008_be, crate::fixed::i008::I008BE01, i8);

mod bool_be {
    use super::*;

    fn any_bool() -> bool {
        let n: u8 = kani::any();
        n != 0
    }

    #[kani::proof]
    fn host_roundtrip_l() {
        let a = any_bool();
        assert!(conn_laws::iso_roundtrip_l(&crate::fixed::u008::BOOLBE01, a));
    }

    #[kani::proof]
    fn order_preserving() {
        let a = any_bool();
        let b = any_bool();
        assert!(
            a.cmp(&b)
                == crate::fixed::u008::BOOLBE01
                    .ceil(a)
                    .cmp(&crate::fixed::u008::BOOLBE01.ceil(b))
        );
    }
}
