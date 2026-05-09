//! Kani harnesses for 1-byte sortable little-endian byte encodings.

use crate::conn::{ConnL, ConnR};
use crate::fixed::LE;
use crate::prop::conn as conn_laws;

macro_rules! prove_iso_le {
    ($mod_name:ident, $CONN:path, $T:ty) => {
        mod $mod_name {
            use super::*;

            #[kani::proof]
            fn galois_l() {
                let a: $T = kani::any();
                let b = LE(kani::any::<[u8; 1]>());
                assert!(conn_laws::galois_l(&$CONN.conn_l(), a, b));
            }

            #[kani::proof]
            fn galois_r() {
                let a: $T = kani::any();
                let b = LE(kani::any::<[u8; 1]>());
                assert!(conn_laws::galois_r(&$CONN.conn_r(), a, b));
            }

            #[kani::proof]
            fn iso_roundtrip_l() {
                let a: $T = kani::any();
                assert!(conn_laws::iso_roundtrip_l(&$CONN.conn_l(), a));
            }

            #[kani::proof]
            fn roundtrip_ceil() {
                let b = LE(kani::any::<[u8; 1]>());
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

prove_iso_le!(u008_le, crate::fixed::u008::U008LE01, u8);
prove_iso_le!(i008_le, crate::fixed::i008::I008LE01, i8);

mod bool_le {
    use super::*;

    fn any_bool() -> bool {
        let n: u8 = kani::any();
        n != 0
    }

    #[kani::proof]
    fn host_roundtrip_l() {
        let a = any_bool();
        assert!(conn_laws::iso_roundtrip_l(&crate::fixed::u008::BOOLLE01, a));
    }

    #[kani::proof]
    fn order_preserving() {
        let a = any_bool();
        let b = any_bool();
        assert!(
            a.cmp(&b)
                == crate::fixed::u008::BOOLLE01
                    .ceil(a)
                    .cmp(&crate::fixed::u008::BOOLLE01.ceil(b))
        );
    }
}
