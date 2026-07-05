//! Kani harnesses for [`crate::uhlc::NDURU064`] and
//! [`crate::uhlc::HLIDLX16`], both iso Conns. HLIDLX16 proves the
//! all-zero puncture is represented by `None`, while every non-zero
//! byte string round-trips through `Some(ID)`.

use crate::conn::{ConnL, ConnR};
use crate::core::LX;
use crate::prop::conn as conn_laws;
use crate::uhlc::{HLIDLX16, NDURU064};
use core::num::NonZeroU128;
use uhlc::{ID, NTP64};

fn arb_opt_id_symbolic() -> Option<ID> {
    NonZeroU128::new(kani::any()).map(ID::from)
}

mod ndur_u064 {
    use super::*;

    #[kani::proof]
    fn galois_l() {
        let t = NTP64(kani::any());
        let n: u64 = kani::any();
        assert!(conn_laws::galois_l(&NDURU064.view_l(), t, n));
    }

    #[kani::proof]
    fn galois_r() {
        let t = NTP64(kani::any());
        let n: u64 = kani::any();
        assert!(conn_laws::galois_r(&NDURU064.view_r(), t, n));
    }

    #[kani::proof]
    fn iso_roundtrip_l() {
        let t = NTP64(kani::any());
        assert!(conn_laws::iso_roundtrip_l(&NDURU064.view_l(), t));
    }

    #[kani::proof]
    fn floor_le_ceil() {
        let t = NTP64(kani::any());
        assert!(conn_laws::floor_le_ceil(&NDURU064, t));
    }
}

mod hlid_lx16 {
    use super::*;

    #[kani::proof]
    fn galois_l() {
        let a = arb_opt_id_symbolic();
        let bytes: [u8; 16] = kani::any();
        assert!(conn_laws::galois_l(&HLIDLX16.view_l(), a, LX(bytes)));
    }

    #[kani::proof]
    fn galois_r() {
        let a = arb_opt_id_symbolic();
        let bytes: [u8; 16] = kani::any();
        assert!(conn_laws::galois_r(&HLIDLX16.view_r(), a, LX(bytes)));
    }

    #[kani::proof]
    fn iso_roundtrip_l() {
        let a = arb_opt_id_symbolic();
        assert!(conn_laws::iso_roundtrip_l(&HLIDLX16.view_l(), a));
    }

    #[kani::proof]
    fn roundtrip_ceil() {
        let bytes: [u8; 16] = kani::any();
        assert!(conn_laws::roundtrip_ceil(&HLIDLX16.view_l(), LX(bytes)));
    }

    #[kani::proof]
    fn floor_le_ceil() {
        let a = arb_opt_id_symbolic();
        assert!(conn_laws::floor_le_ceil(&HLIDLX16, a));
    }
}
