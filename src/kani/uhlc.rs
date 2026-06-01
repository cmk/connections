//! Kani harnesses for [`crate::uhlc::NDURU064`] (iso) and
//! [`crate::uhlc::HLIDLX16`] (right-Galois). NDURU064 gets the
//! standard iso battery; HLIDLX16 gets the R-only battery plus a
//! totality proof (`lower_never_panics`) that exercises
//! `kani::any::<[u8; 16]>()` with **no precondition** — CBMC bit-
//! blasts over the full domain and verifies the function returns
//! a value (the lex-min ID) on the all-zero puncture without
//! `unreachable!()` or `panic!()` firing.

use crate::conn::{ConnL, ConnR};
use crate::core::LX;
use crate::prop::conn as conn_laws;
use crate::uhlc::{HLIDLX16, NDURU064};
use core::num::NonZeroU128;
use uhlc::{ID, NTP64};

fn arb_id_symbolic() -> ID {
    let n: u128 = kani::any();
    kani::assume(n != 0);
    ID::from(NonZeroU128::new(n).unwrap())
}

mod ndur_u064 {
    use super::*;

    #[kani::proof]
    fn galois_l() {
        let t = NTP64(kani::any());
        let n: u64 = kani::any();
        assert!(conn_laws::galois_l(&NDURU064.conn_l(), t, n));
    }

    #[kani::proof]
    fn galois_r() {
        let t = NTP64(kani::any());
        let n: u64 = kani::any();
        assert!(conn_laws::galois_r(&NDURU064.conn_r(), t, n));
    }

    #[kani::proof]
    fn iso_roundtrip_l() {
        let t = NTP64(kani::any());
        assert!(conn_laws::iso_roundtrip_l(&NDURU064.conn_l(), t));
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
    fn galois_r() {
        let a = arb_id_symbolic();
        let bytes: [u8; 16] = kani::any();
        assert!(conn_laws::galois_r(&HLIDLX16, a, LX(bytes)));
    }

    #[kani::proof]
    fn closure_r() {
        let a = arb_id_symbolic();
        assert!(conn_laws::closure_r(&HLIDLX16, a));
    }

    #[kani::proof]
    fn kernel_r() {
        let bytes: [u8; 16] = kani::any();
        assert!(conn_laws::kernel_r(&HLIDLX16, LX(bytes)));
    }

    #[kani::proof]
    fn monotone_r() {
        let b1: [u8; 16] = kani::any();
        let b2: [u8; 16] = kani::any();
        assert!(conn_laws::monotone_r(&HLIDLX16, LX(b1), LX(b2)));
    }

    /// **Totality.** No `kani::assume` precondition — the full
    /// `[u8; 16]` domain, including the all-zero puncture, must
    /// produce a value (the lex-min ID at the puncture) without
    /// `unreachable!()` or `panic!()` firing.
    #[kani::proof]
    fn lower_never_panics() {
        let bytes: [u8; 16] = kani::any();
        let _ = crate::conn::lower(&HLIDLX16, LX(bytes));
    }
}
