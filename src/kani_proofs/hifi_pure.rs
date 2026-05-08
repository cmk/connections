//! Conn-level Galois-law harnesses for the pure-arithmetic hifi-domain
//! Conns — Tier 1 of Plan 43.
//!
//! In scope:
//! - `HDURNANO` (`conn_l!`) — `Extended<HD> → i128` total nanoseconds.
//! - `HDURSECS` (`conn_l!`) — `Extended<HD> → i64` whole seconds.
//! - `ETAINANO` (`conn_l!`) — `Extended<Epoch> → i128` TAI nanoseconds.
//! - `ETAIHDUR` (`iso!`) — `Epoch ↔ HD` TAI-scale projection.
//!
//! Out of scope (leap-second / UTC-scale internals): `EUNXNANO`,
//! `EUTCHDUR`, `F064ETAI` Conn-level laws, `F064EUNX`. See plan
//! §Tier 2.
//!
//! All `Extended<_>` sources use the same 3-way `kani::any::<u8>()`
//! discriminator pattern as `crate::kani_proofs::ext_int`.

#![allow(unused_imports)]

use crate::conn::{ConnL, ConnR};
use crate::extended::Extended;
use crate::hifi::{ETAIHDUR, ETAINANO, HDURNANO, HDURSECS};
use crate::prop::conn as conn_laws;
use hifitime::{Duration as HD, Epoch};

// ── Symbolic-input helpers ──────────────────────────────────────────

fn arb_hd() -> HD {
    let total_ns: i128 = kani::any();
    let max = HD::MAX.total_nanoseconds();
    let min = HD::MIN.total_nanoseconds();
    kani::assume(total_ns >= min && total_ns <= max);
    HD::from_total_nanoseconds(total_ns)
}

fn arb_ext_hd() -> Extended<HD> {
    let tag: u8 = kani::any();
    match tag % 3 {
        0 => Extended::NegInf,
        1 => Extended::Finite(arb_hd()),
        _ => Extended::PosInf,
    }
}

fn arb_epoch() -> Epoch {
    Epoch::from_tai_duration(arb_hd())
}

fn arb_ext_epoch() -> Extended<Epoch> {
    let tag: u8 = kani::any();
    match tag % 3 {
        0 => Extended::NegInf,
        1 => Extended::Finite(arb_epoch()),
        _ => Extended::PosInf,
    }
}

fn arb_i64() -> i64 {
    kani::any()
}

fn arb_i128() -> i128 {
    kani::any()
}

// ── L-only battery ──────────────────────────────────────────────────

macro_rules! prove_l {
    ($mod_name:ident, $C:expr, $arb_a:ident, $arb_b:ident) => {
        mod $mod_name {
            use super::*;

            #[kani::proof]
            fn galois_l() {
                let a = $arb_a();
                let b = $arb_b();
                assert!(conn_laws::galois_l(&$C, a, b));
            }

            #[kani::proof]
            fn monotone_l() {
                let a1 = $arb_a();
                let a2 = $arb_a();
                assert!(conn_laws::monotone_l(&$C, a1, a2));
            }

            #[kani::proof]
            fn closure_l() {
                let a = $arb_a();
                assert!(conn_laws::closure_l(&$C, a));
            }

            #[kani::proof]
            fn kernel_l() {
                let b = $arb_b();
                assert!(conn_laws::kernel_l(&$C, b));
            }

            #[kani::proof]
            fn idempotent_l() {
                let a = $arb_a();
                assert!(conn_laws::idempotent_l(&$C, a));
            }
        }
    };
}

// ── Iso battery (full triple + iso_roundtrip_l + roundtrip_ceil) ───

macro_rules! prove_iso {
    ($mod_name:ident, $L:expr, $R:expr, $arb_a:ident, $arb_b:ident) => {
        mod $mod_name {
            use super::*;

            #[kani::proof]
            fn galois_l() {
                let a = $arb_a();
                let b = $arb_b();
                assert!(conn_laws::galois_l(&$L, a, b));
            }

            #[kani::proof]
            fn galois_r() {
                let a = $arb_a();
                let b = $arb_b();
                assert!(conn_laws::galois_r(&$R, a, b));
            }

            #[kani::proof]
            fn monotone_l() {
                let a1 = $arb_a();
                let a2 = $arb_a();
                assert!(conn_laws::monotone_l(&$L, a1, a2));
            }

            #[kani::proof]
            fn closure_l() {
                let a = $arb_a();
                assert!(conn_laws::closure_l(&$L, a));
            }

            #[kani::proof]
            fn kernel_l() {
                let b = $arb_b();
                assert!(conn_laws::kernel_l(&$L, b));
            }

            #[kani::proof]
            fn idempotent_l() {
                let a = $arb_a();
                assert!(conn_laws::idempotent_l(&$L, a));
            }

            // Iso-specific: forward round-trip is exact in both
            // directions (no information lost on either side).
            #[kani::proof]
            fn iso_roundtrip_l() {
                let a = $arb_a();
                assert!(conn_laws::iso_roundtrip_l(&$L, a));
            }

            #[kani::proof]
            fn roundtrip_ceil() {
                let b = $arb_b();
                assert!(conn_laws::roundtrip_ceil(&$L, b));
            }
        }
    };
}

// ── HDURNANO / HDURSECS / ETAINANO — `conn_l!` ──────────────────────

prove_l!(hdurnano, HDURNANO, arb_ext_hd, arb_i128);
prove_l!(hdursecs, HDURSECS, arb_ext_hd, arb_i64);
prove_l!(etainano, ETAINANO, arb_ext_epoch, arb_i128);

// ── ETAIHDUR — `iso!` (degenerate ConnK, lossless bijection) ───────

prove_iso!(
    etaihdur,
    ETAIHDUR.conn_l(),
    ETAIHDUR.conn_r(),
    arb_epoch,
    arb_hd
);
