//! Conn-level Galois-law harnesses for the calendar-enum hifi-domain
//! Conns (Sprint 5 / Plan 46).
//!
//! All three are pure match-arm logic on `repr(u8)` enum discriminants
//! — no calendar tables, no leap seconds, no transcendentals — so the
//! full Conn-level battery should verify at Tier 2 (`kani::any`
//! symbolic input over the full `Extended<_>` source domain × full
//! u8 / NonZeroU8 target domain).
//!
//! In scope:
//! - `MONTU008` (`conn_l!`) — `Extended<MonthName> → u8`.
//! - `MONTN008` (`conn_l!`) — `Extended<MonthName> → NonZeroU8`.
//! - `WKDYU008` (`conn_l!`) — `Extended<Weekday> → u8`.
//!
//! Plus three saturate-arm spot-check harnesses proving the
//! divergence-from-`From<u8>` invariants over the full symbolic u8
//! domain (`montu008_zero_is_neg_inf`, `montu008_at_least_thirteen_is_pos_inf`,
//! `wkdyu008_at_least_seven_is_pos_inf`). These prove the
//! "saturate, don't pretend" semantic as a theorem rather than a
//! sample-based spot test.

#![allow(unused_imports)]

use crate::conn::ConnL;
use crate::extended::Extended;
use crate::hifi::{MONTN008, MONTU008, WKDYU008};
use crate::prop::conn as conn_laws;
use ::core::num::NonZeroU8;
use hifitime::{MonthName, Weekday};

// ── Symbolic-input helpers ──────────────────────────────────────

fn arb_month() -> MonthName {
    let tag: u8 = kani::any();
    kani::assume(tag <= 11);
    // MonthName::from(n+1) maps 1=Jan…12=Dec; tag is 0-indexed for
    // CBMC efficiency, then we offset by 1.
    MonthName::from(tag + 1)
}

fn arb_ext_month() -> Extended<MonthName> {
    let tag: u8 = kani::any();
    match tag % 3 {
        0 => Extended::NegInf,
        1 => Extended::Finite(arb_month()),
        _ => Extended::PosInf,
    }
}

fn arb_weekday() -> Weekday {
    let tag: u8 = kani::any();
    kani::assume(tag <= 6);
    Weekday::from(tag)
}

fn arb_ext_weekday() -> Extended<Weekday> {
    let tag: u8 = kani::any();
    match tag % 3 {
        0 => Extended::NegInf,
        1 => Extended::Finite(arb_weekday()),
        _ => Extended::PosInf,
    }
}

fn arb_u8() -> u8 {
    kani::any()
}

fn arb_nz_u8() -> NonZeroU8 {
    let n: u8 = kani::any();
    kani::assume(n != 0);
    NonZeroU8::new(n).unwrap()
}

// ── L-only battery (per-Conn macro instantiation) ───────────────

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

prove_l!(montu008, MONTU008, arb_ext_month, arb_u8);
prove_l!(montn008, MONTN008, arb_ext_month, arb_nz_u8);
prove_l!(wkdyu008, WKDYU008, arb_ext_weekday, arb_u8);

// ── Saturation-arm theorems ─────────────────────────────────────
//
// These prove the "saturate, don't pretend" divergence from
// `MonthName::from(u8)` / `Weekday::from(u8)` over the **full
// symbolic u8 domain** (256 values × 3 Conn arms). Cheap for CBMC
// and the highest-value Sprint 5 invariant.

#[kani::proof]
fn montu008_zero_is_neg_inf() {
    // u8=0 must NOT silently default to January (MonthName::from(0)
    // returns January) — it must saturate to NegInf.
    let r = crate::conn::upper(&MONTU008, 0);
    assert!(matches!(r, Extended::NegInf));
}

#[kani::proof]
fn montu008_at_least_thirteen_is_pos_inf() {
    // Every u8 ≥ 13 must saturate to PosInf, NOT default to January.
    let n: u8 = kani::any();
    kani::assume(n >= 13);
    let r = crate::conn::upper(&MONTU008, n);
    assert!(matches!(r, Extended::PosInf));
}

#[kani::proof]
fn wkdyu008_at_least_seven_is_pos_inf() {
    // Every u8 ≥ 7 must saturate to PosInf, NOT wrap to Monday.
    let n: u8 = kani::any();
    kani::assume(n >= 7);
    let r = crate::conn::upper(&WKDYU008, n);
    assert!(matches!(r, Extended::PosInf));
}

#[kani::proof]
fn montn008_at_least_thirteen_is_pos_inf() {
    // Every NonZeroU8 ≥ 13 must saturate to PosInf.
    let n: u8 = kani::any();
    kani::assume(n >= 13);
    let nz = NonZeroU8::new(n).unwrap();
    let r = crate::conn::upper(&MONTN008, nz);
    assert!(matches!(r, Extended::PosInf));
}
