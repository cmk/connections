//! Conn-level Galois-law harnesses for the pure-arithmetic time-domain
//! Conns — the Tier 1 contribution of Plan 43.
//!
//! In scope:
//! - `TIMENANO` (`conn_l!`) — `Extended<Time> → i64` nanoseconds since midnight.
//! - `TIMESECS` (`conn_l!`) — `Extended<Time> → i64` whole seconds.
//! - `TDURSECS` (`conn_k!`) — `Duration → Extended<i64>` whole seconds (full triple).
//! - `SDURU064` (`conn_l!`) — `Extended<StdDuration> → Extended<u64>` whole seconds.
//! - `SDURU128` (`conn_l!`) — `Extended<StdDuration> → Extended<u128>` total nanoseconds.
//!
//! Out of scope (calendar / leap-second internals): `DATEJDAY`,
//! `PDTMDATE`, `ODTMNANO`, `ODTMSECS`. See plan §Tier 2.
//!
//! Source-side `Extended<T>` values are constructed via a 3-way
//! discriminator on a `kani::any::<u8>()` tag (same shape as
//! `arb_ext!` in `crate::kani::ext_int`). Concrete `T` values
//! (`Time`, `Duration`, `StdDuration`) are built from canonical
//! integer storage via `kani::any` so the entire reachable state
//! space is symbolic.

#![allow(unused_imports)]

use crate::conn::{ConnL, ConnR};
use crate::extended::Extended;
use crate::prop::conn as conn_laws;
use crate::time::{SDURU064, SDURU128, TDURSECS, TIMENANO, TIMESECS};
use std::time::Duration as StdDuration;
use time::{Duration, Time};

// ── Symbolic-input helpers ──────────────────────────────────────────

fn arb_time() -> Time {
    let total_ns: u64 = kani::any();
    kani::assume(total_ns < 86_400 * 1_000_000_000);
    let h = (total_ns / (3_600 * 1_000_000_000)) as u8;
    let m = ((total_ns / (60 * 1_000_000_000)) % 60) as u8;
    let s = ((total_ns / 1_000_000_000) % 60) as u8;
    let ns = (total_ns % 1_000_000_000) as u32;
    Time::from_hms_nano(h, m, s, ns).expect("validated by construction")
}

fn arb_ext_time() -> Extended<Time> {
    let tag: u8 = kani::any();
    match tag % 3 {
        0 => Extended::NegInf,
        1 => Extended::Finite(arb_time()),
        _ => Extended::PosInf,
    }
}

fn arb_duration() -> Duration {
    // Build via i128 total_nanoseconds in Duration's exact range so
    // (secs, subsec) are sign-coherent (mirrors `shift_duration` in
    // `time::duration`).
    let total_ns: i128 = kani::any();
    let max = Duration::MAX.whole_nanoseconds();
    let min = Duration::MIN.whole_nanoseconds();
    kani::assume(total_ns >= min && total_ns <= max);
    let secs = (total_ns / 1_000_000_000) as i64;
    let subsec = (total_ns % 1_000_000_000) as i32;
    Duration::new(secs, subsec)
}

fn arb_std_duration() -> StdDuration {
    let total_ns: u128 = kani::any();
    let max = StdDuration::MAX.as_nanos();
    kani::assume(total_ns <= max);
    let secs = (total_ns / 1_000_000_000) as u64;
    let subsec = (total_ns % 1_000_000_000) as u32;
    StdDuration::new(secs, subsec)
}

fn arb_ext_std_duration() -> Extended<StdDuration> {
    let tag: u8 = kani::any();
    match tag % 3 {
        0 => Extended::NegInf,
        1 => Extended::Finite(arb_std_duration()),
        _ => Extended::PosInf,
    }
}

fn arb_i64() -> i64 {
    kani::any()
}

fn arb_ext_i64() -> Extended<i64> {
    let tag: u8 = kani::any();
    let v: i64 = kani::any();
    match tag % 3 {
        0 => Extended::NegInf,
        1 => Extended::Finite(v),
        _ => Extended::PosInf,
    }
}

fn arb_ext_u64() -> Extended<u64> {
    let tag: u8 = kani::any();
    let v: u64 = kani::any();
    match tag % 3 {
        0 => Extended::NegInf,
        1 => Extended::Finite(v),
        _ => Extended::PosInf,
    }
}

fn arb_ext_u128() -> Extended<u128> {
    let tag: u8 = kani::any();
    let v: u128 = kani::any();
    match tag % 3 {
        0 => Extended::NegInf,
        1 => Extended::Finite(v),
        _ => Extended::PosInf,
    }
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

// ── L+R full-triple battery ────────────────────────────────────────

macro_rules! prove_lr {
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

            #[kani::proof]
            fn galois_r() {
                let a = $arb_a();
                let b = $arb_b();
                assert!(conn_laws::galois_r(&$R, a, b));
            }

            #[kani::proof]
            fn monotone_r() {
                let b1 = $arb_b();
                let b2 = $arb_b();
                assert!(conn_laws::monotone_r(&$R, b1, b2));
            }

            #[kani::proof]
            fn closure_r() {
                let a = $arb_a();
                assert!(conn_laws::closure_r(&$R, a));
            }

            #[kani::proof]
            fn kernel_r() {
                let b = $arb_b();
                assert!(conn_laws::kernel_r(&$R, b));
            }

            #[kani::proof]
            fn idempotent_r() {
                let b = $arb_b();
                assert!(conn_laws::idempotent_r(&$R, b));
            }
        }
    };
}

// ── TIMENANO / TIMESECS — `conn_l!` markers (direct Conn values) ───

prove_l!(timenano, TIMENANO, arb_ext_time, arb_i64);
prove_l!(timesecs, TIMESECS, arb_ext_time, arb_i64);

// ── TDURSECS — full triple (`conn_k!`) ──────────────────────────────

prove_lr!(
    tdursecs,
    TDURSECS.view_l(),
    TDURSECS.view_r(),
    arb_duration,
    arb_ext_i64
);

// ── SDURU064 / SDURU128 — `conn_l!` ────────────────────────────────

prove_l!(sduru064, SDURU064, arb_ext_std_duration, arb_ext_u64);
prove_l!(sduru128, SDURU128, arb_ext_std_duration, arb_ext_u128);
