//! Kani harnesses for [`crate::ext_int!`] — `Extended<iN> → iM` /
//! `Extended<uN> → iM` widening (left-Galois single-sided per Plan 32;
//! the macro expands to a marker struct with `ConnL` only).
//!
//! Mirrors the proptest battery applied to these Conns elsewhere in
//! the crate. Source side is `Extended<$A>` (carries explicit
//! `NegInf` / `PosInf` sentinels); Kani enumerates the three variants
//! manually since `Extended<_>` doesn't implement `kani::Arbitrary`.

use crate::conn::ConnL;
use crate::extended::Extended;
use crate::prop::conn as conn_laws;

/// Symbolic `Extended<$prim>` — Kani enumerates `NegInf`, `Finite(any)`,
/// `PosInf` via a 3-way discriminator on a `kani::any::<u8>()` tag.
macro_rules! arb_ext {
    ($prim:ty) => {{
        let tag: u8 = kani::any();
        let v: $prim = kani::any();
        match tag % 3 {
            0 => Extended::NegInf,
            1 => Extended::Finite(v),
            _ => Extended::PosInf,
        }
    }};
}

/// Emit five L-Galois harnesses for one `ext_int!` Conn.
macro_rules! prove_ext_int {
    ($mod_name:ident, $CONN:path, $A:ty, $B:ty) => {
        mod $mod_name {
            use super::*;

            #[kani::proof]
            fn galois_l() {
                let a: Extended<$A> = arb_ext!($A);
                let b: $B = kani::any();
                assert!(conn_laws::galois_l(&$CONN.conn_l(), a, b));
            }

            // `prop::conn::monotone_l` returns `true` vacuously for
            // `a1 > a2`; unconstrained inputs are sound.
            #[kani::proof]
            fn monotone_l() {
                let a1: Extended<$A> = arb_ext!($A);
                let a2: Extended<$A> = arb_ext!($A);
                assert!(conn_laws::monotone_l(&$CONN.conn_l(), a1, a2));
            }

            #[kani::proof]
            fn closure_l() {
                let a: Extended<$A> = arb_ext!($A);
                assert!(conn_laws::closure_l(&$CONN.conn_l(), a));
            }

            #[kani::proof]
            fn kernel_l() {
                let b: $B = kani::any();
                assert!(conn_laws::kernel_l(&$CONN.conn_l(), b));
            }

            #[kani::proof]
            fn idempotent_l() {
                let a: Extended<$A> = arb_ext!($A);
                assert!(conn_laws::idempotent_l(&$CONN.conn_l(), a));
            }
        }
    };
}

// ── i16 destinations ────────────────────────────────────────────────
use crate::fixed::i016 as fi016;
prove_ext_int!(i008i016, fi016::I008I016, i8, i16);
prove_ext_int!(u008i016, fi016::U008I016, u8, i16);

// ── i32 destinations ────────────────────────────────────────────────
use crate::fixed::i032 as fi032;
prove_ext_int!(i008i032, fi032::I008I032, i8, i32);
prove_ext_int!(i016i032, fi032::I016I032, i16, i32);
prove_ext_int!(u008i032, fi032::U008I032, u8, i32);
prove_ext_int!(u016i032, fi032::U016I032, u16, i32);

// ── i64 destinations ────────────────────────────────────────────────
use crate::fixed::i064 as fi064;
prove_ext_int!(i008i064, fi064::I008I064, i8, i64);
prove_ext_int!(i016i064, fi064::I016I064, i16, i64);
prove_ext_int!(i032i064, fi064::I032I064, i32, i64);
prove_ext_int!(u008i064, fi064::U008I064, u8, i64);
prove_ext_int!(u016i064, fi064::U016I064, u16, i64);
prove_ext_int!(u032i064, fi064::U032I064, u32, i64);

// ── i128 destinations ───────────────────────────────────────────────
use crate::fixed::i128 as fi128;
prove_ext_int!(i008i128, fi128::I008I128, i8, i128);
prove_ext_int!(i016i128, fi128::I016I128, i16, i128);
prove_ext_int!(i032i128, fi128::I032I128, i32, i128);
prove_ext_int!(i064i128, fi128::I064I128, i64, i128);
prove_ext_int!(u008i128, fi128::U008I128, u8, i128);
prove_ext_int!(u016i128, fi128::U016I128, u16, i128);
prove_ext_int!(u032i128, fi128::U032I128, u32, i128);
prove_ext_int!(u064i128, fi128::U064I128, u64, i128);
