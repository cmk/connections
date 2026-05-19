//! Kani harnesses for [`crate::uint_uint!`] (`uN → uM` widening) and
//! [`crate::int_uint!`] (`iN → uM` widening / same-width cross-sign).
//! Both are single-sided left-Galois (`pub const Conn<A, B>`) — no
//! triple, no marker struct.
//!
//! Source is a plain primitive (no `Extended<_>` wrapper); Kani's
//! `kani::any::<_>()` handles every primitive integer type natively.

use crate::prop::conn as conn_laws;

/// Five L-Galois harnesses for one `uint_uint!` or `int_uint!` Conn.
macro_rules! prove_uint_widen {
    ($mod_name:ident, $CONN:path, $A:ty, $B:ty) => {
        mod $mod_name {
            use super::*;

            #[kani::proof]
            fn galois_l() {
                let a: $A = kani::any();
                let b: $B = kani::any();
                assert!(conn_laws::galois_l(&$CONN, a, b));
            }

            // `prop::conn::monotone_l` is conditional; unconstrained
            // inputs are sound (see int_narrow.rs for full notes).
            #[kani::proof]
            fn monotone_l() {
                let a1: $A = kani::any();
                let a2: $A = kani::any();
                assert!(conn_laws::monotone_l(&$CONN, a1, a2));
            }

            #[kani::proof]
            fn closure_l() {
                let a: $A = kani::any();
                assert!(conn_laws::closure_l(&$CONN, a));
            }

            #[kani::proof]
            fn kernel_l() {
                let b: $B = kani::any();
                assert!(conn_laws::kernel_l(&$CONN, b));
            }

            #[kani::proof]
            fn idempotent_l() {
                let a: $A = kani::any();
                assert!(conn_laws::idempotent_l(&$CONN, a));
            }
        }
    };
}

// ── uint_uint! widenings ────────────────────────────────────────────
use crate::fixed::u016 as fu016;
use crate::fixed::u032 as fu032;
use crate::fixed::u064 as fu064;
use crate::fixed::u128 as fu128;

prove_uint_widen!(uu_u008u016, fu016::U008U016, u8, u16);
prove_uint_widen!(uu_u008u032, fu032::U008U032, u8, u32);
prove_uint_widen!(uu_u016u032, fu032::U016U032, u16, u32);
prove_uint_widen!(uu_u008u064, fu064::U008U064, u8, u64);
prove_uint_widen!(uu_u016u064, fu064::U016U064, u16, u64);
prove_uint_widen!(uu_u032u064, fu064::U032U064, u32, u64);
prove_uint_widen!(uu_u008u128, fu128::U008U128, u8, u128);
prove_uint_widen!(uu_u016u128, fu128::U016U128, u16, u128);
prove_uint_widen!(uu_u032u128, fu128::U032U128, u32, u128);
prove_uint_widen!(uu_u064u128, fu128::U064U128, u64, u128);

// ── int_uint! widenings ─────────────────────────────────────────────
use crate::fixed::u008 as fu008;

prove_uint_widen!(iu_i008u008, fu008::I008U008, i8, u8);
prove_uint_widen!(iu_i008u016, fu016::I008U016, i8, u16);
prove_uint_widen!(iu_i016u016, fu016::I016U016, i16, u16);
prove_uint_widen!(iu_i008u032, fu032::I008U032, i8, u32);
prove_uint_widen!(iu_i016u032, fu032::I016U032, i16, u32);
prove_uint_widen!(iu_i032u032, fu032::I032U032, i32, u32);
prove_uint_widen!(iu_i008u064, fu064::I008U064, i8, u64);
prove_uint_widen!(iu_i016u064, fu064::I016U064, i16, u64);
prove_uint_widen!(iu_i032u064, fu064::I032U064, i32, u64);
prove_uint_widen!(iu_i064u064, fu064::I064U064, i64, u64);
prove_uint_widen!(iu_i008u128, fu128::I008U128, i8, u128);
prove_uint_widen!(iu_i016u128, fu128::I016U128, i16, u128);
prove_uint_widen!(iu_i032u128, fu128::I032U128, i32, u128);
prove_uint_widen!(iu_i064u128, fu128::I064U128, i64, u128);
prove_uint_widen!(iu_i128u128, fu128::I128U128, i128, u128);
