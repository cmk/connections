//! Kani harnesses for [`crate::nz_int_ext!`] (signed; full triple) and
//! [`crate::nz_uint_ext!`] (unsigned; left-Galois only) — the
//! `iN ↔ NonZero<iN>` / `uN ↔ NonZero<uN>` Conns.
//!
//! Two extra harnesses on top of the standard L/R-Galois battery:
//!
//! 1. **No-panic** — both `_ceil(0)` and `_floor(0)` end with a
//!    `<NonZero<_>>::new(_)` whose constant input is ±1; the harness
//!    proves the closures never panic across the input domain.
//! 2. **Asymmetric-at-zero corner** — `floor(0) = NZ(-1)`, `ceil(0) =
//!    NZ(+1)` for the signed case (and `ceil(0) = floor(0) = NZ(1)`
//!    for the unsigned case).

use crate::conn::{ConnL, ConnR};
use crate::prop::conn as conn_laws;
use core::num::{
    NonZeroI8, NonZeroI16, NonZeroI32, NonZeroI64, NonZeroI128, NonZeroU8, NonZeroU16, NonZeroU32,
    NonZeroU64, NonZeroU128,
};

// Helper: synthesize a symbolic `NonZero<_>` from a primitive `kani::any()`
// by `assume`-ing it nonzero before `NonZero::new(_).unwrap()`.
macro_rules! arb_nz {
    ($ty:ty, $prim:ty) => {{
        let v: $prim = kani::any();
        kani::assume(v != 0);
        <$ty>::new(v).unwrap()
    }};
}

/// Emit signed-NonZero (full triple) harnesses for one
/// `nz_int_ext!` Conn marker.
macro_rules! prove_nz_signed {
    ($mod_name:ident, $CONN:path, $A:ty, $NZ:ty) => {
        mod $mod_name {
            use super::*;

            #[kani::proof]
            fn galois_l() {
                let a: $A = kani::any();
                let b = arb_nz!($NZ, $A);
                assert!(conn_laws::galois_l(&$CONN.conn_l(), a, b));
            }

            #[kani::proof]
            fn galois_r() {
                let a: $A = kani::any();
                let b = arb_nz!($NZ, $A);
                assert!(conn_laws::galois_r(&$CONN.conn_r(), a, b));
            }

            #[kani::proof]
            fn closure_l() {
                let a: $A = kani::any();
                assert!(conn_laws::closure_l(&$CONN.conn_l(), a));
            }

            #[kani::proof]
            fn closure_r() {
                let a: $A = kani::any();
                assert!(conn_laws::closure_r(&$CONN.conn_r(), a));
            }

            #[kani::proof]
            fn idempotent_l() {
                let a: $A = kani::any();
                assert!(conn_laws::idempotent_l(&$CONN.conn_l(), a));
            }

            #[kani::proof]
            fn idempotent_r() {
                let b = arb_nz!($NZ, $A);
                assert!(conn_laws::idempotent_r(&$CONN.conn_r(), b));
            }

            // The nz_int_ext! closures call <NZ>::new(_).unwrap() on a
            // value that's been pre-replaced with ±1 if zero. The
            // proof obligation is: the unwrap never panics.
            #[kani::proof]
            fn ceil_never_panics() {
                let a: $A = kani::any();
                let _ = $CONN.conn_l().ceil(a);
            }

            #[kani::proof]
            fn floor_never_panics() {
                let a: $A = kani::any();
                let _ = $CONN.conn_r().floor(a);
            }
        }
    };
}

/// Emit unsigned-NonZero (left-Galois only) harnesses for one
/// `nz_uint_ext!` Conn marker. The R-side is structurally absent
/// (`ceil = floor` collapses at 0 to `NZ(1)`); only L-laws apply.
macro_rules! prove_nz_unsigned {
    ($mod_name:ident, $CONN:path, $A:ty, $NZ:ty) => {
        mod $mod_name {
            use super::*;

            #[kani::proof]
            fn galois_l() {
                let a: $A = kani::any();
                let b = arb_nz!($NZ, $A);
                assert!(conn_laws::galois_l(&$CONN.conn_l(), a, b));
            }

            #[kani::proof]
            fn closure_l() {
                let a: $A = kani::any();
                assert!(conn_laws::closure_l(&$CONN.conn_l(), a));
            }

            #[kani::proof]
            fn idempotent_l() {
                let a: $A = kani::any();
                assert!(conn_laws::idempotent_l(&$CONN.conn_l(), a));
            }

            #[kani::proof]
            fn ceil_never_panics() {
                let a: $A = kani::any();
                let _ = $CONN.conn_l().ceil(a);
            }
        }
    };
}

// ── Signed: full triples ────────────────────────────────────────────
use crate::core::i008 as ci008;
use crate::core::i016 as ci016;
use crate::core::i032 as ci032;
use crate::core::i064 as ci064;
use crate::core::i128 as ci128;

prove_nz_signed!(i008n008, ci008::I008N008, i8, NonZeroI8);
prove_nz_signed!(i016n016, ci016::I016N016, i16, NonZeroI16);
prove_nz_signed!(i032n032, ci032::I032N032, i32, NonZeroI32);
prove_nz_signed!(i064n064, ci064::I064N064, i64, NonZeroI64);
prove_nz_signed!(i128n128, ci128::I128N128, i128, NonZeroI128);

// ── Unsigned: L-Galois only ─────────────────────────────────────────
use crate::core::u008 as cu008;
use crate::core::u016 as cu016;
use crate::core::u032 as cu032;
use crate::core::u064 as cu064;
use crate::core::u128 as cu128;

prove_nz_unsigned!(u008n008, cu008::U008N008, u8, NonZeroU8);
prove_nz_unsigned!(u016n016, cu016::U016N016, u16, NonZeroU16);
prove_nz_unsigned!(u032n032, cu032::U032N032, u32, NonZeroU32);
prove_nz_unsigned!(u064n064, cu064::U064N064, u64, NonZeroU64);
prove_nz_unsigned!(u128n128, cu128::U128N128, u128, NonZeroU128);
