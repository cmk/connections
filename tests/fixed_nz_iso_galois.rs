//! Galois-law proptest battery for the NonZero (`I###N###`,
//! `U###N###`) and cross-crate iso (`Q000I###`, `Q000U###`) Conn
//! families across all per-host-type widths except i8/u8 (whose
//! representative spot+proptest coverage lives inline in
//! `src/fixed/i8.rs` and `src/fixed/u8.rs`).
//!
//! The macros `nz_int_ext!` / `nz_uint_ext!` and the `Conn::new_iso`
//! based iso constructor produce structurally identical bodies at
//! every width, so a per-width parity check is cheap insurance
//! against per-file import or wiring mistakes.
//!
//! Hosting these as an integration test (rather than 8 inline
//! `proptest!` blocks across `src/fixed/{i,u}{16,32,64,128}.rs`)
//! keeps the lib-test compile time small.

use ::fixed::types::extra::U0;
use ::fixed::{FixedI16, FixedI32, FixedI64, FixedI128, FixedU16, FixedU32, FixedU64, FixedU128};
use connections::fixed;
use connections::prop::conn as conn_laws;
use core::num::{
    NonZeroI16, NonZeroI32, NonZeroI64, NonZeroI128, NonZeroU16, NonZeroU32, NonZeroU64,
    NonZeroU128,
};
use proptest::prelude::*;

// ── Signed NonZero: both Galois laws hold (asymmetric floor/ceil
//    at zero brackets the target's puncture). ─────────────────────

macro_rules! signed_nz_props {
    ($mod_name:ident, $CONN:expr, $A:ty, $NZ:ty) => {
        mod $mod_name {
            use super::*;

            fn arb_nz() -> impl Strategy<Value = $NZ> {
                any::<$A>().prop_filter_map("non-zero", <$NZ>::new)
            }

            proptest! {
                #[test]
                fn galois_l(a in any::<$A>(), b in arb_nz()) {
                    prop_assert!(conn_laws::conn_galois_l(&$CONN, a, b));
                }
                #[test]
                fn galois_r(a in any::<$A>(), b in arb_nz()) {
                    prop_assert!(conn_laws::conn_galois_r(&$CONN, a, b));
                }
                #[test]
                fn inner_then_ceil_recovers(nz in arb_nz()) {
                    prop_assert_eq!($CONN.ceil($CONN.inner(nz)), nz);
                    prop_assert_eq!($CONN.floor($CONN.inner(nz)), nz);
                }
            }
        }
    };
}

signed_nz_props!(i016n016, fixed::i16::I016N016, i16, NonZeroI16);
signed_nz_props!(i032n032, fixed::i32::I032N032, i32, NonZeroI32);
signed_nz_props!(i064n064, fixed::i64::I064N064, i64, NonZeroI64);
signed_nz_props!(i128n128, fixed::i128::I128N128, i128, NonZeroI128);

// ── Unsigned NonZero: only galois_l holds. galois_r fails at the
//    unsigned bottom plateau (no NonZero strictly below 1). ──────

macro_rules! unsigned_nz_props {
    ($mod_name:ident, $CONN:expr, $A:ty, $NZ:ty) => {
        mod $mod_name {
            use super::*;

            fn arb_nz() -> impl Strategy<Value = $NZ> {
                any::<$A>().prop_filter_map("non-zero", <$NZ>::new)
            }

            proptest! {
                #[test]
                fn galois_l(a in any::<$A>(), b in arb_nz()) {
                    prop_assert!(conn_laws::conn_galois_l(&$CONN, a, b));
                }
                #[test]
                fn inner_then_ceil_recovers(nz in arb_nz()) {
                    prop_assert_eq!($CONN.ceil($CONN.inner(nz)), nz);
                    prop_assert_eq!($CONN.floor($CONN.inner(nz)), nz);
                }
            }
        }
    };
}

unsigned_nz_props!(u016n016, fixed::u16::U016N016, u16, NonZeroU16);
unsigned_nz_props!(u032n032, fixed::u32::U032N032, u32, NonZeroU32);
unsigned_nz_props!(u064n064, fixed::u64::U064N064, u64, NonZeroU64);
unsigned_nz_props!(u128n128, fixed::u128::U128N128, u128, NonZeroU128);

// ── Cross-crate iso: both Galois laws hold (degenerate iso). ────

macro_rules! iso_props {
    ($mod_name:ident, $CONN:expr, $A:ty, $FIXED:ident) => {
        mod $mod_name {
            use super::*;

            proptest! {
                #[test]
                fn galois_l(a_bits in any::<$A>(), b in any::<$A>()) {
                    let a = $FIXED::<U0>::from_bits(a_bits);
                    prop_assert!(conn_laws::conn_galois_l(&$CONN, a, b));
                }
                #[test]
                fn galois_r(a_bits in any::<$A>(), b in any::<$A>()) {
                    let a = $FIXED::<U0>::from_bits(a_bits);
                    prop_assert!(conn_laws::conn_galois_r(&$CONN, a, b));
                }
                #[test]
                fn round_trip_both_directions(v in any::<$A>()) {
                    let q = $FIXED::<U0>::from_bits(v);
                    prop_assert_eq!($CONN.ceil($CONN.inner(v)), v);
                    prop_assert_eq!($CONN.inner($CONN.ceil(q)), q);
                }
            }
        }
    };
}

iso_props!(q000i016, fixed::i16::Q000I016, i16, FixedI16);
iso_props!(q000i032, fixed::i32::Q000I032, i32, FixedI32);
iso_props!(q000i064, fixed::i64::Q000I064, i64, FixedI64);
iso_props!(q000i128, fixed::i128::Q000I128, i128, FixedI128);
iso_props!(q000u016, fixed::u16::Q000U016, u16, FixedU16);
iso_props!(q000u032, fixed::u32::Q000U032, u32, FixedU32);
iso_props!(q000u064, fixed::u64::Q000U064, u64, FixedU64);
iso_props!(q000u128, fixed::u128::Q000U128, u128, FixedU128);
