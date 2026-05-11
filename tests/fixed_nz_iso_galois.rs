#![cfg(feature = "fixed")]

//! Galois-law proptest battery for the NonZero (`I###N###`,
//! `U###N###`) and cross-crate iso (`Q000I###`, `Q000U###`) Conn
//! families across all per-host-type widths except i8/u8 (whose
//! representative spot+proptest coverage lives inline in
//! `src/fixed/i008.rs` and `src/fixed/u008.rs`).
//!
//! The macros `nz_int_ext!` / `nz_uint_ext!` and the `Conn::new_iso`
//! based iso constructor produce structurally identical bodies at
//! every width, so a per-width parity check is cheap insurance
//! against per-file import or wiring mistakes.
//!
//! Hosting these as an integration test (rather than 8 inline
//! `proptest!` blocks across `src/fixed/{i,u}{16,32,64,128}.rs`)
//! keeps the lib-test compile time small.

use ::fixed::types::extra::{U0, U15, U31, U63, U127};
use ::fixed::{FixedI16, FixedI32, FixedI64, FixedI128, FixedU16, FixedU32, FixedU64, FixedU128};

use ::core::num::{
    NonZeroI16, NonZeroI32, NonZeroI64, NonZeroI128, NonZeroU16, NonZeroU32, NonZeroU64,
    NonZeroU128,
};
use connections::conn::{ConnL, ConnR};
use connections::prop::conn as conn_laws;
use connections::{core, fixed};
use proptest::prelude::*;

// ── Signed NonZero: both Galois laws hold (asymmetric floor/ceil
//    at zero brackets the target's puncture). ─────────────────────

macro_rules! signed_nz_props {
    ($mod_name:ident, $CONN:path, $A:ty, $NZ:ty) => {
        mod $mod_name {
            use super::*;

            fn arb_nz() -> impl Strategy<Value = $NZ> {
                any::<$A>().prop_filter_map("non-zero", <$NZ>::new)
            }

            proptest! {
                #[test]
                fn galois_l(a in any::<$A>(), b in arb_nz()) {
                    prop_assert!(conn_laws::galois_l(&$CONN.conn_l(), a, b));
                }
                #[test]
                fn galois_r(a in any::<$A>(), b in arb_nz()) {
                    prop_assert!(conn_laws::galois_r(&$CONN.conn_r(), a, b));
                }
                #[test]
                fn inner_then_ceil_recovers(nz in arb_nz()) {
                    prop_assert_eq!($CONN.ceil($CONN.upper(nz)), nz);
                    prop_assert_eq!($CONN.floor($CONN.upper(nz)), nz);
                }
            }
        }
    };
}

signed_nz_props!(i016n016, core::i016::I016N016, i16, NonZeroI16);
signed_nz_props!(i032n032, core::i032::I032N032, i32, NonZeroI32);
signed_nz_props!(i064n064, core::i064::I064N064, i64, NonZeroI64);
signed_nz_props!(i128n128, core::i128::I128N128, i128, NonZeroI128);

// ── Unsigned NonZero: only galois_l holds. galois_r fails at the
//    unsigned bottom plateau (no NonZero strictly below 1). ──────

macro_rules! unsigned_nz_props {
    ($mod_name:ident, $CONN:path, $A:ty, $NZ:ty) => {
        mod $mod_name {
            use super::*;

            fn arb_nz() -> impl Strategy<Value = $NZ> {
                any::<$A>().prop_filter_map("non-zero", <$NZ>::new)
            }

            proptest! {
                #[test]
                fn galois_l(a in any::<$A>(), b in arb_nz()) {
                    prop_assert!(conn_laws::galois_l(&$CONN.conn_l(), a, b));
                }
                #[test]
                fn inner_then_ceil_recovers(nz in arb_nz()) {
                    prop_assert_eq!($CONN.ceil($CONN.upper(nz)), nz);
                }
            }
        }
    };
}

unsigned_nz_props!(u016n016, core::u016::U016N016, u16, NonZeroU16);
unsigned_nz_props!(u032n032, core::u032::U032N032, u32, NonZeroU32);
unsigned_nz_props!(u064n064, core::u064::U064N064, u64, NonZeroU64);
unsigned_nz_props!(u128n128, core::u128::U128N128, u128, NonZeroU128);

// ── Cross-crate iso: both Galois laws hold (degenerate iso). ────

macro_rules! iso_props {
    ($mod_name:ident, $CONN:path, $A:ty, $FIXED:ident, $FRAC:ty) => {
        mod $mod_name {
            use super::*;

            proptest! {
                #[test]
                fn galois_l(a_bits in any::<$A>(), b in any::<$A>()) {
                    let a = $FIXED::<$FRAC>::from_bits(a_bits);
                    prop_assert!(conn_laws::galois_l(&$CONN.conn_l(), a, b));
                }
                #[test]
                fn galois_r(a_bits in any::<$A>(), b in any::<$A>()) {
                    let a = $FIXED::<$FRAC>::from_bits(a_bits);
                    prop_assert!(conn_laws::galois_r(&$CONN.conn_r(), a, b));
                }
                #[test]
                fn round_trip_both_directions(v in any::<$A>()) {
                    let q = $FIXED::<$FRAC>::from_bits(v);
                    prop_assert_eq!($CONN.upper($CONN.ceil(q)), q);
                    prop_assert_eq!($CONN.ceil($CONN.upper(v)), v);
                    prop_assert_eq!($CONN.lower($CONN.floor(q)), q);
                    prop_assert_eq!($CONN.floor($CONN.lower(v)), v);
                }
            }
        }
    };
}

iso_props!(q000i016, fixed::i016::Q000I016, i16, FixedI16, U0);
iso_props!(q000i032, fixed::i032::Q000I032, i32, FixedI32, U0);
iso_props!(q000i064, fixed::i064::Q000I064, i64, FixedI64, U0);
iso_props!(q000i128, fixed::i128::Q000I128, i128, FixedI128, U0);
iso_props!(q000u016, fixed::u016::Q000U016, u16, FixedU16, U0);
iso_props!(q000u032, fixed::u032::Q000U032, u32, FixedU32, U0);
iso_props!(q000u064, fixed::u064::Q000U064, u64, FixedU64, U0);
iso_props!(q000u128, fixed::u128::Q000U128, u128, FixedU128, U0);
iso_props!(q015i016, fixed::i016::Q015I016, i16, FixedI16, U15);
iso_props!(q031i032, fixed::i032::Q031I032, i32, FixedI32, U31);
iso_props!(q063i064, fixed::i064::Q063I064, i64, FixedI64, U63);
iso_props!(q127i128, fixed::i128::Q127I128, i128, FixedI128, U127);
