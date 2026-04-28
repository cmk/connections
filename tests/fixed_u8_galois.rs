//! Galois-law proptest battery for `conn::fixed::u8`.
//!
//! Hosted as an integration test (separate crate) so the main lib
//! test binary doesn't carry all 252 generated test functions for
//! this module — the unsigned binary-fixed sprint added enough new
//! tests to push the lib-test rustc invocation past CI's container
//! memory budget. Each `tests/conn_fixed_u<width>_galois.rs` is a
//! standalone rustc invocation, so peak memory per compile stays
//! within budget.
//!
//! Spot tests stay collocated with the source in
//! `src/conn/fixed/u8.rs` — they're cheap to compile.

use connections::fixed::u8::*;
use connections::prop::conn as conn_laws;
use fixed::FixedU8;
use fixed::types::extra::{U0, U1, U2, U3, U4, U6, U7, U8};
use proptest::prelude::*;

macro_rules! props_for_pair {
    ($mod_name:ident, $conn:ident, $FineFrac:ty, $CoarseFrac:ty) => {
        mod $mod_name {
            use super::*;

            proptest! {
                #[test]
                fn galois_l(f in any::<u8>(), b in any::<u8>()) {
                    let fine = FixedU8::<$FineFrac>::from_bits(f);
                    let coarse = FixedU8::<$CoarseFrac>::from_bits(b);
                    prop_assert!(conn_laws::conn_galois_l(&$conn, fine, coarse));
                }
                #[test]
                fn galois_r(f in any::<u8>(), b in any::<u8>()) {
                    let fine = FixedU8::<$FineFrac>::from_bits(f);
                    let coarse = FixedU8::<$CoarseFrac>::from_bits(b);
                    prop_assert!(conn_laws::conn_galois_r(&$conn, fine, coarse));
                }
                #[test]
                fn monotone_l(f1 in any::<u8>(), f2 in any::<u8>()) {
                    let f1 = FixedU8::<$FineFrac>::from_bits(f1);
                    let f2 = FixedU8::<$FineFrac>::from_bits(f2);
                    prop_assert!(conn_laws::conn_monotone_l(&$conn, f1, f2));
                }
                #[test]
                fn monotone_r(b1 in any::<u8>(), b2 in any::<u8>()) {
                    let b1 = FixedU8::<$CoarseFrac>::from_bits(b1);
                    let b2 = FixedU8::<$CoarseFrac>::from_bits(b2);
                    prop_assert!(conn_laws::conn_monotone_r(&$conn, b1, b2));
                }
                #[test]
                fn closure_l(f in any::<u8>()) {
                    let fine = FixedU8::<$FineFrac>::from_bits(f);
                    prop_assert!(conn_laws::conn_closure_l(&$conn, fine));
                }
                #[test]
                fn closure_r(f in any::<u8>()) {
                    let fine = FixedU8::<$FineFrac>::from_bits(f);
                    prop_assert!(conn_laws::conn_closure_r(&$conn, fine));
                }
                #[test]
                fn kernel_l(b in any::<u8>()) {
                    let c = FixedU8::<$CoarseFrac>::from_bits(b);
                    prop_assert!(conn_laws::conn_kernel_l(&$conn, c));
                }
                #[test]
                fn kernel_r(b in any::<u8>()) {
                    let c = FixedU8::<$CoarseFrac>::from_bits(b);
                    prop_assert!(conn_laws::conn_kernel_r(&$conn, c));
                }
                #[test]
                fn idempotent(f in any::<u8>()) {
                    let fine = FixedU8::<$FineFrac>::from_bits(f);
                    prop_assert!(conn_laws::conn_idempotent(&$conn, fine));
                }
            }
        }
    };
}

props_for_pair!(q001q000, Q001Q000, U1, U0);
props_for_pair!(q002q000, Q002Q000, U2, U0);
props_for_pair!(q003q000, Q003Q000, U3, U0);
props_for_pair!(q004q000, Q004Q000, U4, U0);
props_for_pair!(q006q000, Q006Q000, U6, U0);
props_for_pair!(q007q000, Q007Q000, U7, U0);
props_for_pair!(q008q000, Q008Q000, U8, U0);
props_for_pair!(q002q001, Q002Q001, U2, U1);
props_for_pair!(q003q001, Q003Q001, U3, U1);
props_for_pair!(q004q001, Q004Q001, U4, U1);
props_for_pair!(q006q001, Q006Q001, U6, U1);
props_for_pair!(q007q001, Q007Q001, U7, U1);
props_for_pair!(q008q001, Q008Q001, U8, U1);
props_for_pair!(q003q002, Q003Q002, U3, U2);
props_for_pair!(q004q002, Q004Q002, U4, U2);
props_for_pair!(q006q002, Q006Q002, U6, U2);
props_for_pair!(q007q002, Q007Q002, U7, U2);
props_for_pair!(q008q002, Q008Q002, U8, U2);
props_for_pair!(q004q003, Q004Q003, U4, U3);
props_for_pair!(q006q003, Q006Q003, U6, U3);
props_for_pair!(q007q003, Q007Q003, U7, U3);
props_for_pair!(q008q003, Q008Q003, U8, U3);
props_for_pair!(q006q004, Q006Q004, U6, U4);
props_for_pair!(q007q004, Q007Q004, U7, U4);
props_for_pair!(q008q004, Q008Q004, U8, U4);
props_for_pair!(q007q006, Q007Q006, U7, U6);
props_for_pair!(q008q006, Q008Q006, U8, U6);
props_for_pair!(q008q007, Q008Q007, U8, U7);
