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
use connections::prop::laws;
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
                    prop_assert!(laws::conn_galois_l(&$conn, fine, coarse));
                }
                #[test]
                fn galois_r(f in any::<u8>(), b in any::<u8>()) {
                    let fine = FixedU8::<$FineFrac>::from_bits(f);
                    let coarse = FixedU8::<$CoarseFrac>::from_bits(b);
                    prop_assert!(laws::conn_galois_r(&$conn, fine, coarse));
                }
                #[test]
                fn monotone_l(f1 in any::<u8>(), f2 in any::<u8>()) {
                    let f1 = FixedU8::<$FineFrac>::from_bits(f1);
                    let f2 = FixedU8::<$FineFrac>::from_bits(f2);
                    prop_assert!(laws::conn_monotone_l(&$conn, f1, f2));
                }
                #[test]
                fn monotone_r(b1 in any::<u8>(), b2 in any::<u8>()) {
                    let b1 = FixedU8::<$CoarseFrac>::from_bits(b1);
                    let b2 = FixedU8::<$CoarseFrac>::from_bits(b2);
                    prop_assert!(laws::conn_monotone_r(&$conn, b1, b2));
                }
                #[test]
                fn closure_l(f in any::<u8>()) {
                    let fine = FixedU8::<$FineFrac>::from_bits(f);
                    prop_assert!(laws::conn_closure_l(&$conn, fine));
                }
                #[test]
                fn closure_r(f in any::<u8>()) {
                    let fine = FixedU8::<$FineFrac>::from_bits(f);
                    prop_assert!(laws::conn_closure_r(&$conn, fine));
                }
                #[test]
                fn kernel_l(b in any::<u8>()) {
                    let c = FixedU8::<$CoarseFrac>::from_bits(b);
                    prop_assert!(laws::conn_kernel_l(&$conn, c));
                }
                #[test]
                fn kernel_r(b in any::<u8>()) {
                    let c = FixedU8::<$CoarseFrac>::from_bits(b);
                    prop_assert!(laws::conn_kernel_r(&$conn, c));
                }
                #[test]
                fn idempotent(f in any::<u8>()) {
                    let fine = FixedU8::<$FineFrac>::from_bits(f);
                    prop_assert!(laws::conn_idempotent(&$conn, fine));
                }
            }
        }
    };
}

props_for_pair!(u001u000, U001U000, U1, U0);
props_for_pair!(u002u000, U002U000, U2, U0);
props_for_pair!(u003u000, U003U000, U3, U0);
props_for_pair!(u004u000, U004U000, U4, U0);
props_for_pair!(u006u000, U006U000, U6, U0);
props_for_pair!(u007u000, U007U000, U7, U0);
props_for_pair!(u008u000, U008U000, U8, U0);
props_for_pair!(u002u001, U002U001, U2, U1);
props_for_pair!(u003u001, U003U001, U3, U1);
props_for_pair!(u004u001, U004U001, U4, U1);
props_for_pair!(u006u001, U006U001, U6, U1);
props_for_pair!(u007u001, U007U001, U7, U1);
props_for_pair!(u008u001, U008U001, U8, U1);
props_for_pair!(u003u002, U003U002, U3, U2);
props_for_pair!(u004u002, U004U002, U4, U2);
props_for_pair!(u006u002, U006U002, U6, U2);
props_for_pair!(u007u002, U007U002, U7, U2);
props_for_pair!(u008u002, U008U002, U8, U2);
props_for_pair!(u004u003, U004U003, U4, U3);
props_for_pair!(u006u003, U006U003, U6, U3);
props_for_pair!(u007u003, U007U003, U7, U3);
props_for_pair!(u008u003, U008U003, U8, U3);
props_for_pair!(u006u004, U006U004, U6, U4);
props_for_pair!(u007u004, U007U004, U7, U4);
props_for_pair!(u008u004, U008U004, U8, U4);
props_for_pair!(u007u006, U007U006, U7, U6);
props_for_pair!(u008u006, U008U006, U8, U6);
props_for_pair!(u008u007, U008U007, U8, U7);
