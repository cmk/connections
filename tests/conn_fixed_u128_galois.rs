//! Galois-law proptest battery for `conn::fixed::u128`. Integration
//! test — see `tests/conn_fixed_u08_galois.rs` for rationale.
//!
//! u128 generators are expensive; case count capped to 64 (same
//! precedent as `conn::fixed::i128`).

use connections::conn::fixed::u128::*;
use connections::property::laws;
use fixed::FixedU128;
use fixed::types::extra::{U0, U16, U32, U64, U96, U127, U128};
use proptest::prelude::*;

macro_rules! props_for_pair {
    ($mod_name:ident, $conn:ident, $FineFrac:ty, $CoarseFrac:ty) => {
        mod $mod_name {
            use super::*;

            proptest! {
                #![proptest_config(ProptestConfig::with_cases(64))]

                #[test]
                fn galois_l(f in any::<u128>(), b in any::<u128>()) {
                    let fine = FixedU128::<$FineFrac>::from_bits(f);
                    let coarse = FixedU128::<$CoarseFrac>::from_bits(b);
                    prop_assert!(laws::conn_galois_l(&$conn, fine, coarse));
                }
                #[test]
                fn galois_r(f in any::<u128>(), b in any::<u128>()) {
                    let fine = FixedU128::<$FineFrac>::from_bits(f);
                    let coarse = FixedU128::<$CoarseFrac>::from_bits(b);
                    prop_assert!(laws::conn_galois_r(&$conn, fine, coarse));
                }
                #[test]
                fn monotone_l(f1 in any::<u128>(), f2 in any::<u128>()) {
                    let f1 = FixedU128::<$FineFrac>::from_bits(f1);
                    let f2 = FixedU128::<$FineFrac>::from_bits(f2);
                    prop_assert!(laws::conn_monotone_l(&$conn, f1, f2));
                }
                #[test]
                fn monotone_r(b1 in any::<u128>(), b2 in any::<u128>()) {
                    let b1 = FixedU128::<$CoarseFrac>::from_bits(b1);
                    let b2 = FixedU128::<$CoarseFrac>::from_bits(b2);
                    prop_assert!(laws::conn_monotone_r(&$conn, b1, b2));
                }
                #[test]
                fn closure_l(f in any::<u128>()) {
                    let fine = FixedU128::<$FineFrac>::from_bits(f);
                    prop_assert!(laws::conn_closure_l(&$conn, fine));
                }
                #[test]
                fn closure_r(f in any::<u128>()) {
                    let fine = FixedU128::<$FineFrac>::from_bits(f);
                    prop_assert!(laws::conn_closure_r(&$conn, fine));
                }
                #[test]
                fn kernel_l(b in any::<u128>()) {
                    let c = FixedU128::<$CoarseFrac>::from_bits(b);
                    prop_assert!(laws::conn_kernel_l(&$conn, c));
                }
                #[test]
                fn kernel_r(b in any::<u128>()) {
                    let c = FixedU128::<$CoarseFrac>::from_bits(b);
                    prop_assert!(laws::conn_kernel_r(&$conn, c));
                }
                #[test]
                fn idempotent(f in any::<u128>()) {
                    let fine = FixedU128::<$FineFrac>::from_bits(f);
                    prop_assert!(laws::conn_idempotent(&$conn, fine));
                }
            }
        }
    };
}

props_for_pair!(u016u000, U016U000, U16, U0);
props_for_pair!(u032u000, U032U000, U32, U0);
props_for_pair!(u064u000, U064U000, U64, U0);
props_for_pair!(u096u000, U096U000, U96, U0);
props_for_pair!(u127u000, U127U000, U127, U0);
props_for_pair!(u128u000, U128U000, U128, U0);
props_for_pair!(u032u016, U032U016, U32, U16);
props_for_pair!(u064u016, U064U016, U64, U16);
props_for_pair!(u096u016, U096U016, U96, U16);
props_for_pair!(u127u016, U127U016, U127, U16);
props_for_pair!(u128u016, U128U016, U128, U16);
props_for_pair!(u064u032, U064U032, U64, U32);
props_for_pair!(u096u032, U096U032, U96, U32);
props_for_pair!(u127u032, U127U032, U127, U32);
props_for_pair!(u128u032, U128U032, U128, U32);
props_for_pair!(u096u064, U096U064, U96, U64);
props_for_pair!(u127u064, U127U064, U127, U64);
props_for_pair!(u128u064, U128U064, U128, U64);
props_for_pair!(u127u096, U127U096, U127, U96);
props_for_pair!(u128u096, U128U096, U128, U96);
props_for_pair!(u128u127, U128U127, U128, U127);
