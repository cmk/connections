//! Galois-law proptest battery for `conn::fixed::u64`. Integration
//! test — see `tests/conn_fixed_u08_galois.rs` for rationale.

use connections::fixed::u64::*;
use connections::prop::conn as conn_laws;
use fixed::FixedU64;
use fixed::types::extra::{U0, U8, U16, U32, U48, U63, U64};
use proptest::prelude::*;

macro_rules! props_for_pair {
    ($mod_name:ident, $conn:ident, $FineFrac:ty, $CoarseFrac:ty) => {
        mod $mod_name {
            use super::*;

            proptest! {
                #[test]
                fn galois_l(f in any::<u64>(), b in any::<u64>()) {
                    let fine = FixedU64::<$FineFrac>::from_bits(f);
                    let coarse = FixedU64::<$CoarseFrac>::from_bits(b);
                    prop_assert!(conn_laws::conn_galois_l(&$conn, fine, coarse));
                }
                #[test]
                fn galois_r(f in any::<u64>(), b in any::<u64>()) {
                    let fine = FixedU64::<$FineFrac>::from_bits(f);
                    let coarse = FixedU64::<$CoarseFrac>::from_bits(b);
                    prop_assert!(conn_laws::conn_galois_r(&$conn, fine, coarse));
                }
                #[test]
                fn monotone_l(f1 in any::<u64>(), f2 in any::<u64>()) {
                    let f1 = FixedU64::<$FineFrac>::from_bits(f1);
                    let f2 = FixedU64::<$FineFrac>::from_bits(f2);
                    prop_assert!(conn_laws::conn_monotone_l(&$conn, f1, f2));
                }
                #[test]
                fn monotone_r(b1 in any::<u64>(), b2 in any::<u64>()) {
                    let b1 = FixedU64::<$CoarseFrac>::from_bits(b1);
                    let b2 = FixedU64::<$CoarseFrac>::from_bits(b2);
                    prop_assert!(conn_laws::conn_monotone_r(&$conn, b1, b2));
                }
                #[test]
                fn closure_l(f in any::<u64>()) {
                    let fine = FixedU64::<$FineFrac>::from_bits(f);
                    prop_assert!(conn_laws::conn_closure_l(&$conn, fine));
                }
                #[test]
                fn closure_r(f in any::<u64>()) {
                    let fine = FixedU64::<$FineFrac>::from_bits(f);
                    prop_assert!(conn_laws::conn_closure_r(&$conn, fine));
                }
                #[test]
                fn kernel_l(b in any::<u64>()) {
                    let c = FixedU64::<$CoarseFrac>::from_bits(b);
                    prop_assert!(conn_laws::conn_kernel_l(&$conn, c));
                }
                #[test]
                fn kernel_r(b in any::<u64>()) {
                    let c = FixedU64::<$CoarseFrac>::from_bits(b);
                    prop_assert!(conn_laws::conn_kernel_r(&$conn, c));
                }
                #[test]
                fn idempotent(f in any::<u64>()) {
                    let fine = FixedU64::<$FineFrac>::from_bits(f);
                    prop_assert!(conn_laws::conn_idempotent(&$conn, fine));
                }
            }
        }
    };
}

props_for_pair!(u008u000, U008U000, U8, U0);
props_for_pair!(u016u000, U016U000, U16, U0);
props_for_pair!(u032u000, U032U000, U32, U0);
props_for_pair!(u048u000, U048U000, U48, U0);
props_for_pair!(u063u000, U063U000, U63, U0);
props_for_pair!(u064u000, U064U000, U64, U0);
props_for_pair!(u016u008, U016U008, U16, U8);
props_for_pair!(u032u008, U032U008, U32, U8);
props_for_pair!(u048u008, U048U008, U48, U8);
props_for_pair!(u063u008, U063U008, U63, U8);
props_for_pair!(u064u008, U064U008, U64, U8);
props_for_pair!(u032u016, U032U016, U32, U16);
props_for_pair!(u048u016, U048U016, U48, U16);
props_for_pair!(u063u016, U063U016, U63, U16);
props_for_pair!(u064u016, U064U016, U64, U16);
props_for_pair!(u048u032, U048U032, U48, U32);
props_for_pair!(u063u032, U063U032, U63, U32);
props_for_pair!(u064u032, U064U032, U64, U32);
props_for_pair!(u063u048, U063U048, U63, U48);
props_for_pair!(u064u048, U064U048, U64, U48);
props_for_pair!(u064u063, U064U063, U64, U63);
