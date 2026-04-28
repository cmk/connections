//! Galois-law proptest battery for `conn::fixed::u32`. Integration
//! test — see `tests/conn_fixed_u08_galois.rs` for rationale.

use connections::fixed::u32::*;
use connections::prop::conn as conn_laws;
use fixed::FixedU32;
use fixed::types::extra::{U0, U4, U8, U16, U24, U31, U32};
use proptest::prelude::*;

macro_rules! props_for_pair {
    ($mod_name:ident, $conn:ident, $FineFrac:ty, $CoarseFrac:ty) => {
        mod $mod_name {
            use super::*;

            proptest! {
                #[test]
                fn galois_l(f in any::<u32>(), b in any::<u32>()) {
                    let fine = FixedU32::<$FineFrac>::from_bits(f);
                    let coarse = FixedU32::<$CoarseFrac>::from_bits(b);
                    prop_assert!(conn_laws::conn_galois_l(&$conn, fine, coarse));
                }
                #[test]
                fn galois_r(f in any::<u32>(), b in any::<u32>()) {
                    let fine = FixedU32::<$FineFrac>::from_bits(f);
                    let coarse = FixedU32::<$CoarseFrac>::from_bits(b);
                    prop_assert!(conn_laws::conn_galois_r(&$conn, fine, coarse));
                }
                #[test]
                fn monotone_l(f1 in any::<u32>(), f2 in any::<u32>()) {
                    let f1 = FixedU32::<$FineFrac>::from_bits(f1);
                    let f2 = FixedU32::<$FineFrac>::from_bits(f2);
                    prop_assert!(conn_laws::conn_monotone_l(&$conn, f1, f2));
                }
                #[test]
                fn monotone_r(b1 in any::<u32>(), b2 in any::<u32>()) {
                    let b1 = FixedU32::<$CoarseFrac>::from_bits(b1);
                    let b2 = FixedU32::<$CoarseFrac>::from_bits(b2);
                    prop_assert!(conn_laws::conn_monotone_r(&$conn, b1, b2));
                }
                #[test]
                fn closure_l(f in any::<u32>()) {
                    let fine = FixedU32::<$FineFrac>::from_bits(f);
                    prop_assert!(conn_laws::conn_closure_l(&$conn, fine));
                }
                #[test]
                fn closure_r(f in any::<u32>()) {
                    let fine = FixedU32::<$FineFrac>::from_bits(f);
                    prop_assert!(conn_laws::conn_closure_r(&$conn, fine));
                }
                #[test]
                fn kernel_l(b in any::<u32>()) {
                    let c = FixedU32::<$CoarseFrac>::from_bits(b);
                    prop_assert!(conn_laws::conn_kernel_l(&$conn, c));
                }
                #[test]
                fn kernel_r(b in any::<u32>()) {
                    let c = FixedU32::<$CoarseFrac>::from_bits(b);
                    prop_assert!(conn_laws::conn_kernel_r(&$conn, c));
                }
                #[test]
                fn idempotent(f in any::<u32>()) {
                    let fine = FixedU32::<$FineFrac>::from_bits(f);
                    prop_assert!(conn_laws::conn_idempotent(&$conn, fine));
                }
            }
        }
    };
}

props_for_pair!(u004u000, U004U000, U4, U0);
props_for_pair!(u008u000, U008U000, U8, U0);
props_for_pair!(u016u000, U016U000, U16, U0);
props_for_pair!(u024u000, U024U000, U24, U0);
props_for_pair!(u031u000, U031U000, U31, U0);
props_for_pair!(u032u000, U032U000, U32, U0);
props_for_pair!(u008u004, U008U004, U8, U4);
props_for_pair!(u016u004, U016U004, U16, U4);
props_for_pair!(u024u004, U024U004, U24, U4);
props_for_pair!(u031u004, U031U004, U31, U4);
props_for_pair!(u032u004, U032U004, U32, U4);
props_for_pair!(u016u008, U016U008, U16, U8);
props_for_pair!(u024u008, U024U008, U24, U8);
props_for_pair!(u031u008, U031U008, U31, U8);
props_for_pair!(u032u008, U032U008, U32, U8);
props_for_pair!(u024u016, U024U016, U24, U16);
props_for_pair!(u031u016, U031U016, U31, U16);
props_for_pair!(u032u016, U032U016, U32, U16);
props_for_pair!(u031u024, U031U024, U31, U24);
props_for_pair!(u032u024, U032U024, U32, U24);
props_for_pair!(u032u031, U032U031, U32, U31);
