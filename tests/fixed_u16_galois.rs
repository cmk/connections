//! Galois-law proptest battery for `conn::fixed::u16`.
//!
//! See `tests/conn_fixed_u08_galois.rs` for the rationale: this is
//! an integration test rather than a `#[cfg(test)] mod` inside
//! `src/conn/fixed/u16.rs` to keep the lib-test rustc invocation
//! under CI's container memory budget.

use connections::fixed::u16::*;
use connections::property::laws;
use fixed::FixedU16;
use fixed::types::extra::{U0, U2, U4, U8, U12, U14, U15, U16};
use proptest::prelude::*;

macro_rules! props_for_pair {
    ($mod_name:ident, $conn:ident, $FineFrac:ty, $CoarseFrac:ty) => {
        mod $mod_name {
            use super::*;

            proptest! {
                #[test]
                fn galois_l(f in any::<u16>(), b in any::<u16>()) {
                    let fine = FixedU16::<$FineFrac>::from_bits(f);
                    let coarse = FixedU16::<$CoarseFrac>::from_bits(b);
                    prop_assert!(laws::conn_galois_l(&$conn, fine, coarse));
                }
                #[test]
                fn galois_r(f in any::<u16>(), b in any::<u16>()) {
                    let fine = FixedU16::<$FineFrac>::from_bits(f);
                    let coarse = FixedU16::<$CoarseFrac>::from_bits(b);
                    prop_assert!(laws::conn_galois_r(&$conn, fine, coarse));
                }
                #[test]
                fn monotone_l(f1 in any::<u16>(), f2 in any::<u16>()) {
                    let f1 = FixedU16::<$FineFrac>::from_bits(f1);
                    let f2 = FixedU16::<$FineFrac>::from_bits(f2);
                    prop_assert!(laws::conn_monotone_l(&$conn, f1, f2));
                }
                #[test]
                fn monotone_r(b1 in any::<u16>(), b2 in any::<u16>()) {
                    let b1 = FixedU16::<$CoarseFrac>::from_bits(b1);
                    let b2 = FixedU16::<$CoarseFrac>::from_bits(b2);
                    prop_assert!(laws::conn_monotone_r(&$conn, b1, b2));
                }
                #[test]
                fn closure_l(f in any::<u16>()) {
                    let fine = FixedU16::<$FineFrac>::from_bits(f);
                    prop_assert!(laws::conn_closure_l(&$conn, fine));
                }
                #[test]
                fn closure_r(f in any::<u16>()) {
                    let fine = FixedU16::<$FineFrac>::from_bits(f);
                    prop_assert!(laws::conn_closure_r(&$conn, fine));
                }
                #[test]
                fn kernel_l(b in any::<u16>()) {
                    let c = FixedU16::<$CoarseFrac>::from_bits(b);
                    prop_assert!(laws::conn_kernel_l(&$conn, c));
                }
                #[test]
                fn kernel_r(b in any::<u16>()) {
                    let c = FixedU16::<$CoarseFrac>::from_bits(b);
                    prop_assert!(laws::conn_kernel_r(&$conn, c));
                }
                #[test]
                fn idempotent(f in any::<u16>()) {
                    let fine = FixedU16::<$FineFrac>::from_bits(f);
                    prop_assert!(laws::conn_idempotent(&$conn, fine));
                }
            }
        }
    };
}

props_for_pair!(u002u000, U002U000, U2, U0);
props_for_pair!(u004u000, U004U000, U4, U0);
props_for_pair!(u008u000, U008U000, U8, U0);
props_for_pair!(u012u000, U012U000, U12, U0);
props_for_pair!(u014u000, U014U000, U14, U0);
props_for_pair!(u015u000, U015U000, U15, U0);
props_for_pair!(u016u000, U016U000, U16, U0);
props_for_pair!(u004u002, U004U002, U4, U2);
props_for_pair!(u008u002, U008U002, U8, U2);
props_for_pair!(u012u002, U012U002, U12, U2);
props_for_pair!(u014u002, U014U002, U14, U2);
props_for_pair!(u015u002, U015U002, U15, U2);
props_for_pair!(u016u002, U016U002, U16, U2);
props_for_pair!(u008u004, U008U004, U8, U4);
props_for_pair!(u012u004, U012U004, U12, U4);
props_for_pair!(u014u004, U014U004, U14, U4);
props_for_pair!(u015u004, U015U004, U15, U4);
props_for_pair!(u016u004, U016U004, U16, U4);
props_for_pair!(u012u008, U012U008, U12, U8);
props_for_pair!(u014u008, U014U008, U14, U8);
props_for_pair!(u015u008, U015U008, U15, U8);
props_for_pair!(u016u008, U016U008, U16, U8);
props_for_pair!(u014u012, U014U012, U14, U12);
props_for_pair!(u015u012, U015U012, U15, U12);
props_for_pair!(u016u012, U016U012, U16, U12);
props_for_pair!(u015u014, U015U014, U15, U14);
props_for_pair!(u016u014, U016U014, U16, U14);
props_for_pair!(u016u015, U016U015, U16, U15);
