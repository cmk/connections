//! Galois-law proptest battery for `conn::fixed::u128`. Integration
//! test — see `tests/conn_fixed_u08_galois.rs` for rationale.
//!
//! u128 generators are expensive; case count capped to 64 (same
//! precedent as `conn::fixed::i128`).

#[allow(unused_imports)]
use connections::conn::{ViewL, ViewR};
use connections::fixed::u128::*;
use connections::prop::conn as conn_laws;
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
                    prop_assert!(conn_laws::galois_l(&<$conn as connections::conn::ViewL<_, _>>::L, fine, coarse));
                }
                #[test]
                fn galois_r(f in any::<u128>(), b in any::<u128>()) {
                    let fine = FixedU128::<$FineFrac>::from_bits(f);
                    let coarse = FixedU128::<$CoarseFrac>::from_bits(b);
                    prop_assert!(conn_laws::galois_r(&<$conn as connections::conn::ViewR<_, _>>::R, fine, coarse));
                }
                #[test]
                fn monotone_l(f1 in any::<u128>(), f2 in any::<u128>()) {
                    let f1 = FixedU128::<$FineFrac>::from_bits(f1);
                    let f2 = FixedU128::<$FineFrac>::from_bits(f2);
                    prop_assert!(conn_laws::monotone_l(&<$conn as connections::conn::ViewL<_, _>>::L, f1, f2));
                }
                #[test]
                fn monotone_r(b1 in any::<u128>(), b2 in any::<u128>()) {
                    let b1 = FixedU128::<$CoarseFrac>::from_bits(b1);
                    let b2 = FixedU128::<$CoarseFrac>::from_bits(b2);
                    prop_assert!(conn_laws::monotone_r(&<$conn as connections::conn::ViewR<_, _>>::R, b1, b2));
                }
                #[test]
                fn closure_l(f in any::<u128>()) {
                    let fine = FixedU128::<$FineFrac>::from_bits(f);
                    prop_assert!(conn_laws::closure_l(&<$conn as connections::conn::ViewL<_, _>>::L, fine));
                }
                #[test]
                fn closure_r(f in any::<u128>()) {
                    let fine = FixedU128::<$FineFrac>::from_bits(f);
                    prop_assert!(conn_laws::closure_r(&<$conn as connections::conn::ViewR<_, _>>::R, fine));
                }
                #[test]
                fn kernel_l(b in any::<u128>()) {
                    let c = FixedU128::<$CoarseFrac>::from_bits(b);
                    prop_assert!(conn_laws::kernel_l(&<$conn as connections::conn::ViewL<_, _>>::L, c));
                }
                #[test]
                fn kernel_r(b in any::<u128>()) {
                    let c = FixedU128::<$CoarseFrac>::from_bits(b);
                    prop_assert!(conn_laws::kernel_r(&<$conn as connections::conn::ViewR<_, _>>::R, c));
                }
                #[test]
                fn idempotent(f in any::<u128>()) {
                    let fine = FixedU128::<$FineFrac>::from_bits(f);
                    prop_assert!(conn_laws::idempotent(&<$conn as connections::conn::ViewL<_, _>>::L, fine));
                }
            }
        }
    };
}

props_for_pair!(q016q000, Q016Q000, U16, U0);
props_for_pair!(q032q000, Q032Q000, U32, U0);
props_for_pair!(q064q000, Q064Q000, U64, U0);
props_for_pair!(q096q000, Q096Q000, U96, U0);
props_for_pair!(q127q000, Q127Q000, U127, U0);
props_for_pair!(q128q000, Q128Q000, U128, U0);
props_for_pair!(q032q016, Q032Q016, U32, U16);
props_for_pair!(q064q016, Q064Q016, U64, U16);
props_for_pair!(q096q016, Q096Q016, U96, U16);
props_for_pair!(q127q016, Q127Q016, U127, U16);
props_for_pair!(q128q016, Q128Q016, U128, U16);
props_for_pair!(q064q032, Q064Q032, U64, U32);
props_for_pair!(q096q032, Q096Q032, U96, U32);
props_for_pair!(q127q032, Q127Q032, U127, U32);
props_for_pair!(q128q032, Q128Q032, U128, U32);
props_for_pair!(q096q064, Q096Q064, U96, U64);
props_for_pair!(q127q064, Q127Q064, U127, U64);
props_for_pair!(q128q064, Q128Q064, U128, U64);
props_for_pair!(q127q096, Q127Q096, U127, U96);
props_for_pair!(q128q096, Q128Q096, U128, U96);
props_for_pair!(q128q127, Q128Q127, U128, U127);
