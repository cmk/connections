//! Galois-law proptest battery for `conn::fixed::u64`. Integration
//! test — see `tests/conn_fixed_u08_galois.rs` for rationale.

#[allow(unused_imports)]
use connections::conn::{ViewL, ViewR};
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
                    prop_assert!(conn_laws::galois_l(&<$conn as connections::conn::ViewL<_, _>>::L, fine, coarse));
                }
                #[test]
                fn galois_r(f in any::<u64>(), b in any::<u64>()) {
                    let fine = FixedU64::<$FineFrac>::from_bits(f);
                    let coarse = FixedU64::<$CoarseFrac>::from_bits(b);
                    prop_assert!(conn_laws::galois_r(&<$conn as connections::conn::ViewR<_, _>>::R, fine, coarse));
                }
                #[test]
                fn monotone_l(f1 in any::<u64>(), f2 in any::<u64>()) {
                    let f1 = FixedU64::<$FineFrac>::from_bits(f1);
                    let f2 = FixedU64::<$FineFrac>::from_bits(f2);
                    prop_assert!(conn_laws::monotone_l(&<$conn as connections::conn::ViewL<_, _>>::L, f1, f2));
                }
                #[test]
                fn monotone_r(b1 in any::<u64>(), b2 in any::<u64>()) {
                    let b1 = FixedU64::<$CoarseFrac>::from_bits(b1);
                    let b2 = FixedU64::<$CoarseFrac>::from_bits(b2);
                    prop_assert!(conn_laws::monotone_r(&<$conn as connections::conn::ViewR<_, _>>::R, b1, b2));
                }
                #[test]
                fn closure_l(f in any::<u64>()) {
                    let fine = FixedU64::<$FineFrac>::from_bits(f);
                    prop_assert!(conn_laws::closure_l(&<$conn as connections::conn::ViewL<_, _>>::L, fine));
                }
                #[test]
                fn closure_r(f in any::<u64>()) {
                    let fine = FixedU64::<$FineFrac>::from_bits(f);
                    prop_assert!(conn_laws::closure_r(&<$conn as connections::conn::ViewR<_, _>>::R, fine));
                }
                #[test]
                fn kernel_l(b in any::<u64>()) {
                    let c = FixedU64::<$CoarseFrac>::from_bits(b);
                    prop_assert!(conn_laws::kernel_l(&<$conn as connections::conn::ViewL<_, _>>::L, c));
                }
                #[test]
                fn kernel_r(b in any::<u64>()) {
                    let c = FixedU64::<$CoarseFrac>::from_bits(b);
                    prop_assert!(conn_laws::kernel_r(&<$conn as connections::conn::ViewR<_, _>>::R, c));
                }
                #[test]
                fn idempotent(f in any::<u64>()) {
                    let fine = FixedU64::<$FineFrac>::from_bits(f);
                    prop_assert!(conn_laws::idempotent(&<$conn as connections::conn::ViewL<_, _>>::L, fine));
                }
            }
        }
    };
}

props_for_pair!(q008q000, Q008Q000, U8, U0);
props_for_pair!(q016q000, Q016Q000, U16, U0);
props_for_pair!(q032q000, Q032Q000, U32, U0);
props_for_pair!(q048q000, Q048Q000, U48, U0);
props_for_pair!(q063q000, Q063Q000, U63, U0);
props_for_pair!(q064q000, Q064Q000, U64, U0);
props_for_pair!(q016q008, Q016Q008, U16, U8);
props_for_pair!(q032q008, Q032Q008, U32, U8);
props_for_pair!(q048q008, Q048Q008, U48, U8);
props_for_pair!(q063q008, Q063Q008, U63, U8);
props_for_pair!(q064q008, Q064Q008, U64, U8);
props_for_pair!(q032q016, Q032Q016, U32, U16);
props_for_pair!(q048q016, Q048Q016, U48, U16);
props_for_pair!(q063q016, Q063Q016, U63, U16);
props_for_pair!(q064q016, Q064Q016, U64, U16);
props_for_pair!(q048q032, Q048Q032, U48, U32);
props_for_pair!(q063q032, Q063Q032, U63, U32);
props_for_pair!(q064q032, Q064Q032, U64, U32);
props_for_pair!(q063q048, Q063Q048, U63, U48);
props_for_pair!(q064q048, Q064Q048, U64, U48);
props_for_pair!(q064q063, Q064Q063, U64, U63);
