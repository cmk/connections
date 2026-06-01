//! Galois-law proptest battery for `core::i008`. Integration
//! test — see `tests/core/u008.rs` for rationale.
//!
//! No widening lands on `i8`. Population is split between left-
//! Galois single-sided narrowing (`I??I008`, T3) and right-Galois
//! single-sided non-widening (`U??I008`, T5).

#[allow(unused_imports)]
use connections::conn::{ConnL, ConnR};
#[allow(unused_imports)]
use connections::core::{
    i008::*, i016::*, i032::*, i064::*, i128::*, u008::*, u016::*, u032::*, u064::*, u128::*,
};
use proptest::prelude::*;

// `galois_lower` intentionally omitted; see
// `tests/core/u008.rs`.
macro_rules! single_sided_props {
    ($mod_name:ident, $CONN:path, $arb_src:expr, $arb_tgt:expr) => {
        mod $mod_name {
            use super::*;

            proptest! {
                #[test]
                fn galois_upper(a in $arb_src, b in $arb_tgt) {
                    prop_assert_eq!(connections::conn::ceil(&$CONN, a) <= b, a <= connections::conn::upper(&$CONN, b));
                }
                #[test]
                fn ceil_monotone(a1 in $arb_src, a2 in $arb_src) {
                    let (lo, hi) = if a1 <= a2 { (a1, a2) } else { (a2, a1) };
                    prop_assert!(connections::conn::ceil(&$CONN, lo) <= connections::conn::ceil(&$CONN, hi));
                }
                #[test]
                fn inner_monotone(b1 in $arb_tgt, b2 in $arb_tgt) {
                    let (lo, hi) = if b1 <= b2 { (b1, b2) } else { (b2, b1) };
                    prop_assert!(connections::conn::upper(&$CONN, lo) <= connections::conn::upper(&$CONN, hi));
                }
                #[test]
                fn kernel(b in $arb_tgt) {
                    prop_assert!(connections::conn::ceil(&$CONN, connections::conn::upper(&$CONN, b)) <= b);
                }
                #[test]
                fn idempotent(a in $arb_src) {
                    let once = connections::conn::upper(&$CONN, connections::conn::ceil(&$CONN, a));
                    let twice = connections::conn::upper(&$CONN, connections::conn::ceil(&$CONN, once));
                    prop_assert_eq!(once, twice);
                }
            }
        }
    };
}

// §1 I→I narrowing
single_sided_props!(i016i008, I016I008, any::<i16>(), any::<i8>());
single_sided_props!(i032i008, I032I008, any::<i32>(), any::<i8>());
single_sided_props!(i064i008, I064I008, any::<i64>(), any::<i8>());
single_sided_props!(i128i008, I128I008, any::<i128>(), any::<i8>());

// §3 U→I non-widening — single-sided right-Galois.
//
//   galois_lower:    inner(b) ≤ a  ⟺  b ≤ floor(a)
//   floor_monotone:  a1 ≤ a2  ⟹  floor(a1) ≤ floor(a2)
//   inner_monotone:  b1 ≤ b2  ⟹  inner(b1) ≤ inner(b2)
//   kernel_lower:    b ≤ floor(inner(b))
macro_rules! single_sided_right_props {
    ($mod_name:ident, $CONN:path, $arb_src:expr, $arb_tgt:expr) => {
        mod $mod_name {
            use super::*;

            proptest! {
                #[test]
                fn galois_lower(a in $arb_src, b in $arb_tgt) {
                    prop_assert_eq!(connections::conn::lower(&$CONN, b) <= a, b <= connections::conn::floor(&$CONN, a));
                }
                #[test]
                fn floor_monotone(a1 in $arb_src, a2 in $arb_src) {
                    let (lo, hi) = if a1 <= a2 { (a1, a2) } else { (a2, a1) };
                    prop_assert!(connections::conn::floor(&$CONN, lo) <= connections::conn::floor(&$CONN, hi));
                }
                #[test]
                fn inner_monotone(b1 in $arb_tgt, b2 in $arb_tgt) {
                    let (lo, hi) = if b1 <= b2 { (b1, b2) } else { (b2, b1) };
                    prop_assert!(connections::conn::lower(&$CONN, lo) <= connections::conn::lower(&$CONN, hi));
                }
                #[test]
                fn kernel_lower(b in $arb_tgt) {
                    prop_assert!(b <= connections::conn::floor(&$CONN, connections::conn::lower(&$CONN, b)));
                }
                #[test]
                fn idempotent(a in $arb_src) {
                    // For Conn::new_right, ceil = floor; idempotent
                    // tests inner ∘ ceil applied twice. Same closure
                    // operator either way.
                    let once = connections::conn::lower(&$CONN, connections::conn::floor(&$CONN, a));
                    let twice = connections::conn::lower(&$CONN, connections::conn::floor(&$CONN, once));
                    prop_assert_eq!(once, twice);
                }
            }
        }
    };
}

single_sided_right_props!(u008i008, U008I008, any::<u8>(), any::<i8>());
single_sided_right_props!(u016i008, U016I008, any::<u16>(), any::<i8>());
single_sided_right_props!(u032i008, U032I008, any::<u32>(), any::<i8>());
single_sided_right_props!(u064i008, U064I008, any::<u64>(), any::<i8>());
single_sided_right_props!(u128i008, U128I008, any::<u128>(), any::<i8>());
