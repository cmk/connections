//! Galois-law proptest battery for `conn::std::i8`. Integration
//! test — see `tests/conn_std_u8_galois.rs` for rationale.
//!
//! No widening lands on `i8`. Population is split between left-
//! Galois single-sided narrowing (`I??I008`, T3) and right-Galois
//! single-sided non-widening (`U??I008`, T5).

use connections::conn::std::i8::*;
use proptest::prelude::*;

macro_rules! single_sided_props {
    ($mod_name:ident, $CONN:expr, $arb_src:expr, $arb_tgt:expr) => {
        mod $mod_name {
            use super::*;

            proptest! {
                #[test]
                fn galois_upper(a in $arb_src, b in $arb_tgt) {
                    prop_assert_eq!($CONN.ceil(a) <= b, a <= $CONN.inner(b));
                }
                #[test]
                fn ceil_monotone(a1 in $arb_src, a2 in $arb_src) {
                    let (lo, hi) = if a1 <= a2 { (a1, a2) } else { (a2, a1) };
                    prop_assert!($CONN.ceil(lo) <= $CONN.ceil(hi));
                }
                #[test]
                fn inner_monotone(b1 in $arb_tgt, b2 in $arb_tgt) {
                    let (lo, hi) = if b1 <= b2 { (b1, b2) } else { (b2, b1) };
                    prop_assert!($CONN.inner(lo) <= $CONN.inner(hi));
                }
                #[test]
                fn kernel(b in $arb_tgt) {
                    prop_assert!($CONN.ceil($CONN.inner(b)) <= b);
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
