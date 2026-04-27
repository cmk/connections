//! Galois-law proptest battery for `conn::std::u16`. Integration
//! test — see `tests/conn_std_u8_galois.rs` for rationale.

use connections::conn::std::u16::*;
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
                #[test]
                fn idempotent(a in $arb_src) {
                    let once = $CONN.inner($CONN.ceil(a));
                    let twice = $CONN.inner($CONN.ceil(once));
                    prop_assert_eq!(once, twice);
                }
            }
        }
    };
}

single_sided_props!(u008u016, U008U016, any::<u8>(), any::<u16>());
single_sided_props!(i008u016, I008U016, any::<i8>(), any::<u16>());
single_sided_props!(i016u016, I016U016, any::<i16>(), any::<u16>());

// §2 U→U narrowing into u16
single_sided_props!(u032u016, U032U016, any::<u32>(), any::<u16>());
single_sided_props!(u064u016, U064U016, any::<u64>(), any::<u16>());
single_sided_props!(u128u016, U128U016, any::<u128>(), any::<u16>());

// §4 I→U narrowing into u16
single_sided_props!(i032u016, I032U016, any::<i32>(), any::<u16>());
single_sided_props!(i064u016, I064U016, any::<i64>(), any::<u16>());
single_sided_props!(i128u016, I128U016, any::<i128>(), any::<u16>());
