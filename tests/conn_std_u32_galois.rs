//! Galois-law proptest battery for `conn::std::u32`. Integration
//! test — see `tests/conn_std_u8_galois.rs` for rationale.

use connections::conn::std::u32::*;
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

single_sided_props!(u008u032, U008U032, any::<u8>(), any::<u32>());
single_sided_props!(u016u032, U016U032, any::<u16>(), any::<u32>());
single_sided_props!(i008u032, I008U032, any::<i8>(), any::<u32>());
single_sided_props!(i016u032, I016U032, any::<i16>(), any::<u32>());
single_sided_props!(i032u032, I032U032, any::<i32>(), any::<u32>());
