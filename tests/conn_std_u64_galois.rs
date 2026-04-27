//! Galois-law proptest battery for `conn::std::u64`. Integration
//! test — see `tests/conn_std_u8_galois.rs` for rationale.

use connections::conn::std::u64::*;
use proptest::prelude::*;

// `galois_lower` intentionally omitted; see
// `tests/conn_std_u8_galois.rs`.
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

single_sided_props!(u008u064, U008U064, any::<u8>(), any::<u64>());
single_sided_props!(u016u064, U016U064, any::<u16>(), any::<u64>());
single_sided_props!(u032u064, U032U064, any::<u32>(), any::<u64>());
single_sided_props!(i008u064, I008U064, any::<i8>(), any::<u64>());
single_sided_props!(i016u064, I016U064, any::<i16>(), any::<u64>());
single_sided_props!(i032u064, I032U064, any::<i32>(), any::<u64>());
single_sided_props!(i064u064, I064U064, any::<i64>(), any::<u64>());

// §2 U→U narrowing into u64
single_sided_props!(u128u064, U128U064, any::<u128>(), any::<u64>());

// §4 I→U narrowing into u64
single_sided_props!(i128u064, I128U064, any::<i128>(), any::<u64>());
