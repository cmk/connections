//! Galois-law proptest battery for `core::u032`. Integration
//! test — see `tests/core/u008.rs` for rationale.

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
                    prop_assert_eq!($CONN.ceil(a) <= b, a <= $CONN.upper(b));
                }
                #[test]
                fn ceil_monotone(a1 in $arb_src, a2 in $arb_src) {
                    let (lo, hi) = if a1 <= a2 { (a1, a2) } else { (a2, a1) };
                    prop_assert!($CONN.ceil(lo) <= $CONN.ceil(hi));
                }
                #[test]
                fn inner_monotone(b1 in $arb_tgt, b2 in $arb_tgt) {
                    let (lo, hi) = if b1 <= b2 { (b1, b2) } else { (b2, b1) };
                    prop_assert!($CONN.upper(lo) <= $CONN.upper(hi));
                }
                #[test]
                fn kernel(b in $arb_tgt) {
                    prop_assert!($CONN.ceil($CONN.upper(b)) <= b);
                }
                #[test]
                fn idempotent(a in $arb_src) {
                    let once = $CONN.upper($CONN.ceil(a));
                    let twice = $CONN.upper($CONN.ceil(once));
                    prop_assert_eq!(once, twice);
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

// §2 U→U narrowing into u32
single_sided_props!(u064u032, U064U032, any::<u64>(), any::<u32>());
single_sided_props!(u128u032, U128U032, any::<u128>(), any::<u32>());

// §4 I→U narrowing into u32
single_sided_props!(i064u032, I064U032, any::<i64>(), any::<u32>());
single_sided_props!(i128u032, I128U032, any::<i128>(), any::<u32>());
