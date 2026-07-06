//! Galois-law proptest battery for `core::isize` (the `isize` family).
//! Integration test — see `tests/core/u008.rs` for rationale.
//!
//! Portable on every pointer width: `ISZEI008` / `ISZEI016` are narrowings,
//! `ISZEI128` is a widening with an `Extended<isize>` source. The
//! direction-flipping `→ i32` / `→ i64` rungs are omitted (see
//! `crate::core::isize`).

use connections::core::isize::{ISZEI008, ISZEI016, ISZEI128};
use connections::extended::Extended;
use proptest::prelude::*;

fn arb_isize() -> impl Strategy<Value = isize> {
    prop_oneof![
        Just(0isize),
        Just(isize::MIN),
        Just(isize::MAX),
        Just(i8::MIN as isize),
        Just(i8::MAX as isize),
        Just(i16::MIN as isize),
        Just(i16::MAX as isize),
        any::<isize>(),
    ]
}
fn arb_i8() -> impl Strategy<Value = i8> {
    prop_oneof![Just(i8::MIN), Just(0i8), Just(i8::MAX), any::<i8>()]
}
fn arb_i16() -> impl Strategy<Value = i16> {
    prop_oneof![Just(i16::MIN), Just(0i16), Just(i16::MAX), any::<i16>()]
}
fn arb_ext_isize() -> impl Strategy<Value = Extended<isize>> {
    prop_oneof![
        1 => Just(Extended::NegInf),
        1 => Just(Extended::PosInf),
        1 => Just(Extended::Finite(isize::MIN)),
        1 => Just(Extended::Finite(isize::MAX)),
        8 => any::<isize>().prop_map(Extended::Finite),
    ]
}

// §1 I→I narrowing — single-sided left-Galois.
// `galois_lower` intentionally omitted; see `tests/core/u008.rs`.
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

// §2 I→I widening — `ext_int!` Conns are ConnL only (Plan 32).
macro_rules! ext_int_props {
    ($mod_name:ident, $CONN:path, $arb_src:expr, $arb_tgt:expr) => {
        mod $mod_name {
            use super::*;

            proptest! {
                #[test]
                fn galois_upper(a in $arb_src, b in $arb_tgt) {
                    prop_assert_eq!($CONN.ceil(a) <= b, a <= $CONN.upper(b));
                }
                #[test]
                fn closure_upper(a in $arb_src) {
                    prop_assert!(a <= $CONN.upper($CONN.ceil(a)));
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
                fn kernel_upper(b in $arb_tgt) {
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

single_sided_props!(iszei008, ISZEI008, arb_isize(), arb_i8());
single_sided_props!(iszei016, ISZEI016, arb_isize(), arb_i16());
ext_int_props!(iszei128, ISZEI128, arb_ext_isize(), any::<i128>());
