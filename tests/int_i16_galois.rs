//! Galois-law proptest battery for `conn::std::i16`. Integration
//! test — see `tests/conn_std_u8_galois.rs` for rationale.
//!
//! Existing widening Conns use the Extended-source full-triple
//! battery. T3 (I→I narrowing) and T5 (U→I non-widening) commits
//! append additional invocations to this file.

use connections::extended::Extended;
use connections::fixed::i16::*;
use proptest::prelude::*;

// Strategies for `Extended<T>` — bias toward boundary values.
// Each generator: 4 boundary singletons (NegInf, PosInf,
// Finite::MIN, Finite::MAX) plus uniform Finite values, frequency
// 1:1:1:1:8.
macro_rules! arb_ext {
    ($name:ident, $T:ty) => {
        fn $name() -> impl Strategy<Value = Extended<$T>> {
            prop_oneof![
                1 => Just(Extended::NegInf),
                1 => Just(Extended::PosInf),
                1 => Just(Extended::Finite(<$T>::MIN)),
                1 => Just(Extended::Finite(<$T>::MAX)),
                8 => any::<$T>().prop_map(Extended::Finite),
            ]
        }
    };
}

arb_ext!(arb_ext_i8, i8);
arb_ext!(arb_ext_u8, u8);

macro_rules! ext_int_props {
    ($mod_name:ident, $CONN:expr, $arb_src:expr, $arb_tgt:expr) => {
        mod $mod_name {
            use super::*;

            proptest! {
                #[test]
                fn galois_upper(a in $arb_src, b in $arb_tgt) {
                    prop_assert_eq!($CONN.ceil(a) <= b, a <= $CONN.inner(b));
                }
                #[test]
                fn galois_lower(a in $arb_src, b in $arb_tgt) {
                    prop_assert_eq!($CONN.inner(b) <= a, b <= $CONN.floor(a));
                }
                #[test]
                fn ceil_monotone(a1 in $arb_src, a2 in $arb_src) {
                    let (lo, hi) = if a1 <= a2 { (a1, a2) } else { (a2, a1) };
                    prop_assert!($CONN.ceil(lo) <= $CONN.ceil(hi));
                }
                #[test]
                fn floor_monotone(a1 in $arb_src, a2 in $arb_src) {
                    let (lo, hi) = if a1 <= a2 { (a1, a2) } else { (a2, a1) };
                    prop_assert!($CONN.floor(lo) <= $CONN.floor(hi));
                }
                #[test]
                fn inner_monotone(b1 in $arb_tgt, b2 in $arb_tgt) {
                    let (lo, hi) = if b1 <= b2 { (b1, b2) } else { (b2, b1) };
                    prop_assert!($CONN.inner(lo) <= $CONN.inner(hi));
                }
                #[test]
                fn kernel_upper(b in $arb_tgt) {
                    prop_assert!($CONN.ceil($CONN.inner(b)) <= b);
                }
                #[test]
                fn kernel_lower(b in $arb_tgt) {
                    prop_assert!(b <= $CONN.floor($CONN.inner(b)));
                }
                #[test]
                fn idempotent(a in $arb_src) {
                    let once = $CONN.inner($CONN.floor(a));
                    let twice = $CONN.inner($CONN.floor(once));
                    prop_assert_eq!(once, twice);
                }
            }
        }
    };
}

ext_int_props!(i008i016, I008I016, arb_ext_i8(), any::<i16>());
ext_int_props!(u008i016, U008I016, arb_ext_u8(), any::<i16>());

// §1 I→I narrowing — single-sided left-Galois.
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

single_sided_props!(i032i016, I032I016, any::<i32>(), any::<i16>());
single_sided_props!(i064i016, I064I016, any::<i64>(), any::<i16>());
single_sided_props!(i128i016, I128I016, any::<i128>(), any::<i16>());

// §3 U→I non-widening — single-sided right-Galois.
macro_rules! single_sided_right_props {
    ($mod_name:ident, $CONN:expr, $arb_src:expr, $arb_tgt:expr) => {
        mod $mod_name {
            use super::*;

            proptest! {
                #[test]
                fn galois_lower(a in $arb_src, b in $arb_tgt) {
                    prop_assert_eq!($CONN.inner(b) <= a, b <= $CONN.floor(a));
                }
                #[test]
                fn floor_monotone(a1 in $arb_src, a2 in $arb_src) {
                    let (lo, hi) = if a1 <= a2 { (a1, a2) } else { (a2, a1) };
                    prop_assert!($CONN.floor(lo) <= $CONN.floor(hi));
                }
                #[test]
                fn inner_monotone(b1 in $arb_tgt, b2 in $arb_tgt) {
                    let (lo, hi) = if b1 <= b2 { (b1, b2) } else { (b2, b1) };
                    prop_assert!($CONN.inner(lo) <= $CONN.inner(hi));
                }
                #[test]
                fn kernel_lower(b in $arb_tgt) {
                    prop_assert!(b <= $CONN.floor($CONN.inner(b)));
                }
                #[test]
                fn idempotent(a in $arb_src) {
                    let once = $CONN.inner($CONN.floor(a));
                    let twice = $CONN.inner($CONN.floor(once));
                    prop_assert_eq!(once, twice);
                }
            }
        }
    };
}

single_sided_right_props!(u016i016, U016I016, any::<u16>(), any::<i16>());
single_sided_right_props!(u032i016, U032I016, any::<u32>(), any::<i16>());
single_sided_right_props!(u064i016, U064I016, any::<u64>(), any::<i16>());
single_sided_right_props!(u128i016, U128I016, any::<u128>(), any::<i16>());
