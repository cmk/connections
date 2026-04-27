//! Galois-law proptest battery for `conn::std::i64`. Integration
//! test — see `tests/conn_std_u8_galois.rs` for rationale.

use connections::conn::std::i64::*;
use connections::extended::Extended;
use proptest::prelude::*;

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
arb_ext!(arb_ext_i16, i16);
arb_ext!(arb_ext_i32, i32);
arb_ext!(arb_ext_u8, u8);
arb_ext!(arb_ext_u16, u16);
arb_ext!(arb_ext_u32, u32);

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
            }
        }
    };
}

ext_int_props!(i008i064, I008I064, arb_ext_i8(), any::<i64>());
ext_int_props!(i016i064, I016I064, arb_ext_i16(), any::<i64>());
ext_int_props!(i032i064, I032I064, arb_ext_i32(), any::<i64>());
ext_int_props!(u008i064, U008I064, arb_ext_u8(), any::<i64>());
ext_int_props!(u016i064, U016I064, arb_ext_u16(), any::<i64>());
ext_int_props!(u032i064, U032I064, arb_ext_u32(), any::<i64>());

// §1 I→I narrowing — single-sided left-Galois.
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

single_sided_props!(i128i064, I128I064, any::<i128>(), any::<i64>());
