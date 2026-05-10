//! Galois-law proptest battery for `conn::std::i128`. Integration
//! test — see `tests/conn_std_u8_galois.rs` for rationale.

#[allow(unused_imports)]
use connections::conn::{ConnL, ConnR};
#[allow(unused_imports)]
use connections::core::{
    i008::*, i016::*, i032::*, i064::*, i128::*, u008::*, u016::*, u032::*, u064::*, u128::*,
};
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
arb_ext!(arb_ext_i64, i64);
arb_ext!(arb_ext_u8, u8);
arb_ext!(arb_ext_u16, u16);
arb_ext!(arb_ext_u32, u32);
arb_ext!(arb_ext_u64, u64);

// `ext_int!` Conns are now ConnL only (Plan 32).
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

ext_int_props!(i008i128, I008I128, arb_ext_i8(), any::<i128>());
ext_int_props!(i016i128, I016I128, arb_ext_i16(), any::<i128>());
ext_int_props!(i032i128, I032I128, arb_ext_i32(), any::<i128>());
ext_int_props!(i064i128, I064I128, arb_ext_i64(), any::<i128>());
ext_int_props!(u008i128, U008I128, arb_ext_u8(), any::<i128>());
ext_int_props!(u016i128, U016I128, arb_ext_u16(), any::<i128>());
ext_int_props!(u032i128, U032I128, arb_ext_u32(), any::<i128>());
ext_int_props!(u064i128, U064I128, arb_ext_u64(), any::<i128>());

// §3 U→I non-widening — single-sided right-Galois.
macro_rules! single_sided_right_props {
    ($mod_name:ident, $CONN:path, $arb_src:expr, $arb_tgt:expr) => {
        mod $mod_name {
            use super::*;

            proptest! {
                #[test]
                fn galois_lower(a in $arb_src, b in $arb_tgt) {
                    prop_assert_eq!($CONN.lower(b) <= a, b <= $CONN.floor(a));
                }
                #[test]
                fn floor_monotone(a1 in $arb_src, a2 in $arb_src) {
                    let (lo, hi) = if a1 <= a2 { (a1, a2) } else { (a2, a1) };
                    prop_assert!($CONN.floor(lo) <= $CONN.floor(hi));
                }
                #[test]
                fn inner_monotone(b1 in $arb_tgt, b2 in $arb_tgt) {
                    let (lo, hi) = if b1 <= b2 { (b1, b2) } else { (b2, b1) };
                    prop_assert!($CONN.lower(lo) <= $CONN.lower(hi));
                }
                #[test]
                fn kernel_lower(b in $arb_tgt) {
                    prop_assert!(b <= $CONN.floor($CONN.lower(b)));
                }
                #[test]
                fn idempotent(a in $arb_src) {
                    let once = $CONN.lower($CONN.floor(a));
                    let twice = $CONN.lower($CONN.floor(once));
                    prop_assert_eq!(once, twice);
                }
            }
        }
    };
}

single_sided_right_props!(u128i128, U128I128, any::<u128>(), any::<i128>());
