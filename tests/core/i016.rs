//! Galois-law proptest battery for `core::i016`. Integration
//! test — see `tests/core/u008.rs` for rationale.
//!
//! Existing widening Conns use the Extended-source full-triple
//! battery. T3 (I→I narrowing) and T5 (U→I non-widening) commits
//! append additional invocations to this file.

#[allow(unused_imports)]
use connections::conn::{ConnL, ConnR};
#[allow(unused_imports)]
use connections::core::{
    i008::*, i016::*, i032::*, i064::*, i128::*, u008::*, u016::*, u032::*, u064::*, u128::*,
};
use connections::extended::Extended;
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

// `ext_int!` Conns are now ConnL only (Plan 32 — `inner` is
// non-injective at the saturation regions, so no true triple
// exists). The L-side battery covers all per-side adjunction laws;
// `floor`/`floor_monotone`/`kernel_lower` are gone (compile-time
// removed by the macro switch to `Conn::new_l`).
macro_rules! ext_int_props {
    ($mod_name:ident, $CONN:path, $arb_src:expr, $arb_tgt:expr) => {
        mod $mod_name {
            use super::*;

            proptest! {
                #[test]
                fn galois_upper(a in $arb_src, b in $arb_tgt) {
                    prop_assert_eq!(connections::conn::ceil(&$CONN, a) <= b, a <= connections::conn::upper(&$CONN, b));
                }
                #[test]
                fn closure_upper(a in $arb_src) {
                    prop_assert!(a <= connections::conn::upper(&$CONN, connections::conn::ceil(&$CONN, a)));
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
                fn kernel_upper(b in $arb_tgt) {
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

ext_int_props!(i008i016, I008I016, arb_ext_i8(), any::<i16>());
ext_int_props!(u008i016, U008I016, arb_ext_u8(), any::<i16>());

// §1 I→I narrowing — single-sided left-Galois.
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

single_sided_props!(i032i016, I032I016, any::<i32>(), any::<i16>());
single_sided_props!(i064i016, I064I016, any::<i64>(), any::<i16>());
single_sided_props!(i128i016, I128I016, any::<i128>(), any::<i16>());

// §3 U→I non-widening — single-sided right-Galois.
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
                    let once = connections::conn::lower(&$CONN, connections::conn::floor(&$CONN, a));
                    let twice = connections::conn::lower(&$CONN, connections::conn::floor(&$CONN, once));
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
