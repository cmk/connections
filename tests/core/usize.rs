//! Galois-law proptest battery for `core::size` (the `usize` family).
//! Integration test — see `tests/core/u008.rs` for rationale.
//!
//! `usize` is pointer-width, so `any::<usize>()` samples the host
//! target's width (64-bit on CI); the saturating `TryFrom` bodies keep
//! the laws true regardless of that width.

use connections::core::size::{SIZEU008, SIZEU016, SIZEU032, SIZEU064, SIZEU128};
use proptest::prelude::*;

// `galois_lower` intentionally omitted (these are one-sided L-Conns);
// see `tests/core/u008.rs`.
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

// Boundary-biased strategies: the saturation plateaus live at the type
// maxima, so pin them explicitly rather than trusting `any` to sample them.
fn arb_usize() -> impl Strategy<Value = usize> {
    prop_oneof![
        Just(0usize),
        Just(usize::MAX),
        Just(u8::MAX as usize),
        Just(u16::MAX as usize),
        Just(u32::MAX as usize),
        any::<usize>()
    ]
}
fn arb_u8() -> impl Strategy<Value = u8> {
    prop_oneof![Just(0u8), Just(u8::MAX), any::<u8>()]
}
fn arb_u16() -> impl Strategy<Value = u16> {
    prop_oneof![Just(0u16), Just(u16::MAX), any::<u16>()]
}
fn arb_u32() -> impl Strategy<Value = u32> {
    prop_oneof![Just(0u32), Just(u32::MAX), any::<u32>()]
}
fn arb_u64() -> impl Strategy<Value = u64> {
    prop_oneof![
        Just(0u64),
        Just(u64::MAX),
        Just(usize::MAX as u64),
        any::<u64>()
    ]
}
fn arb_u128() -> impl Strategy<Value = u128> {
    prop_oneof![
        Just(0u128),
        Just(u128::MAX),
        Just(usize::MAX as u128),
        any::<u128>()
    ]
}

single_sided_props!(sizeu008, SIZEU008, arb_usize(), arb_u8());
single_sided_props!(sizeu016, SIZEU016, arb_usize(), arb_u16());
single_sided_props!(sizeu032, SIZEU032, arb_usize(), arb_u32());
single_sided_props!(sizeu064, SIZEU064, arb_usize(), arb_u64());
single_sided_props!(sizeu128, SIZEU128, arb_usize(), arb_u128());
