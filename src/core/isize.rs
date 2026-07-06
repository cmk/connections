//! `isize` → `i8` / `i16` / `i128` pointer-width cast Conns.
//!
//! Unlike [`crate::core::usize`], this family is built from the stock
//! fixed-width macros and is **lawful on every pointer width** (16/32/64),
//! because it ships only the rungs whose cast *direction* is fixed across
//! all targets:
//!
//! - [`ISZEI008`] — `isize → i8`, always a narrowing (`isize ≥ 16 > 8`
//!   bits) → the fixed-width `int_int_narrow!` macro.
//! - [`ISZEI016`] — `isize → i16`, a narrowing on 32/64-bit and the identity
//!   iso on a 16-bit target, never a widening → `int_int_narrow!`.
//! - [`ISZEI128`] — `isize → i128`, always a widening (`i128` is the widest)
//!   → the `ext_int!` macro, with an [`Extended<isize>`] source
//!   (like `I064I128`). Signed widening needs the `Extended` source:
//!   `isize::MIN` embeds *above* `i128::MIN`, leaving unreachable negatives
//!   that `NegInf` / `PosInf` absorb.
//!
//! **`isize → i32` and `isize → i64` are intentionally omitted.** Their cast
//! direction *flips* with pointer width — `→ i32` narrows on 64-bit, is the
//! identity on 32-bit, and *widens* on 16-bit; `→ i64` is the identity on
//! 64-bit and widens on ≤ 32-bit. No single stock-macro const covers a
//! flipping rung (`int_int_narrow!` truncates on the widening target;
//! `ext_int!` overflows computing its `BELOW`/`ABOVE` bounds on the
//! iso/narrowing target), so a portable version needs a bespoke cross-regime
//! `Extended` hybrid. That strategy choice is deferred rather than baked in
//! here.
//!
//! [`Extended<isize>`]: crate::extended::Extended

use crate::core::{ext_int, int_int_narrow};

int_int_narrow!(ISZEI008, isize, i8);
int_int_narrow!(ISZEI016, isize, i16);
ext_int!(ISZEI128, isize, i128);

// ────────────────────────────────────────────────────────────────────
// Tests
// ────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::extended::Extended;
    use crate::prop::conn as conn_laws;
    use proptest::prelude::*;

    // ── Narrowing saturate-both + high-end fixup spot checks ──────────

    #[test]
    fn iszei008_saturates_and_fixes_up() {
        // isize is wider than i8 on every target: ceil saturates at both
        // ends; inner has the high-end FINE_MAX fixup but no low-end one.
        assert_eq!(ISZEI008.ceil(isize::MAX), i8::MAX);
        assert_eq!(ISZEI008.ceil(isize::MIN), i8::MIN);
        assert_eq!(ISZEI008.upper(i8::MAX), isize::MAX); // FINE_MAX fixup
        assert_eq!(ISZEI008.upper(i8::MIN), i8::MIN as isize); // no fixup
        assert_eq!(ISZEI008.ceil(-100), -100);
        assert_eq!(ISZEI008.upper(-100), -100);
    }

    #[test]
    fn iszei016_saturates_and_fixes_up() {
        assert_eq!(ISZEI016.ceil(isize::MAX), i16::MAX);
        assert_eq!(ISZEI016.ceil(isize::MIN), i16::MIN);
        assert_eq!(ISZEI016.upper(i16::MAX), isize::MAX);
        assert_eq!(ISZEI016.upper(i16::MIN), i16::MIN as isize);
        assert_eq!(ISZEI016.ceil(-1_000), -1_000);
        assert_eq!(ISZEI016.upper(-1_000), -1_000);
    }

    // ── Widening (Extended source) spot checks ────────────────────────

    #[test]
    fn iszei128_extends_to_one_above() {
        // Mirrors i064::I064I128: PosInf lands one above the source max,
        // NegInf at the target min, finites embed losslessly.
        assert_eq!(ISZEI128.ceil(Extended::PosInf), (isize::MAX as i128) + 1);
        assert_eq!(ISZEI128.ceil(Extended::NegInf), i128::MIN);
        assert_eq!(ISZEI128.ceil(Extended::Finite(-42)), -42);
        assert_eq!(ISZEI128.upper(-42), Extended::Finite(-42));
    }

    // ── Boundary-biased Galois-law properties ─────────────────────────

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

    proptest! {
        #[test]
        fn iszei008_galois_l(a in arb_isize(), b in arb_i8()) {
            prop_assert!(conn_laws::galois_l(&ISZEI008, a, b));
        }
        #[test]
        fn iszei008_kernel_l(b in arb_i8()) {
            prop_assert!(conn_laws::kernel_l(&ISZEI008, b));
        }
        #[test]
        fn iszei016_galois_l(a in arb_isize(), b in arb_i16()) {
            prop_assert!(conn_laws::galois_l(&ISZEI016, a, b));
        }
        #[test]
        fn iszei016_kernel_l(b in arb_i16()) {
            prop_assert!(conn_laws::kernel_l(&ISZEI016, b));
        }
        #[test]
        fn iszei128_galois_l(a in arb_ext_isize(), b in any::<i128>()) {
            prop_assert!(conn_laws::galois_l(&ISZEI128, a, b));
        }
        #[test]
        fn iszei128_kernel_l(b in any::<i128>()) {
            prop_assert!(conn_laws::kernel_l(&ISZEI128, b));
        }
    }
}
