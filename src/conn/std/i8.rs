//! Conns landing on `i8`. Per the right-side-wins module rule, this
//! file hosts every Conn whose destination type is `i8`.
//!
//! - **`I??I008`** narrowing (T3): wider signed → `i8` saturating
//!   cast (`int_int_narrow!`).
//! - **`U??I008`** non-widening (T5): unsigned source → `i8` with
//!   negative-clip on `inner` (`uint_int_sat!`, right-Galois).
//!
//! No widening lands here: `i8` is the narrowest signed primitive,
//! so nothing widens *into* it.

use super::int_int_narrow;
use crate::conn::Conn;

// ── §1 I→I narrowing ───────────────────────────────────────────────
int_int_narrow!(I016I008, i16, i8);
int_int_narrow!(I032I008, i32, i8);
int_int_narrow!(I064I008, i64, i8);
int_int_narrow!(I128I008, i128, i8);

#[cfg(test)]
mod tests {
    use super::*;

    // ── Spot checks: I→I narrowing ─────────────────────────────────

    #[test]
    fn i_to_i_saturate_high() {
        assert_eq!(I016I008.ceil(i16::MAX), i8::MAX);
        assert_eq!(I032I008.ceil(i32::MAX), i8::MAX);
        assert_eq!(I064I008.ceil(i64::MAX), i8::MAX);
        assert_eq!(I128I008.ceil(i128::MAX), i8::MAX);
    }

    #[test]
    fn i_to_i_saturate_low() {
        assert_eq!(I016I008.ceil(i16::MIN), i8::MIN);
        assert_eq!(I032I008.ceil(i32::MIN), i8::MIN);
        assert_eq!(I064I008.ceil(i64::MIN), i8::MIN);
        assert_eq!(I128I008.ceil(i128::MIN), i8::MIN);
    }

    #[test]
    fn i_to_i_round_trip_finite() {
        // Values inside i8's range pass through unchanged.
        for &b in &[i8::MIN, -1, 0, 1, i8::MAX] {
            assert_eq!(I016I008.ceil(I016I008.inner(b)), b);
            assert_eq!(I032I008.ceil(I032I008.inner(b)), b);
            assert_eq!(I064I008.ceil(I064I008.inner(b)), b);
            assert_eq!(I128I008.ceil(I128I008.inner(b)), b);
        }
    }

    #[test]
    fn i_to_i_inner_fine_max_fixup() {
        // FINE_MAX fixup: inner(i_N::MAX) = i_M::MAX so galois_l holds
        // at the source-side high plateau.
        assert_eq!(I016I008.inner(i8::MAX), i16::MAX);
        assert_eq!(I032I008.inner(i8::MAX), i32::MAX);
        assert_eq!(I064I008.inner(i8::MAX), i64::MAX);
        assert_eq!(I128I008.inner(i8::MAX), i128::MAX);
        // Below the fixup, inner is the lossless widen.
        assert_eq!(I016I008.inner(126), 126_i16);
        assert_eq!(I016I008.inner(i8::MIN), i8::MIN as i16);
    }
}
