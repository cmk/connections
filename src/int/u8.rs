//! Conns landing on `u8`. Per the right-side-wins module rule, this
//! file hosts every Conn whose destination type is `u8`.
//!
//! - **`I008U008`** — `i8 → u8` cross-sign saturating cast (existing
//!   `int_uint!`).
//! - **`I??U008`** narrowing (T6): wider signed → `u8` saturating
//!   cast (`int_uint_narrow!`).
//! - **`U??U008`** narrowing (T4): wider unsigned → `u8` saturating
//!   cast (`uint_uint_narrow!`).
//!
//! No widening lands here: `u8` is the narrowest unsigned primitive.

use super::{int_uint, int_uint_narrow, uint_uint_narrow};
use crate::conn::Conn;

// ── Existing same-width cross-sign ─────────────────────────────────
int_uint!(I008U008, i8, u8);

// ── §2 U→U narrowing ───────────────────────────────────────────────
uint_uint_narrow!(U016U008, u16, u8);
uint_uint_narrow!(U032U008, u32, u8);
uint_uint_narrow!(U064U008, u64, u8);
uint_uint_narrow!(U128U008, u128, u8);

// ── §4 I→U narrowing ───────────────────────────────────────────────
int_uint_narrow!(I016U008, i16, u8);
int_uint_narrow!(I032U008, i32, u8);
int_uint_narrow!(I064U008, i64, u8);
int_uint_narrow!(I128U008, i128, u8);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn i008u008_ceil_clips_negatives_to_zero() {
        assert_eq!(I008U008.ceil(-5), 0);
        assert_eq!(I008U008.ceil(i8::MIN), 0);
    }

    #[test]
    fn i008u008_ceil_passes_non_negative() {
        assert_eq!(I008U008.ceil(0), 0);
        assert_eq!(I008U008.ceil(127), 127);
    }

    #[test]
    fn i008u008_inner_saturates_at_source_max() {
        assert_eq!(I008U008.inner(u8::MAX), i8::MAX);
        assert_eq!(I008U008.inner(127), 127);
        assert_eq!(I008U008.inner(50), 50);
    }

    // ── Spot checks: U→U narrowing into u8 ─────────────────────────

    #[test]
    fn u_to_u8_saturate() {
        assert_eq!(U016U008.ceil(u16::MAX), u8::MAX);
        assert_eq!(U032U008.ceil(u32::MAX), u8::MAX);
        assert_eq!(U064U008.ceil(u64::MAX), u8::MAX);
        assert_eq!(U128U008.ceil(u128::MAX), u8::MAX);
    }

    #[test]
    fn u_to_u8_inner_fine_max_fixup() {
        assert_eq!(U016U008.inner(u8::MAX), u16::MAX);
        assert_eq!(U032U008.inner(u8::MAX), u32::MAX);
        assert_eq!(U064U008.inner(u8::MAX), u64::MAX);
        assert_eq!(U128U008.inner(u8::MAX), u128::MAX);
        // Below the fixup, lossless widen.
        assert_eq!(U016U008.inner(0), 0_u16);
        assert_eq!(U016U008.inner(254), 254_u16);
    }

    // ── Spot checks: I→U narrowing into u8 ────────────────────────

    #[test]
    fn i_to_u8_neg_clip() {
        assert_eq!(I016U008.ceil(-1), 0);
        assert_eq!(I016U008.ceil(i16::MIN), 0);
        assert_eq!(I128U008.ceil(i128::MIN), 0);
    }

    #[test]
    fn i_to_u8_high_saturate() {
        assert_eq!(I016U008.ceil(i16::MAX), u8::MAX);
        assert_eq!(I032U008.ceil(i32::MAX), u8::MAX);
        assert_eq!(I128U008.ceil(i128::MAX), u8::MAX);
    }

    #[test]
    fn i_to_u8_inner_fine_max_fixup() {
        assert_eq!(I016U008.inner(u8::MAX), i16::MAX);
        assert_eq!(I128U008.inner(u8::MAX), i128::MAX);
        assert_eq!(I016U008.inner(0), 0_i16);
        assert_eq!(I016U008.inner(100), 100_i16);
    }
}
