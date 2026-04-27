//! Conns landing on `u16`. Per the right-side-wins module rule,
//! this file hosts every Conn whose destination type is `u16`.

use super::{int_uint, int_uint_narrow, uint_uint, uint_uint_narrow};
use crate::conn::Conn;

// ── Existing widening ──────────────────────────────────────────────
uint_uint!(U008U016, u8, u16);
int_uint!(I008U016, i8, u16);
int_uint!(I016U016, i16, u16);

// ── §2 U→U narrowing ───────────────────────────────────────────────
uint_uint_narrow!(U032U016, u32, u16);
uint_uint_narrow!(U064U016, u64, u16);
uint_uint_narrow!(U128U016, u128, u16);

// ── §4 I→U narrowing ───────────────────────────────────────────────
int_uint_narrow!(I032U016, i32, u16);
int_uint_narrow!(I064U016, i64, u16);
int_uint_narrow!(I128U016, i128, u16);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn u008u016_ceil_widens_losslessly() {
        assert_eq!(U008U016.ceil(0u8), 0u16);
        assert_eq!(U008U016.ceil(u8::MAX), u8::MAX as u16);
    }

    #[test]
    fn u008u016_inner_saturates_at_source_max() {
        assert_eq!(U008U016.inner(u16::MAX), u8::MAX);
        assert_eq!(U008U016.inner(50), 50);
    }

    #[test]
    fn i016u016_galois_at_mid_positive() {
        // Exercises the active branch (`a >= 0`, ceil widens, inner
        // identity-casts back) — proptest covers this too, but
        // proptest's `any::<iN>()` weights heavily toward boundary
        // values; this fixes a representative middle point.
        for (a, b) in [(50i16, 100u16), (50i16, 49u16), (100i16, 100u16)] {
            assert_eq!(
                I016U016.ceil(a) <= b,
                a <= I016U016.inner(b),
                "I016U016 galois_upper @ ({a}, {b})"
            );
        }
    }

    #[test]
    fn i008u016_inner_saturates() {
        assert_eq!(I008U016.inner(u16::MAX), i8::MAX);
        assert_eq!(I008U016.inner(127), 127);
    }

    // ── Spot checks: U→U narrowing into u16 ────────────────────────

    #[test]
    fn u_to_u16_saturate_and_fixup() {
        assert_eq!(U032U016.ceil(u32::MAX), u16::MAX);
        assert_eq!(U128U016.ceil(u128::MAX), u16::MAX);
        assert_eq!(U032U016.inner(u16::MAX), u32::MAX);
        assert_eq!(U064U016.inner(u16::MAX), u64::MAX);
        assert_eq!(U128U016.inner(u16::MAX), u128::MAX);
        assert_eq!(U032U016.inner(60_000), 60_000_u32);
    }

    // ── Spot checks: I→U narrowing into u16 ───────────────────────

    #[test]
    fn i_to_u16_neg_high_fixup() {
        assert_eq!(I032U016.ceil(-1), 0);
        assert_eq!(I032U016.ceil(i32::MIN), 0);
        assert_eq!(I032U016.ceil(i32::MAX), u16::MAX);
        assert_eq!(I128U016.ceil(i128::MAX), u16::MAX);
        assert_eq!(I032U016.inner(u16::MAX), i32::MAX);
        assert_eq!(I128U016.inner(u16::MAX), i128::MAX);
    }
}
