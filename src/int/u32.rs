//! Conns landing on `u32`. Per the right-side-wins module rule,
//! this file hosts every Conn whose destination type is `u32`.

use super::{int_uint, int_uint_narrow, uint_uint, uint_uint_narrow};
use crate::conn::Conn;

// ── Existing widening ──────────────────────────────────────────────
uint_uint!(U008U032, u8, u32);
uint_uint!(U016U032, u16, u32);
int_uint!(I008U032, i8, u32);
int_uint!(I016U032, i16, u32);
int_uint!(I032U032, i32, u32);

// ── §2 U→U narrowing ───────────────────────────────────────────────
uint_uint_narrow!(U064U032, u64, u32);
uint_uint_narrow!(U128U032, u128, u32);

// ── §4 I→U narrowing ───────────────────────────────────────────────
int_uint_narrow!(I064U032, i64, u32);
int_uint_narrow!(I128U032, i128, u32);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn u016u032_inner_saturates_at_source_max() {
        assert_eq!(U016U032.inner(u32::MAX), u16::MAX);
        assert_eq!(U016U032.inner(60_000), 60_000);
    }

    #[test]
    fn i016u032_clips_negatives() {
        assert_eq!(I016U032.ceil(-32_768), 0);
        assert_eq!(I016U032.ceil(32_767), 32_767);
    }

    #[test]
    fn i032u032_inner_saturates() {
        assert_eq!(I032U032.inner(u32::MAX), i32::MAX);
        assert_eq!(I032U032.inner(20_000), 20_000);
    }

    // ── Spot checks: U→U narrowing into u32 ────────────────────────

    #[test]
    fn u_to_u32_saturate_and_fixup() {
        assert_eq!(U064U032.ceil(u64::MAX), u32::MAX);
        assert_eq!(U128U032.ceil(u128::MAX), u32::MAX);
        assert_eq!(U064U032.inner(u32::MAX), u64::MAX);
        assert_eq!(U128U032.inner(u32::MAX), u128::MAX);
    }

    // ── Spot checks: I→U narrowing into u32 ───────────────────────

    #[test]
    fn i_to_u32_neg_high_fixup() {
        assert_eq!(I064U032.ceil(-1), 0);
        assert_eq!(I064U032.ceil(i64::MAX), u32::MAX);
        assert_eq!(I128U032.ceil(i128::MIN), 0);
        assert_eq!(I064U032.inner(u32::MAX), i64::MAX);
        assert_eq!(I128U032.inner(u32::MAX), i128::MAX);
    }
}
