//! Conns landing on `u64`. Per the right-side-wins module rule,
//! this file hosts every Conn whose destination type is `u64`.

use super::{int_uint, uint_uint, uint_uint_narrow};
use crate::conn::Conn;

// ── Existing widening ──────────────────────────────────────────────
uint_uint!(U008U064, u8, u64);
uint_uint!(U016U064, u16, u64);
uint_uint!(U032U064, u32, u64);
int_uint!(I008U064, i8, u64);
int_uint!(I016U064, i16, u64);
int_uint!(I032U064, i32, u64);
int_uint!(I064U064, i64, u64);

// ── §2 U→U narrowing ───────────────────────────────────────────────
uint_uint_narrow!(U128U064, u128, u64);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn u032u064_inner_saturates_at_source_max() {
        assert_eq!(U032U064.inner(u64::MAX), u32::MAX);
    }

    #[test]
    fn i064u064_at_extremes() {
        assert_eq!(I064U064.ceil(i64::MIN), 0);
        assert_eq!(I064U064.ceil(i64::MAX), i64::MAX as u64);
        assert_eq!(I064U064.inner(u64::MAX), i64::MAX);
    }

    // ── Spot checks: U→U narrowing into u64 ────────────────────────

    #[test]
    fn u128u064_saturate_and_fixup() {
        assert_eq!(U128U064.ceil(u128::MAX), u64::MAX);
        assert_eq!(U128U064.inner(u64::MAX), u128::MAX);
        assert_eq!(U128U064.inner(0), 0_u128);
    }
}
