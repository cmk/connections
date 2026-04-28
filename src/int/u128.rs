//! Conns landing on `u128`. Per the right-side-wins module rule,
//! this file hosts every Conn whose destination type is `u128`.

use super::{int_uint, uint_uint};
use crate::conn::Conn;

// ── Existing widening ──────────────────────────────────────────────
uint_uint!(U008U128, u8, u128);
uint_uint!(U016U128, u16, u128);
uint_uint!(U032U128, u32, u128);
uint_uint!(U064U128, u64, u128);
int_uint!(I008U128, i8, u128);
int_uint!(I016U128, i16, u128);
int_uint!(I032U128, i32, u128);
int_uint!(I064U128, i64, u128);
int_uint!(I128U128, i128, u128);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn u064u128_inner_saturates_at_source_max() {
        assert_eq!(U064U128.inner(u128::MAX), u64::MAX);
    }

    #[test]
    fn i128u128_at_extremes() {
        assert_eq!(I128U128.ceil(i128::MIN), 0);
        assert_eq!(I128U128.ceil(i128::MAX), i128::MAX as u128);
        assert_eq!(I128U128.inner(u128::MAX), i128::MAX);
    }
}
