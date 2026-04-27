//! Conns landing on `i64`. Per the right-side-wins module rule,
//! this file hosts every Conn whose destination type is `i64`.

use super::{ext_int, int_int_narrow, uint_int_sat};
use crate::conn::Conn;
use crate::extended::Extended;

// ── Existing widening (Extended source) ────────────────────────────
ext_int!(I008I064, i8, i64);
ext_int!(I016I064, i16, i64);
ext_int!(I032I064, i32, i64);
ext_int!(U008I064, u8, i64);
ext_int!(U016I064, u16, i64);
ext_int!(U032I064, u32, i64);

// ── §1 I→I narrowing ───────────────────────────────────────────────
int_int_narrow!(I128I064, i128, i64);

// ── §3 U→I non-widening ────────────────────────────────────────────
uint_int_sat!(U064I064, u64, i64);
uint_int_sat!(U128I064, u128, i64);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn i032i064_extends_to_one_below_above() {
        assert_eq!(I032I064.floor(Extended::NegInf), (i32::MIN as i64) - 1);
        assert_eq!(I032I064.ceil(Extended::PosInf), (i32::MAX as i64) + 1);
    }

    #[test]
    fn u032i064_extends_to_one_above() {
        assert_eq!(U032I064.ceil(Extended::PosInf), 4_294_967_296);
        assert_eq!(U032I064.floor(Extended::NegInf), -1);
    }

    // ── Spot checks: I→I narrowing into i64 ────────────────────────

    #[test]
    fn i128i064_saturate_and_fixup() {
        assert_eq!(I128I064.ceil(i128::MAX), i64::MAX);
        assert_eq!(I128I064.ceil(i128::MIN), i64::MIN);
        assert_eq!(I128I064.inner(i64::MAX), i128::MAX);
        assert_eq!(I128I064.inner(i64::MIN), i64::MIN as i128);
    }

    // ── Spot checks: U→I non-widening into i64 ────────────────────

    #[test]
    fn u_to_i64_neg_and_high() {
        assert_eq!(U064I064.inner(-1), 0_u64);
        assert_eq!(U064I064.floor(u64::MAX), i64::MAX);
        assert_eq!(U128I064.inner(i64::MIN), 0_u128);
        assert_eq!(U128I064.floor(u128::MAX), i64::MAX);
    }
}
