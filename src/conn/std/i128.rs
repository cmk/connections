//! Conns landing on `i128`. Per the right-side-wins module rule,
//! this file hosts every Conn whose destination type is `i128`.

use super::{ext_int, uint_int_sat};
use crate::conn::Conn;
use crate::extended::Extended;

// ── Existing widening (Extended source) ────────────────────────────
ext_int!(I008I128, i8, i128);
ext_int!(I016I128, i16, i128);
ext_int!(I032I128, i32, i128);
ext_int!(I064I128, i64, i128);
ext_int!(U008I128, u8, i128);
ext_int!(U016I128, u16, i128);
ext_int!(U032I128, u32, i128);
ext_int!(U064I128, u64, i128);

// ── §3 U→I non-widening ────────────────────────────────────────────
uint_int_sat!(U128I128, u128, i128);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn i064i128_extends_to_one_below_above() {
        assert_eq!(I064I128.floor(Extended::NegInf), (i64::MIN as i128) - 1);
        assert_eq!(I064I128.ceil(Extended::PosInf), (i64::MAX as i128) + 1);
    }

    #[test]
    fn u064i128_extends_to_one_above() {
        assert_eq!(U064I128.ceil(Extended::PosInf), (u64::MAX as i128) + 1);
        assert_eq!(U064I128.floor(Extended::NegInf), -1);
    }

    // ── Spot checks: U→I non-widening into i128 ──────────────────

    #[test]
    fn u128i128_neg_and_high() {
        assert_eq!(U128I128.inner(-1), 0_u128);
        assert_eq!(U128I128.inner(i128::MIN), 0_u128);
        assert_eq!(U128I128.floor(u128::MAX), i128::MAX);
        // Round-trip in [0, i128::MAX]:
        assert_eq!(U128I128.floor(U128I128.inner(50)), 50);
        assert_eq!(U128I128.floor(U128I128.inner(i128::MAX)), i128::MAX);
    }
}
