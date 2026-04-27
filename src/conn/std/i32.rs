//! Conns landing on `i32`. Per the right-side-wins module rule,
//! this file hosts every Conn whose destination type is `i32`.

use super::{ext_int, int_int_narrow};
use crate::conn::Conn;
use crate::extended::Extended;

// ── Existing widening (Extended source) ────────────────────────────
ext_int!(I008I032, i8, i32);
ext_int!(I016I032, i16, i32);
ext_int!(U008I032, u8, i32);
ext_int!(U016I032, u16, i32);

// ── §1 I→I narrowing ───────────────────────────────────────────────
int_int_narrow!(I064I032, i64, i32);
int_int_narrow!(I128I032, i128, i32);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn i008i032_round_trip_at_finite_boundaries() {
        assert_eq!(I008I032.ceil(Extended::Finite(i8::MIN)), -128);
        assert_eq!(I008I032.ceil(Extended::Finite(i8::MAX)), 127);
        assert_eq!(I008I032.inner(-128), Extended::Finite(i8::MIN));
        assert_eq!(I008I032.inner(127), Extended::Finite(i8::MAX));
    }

    #[test]
    fn u016i032_inner_partitions() {
        assert_eq!(U016I032.inner(-1), Extended::NegInf);
        assert_eq!(U016I032.inner(0), Extended::Finite(0));
        assert_eq!(U016I032.inner(65_535), Extended::Finite(u16::MAX));
        assert_eq!(U016I032.inner(65_536), Extended::PosInf);
    }

    // ── Spot checks: I→I narrowing into i32 ────────────────────────

    #[test]
    fn i_to_i32_saturate() {
        assert_eq!(I064I032.ceil(i64::MAX), i32::MAX);
        assert_eq!(I064I032.ceil(i64::MIN), i32::MIN);
        assert_eq!(I128I032.ceil(i128::MAX), i32::MAX);
        assert_eq!(I128I032.ceil(i128::MIN), i32::MIN);
    }

    #[test]
    fn i_to_i32_inner_fine_max_fixup() {
        assert_eq!(I064I032.inner(i32::MAX), i64::MAX);
        assert_eq!(I128I032.inner(i32::MAX), i128::MAX);
    }
}
