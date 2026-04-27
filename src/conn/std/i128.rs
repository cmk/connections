//! Conns landing on `i128`. Per the right-side-wins module rule,
//! this file hosts every Conn whose destination type is `i128`.

use super::ext_int;
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
}
