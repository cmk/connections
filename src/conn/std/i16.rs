//! Conns landing on `i16`. Per the right-side-wins module rule,
//! this file hosts every Conn whose destination type is `i16`.

use super::ext_int;
use crate::conn::Conn;
use crate::extended::Extended;

// ── Existing widening (Extended source) ────────────────────────────
ext_int!(I008I016, i8, i16);
ext_int!(U008I016, u8, i16);

#[cfg(test)]
mod tests {
    use super::*;

    // ── Spot checks: I008I016 ─────────────────────────────────────

    #[test]
    fn i008i016_ceil_at_boundaries() {
        // NegInf saturates to target MIN.
        assert_eq!(I008I016.ceil(Extended::NegInf), i16::MIN);
        // PosInf goes to "one above source max".
        assert_eq!(I008I016.ceil(Extended::PosInf), 128);
        // Finite passes through with sign.
        assert_eq!(I008I016.ceil(Extended::Finite(0)), 0);
        assert_eq!(I008I016.ceil(Extended::Finite(i8::MIN)), -128);
        assert_eq!(I008I016.ceil(Extended::Finite(i8::MAX)), 127);
    }

    #[test]
    fn i008i016_floor_at_boundaries() {
        // NegInf goes to "one below source min".
        assert_eq!(I008I016.floor(Extended::NegInf), -129);
        // PosInf saturates to target MAX.
        assert_eq!(I008I016.floor(Extended::PosInf), i16::MAX);
    }

    #[test]
    fn i008i016_inner_partitions_target_range() {
        // x ≤ below → NegInf
        assert_eq!(I008I016.inner(-129), Extended::NegInf);
        assert_eq!(I008I016.inner(i16::MIN), Extended::NegInf);
        // x ≥ above → PosInf
        assert_eq!(I008I016.inner(128), Extended::PosInf);
        assert_eq!(I008I016.inner(i16::MAX), Extended::PosInf);
        // -128 ≤ x ≤ 127 → Finite
        assert_eq!(I008I016.inner(-128), Extended::Finite(i8::MIN));
        assert_eq!(I008I016.inner(0), Extended::Finite(0));
        assert_eq!(I008I016.inner(127), Extended::Finite(i8::MAX));
    }

    // ── Spot checks: U008I016 ─────────────────────────────────────

    #[test]
    fn u008i016_ceil_at_boundaries() {
        assert_eq!(U008I016.ceil(Extended::NegInf), i16::MIN);
        assert_eq!(U008I016.ceil(Extended::PosInf), 256);
        assert_eq!(U008I016.ceil(Extended::Finite(0)), 0);
        assert_eq!(U008I016.ceil(Extended::Finite(255)), 255);
    }

    #[test]
    fn u008i016_floor_at_boundaries() {
        assert_eq!(U008I016.floor(Extended::NegInf), -1);
        assert_eq!(U008I016.floor(Extended::PosInf), i16::MAX);
        assert_eq!(U008I016.floor(Extended::Finite(255)), 255);
    }

    #[test]
    fn u008i016_inner_partitions_target_range() {
        assert_eq!(U008I016.inner(-1), Extended::NegInf);
        assert_eq!(U008I016.inner(i16::MIN), Extended::NegInf);
        assert_eq!(U008I016.inner(256), Extended::PosInf);
        assert_eq!(U008I016.inner(i16::MAX), Extended::PosInf);
        assert_eq!(U008I016.inner(0), Extended::Finite(0));
        assert_eq!(U008I016.inner(50), Extended::Finite(50));
        assert_eq!(U008I016.inner(255), Extended::Finite(255));
    }
}
