//! Conns landing on `u16`. Per the right-side-wins module rule,
//! this file hosts every Conn whose destination type is `u16`.

use super::{int_uint, uint_uint};
use crate::conn::Conn;

// ── Existing widening ──────────────────────────────────────────────
uint_uint!(U008U016, u8, u16);
int_uint!(I008U016, i8, u16);
int_uint!(I016U016, i16, u16);

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
}
