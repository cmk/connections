//! Conns landing on `u8`. Per the right-side-wins module rule, this
//! file hosts every Conn whose destination type is `u8`.
//!
//! - **`I008U008`** — `i8 → u8` cross-sign saturating cast (existing
//!   `int_uint!`).
//! - **`I??U008`** narrowing (T6): wider signed → `u8` saturating
//!   cast (`int_uint_narrow!`).
//! - **`U??U008`** narrowing (T4): wider unsigned → `u8` saturating
//!   cast (`uint_uint_narrow!`).
//!
//! No widening lands here: `u8` is the narrowest unsigned primitive.

use super::int_uint;
use crate::conn::Conn;

// ── Existing same-width cross-sign ─────────────────────────────────
int_uint!(I008U008, i8, u8);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn i008u008_ceil_clips_negatives_to_zero() {
        assert_eq!(I008U008.ceil(-5), 0);
        assert_eq!(I008U008.ceil(i8::MIN), 0);
    }

    #[test]
    fn i008u008_ceil_passes_non_negative() {
        assert_eq!(I008U008.ceil(0), 0);
        assert_eq!(I008U008.ceil(127), 127);
    }

    #[test]
    fn i008u008_inner_saturates_at_source_max() {
        assert_eq!(I008U008.inner(u8::MAX), i8::MAX);
        assert_eq!(I008U008.inner(127), 127);
        assert_eq!(I008U008.inner(50), 50);
    }
}
