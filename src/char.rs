//! `char` connections.
//!
//! Houses [`U032CHAR`] — `Extended<u32> → Extended<char>` — projecting
//! a 32-bit codepoint candidate into the validated Unicode range
//! `[0, 0xD7FF] ∪ [0xE000, 0x10FFFF]`. The surrogate gap and the
//! `> 0x10FFFF` overflow are handled by ceil/floor asymmetry; both
//! Galois laws hold over the lattice ordering of `Extended<char>`.
//!
//! Per CLAUDE.md § Conn placement, char wins the same-tier tie over
//! `u32` (right wins → coarser side → 21-bit char), so this is the
//! natural module for u32↔char. To compose into `u8 → char` from
//! downstream code, chain `compose_l!(U008U032.conn_l(), U032CHAR.conn_l())` (or
//! the analogous `_r` chain).

use crate::extended::Extended;

const SURROGATE_LO: u32 = 0xD800;
const SURROGATE_HI: u32 = 0xDFFF;
const CHAR_MAX_U32: u32 = 0x10FFFF;

const fn ceil_u32_char(x: Extended<u32>) -> Extended<char> {
    match x {
        Extended::NegInf => Extended::NegInf,
        Extended::PosInf => Extended::PosInf,
        Extended::Finite(u) => {
            if u > CHAR_MAX_U32 {
                Extended::PosInf
            } else if u >= SURROGATE_LO && u <= SURROGATE_HI {
                Extended::Finite('\u{E000}')
            } else {
                // u is in [0, 0xD7FF] ∪ [0xE000, 0x10FFFF]; from_u32
                // is total here. The `match` handles the unreachable
                // None to keep the body const-eligible (no unwrap).
                match char::from_u32(u) {
                    Some(c) => Extended::Finite(c),
                    None => Extended::PosInf,
                }
            }
        }
    }
}

const fn floor_u32_char(x: Extended<u32>) -> Extended<char> {
    match x {
        Extended::NegInf => Extended::NegInf,
        Extended::PosInf => Extended::PosInf,
        Extended::Finite(u) => {
            if u > CHAR_MAX_U32 {
                Extended::Finite('\u{10FFFF}')
            } else if u >= SURROGATE_LO && u <= SURROGATE_HI {
                Extended::Finite('\u{D7FF}')
            } else {
                match char::from_u32(u) {
                    Some(c) => Extended::Finite(c),
                    None => Extended::NegInf,
                }
            }
        }
    }
}

const fn inner_char_u32(c: Extended<char>) -> Extended<u32> {
    match c {
        Extended::NegInf => Extended::NegInf,
        Extended::PosInf => Extended::PosInf,
        Extended::Finite(c) => Extended::Finite(c as u32),
    }
}

crate::conn_k! {
    /// `Extended<u32> → Extended<char>` — validated-codepoint projection.
    ///
    /// `inner`: lossless `char → u32` cast (`NegInf`/`PosInf` pass
    /// through; `Finite(c)` casts `c as u32`).
    ///
    /// `ceil`: smallest `char` whose `u32` embedding is `≥` the input.
    /// Maps `u in [0xD800, 0xDFFF]` to `Finite('\u{E000}')` (jump over
    /// the surrogate gap) and `u > 0x10FFFF` to `PosInf` (saturate
    /// above the Unicode max).
    ///
    /// `floor`: largest `char` whose `u32` embedding is `≤` the input.
    /// Maps `u in [0xD800, 0xDFFF]` to `Finite('\u{D7FF}')` and any
    /// `u > 0x10FFFF` to `Finite('\u{10FFFF}')`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::char::U032CHAR;
    /// use connections::conn::{ConnL, ConnR};
    /// use connections::extended::Extended;
    ///
    /// // Valid codepoints pass through.
    /// assert_eq!(U032CHAR.ceil(Extended::Finite('A' as u32)), Extended::Finite('A'));
    /// assert_eq!(U032CHAR.floor(Extended::Finite('A' as u32)), Extended::Finite('A'));
    ///
    /// // Surrogate gap: ceil jumps up, floor jumps down.
    /// assert_eq!(U032CHAR.ceil(Extended::Finite(0xD800)), Extended::Finite('\u{E000}'));
    /// assert_eq!(U032CHAR.floor(Extended::Finite(0xD800)), Extended::Finite('\u{D7FF}'));
    ///
    /// // Above CHAR_MAX: ceil → PosInf, floor → Finite(CHAR_MAX).
    /// assert_eq!(U032CHAR.ceil(Extended::Finite(0x110000)), Extended::PosInf);
    /// assert_eq!(U032CHAR.floor(Extended::Finite(0x110000)), Extended::Finite('\u{10FFFF}'));
    /// ```
    pub U032CHAR : Extended<u32> => Extended<char> {
        ceil:  ceil_u32_char,
        inner: inner_char_u32,
        floor: floor_u32_char,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[allow(unused_imports)]
    use crate::conn::{ConnL, ConnR};
    use crate::prop::arb::{arb_extended_char, arb_extended_u32};
    use crate::prop::conn as conn_laws;
    use proptest::prelude::*;

    // ── Spot checks ────────────────────────────────────────────────

    #[test]
    fn surrogate_gap_ceil() {
        for u in [0xD800_u32, 0xD900, 0xDFFF] {
            assert_eq!(
                U032CHAR.ceil(Extended::Finite(u)),
                Extended::Finite('\u{E000}'),
                "ceil({:#x})",
                u
            );
        }
    }

    #[test]
    fn surrogate_gap_floor() {
        for u in [0xD800_u32, 0xD900, 0xDFFF] {
            assert_eq!(
                U032CHAR.floor(Extended::Finite(u)),
                Extended::Finite('\u{D7FF}'),
                "floor({:#x})",
                u
            );
        }
    }

    #[test]
    fn beyond_max_ceil() {
        assert_eq!(U032CHAR.ceil(Extended::Finite(0x110000)), Extended::PosInf);
        assert_eq!(U032CHAR.ceil(Extended::Finite(u32::MAX)), Extended::PosInf);
    }

    #[test]
    fn beyond_max_floor() {
        assert_eq!(
            U032CHAR.floor(Extended::Finite(0x110000)),
            Extended::Finite('\u{10FFFF}')
        );
        assert_eq!(
            U032CHAR.floor(Extended::Finite(u32::MAX)),
            Extended::Finite('\u{10FFFF}')
        );
    }

    #[test]
    fn valid_passthrough() {
        for &c in &['\u{0}', 'A', '\n', '\u{D7FF}', '\u{E000}', '\u{10FFFF}'] {
            assert_eq!(
                U032CHAR.ceil(Extended::Finite(c as u32)),
                Extended::Finite(c)
            );
            assert_eq!(
                U032CHAR.floor(Extended::Finite(c as u32)),
                Extended::Finite(c)
            );
            assert_eq!(
                U032CHAR.upper(Extended::Finite(c)),
                Extended::Finite(c as u32)
            );
        }
    }

    #[test]
    fn extremes_pass_through() {
        assert_eq!(U032CHAR.ceil(Extended::NegInf), Extended::NegInf);
        assert_eq!(U032CHAR.floor(Extended::NegInf), Extended::NegInf);
        assert_eq!(U032CHAR.ceil(Extended::PosInf), Extended::PosInf);
        assert_eq!(U032CHAR.floor(Extended::PosInf), Extended::PosInf);
        assert_eq!(U032CHAR.upper(Extended::NegInf), Extended::NegInf);
        assert_eq!(U032CHAR.upper(Extended::PosInf), Extended::PosInf);
    }

    // ── Property tests ─────────────────────────────────────────────

    crate::law_battery! {
        mod laws,
        conn: U032CHAR,
        fine:   arb_extended_u32(),
        coarse: arb_extended_char(),
    }

    // `floor_le_ceil` isn't part of the law_battery!(full) set
    // (ConnK-bound rather than per-side) — kept as a standalone
    // proptest below.
    proptest! {
        #[test]
        fn floor_le_ceil(a in arb_extended_u32()) {
            prop_assert!(conn_laws::floor_le_ceil(&U032CHAR, a));
        }
    }
}
