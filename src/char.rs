//! `char` connections.
//!
//! Houses [`U032CHAR`] — `u32 → char` — projecting a 32-bit codepoint
//! candidate into the validated Unicode range
//! `[0, 0xD7FF] ∪ [0xE000, 0x10FFFF]`. The surrogate gap and the
//! `> 0x10FFFF` overflow are handled by saturating `ceil`. Galois L
//! holds via synthetic-top promotion of `inner('\u{10FFFF}') = u32::MAX`.
//!
//! Per CLAUDE.md § Conn placement, char wins the same-tier tie over
//! `u32` (right wins → coarser side → 21-bit char), so this is the
//! natural module for u32↔char. To compose `u8 → char` from
//! downstream code, lift `u8 → u32 → char` through `Extended` first
//! (`lift_l!(U008U032)` then `compose_l!`-chain with `lift_l!(U032CHAR)`).

const SURROGATE_LO: u32 = 0xD800;
const SURROGATE_HI: u32 = 0xDFFF;
const CHAR_MAX_U32: u32 = 0x10FFFF;

const fn ceil_u32_char(u: u32) -> char {
    if u > CHAR_MAX_U32 {
        '\u{10FFFF}'
    } else if u >= SURROGATE_LO && u <= SURROGATE_HI {
        '\u{E000}'
    } else {
        // u is in [0, 0xD7FF] ∪ [0xE000, 0x10FFFF]; from_u32 is total
        // here. The `match` keeps the body const-eligible (no unwrap).
        match char::from_u32(u) {
            Some(c) => c,
            None => '\u{10FFFF}',
        }
    }
}

const fn inner_char_u32(c: char) -> u32 {
    // Synthetic-top promotion: '\u{10FFFF}' → u32::MAX makes Galois L
    // hold across the `u > 0x10FFFF` saturation arm in `ceil`. The
    // round-trip on the rest of `char` is the natural `c as u32`.
    if c as u32 == CHAR_MAX_U32 {
        u32::MAX
    } else {
        c as u32
    }
}

crate::conn_l! {
    /// `u32 → char` — validated-codepoint projection (left-Galois).
    ///
    /// `inner`: lossless `char → u32` cast on the natural range, with
    /// synthetic-top promotion of `'\u{10FFFF}' → u32::MAX` so that
    /// Galois L holds across the `u > 0x10FFFF` saturation arm.
    ///
    /// `ceil`: smallest `char` whose `u32` embedding is `≥` the input,
    /// saturating to `'\u{10FFFF}'` when `u > 0x10FFFF`. Maps
    /// `u in [0xD800, 0xDFFF]` to `'\u{E000}'` (jump over the
    /// surrogate gap).
    ///
    /// **One-sided.** Shipped as `ConnL` rather than `conn_k!` because
    /// the synthetic-top promotion in `inner` makes the dual adjunction
    /// fail at the top boundary; no `floor` admits the symmetric
    /// `inner ⊣ floor` law.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::char::U032CHAR;
    /// use connections::conn::ConnL;
    ///
    /// // Valid codepoints pass through.
    /// assert_eq!(U032CHAR.ceil('A' as u32), 'A');
    ///
    /// // Surrogate gap: ceil jumps up over [0xD800, 0xDFFF].
    /// assert_eq!(U032CHAR.ceil(0xD800), '\u{E000}');
    ///
    /// // Above CHAR_MAX: ceil saturates at '\u{10FFFF}'.
    /// assert_eq!(U032CHAR.ceil(0x110000), '\u{10FFFF}');
    /// assert_eq!(U032CHAR.ceil(u32::MAX),  '\u{10FFFF}');
    ///
    /// // Synthetic-top promotion: inner('\u{10FFFF}') == u32::MAX.
    /// assert_eq!(U032CHAR.upper('\u{10FFFF}'), u32::MAX);
    /// assert_eq!(U032CHAR.upper('A'),          'A' as u32);
    /// ```
    pub U032CHAR : u32 => char {
        ceil:  ceil_u32_char,
        inner: inner_char_u32,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[allow(unused_imports)]
    use crate::conn::ConnL;
    use crate::prop::arb::{arb_char, arb_u32_char_boundary};

    // ── Spot checks ────────────────────────────────────────────────

    #[test]
    fn surrogate_gap_ceil() {
        for u in [0xD800_u32, 0xD900, 0xDFFF] {
            assert_eq!(U032CHAR.ceil(u), '\u{E000}', "ceil({:#x})", u);
        }
    }

    #[test]
    fn above_max_ceil_saturates() {
        assert_eq!(U032CHAR.ceil(0x110000), '\u{10FFFF}');
        assert_eq!(U032CHAR.ceil(u32::MAX), '\u{10FFFF}');
    }

    #[test]
    fn valid_passthrough() {
        for &c in &['\u{0}', 'A', '\n', '\u{D7FF}', '\u{E000}'] {
            assert_eq!(U032CHAR.ceil(c as u32), c);
            assert_eq!(U032CHAR.upper(c), c as u32);
        }
    }

    #[test]
    fn synthetic_top() {
        // `inner('\u{10FFFF}')` returns `u32::MAX`, not `0x10FFFF`.
        // This is the synthetic-top promotion that lets Galois L hold
        // across the `u > 0x10FFFF` saturation arm in `ceil`.
        assert_eq!(U032CHAR.upper('\u{10FFFF}'), u32::MAX);
        assert_eq!(U032CHAR.ceil(0x10FFFF), '\u{10FFFF}');
    }

    // ── Property tests ─────────────────────────────────────────────

    crate::law_battery! {
        mod laws,
        conn: U032CHAR,
        fine:   arb_u32_char_boundary(),
        coarse: arb_char(),
        subset: l_only,
    }
}
