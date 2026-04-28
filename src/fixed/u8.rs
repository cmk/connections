//! Binary fixed-point ladder over `fixed::FixedU8<Frac>`.
//!
//! Frac level set: `{U0, U1, U2, U3, U4, U6, U7, U8}` → 28 ordered pairs
//! `(Fine, Coarse)` with `Fine > Coarse`. Mirrors [`super::i8`] with two
//! adaptations:
//!
//! - The backing type is `FixedU8<Frac>` (u8) instead of `FixedI8<Frac>`
//!   (i8). Inner widens through u16 (next-larger unsigned).
//! - The signed `if x.to_bits() == FINE_MIN { return Coarse::MIN; }`
//!   guard in `ceil` is unnecessary — unsigned has no negative range.
//!   The `floor(FINE_MAX) = Coarse::MAX` guard remains, for the same
//!   Galois-law reason as in the signed module: `inner` saturates at
//!   `u8::MAX`, so floor at the saturation plateau must return
//!   `Coarse::MAX` to keep the lower adjoint lawful.
//!
//! `U7` (= Q1.7) is the canonical 7-bit MIDI velocity / 7-bit DSP
//! amplitude format, included alongside the mirror-of-signed levels.

use super::{int_uint, int_uint_narrow, uint_uint_narrow};
use crate::conn::Conn;
use ::fixed::FixedU8;
use ::fixed::types::extra::{U0, U1, U2, U3, U4, U6, U7, U8, Unsigned};

// ── §1 std-int Conns landing on `u8` ────────────────────────────────
//
// `u8` is the narrowest unsigned primitive — nothing widens *into* it.
// Same-width cross-sign clip (`I008U008`), U→U narrowing
// (`uint_uint_narrow!`), and I→U narrowing (`int_uint_narrow!`).

int_uint!(I008U008, i8, u8);

uint_uint_narrow!(U016U008, u16, u8);
uint_uint_narrow!(U032U008, u32, u8);
uint_uint_narrow!(U064U008, u64, u8);
uint_uint_narrow!(U128U008, u128, u8);

int_uint_narrow!(I016U008, i16, u8);
int_uint_narrow!(I032U008, i32, u8);
int_uint_narrow!(I064U008, i64, u8);
int_uint_narrow!(I128U008, i128, u8);

// ── §2 Q-format ladder over `FixedU8<Frac>` ─────────────────────────

/// `U<frac> = FixedU8<U<frac>>` — u8-backed binary fixed-point with
/// `<frac>` fractional bits. Frac digits are zero-padded to 3 chars
/// to fit the X123Y456 conn-name shape.
pub type U000 = FixedU8<U0>;
pub type U001 = FixedU8<U1>;
pub type U002 = FixedU8<U2>;
pub type U003 = FixedU8<U3>;
pub type U004 = FixedU8<U4>;
pub type U006 = FixedU8<U6>;
pub type U007 = FixedU8<U7>;
pub type U008 = FixedU8<U8>;

macro_rules! fix_fix_u8 {
    ($const_name:ident, $FineFrac:ty, $CoarseFrac:ty) => {
#[rustfmt::skip]
        #[doc = concat!(
            "`FixedU8<",
            stringify!($FineFrac),
            "> → FixedU8<",
            stringify!($CoarseFrac),
            ">` frac-level convert (u8-backed)."
        )]
        pub const $const_name: Conn<FixedU8<$FineFrac>, FixedU8<$CoarseFrac>> = {
            const SHIFT: u32 = <$FineFrac as Unsigned>::U32 - <$CoarseFrac as Unsigned>::U32;
            // u16 covers SHIFT ∈ [1, 8]: 1 << 8 = 256 fits, and
            // u8::MAX × 256 = 65 280 < u16::MAX = 65 535.
            const RATIO: u16 = 1_u16 << SHIFT;
            const FINE_MAX: u8 = u8::MAX;

            fn ceil(x: FixedU8<$FineFrac>) -> FixedU8<$CoarseFrac> {
                let bits = x.to_bits() as u16;
                let q = bits / RATIO;
                let r = bits % RATIO;
                // `res ≤ ⌈bits / RATIO⌉ ≤ ⌈u8::MAX / 2⌉ = 128` since
                // RATIO ≥ 2 (Fine has more frac bits than Coarse, so
                // SHIFT ≥ 1). The `as u8` cast is therefore lossless.
                let res = if r != 0 { q + 1 } else { q };
                FixedU8::from_bits(res as u8)
            }

            fn inner(x: FixedU8<$CoarseFrac>) -> FixedU8<$FineFrac> {
                let res = (x.to_bits() as u16) * RATIO;
                let saturated = if res > FINE_MAX as u16 {
                    FINE_MAX
                } else {
                    res as u8
                };
                FixedU8::from_bits(saturated)
            }

            fn floor(x: FixedU8<$FineFrac>) -> FixedU8<$CoarseFrac> {
                if x.to_bits() == FINE_MAX {
                    return FixedU8::<$CoarseFrac>::from_bits(u8::MAX);
                }
                let res = (x.to_bits() as u16) / RATIO;
                FixedU8::from_bits(res as u8)
            }

            Conn::new(ceil, inner, floor)
        };
    };
}

// 28 ordered pairs from {U0, U1, U2, U3, U4, U6, U7, U8}.
fix_fix_u8!(Q001Q000, U1, U0);
fix_fix_u8!(Q002Q000, U2, U0);
fix_fix_u8!(Q003Q000, U3, U0);
fix_fix_u8!(Q004Q000, U4, U0);
fix_fix_u8!(Q006Q000, U6, U0);
fix_fix_u8!(Q007Q000, U7, U0);
fix_fix_u8!(Q008Q000, U8, U0);
fix_fix_u8!(Q002Q001, U2, U1);
fix_fix_u8!(Q003Q001, U3, U1);
fix_fix_u8!(Q004Q001, U4, U1);
fix_fix_u8!(Q006Q001, U6, U1);
fix_fix_u8!(Q007Q001, U7, U1);
fix_fix_u8!(Q008Q001, U8, U1);
fix_fix_u8!(Q003Q002, U3, U2);
fix_fix_u8!(Q004Q002, U4, U2);
fix_fix_u8!(Q006Q002, U6, U2);
fix_fix_u8!(Q007Q002, U7, U2);
fix_fix_u8!(Q008Q002, U8, U2);
fix_fix_u8!(Q004Q003, U4, U3);
fix_fix_u8!(Q006Q003, U6, U3);
fix_fix_u8!(Q007Q003, U7, U3);
fix_fix_u8!(Q008Q003, U8, U3);
fix_fix_u8!(Q006Q004, U6, U4);
fix_fix_u8!(Q007Q004, U7, U4);
fix_fix_u8!(Q008Q004, U8, U4);
fix_fix_u8!(Q007Q006, U7, U6);
fix_fix_u8!(Q008Q006, U8, U6);
fix_fix_u8!(Q008Q007, U8, U7);

// ────────────────────────────────────────────────────────────────────
// Tests
// ────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    // ── §1 std-int spot checks (merged from former int/u8.rs) ──────

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

    #[test]
    fn u_to_u8_saturate() {
        assert_eq!(U016U008.ceil(u16::MAX), u8::MAX);
        assert_eq!(U032U008.ceil(u32::MAX), u8::MAX);
        assert_eq!(U064U008.ceil(u64::MAX), u8::MAX);
        assert_eq!(U128U008.ceil(u128::MAX), u8::MAX);
    }

    #[test]
    fn u_to_u8_inner_fine_max_fixup() {
        assert_eq!(U016U008.inner(u8::MAX), u16::MAX);
        assert_eq!(U032U008.inner(u8::MAX), u32::MAX);
        assert_eq!(U064U008.inner(u8::MAX), u64::MAX);
        assert_eq!(U128U008.inner(u8::MAX), u128::MAX);
        assert_eq!(U016U008.inner(0), 0_u16);
        assert_eq!(U016U008.inner(254), 254_u16);
    }

    #[test]
    fn i_to_u8_neg_clip() {
        assert_eq!(I016U008.ceil(-1), 0);
        assert_eq!(I016U008.ceil(i16::MIN), 0);
        assert_eq!(I128U008.ceil(i128::MIN), 0);
    }

    #[test]
    fn i_to_u8_high_saturate() {
        assert_eq!(I016U008.ceil(i16::MAX), u8::MAX);
        assert_eq!(I032U008.ceil(i32::MAX), u8::MAX);
        assert_eq!(I128U008.ceil(i128::MAX), u8::MAX);
    }

    #[test]
    fn i_to_u8_inner_fine_max_fixup() {
        assert_eq!(I016U008.inner(u8::MAX), i16::MAX);
        assert_eq!(I128U008.inner(u8::MAX), i128::MAX);
        assert_eq!(I016U008.inner(0), 0_i16);
        assert_eq!(I016U008.inner(100), 100_i16);
    }

    // ── §2 Q-format spot checks ────────────────────────────────────

    /// MIDI velocity 64 — the canonical mid-range velocity, exactly
    /// 0.5 in Q1.7 (`U007`) — embeds via `Q008Q007.inner` to 128
    /// (= 0.5 in Q0.8 / `U008`). `U008` is the Fine side (more
    /// fractional bits) and `U007` is the Coarse side.
    #[test]
    fn spot_midi_velocity_q17_to_q08() {
        let velocity_64 = FixedU8::<U7>::from_bits(64);
        let pixel = Q008Q007.inner(velocity_64);
        assert_eq!(pixel, FixedU8::<U8>::from_bits(128));
        // Round-trip Q0.8 → Q1.7 via ceil/floor (RATIO = 2 is exact
        // on multiples of 2, so they agree).
        assert_eq!(Q008Q007.ceil(pixel), velocity_64);
        assert_eq!(Q008Q007.floor(pixel), velocity_64);
    }

    /// MIDI max velocity 127 (= 127/128 = 0.992... in Q1.7) embeds
    /// via inner to 254 in Q0.8 (= 127/128 of 256).
    #[test]
    fn spot_q17_max_velocity_to_q08() {
        let velocity_max = FixedU8::<U7>::from_bits(127);
        assert_eq!(Q008Q007.inner(velocity_max), FixedU8::<U8>::from_bits(254));
    }

    #[test]
    fn spot_q004q000_on_grid() {
        // 1.5 in Q4.4 (bits 24) — exactly representable in Q8.0 by 1 or 2.
        let q44 = FixedU8::<U4>::from_bits(24);
        assert_eq!(Q004Q000.floor(q44), FixedU8::<U0>::from_bits(1));
        assert_eq!(Q004Q000.ceil(q44), FixedU8::<U0>::from_bits(2));
        assert_eq!(
            Q004Q000.inner(FixedU8::<U0>::from_bits(1)),
            FixedU8::<U4>::from_bits(16)
        );
    }

    #[test]
    fn spot_q008q000_degenerate() {
        // SHIFT = 8, RATIO = 256. Only Coarse(0) round-trips; bits ≥ 1
        // saturates inner at u8::MAX.
        assert_eq!(
            Q008Q000.inner(FixedU8::<U0>::from_bits(0)),
            FixedU8::<U8>::from_bits(0),
        );
        assert_eq!(
            Q008Q000.inner(FixedU8::<U0>::from_bits(1)),
            FixedU8::<U8>::from_bits(u8::MAX),
        );
        assert_eq!(
            Q008Q000.inner(FixedU8::<U0>::from_bits(255)),
            FixedU8::<U8>::from_bits(u8::MAX),
        );
    }

    #[test]
    fn spot_boundary_fixups() {
        // Fine::MAX boundary fixup exercised on Q004Q000 (RATIO = 16).
        // floor(u8::MAX) returns Coarse::MAX (= u8::MAX) so the Galois
        // law `inner(b) ≤ a ⟺ b ≤ floor(a)` holds at the saturation
        // plateau (where inner saturates at u8::MAX).
        let fmax = FixedU8::<U4>::from_bits(u8::MAX);
        assert_eq!(Q004Q000.floor(fmax), FixedU8::<U0>::from_bits(u8::MAX));
        // No FINE_MIN fixup needed: u8::MIN = 0; ceil(0) = 0 falls out of
        // the natural division (0 / 16 = 0, remainder 0).
        let fmin = FixedU8::<U4>::from_bits(0);
        assert_eq!(Q004Q000.ceil(fmin), FixedU8::<U0>::from_bits(0));
        assert_eq!(Q004Q000.floor(fmin), FixedU8::<U0>::from_bits(0));
    }

    // The Galois proptest battery (252 generated tests across 28
    // ordered pairs) lives in `tests/conn_fixed_u08_galois.rs` —
    // hosting it as an integration test keeps the lib-test rustc
    // invocation under CI's container memory budget.
}
