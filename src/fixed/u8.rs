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

use crate::conn::Conn;
use ::fixed::FixedU8;
use ::fixed::types::extra::{U0, U1, U2, U3, U4, U6, U7, U8, Unsigned};

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
fix_fix_u8!(U001U000, U1, U0);
fix_fix_u8!(U002U000, U2, U0);
fix_fix_u8!(U003U000, U3, U0);
fix_fix_u8!(U004U000, U4, U0);
fix_fix_u8!(U006U000, U6, U0);
fix_fix_u8!(U007U000, U7, U0);
fix_fix_u8!(U008U000, U8, U0);
fix_fix_u8!(U002U001, U2, U1);
fix_fix_u8!(U003U001, U3, U1);
fix_fix_u8!(U004U001, U4, U1);
fix_fix_u8!(U006U001, U6, U1);
fix_fix_u8!(U007U001, U7, U1);
fix_fix_u8!(U008U001, U8, U1);
fix_fix_u8!(U003U002, U3, U2);
fix_fix_u8!(U004U002, U4, U2);
fix_fix_u8!(U006U002, U6, U2);
fix_fix_u8!(U007U002, U7, U2);
fix_fix_u8!(U008U002, U8, U2);
fix_fix_u8!(U004U003, U4, U3);
fix_fix_u8!(U006U003, U6, U3);
fix_fix_u8!(U007U003, U7, U3);
fix_fix_u8!(U008U003, U8, U3);
fix_fix_u8!(U006U004, U6, U4);
fix_fix_u8!(U007U004, U7, U4);
fix_fix_u8!(U008U004, U8, U4);
fix_fix_u8!(U007U006, U7, U6);
fix_fix_u8!(U008U006, U8, U6);
fix_fix_u8!(U008U007, U8, U7);

// ────────────────────────────────────────────────────────────────────
// Tests
// ────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    /// MIDI velocity 64 — the canonical mid-range velocity, exactly
    /// 0.5 in Q1.7 (`U007`) — embeds via `U008U007.inner` to 128
    /// (= 0.5 in Q0.8 / `U008`). `U008` is the Fine side (more
    /// fractional bits) and `U007` is the Coarse side.
    #[test]
    fn spot_midi_velocity_q17_to_q08() {
        let velocity_64 = FixedU8::<U7>::from_bits(64);
        let pixel = U008U007.inner(velocity_64);
        assert_eq!(pixel, FixedU8::<U8>::from_bits(128));
        // Round-trip Q0.8 → Q1.7 via ceil/floor (RATIO = 2 is exact
        // on multiples of 2, so they agree).
        assert_eq!(U008U007.ceil(pixel), velocity_64);
        assert_eq!(U008U007.floor(pixel), velocity_64);
    }

    /// MIDI max velocity 127 (= 127/128 = 0.992... in Q1.7) embeds
    /// via inner to 254 in Q0.8 (= 127/128 of 256).
    #[test]
    fn spot_q17_max_velocity_to_q08() {
        let velocity_max = FixedU8::<U7>::from_bits(127);
        assert_eq!(U008U007.inner(velocity_max), FixedU8::<U8>::from_bits(254));
    }

    #[test]
    fn spot_u004u000_on_grid() {
        // 1.5 in Q4.4 (bits 24) — exactly representable in Q8.0 by 1 or 2.
        let q44 = FixedU8::<U4>::from_bits(24);
        assert_eq!(U004U000.floor(q44), FixedU8::<U0>::from_bits(1));
        assert_eq!(U004U000.ceil(q44), FixedU8::<U0>::from_bits(2));
        assert_eq!(
            U004U000.inner(FixedU8::<U0>::from_bits(1)),
            FixedU8::<U4>::from_bits(16)
        );
    }

    #[test]
    fn spot_u008u000_degenerate() {
        // SHIFT = 8, RATIO = 256. Only Coarse(0) round-trips; bits ≥ 1
        // saturates inner at u8::MAX.
        assert_eq!(
            U008U000.inner(FixedU8::<U0>::from_bits(0)),
            FixedU8::<U8>::from_bits(0),
        );
        assert_eq!(
            U008U000.inner(FixedU8::<U0>::from_bits(1)),
            FixedU8::<U8>::from_bits(u8::MAX),
        );
        assert_eq!(
            U008U000.inner(FixedU8::<U0>::from_bits(255)),
            FixedU8::<U8>::from_bits(u8::MAX),
        );
    }

    #[test]
    fn spot_boundary_fixups() {
        // Fine::MAX boundary fixup exercised on U004U000 (RATIO = 16).
        // floor(u8::MAX) returns Coarse::MAX (= u8::MAX) so the Galois
        // law `inner(b) ≤ a ⟺ b ≤ floor(a)` holds at the saturation
        // plateau (where inner saturates at u8::MAX).
        let fmax = FixedU8::<U4>::from_bits(u8::MAX);
        assert_eq!(U004U000.floor(fmax), FixedU8::<U0>::from_bits(u8::MAX));
        // No FINE_MIN fixup needed: u8::MIN = 0; ceil(0) = 0 falls out of
        // the natural division (0 / 16 = 0, remainder 0).
        let fmin = FixedU8::<U4>::from_bits(0);
        assert_eq!(U004U000.ceil(fmin), FixedU8::<U0>::from_bits(0));
        assert_eq!(U004U000.floor(fmin), FixedU8::<U0>::from_bits(0));
    }

    // The Galois proptest battery (252 generated tests across 28
    // ordered pairs) lives in `tests/conn_fixed_u08_galois.rs` —
    // hosting it as an integration test keeps the lib-test rustc
    // invocation under CI's container memory budget.
}
