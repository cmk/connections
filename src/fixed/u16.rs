//! Binary fixed-point ladder over `fixed::FixedU16<Frac>`.
//!
//! Frac level set: `{U0, U2, U4, U8, U12, U14, U15, U16}` → 28 ordered
//! pairs `(Fine, Coarse)` with `Fine > Coarse`. Mirrors [`super::i16`]
//! with `FixedU16` backing instead of `FixedI16`, and adds two
//! unsigned-natural Q-formats:
//!
//! - **`U14`** (Q2.14): canonical packing for 14-bit MIDI control
//!   values (pitch bend, channel pressure with high resolution) into
//!   a 16-bit word.
//! - **`U15`** (Q1.15): canonical 16-bit unsigned audio amplitude /
//!   normalised-pixel format.
//!
//! `U16` (Q0.16) is the fully-fractional 16-bit normalised integer.
//!
//! Same totality + Galois-axiom guarantees as `i16`. The signed
//! `FINE_MIN` boundary fixup is dropped (unsigned has no negative
//! range); the `FINE_MAX` fixup in `floor` remains, for the same
//! Galois-law reason: `inner` saturates at `u16::MAX`, so floor at
//! the saturation plateau must return `Coarse::MAX` to keep the
//! lower adjoint lawful.

use super::{int_uint, int_uint_narrow, nz_uint_ext, uint_uint, uint_uint_narrow};
use crate::conn::Conn;
use core::num::NonZeroU16;
use ::fixed::FixedU16;
use ::fixed::types::extra::{U0, U2, U4, U8, U12, U14, U15, U16, Unsigned};

// ── §1 std-int Conns landing on `u16` ───────────────────────────────

uint_uint!(U008U016, u8, u16);
int_uint!(I008U016, i8, u16);
int_uint!(I016U016, i16, u16);

uint_uint_narrow!(U032U016, u32, u16);
uint_uint_narrow!(U064U016, u64, u16);
uint_uint_narrow!(U128U016, u128, u16);

int_uint_narrow!(I032U016, i32, u16);
int_uint_narrow!(I064U016, i64, u16);
int_uint_narrow!(I128U016, i128, u16);

// ── §3 NonZeroU16 ↔ Extended<u16> ──────────────────────────────────

nz_uint_ext!(U016N016, u16, NonZeroU16);

// ── §4 cross-crate iso: FixedU16<U0> ↔ u16 ─────────────────────────

/// `FixedU16<U0> ↔ u16` — Q16.0 unsigned lossless iso. Degenerate Galois.
pub const Q000U016: Conn<FixedU16<U0>, u16> = {
    fn forward(q: FixedU16<U0>) -> u16 {
        q.to_bits()
    }
    fn back(i: u16) -> FixedU16<U0> {
        FixedU16::<U0>::from_bits(i)
    }
    Conn::new_iso(forward, back)
};

// ── §2 Q-format ladder over `FixedU16<Frac>` ────────────────────────

/// `U<frac> = FixedU16<U<frac>>` — u16-backed binary fixed-point.
pub type U000 = FixedU16<U0>;
pub type U002 = FixedU16<U2>;
pub type U004 = FixedU16<U4>;
pub type U008 = FixedU16<U8>;
pub type U012 = FixedU16<U12>;
pub type U014 = FixedU16<U14>;
pub type U015 = FixedU16<U15>;
pub type U016 = FixedU16<U16>;

macro_rules! fix_fix_u16 {
    ($const_name:ident, $FineFrac:ty, $CoarseFrac:ty) => {
#[rustfmt::skip]
        #[doc = concat!(
            "`FixedU16<",
            stringify!($FineFrac),
            "> → FixedU16<",
            stringify!($CoarseFrac),
            ">` frac-level convert (u16-backed)."
        )]
        pub const $const_name: Conn<FixedU16<$FineFrac>, FixedU16<$CoarseFrac>> = {
            const SHIFT: u32 = <$FineFrac as Unsigned>::U32 - <$CoarseFrac as Unsigned>::U32;
            // u32 covers SHIFT ∈ [1, 16]: 1 << 16 = 65 536 fits, and
            // u16::MAX × (1 << 16) = 4 294 836 225 < u32::MAX, so the
            // multiplication in `inner` cannot overflow u32 before the
            // saturating clamp.
            const RATIO: u32 = 1_u32 << SHIFT;
            const FINE_MAX: u16 = u16::MAX;

            fn ceil(x: FixedU16<$FineFrac>) -> FixedU16<$CoarseFrac> {
                let bits = x.to_bits() as u32;
                let q = bits / RATIO;
                let r = bits % RATIO;
                // `res ≤ ⌈u16::MAX / 2⌉ = 32_768` since RATIO ≥ 2;
                // the `as u16` cast is lossless.
                let res = if r != 0 { q + 1 } else { q };
                FixedU16::from_bits(res as u16)
            }

            fn inner(x: FixedU16<$CoarseFrac>) -> FixedU16<$FineFrac> {
                let res = (x.to_bits() as u32) * RATIO;
                let saturated = if res > FINE_MAX as u32 {
                    FINE_MAX
                } else {
                    res as u16
                };
                FixedU16::from_bits(saturated)
            }

            fn floor(x: FixedU16<$FineFrac>) -> FixedU16<$CoarseFrac> {
                if x.to_bits() == FINE_MAX {
                    return FixedU16::<$CoarseFrac>::from_bits(u16::MAX);
                }
                let res = (x.to_bits() as u32) / RATIO;
                FixedU16::from_bits(res as u16)
            }

            Conn::new(ceil, inner, floor)
        };
    };
}

// 28 ordered pairs from {U0, U2, U4, U8, U12, U14, U15, U16}.
fix_fix_u16!(Q002Q000, U2, U0);
fix_fix_u16!(Q004Q000, U4, U0);
fix_fix_u16!(Q008Q000, U8, U0);
fix_fix_u16!(Q012Q000, U12, U0);
fix_fix_u16!(Q014Q000, U14, U0);
fix_fix_u16!(Q015Q000, U15, U0);
fix_fix_u16!(Q016Q000, U16, U0);
fix_fix_u16!(Q004Q002, U4, U2);
fix_fix_u16!(Q008Q002, U8, U2);
fix_fix_u16!(Q012Q002, U12, U2);
fix_fix_u16!(Q014Q002, U14, U2);
fix_fix_u16!(Q015Q002, U15, U2);
fix_fix_u16!(Q016Q002, U16, U2);
fix_fix_u16!(Q008Q004, U8, U4);
fix_fix_u16!(Q012Q004, U12, U4);
fix_fix_u16!(Q014Q004, U14, U4);
fix_fix_u16!(Q015Q004, U15, U4);
fix_fix_u16!(Q016Q004, U16, U4);
fix_fix_u16!(Q012Q008, U12, U8);
fix_fix_u16!(Q014Q008, U14, U8);
fix_fix_u16!(Q015Q008, U15, U8);
fix_fix_u16!(Q016Q008, U16, U8);
fix_fix_u16!(Q014Q012, U14, U12);
fix_fix_u16!(Q015Q012, U15, U12);
fix_fix_u16!(Q016Q012, U16, U12);
fix_fix_u16!(Q015Q014, U15, U14);
fix_fix_u16!(Q016Q014, U16, U14);
fix_fix_u16!(Q016Q015, U16, U15);

// ────────────────────────────────────────────────────────────────────
// Tests
// ────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    // ── §1 std-int spot checks (merged from former int/u16.rs) ─────

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

    #[test]
    fn u_to_u16_saturate_and_fixup() {
        assert_eq!(U032U016.ceil(u32::MAX), u16::MAX);
        assert_eq!(U128U016.ceil(u128::MAX), u16::MAX);
        assert_eq!(U032U016.inner(u16::MAX), u32::MAX);
        assert_eq!(U064U016.inner(u16::MAX), u64::MAX);
        assert_eq!(U128U016.inner(u16::MAX), u128::MAX);
        assert_eq!(U032U016.inner(60_000), 60_000_u32);
    }

    #[test]
    fn i_to_u16_neg_high_fixup() {
        assert_eq!(I032U016.ceil(-1), 0);
        assert_eq!(I032U016.ceil(i32::MIN), 0);
        assert_eq!(I032U016.ceil(i32::MAX), u16::MAX);
        assert_eq!(I128U016.ceil(i128::MAX), u16::MAX);
        assert_eq!(I032U016.inner(u16::MAX), i32::MAX);
        assert_eq!(I128U016.inner(u16::MAX), i128::MAX);
    }

    // ── §2 Q-format spot checks ────────────────────────────────────

    /// Q1.15 audio amplitude → Q0.16 normalised pixel intensity:
    /// the value 16384 in Q1.15 (= 0.5) embeds via `Q016Q015.inner`
    /// to 32768 in Q0.16 (= 0.5).
    #[test]
    fn spot_q15_audio_to_q16() {
        let q15 = FixedU16::<U15>::from_bits(16384);
        let q16 = Q016Q015.inner(q15);
        assert_eq!(q16, FixedU16::<U16>::from_bits(32768));
        // RATIO=2 is exact: ceil/floor agree.
        assert_eq!(Q016Q015.ceil(q16), q15);
        assert_eq!(Q016Q015.floor(q16), q15);
    }

    /// 14-bit MIDI control value packed in u16 as Q2.14: the
    /// midpoint 8192 (= 0.5 in Q2.14) embeds through `Q016Q014` to
    /// 32768 in Q0.16. RATIO = 4.
    #[test]
    fn spot_q14_midi_to_q16() {
        let q14 = FixedU16::<U14>::from_bits(8192);
        let q16 = Q016Q014.inner(q14);
        assert_eq!(q16, FixedU16::<U16>::from_bits(32768));
    }

    #[test]
    fn spot_q008q004_on_grid() {
        // 1.5 in Q8.8 (bits 0x0180 = 384) — exactly representable in Q12.4.
        let q88 = FixedU16::<U8>::from_bits(384);
        assert_eq!(Q008Q004.floor(q88), FixedU16::<U4>::from_bits(24));
        assert_eq!(Q008Q004.ceil(q88), FixedU16::<U4>::from_bits(24));
        assert_eq!(Q008Q004.inner(FixedU16::<U4>::from_bits(24)), q88);
    }

    #[test]
    fn spot_q008q004_off_grid() {
        // 1.398... (bits 358) — between Q12.4 grid points 22 and 23.
        let off = FixedU16::<U8>::from_bits(358);
        assert_eq!(Q008Q004.floor(off), FixedU16::<U4>::from_bits(22));
        assert_eq!(Q008Q004.ceil(off), FixedU16::<U4>::from_bits(23));
    }

    #[test]
    fn spot_q016q000_degenerate() {
        // SHIFT = 16, RATIO = 65 536. Every Coarse value with bits ≥ 1
        // saturates inner. Only Coarse(0) round-trips.
        assert_eq!(
            Q016Q000.inner(FixedU16::<U0>::from_bits(0)),
            FixedU16::<U16>::from_bits(0),
        );
        assert_eq!(
            Q016Q000.inner(FixedU16::<U0>::from_bits(1)),
            FixedU16::<U16>::from_bits(u16::MAX),
        );
        assert_eq!(
            Q016Q000.inner(FixedU16::<U0>::from_bits(u16::MAX)),
            FixedU16::<U16>::from_bits(u16::MAX),
        );
    }

    #[test]
    fn spot_boundary_fixups() {
        // Fine::MAX boundary fixup on Q008Q004 (RATIO = 16). At the
        // saturation plateau (where inner saturates at u16::MAX),
        // floor must return Coarse::MAX = u16::MAX so the Galois law
        // `inner(b) ≤ a ⟺ b ≤ floor(a)` holds.
        let fmax = FixedU16::<U8>::from_bits(u16::MAX);
        assert_eq!(Q008Q004.floor(fmax), FixedU16::<U4>::from_bits(u16::MAX));
        // No FINE_MIN fixup needed for unsigned.
        let fmin = FixedU16::<U8>::from_bits(0);
        assert_eq!(Q008Q004.ceil(fmin), FixedU16::<U4>::from_bits(0));
    }

    // The Galois proptest battery (252 generated tests across 28
    // ordered pairs) lives in `tests/conn_fixed_u16_galois.rs` —
    // hosting it as an integration test keeps the lib-test rustc
    // invocation under CI's container memory budget.
}
