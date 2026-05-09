//! Binary fixed-point ladder over `fixed::FixedU16<Frac>`.
//!
//! Frac level set: `{F0, F2, F4, F8, F12, F14, F15, F16}` → 28 ordered
//! pairs `(Fine, Coarse)` with `Fine > Coarse`. Mirrors [`super::i16`]
//! with `FixedU16` backing instead of `FixedI16`, and adds two
//! unsigned-natural Q-formats:
//!
//! - **`F14`** (Q2.14): canonical packing for 14-bit MIDI control
//!   values (pitch bend, channel pressure with high resolution) into
//!   a 16-bit word.
//! - **`F15`** (Q1.15): canonical 16-bit unsigned audio amplitude /
//!   normalised-pixel format.
//!
//! `F16` (Q0.16) is the fully-fractional 16-bit normalised integer.
//!
//! Same totality + Galois-axiom guarantees as `i16`. The signed
//! `FINE_MIN` boundary fixup is dropped (unsigned has no negative
//! range); the `FINE_MAX` fixup in `floor` remains, for the same
//! Galois-law reason: `inner` saturates at `u16::MAX`, so floor at
//! the saturation plateau must return `Coarse::MAX` to keep the
//! lower adjoint lawful.

use super::{int_uint, int_uint_narrow, nz_uint_ext, uint_uint, uint_uint_narrow};
use ::fixed::FixedU16;
use ::fixed::types::extra::{
    U0 as F0, U2 as F2, U4 as F4, U8 as F8, U12 as F12, U14 as F14, U15 as F15, U16 as F16,
    Unsigned,
};
use core::num::NonZeroU16;

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

// ── §2 u16 ↔ NonZeroU16 ──────────────────────────────────

nz_uint_ext!(U016N016, u16, NonZeroU16);

// ── §3 cross-crate iso: FixedU16<F0> ↔ u16 ─────────────────────────

const fn q000u016_fwd(q: FixedU16<F0>) -> u16 {
    q.to_bits()
}
const fn q000u016_bk(i: u16) -> FixedU16<F0> {
    FixedU16::<F0>::from_bits(i)
}

crate::iso! {
    /// `FixedU16<F0> ↔ u16` — Q16.0 unsigned lossless iso. Degenerate Galois.
    pub Q000U016 : FixedU16<F0> => u16 {
        forward: q000u016_fwd,
        back:    q000u016_bk,
    }
}

// ── Sortable big-endian byte encodings ─────────────────────

const fn u16_to_be02(x: u16) -> [u8; 2] {
    x.to_be_bytes()
}
const fn be02_to_u16(b: [u8; 2]) -> u16 {
    u16::from_be_bytes(b)
}

crate::iso! {
    /// `u16 ↔ [u8; 2]` — big-endian iso. Byte-lex order matches u16 order.
    pub U016BE02 : u16 => [u8; 2] {
        forward: u16_to_be02,
        back:    be02_to_u16,
    }
}

// ── §4 Q-format ladder over `FixedU16<Frac>` ────────────────────────

/// `U<frac> = FixedU16<U<frac>>` — u16-backed binary fixed-point.
pub type U0 = FixedU16<F0>;
pub type U2 = FixedU16<F2>;
pub type U4 = FixedU16<F4>;
pub type U8 = FixedU16<F8>;
pub type U12 = FixedU16<F12>;
pub type U14 = FixedU16<F14>;
pub type U15 = FixedU16<F15>;
pub type U16 = FixedU16<F16>;

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
        pub struct $const_name;

        impl $const_name {
            const SHIFT: u32 = <$FineFrac as Unsigned>::U32 - <$CoarseFrac as Unsigned>::U32;
            // u32 covers SHIFT ∈ [1, 16]: 1 << 16 = 65 536 fits, and
            // u16::MAX × (1 << 16) = 4 294 836 225 < u32::MAX, so the
            // multiplication in `inner` cannot overflow u32 before the
            // saturating clamp.
            const RATIO: u32 = 1_u32 << Self::SHIFT;
            const FINE_MAX: u16 = u16::MAX;

            const fn _ceil(x: FixedU16<$FineFrac>) -> FixedU16<$CoarseFrac> {
                let bits = x.to_bits() as u32;
                let q = bits / Self::RATIO;
                let r = bits % Self::RATIO;
                // `res ≤ ⌈u16::MAX / 2⌉ = 32_768` since Self::RATIO ≥ 2;
                // the `as u16` cast is lossless.
                let res = if r != 0 { q + 1 } else { q };
                FixedU16::from_bits(res as u16)
            }

            const fn _inner(x: FixedU16<$CoarseFrac>) -> FixedU16<$FineFrac> {
                let res = (x.to_bits() as u32) * Self::RATIO;
                let saturated = if res > Self::FINE_MAX as u32 {
                    Self::FINE_MAX
                } else {
                    res as u16
                };
                FixedU16::from_bits(saturated)
            }
        }

        // (Plan 32) ConnL only — `_inner` non-injective at saturation.
        impl $crate::conn::ConnL<FixedU16<$FineFrac>, FixedU16<$CoarseFrac>> for $const_name {
            #[inline]
            fn conn_l(
                &self,
            ) -> $crate::conn::Conn<FixedU16<$FineFrac>, FixedU16<$CoarseFrac>, $crate::conn::L>
            {
                $crate::conn::Conn::new_l($const_name::_ceil, $const_name::_inner)
            }
        }
    };
}

// 28 ordered pairs from {F0, F2, F4, F8, F12, F14, F15, F16}.
fix_fix_u16!(Q002Q000, F2, F0);
fix_fix_u16!(Q004Q000, F4, F0);
fix_fix_u16!(Q008Q000, F8, F0);
fix_fix_u16!(Q012Q000, F12, F0);
fix_fix_u16!(Q014Q000, F14, F0);
fix_fix_u16!(Q015Q000, F15, F0);
fix_fix_u16!(Q016Q000, F16, F0);
fix_fix_u16!(Q004Q002, F4, F2);
fix_fix_u16!(Q008Q002, F8, F2);
fix_fix_u16!(Q012Q002, F12, F2);
fix_fix_u16!(Q014Q002, F14, F2);
fix_fix_u16!(Q015Q002, F15, F2);
fix_fix_u16!(Q016Q002, F16, F2);
fix_fix_u16!(Q008Q004, F8, F4);
fix_fix_u16!(Q012Q004, F12, F4);
fix_fix_u16!(Q014Q004, F14, F4);
fix_fix_u16!(Q015Q004, F15, F4);
fix_fix_u16!(Q016Q004, F16, F4);
fix_fix_u16!(Q012Q008, F12, F8);
fix_fix_u16!(Q014Q008, F14, F8);
fix_fix_u16!(Q015Q008, F15, F8);
fix_fix_u16!(Q016Q008, F16, F8);
fix_fix_u16!(Q014Q012, F14, F12);
fix_fix_u16!(Q015Q012, F15, F12);
fix_fix_u16!(Q016Q012, F16, F12);
fix_fix_u16!(Q015Q014, F15, F14);
fix_fix_u16!(Q016Q014, F16, F14);
fix_fix_u16!(Q016Q015, F16, F15);

// ────────────────────────────────────────────────────────────────────
// Tests
// ────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    #[allow(unused_imports)]
    use crate::conn::{ConnL, ConnR};
    use crate::prop::conn as conn_laws;
    use proptest::prelude::*;

    // ── §1 std-int spot checks (merged from former int/u16.rs) ─────

    #[test]
    fn u008u016_ceil_widens_losslessly() {
        assert_eq!(U008U016.ceil(0u8), 0u16);
        assert_eq!(U008U016.ceil(u8::MAX), u8::MAX as u16);
    }

    #[test]
    fn u008u016_inner_saturates_at_source_max() {
        assert_eq!(U008U016.upper(u16::MAX), u8::MAX);
        assert_eq!(U008U016.upper(50), 50);
    }

    #[test]
    fn i016u016_galois_at_mid_positive() {
        for (a, b) in [(50i16, 100u16), (50i16, 49u16), (100i16, 100u16)] {
            assert_eq!(
                I016U016.ceil(a) <= b,
                a <= I016U016.upper(b),
                "I016U016 galois_upper @ ({a}, {b})"
            );
        }
    }

    #[test]
    fn i008u016_inner_saturates() {
        assert_eq!(I008U016.upper(u16::MAX), i8::MAX);
        assert_eq!(I008U016.upper(127), 127);
    }

    #[test]
    fn u_to_u16_saturate_and_fixup() {
        assert_eq!(U032U016.ceil(u32::MAX), u16::MAX);
        assert_eq!(U128U016.ceil(u128::MAX), u16::MAX);
        assert_eq!(U032U016.upper(u16::MAX), u32::MAX);
        assert_eq!(U064U016.upper(u16::MAX), u64::MAX);
        assert_eq!(U128U016.upper(u16::MAX), u128::MAX);
        assert_eq!(U032U016.upper(60_000), 60_000_u32);
    }

    #[test]
    fn i_to_u16_neg_high_fixup() {
        assert_eq!(I032U016.ceil(-1), 0);
        assert_eq!(I032U016.ceil(i32::MIN), 0);
        assert_eq!(I032U016.ceil(i32::MAX), u16::MAX);
        assert_eq!(I128U016.ceil(i128::MAX), u16::MAX);
        assert_eq!(I032U016.upper(u16::MAX), i32::MAX);
        assert_eq!(I128U016.upper(u16::MAX), i128::MAX);
    }

    // ── §4 Q-format spot checks ────────────────────────────────────

    /// Q1.15 audio amplitude → Q0.16 normalised pixel intensity:
    /// the value 16384 in Q1.15 (= 0.5) embeds via `Q016Q015.upper`
    /// to 32768 in Q0.16 (= 0.5).
    #[test]
    fn spot_q15_audio_to_q16() {
        let q15 = FixedU16::<F15>::from_bits(16384);
        let q16 = Q016Q015.upper(q15);
        assert_eq!(q16, FixedU16::<F16>::from_bits(32768));
        // RATIO=2 exact: ceil round-trips. (Plan 32: ConnL only.)
        assert_eq!(Q016Q015.ceil(q16), q15);
    }

    /// 14-bit MIDI control value packed in u16 as Q2.14: the
    /// midpoint 8192 (= 0.5 in Q2.14) embeds through `Q016Q014` to
    /// 32768 in Q0.16. RATIO = 4.
    #[test]
    fn spot_q14_midi_to_q16() {
        let q14 = FixedU16::<F14>::from_bits(8192);
        let q16 = Q016Q014.upper(q14);
        assert_eq!(q16, FixedU16::<F16>::from_bits(32768));
    }

    #[test]
    fn spot_q008q004_on_grid() {
        // 1.5 in Q8.8 (bits 384) — exactly representable in Q12.4.
        let q88 = FixedU16::<F8>::from_bits(384);
        assert_eq!(Q008Q004.ceil(q88), FixedU16::<F4>::from_bits(24));
        assert_eq!(Q008Q004.upper(FixedU16::<F4>::from_bits(24)), q88);
    }

    #[test]
    fn spot_q008q004_off_grid() {
        // 1.398... (bits 358) — Q12.4 ceil rounds up to 23.
        let off = FixedU16::<F8>::from_bits(358);
        assert_eq!(Q008Q004.ceil(off), FixedU16::<F4>::from_bits(23));
    }

    #[test]
    fn spot_q016q000_degenerate() {
        // SHIFT = 16, RATIO = 65 536. Every Coarse value with bits ≥ 1
        // saturates inner. Only Coarse(0) round-trips.
        assert_eq!(
            Q016Q000.upper(FixedU16::<F0>::from_bits(0)),
            FixedU16::<F16>::from_bits(0),
        );
        assert_eq!(
            Q016Q000.upper(FixedU16::<F0>::from_bits(1)),
            FixedU16::<F16>::from_bits(u16::MAX),
        );
        assert_eq!(
            Q016Q000.upper(FixedU16::<F0>::from_bits(u16::MAX)),
            FixedU16::<F16>::from_bits(u16::MAX),
        );
    }

    #[test]
    fn spot_boundary_fixups() {
        // (Plan 32: floor removed.) No FINE_MIN fixup for unsigned.
        let fmin = FixedU16::<F8>::from_bits(0);
        assert_eq!(Q008Q004.ceil(fmin), FixedU16::<F4>::from_bits(0));
    }

    // ── BE byte-encoding tests ─────────────────────────────

    fn arb_byte2() -> impl Strategy<Value = [u8; 2]> {
        prop_oneof![Just([0; 2]), Just([0xFF; 2]), any::<[u8; 2]>()]
    }

    proptest! {
        #[test]
        fn u16_be_iso_roundtrip_l(a in prop_oneof![Just(0u16), Just(u16::MAX), any::<u16>()]) {
            prop_assert!(conn_laws::iso_roundtrip_l(&U016BE02.conn_l(), a));
        }
        #[test]
        fn u16_be_roundtrip_ceil(b in arb_byte2()) {
            prop_assert!(conn_laws::roundtrip_ceil(&U016BE02.conn_l(), b));
        }
        #[test]
        fn u16_be_galois_l(a in any::<u16>(), b in arb_byte2()) {
            prop_assert!(conn_laws::galois_l(&U016BE02.conn_l(), a, b));
        }
        #[test]
        fn u16_be_galois_r(a in any::<u16>(), b in arb_byte2()) {
            prop_assert!(conn_laws::galois_r(&U016BE02.conn_r(), a, b));
        }
        #[test]
        fn u16_be_floor_le_ceil(a in any::<u16>()) {
            prop_assert!(conn_laws::floor_le_ceil(&U016BE02, a));
        }
        #[test]
        fn u16_be_order_preserving(a in any::<u16>(), b in any::<u16>()) {
            prop_assert_eq!(a.cmp(&b), U016BE02.ceil(a).cmp(&U016BE02.ceil(b)));
        }
    }

    // The Galois proptest battery (252 generated tests across 28
    // ordered pairs) lives in `tests/fixed_u16_galois.rs` —
    // hosting it as an integration test keeps the lib-test rustc
    // invocation under CI's container memory budget.
}
