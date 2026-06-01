//! Binary fixed-point ladder over `fixed::FixedU16<Frac>`, plus the
//! cross-crate iso to `u16` and the IEEE-float → `FixedU16<F>` bridges.
//!
//! Pure-`core` Conns sourced from `u16` live next door in
//! [`crate::core::u016`].
//!
//! Frac level set: `{F0, F2, F4, F8, F12, F14, F15, F16}`. `F14` is
//! the 14-bit MIDI control packing; `F15` the 16-bit unsigned audio
//! amplitude / normalised-pixel format; `F16` the fully-fractional
//! 16-bit normalised integer.

use super::float_fixed;
#[cfg(feature = "f16")]
use super::float_fixed_l;
use ::fixed::FixedU16;
use ::fixed::types::extra::{
    U0 as F0, U2 as F2, U4 as F4, U8 as F8, U12 as F12, U14 as F14, U15 as F15, U16 as F16,
    Unsigned,
};

// ── Cross-crate iso: FixedU16<F0> ↔ u16 ───────────────────────────

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

// ── Q-format ladder over `FixedU16<Frac>` ──────────────────────────

pub type U000 = FixedU16<F0>;
pub type U002 = FixedU16<F2>;
pub type U004 = FixedU16<F4>;
pub type U008 = FixedU16<F8>;
pub type U012 = FixedU16<F12>;
pub type U014 = FixedU16<F14>;
pub type U015 = FixedU16<F15>;
pub type U016 = FixedU16<F16>;

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
        pub const $const_name: $crate::conn::Conn<FixedU16<$FineFrac>, FixedU16<$CoarseFrac>> = {
            const SHIFT: u32 = <$FineFrac as Unsigned>::U32 - <$CoarseFrac as Unsigned>::U32;
            const RATIO: u32 = 1_u32 << SHIFT;
            const FINE_MAX: u16 = u16::MAX;

            fn ceil(x: FixedU16<$FineFrac>) -> FixedU16<$CoarseFrac> {
                let bits = x.to_bits() as u32;
                let q = bits / RATIO;
                let r = bits % RATIO;
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

            $crate::conn::Conn::new_l(ceil, inner)
        };
    };
}

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

// ── f32 → FixedU16<U<frac>> narrowing (full triple) ───────────────

float_fixed!(pub F032Q000, f32, FixedU16, F0,  u16);
float_fixed!(pub F032Q002, f32, FixedU16, F2,  u16);
float_fixed!(pub F032Q004, f32, FixedU16, F4,  u16);
float_fixed!(pub F032Q008, f32, FixedU16, F8,  u16);
float_fixed!(pub F032Q012, f32, FixedU16, F12, u16);
float_fixed!(pub F032Q014, f32, FixedU16, F14, u16);
float_fixed!(pub F032Q015, f32, FixedU16, F15, u16);
float_fixed!(pub F032Q016, f32, FixedU16, F16, u16);

// ── f64 → FixedU16<U<frac>> narrowing ───────────────────────────────

float_fixed!(pub F064Q000, f64, FixedU16, F0,  u16);
float_fixed!(pub F064Q002, f64, FixedU16, F2,  u16);
float_fixed!(pub F064Q004, f64, FixedU16, F4,  u16);
float_fixed!(pub F064Q008, f64, FixedU16, F8,  u16);
float_fixed!(pub F064Q012, f64, FixedU16, F12, u16);
float_fixed!(pub F064Q014, f64, FixedU16, F14, u16);
float_fixed!(pub F064Q015, f64, FixedU16, F15, u16);
float_fixed!(pub F064Q016, f64, FixedU16, F16, u16);

// ── f16 → FixedU16<U<frac>> narrowing (L-only; gated on `f16`) ────

#[cfg(feature = "f16")]
float_fixed_l!(pub F016Q000, f16, FixedU16, F0,  u16);
#[cfg(feature = "f16")]
float_fixed_l!(pub F016Q002, f16, FixedU16, F2,  u16);
#[cfg(feature = "f16")]
float_fixed_l!(pub F016Q004, f16, FixedU16, F4,  u16);
#[cfg(feature = "f16")]
float_fixed_l!(pub F016Q008, f16, FixedU16, F8,  u16);
#[cfg(feature = "f16")]
float_fixed_l!(pub F016Q012, f16, FixedU16, F12, u16);
#[cfg(feature = "f16")]
float_fixed_l!(pub F016Q014, f16, FixedU16, F14, u16);
#[cfg(feature = "f16")]
float_fixed_l!(pub F016Q015, f16, FixedU16, F15, u16);
#[cfg(feature = "f16")]
float_fixed_l!(pub F016Q016, f16, FixedU16, F16, u16);

// ────────────────────────────────────────────────────────────────────
// Tests
// ────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    #[allow(unused_imports)]
    use crate::conn::{ConnL, ConnR};
    #[allow(unused_imports)]
    use proptest::prelude::*;

    #[test]
    fn spot_q15_audio_to_q16() {
        let q15 = FixedU16::<F15>::from_bits(16384);
        let q16 = crate::conn::upper(&Q016Q015, q15);
        assert_eq!(q16, FixedU16::<F16>::from_bits(32768));
        assert_eq!(crate::conn::ceil(&Q016Q015, q16), q15);
    }

    #[test]
    fn spot_q14_midi_to_q16() {
        let q14 = FixedU16::<F14>::from_bits(8192);
        let q16 = crate::conn::upper(&Q016Q014, q14);
        assert_eq!(q16, FixedU16::<F16>::from_bits(32768));
    }

    #[test]
    fn spot_q008q004_on_grid() {
        let q88 = FixedU16::<F8>::from_bits(384);
        assert_eq!(
            crate::conn::ceil(&Q008Q004, q88),
            FixedU16::<F4>::from_bits(24)
        );
        assert_eq!(
            crate::conn::upper(&Q008Q004, FixedU16::<F4>::from_bits(24)),
            q88
        );
    }

    #[test]
    fn spot_q008q004_off_grid() {
        let off = FixedU16::<F8>::from_bits(358);
        assert_eq!(
            crate::conn::ceil(&Q008Q004, off),
            FixedU16::<F4>::from_bits(23)
        );
    }

    #[test]
    fn spot_q016q000_degenerate() {
        assert_eq!(
            crate::conn::upper(&Q016Q000, FixedU16::<F0>::from_bits(0)),
            FixedU16::<F16>::from_bits(0),
        );
        assert_eq!(
            crate::conn::upper(&Q016Q000, FixedU16::<F0>::from_bits(1)),
            FixedU16::<F16>::from_bits(u16::MAX),
        );
        assert_eq!(
            crate::conn::upper(&Q016Q000, FixedU16::<F0>::from_bits(u16::MAX)),
            FixedU16::<F16>::from_bits(u16::MAX),
        );
    }

    #[test]
    fn spot_boundary_fixups() {
        let fmin = FixedU16::<F8>::from_bits(0);
        assert_eq!(
            crate::conn::ceil(&Q008Q004, fmin),
            FixedU16::<F4>::from_bits(0)
        );
    }
}
