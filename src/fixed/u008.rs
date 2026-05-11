//! Binary fixed-point ladder over `fixed::FixedU8<Frac>`, plus the
//! cross-crate iso to `u8` and the IEEE-float → `FixedU8<F>` bridges.
//!
//! Pure-`core` Conns sourced from `u8` (widening, sat-cross-sign,
//! `u8 ↔ NonZeroU8`, BE/LE byte iso, …) live next door in
//! [`crate::core::u008`]. The `bool` ↔ byte projections live in
//! [`crate::core::bool`].
//!
//! Frac level set: `{F0, F1, F2, F3, F4, F6, F7, F8}` → 28 ordered pairs.
//! `F7` (= Q1.7) is the canonical 7-bit MIDI velocity / 7-bit DSP
//! amplitude format.

use super::float_fixed;
use ::fixed::FixedU8;
use ::fixed::types::extra::{
    U0 as F0, U1 as F1, U2 as F2, U3 as F3, U4 as F4, U6 as F6, U7 as F7, U8 as F8, Unsigned,
};

// ── Cross-crate iso: FixedU8<F0> ↔ u8 ─────────────────────────────

const fn q000u008_fwd(q: FixedU8<F0>) -> u8 {
    q.to_bits()
}
const fn q000u008_bk(i: u8) -> FixedU8<F0> {
    FixedU8::<F0>::from_bits(i)
}

crate::iso! {
    /// `FixedU8<F0> ↔ u8` — Q8.0 unsigned lossless iso. Degenerate Galois.
    pub Q000U008 : FixedU8<F0> => u8 {
        forward: q000u008_fwd,
        back:    q000u008_bk,
    }
}

// ── Q-format ladder over `FixedU8<Frac>` ───────────────────────────

pub type U000 = FixedU8<F0>;
pub type U001 = FixedU8<F1>;
pub type U002 = FixedU8<F2>;
pub type U003 = FixedU8<F3>;
pub type U004 = FixedU8<F4>;
pub type U006 = FixedU8<F6>;
pub type U007 = FixedU8<F7>;
pub type U008 = FixedU8<F8>;

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
        pub const $const_name: $crate::conn::Conn<FixedU8<$FineFrac>, FixedU8<$CoarseFrac>> = {
            const SHIFT: u32 = <$FineFrac as Unsigned>::U32 - <$CoarseFrac as Unsigned>::U32;
            const RATIO: u16 = 1_u16 << SHIFT;
            const FINE_MAX: u8 = u8::MAX;

            fn ceil(x: FixedU8<$FineFrac>) -> FixedU8<$CoarseFrac> {
                let bits = x.to_bits() as u16;
                let q = bits / RATIO;
                let r = bits % RATIO;
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

            $crate::conn::Conn::new_l(ceil, inner)
        };
    };
}

fix_fix_u8!(Q001Q000, F1, F0);
fix_fix_u8!(Q002Q000, F2, F0);
fix_fix_u8!(Q003Q000, F3, F0);
fix_fix_u8!(Q004Q000, F4, F0);
fix_fix_u8!(Q006Q000, F6, F0);
fix_fix_u8!(Q007Q000, F7, F0);
fix_fix_u8!(Q008Q000, F8, F0);
fix_fix_u8!(Q002Q001, F2, F1);
fix_fix_u8!(Q003Q001, F3, F1);
fix_fix_u8!(Q004Q001, F4, F1);
fix_fix_u8!(Q006Q001, F6, F1);
fix_fix_u8!(Q007Q001, F7, F1);
fix_fix_u8!(Q008Q001, F8, F1);
fix_fix_u8!(Q003Q002, F3, F2);
fix_fix_u8!(Q004Q002, F4, F2);
fix_fix_u8!(Q006Q002, F6, F2);
fix_fix_u8!(Q007Q002, F7, F2);
fix_fix_u8!(Q008Q002, F8, F2);
fix_fix_u8!(Q004Q003, F4, F3);
fix_fix_u8!(Q006Q003, F6, F3);
fix_fix_u8!(Q007Q003, F7, F3);
fix_fix_u8!(Q008Q003, F8, F3);
fix_fix_u8!(Q006Q004, F6, F4);
fix_fix_u8!(Q007Q004, F7, F4);
fix_fix_u8!(Q008Q004, F8, F4);
fix_fix_u8!(Q007Q006, F7, F6);
fix_fix_u8!(Q008Q006, F8, F6);
fix_fix_u8!(Q008Q007, F8, F7);

// ── f32 → FixedU8<U<frac>> narrowing (full triple) ────────────────

float_fixed!(pub F032Q000, f32, FixedU8, F0, u8);
float_fixed!(pub F032Q001, f32, FixedU8, F1, u8);
float_fixed!(pub F032Q002, f32, FixedU8, F2, u8);
float_fixed!(pub F032Q003, f32, FixedU8, F3, u8);
float_fixed!(pub F032Q004, f32, FixedU8, F4, u8);
float_fixed!(pub F032Q006, f32, FixedU8, F6, u8);
float_fixed!(pub F032Q007, f32, FixedU8, F7, u8);
float_fixed!(pub F032Q008, f32, FixedU8, F8, u8);

// ── f64 → FixedU8<U<frac>> narrowing ───────────────────────────────

float_fixed!(pub F064Q000, f64, FixedU8, F0, u8);
float_fixed!(pub F064Q001, f64, FixedU8, F1, u8);
float_fixed!(pub F064Q002, f64, FixedU8, F2, u8);
float_fixed!(pub F064Q003, f64, FixedU8, F3, u8);
float_fixed!(pub F064Q004, f64, FixedU8, F4, u8);
float_fixed!(pub F064Q006, f64, FixedU8, F6, u8);
float_fixed!(pub F064Q007, f64, FixedU8, F7, u8);
float_fixed!(pub F064Q008, f64, FixedU8, F8, u8);

// ── f16 → FixedU8<U<frac>> narrowing (gated on `f16`) ─────────────

#[cfg(feature = "f16")]
float_fixed!(pub F016Q000, f16, FixedU8, F0, u8);
#[cfg(feature = "f16")]
float_fixed!(pub F016Q001, f16, FixedU8, F1, u8);
#[cfg(feature = "f16")]
float_fixed!(pub F016Q002, f16, FixedU8, F2, u8);
#[cfg(feature = "f16")]
float_fixed!(pub F016Q003, f16, FixedU8, F3, u8);
#[cfg(feature = "f16")]
float_fixed!(pub F016Q004, f16, FixedU8, F4, u8);
#[cfg(feature = "f16")]
float_fixed!(pub F016Q006, f16, FixedU8, F6, u8);
#[cfg(feature = "f16")]
float_fixed!(pub F016Q007, f16, FixedU8, F7, u8);
#[cfg(feature = "f16")]
float_fixed!(pub F016Q008, f16, FixedU8, F8, u8);

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

    #[test]
    fn q000u008_round_trips_both_ways() {
        for &v in &[0_u8, 1, 42, u8::MAX] {
            let q = FixedU8::<F0>::from_bits(v);
            assert_eq!(Q000U008.ceil(q), v);
            assert_eq!(Q000U008.floor(q), v);
            assert_eq!(Q000U008.upper(v), q);
            assert_eq!(Q000U008.lower(v), q);
            assert_eq!(Q000U008.ceil(Q000U008.upper(v)), v);
            assert_eq!(Q000U008.upper(Q000U008.ceil(q)), q);
        }
    }

    proptest! {
        #[test]
        fn q000u008_galois_l(a_bits in any::<u8>(), b in any::<u8>()) {
            let a = FixedU8::<F0>::from_bits(a_bits);
            prop_assert!(conn_laws::galois_l(&Q000U008.conn_l(), a, b));
        }

        #[test]
        fn q000u008_galois_r(a_bits in any::<u8>(), b in any::<u8>()) {
            let a = FixedU8::<F0>::from_bits(a_bits);
            prop_assert!(conn_laws::galois_r(&Q000U008.conn_r(), a, b));
        }

        #[test]
        fn q000u008_round_trip_both_directions(v in any::<u8>()) {
            let q = FixedU8::<F0>::from_bits(v);
            prop_assert_eq!(Q000U008.upper(Q000U008.ceil(q)), q);
            prop_assert_eq!(Q000U008.ceil(Q000U008.upper(v)), v);
            prop_assert_eq!(Q000U008.lower(Q000U008.floor(q)), q);
            prop_assert_eq!(Q000U008.floor(Q000U008.lower(v)), v);
        }
    }

    #[test]
    fn spot_midi_velocity_q17_to_q08() {
        let velocity_64 = FixedU8::<F7>::from_bits(64);
        let pixel = Q008Q007.upper(velocity_64);
        assert_eq!(pixel, FixedU8::<F8>::from_bits(128));
        assert_eq!(Q008Q007.ceil(pixel), velocity_64);
    }

    #[test]
    fn spot_q17_max_velocity_to_q08() {
        let velocity_max = FixedU8::<F7>::from_bits(127);
        assert_eq!(Q008Q007.upper(velocity_max), FixedU8::<F8>::from_bits(254));
    }

    #[test]
    fn spot_q004q000_on_grid() {
        let q44 = FixedU8::<F4>::from_bits(24);
        assert_eq!(Q004Q000.ceil(q44), FixedU8::<F0>::from_bits(2));
        assert_eq!(
            Q004Q000.upper(FixedU8::<F0>::from_bits(1)),
            FixedU8::<F4>::from_bits(16)
        );
    }

    #[test]
    fn spot_q008q000_degenerate() {
        assert_eq!(
            Q008Q000.upper(FixedU8::<F0>::from_bits(0)),
            FixedU8::<F8>::from_bits(0),
        );
        assert_eq!(
            Q008Q000.upper(FixedU8::<F0>::from_bits(1)),
            FixedU8::<F8>::from_bits(u8::MAX),
        );
        assert_eq!(
            Q008Q000.upper(FixedU8::<F0>::from_bits(255)),
            FixedU8::<F8>::from_bits(u8::MAX),
        );
    }

    #[test]
    fn spot_boundary_fixups() {
        let fmin = FixedU8::<F4>::from_bits(0);
        assert_eq!(Q004Q000.ceil(fmin), FixedU8::<F0>::from_bits(0));
    }
}
