//! Binary fixed-point ladder over `fixed::FixedI16<Frac>`, plus the
//! cross-crate iso to `i16` and the IEEE-float → `FixedI16<F>` bridges.
//!
//! Pure-`core` Conns sourced from `i16` (signed widening/narrowing,
//! two's-complement B2/L2 byte iso, `i16 ↔ NonZeroI16`, …) live next door
//! in [`crate::core::i016`].
//!
//! For each ordered pair `(FineFrac, CoarseFrac)` from the level set
//! `{0, 2, 4, 8, 12, 16}` with `FineFrac > CoarseFrac`, a
//! [`Conn`](crate::conn::Conn)`L<FixedI16<U_fine>, FixedI16<U_coarse>>`
//! constant `Q<dd>Q<dd>` (zero-padded) provides the left-Galois pair
//! `ceil ⊣ inner`. See Plan 32 / `doc/design.md` for the
//! one-sided-only rationale.

use super::float_fixed;
#[cfg(feature = "f16")]
use super::float_fixed_l;
use ::fixed::FixedI16;
use ::fixed::types::extra::{U0, U2, U4, U8, U12, U15, U16, Unsigned};

// ── Cross-crate isos: FixedI16<U*> ↔ i16 ──────────────────────────

const fn q000i016_fwd(q: FixedI16<U0>) -> i16 {
    q.to_bits()
}
const fn q000i016_bk(i: i16) -> FixedI16<U0> {
    FixedI16::<U0>::from_bits(i)
}

const fn q015i016_fwd(q: FixedI16<U15>) -> i16 {
    q.to_bits()
}
const fn q015i016_bk(i: i16) -> FixedI16<U15> {
    FixedI16::<U15>::from_bits(i)
}

crate::iso! {
    /// `FixedI16<U0> ↔ i16` — Q16.0 lossless iso. Degenerate Galois.
    pub Q000I016 : FixedI16<U0> => i16 {
        forward: q000i016_fwd,
        back:    q000i016_bk,
    }
}

crate::iso! {
    /// `FixedI16<U15> ↔ i16` — signed normalized Q1.15 lossless bit iso.
    /// Numeric Q values cover `[-1, 1 - 2^-15]`; the primitive carries
    /// the same two's-complement storage bits.
    pub Q015I016 : FixedI16<U15> => i16 {
        forward: q015i016_fwd,
        back:    q015i016_bk,
    }
}

// ── Q-format ladder over `FixedI16<Frac>` ──────────────────────────

/// `I### = FixedI16<U<frac>>` — i16-backed binary fixed-point.
pub type I000 = FixedI16<U0>;
pub type I002 = FixedI16<U2>;
pub type I004 = FixedI16<U4>;
pub type I008 = FixedI16<U8>;
pub type I012 = FixedI16<U12>;
pub type I016 = FixedI16<U16>;

macro_rules! fix_fix_i16 {
    ($const_name:ident, $FineFrac:ty, $CoarseFrac:ty) => {
#[rustfmt::skip]
        #[doc = concat!(
            "`FixedI16<",
            stringify!($FineFrac),
            "> → FixedI16<",
            stringify!($CoarseFrac),
            ">` frac-level convert (i16-backed)."
        )]
        pub const $const_name: $crate::conn::Conn<FixedI16<$FineFrac>, FixedI16<$CoarseFrac>> = {
            const SHIFT: u32 = <$FineFrac as Unsigned>::U32 - <$CoarseFrac as Unsigned>::U32;
            const RATIO: i32 = 1_i32 << SHIFT;
            const FINE_MIN: i16 = i16::MIN;
            const FINE_MAX: i16 = i16::MAX;

            fn ceil(x: FixedI16<$FineFrac>) -> FixedI16<$CoarseFrac> {
                if x.to_bits() == FINE_MIN {
                    return FixedI16::<$CoarseFrac>::from_bits(i16::MIN);
                }
                let bits = x.to_bits() as i32;
                let q = bits.div_euclid(RATIO);
                let r = bits.rem_euclid(RATIO);
                let res = if r != 0 { q + 1 } else { q };
                FixedI16::from_bits(res as i16)
            }

            fn inner(x: FixedI16<$CoarseFrac>) -> FixedI16<$FineFrac> {
                let res = (x.to_bits() as i32) * RATIO;
                let saturated = if res > FINE_MAX as i32 {
                    FINE_MAX
                } else if res < FINE_MIN as i32 {
                    FINE_MIN
                } else {
                    res as i16
                };
                FixedI16::from_bits(saturated)
            }

            $crate::conn::Conn::new_l(ceil, inner)
        };
    };
}

fix_fix_i16!(Q002Q000, U2, U0);
fix_fix_i16!(Q004Q000, U4, U0);
fix_fix_i16!(Q008Q000, U8, U0);
fix_fix_i16!(Q012Q000, U12, U0);
fix_fix_i16!(Q016Q000, U16, U0);
fix_fix_i16!(Q004Q002, U4, U2);
fix_fix_i16!(Q008Q002, U8, U2);
fix_fix_i16!(Q012Q002, U12, U2);
fix_fix_i16!(Q016Q002, U16, U2);
fix_fix_i16!(Q008Q004, U8, U4);
fix_fix_i16!(Q012Q004, U12, U4);
fix_fix_i16!(Q016Q004, U16, U4);
fix_fix_i16!(Q012Q008, U12, U8);
fix_fix_i16!(Q016Q008, U16, U8);
fix_fix_i16!(Q016Q012, U16, U12);

// ── f32 → FixedI16<U<frac>> narrowing ──────────────────────────────

float_fixed!(pub F032Q000, f32, FixedI16, U0,  i16);
float_fixed!(pub F032Q002, f32, FixedI16, U2,  i16);
float_fixed!(pub F032Q004, f32, FixedI16, U4,  i16);
float_fixed!(pub F032Q008, f32, FixedI16, U8,  i16);
float_fixed!(pub F032Q012, f32, FixedI16, U12, i16);
float_fixed!(pub F032Q016, f32, FixedI16, U16, i16);

// ── f64 → FixedI16<U<frac>> narrowing ──────────────────────────────

float_fixed!(pub F064Q000, f64, FixedI16, U0,  i16);
float_fixed!(pub F064Q002, f64, FixedI16, U2,  i16);
float_fixed!(pub F064Q004, f64, FixedI16, U4,  i16);
float_fixed!(pub F064Q008, f64, FixedI16, U8,  i16);
float_fixed!(pub F064Q012, f64, FixedI16, U12, i16);
float_fixed!(pub F064Q016, f64, FixedI16, U16, i16);

// ── f16 → FixedI16<U<frac>> narrowing (L-only; gated on `f16`) ────

#[cfg(feature = "f16")]
float_fixed_l!(pub F016Q000, f16, FixedI16, U0,  i16);
#[cfg(feature = "f16")]
float_fixed_l!(pub F016Q002, f16, FixedI16, U2,  i16);
#[cfg(feature = "f16")]
float_fixed_l!(pub F016Q004, f16, FixedI16, U4,  i16);
#[cfg(feature = "f16")]
float_fixed_l!(pub F016Q008, f16, FixedI16, U8,  i16);
#[cfg(feature = "f16")]
float_fixed_l!(pub F016Q012, f16, FixedI16, U12, i16);
#[cfg(feature = "f16")]
float_fixed_l!(pub F016Q016, f16, FixedI16, U16, i16);

// ────────────────────────────────────────────────────────────────────
// Tests
// ────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    #[allow(unused_imports)]
    use crate::conn::{ConnL, ConnR};
    use proptest::prelude::*;

    #[test]
    fn spot_q008q004_on_grid() {
        let q88 = FixedI16::<U8>::from_bits(384);
        assert_eq!(
            crate::conn::ceil(&Q008Q004, q88),
            FixedI16::<U4>::from_bits(24)
        );
        assert_eq!(
            crate::conn::upper(&Q008Q004, FixedI16::<U4>::from_bits(24)),
            q88
        );
    }

    #[test]
    fn spot_q008q004_off_grid_positive() {
        let off = FixedI16::<U8>::from_bits(358);
        assert_eq!(
            crate::conn::ceil(&Q008Q004, off),
            FixedI16::<U4>::from_bits(23)
        );
    }

    #[test]
    fn spot_q008q004_off_grid_negative() {
        let neg = FixedI16::<U8>::from_bits(-358);
        assert_eq!(
            crate::conn::ceil(&Q008Q004, neg),
            FixedI16::<U4>::from_bits(-22)
        );
    }

    #[test]
    fn spot_q008q004_saturation_boundary() {
        let fmax = FixedI16::<U8>::from_bits(i16::MAX);
        assert_eq!(
            crate::conn::ceil(&Q008Q004, fmax),
            FixedI16::<U4>::from_bits(2048)
        );
        assert_eq!(
            crate::conn::upper(&Q008Q004, FixedI16::<U4>::from_bits(2048)),
            fmax
        );

        let fmin = FixedI16::<U8>::from_bits(i16::MIN);
        assert_eq!(
            crate::conn::ceil(&Q008Q004, fmin),
            FixedI16::<U4>::from_bits(i16::MIN)
        );
    }

    #[test]
    fn spot_q016q000_degenerate() {
        assert_eq!(
            crate::conn::upper(&Q016Q000, FixedI16::<U0>::from_bits(0)),
            FixedI16::<U16>::from_bits(0),
        );
        assert_eq!(
            crate::conn::upper(&Q016Q000, FixedI16::<U0>::from_bits(1)),
            FixedI16::<U16>::from_bits(i16::MAX),
        );
        assert_eq!(
            crate::conn::upper(&Q016Q000, FixedI16::<U0>::from_bits(-1)),
            FixedI16::<U16>::from_bits(i16::MIN),
        );
    }

    macro_rules! props_for_pair {
        ($mod_name:ident, $conn:ident, $FineFrac:ty, $CoarseFrac:ty) => {
            $crate::law_battery! {
                mod $mod_name,
                conn: $conn,
                fine:   prop_oneof![
                    1 => Just(FixedI16::<$FineFrac>::from_bits(i16::MIN)),
                    1 => Just(FixedI16::<$FineFrac>::from_bits(i16::MAX)),
                    1 => Just(FixedI16::<$FineFrac>::from_bits(0)),
                    8 => any::<i16>().prop_map(FixedI16::<$FineFrac>::from_bits),
                ],
                coarse: prop_oneof![
                    1 => Just(FixedI16::<$CoarseFrac>::from_bits(i16::MIN)),
                    1 => Just(FixedI16::<$CoarseFrac>::from_bits(i16::MAX)),
                    1 => Just(FixedI16::<$CoarseFrac>::from_bits(0)),
                    8 => any::<i16>().prop_map(FixedI16::<$CoarseFrac>::from_bits),
                ],
                subset: l_only,
            }
        };
    }

    props_for_pair!(q002q000, Q002Q000, U2, U0);
    props_for_pair!(q004q000, Q004Q000, U4, U0);
    props_for_pair!(q008q000, Q008Q000, U8, U0);
    props_for_pair!(q012q000, Q012Q000, U12, U0);
    props_for_pair!(q016q000, Q016Q000, U16, U0);
    props_for_pair!(q004q002, Q004Q002, U4, U2);
    props_for_pair!(q008q002, Q008Q002, U8, U2);
    props_for_pair!(q012q002, Q012Q002, U12, U2);
    props_for_pair!(q016q002, Q016Q002, U16, U2);
    props_for_pair!(q008q004, Q008Q004, U8, U4);
    props_for_pair!(q012q004, Q012Q004, U12, U4);
    props_for_pair!(q016q004, Q016Q004, U16, U4);
    props_for_pair!(q012q008, Q012Q008, U12, U8);
    props_for_pair!(q016q008, Q016Q008, U16, U8);
    props_for_pair!(q016q012, Q016Q012, U16, U12);
}
