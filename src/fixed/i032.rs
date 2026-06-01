//! Binary fixed-point ladder over `fixed::FixedI32<Frac>`, plus the
//! cross-crate iso to `i32` and the IEEE-float → `FixedI32<F>` bridges.
//!
//! Pure-`core` Conns sourced from `i32` live next door in
//! [`crate::core::i032`].

use super::{float_fixed, float_fixed_l};
use ::fixed::FixedI32;
use ::fixed::types::extra::{U0, U4, U8, U16, U24, U31, U32, Unsigned};

// ── Cross-crate isos: FixedI32<U*> ↔ i32 ──────────────────────────

const fn q000i032_fwd(q: FixedI32<U0>) -> i32 {
    q.to_bits()
}
const fn q000i032_bk(i: i32) -> FixedI32<U0> {
    FixedI32::<U0>::from_bits(i)
}

const fn q031i032_fwd(q: FixedI32<U31>) -> i32 {
    q.to_bits()
}
const fn q031i032_bk(i: i32) -> FixedI32<U31> {
    FixedI32::<U31>::from_bits(i)
}

crate::iso! {
    /// `FixedI32<U0> ↔ i32` — Q32.0 lossless iso. Degenerate Galois.
    pub Q000I032 : FixedI32<U0> => i32 {
        forward: q000i032_fwd,
        back:    q000i032_bk,
    }
}

crate::iso! {
    /// `FixedI32<U31> ↔ i32` — signed normalized Q1.31 lossless bit iso.
    /// Numeric Q values cover `[-1, 1 - 2^-31]`; the primitive carries
    /// the same two's-complement storage bits.
    pub Q031I032 : FixedI32<U31> => i32 {
        forward: q031i032_fwd,
        back:    q031i032_bk,
    }
}

// ── Q-format ladder over `FixedI32<Frac>` ──────────────────────────

pub type I000 = FixedI32<U0>;
pub type I004 = FixedI32<U4>;
pub type I008 = FixedI32<U8>;
pub type I016 = FixedI32<U16>;
pub type I024 = FixedI32<U24>;
pub type I032 = FixedI32<U32>;

macro_rules! fix_fix_i32 {
    ($const_name:ident, $FineFrac:ty, $CoarseFrac:ty) => {
#[rustfmt::skip]
        #[doc = concat!(
            "`FixedI32<",
            stringify!($FineFrac),
            "> → FixedI32<",
            stringify!($CoarseFrac),
            ">` frac-level convert (i32-backed)."
        )]
        pub const $const_name: $crate::conn::Conn<FixedI32<$FineFrac>, FixedI32<$CoarseFrac>> = {
            const SHIFT: u32 = <$FineFrac as Unsigned>::U32 - <$CoarseFrac as Unsigned>::U32;
            const RATIO: i64 = 1_i64 << SHIFT;
            const FINE_MIN: i32 = i32::MIN;
            const FINE_MAX: i32 = i32::MAX;

            fn ceil(x: FixedI32<$FineFrac>) -> FixedI32<$CoarseFrac> {
                if x.to_bits() == FINE_MIN {
                    return FixedI32::<$CoarseFrac>::from_bits(i32::MIN);
                }
                let bits = x.to_bits() as i64;
                let q = bits.div_euclid(RATIO);
                let r = bits.rem_euclid(RATIO);
                let res = if r != 0 { q + 1 } else { q };
                FixedI32::from_bits(res as i32)
            }

            fn inner(x: FixedI32<$CoarseFrac>) -> FixedI32<$FineFrac> {
                let res = (x.to_bits() as i64) * RATIO;
                let saturated = if res > FINE_MAX as i64 {
                    FINE_MAX
                } else if res < FINE_MIN as i64 {
                    FINE_MIN
                } else {
                    res as i32
                };
                FixedI32::from_bits(saturated)
            }

            $crate::conn::Conn::new_l(ceil, inner)
        };
    };
}

fix_fix_i32!(Q004Q000, U4, U0);
fix_fix_i32!(Q008Q000, U8, U0);
fix_fix_i32!(Q016Q000, U16, U0);
fix_fix_i32!(Q024Q000, U24, U0);
fix_fix_i32!(Q032Q000, U32, U0);
fix_fix_i32!(Q008Q004, U8, U4);
fix_fix_i32!(Q016Q004, U16, U4);
fix_fix_i32!(Q024Q004, U24, U4);
fix_fix_i32!(Q032Q004, U32, U4);
fix_fix_i32!(Q016Q008, U16, U8);
fix_fix_i32!(Q024Q008, U24, U8);
fix_fix_i32!(Q032Q008, U32, U8);
fix_fix_i32!(Q024Q016, U24, U16);
fix_fix_i32!(Q032Q016, U32, U16);
fix_fix_i32!(Q032Q024, U32, U24);

// ── f32 → FixedI32<U<frac>> narrowing (L-only) ────────────────────

float_fixed_l!(pub F032Q000, f32, FixedI32, U0,  i32);
float_fixed_l!(pub F032Q004, f32, FixedI32, U4,  i32);
float_fixed_l!(pub F032Q008, f32, FixedI32, U8,  i32);
float_fixed_l!(pub F032Q016, f32, FixedI32, U16, i32);
float_fixed_l!(pub F032Q024, f32, FixedI32, U24, i32);
float_fixed_l!(pub F032Q032, f32, FixedI32, U32, i32);

// ── f64 → FixedI32<U<frac>> narrowing (full triple) ───────────────

float_fixed!(pub F064Q000, f64, FixedI32, U0,  i32);
float_fixed!(pub F064Q004, f64, FixedI32, U4,  i32);
float_fixed!(pub F064Q008, f64, FixedI32, U8,  i32);
float_fixed!(pub F064Q016, f64, FixedI32, U16, i32);
float_fixed!(pub F064Q024, f64, FixedI32, U24, i32);
float_fixed!(pub F064Q032, f64, FixedI32, U32, i32);

// ── f16 → FixedI32<U<frac>> narrowing (L-only; gated on `f16`) ────

#[cfg(feature = "f16")]
float_fixed_l!(pub F016Q000, f16, FixedI32, U0,  i32);
#[cfg(feature = "f16")]
float_fixed_l!(pub F016Q004, f16, FixedI32, U4,  i32);
#[cfg(feature = "f16")]
float_fixed_l!(pub F016Q008, f16, FixedI32, U8,  i32);
#[cfg(feature = "f16")]
float_fixed_l!(pub F016Q016, f16, FixedI32, U16, i32);
#[cfg(feature = "f16")]
float_fixed_l!(pub F016Q024, f16, FixedI32, U24, i32);
#[cfg(feature = "f16")]
float_fixed_l!(pub F016Q032, f16, FixedI32, U32, i32);

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
    fn spot_q016q008_on_grid() {
        let q1616 = FixedI32::<U16>::from_bits(98304);
        assert_eq!(
            crate::conn::ceil(&Q016Q008, q1616),
            FixedI32::<U8>::from_bits(384)
        );
        assert_eq!(
            crate::conn::upper(&Q016Q008, FixedI32::<U8>::from_bits(384)),
            q1616
        );
    }

    #[test]
    fn spot_q032q000_degenerate() {
        assert_eq!(
            crate::conn::upper(&Q032Q000, FixedI32::<U0>::from_bits(0)),
            FixedI32::<U32>::from_bits(0),
        );
        assert_eq!(
            crate::conn::upper(&Q032Q000, FixedI32::<U0>::from_bits(1)),
            FixedI32::<U32>::from_bits(i32::MAX),
        );
        assert_eq!(
            crate::conn::upper(&Q032Q000, FixedI32::<U0>::from_bits(-1)),
            FixedI32::<U32>::from_bits(i32::MIN),
        );
    }

    #[test]
    fn spot_boundary_fixups() {
        let fmin = FixedI32::<U16>::from_bits(i32::MIN);
        assert_eq!(
            crate::conn::ceil(&Q016Q008, fmin),
            FixedI32::<U8>::from_bits(i32::MIN)
        );
    }

    macro_rules! props_for_pair {
        ($mod_name:ident, $conn:ident, $FineFrac:ty, $CoarseFrac:ty) => {
            $crate::law_battery! {
                mod $mod_name,
                conn: $conn,
                fine:   prop_oneof![
                    1 => Just(FixedI32::<$FineFrac>::from_bits(i32::MIN)),
                    1 => Just(FixedI32::<$FineFrac>::from_bits(i32::MAX)),
                    1 => Just(FixedI32::<$FineFrac>::from_bits(0)),
                    8 => any::<i32>().prop_map(FixedI32::<$FineFrac>::from_bits),
                ],
                coarse: prop_oneof![
                    1 => Just(FixedI32::<$CoarseFrac>::from_bits(i32::MIN)),
                    1 => Just(FixedI32::<$CoarseFrac>::from_bits(i32::MAX)),
                    1 => Just(FixedI32::<$CoarseFrac>::from_bits(0)),
                    8 => any::<i32>().prop_map(FixedI32::<$CoarseFrac>::from_bits),
                ],
                subset: l_only,
            }
        };
    }

    props_for_pair!(q004q000, Q004Q000, U4, U0);
    props_for_pair!(q008q000, Q008Q000, U8, U0);
    props_for_pair!(q016q000, Q016Q000, U16, U0);
    props_for_pair!(q024q000, Q024Q000, U24, U0);
    props_for_pair!(q032q000, Q032Q000, U32, U0);
    props_for_pair!(q008q004, Q008Q004, U8, U4);
    props_for_pair!(q016q004, Q016Q004, U16, U4);
    props_for_pair!(q024q004, Q024Q004, U24, U4);
    props_for_pair!(q032q004, Q032Q004, U32, U4);
    props_for_pair!(q016q008, Q016Q008, U16, U8);
    props_for_pair!(q024q008, Q024Q008, U24, U8);
    props_for_pair!(q032q008, Q032Q008, U32, U8);
    props_for_pair!(q024q016, Q024Q016, U24, U16);
    props_for_pair!(q032q016, Q032Q016, U32, U16);
    props_for_pair!(q032q024, Q032Q024, U32, U24);
}
