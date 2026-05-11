//! Binary fixed-point ladder over `fixed::FixedI128<Frac>`, plus the
//! cross-crate iso to `i128` and the IEEE-float → `FixedI128<F>` bridges.
//!
//! Pure-`core` Conns sourced from `i128` (signed narrowing,
//! two's-complement B2/L2 byte iso, `i128 ↔ NonZeroI128`, …) live next
//! door in [`crate::core::i128`].
//!
//! Stable Rust has no native `i256` to widen through, so the i64-style
//! `(x.to_bits() as i128) * RATIO` pattern doesn't compose. Instead we
//! use [`i128::checked_mul`] + saturate, and [`i128::checked_shl`] to
//! detect the `SHIFT == 128` degenerate case (`Q128Q000`, where
//! `RATIO = 2^128` doesn't fit in `i128` at all).

use super::float_fixed_l;
use ::fixed::FixedI128;
use ::fixed::types::extra::{U0, U16, U32, U64, U96, U127, U128, Unsigned};

// ── Cross-crate isos: FixedI128<U*> ↔ i128 ────────────────────────

const fn q000i128_fwd(q: FixedI128<U0>) -> i128 {
    q.to_bits()
}
const fn q000i128_bk(i: i128) -> FixedI128<U0> {
    FixedI128::<U0>::from_bits(i)
}

const fn q127i128_fwd(q: FixedI128<U127>) -> i128 {
    q.to_bits()
}
const fn q127i128_bk(i: i128) -> FixedI128<U127> {
    FixedI128::<U127>::from_bits(i)
}

crate::iso! {
    /// `FixedI128<U0> ↔ i128` — Q128.0 lossless iso. Degenerate Galois.
    pub Q000I128 : FixedI128<U0> => i128 {
        forward: q000i128_fwd,
        back:    q000i128_bk,
    }
}

crate::iso! {
    /// `FixedI128<U127> ↔ i128` — signed normalized Q1.127 lossless bit iso.
    /// Numeric Q values cover `[-1, 1 - 2^-127]`; the primitive carries
    /// the same two's-complement storage bits.
    pub Q127I128 : FixedI128<U127> => i128 {
        forward: q127i128_fwd,
        back:    q127i128_bk,
    }
}

// ── Q-format ladder over `FixedI128<Frac>` ─────────────────────────

pub type I000 = FixedI128<U0>;
pub type I016 = FixedI128<U16>;
pub type I032 = FixedI128<U32>;
pub type I064 = FixedI128<U64>;
pub type I096 = FixedI128<U96>;
pub type I128 = FixedI128<U128>;

macro_rules! fix_fix_i128 {
    ($const_name:ident, $FineFrac:ty, $CoarseFrac:ty) => {
#[rustfmt::skip]
        #[doc = concat!(
            "`FixedI128<",
            stringify!($FineFrac),
            "> → FixedI128<",
            stringify!($CoarseFrac),
            ">` frac-level convert (i128-backed)."
        )]
        pub const $const_name: $crate::conn::Conn<FixedI128<$FineFrac>, FixedI128<$CoarseFrac>> = {
            const SHIFT: u32 = <$FineFrac as Unsigned>::U32 - <$CoarseFrac as Unsigned>::U32;
            const RATIO: Option<i128> = 1_i128.checked_shl(SHIFT);
            const FINE_MIN: i128 = i128::MIN;
            const FINE_MAX: i128 = i128::MAX;

            fn ceil(x: FixedI128<$FineFrac>) -> FixedI128<$CoarseFrac> {
                if x.to_bits() == FINE_MIN {
                    return FixedI128::<$CoarseFrac>::from_bits(i128::MIN);
                }
                let bits = x.to_bits();
                match RATIO {
                    Some(r) => {
                        let q = bits.div_euclid(r);
                        let res = if bits.rem_euclid(r) != 0 { q + 1 } else { q };
                        FixedI128::from_bits(res)
                    }
                    None => {
                        if bits > 0 {
                            FixedI128::from_bits(1)
                        } else {
                            FixedI128::from_bits(0)
                        }
                    }
                }
            }

            fn inner(x: FixedI128<$CoarseFrac>) -> FixedI128<$FineFrac> {
                let bits = x.to_bits();
                let saturated = match RATIO {
                    Some(r) => match bits.checked_mul(r) {
                        Some(v) => v,
                        None => {
                            if bits > 0 {
                                FINE_MAX
                            } else {
                                FINE_MIN
                            }
                        }
                    },
                    None => {
                        if bits == 0 {
                            0
                        } else if bits > 0 {
                            FINE_MAX
                        } else {
                            FINE_MIN
                        }
                    }
                };
                FixedI128::from_bits(saturated)
            }

            $crate::conn::Conn::new_l(ceil, inner)
        };
    };
}

fix_fix_i128!(Q016Q000, U16, U0);
fix_fix_i128!(Q032Q000, U32, U0);
fix_fix_i128!(Q064Q000, U64, U0);
fix_fix_i128!(Q096Q000, U96, U0);
fix_fix_i128!(Q128Q000, U128, U0);
fix_fix_i128!(Q032Q016, U32, U16);
fix_fix_i128!(Q064Q016, U64, U16);
fix_fix_i128!(Q096Q016, U96, U16);
fix_fix_i128!(Q128Q016, U128, U16);
fix_fix_i128!(Q064Q032, U64, U32);
fix_fix_i128!(Q096Q032, U96, U32);
fix_fix_i128!(Q128Q032, U128, U32);
fix_fix_i128!(Q096Q064, U96, U64);
fix_fix_i128!(Q128Q064, U128, U64);
fix_fix_i128!(Q128Q096, U128, U96);

// ── f32 / f64 / f16 → FixedI128<U<frac>> narrowing (all L-only) ───

float_fixed_l!(pub F032Q000, f32, FixedI128, U0,   i128);
float_fixed_l!(pub F032Q016, f32, FixedI128, U16,  i128);
float_fixed_l!(pub F032Q032, f32, FixedI128, U32,  i128);
float_fixed_l!(pub F032Q064, f32, FixedI128, U64,  i128);
float_fixed_l!(pub F032Q096, f32, FixedI128, U96,  i128);
float_fixed_l!(pub F032Q128, f32, FixedI128, U128, i128);

float_fixed_l!(pub F064Q000, f64, FixedI128, U0,   i128);
float_fixed_l!(pub F064Q016, f64, FixedI128, U16,  i128);
float_fixed_l!(pub F064Q032, f64, FixedI128, U32,  i128);
float_fixed_l!(pub F064Q064, f64, FixedI128, U64,  i128);
float_fixed_l!(pub F064Q096, f64, FixedI128, U96,  i128);
float_fixed_l!(pub F064Q128, f64, FixedI128, U128, i128);

#[cfg(feature = "f16")]
float_fixed_l!(pub F016Q000, f16, FixedI128, U0,   i128);
#[cfg(feature = "f16")]
float_fixed_l!(pub F016Q016, f16, FixedI128, U16,  i128);
#[cfg(feature = "f16")]
float_fixed_l!(pub F016Q032, f16, FixedI128, U32,  i128);
#[cfg(feature = "f16")]
float_fixed_l!(pub F016Q064, f16, FixedI128, U64,  i128);
#[cfg(feature = "f16")]
float_fixed_l!(pub F016Q096, f16, FixedI128, U96,  i128);
#[cfg(feature = "f16")]
float_fixed_l!(pub F016Q128, f16, FixedI128, U128, i128);

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
    fn degenerate_max_shift() {
        assert_eq!(
            Q128Q000.upper(FixedI128::<U0>::from_bits(0)),
            FixedI128::<U128>::from_bits(0),
        );
        assert_eq!(
            Q128Q000.upper(FixedI128::<U0>::from_bits(1)),
            FixedI128::<U128>::from_bits(i128::MAX),
        );
        assert_eq!(
            Q128Q000.upper(FixedI128::<U0>::from_bits(-1)),
            FixedI128::<U128>::from_bits(i128::MIN),
        );
        assert_eq!(
            Q128Q000.ceil(FixedI128::<U128>::from_bits(0)),
            FixedI128::<U0>::from_bits(0),
        );
        assert_eq!(
            Q128Q000.ceil(FixedI128::<U128>::from_bits(1)),
            FixedI128::<U0>::from_bits(1),
        );
        assert_eq!(
            Q128Q000.ceil(FixedI128::<U128>::from_bits(-1)),
            FixedI128::<U0>::from_bits(0),
        );
        assert_eq!(
            Q128Q000.ceil(FixedI128::<U128>::from_bits(i128::MIN)),
            FixedI128::<U0>::from_bits(i128::MIN),
        );
    }

    #[test]
    fn spot_q128q064_on_grid() {
        let coarse_one = FixedI128::<U64>::from_bits(1);
        let fine_via_inner = Q128Q064.upper(coarse_one);
        assert_eq!(fine_via_inner, FixedI128::<U128>::from_bits(1_i128 << 64));
    }

    #[test]
    fn spot_boundary_fixups() {
        let fmin = FixedI128::<U128>::from_bits(i128::MIN);
        assert_eq!(Q128Q064.ceil(fmin), FixedI128::<U64>::from_bits(i128::MIN));
    }

    #[test]
    fn inner_saturates_on_overflow() {
        let big_coarse = FixedI128::<U16>::from_bits(i128::MAX);
        assert_eq!(
            Q128Q016.upper(big_coarse),
            FixedI128::<U128>::from_bits(i128::MAX),
        );
        let neg_coarse = FixedI128::<U16>::from_bits(i128::MIN);
        assert_eq!(
            Q128Q016.upper(neg_coarse),
            FixedI128::<U128>::from_bits(i128::MIN),
        );
    }

    macro_rules! props_for_pair {
        ($mod_name:ident, $conn:ident, $FineFrac:ty, $CoarseFrac:ty) => {
            $crate::law_battery! {
                mod $mod_name,
                conn: $conn,
                fine:   prop_oneof![
                    1 => Just(FixedI128::<$FineFrac>::from_bits(i128::MIN)),
                    1 => Just(FixedI128::<$FineFrac>::from_bits(i128::MAX)),
                    1 => Just(FixedI128::<$FineFrac>::from_bits(0)),
                    8 => any::<i128>().prop_map(FixedI128::<$FineFrac>::from_bits),
                ],
                coarse: prop_oneof![
                    1 => Just(FixedI128::<$CoarseFrac>::from_bits(i128::MIN)),
                    1 => Just(FixedI128::<$CoarseFrac>::from_bits(i128::MAX)),
                    1 => Just(FixedI128::<$CoarseFrac>::from_bits(0)),
                    8 => any::<i128>().prop_map(FixedI128::<$CoarseFrac>::from_bits),
                ],
                subset: l_only,
                cases: 64,
            }
        };
    }

    props_for_pair!(q016q000, Q016Q000, U16, U0);
    props_for_pair!(q032q000, Q032Q000, U32, U0);
    props_for_pair!(q064q000, Q064Q000, U64, U0);
    props_for_pair!(q096q000, Q096Q000, U96, U0);
    props_for_pair!(q128q000, Q128Q000, U128, U0);
    props_for_pair!(q032q016, Q032Q016, U32, U16);
    props_for_pair!(q064q016, Q064Q016, U64, U16);
    props_for_pair!(q096q016, Q096Q016, U96, U16);
    props_for_pair!(q128q016, Q128Q016, U128, U16);
    props_for_pair!(q064q032, Q064Q032, U64, U32);
    props_for_pair!(q096q032, Q096Q032, U96, U32);
    props_for_pair!(q128q032, Q128Q032, U128, U32);
    props_for_pair!(q096q064, Q096Q064, U96, U64);
    props_for_pair!(q128q064, Q128Q064, U128, U64);
    props_for_pair!(q128q096, Q128Q096, U128, U96);
}
