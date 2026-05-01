//! Binary fixed-point ladder over `fixed::FixedI64<Frac>`.
//!
//! Frac level set: `{U0, U8, U16, U32, U48, U64}` → 15 ordered pairs
//! `(Fine, Coarse)` with `Fine > Coarse`. See [`super::i16`] for the
//! design (this module mirrors it with `i64` inner / `i128` widening).

use super::{ext_int, int_int_narrow, nz_int_ext, uint_int_sat};
use ::fixed::FixedI64;
use ::fixed::types::extra::{U0, U8, U16, U32, U48, U64, Unsigned};
use core::num::NonZeroI64;

// ── §1 std-int Conns landing on `i64` ───────────────────────────────

ext_int!(I008I064, i8, i64);
ext_int!(I016I064, i16, i64);
ext_int!(I032I064, i32, i64);
ext_int!(U008I064, u8, i64);
ext_int!(U016I064, u16, i64);
ext_int!(U032I064, u32, i64);

int_int_narrow!(I128I064, i128, i64);

uint_int_sat!(U064I064, u64, i64);
uint_int_sat!(U128I064, u128, i64);

// ── §2 i64 ↔ NonZeroI64 ──────────────────────────────────

nz_int_ext!(I064N064, i64, NonZeroI64);

// ── §3 cross-crate iso: FixedI64<U0> ↔ i64 ─────────────────────────

const fn q000i064_fwd(q: FixedI64<U0>) -> i64 {
    q.to_bits()
}
const fn q000i064_bk(i: i64) -> FixedI64<U0> {
    FixedI64::<U0>::from_bits(i)
}

crate::iso! {
    /// `FixedI64<U0> ↔ i64` — Q64.0 lossless iso. Degenerate Galois.
    pub Q000I064 : FixedI64<U0> => i64 {
        forward: q000i064_fwd,
        back:    q000i064_bk,
    }
}

// ── §4 Q-format ladder over `FixedI64<Frac>` ────────────────────────

/// `I<frac> = FixedI64<U<frac>>` — i64-backed binary fixed-point.
pub type I000 = FixedI64<U0>;
pub type I008 = FixedI64<U8>;
pub type I016 = FixedI64<U16>;
pub type I032 = FixedI64<U32>;
pub type I048 = FixedI64<U48>;
pub type I064 = FixedI64<U64>;

macro_rules! fix_fix_i64 {
    ($const_name:ident, $FineFrac:ty, $CoarseFrac:ty) => {
#[rustfmt::skip]
        #[doc = concat!(
            "`FixedI64<",
            stringify!($FineFrac),
            "> → FixedI64<",
            stringify!($CoarseFrac),
            ">` frac-level convert (i64-backed)."
        )]
        pub struct $const_name;

        impl $const_name {
            const SHIFT: u32 = <$FineFrac as Unsigned>::U32 - <$CoarseFrac as Unsigned>::U32;
            // i128 covers SHIFT ∈ [1, 64]: 1 << 64 = 2^64 fits, and
            // i64::MAX × 2^64 ≈ 2^127 < i128::MAX.
            const RATIO: i128 = 1_i128 << Self::SHIFT;
            const FINE_MIN: i64 = i64::MIN;
            const FINE_MAX: i64 = i64::MAX;

            const fn _ceil(x: FixedI64<$FineFrac>) -> FixedI64<$CoarseFrac> {
                if x.to_bits() == Self::FINE_MIN {
                    return FixedI64::<$CoarseFrac>::from_bits(i64::MIN);
                }
                let bits = x.to_bits() as i128;
                let q = bits.div_euclid(Self::RATIO);
                let r = bits.rem_euclid(Self::RATIO);
                let res = if r != 0 { q + 1 } else { q };
                FixedI64::from_bits(res as i64)
            }

            const fn _inner(x: FixedI64<$CoarseFrac>) -> FixedI64<$FineFrac> {
                let res = (x.to_bits() as i128) * Self::RATIO;
                let saturated = if res > Self::FINE_MAX as i128 {
                    Self::FINE_MAX
                } else if res < Self::FINE_MIN as i128 {
                    Self::FINE_MIN
                } else {
                    res as i64
                };
                FixedI64::from_bits(saturated)
            }
        }

        // (Plan 32) ConnL only — `_inner` non-injective at saturation.
        impl $crate::conn::ViewL<FixedI64<$FineFrac>, FixedI64<$CoarseFrac>> for $const_name {
            const L: $crate::conn::ConnL<FixedI64<$FineFrac>, FixedI64<$CoarseFrac>> =
                $crate::conn::Conn::new_l($const_name::_ceil, $const_name::_inner);
        }
    };
}

// 15 ordered pairs from {U0, U8, U16, U32, U48, U64}.
fix_fix_i64!(Q008Q000, U8, U0);
fix_fix_i64!(Q016Q000, U16, U0);
fix_fix_i64!(Q032Q000, U32, U0);
fix_fix_i64!(Q048Q000, U48, U0);
fix_fix_i64!(Q064Q000, U64, U0);
fix_fix_i64!(Q016Q008, U16, U8);
fix_fix_i64!(Q032Q008, U32, U8);
fix_fix_i64!(Q048Q008, U48, U8);
fix_fix_i64!(Q064Q008, U64, U8);
fix_fix_i64!(Q032Q016, U32, U16);
fix_fix_i64!(Q048Q016, U48, U16);
fix_fix_i64!(Q064Q016, U64, U16);
fix_fix_i64!(Q048Q032, U48, U32);
fix_fix_i64!(Q064Q032, U64, U32);
fix_fix_i64!(Q064Q048, U64, U48);

// ────────────────────────────────────────────────────────────────────
// Tests
// ────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    #[allow(unused_imports)]
    use crate::conn::{ViewL, ViewR};
    use crate::extended::Extended;
    use proptest::prelude::*;

    // ── §1 std-int spot checks (merged from former int/i64.rs) ─────

    // (Plan 32) `floor` arms removed; `ext_int!` is now ConnL.
    #[test]
    fn i032i064_extends_to_one_above() {
        assert_eq!(I032I064.ceil(Extended::PosInf), (i32::MAX as i64) + 1);
        assert_eq!(I032I064.ceil(Extended::NegInf), i64::MIN);
    }

    #[test]
    fn u032i064_extends_to_one_above() {
        assert_eq!(U032I064.ceil(Extended::PosInf), 4_294_967_296);
        assert_eq!(U032I064.ceil(Extended::NegInf), i64::MIN);
    }

    #[test]
    fn i128i064_saturate_and_fixup() {
        assert_eq!(I128I064.ceil(i128::MAX), i64::MAX);
        assert_eq!(I128I064.ceil(i128::MIN), i64::MIN);
        assert_eq!(I128I064.inner(i64::MAX), i128::MAX);
        assert_eq!(I128I064.inner(i64::MIN), i64::MIN as i128);
    }

    #[test]
    fn u_to_i64_neg_and_high() {
        assert_eq!(U064I064.inner(-1), 0_u64);
        assert_eq!(U064I064.floor(u64::MAX), i64::MAX);
        assert_eq!(U128I064.inner(i64::MIN), 0_u128);
        assert_eq!(U128I064.floor(u128::MAX), i64::MAX);
    }

    // ── §4 Q-format spot checks ────────────────────────────────────

    #[test]
    fn spot_q032q016_on_grid() {
        // 1.5 in Q32.32 (bits = 1.5 × 2^32) round-trips through Q48.16.
        // (Plan 32: ConnL only.)
        let bits_3232: i64 = 3 << 31;
        let q3232 = FixedI64::<U32>::from_bits(bits_3232);
        assert_eq!(Q032Q016.ceil(q3232), FixedI64::<U16>::from_bits(3 << 15));
    }

    #[test]
    fn spot_q064q000_degenerate() {
        // SHIFT = 64. Only Coarse(0) round-trips; ±1 saturates inner.
        assert_eq!(
            Q064Q000.inner(FixedI64::<U0>::from_bits(0)),
            FixedI64::<U64>::from_bits(0),
        );
        assert_eq!(
            Q064Q000.inner(FixedI64::<U0>::from_bits(1)),
            FixedI64::<U64>::from_bits(i64::MAX),
        );
        assert_eq!(
            Q064Q000.inner(FixedI64::<U0>::from_bits(-1)),
            FixedI64::<U64>::from_bits(i64::MIN),
        );
    }

    #[test]
    fn spot_boundary_fixups() {
        // Fine::MIN ceil fixup. (Plan 32: floor removed.)
        let fmin = FixedI64::<U32>::from_bits(i64::MIN);
        assert_eq!(Q032Q016.ceil(fmin), FixedI64::<U16>::from_bits(i64::MIN));
    }

    // 15 conns × 9 properties = 135 generated proptests (64 cases each)
    // — i64 generators are expensive, so cap via `cases: 64`.
    macro_rules! props_for_pair {
        ($mod_name:ident, $conn:ident, $FineFrac:ty, $CoarseFrac:ty) => {
            $crate::law_battery! {
                mod $mod_name,
                conn: $conn,
                fine:   any::<i64>().prop_map(FixedI64::<$FineFrac>::from_bits),
                coarse: any::<i64>().prop_map(FixedI64::<$CoarseFrac>::from_bits),
                subset: l_only,
                cases: 64,
            }
        };
    }

    props_for_pair!(q008q000, Q008Q000, U8, U0);
    props_for_pair!(q016q000, Q016Q000, U16, U0);
    props_for_pair!(q032q000, Q032Q000, U32, U0);
    props_for_pair!(q048q000, Q048Q000, U48, U0);
    props_for_pair!(q064q000, Q064Q000, U64, U0);
    props_for_pair!(q016q008, Q016Q008, U16, U8);
    props_for_pair!(q032q008, Q032Q008, U32, U8);
    props_for_pair!(q048q008, Q048Q008, U48, U8);
    props_for_pair!(q064q008, Q064Q008, U64, U8);
    props_for_pair!(q032q016, Q032Q016, U32, U16);
    props_for_pair!(q048q016, Q048Q016, U48, U16);
    props_for_pair!(q064q016, Q064Q016, U64, U16);
    props_for_pair!(q048q032, Q048Q032, U48, U32);
    props_for_pair!(q064q032, Q064Q032, U64, U32);
    props_for_pair!(q064q048, Q064Q048, U64, U48);
}
