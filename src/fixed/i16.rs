//! Binary fixed-point ladder over `fixed::FixedI16<Frac>`.
//!
//! For each ordered pair `(FineFrac, CoarseFrac)` from the level set
//! `{0, 2, 4, 8, 12, 16}` with `FineFrac > CoarseFrac`, a
//! [`Conn`](crate::conn::Conn)`L<FixedI16<U_fine>, FixedI16<U_coarse>>`
//! constant `Q<dd>Q<dd>` (zero-padded) provides the left-Galois pair
//! `ceil ⊣ inner`:
//!
//! - `ceil:  Fine → Coarse` smallest `c` with `inner(c) ≥ f`
//! - `inner: Coarse → Fine`  bit-shift left by `(FineFrac − CoarseFrac)`,
//!   saturating at `Fine::{MIN, MAX}`
//!
//! Both functions are **total**. The four L-side Galois axioms
//! (adjointness, closure, kernel, monotonicity) hold for every input.
//!
//! **Why one-sided?** `inner` is **not** injective: any Coarse value
//! where `|c.bits * RATIO|` exceeds `i16::MAX` saturates to
//! `Fine::{MIN, MAX}`, collapsing a plateau of Coarse values onto a
//! single Fine value. Per the equivalence `inner order-reflecting ⟺
//! floor ≤ ceil`, no `floor` function can satisfy the rounding
//! sandwich at the plateau without breaking one of the per-side
//! Galois laws. Plan 32 demoted these from `conn_k!` to `Conn::new_l`
//! to remove the lie. `ceil` retains the FINE_MIN boundary fixup
//! (`ceil(Fine::MIN) = Coarse::MIN`) needed for galois_l at the
//! lower extreme.

use super::{ext_int, int_int_narrow, nz_int_ext, uint_int_sat};
use ::fixed::FixedI16;
use ::fixed::types::extra::{U0, U2, U4, U8, U12, U16, Unsigned};
use core::num::NonZeroI16;

// ── §1 std-int Conns landing on `i16` ───────────────────────────────

ext_int!(I008I016, i8, i16);
ext_int!(U008I016, u8, i16);

int_int_narrow!(I032I016, i32, i16);
int_int_narrow!(I064I016, i64, i16);
int_int_narrow!(I128I016, i128, i16);

uint_int_sat!(U016I016, u16, i16);
uint_int_sat!(U032I016, u32, i16);
uint_int_sat!(U064I016, u64, i16);
uint_int_sat!(U128I016, u128, i16);

// ── §2 i16 ↔ NonZeroI16 ──────────────────────────────────

nz_int_ext!(I016N016, i16, NonZeroI16);

// ── §3 cross-crate iso: FixedI16<U0> ↔ i16 ─────────────────────────

const fn q000i016_fwd(q: FixedI16<U0>) -> i16 {
    q.to_bits()
}
const fn q000i016_bk(i: i16) -> FixedI16<U0> {
    FixedI16::<U0>::from_bits(i)
}

crate::iso! {
    /// `FixedI16<U0> ↔ i16` — Q16.0 lossless iso. Degenerate Galois.
    pub Q000I016 : FixedI16<U0> => i16 {
        forward: q000i016_fwd,
        back:    q000i016_bk,
    }
}

// ── §4 Q-format ladder over `FixedI16<Frac>` ────────────────────────

/// `I<frac> = FixedI16<U<frac>>` — i16-backed binary fixed-point.
pub type I0 = FixedI16<U0>;
pub type I2 = FixedI16<U2>;
pub type I4 = FixedI16<U4>;
pub type I8 = FixedI16<U8>;
pub type I12 = FixedI16<U12>;
pub type I16 = FixedI16<U16>;

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
        pub struct $const_name;

        impl $const_name {
            const SHIFT: u32 = <$FineFrac as Unsigned>::U32 - <$CoarseFrac as Unsigned>::U32;
            // i32 covers SHIFT ∈ [1, 16]: 1 << 16 = 65 536 fits, and
            // i16::MAX × (1 << 16) = 2 147 418 112 < i32::MAX, so the
            // multiplication in `inner` cannot overflow i32 before the
            // saturating clamp.
            const RATIO: i32 = 1_i32 << Self::SHIFT;
            const FINE_MIN: i16 = i16::MIN;
            const FINE_MAX: i16 = i16::MAX;

            const fn _ceil(x: FixedI16<$FineFrac>) -> FixedI16<$CoarseFrac> {
                // Boundary fixup: every Coarse value c ≤ -i16::MAX/Self::RATIO
                // − 1 saturates inner to Fine::MIN. The Galois law
                // requires ceil(Fine::MIN) = Coarse::MIN.
                if x.to_bits() == Self::FINE_MIN {
                    return FixedI16::<$CoarseFrac>::from_bits(i16::MIN);
                }
                let bits = x.to_bits() as i32;
                let q = bits.div_euclid(Self::RATIO);
                let r = bits.rem_euclid(Self::RATIO);
                let res = if r != 0 { q + 1 } else { q };
                FixedI16::from_bits(res as i16)
            }

            const fn _inner(x: FixedI16<$CoarseFrac>) -> FixedI16<$FineFrac> {
                let res = (x.to_bits() as i32) * Self::RATIO;
                let saturated = if res > Self::FINE_MAX as i32 {
                    Self::FINE_MAX
                } else if res < Self::FINE_MIN as i32 {
                    Self::FINE_MIN
                } else {
                    res as i16
                };
                FixedI16::from_bits(saturated)
            }
        }

        // (Plan 32) ConnL only — `_inner` non-injective at saturation.
        impl $crate::conn::ConnL<FixedI16<$FineFrac>, FixedI16<$CoarseFrac>> for $const_name {
            #[inline]
            fn conn_l(
                &self,
            ) -> $crate::conn::Conn<FixedI16<$FineFrac>, FixedI16<$CoarseFrac>, $crate::conn::L>
            {
                $crate::conn::Conn::new_l($const_name::_ceil, $const_name::_inner)
            }
        }
    };
}

// All ordered (Fine, Coarse) pairs from {U0, U2, U4, U8, U12, U16}
// with Fine > Coarse. 15 conns total.
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

// ────────────────────────────────────────────────────────────────────
// Tests
// ────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    #[allow(unused_imports)]
    use crate::conn::{ConnL, ConnR};
    use crate::extended::Extended;
    use proptest::prelude::*;

    // ── §1 std-int spot checks (merged from former int/i16.rs) ─────

    #[test]
    fn i008i016_ceil_at_boundaries() {
        assert_eq!(I008I016.ceil(Extended::NegInf), i16::MIN);
        assert_eq!(I008I016.ceil(Extended::PosInf), 128);
        assert_eq!(I008I016.ceil(Extended::Finite(0)), 0);
        assert_eq!(I008I016.ceil(Extended::Finite(i8::MIN)), -128);
        assert_eq!(I008I016.ceil(Extended::Finite(i8::MAX)), 127);
    }

    // (Plan 32) `i008i016_floor_at_boundaries` removed: `ext_int!`
    // is now ConnL, no `.floor()` method.

    #[test]
    fn i008i016_inner_partitions_target_range() {
        assert_eq!(I008I016.upper(-129), Extended::NegInf);
        assert_eq!(I008I016.upper(i16::MIN), Extended::NegInf);
        assert_eq!(I008I016.upper(128), Extended::PosInf);
        assert_eq!(I008I016.upper(i16::MAX), Extended::PosInf);
        assert_eq!(I008I016.upper(-128), Extended::Finite(i8::MIN));
        assert_eq!(I008I016.upper(0), Extended::Finite(0));
        assert_eq!(I008I016.upper(127), Extended::Finite(i8::MAX));
    }

    #[test]
    fn u008i016_ceil_at_boundaries() {
        assert_eq!(U008I016.ceil(Extended::NegInf), i16::MIN);
        assert_eq!(U008I016.ceil(Extended::PosInf), 256);
        assert_eq!(U008I016.ceil(Extended::Finite(0)), 0);
        assert_eq!(U008I016.ceil(Extended::Finite(255)), 255);
    }

    // (Plan 32) `u008i016_floor_at_boundaries` removed: ConnL only.

    #[test]
    fn u008i016_inner_partitions_target_range() {
        assert_eq!(U008I016.upper(-1), Extended::NegInf);
        assert_eq!(U008I016.upper(i16::MIN), Extended::NegInf);
        assert_eq!(U008I016.upper(256), Extended::PosInf);
        assert_eq!(U008I016.upper(i16::MAX), Extended::PosInf);
        assert_eq!(U008I016.upper(0), Extended::Finite(0));
        assert_eq!(U008I016.upper(50), Extended::Finite(50));
        assert_eq!(U008I016.upper(255), Extended::Finite(255));
    }

    #[test]
    fn i_to_i16_saturate() {
        assert_eq!(I032I016.ceil(i32::MAX), i16::MAX);
        assert_eq!(I032I016.ceil(i32::MIN), i16::MIN);
        assert_eq!(I128I016.ceil(i128::MAX), i16::MAX);
        assert_eq!(I128I016.ceil(i128::MIN), i16::MIN);
    }

    #[test]
    fn i_to_i16_inner_fine_max_fixup() {
        assert_eq!(I032I016.upper(i16::MAX), i32::MAX);
        assert_eq!(I064I016.upper(i16::MAX), i64::MAX);
        assert_eq!(I128I016.upper(i16::MAX), i128::MAX);
        assert_eq!(I032I016.upper(0), 0_i32);
        assert_eq!(I032I016.upper(i16::MIN), i16::MIN as i32);
    }

    #[test]
    fn u_to_i16_neg_and_high() {
        assert_eq!(U016I016.lower(-1), 0_u16);
        assert_eq!(U016I016.lower(i16::MIN), 0_u16);
        assert_eq!(U016I016.floor(u16::MAX), i16::MAX);
        assert_eq!(U128I016.floor(u128::MAX), i16::MAX);
    }

    // ── §4 Q-format spot checks ────────────────────────────────────

    // Spot checks: hand-computed rounding at exact, off-grid, and
    // saturation-boundary inputs.

    #[test]
    fn spot_q008q004_on_grid() {
        // 1.5 in Q8.8 (bits 384) — exactly representable in Q12.4.
        let q88 = FixedI16::<U8>::from_bits(384);
        assert_eq!(Q008Q004.ceil(q88), FixedI16::<U4>::from_bits(24));
        assert_eq!(Q008Q004.upper(FixedI16::<U4>::from_bits(24)), q88);
    }

    #[test]
    fn spot_q008q004_off_grid_positive() {
        // 1.3984375 (bits 358) — between Q12.4 grid points 22 and 23.
        let off = FixedI16::<U8>::from_bits(358);
        assert_eq!(Q008Q004.ceil(off), FixedI16::<U4>::from_bits(23));
    }

    #[test]
    fn spot_q008q004_off_grid_negative() {
        // -1.3984375 (bits -358). div_euclid + rem_euclid → ceil rounds up.
        let neg = FixedI16::<U8>::from_bits(-358);
        assert_eq!(Q008Q004.ceil(neg), FixedI16::<U4>::from_bits(-22));
    }

    #[test]
    fn spot_q008q004_saturation_boundary() {
        // Fine::MAX (bits 32767) ceils up to Coarse(2048) = value 128.0.
        // (Plan 32) `floor` removed: the FINE_MAX `floor` fixup
        // returning `Coarse::MAX` was the source of the
        // `floor_le_ceil` violation that demoted these to ConnL.
        let fmax = FixedI16::<U8>::from_bits(i16::MAX);
        assert_eq!(Q008Q004.ceil(fmax), FixedI16::<U4>::from_bits(2048));
        assert_eq!(Q008Q004.upper(FixedI16::<U4>::from_bits(2048)), fmax);

        // Fine::MIN ceils to Coarse::MIN (the FINE_MIN ceil fixup is
        // still needed for galois_l, kept in the macro).
        let fmin = FixedI16::<U8>::from_bits(i16::MIN);
        assert_eq!(Q008Q004.ceil(fmin), FixedI16::<U4>::from_bits(i16::MIN));
    }

    #[test]
    fn spot_q016q000_degenerate() {
        // SHIFT = 16, RATIO = 65 536. Every Coarse value with |bits| ≥ 1
        // saturates inner. Only Coarse(0) round-trips.
        assert_eq!(
            Q016Q000.upper(FixedI16::<U0>::from_bits(0)),
            FixedI16::<U16>::from_bits(0),
        );
        assert_eq!(
            Q016Q000.upper(FixedI16::<U0>::from_bits(1)),
            FixedI16::<U16>::from_bits(i16::MAX),
        );
        assert_eq!(
            Q016Q000.upper(FixedI16::<U0>::from_bits(-1)),
            FixedI16::<U16>::from_bits(i16::MIN),
        );
    }

    // Generator macro: nine universally-quantified Galois predicates per
    // Conn, delegating to `crate::prop::conn`. All inputs span the
    // full i16 range — the connection is total and lawful for every
    // value, so no bounded strategies are needed.
    //
    // `floor_le_ceil` is currently NOT asserted because these
    // Conns ship as full triples but `inner` is non-order-reflecting
    // at the saturation plateau, so `floor > ceil` there. This is
    // tracked as known debt — Plan 27 audits the crate for the same
    // pattern and converts offending Conns to one-sided
    // (`Conn::new_l` / `Conn::new_r`) so `floor_le_ceil` holds
    // structurally. Until then, the test is omitted here to avoid
    // failing CI on a pre-existing issue.
    // 15 conns × 9 properties = 135 generated proptests, via the
    // shared `crate::law_battery!` macro (Plan 31 T2).
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
