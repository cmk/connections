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

#[allow(unused_imports)]
use super::{LE, ext_int, float_fixed, int_int_narrow, int_uint, int_uint_narrow, nz_int_ext};
#[cfg(test)]
#[allow(unused_imports)]
use crate::fixed::{
    i008::I008I016, i032::I032I016, i064::I064I016, i128::I128I016, u008::U008I016, u016::U016I016,
    u032::U032I016, u064::U064I016, u128::U128I016,
};
use ::fixed::FixedI16;
use ::fixed::types::extra::{U0, U2, U4, U8, U12, U16, Unsigned};
use core::num::NonZeroI16;

// - std-int Conns sourced from `i16` -------------------------------

int_int_narrow!(I016I008, i16, i8);
ext_int!(I016I032, i16, i32);
ext_int!(I016I064, i16, i64);
ext_int!(I016I128, i16, i128);

int_uint_narrow!(I016U008, i16, u8);
int_uint!(I016U016, i16, u16);
int_uint!(I016U032, i16, u32);
int_uint!(I016U064, i16, u64);
int_uint!(I016U128, i16, u128);

// ── §2 i16 ↔ NonZeroI16 ──────────────────────────────────

nz_int_ext!(I016N016, i16, NonZeroI16);

// ── §3 cross-crate iso: i16 ↔ FixedI16<U0> ─────────────────────────

const fn i016q000_fwd(i: i16) -> FixedI16<U0> {
    FixedI16::<U0>::from_bits(i)
}
const fn i016q000_bk(q: FixedI16<U0>) -> i16 {
    q.to_bits()
}

crate::iso! {
    /// `i16 ↔ FixedI16<U0>` — Q16.0 lossless iso. Degenerate Galois.
    pub I016Q000 : i16 => FixedI16<U0> {
        forward: i016q000_fwd,
        back:    i016q000_bk,
    }
}

// ── Sortable big-endian byte encodings ─────────────────────

const fn i16_to_be02(x: i16) -> [u8; 2] {
    ((x as u16) ^ 0x8000).to_be_bytes()
}
const fn be02_to_i16(b: [u8; 2]) -> i16 {
    (u16::from_be_bytes(b) ^ 0x8000) as i16
}

crate::iso! {
    /// `i16 ↔ [u8; 2]` — sign-flipped big-endian iso.
    pub I016BE02 : i16 => [u8; 2] {
        forward: i16_to_be02,
        back:    be02_to_i16,
    }
}

// ── Sortable little-endian byte encodings ──────────────────

const fn i16_to_le02(x: i16) -> LE<2> {
    LE(((x as u16) ^ 0x8000).to_le_bytes())
}
const fn le02_to_i16(b: LE<2>) -> i16 {
    (u16::from_le_bytes(b.0) ^ 0x8000) as i16
}

crate::iso! {
    /// `i16 ↔ LE<2>` — sign-flipped little-endian iso with numeric-sort ordering.
    pub I016LE02 : i16 => LE<2> {
        forward: i16_to_le02,
        back:    le02_to_i16,
    }
}

// ── §4 Q-format ladder over `FixedI16<Frac>` ────────────────────────

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
            // i32 covers SHIFT ∈ [1, 16]: 1 << 16 = 65 536 fits, and
            // i16::MAX × (1 << 16) = 2 147 418 112 < i32::MAX, so the
            // multiplication in `inner` cannot overflow i32 before the
            // saturating clamp.
            const RATIO: i32 = 1_i32 << SHIFT;
            const FINE_MIN: i16 = i16::MIN;
            const FINE_MAX: i16 = i16::MAX;

            fn ceil(x: FixedI16<$FineFrac>) -> FixedI16<$CoarseFrac> {
                // Boundary fixup: every Coarse value c ≤ -i16::MAX/RATIO
                // − 1 saturates inner to Fine::MIN. The Galois law
                // requires ceil(Fine::MIN) = Coarse::MIN.
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

            // (Plan 32) ConnL only — `_inner` non-injective at saturation.
            $crate::conn::Conn::new_l(ceil, inner)
        };
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

// ── §5 f32 → FixedI16<U<frac>> narrowing ───────────────────────────
//
// Host bit-width 16 ≤ f32 mantissa 24, so every Conn is a full
// adjoint triple.

float_fixed!(pub F032Q000, f32, FixedI16, U0,  i16);
float_fixed!(pub F032Q002, f32, FixedI16, U2,  i16);
float_fixed!(pub F032Q004, f32, FixedI16, U4,  i16);
float_fixed!(pub F032Q008, f32, FixedI16, U8,  i16);
float_fixed!(pub F032Q012, f32, FixedI16, U12, i16);
float_fixed!(pub F032Q016, f32, FixedI16, U16, i16);

// ── §6 f64 → FixedI16<U<frac>> narrowing ───────────────────────────

float_fixed!(pub F064Q000, f64, FixedI16, U0,  i16);
float_fixed!(pub F064Q002, f64, FixedI16, U2,  i16);
float_fixed!(pub F064Q004, f64, FixedI16, U4,  i16);
float_fixed!(pub F064Q008, f64, FixedI16, U8,  i16);
float_fixed!(pub F064Q012, f64, FixedI16, U12, i16);
float_fixed!(pub F064Q016, f64, FixedI16, U16, i16);

// ────────────────────────────────────────────────────────────────────
// Tests
// ────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    #[allow(unused_imports)]
    use crate::conn::{ConnL, ConnR};
    use crate::extended::Extended;
    use crate::prop::conn as conn_laws;
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
    // ── BE byte-encoding tests ─────────────────────────────

    fn arb_byte2() -> impl Strategy<Value = [u8; 2]> {
        prop_oneof![Just([0; 2]), Just([0xFF; 2]), any::<[u8; 2]>()]
    }

    fn arb_lebyte2() -> impl Strategy<Value = LE<2>> {
        arb_byte2().prop_map(LE)
    }

    proptest! {
        #[test]
        fn i16_be_iso_roundtrip_l(a in prop_oneof![Just(i16::MIN), Just(0i16), Just(i16::MAX), any::<i16>()]) {
            prop_assert!(conn_laws::iso_roundtrip_l(&I016BE02.conn_l(), a));
        }
        #[test]
        fn i16_be_roundtrip_ceil(b in arb_byte2()) {
            prop_assert!(conn_laws::roundtrip_ceil(&I016BE02.conn_l(), b));
        }
        #[test]
        fn i16_be_galois_l(a in any::<i16>(), b in arb_byte2()) {
            prop_assert!(conn_laws::galois_l(&I016BE02.conn_l(), a, b));
        }
        #[test]
        fn i16_be_galois_r(a in any::<i16>(), b in arb_byte2()) {
            prop_assert!(conn_laws::galois_r(&I016BE02.conn_r(), a, b));
        }
        #[test]
        fn i16_be_floor_le_ceil(a in any::<i16>()) {
            prop_assert!(conn_laws::floor_le_ceil(&I016BE02, a));
        }
        #[test]
        fn i16_be_order_preserving(a in any::<i16>(), b in any::<i16>()) {
            prop_assert_eq!(a.cmp(&b), I016BE02.ceil(a).cmp(&I016BE02.ceil(b)));
        }

        #[test]
        fn i016_le_iso_roundtrip_l(a in prop_oneof![Just(i16::MIN), Just(0i16), Just(i16::MAX), any::<i16>()]) {
            prop_assert!(conn_laws::iso_roundtrip_l(&I016LE02.conn_l(), a));
        }

        #[test]
        fn i016_le_roundtrip_ceil(b in arb_lebyte2()) {
            prop_assert!(conn_laws::roundtrip_ceil(&I016LE02.conn_l(), b));
        }

        #[test]
        fn i016_le_galois_l(a in any::<i16>(), b in arb_lebyte2()) {
            prop_assert!(conn_laws::galois_l(&I016LE02.conn_l(), a, b));
        }

        #[test]
        fn i016_le_galois_r(a in any::<i16>(), b in arb_lebyte2()) {
            prop_assert!(conn_laws::galois_r(&I016LE02.conn_r(), a, b));
        }

        #[test]
        fn i016_le_floor_le_ceil(a in any::<i16>()) {
            prop_assert!(conn_laws::floor_le_ceil(&I016LE02, a));
        }

        #[test]
        fn i016_le_order_preserving(a in any::<i16>(), b in any::<i16>()) {
            prop_assert_eq!(a.cmp(&b), I016LE02.ceil(a).cmp(&I016LE02.ceil(b)));
        }
    }

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

    // The f32/f64 → Q-format Galois proptest battery (168 generated
    // tests across 12 Conns) lives in
    // `tests/fixed_i16_float_q_galois.rs`. Same lib-test memory
    // workaround as the Q→Q ladder.
}
