//! Binary fixed-point ladder over `fixed::FixedI64<Frac>`.
//!
//! Frac level set: `{U0, U8, U16, U32, U48, U64}` → 15 ordered pairs
//! `(Fine, Coarse)` with `Fine > Coarse`. See [`super::i016`] for the
//! design (this module mirrors it with `i64` inner / `i128` widening).

#[allow(unused_imports)]
use super::{LE, ext_int, float_fixed_l, int_int_narrow, int_uint, int_uint_narrow, nz_int_ext};
#[cfg(test)]
#[allow(unused_imports)]
use crate::fixed::{
    i008::I008I064, i016::I016I064, i032::I032I064, i128::I128I064, u008::U008I064, u016::U016I064,
    u032::U032I064, u064::U064I064, u128::U128I064,
};
use ::fixed::FixedI64;
use ::fixed::types::extra::{U0, U8, U16, U32, U48, U64, Unsigned};
use core::num::NonZeroI64;

// - std-int Conns sourced from `i64` -------------------------------

int_int_narrow!(I064I008, i64, i8);
int_int_narrow!(I064I016, i64, i16);
int_int_narrow!(I064I032, i64, i32);
ext_int!(I064I128, i64, i128);

int_uint_narrow!(I064U008, i64, u8);
int_uint_narrow!(I064U016, i64, u16);
int_uint_narrow!(I064U032, i64, u32);
int_uint!(I064U064, i64, u64);
int_uint!(I064U128, i64, u128);

// ── §2 i64 ↔ NonZeroI64 ──────────────────────────────────

nz_int_ext!(I064N064, i64, NonZeroI64);

// ── §3 cross-crate iso: i64 ↔ FixedI64<U0> ─────────────────────────

const fn i064q000_fwd(i: i64) -> FixedI64<U0> {
    FixedI64::<U0>::from_bits(i)
}
const fn i064q000_bk(q: FixedI64<U0>) -> i64 {
    q.to_bits()
}

crate::iso! {
    /// `i64 ↔ FixedI64<U0>` — Q64.0 lossless iso. Degenerate Galois.
    pub I064Q000 : i64 => FixedI64<U0> {
        forward: i064q000_fwd,
        back:    i064q000_bk,
    }
}

// ── Sortable big-endian byte encodings ─────────────────────

const fn i64_to_be08(x: i64) -> [u8; 8] {
    ((x as u64) ^ 0x8000_0000_0000_0000).to_be_bytes()
}
const fn be08_to_i64(b: [u8; 8]) -> i64 {
    (u64::from_be_bytes(b) ^ 0x8000_0000_0000_0000) as i64
}

crate::iso! {
    /// `i64 ↔ [u8; 8]` — sign-flipped big-endian iso.
    pub I064BE08 : i64 => [u8; 8] {
        forward: i64_to_be08,
        back:    be08_to_i64,
    }
}

// ── Sortable little-endian byte encodings ──────────────────

const fn i64_to_le08(x: i64) -> LE<8> {
    LE(((x as u64) ^ 0x8000_0000_0000_0000).to_le_bytes())
}
const fn le08_to_i64(b: LE<8>) -> i64 {
    (u64::from_le_bytes(b.0) ^ 0x8000_0000_0000_0000) as i64
}

crate::iso! {
    /// `i64 ↔ LE<8>` — sign-flipped little-endian iso with numeric-sort ordering.
    pub I064LE08 : i64 => LE<8> {
        forward: i64_to_le08,
        back:    le08_to_i64,
    }
}

// ── §4 Q-format ladder over `FixedI64<Frac>` ────────────────────────

/// `I### = FixedI64<U<frac>>` — i64-backed binary fixed-point.
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
        pub const $const_name: $crate::conn::Conn<FixedI64<$FineFrac>, FixedI64<$CoarseFrac>> = {
            const SHIFT: u32 = <$FineFrac as Unsigned>::U32 - <$CoarseFrac as Unsigned>::U32;
            // i128 covers SHIFT ∈ [1, 64]: 1 << 64 = 2^64 fits, and
            // i64::MAX × 2^64 ≈ 2^127 < i128::MAX.
            const RATIO: i128 = 1_i128 << SHIFT;
            const FINE_MIN: i64 = i64::MIN;
            const FINE_MAX: i64 = i64::MAX;

            fn ceil(x: FixedI64<$FineFrac>) -> FixedI64<$CoarseFrac> {
                if x.to_bits() == FINE_MIN {
                    return FixedI64::<$CoarseFrac>::from_bits(i64::MIN);
                }
                let bits = x.to_bits() as i128;
                let q = bits.div_euclid(RATIO);
                let r = bits.rem_euclid(RATIO);
                let res = if r != 0 { q + 1 } else { q };
                FixedI64::from_bits(res as i64)
            }

            fn inner(x: FixedI64<$CoarseFrac>) -> FixedI64<$FineFrac> {
                let res = (x.to_bits() as i128) * RATIO;
                let saturated = if res > FINE_MAX as i128 {
                    FINE_MAX
                } else if res < FINE_MIN as i128 {
                    FINE_MIN
                } else {
                    res as i64
                };
                FixedI64::from_bits(saturated)
            }

            // (Plan 32) ConnL only — `_inner` non-injective at saturation.
            $crate::conn::Conn::new_l(ceil, inner)
        };
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

// ── §5 f32 → FixedI64<U<frac>> narrowing ───────────────────────────
//
// Host bit-width 64 > f32 mantissa 24, every Conn is L-only.

float_fixed_l!(pub F032Q000, f32, FixedI64, U0,  i64);
float_fixed_l!(pub F032Q008, f32, FixedI64, U8,  i64);
float_fixed_l!(pub F032Q016, f32, FixedI64, U16, i64);
float_fixed_l!(pub F032Q032, f32, FixedI64, U32, i64);
float_fixed_l!(pub F032Q048, f32, FixedI64, U48, i64);
float_fixed_l!(pub F032Q064, f32, FixedI64, U64, i64);

// ── §6 f64 → FixedI64<U<frac>> narrowing ───────────────────────────
//
// Host bit-width 64 > f64 mantissa 53, every Conn is L-only.

float_fixed_l!(pub F064Q000, f64, FixedI64, U0,  i64);
float_fixed_l!(pub F064Q008, f64, FixedI64, U8,  i64);
float_fixed_l!(pub F064Q016, f64, FixedI64, U16, i64);
float_fixed_l!(pub F064Q032, f64, FixedI64, U32, i64);
float_fixed_l!(pub F064Q048, f64, FixedI64, U48, i64);
float_fixed_l!(pub F064Q064, f64, FixedI64, U64, i64);

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
        assert_eq!(I128I064.upper(i64::MAX), i128::MAX);
        assert_eq!(I128I064.upper(i64::MIN), i64::MIN as i128);
    }

    #[test]
    fn u_to_i64_neg_and_high() {
        assert_eq!(U064I064.lower(-1), 0_u64);
        assert_eq!(U064I064.floor(u64::MAX), i64::MAX);
        assert_eq!(U128I064.lower(i64::MIN), 0_u128);
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
            Q064Q000.upper(FixedI64::<U0>::from_bits(0)),
            FixedI64::<U64>::from_bits(0),
        );
        assert_eq!(
            Q064Q000.upper(FixedI64::<U0>::from_bits(1)),
            FixedI64::<U64>::from_bits(i64::MAX),
        );
        assert_eq!(
            Q064Q000.upper(FixedI64::<U0>::from_bits(-1)),
            FixedI64::<U64>::from_bits(i64::MIN),
        );
    }

    #[test]
    fn spot_boundary_fixups() {
        // Fine::MIN ceil fixup. (Plan 32: floor removed.)
        let fmin = FixedI64::<U32>::from_bits(i64::MIN);
        assert_eq!(Q032Q016.ceil(fmin), FixedI64::<U16>::from_bits(i64::MIN));
    }

    // ── BE byte-encoding tests ─────────────────────────────

    fn arb_byte8() -> impl Strategy<Value = [u8; 8]> {
        prop_oneof![Just([0; 8]), Just([0xFF; 8]), any::<[u8; 8]>()]
    }

    fn arb_lebyte8() -> impl Strategy<Value = LE<8>> {
        arb_byte8().prop_map(LE)
    }

    proptest! {
        #[test]
        fn i64_be_iso_roundtrip_l(a in prop_oneof![Just(i64::MIN), Just(0i64), Just(i64::MAX), any::<i64>()]) {
            prop_assert!(conn_laws::iso_roundtrip_l(&I064BE08.conn_l(), a));
        }
        #[test]
        fn i64_be_roundtrip_ceil(b in arb_byte8()) {
            prop_assert!(conn_laws::roundtrip_ceil(&I064BE08.conn_l(), b));
        }
        #[test]
        fn i64_be_galois_l(a in any::<i64>(), b in arb_byte8()) {
            prop_assert!(conn_laws::galois_l(&I064BE08.conn_l(), a, b));
        }
        #[test]
        fn i64_be_galois_r(a in any::<i64>(), b in arb_byte8()) {
            prop_assert!(conn_laws::galois_r(&I064BE08.conn_r(), a, b));
        }
        #[test]
        fn i64_be_floor_le_ceil(a in any::<i64>()) {
            prop_assert!(conn_laws::floor_le_ceil(&I064BE08, a));
        }
        #[test]
        fn i64_be_order_preserving(a in any::<i64>(), b in any::<i64>()) {
            prop_assert_eq!(a.cmp(&b), I064BE08.ceil(a).cmp(&I064BE08.ceil(b)));
        }

        #[test]
        fn i064_le_iso_roundtrip_l(a in prop_oneof![Just(i64::MIN), Just(0i64), Just(i64::MAX), any::<i64>()]) {
            prop_assert!(conn_laws::iso_roundtrip_l(&I064LE08.conn_l(), a));
        }

        #[test]
        fn i064_le_roundtrip_ceil(b in arb_lebyte8()) {
            prop_assert!(conn_laws::roundtrip_ceil(&I064LE08.conn_l(), b));
        }

        #[test]
        fn i064_le_galois_l(a in any::<i64>(), b in arb_lebyte8()) {
            prop_assert!(conn_laws::galois_l(&I064LE08.conn_l(), a, b));
        }

        #[test]
        fn i064_le_galois_r(a in any::<i64>(), b in arb_lebyte8()) {
            prop_assert!(conn_laws::galois_r(&I064LE08.conn_r(), a, b));
        }

        #[test]
        fn i064_le_floor_le_ceil(a in any::<i64>()) {
            prop_assert!(conn_laws::floor_le_ceil(&I064LE08, a));
        }

        #[test]
        fn i064_le_order_preserving(a in any::<i64>(), b in any::<i64>()) {
            prop_assert_eq!(a.cmp(&b), I064LE08.ceil(a).cmp(&I064LE08.ceil(b)));
        }
    }

    // 15 conns × 9 properties = 135 generated proptests (64 cases each)
    // — i64 generators are expensive, so cap via `cases: 64`.
    macro_rules! props_for_pair {
        ($mod_name:ident, $conn:ident, $FineFrac:ty, $CoarseFrac:ty) => {
            $crate::law_battery! {
                mod $mod_name,
                conn: $conn,
                fine:   prop_oneof![
                    1 => Just(FixedI64::<$FineFrac>::from_bits(i64::MIN)),
                    1 => Just(FixedI64::<$FineFrac>::from_bits(i64::MAX)),
                    1 => Just(FixedI64::<$FineFrac>::from_bits(0)),
                    8 => any::<i64>().prop_map(FixedI64::<$FineFrac>::from_bits),
                ],
                coarse: prop_oneof![
                    1 => Just(FixedI64::<$CoarseFrac>::from_bits(i64::MIN)),
                    1 => Just(FixedI64::<$CoarseFrac>::from_bits(i64::MAX)),
                    1 => Just(FixedI64::<$CoarseFrac>::from_bits(0)),
                    8 => any::<i64>().prop_map(FixedI64::<$CoarseFrac>::from_bits),
                ],
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

    // ── Boundary spot checks: ceil at the f64-rounded host max ────
    //
    // For `FixedI64<F0>`, `i64::MAX = 2^63 - 1` rounds up to `2^63`
    // in f64. The L-only ceil must route `Extend(2^63_f64)` to
    // `PosInf`, not `Finite(MAX)` — otherwise L-Galois fails at
    // `(Extend(2^63_f64), Finite(MAX))` because
    // `inner(Finite(MAX))` round-down steps to `2^63 - 2^10`,
    // strictly below `2^63`.
    #[test]
    fn f064q000_above_max_to_posinf() {
        let above_max = (i64::MAX as f64) * 2.0_f64.powi(0); // = 2^63
        let v = crate::float::ExtendedFloat::Extend(above_max);
        assert_eq!(F064Q000.ceil(v), crate::extended::Extended::PosInf);
    }

    #[test]
    fn f064q008_above_max_to_posinf() {
        // FixedI64<U8> max = (2^63 - 1) / 2^8 ≈ 2^55, f64 rounds to 2^55.
        let above_max = (i64::MAX as f64) / 256.0_f64; // = 2^55
        let v = crate::float::ExtendedFloat::Extend(above_max);
        assert_eq!(F064Q008.ceil(v), crate::extended::Extended::PosInf);
    }

    // ── §5/§6 f32/f64 → Q-format property tests ────────────────────
    macro_rules! props_for_float_q_l {
        ($mod_name:ident, $conn:ident, $float_ext:ident, $Frac:ty) => {
            $crate::law_battery! {
                mod $mod_name,
                conn: $conn,
                fine: $crate::prop::arb::$float_ext(),
                coarse: prop_oneof![
                    1 => Just(crate::extended::Extended::NegInf),
                    1 => Just(crate::extended::Extended::PosInf),
                    1 => Just(crate::extended::Extended::Finite(FixedI64::<$Frac>::from_bits(0))),
                    1 => Just(crate::extended::Extended::Finite(FixedI64::<$Frac>::from_bits(i64::MIN))),
                    1 => Just(crate::extended::Extended::Finite(FixedI64::<$Frac>::from_bits(i64::MAX))),
                    8 => any::<i64>()
                        .prop_map(|b| crate::extended::Extended::Finite(FixedI64::<$Frac>::from_bits(b))),
                ],
                subset: l_only,
            }
        };
    }

    props_for_float_q_l!(laws_f032q000, F032Q000, extended_float_f32, U0);
    props_for_float_q_l!(laws_f032q008, F032Q008, extended_float_f32, U8);
    props_for_float_q_l!(laws_f032q016, F032Q016, extended_float_f32, U16);
    props_for_float_q_l!(laws_f032q032, F032Q032, extended_float_f32, U32);
    props_for_float_q_l!(laws_f032q048, F032Q048, extended_float_f32, U48);
    props_for_float_q_l!(laws_f032q064, F032Q064, extended_float_f32, U64);

    props_for_float_q_l!(laws_f064q000, F064Q000, extended_float_f64, U0);
    props_for_float_q_l!(laws_f064q008, F064Q008, extended_float_f64, U8);
    props_for_float_q_l!(laws_f064q016, F064Q016, extended_float_f64, U16);
    props_for_float_q_l!(laws_f064q032, F064Q032, extended_float_f64, U32);
    props_for_float_q_l!(laws_f064q048, F064Q048, extended_float_f64, U48);
    props_for_float_q_l!(laws_f064q064, F064Q064, extended_float_f64, U64);
}
