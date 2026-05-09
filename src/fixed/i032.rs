//! Binary fixed-point ladder over `fixed::FixedI32<Frac>`.
//!
//! Frac level set: `{U0, U4, U8, U16, U24, U32}` → 15 ordered pairs
//! `(Fine, Coarse)` with `Fine > Coarse`. See [`super::i016`] for the
//! design (this module mirrors it with `i32` inner / `i64` widening).

use super::{LE, ext_int, int_int_narrow, nz_int_ext, uint_int_sat};
use ::fixed::FixedI32;
use ::fixed::types::extra::{U0, U4, U8, U16, U24, U32, Unsigned};
use core::num::NonZeroI32;

// ── §1 std-int Conns landing on `i32` ───────────────────────────────

ext_int!(I008I032, i8, i32);
ext_int!(I016I032, i16, i32);
ext_int!(U008I032, u8, i32);
ext_int!(U016I032, u16, i32);

int_int_narrow!(I064I032, i64, i32);
int_int_narrow!(I128I032, i128, i32);

uint_int_sat!(
    ///
    /// # Example: `u32` PID → `i32` (libc `pid_t`)
    ///
    /// `std::process::id()` returns a `u32`, but `libc::pid_t = i32`.
    /// A naïve `pid_u32 as i32` cast wraps for any `u32 > i32::MAX` —
    /// silently turning a sentinel value into a negative PID.
    /// [`U032I032.floor`](crate::conn::Conn::floor) saturates to
    /// `i32::MAX` instead, preserving the R-Galois `inner ⊣ floor`
    /// law:
    ///
    /// ```rust
    /// use connections::conn::ConnR;
    /// use connections::fixed::i032::U032I032;
    ///
    /// // Mid-range u32 PIDs that fit in i32 pass through.
    /// assert_eq!(U032I032.floor(1_u32),               1_i32);
    /// assert_eq!(U032I032.floor(i32::MAX as u32),     i32::MAX);
    ///
    /// // Anything above i32::MAX saturates — never wraps to negative.
    /// assert_eq!(U032I032.floor((i32::MAX as u32) + 1), i32::MAX);
    /// assert_eq!(U032I032.floor(u32::MAX),              i32::MAX);
    ///
    /// // Round-trip: i32 → u32 saturates negatives to 0 (the largest
    /// // u32 satisfying inner(b) ≤ a for any a < 0).
    /// assert_eq!(U032I032.lower(-1),       0_u32);
    /// assert_eq!(U032I032.lower(0),        0_u32);
    /// assert_eq!(U032I032.lower(i32::MAX), i32::MAX as u32);
    /// ```
    U032I032, u32, i32
);
uint_int_sat!(U064I032, u64, i32);
uint_int_sat!(U128I032, u128, i32);

// ── §2 i32 ↔ NonZeroI32 ──────────────────────────────────

nz_int_ext!(I032N032, i32, NonZeroI32);

// ── §3 cross-crate iso: FixedI32<U0> ↔ i32 ─────────────────────────

const fn q000i032_fwd(q: FixedI32<U0>) -> i32 {
    q.to_bits()
}
const fn q000i032_bk(i: i32) -> FixedI32<U0> {
    FixedI32::<U0>::from_bits(i)
}

crate::iso! {
    /// `FixedI32<U0> ↔ i32` — Q32.0 lossless iso. Degenerate Galois.
    pub Q000I032 : FixedI32<U0> => i32 {
        forward: q000i032_fwd,
        back:    q000i032_bk,
    }
}

// ── Sortable big-endian byte encodings ─────────────────────

const fn i32_to_be04(x: i32) -> [u8; 4] {
    ((x as u32) ^ 0x8000_0000).to_be_bytes()
}
const fn be04_to_i32(b: [u8; 4]) -> i32 {
    (u32::from_be_bytes(b) ^ 0x8000_0000) as i32
}

crate::iso! {
    /// `i32 ↔ [u8; 4]` — sign-flipped big-endian iso.
    pub I032BE04 : i32 => [u8; 4] {
        forward: i32_to_be04,
        back:    be04_to_i32,
    }
}

// ── Sortable little-endian byte encodings ──────────────────

const fn i32_to_le04(x: i32) -> LE<4> {
    LE(((x as u32) ^ 0x8000_0000).to_le_bytes())
}
const fn le04_to_i32(b: LE<4>) -> i32 {
    (u32::from_le_bytes(b.0) ^ 0x8000_0000) as i32
}

crate::iso! {
    /// `i32 ↔ LE<4>` — sign-flipped little-endian iso with numeric-sort ordering.
    pub I032LE04 : i32 => LE<4> {
        forward: i32_to_le04,
        back:    le04_to_i32,
    }
}

// ── §4 Q-format ladder over `FixedI32<Frac>` ────────────────────────

/// `I### = FixedI32<U<frac>>` — i32-backed binary fixed-point.
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
            // i64 covers SHIFT ∈ [1, 32]: 1 << 32 fits, and
            // i32::MAX × (1 << 32) ≈ 2^63 < i64::MAX.
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

            // (Plan 32) ConnL only — `_inner` non-injective at saturation.
            $crate::conn::Conn::new_l(ceil, inner)
        };
    };
}

// 15 ordered pairs from {U0, U4, U8, U16, U24, U32}.
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

    // ── §1 std-int spot checks (merged from former int/i32.rs) ─────

    #[test]
    fn i008i032_round_trip_at_finite_boundaries() {
        assert_eq!(I008I032.ceil(Extended::Finite(i8::MIN)), -128);
        assert_eq!(I008I032.ceil(Extended::Finite(i8::MAX)), 127);
        assert_eq!(I008I032.upper(-128), Extended::Finite(i8::MIN));
        assert_eq!(I008I032.upper(127), Extended::Finite(i8::MAX));
    }

    #[test]
    fn u016i032_inner_partitions() {
        assert_eq!(U016I032.upper(-1), Extended::NegInf);
        assert_eq!(U016I032.upper(0), Extended::Finite(0));
        assert_eq!(U016I032.upper(65_535), Extended::Finite(u16::MAX));
        assert_eq!(U016I032.upper(65_536), Extended::PosInf);
    }

    #[test]
    fn i_to_i32_saturate() {
        assert_eq!(I064I032.ceil(i64::MAX), i32::MAX);
        assert_eq!(I064I032.ceil(i64::MIN), i32::MIN);
        assert_eq!(I128I032.ceil(i128::MAX), i32::MAX);
        assert_eq!(I128I032.ceil(i128::MIN), i32::MIN);
    }

    #[test]
    fn i_to_i32_inner_fine_max_fixup() {
        assert_eq!(I064I032.upper(i32::MAX), i64::MAX);
        assert_eq!(I128I032.upper(i32::MAX), i128::MAX);
    }

    #[test]
    fn u_to_i32_neg_and_high() {
        assert_eq!(U032I032.lower(-1), 0_u32);
        assert_eq!(U064I032.floor(u64::MAX), i32::MAX);
        assert_eq!(U128I032.lower(i32::MIN), 0_u128);
    }

    // ── §4 Q-format spot checks ────────────────────────────────────

    #[test]
    fn spot_q016q008_on_grid() {
        // 1.5 in Q16.16 (bits = 1.5 × 2^16 = 98304); same value in Q24.8
        // is bits 384. (ConnL: ceil only; floor removed in Plan 32.)
        let q1616 = FixedI32::<U16>::from_bits(98304);
        assert_eq!(Q016Q008.ceil(q1616), FixedI32::<U8>::from_bits(384));
        assert_eq!(Q016Q008.upper(FixedI32::<U8>::from_bits(384)), q1616);
    }

    #[test]
    fn spot_q032q000_degenerate() {
        // SHIFT = 32. Only Coarse(0) round-trips; ±1 saturates inner.
        assert_eq!(
            Q032Q000.upper(FixedI32::<U0>::from_bits(0)),
            FixedI32::<U32>::from_bits(0),
        );
        assert_eq!(
            Q032Q000.upper(FixedI32::<U0>::from_bits(1)),
            FixedI32::<U32>::from_bits(i32::MAX),
        );
        assert_eq!(
            Q032Q000.upper(FixedI32::<U0>::from_bits(-1)),
            FixedI32::<U32>::from_bits(i32::MIN),
        );
    }

    #[test]
    fn spot_boundary_fixups() {
        // Fine::MIN ceil fixup. (Plan 32: Fine::MAX `floor` fixup
        // gone with the ConnL demotion.)
        let fmin = FixedI32::<U16>::from_bits(i32::MIN);
        assert_eq!(Q016Q008.ceil(fmin), FixedI32::<U8>::from_bits(i32::MIN));
    }

    // ── BE byte-encoding tests ─────────────────────────────

    fn arb_byte4() -> impl Strategy<Value = [u8; 4]> {
        prop_oneof![Just([0; 4]), Just([0xFF; 4]), any::<[u8; 4]>()]
    }

    fn arb_lebyte4() -> impl Strategy<Value = LE<4>> {
        arb_byte4().prop_map(LE)
    }

    proptest! {
        #[test]
        fn i32_be_iso_roundtrip_l(a in prop_oneof![Just(i32::MIN), Just(0i32), Just(i32::MAX), any::<i32>()]) {
            prop_assert!(conn_laws::iso_roundtrip_l(&I032BE04.conn_l(), a));
        }
        #[test]
        fn i32_be_roundtrip_ceil(b in arb_byte4()) {
            prop_assert!(conn_laws::roundtrip_ceil(&I032BE04.conn_l(), b));
        }
        #[test]
        fn i32_be_galois_l(a in any::<i32>(), b in arb_byte4()) {
            prop_assert!(conn_laws::galois_l(&I032BE04.conn_l(), a, b));
        }
        #[test]
        fn i32_be_galois_r(a in any::<i32>(), b in arb_byte4()) {
            prop_assert!(conn_laws::galois_r(&I032BE04.conn_r(), a, b));
        }
        #[test]
        fn i32_be_floor_le_ceil(a in any::<i32>()) {
            prop_assert!(conn_laws::floor_le_ceil(&I032BE04, a));
        }
        #[test]
        fn i32_be_order_preserving(a in any::<i32>(), b in any::<i32>()) {
            prop_assert_eq!(a.cmp(&b), I032BE04.ceil(a).cmp(&I032BE04.ceil(b)));
        }

        #[test]
        fn i032_le_iso_roundtrip_l(a in prop_oneof![Just(i32::MIN), Just(0i32), Just(i32::MAX), any::<i32>()]) {
            prop_assert!(conn_laws::iso_roundtrip_l(&I032LE04.conn_l(), a));
        }

        #[test]
        fn i032_le_roundtrip_ceil(b in arb_lebyte4()) {
            prop_assert!(conn_laws::roundtrip_ceil(&I032LE04.conn_l(), b));
        }

        #[test]
        fn i032_le_galois_l(a in any::<i32>(), b in arb_lebyte4()) {
            prop_assert!(conn_laws::galois_l(&I032LE04.conn_l(), a, b));
        }

        #[test]
        fn i032_le_galois_r(a in any::<i32>(), b in arb_lebyte4()) {
            prop_assert!(conn_laws::galois_r(&I032LE04.conn_r(), a, b));
        }

        #[test]
        fn i032_le_floor_le_ceil(a in any::<i32>()) {
            prop_assert!(conn_laws::floor_le_ceil(&I032LE04, a));
        }

        #[test]
        fn i032_le_order_preserving(a in any::<i32>(), b in any::<i32>()) {
            prop_assert_eq!(a.cmp(&b), I032LE04.ceil(a).cmp(&I032LE04.ceil(b)));
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
