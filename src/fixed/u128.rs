//! Binary fixed-point ladder over `fixed::FixedU128<Frac>`.
//!
//! Frac level set: `{F0, F16, F32, F64, F96, F127, F128}` → 21 ordered
//! pairs. Mirrors [`super::i128`] with `FixedU128` backing and adds
//! `F127` (Q1.127), the canonical 128-bit normalised-amplitude format.
//!
//! Stable Rust has no native `u256` to widen through, so the u64-style
//! `(x.to_bits() as u128) * RATIO` pattern doesn't compose. Instead we
//! use [`u128::checked_mul`] + saturate, and [`u128::checked_shl`] to
//! detect the `SHIFT == 128` degenerate case (`Q128Q000`, where
//! `RATIO = 2^128` doesn't fit in `u128` at all).

#[allow(unused_imports)]
use super::{LE, float_fixed_l, nz_uint_ext, uint_int_sat, uint_uint_narrow};
#[cfg(test)]
#[allow(unused_imports)]
use crate::fixed::{
    i008::I008U128, i016::I016U128, i032::I032U128, i064::I064U128, i128::I128U128, u008::U008U128,
    u016::U016U128, u032::U032U128, u064::U064U128,
};
use ::fixed::FixedU128;
use ::fixed::types::extra::{
    U0 as F0, U16 as F16, U32 as F32, U64 as F64, U96 as F96, U127 as F127, U128 as F128, Unsigned,
};
use core::num::NonZeroU128;

// - std-int Conns sourced from `u128` ------------------------------

uint_int_sat!(U128I008, u128, i8);
uint_int_sat!(U128I016, u128, i16);
uint_int_sat!(U128I032, u128, i32);
uint_int_sat!(U128I064, u128, i64);
uint_int_sat!(U128I128, u128, i128);

uint_uint_narrow!(U128U008, u128, u8);
uint_uint_narrow!(U128U016, u128, u16);
uint_uint_narrow!(U128U032, u128, u32);
uint_uint_narrow!(U128U064, u128, u64);

// ── §2 u128 ↔ NonZeroU128 ────────────────────────────────

nz_uint_ext!(U128N128, u128, NonZeroU128);

// ── §3 cross-crate iso: u128 ↔ FixedU128<F0> ───────────────────────

const fn u128q000_fwd(i: u128) -> FixedU128<F0> {
    FixedU128::<F0>::from_bits(i)
}
const fn u128q000_bk(q: FixedU128<F0>) -> u128 {
    q.to_bits()
}

crate::iso! {
    /// `u128 ↔ FixedU128<F0>` — Q128.0 unsigned lossless iso. Degenerate Galois.
    pub U128Q000 : u128 => FixedU128<F0> {
        forward: u128q000_fwd,
        back:    u128q000_bk,
    }
}

// ── Sortable big-endian byte encodings ─────────────────────

const fn u128_to_be16(x: u128) -> [u8; 16] {
    x.to_be_bytes()
}
const fn be16_to_u128(b: [u8; 16]) -> u128 {
    u128::from_be_bytes(b)
}

crate::iso! {
    /// `u128 ↔ [u8; 16]` — big-endian iso. Byte-lex order matches u128 order.
    pub U128BE16 : u128 => [u8; 16] {
        forward: u128_to_be16,
        back:    be16_to_u128,
    }
}

// ── Sortable little-endian byte encodings ──────────────────

const fn u128_to_le16(x: u128) -> LE<16> {
    LE(x.to_le_bytes())
}
const fn le16_to_u128(b: LE<16>) -> u128 {
    u128::from_le_bytes(b.0)
}

crate::iso! {
    /// `u128 ↔ LE<16>` — little-endian iso with numeric-sort ordering.
    pub U128LE16 : u128 => LE<16> {
        forward: u128_to_le16,
        back:    le16_to_u128,
    }
}

// ── §4 Q-format ladder over `FixedU128<Frac>` ───────────────────────

/// `U### = FixedU128<U<frac>>` — u128-backed binary fixed-point.
pub type U000 = FixedU128<F0>;
pub type U016 = FixedU128<F16>;
pub type U032 = FixedU128<F32>;
pub type U064 = FixedU128<F64>;
pub type U096 = FixedU128<F96>;
pub type U127 = FixedU128<F127>;
pub type U128 = FixedU128<F128>;

macro_rules! fix_fix_u128 {
    ($const_name:ident, $FineFrac:ty, $CoarseFrac:ty) => {
#[rustfmt::skip]
        #[doc = concat!(
            "`FixedU128<",
            stringify!($FineFrac),
            "> → FixedU128<",
            stringify!($CoarseFrac),
            ">` frac-level convert (u128-backed)."
        )]
        pub const $const_name: $crate::conn::Conn<FixedU128<$FineFrac>, FixedU128<$CoarseFrac>> = {
            const SHIFT: u32 = <$FineFrac as Unsigned>::U32 - <$CoarseFrac as Unsigned>::U32;
            // For SHIFT < 128, RATIO = 2^SHIFT fits in u128. For
            // SHIFT == 128 the shift is degenerate — `1_u128.checked_shl(128)`
            // returns None, and we route through the `None` arms below
            // for the Q128Q000 endpoint.
            const RATIO: Option<u128> = 1_u128.checked_shl(SHIFT);
            const FINE_MAX: u128 = u128::MAX;

            fn ceil(x: FixedU128<$FineFrac>) -> FixedU128<$CoarseFrac> {
                let bits = x.to_bits();
                match RATIO {
                    Some(r) => {
                        let q = bits / r;
                        // `q + 1` cannot overflow u128: `r ≥ 2` (the
                        // `Some` arm requires SHIFT ∈ [1, 127], so
                        // RATIO ∈ [2, 2^127]), and `bits ≤ u128::MAX`,
                        // so `q ≤ ⌊u128::MAX / 2⌋ = 2^127 − 1`. Hence
                        // `q + 1 ≤ 2^127 < u128::MAX`.
                        let res = if bits % r != 0 { q + 1 } else { q };
                        FixedU128::from_bits(res)
                    }
                    None => {
                        // SHIFT == 128 (Q128Q000). For any bits ∈ u128,
                        // bits < 2^128, so bits / 2^128 < 1.
                        // ceil: bits > 0 → 1; bits == 0 → 0.
                        if bits > 0 {
                            FixedU128::from_bits(1)
                        } else {
                            FixedU128::from_bits(0)
                        }
                    }
                }
            }

            fn inner(x: FixedU128<$CoarseFrac>) -> FixedU128<$FineFrac> {
                let bits = x.to_bits();
                let saturated = match RATIO {
                    Some(r) => match bits.checked_mul(r) {
                        Some(v) => v,
                        None => FINE_MAX,
                    },
                    None => {
                        // SHIFT == 128: bits × 2^128 only fits when bits = 0.
                        if bits == 0 { 0 } else { FINE_MAX }
                    }
                };
                FixedU128::from_bits(saturated)
            }

            // (Plan 32) ConnL only — `_inner` non-injective at saturation.
            $crate::conn::Conn::new_l(ceil, inner)
        };
    };
}

// 21 ordered pairs from {F0, F16, F32, F64, F96, F127, F128}.
fix_fix_u128!(Q016Q000, F16, F0);
fix_fix_u128!(Q032Q000, F32, F0);
fix_fix_u128!(Q064Q000, F64, F0);
fix_fix_u128!(Q096Q000, F96, F0);
fix_fix_u128!(Q127Q000, F127, F0);
fix_fix_u128!(Q128Q000, F128, F0);
fix_fix_u128!(Q032Q016, F32, F16);
fix_fix_u128!(Q064Q016, F64, F16);
fix_fix_u128!(Q096Q016, F96, F16);
fix_fix_u128!(Q127Q016, F127, F16);
fix_fix_u128!(Q128Q016, F128, F16);
fix_fix_u128!(Q064Q032, F64, F32);
fix_fix_u128!(Q096Q032, F96, F32);
fix_fix_u128!(Q127Q032, F127, F32);
fix_fix_u128!(Q128Q032, F128, F32);
fix_fix_u128!(Q096Q064, F96, F64);
fix_fix_u128!(Q127Q064, F127, F64);
fix_fix_u128!(Q128Q064, F128, F64);
fix_fix_u128!(Q127Q096, F127, F96);
fix_fix_u128!(Q128Q096, F128, F96);
fix_fix_u128!(Q128Q127, F128, F127);

// ── §5 f32 → FixedU128<U<frac>> narrowing ──────────────────────────
//
// Host bit-width 128 > f32 mantissa 24, every Conn is L-only.

float_fixed_l!(pub F032Q000, f32, FixedU128, F0,   u128);
float_fixed_l!(pub F032Q016, f32, FixedU128, F16,  u128);
float_fixed_l!(pub F032Q032, f32, FixedU128, F32,  u128);
float_fixed_l!(pub F032Q064, f32, FixedU128, F64,  u128);
float_fixed_l!(pub F032Q096, f32, FixedU128, F96,  u128);
float_fixed_l!(pub F032Q127, f32, FixedU128, F127, u128);
float_fixed_l!(pub F032Q128, f32, FixedU128, F128, u128);

// ── §6 f64 → FixedU128<U<frac>> narrowing ──────────────────────────
//
// Host bit-width 128 > f64 mantissa 53, every Conn is L-only.

float_fixed_l!(pub F064Q000, f64, FixedU128, F0,   u128);
float_fixed_l!(pub F064Q016, f64, FixedU128, F16,  u128);
float_fixed_l!(pub F064Q032, f64, FixedU128, F32,  u128);
float_fixed_l!(pub F064Q064, f64, FixedU128, F64,  u128);
float_fixed_l!(pub F064Q096, f64, FixedU128, F96,  u128);
float_fixed_l!(pub F064Q127, f64, FixedU128, F127, u128);
float_fixed_l!(pub F064Q128, f64, FixedU128, F128, u128);

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

    // ── §1 std-int spot checks (merged from former int/u128.rs) ────

    #[test]
    fn u064u128_inner_saturates_at_source_max() {
        assert_eq!(U064U128.upper(u128::MAX), u64::MAX);
    }

    #[test]
    fn i128u128_at_extremes() {
        assert_eq!(I128U128.ceil(i128::MIN), 0);
        assert_eq!(I128U128.ceil(i128::MAX), i128::MAX as u128);
        assert_eq!(I128U128.upper(u128::MAX), i128::MAX);
    }

    // ── §4 Q-format spot checks ────────────────────────────────────

    /// Regression for the SHIFT=128 endpoint: RATIO doesn't fit u128;
    /// only Coarse(0) round-trips.
    #[test]
    fn degenerate_max_shift() {
        // inner: only 0 stays in range; everything else saturates to MAX.
        assert_eq!(
            Q128Q000.upper(FixedU128::<F0>::from_bits(0)),
            FixedU128::<F128>::from_bits(0),
        );
        assert_eq!(
            Q128Q000.upper(FixedU128::<F0>::from_bits(1)),
            FixedU128::<F128>::from_bits(u128::MAX),
        );
        assert_eq!(
            Q128Q000.upper(FixedU128::<F0>::from_bits(u128::MAX)),
            FixedU128::<F128>::from_bits(u128::MAX),
        );
        // ceil: positive inputs round up to 1; zero → 0.
        assert_eq!(
            Q128Q000.ceil(FixedU128::<F128>::from_bits(0)),
            FixedU128::<F0>::from_bits(0),
        );
        assert_eq!(
            Q128Q000.ceil(FixedU128::<F128>::from_bits(1)),
            FixedU128::<F0>::from_bits(1),
        );
        // (Plan 32: floor truth-table rows removed.)
    }

    /// Q1.127 (the canonical 128-bit normalised amplitude) → Q0.128:
    /// the value 1<<126 in Q1.127 (= 0.5) embeds via Q128Q127.upper
    /// to 1<<127 in Q0.128 (= 0.5).
    #[test]
    fn spot_q127_to_q128() {
        let q127 = FixedU128::<F127>::from_bits(1 << 126);
        let q128 = Q128Q127.upper(q127);
        assert_eq!(q128, FixedU128::<F128>::from_bits(1 << 127));
        assert_eq!(Q128Q127.ceil(q128), q127);
    }

    #[test]
    fn spot_boundary_fixups() {
        // (Plan 32: floor removed.)
        let fmin = FixedU128::<F128>::from_bits(0);
        assert_eq!(Q128Q064.ceil(fmin), FixedU128::<F64>::from_bits(0));
    }

    /// Inner-saturation regression: for non-degenerate pairs where the
    /// SHIFT is large enough that a non-zero coarse bit overflows the
    /// fine u128 range, inner saturates rather than wrapping.
    #[test]
    fn inner_saturates_on_overflow() {
        // Q128Q016: SHIFT=112. Coarse = u128::MAX → product = u128::MAX
        // × 2^112 ≫ u128::MAX, so checked_mul returns None and we
        // saturate to FINE_MAX.
        let big_coarse = FixedU128::<F16>::from_bits(u128::MAX);
        assert_eq!(
            Q128Q016.upper(big_coarse),
            FixedU128::<F128>::from_bits(u128::MAX),
        );
    }

    /// `ceil`'s `q + 1` step in the `Some(r)` branch must not overflow
    /// u128 at the worst-case input `bits = u128::MAX`. The proptest
    /// battery runs only 64 cases per pair (u128 generators are
    /// expensive), so this regression pins the worst case explicitly:
    /// SHIFT=1 (RATIO=2) gives `q = ⌊(2^128-1)/2⌋ = 2^127 - 1`, and
    /// with `r = 1` the branch computes `q + 1 = 2^127`, which fits.
    #[test]
    fn ceil_at_fine_max_no_overflow() {
        // Q128Q127: SHIFT=1, the smallest RATIO and therefore the
        // largest `q` for any given `bits`.
        let fmax = FixedU128::<F128>::from_bits(u128::MAX);
        // bits = 2^128 - 1, RATIO = 2. q = 2^127 - 1, r = 1, q+1 = 2^127.
        assert_eq!(
            Q128Q127.ceil(fmax),
            FixedU128::<F127>::from_bits(1_u128 << 127),
        );
    }

    // ── byte-encoding tests ────────────────────────────────────────

    fn arb_byte16() -> impl Strategy<Value = [u8; 16]> {
        prop_oneof![Just([0; 16]), Just([0xFF; 16]), any::<[u8; 16]>()]
    }

    fn arb_lebyte16() -> impl Strategy<Value = LE<16>> {
        arb_byte16().prop_map(LE)
    }

    proptest! {
        #[test]
        fn u128_be_iso_roundtrip_l(a in prop_oneof![Just(0u128), Just(u128::MAX), any::<u128>()]) {
            prop_assert!(conn_laws::iso_roundtrip_l(&U128BE16.conn_l(), a));
        }
        #[test]
        fn u128_be_roundtrip_ceil(b in arb_byte16()) {
            prop_assert!(conn_laws::roundtrip_ceil(&U128BE16.conn_l(), b));
        }
        #[test]
        fn u128_be_galois_l(a in any::<u128>(), b in arb_byte16()) {
            prop_assert!(conn_laws::galois_l(&U128BE16.conn_l(), a, b));
        }
        #[test]
        fn u128_be_galois_r(a in any::<u128>(), b in arb_byte16()) {
            prop_assert!(conn_laws::galois_r(&U128BE16.conn_r(), a, b));
        }
        #[test]
        fn u128_be_floor_le_ceil(a in any::<u128>()) {
            prop_assert!(conn_laws::floor_le_ceil(&U128BE16, a));
        }
        #[test]
        fn u128_be_order_preserving(a in any::<u128>(), b in any::<u128>()) {
            prop_assert_eq!(a.cmp(&b), U128BE16.ceil(a).cmp(&U128BE16.ceil(b)));
        }

        #[test]
        fn u128_le_iso_roundtrip_l(a in prop_oneof![Just(0u128), Just(u128::MAX), any::<u128>()]) {
            prop_assert!(conn_laws::iso_roundtrip_l(&U128LE16.conn_l(), a));
        }
        #[test]
        fn u128_le_roundtrip_ceil(b in arb_lebyte16()) {
            prop_assert!(conn_laws::roundtrip_ceil(&U128LE16.conn_l(), b));
        }
        #[test]
        fn u128_le_galois_l(a in any::<u128>(), b in arb_lebyte16()) {
            prop_assert!(conn_laws::galois_l(&U128LE16.conn_l(), a, b));
        }
        #[test]
        fn u128_le_galois_r(a in any::<u128>(), b in arb_lebyte16()) {
            prop_assert!(conn_laws::galois_r(&U128LE16.conn_r(), a, b));
        }
        #[test]
        fn u128_le_floor_le_ceil(a in any::<u128>()) {
            prop_assert!(conn_laws::floor_le_ceil(&U128LE16, a));
        }
        #[test]
        fn u128_le_order_preserving(a in any::<u128>(), b in any::<u128>()) {
            prop_assert_eq!(a.cmp(&b), U128LE16.ceil(a).cmp(&U128LE16.ceil(b)));
        }
    }

    // The Galois proptest battery (189 generated tests across 21
    // ordered pairs, capped to 64 cases each — u128 generators are
    // expensive) lives in `tests/fixed_u128_galois.rs`.
    // Hosting it as an integration test keeps the lib-test rustc
    // invocation under CI's container memory budget.

    // ── Boundary spot checks: ceil at the f64-rounded host max ────
    //
    // `u128::MAX = 2^128 - 1` rounds up to `2^128` in f64. L-only
    // ceil must route `Extend(2^128_f64)` to `PosInf`. Q0/Q16/Q32/
    // Q64 frac levels all round up; Q96/Q127/Q128 are below f64
    // mantissa boundary for the scaled max but we test a
    // representative Q0 + Q64 combo here.
    #[test]
    fn f064q000_above_max_to_posinf() {
        let above_max = u128::MAX as f64; // = 2^128
        let v = crate::float::ExtendedFloat::Extend(above_max);
        assert_eq!(F064Q000.ceil(v), crate::extended::Extended::PosInf);
    }

    #[test]
    fn f064q064_above_max_to_posinf() {
        let above_max = (u128::MAX as f64) / 2.0_f64.powi(64); // = 2^64
        let v = crate::float::ExtendedFloat::Extend(above_max);
        assert_eq!(F064Q064.ceil(v), crate::extended::Extended::PosInf);
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
                    1 => Just(crate::extended::Extended::Finite(FixedU128::<$Frac>::from_bits(0))),
                    1 => Just(crate::extended::Extended::Finite(FixedU128::<$Frac>::from_bits(u128::MAX))),
                    8 => any::<u128>()
                        .prop_map(|b| crate::extended::Extended::Finite(FixedU128::<$Frac>::from_bits(b))),
                ],
                subset: l_only,
            }
        };
    }

    props_for_float_q_l!(laws_f032q000, F032Q000, extended_float_f32, F0);
    props_for_float_q_l!(laws_f032q016, F032Q016, extended_float_f32, F16);
    props_for_float_q_l!(laws_f032q032, F032Q032, extended_float_f32, F32);
    props_for_float_q_l!(laws_f032q064, F032Q064, extended_float_f32, F64);
    props_for_float_q_l!(laws_f032q096, F032Q096, extended_float_f32, F96);
    props_for_float_q_l!(laws_f032q127, F032Q127, extended_float_f32, F127);
    props_for_float_q_l!(laws_f032q128, F032Q128, extended_float_f32, F128);

    props_for_float_q_l!(laws_f064q000, F064Q000, extended_float_f64, F0);
    props_for_float_q_l!(laws_f064q016, F064Q016, extended_float_f64, F16);
    props_for_float_q_l!(laws_f064q032, F064Q032, extended_float_f64, F32);
    props_for_float_q_l!(laws_f064q064, F064Q064, extended_float_f64, F64);
    props_for_float_q_l!(laws_f064q096, F064Q096, extended_float_f64, F96);
    props_for_float_q_l!(laws_f064q127, F064Q127, extended_float_f64, F127);
    props_for_float_q_l!(laws_f064q128, F064Q128, extended_float_f64, F128);
}
