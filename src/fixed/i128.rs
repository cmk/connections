//! Conns sourced from `i128` plus the `FixedI128<Frac>` and
//! `NonZeroI128` host surfaces.
//!
//! ## §1 std-int Conns sourced from `i128`
//!
//! Signed and unsigned widenings (`I??I128`, `U??I128`) and the
//! same-width unsigned-to-signed clip (`U128I128`) — see [`super`]
//! for the macro family.
//!
//! ## §2 `i128` ↔ `NonZeroI128`
//!
//! Asymmetric-adjoint at zero: `floor(0) = NonZero(-1)`,
//! `ceil(0) = NonZero(+1)`. Both Galois laws hold.
//!
//! ## §3 Cross-crate iso `FixedI128<U0>` ↔ `i128`
//!
//! Q128.0 lossless bridge between the Q-format and std-int views of
//! the same 128-bit signed integer storage; `I128Q000` uses
//! the [`conn_k!`](crate::conn_k) macro.
//!
//! ## §4 Q-format ladder over `FixedI128<Frac>`
//!
//! Frac level set: `{U0, U16, U32, U64, U96, U128}` → 15 ordered pairs
//! `(Fine, Coarse)` with `Fine > Coarse`. See [`super::i064`] for the
//! design template; this module differs in one substantive way:
//!
//! Stable Rust has no native `i256` to widen through, so the i64-style
//! `(x.to_bits() as i128) * RATIO` pattern doesn't compose. Instead we
//! use [`i128::checked_mul`] + saturate, and [`i128::checked_shl`] to
//! detect the `SHIFT == 128` degenerate case (`Q128Q000`, where
//! `RATIO = 2^128` doesn't fit in `i128` at all).
//!
//! Bit-identical outputs to a hypothetical i256-widening implementation
//! at every input: both saturate at `i128::MIN` / `i128::MAX` whenever
//! the product would overflow; `checked_mul` is the smaller, SMT-cleaner
//! encoding (`Some(x*y) iff fits, else None`). Galois laws hold by the
//! same construction as the smaller modules.

#[allow(unused_imports)]
use super::{LE, float_fixed_l, int_int_narrow, int_uint, int_uint_narrow, nz_int_ext};
#[cfg(test)]
#[allow(unused_imports)]
use crate::fixed::{
    i008::I008I128, i016::I016I128, i032::I032I128, i064::I064I128, u008::U008I128, u016::U016I128,
    u032::U032I128, u064::U064I128, u128::U128I128,
};
use ::fixed::FixedI128;
use ::fixed::types::extra::{U0, U16, U32, U64, U96, U128, Unsigned};
use core::num::NonZeroI128;

// - std-int Conns sourced from `i128` ------------------------------

int_int_narrow!(I128I008, i128, i8);
int_int_narrow!(I128I016, i128, i16);
int_int_narrow!(I128I032, i128, i32);
int_int_narrow!(I128I064, i128, i64);

int_uint_narrow!(I128U008, i128, u8);
int_uint_narrow!(I128U016, i128, u16);
int_uint_narrow!(I128U032, i128, u32);
int_uint_narrow!(I128U064, i128, u64);
int_uint!(I128U128, i128, u128);

// ── §2 i128 ↔ NonZeroI128 ────────────────────────────────

nz_int_ext!(I128N128, i128, NonZeroI128);

// ── §3 cross-crate iso: i128 ↔ FixedI128<U0> ───────────────────────

const fn i128q000_fwd(i: i128) -> FixedI128<U0> {
    FixedI128::<U0>::from_bits(i)
}
const fn i128q000_bk(q: FixedI128<U0>) -> i128 {
    q.to_bits()
}

crate::iso! {
    /// `i128 ↔ FixedI128<U0>` — Q128.0 lossless iso. Degenerate Galois.
    pub I128Q000 : i128 => FixedI128<U0> {
        forward: i128q000_fwd,
        back:    i128q000_bk,
    }
}

// ── Sortable big-endian byte encodings ─────────────────────

const fn i128_to_be16(x: i128) -> [u8; 16] {
    ((x as u128) ^ 0x8000_0000_0000_0000_0000_0000_0000_0000).to_be_bytes()
}
const fn be16_to_i128(b: [u8; 16]) -> i128 {
    (u128::from_be_bytes(b) ^ 0x8000_0000_0000_0000_0000_0000_0000_0000) as i128
}

crate::iso! {
    /// `i128 ↔ [u8; 16]` — sign-flipped big-endian iso.
    pub I128BE16 : i128 => [u8; 16] {
        forward: i128_to_be16,
        back:    be16_to_i128,
    }
}

// ── Sortable little-endian byte encodings ──────────────────

const fn i128_to_le16(x: i128) -> LE<16> {
    LE(((x as u128) ^ 0x8000_0000_0000_0000_0000_0000_0000_0000).to_le_bytes())
}
const fn le16_to_i128(b: LE<16>) -> i128 {
    (u128::from_le_bytes(b.0) ^ 0x8000_0000_0000_0000_0000_0000_0000_0000) as i128
}

crate::iso! {
    /// `i128 ↔ LE<16>` — sign-flipped little-endian iso with numeric-sort ordering.
    pub I128LE16 : i128 => LE<16> {
        forward: i128_to_le16,
        back:    le16_to_i128,
    }
}

// ── §4 Q-format ladder over `FixedI128<Frac>` ──────────────────────

/// `I### = FixedI128<U<frac>>` — i128-backed binary fixed-point.
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
            // For SHIFT < 128, RATIO = 2^SHIFT fits in i128 as a positive
            // value (max 2^126; one below i128::MAX = 2^127 − 1). For
            // SHIFT == 128 the shift is degenerate — `1_i128.checked_shl(128)`
            // returns None, and we route through the `None` arms below
            // for the Q128Q000 endpoint.
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
                        // SHIFT == 128 (Q128Q000). For any bits ∈ i128,
                        // |bits| < 2^127, so |bits / 2^128| < 0.5.
                        // ceil: bits > 0 → 1; bits ≤ 0 → 0 (FINE_MIN
                        // is already short-circuited above).
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
                        // SHIFT == 128: bits × 2^128 only fits when bits = 0.
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

            // (Plan 32) ConnL only — `_inner` non-injective at saturation.
            $crate::conn::Conn::new_l(ceil, inner)
        };
    };
}

// 15 ordered pairs from {U0, U16, U32, U64, U96, U128}.
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

// ── §5 f32 → FixedI128<U<frac>> narrowing ──────────────────────────
//
// Host bit-width 128 > f32 mantissa 24, every Conn is L-only.

float_fixed_l!(pub F032Q000, f32, FixedI128, U0,   i128);
float_fixed_l!(pub F032Q016, f32, FixedI128, U16,  i128);
float_fixed_l!(pub F032Q032, f32, FixedI128, U32,  i128);
float_fixed_l!(pub F032Q064, f32, FixedI128, U64,  i128);
float_fixed_l!(pub F032Q096, f32, FixedI128, U96,  i128);
float_fixed_l!(pub F032Q128, f32, FixedI128, U128, i128);

// ── §6 f64 → FixedI128<U<frac>> narrowing ──────────────────────────
//
// Host bit-width 128 > f64 mantissa 53, every Conn is L-only.

float_fixed_l!(pub F064Q000, f64, FixedI128, U0,   i128);
float_fixed_l!(pub F064Q016, f64, FixedI128, U16,  i128);
float_fixed_l!(pub F064Q032, f64, FixedI128, U32,  i128);
float_fixed_l!(pub F064Q064, f64, FixedI128, U64,  i128);
float_fixed_l!(pub F064Q096, f64, FixedI128, U96,  i128);
float_fixed_l!(pub F064Q128, f64, FixedI128, U128, i128);

// ── §7 f16 → FixedI128<U<frac>> narrowing ──────────────────────────
//
// Host bit-width 128 > f16 mantissa 11, so L-only (`ceil ⊣ inner`).
// Gated on `feature = "f16"` (nightly).

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
    use crate::extended::Extended;
    use crate::prop::conn as conn_laws;
    use proptest::prelude::*;

    // ── §1 std-int spot checks (merged from former int/i128.rs) ────

    // (Plan 32) `floor` arms removed; `ext_int!` is now ConnL.
    #[test]
    fn i064i128_extends_to_one_above() {
        assert_eq!(I064I128.ceil(Extended::PosInf), (i64::MAX as i128) + 1);
        assert_eq!(I064I128.ceil(Extended::NegInf), i128::MIN);
    }

    #[test]
    fn u064i128_extends_to_one_above() {
        assert_eq!(U064I128.ceil(Extended::PosInf), (u64::MAX as i128) + 1);
        assert_eq!(U064I128.ceil(Extended::NegInf), i128::MIN);
    }

    #[test]
    fn u128i128_neg_and_high() {
        assert_eq!(U128I128.lower(-1), 0_u128);
        assert_eq!(U128I128.lower(i128::MIN), 0_u128);
        assert_eq!(U128I128.floor(u128::MAX), i128::MAX);
        assert_eq!(U128I128.floor(U128I128.lower(50)), 50);
        assert_eq!(U128I128.floor(U128I128.lower(i128::MAX)), i128::MAX);
    }

    // ── §4 Q-format spot checks ────────────────────────────────────

    /// Regression for the SHIFT=128 endpoint: RATIO doesn't fit i128;
    /// only Coarse(0) round-trips.
    #[test]
    fn degenerate_max_shift() {
        // inner: only 0 stays in range; everything else saturates.
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
        // ceil: positive inputs round up to 1; non-positive (and non-MIN)
        // round to 0; MIN takes the i128::MIN boundary fixup.
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
        // (Plan 32) `floor` truth-table rows removed: ConnL only.
    }

    #[test]
    fn spot_q128q064_on_grid() {
        // 1.5 in Q64.64 (bits = 1.5 × 2^64) round-trips through Q64.64
        // (no, the Coarse side has Frac=64, so Q64.64). Pick a value
        // where the Fine bits are an exact multiple of 2^(128-64) = 2^64.
        // bits_fine = 3 × 2^63 represents 1.5 in Q0.128. inner(coarse=3<<63)
        // multiplies through 2^64 — overflow, saturate.
        // Instead use a small value: coarse = 1 represents 2^-64.
        // inner(1) = 1 × 2^64 = 2^64, fits.
        let coarse_one = FixedI128::<U64>::from_bits(1);
        let fine_via_inner = Q128Q064.upper(coarse_one);
        assert_eq!(fine_via_inner, FixedI128::<U128>::from_bits(1_i128 << 64));
    }

    #[test]
    fn spot_boundary_fixups() {
        // Fine::MIN ceil fixup. (Plan 32: floor removed.)
        let fmin = FixedI128::<U128>::from_bits(i128::MIN);
        assert_eq!(Q128Q064.ceil(fmin), FixedI128::<U64>::from_bits(i128::MIN));
    }

    /// Inner-saturation regression: for non-degenerate pairs where the
    /// SHIFT is large enough that a non-zero coarse bit overflows the
    /// fine i128 range, inner saturates rather than wrapping.
    #[test]
    fn inner_saturates_on_overflow() {
        // Q128Q016: SHIFT=112. Coarse = i128::MAX → product = i128::MAX
        // × 2^112 ≫ i128::MAX, so checked_mul returns None and we
        // saturate to FINE_MAX.
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

    // ── byte-encoding tests ────────────────────────────────────────

    fn arb_byte16() -> impl Strategy<Value = [u8; 16]> {
        prop_oneof![Just([0; 16]), Just([0xFF; 16]), any::<[u8; 16]>()]
    }

    fn arb_lebyte16() -> impl Strategy<Value = LE<16>> {
        arb_byte16().prop_map(LE)
    }

    proptest! {
        #[test]
        fn i128_be_iso_roundtrip_l(a in prop_oneof![Just(i128::MIN), Just(0i128), Just(i128::MAX), any::<i128>()]) {
            prop_assert!(conn_laws::iso_roundtrip_l(&I128BE16.conn_l(), a));
        }
        #[test]
        fn i128_be_roundtrip_ceil(b in arb_byte16()) {
            prop_assert!(conn_laws::roundtrip_ceil(&I128BE16.conn_l(), b));
        }
        #[test]
        fn i128_be_galois_l(a in any::<i128>(), b in arb_byte16()) {
            prop_assert!(conn_laws::galois_l(&I128BE16.conn_l(), a, b));
        }
        #[test]
        fn i128_be_galois_r(a in any::<i128>(), b in arb_byte16()) {
            prop_assert!(conn_laws::galois_r(&I128BE16.conn_r(), a, b));
        }
        #[test]
        fn i128_be_floor_le_ceil(a in any::<i128>()) {
            prop_assert!(conn_laws::floor_le_ceil(&I128BE16, a));
        }
        #[test]
        fn i128_be_order_preserving(a in any::<i128>(), b in any::<i128>()) {
            prop_assert_eq!(a.cmp(&b), I128BE16.ceil(a).cmp(&I128BE16.ceil(b)));
        }

        #[test]
        fn i128_le_iso_roundtrip_l(a in prop_oneof![Just(i128::MIN), Just(0i128), Just(i128::MAX), any::<i128>()]) {
            prop_assert!(conn_laws::iso_roundtrip_l(&I128LE16.conn_l(), a));
        }
        #[test]
        fn i128_le_roundtrip_ceil(b in arb_lebyte16()) {
            prop_assert!(conn_laws::roundtrip_ceil(&I128LE16.conn_l(), b));
        }
        #[test]
        fn i128_le_galois_l(a in any::<i128>(), b in arb_lebyte16()) {
            prop_assert!(conn_laws::galois_l(&I128LE16.conn_l(), a, b));
        }
        #[test]
        fn i128_le_galois_r(a in any::<i128>(), b in arb_lebyte16()) {
            prop_assert!(conn_laws::galois_r(&I128LE16.conn_r(), a, b));
        }
        #[test]
        fn i128_le_floor_le_ceil(a in any::<i128>()) {
            prop_assert!(conn_laws::floor_le_ceil(&I128LE16, a));
        }
        #[test]
        fn i128_le_order_preserving(a in any::<i128>(), b in any::<i128>()) {
            prop_assert_eq!(a.cmp(&b), I128LE16.ceil(a).cmp(&I128LE16.ceil(b)));
        }
    }

    // 15 conns × 9 properties = 135 generated proptests (64 cases each)
    // — i128 generators are expensive, so cap via `cases: 64`.
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

    // The f32/f64 → Q-format Galois proptest battery (96 generated
    // tests across 12 Conns, all L-only) lives in
    // `tests/fixed_i128_float_q_galois.rs`.
}
