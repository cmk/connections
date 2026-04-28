//! Binary fixed-point ladder over `fixed::FixedI8<Frac>`.
//!
//! Frac level set: `{U0, U1, U2, U3, U4, U6, U8}` → 21 ordered pairs
//! `(Fine, Coarse)` with `Fine > Coarse`. See [`super::i16`] for the
//! design (this module mirrors it with `i8` inner / `i16` widening).
//! Same totality + Galois-axiom guarantees; same saturation plateau,
//! and the same boundary fixups in `ceil` / `floor`.
//!
//! # Examples
//!
//! `Q3.4 → Q7.0` — every `FixedI8<U4>` value lies in `[-8.0, 7.9375]`.
//! The Conn brackets that value between adjacent integers in Q7.0:
//!
//! ```rust
//! use connections::fixed::i8::Q004Q000;
//! use fixed::FixedI8;
//! use fixed::types::extra::{U0, U4};
//!
//! // 1.5 in Q3.4 (raw bits `0b00011000` = 24) brackets to integers
//! // 1 and 2 in Q7.0:
//! let q34 = FixedI8::<U4>::from_bits(24);
//! assert_eq!(Q004Q000.floor(q34), FixedI8::<U0>::from_bits(1));
//! assert_eq!(Q004Q000.ceil(q34),  FixedI8::<U0>::from_bits(2));
//!
//! // `inner` widens 1 in Q7.0 back to its Q3.4 representation
//! // (raw bits `0b00010000` = 16):
//! assert_eq!(
//!     Q004Q000.inner(FixedI8::<U0>::from_bits(1)),
//!     FixedI8::<U4>::from_bits(16),
//! );
//! ```

use super::{int_int_narrow, nz_int_ext, uint_int_sat};
use crate::conn::Conn;
use crate::extended::Extended;
use core::num::NonZeroI8;
use ::fixed::FixedI8;
use ::fixed::types::extra::{U0, U1, U2, U3, U4, U6, U8, Unsigned};

// ── §1 std-int Conns landing on `i8` ───────────────────────────────
//
// `i8` is the narrowest signed primitive — nothing widens *into* it.
// Just I→I narrowing (`int_int_narrow!`) and U→I non-widening
// (`uint_int_sat!`, right-Galois).

int_int_narrow!(I016I008, i16, i8);
int_int_narrow!(I032I008, i32, i8);
int_int_narrow!(I064I008, i64, i8);
int_int_narrow!(I128I008, i128, i8);

uint_int_sat!(U008I008, u8, i8);
uint_int_sat!(U016I008, u16, i8);
uint_int_sat!(U032I008, u32, i8);
uint_int_sat!(U064I008, u64, i8);
uint_int_sat!(U128I008, u128, i8);

// ── §3 NonZeroI8 ↔ Extended<i8> ────────────────────────────────────

nz_int_ext!(I008N008, i8, NonZeroI8);

// ── §4 cross-crate iso: FixedI8<U0> ↔ i8 ───────────────────────────

/// `FixedI8<U0> ↔ i8` — Q8.0 lossless iso, the canonical bridge
/// between the Q-format and std-int views of the same 8-bit signed
/// integer storage. Degenerate Galois (`floor = ceil`).
pub const Q000I008: Conn<FixedI8<U0>, i8> = {
    fn forward(q: FixedI8<U0>) -> i8 {
        q.to_bits()
    }
    fn back(i: i8) -> FixedI8<U0> {
        FixedI8::<U0>::from_bits(i)
    }
    Conn::new_iso(forward, back)
};

// ── §2 Q-format ladder over `FixedI8<Frac>` ─────────────────────────

/// `I<frac> = FixedI8<U<frac>>` — i8-backed binary fixed-point with
/// `<frac>` fractional bits. Frac digits are zero-padded to 3 chars
/// to fit the X123Y456 conn-name shape.
pub type I000 = FixedI8<U0>;
pub type I001 = FixedI8<U1>;
pub type I002 = FixedI8<U2>;
pub type I003 = FixedI8<U3>;
pub type I004 = FixedI8<U4>;
pub type I006 = FixedI8<U6>;
pub type I008 = FixedI8<U8>;

macro_rules! fix_fix_i8 {
    ($const_name:ident, $FineFrac:ty, $CoarseFrac:ty) => {
#[rustfmt::skip]
        #[doc = concat!(
            "`FixedI8<",
            stringify!($FineFrac),
            "> → FixedI8<",
            stringify!($CoarseFrac),
            ">` frac-level convert (i8-backed)."
        )]
        pub const $const_name: Conn<FixedI8<$FineFrac>, FixedI8<$CoarseFrac>> = {
            const SHIFT: u32 = <$FineFrac as Unsigned>::U32 - <$CoarseFrac as Unsigned>::U32;
            // i16 covers SHIFT ∈ [1, 8]: 1 << 8 = 256 fits, and
            // i8::MAX × 256 = 32 512 < i16::MAX.
            const RATIO: i16 = 1_i16 << SHIFT;
            const FINE_MIN: i8 = i8::MIN;
            const FINE_MAX: i8 = i8::MAX;

            fn ceil(x: FixedI8<$FineFrac>) -> FixedI8<$CoarseFrac> {
                if x.to_bits() == FINE_MIN {
                    return FixedI8::<$CoarseFrac>::from_bits(i8::MIN);
                }
                let bits = x.to_bits() as i16;
                let q = bits.div_euclid(RATIO);
                let r = bits.rem_euclid(RATIO);
                let res = if r != 0 { q + 1 } else { q };
                FixedI8::from_bits(res as i8)
            }

            fn inner(x: FixedI8<$CoarseFrac>) -> FixedI8<$FineFrac> {
                let res = (x.to_bits() as i16) * RATIO;
                let saturated = if res > FINE_MAX as i16 {
                    FINE_MAX
                } else if res < FINE_MIN as i16 {
                    FINE_MIN
                } else {
                    res as i8
                };
                FixedI8::from_bits(saturated)
            }

            fn floor(x: FixedI8<$FineFrac>) -> FixedI8<$CoarseFrac> {
                if x.to_bits() == FINE_MAX {
                    return FixedI8::<$CoarseFrac>::from_bits(i8::MAX);
                }
                let res = (x.to_bits() as i16).div_euclid(RATIO);
                FixedI8::from_bits(res as i8)
            }

            Conn::new(ceil, inner, floor)
        };
    };
}

// 21 ordered pairs from {U0, U1, U2, U3, U4, U6, U8}.
fix_fix_i8!(Q001Q000, U1, U0);
fix_fix_i8!(Q002Q000, U2, U0);
fix_fix_i8!(Q003Q000, U3, U0);
fix_fix_i8!(Q004Q000, U4, U0);
fix_fix_i8!(Q006Q000, U6, U0);
fix_fix_i8!(Q008Q000, U8, U0);
fix_fix_i8!(Q002Q001, U2, U1);
fix_fix_i8!(Q003Q001, U3, U1);
fix_fix_i8!(Q004Q001, U4, U1);
fix_fix_i8!(Q006Q001, U6, U1);
fix_fix_i8!(Q008Q001, U8, U1);
fix_fix_i8!(Q003Q002, U3, U2);
fix_fix_i8!(Q004Q002, U4, U2);
fix_fix_i8!(Q006Q002, U6, U2);
fix_fix_i8!(Q008Q002, U8, U2);
fix_fix_i8!(Q004Q003, U4, U3);
fix_fix_i8!(Q006Q003, U6, U3);
fix_fix_i8!(Q008Q003, U8, U3);
fix_fix_i8!(Q006Q004, U6, U4);
fix_fix_i8!(Q008Q004, U8, U4);
fix_fix_i8!(Q008Q006, U8, U6);

// ────────────────────────────────────────────────────────────────────
// Tests
// ────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::prop::conn as conn_laws;
    use proptest::prelude::*;

    // ── §1 std-int spot checks (merged from former int/i8.rs) ──────

    #[test]
    fn i_to_i_saturate_high() {
        assert_eq!(I016I008.ceil(i16::MAX), i8::MAX);
        assert_eq!(I032I008.ceil(i32::MAX), i8::MAX);
        assert_eq!(I064I008.ceil(i64::MAX), i8::MAX);
        assert_eq!(I128I008.ceil(i128::MAX), i8::MAX);
    }

    #[test]
    fn i_to_i_saturate_low() {
        assert_eq!(I016I008.ceil(i16::MIN), i8::MIN);
        assert_eq!(I032I008.ceil(i32::MIN), i8::MIN);
        assert_eq!(I064I008.ceil(i64::MIN), i8::MIN);
        assert_eq!(I128I008.ceil(i128::MIN), i8::MIN);
    }

    #[test]
    fn i_to_i_round_trip_finite() {
        for &b in &[i8::MIN, -1, 0, 1, i8::MAX] {
            assert_eq!(I016I008.ceil(I016I008.inner(b)), b);
            assert_eq!(I032I008.ceil(I032I008.inner(b)), b);
            assert_eq!(I064I008.ceil(I064I008.inner(b)), b);
            assert_eq!(I128I008.ceil(I128I008.inner(b)), b);
        }
    }

    #[test]
    fn i_to_i_inner_fine_max_fixup() {
        assert_eq!(I016I008.inner(i8::MAX), i16::MAX);
        assert_eq!(I032I008.inner(i8::MAX), i32::MAX);
        assert_eq!(I064I008.inner(i8::MAX), i64::MAX);
        assert_eq!(I128I008.inner(i8::MAX), i128::MAX);
        assert_eq!(I016I008.inner(126), 126_i16);
        assert_eq!(I016I008.inner(i8::MIN), i8::MIN as i16);
    }

    #[test]
    fn u_to_i_neg_collapse() {
        assert_eq!(U008I008.inner(-1), 0_u8);
        assert_eq!(U008I008.inner(i8::MIN), 0_u8);
        assert_eq!(U016I008.inner(-1), 0_u16);
        assert_eq!(U128I008.inner(-50), 0_u128);
    }

    #[test]
    fn u_to_i_high_saturate() {
        assert_eq!(U008I008.floor(u8::MAX), i8::MAX);
        assert_eq!(U016I008.floor(u16::MAX), i8::MAX);
        assert_eq!(U064I008.floor(u64::MAX), i8::MAX);
        assert_eq!(U128I008.floor(u128::MAX), i8::MAX);
    }

    #[test]
    fn u_to_i_round_trip_finite_positive() {
        for &b in &[0_i8, 1, 50, i8::MAX] {
            assert_eq!(U008I008.floor(U008I008.inner(b)), b);
            assert_eq!(U016I008.floor(U016I008.inner(b)), b);
            assert_eq!(U128I008.floor(U128I008.inner(b)), b);
        }
    }

    #[test]
    fn u_to_i_ceil_eq_floor() {
        for &a in &[0_u8, 50, i8::MAX as u8, u8::MAX] {
            assert_eq!(U008I008.ceil(a), U008I008.floor(a));
        }
    }

    // ── §3 Extended<i8> ↔ NonZeroI8 spot checks ────────────────────

    #[test]
    fn i008n008_floor_ceil_split_at_zero() {
        // Asymmetric-adjoint at zero: floor lands on the largest
        // NonZero ≤ 0 (-1); ceil lands on the smallest NonZero ≥ 0 (+1).
        assert_eq!(
            I008N008.floor(Extended::Finite(0)),
            NonZeroI8::new(-1).unwrap()
        );
        assert_eq!(
            I008N008.ceil(Extended::Finite(0)),
            NonZeroI8::new(1).unwrap()
        );
    }

    #[test]
    fn i008n008_finite_nonzero_round_trip() {
        for &v in &[-128, -50, -1, 1, 50, 127] {
            let nz = NonZeroI8::new(v).unwrap();
            assert_eq!(I008N008.ceil(Extended::Finite(v)), nz);
            assert_eq!(I008N008.floor(Extended::Finite(v)), nz);
        }
    }

    #[test]
    fn i008n008_infinities_saturate() {
        // Both adjoints saturate identically at the extremes.
        let min_nz = NonZeroI8::new(i8::MIN).unwrap();
        let max_nz = NonZeroI8::new(i8::MAX).unwrap();
        assert_eq!(I008N008.ceil(Extended::NegInf), min_nz);
        assert_eq!(I008N008.floor(Extended::NegInf), min_nz);
        assert_eq!(I008N008.ceil(Extended::PosInf), max_nz);
        assert_eq!(I008N008.floor(Extended::PosInf), max_nz);
    }

    #[test]
    fn i008n008_inner_is_total_embedding() {
        // inner: NonZero → Extended<i8> is the trivial Finite(.get()).
        for &v in &[-128, -1, 1, 127] {
            let nz = NonZeroI8::new(v).unwrap();
            assert_eq!(I008N008.inner(nz), Extended::Finite(v));
        }
    }

    // ── §4 cross-crate iso (Q000I008) spot checks ──────────────────

    #[test]
    fn q000i008_round_trips_both_ways() {
        for &v in &[i8::MIN, -1, 0, 1, 42, i8::MAX] {
            let q = FixedI8::<U0>::from_bits(v);
            assert_eq!(Q000I008.ceil(q), v);
            assert_eq!(Q000I008.floor(q), v);
            assert_eq!(Q000I008.inner(v), q);
            // Iso: ceil ∘ inner = identity, inner ∘ ceil = identity.
            assert_eq!(Q000I008.ceil(Q000I008.inner(v)), v);
            assert_eq!(Q000I008.inner(Q000I008.ceil(q)), q);
        }
    }

    // ── Property tests covering I008N008 (NonZero) and Q000I008 (iso)

    fn arb_nz_i8() -> impl Strategy<Value = NonZeroI8> {
        any::<i8>().prop_filter_map("non-zero i8", NonZeroI8::new)
    }

    fn arb_extended_i8() -> impl Strategy<Value = Extended<i8>> {
        prop_oneof![
            1 => Just(Extended::NegInf),
            1 => Just(Extended::PosInf),
            8 => any::<i8>().prop_map(Extended::Finite),
        ]
    }

    proptest! {
        // I008N008: source is Extended<i8>, target is NonZeroI8. Both
        // Galois laws hold (the asymmetric floor/ceil at Finite(0)
        // exists precisely so that inner(NonZero(-1)) ≤ Finite(0) ⟺
        // NonZero(-1) ≤ floor(Finite(0)) = NonZero(-1)).
        #[test]
        fn i008n008_galois_l(a in arb_extended_i8(), b in arb_nz_i8()) {
            prop_assert!(conn_laws::conn_galois_l(&I008N008, a, b));
        }

        #[test]
        fn i008n008_galois_r(a in arb_extended_i8(), b in arb_nz_i8()) {
            prop_assert!(conn_laws::conn_galois_r(&I008N008, a, b));
        }

        #[test]
        fn i008n008_inner_then_ceil_recovers_nonzero(nz in arb_nz_i8()) {
            // ceil(inner(nz)) lands back on nz — inner is the trivial
            // embedding into Finite, then ceil on Finite(v != 0) is
            // lossless.
            prop_assert_eq!(I008N008.ceil(I008N008.inner(nz)), nz);
            prop_assert_eq!(I008N008.floor(I008N008.inner(nz)), nz);
        }

        // Q000I008 is an iso — both Galois laws must hold.
        #[test]
        fn q000i008_galois_l(a_bits in any::<i8>(), b in any::<i8>()) {
            let a = FixedI8::<U0>::from_bits(a_bits);
            prop_assert!(conn_laws::conn_galois_l(&Q000I008, a, b));
        }

        #[test]
        fn q000i008_galois_r(a_bits in any::<i8>(), b in any::<i8>()) {
            let a = FixedI8::<U0>::from_bits(a_bits);
            prop_assert!(conn_laws::conn_galois_r(&Q000I008, a, b));
        }

        #[test]
        fn q000i008_round_trip_both_directions(v in any::<i8>()) {
            let q = FixedI8::<U0>::from_bits(v);
            prop_assert_eq!(Q000I008.ceil(Q000I008.inner(v)), v);
            prop_assert_eq!(Q000I008.inner(Q000I008.ceil(q)), q);
        }
    }

    // ── §2 Q-format spot checks ────────────────────────────────────

    #[test]
    fn spot_q004q000_on_grid() {
        // 1.5 in Q4.4 (bits 24) — exactly representable in Q8.0 by 1 or 2.
        let q44 = FixedI8::<U4>::from_bits(24);
        assert_eq!(Q004Q000.floor(q44), FixedI8::<U0>::from_bits(1));
        assert_eq!(Q004Q000.ceil(q44), FixedI8::<U0>::from_bits(2));
        assert_eq!(
            Q004Q000.inner(FixedI8::<U0>::from_bits(1)),
            FixedI8::<U4>::from_bits(16)
        );
    }

    #[test]
    fn spot_q004q000_negative() {
        let q44 = FixedI8::<U4>::from_bits(-24);
        assert_eq!(Q004Q000.floor(q44), FixedI8::<U0>::from_bits(-2));
        assert_eq!(Q004Q000.ceil(q44), FixedI8::<U0>::from_bits(-1));
    }

    #[test]
    fn spot_q008q000_degenerate() {
        // SHIFT = 8, RATIO = 256. Only Coarse(0) round-trips; |bits| ≥ 1
        // saturates inner.
        assert_eq!(
            Q008Q000.inner(FixedI8::<U0>::from_bits(0)),
            FixedI8::<U8>::from_bits(0),
        );
        assert_eq!(
            Q008Q000.inner(FixedI8::<U0>::from_bits(1)),
            FixedI8::<U8>::from_bits(i8::MAX),
        );
        assert_eq!(
            Q008Q000.inner(FixedI8::<U0>::from_bits(-1)),
            FixedI8::<U8>::from_bits(i8::MIN),
        );
    }

    #[test]
    fn spot_boundary_fixups() {
        // Fine::MIN/MAX boundary fixups exercised on Q004Q000 (RATIO = 16).
        let fmin = FixedI8::<U4>::from_bits(i8::MIN);
        let fmax = FixedI8::<U4>::from_bits(i8::MAX);
        assert_eq!(Q004Q000.ceil(fmin), FixedI8::<U0>::from_bits(i8::MIN));
        assert_eq!(Q004Q000.floor(fmax), FixedI8::<U0>::from_bits(i8::MAX));
    }

    // See `super::i16::tests::props_for_pair!` for the design rationale.
    macro_rules! props_for_pair {
        ($mod_name:ident, $conn:ident, $FineFrac:ty, $CoarseFrac:ty) => {
            mod $mod_name {
                use super::*;

                proptest! {
                    #[test]
                    fn galois_l(f in any::<i8>(), b in any::<i8>()) {
                        let fine = FixedI8::<$FineFrac>::from_bits(f);
                        let coarse = FixedI8::<$CoarseFrac>::from_bits(b);
                        prop_assert!(conn_laws::conn_galois_l(&$conn, fine, coarse));
                    }
                    #[test]
                    fn galois_r(f in any::<i8>(), b in any::<i8>()) {
                        let fine = FixedI8::<$FineFrac>::from_bits(f);
                        let coarse = FixedI8::<$CoarseFrac>::from_bits(b);
                        prop_assert!(conn_laws::conn_galois_r(&$conn, fine, coarse));
                    }
                    #[test]
                    fn monotone_l(f1 in any::<i8>(), f2 in any::<i8>()) {
                        let f1 = FixedI8::<$FineFrac>::from_bits(f1);
                        let f2 = FixedI8::<$FineFrac>::from_bits(f2);
                        prop_assert!(conn_laws::conn_monotone_l(&$conn, f1, f2));
                    }
                    #[test]
                    fn monotone_r(b1 in any::<i8>(), b2 in any::<i8>()) {
                        let b1 = FixedI8::<$CoarseFrac>::from_bits(b1);
                        let b2 = FixedI8::<$CoarseFrac>::from_bits(b2);
                        prop_assert!(conn_laws::conn_monotone_r(&$conn, b1, b2));
                    }
                    #[test]
                    fn closure_l(f in any::<i8>()) {
                        let fine = FixedI8::<$FineFrac>::from_bits(f);
                        prop_assert!(conn_laws::conn_closure_l(&$conn, fine));
                    }
                    #[test]
                    fn closure_r(f in any::<i8>()) {
                        let fine = FixedI8::<$FineFrac>::from_bits(f);
                        prop_assert!(conn_laws::conn_closure_r(&$conn, fine));
                    }
                    #[test]
                    fn kernel_l(b in any::<i8>()) {
                        let c = FixedI8::<$CoarseFrac>::from_bits(b);
                        prop_assert!(conn_laws::conn_kernel_l(&$conn, c));
                    }
                    #[test]
                    fn kernel_r(b in any::<i8>()) {
                        let c = FixedI8::<$CoarseFrac>::from_bits(b);
                        prop_assert!(conn_laws::conn_kernel_r(&$conn, c));
                    }
                    #[test]
                    fn idempotent(f in any::<i8>()) {
                        let fine = FixedI8::<$FineFrac>::from_bits(f);
                        prop_assert!(conn_laws::conn_idempotent(&$conn, fine));
                    }
                }
            }
        };
    }

    // 21 conns × 9 properties = 189 generated proptests.
    props_for_pair!(q001q000, Q001Q000, U1, U0);
    props_for_pair!(q002q000, Q002Q000, U2, U0);
    props_for_pair!(q003q000, Q003Q000, U3, U0);
    props_for_pair!(q004q000, Q004Q000, U4, U0);
    props_for_pair!(q006q000, Q006Q000, U6, U0);
    props_for_pair!(q008q000, Q008Q000, U8, U0);
    props_for_pair!(q002q001, Q002Q001, U2, U1);
    props_for_pair!(q003q001, Q003Q001, U3, U1);
    props_for_pair!(q004q001, Q004Q001, U4, U1);
    props_for_pair!(q006q001, Q006Q001, U6, U1);
    props_for_pair!(q008q001, Q008Q001, U8, U1);
    props_for_pair!(q003q002, Q003Q002, U3, U2);
    props_for_pair!(q004q002, Q004Q002, U4, U2);
    props_for_pair!(q006q002, Q006Q002, U6, U2);
    props_for_pair!(q008q002, Q008Q002, U8, U2);
    props_for_pair!(q004q003, Q004Q003, U4, U3);
    props_for_pair!(q006q003, Q006Q003, U6, U3);
    props_for_pair!(q008q003, Q008Q003, U8, U3);
    props_for_pair!(q006q004, Q006Q004, U6, U4);
    props_for_pair!(q008q004, Q008Q004, U8, U4);
    props_for_pair!(q008q006, Q008Q006, U8, U6);
}
