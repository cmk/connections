//! Binary fixed-point ladder over `fixed::FixedI8<Frac>`, plus the
//! cross-crate iso to `i8` and the IEEE-float → `FixedI8<F>` bridges.
//!
//! Frac level set: `{U0, U1, U2, U3, U4, U6, U8}` → 21 ordered pairs
//! `(Fine, Coarse)` with `Fine > Coarse`. See [`super::i016`] for the
//! design (this module mirrors it with `i8` inner / `i16` widening).
//! Same totality + Galois-axiom guarantees; same saturation plateau,
//! and the same boundary fixups in `ceil` / `floor`.
//!
//! Pure-`core` Conns sourced from `i8` (signed widening,
//! two's-complement B2/L2 byte iso, `i8 ↔ NonZeroI8`, …) live next door in
//! [`crate::core::i008`].
//!
//! # Examples
//!
//! `Q3.4 → Q7.0` — every `FixedI8<U4>` value lies in `[-8.0, 7.9375]`.
//! The Conn rounds that value up to the next integer in Q7.0:
//!
//! ```rust
//! use connections::conn::ConnL;  // brings .ceil/.upper in via default methods
//! use connections::fixed::i008::Q004Q000;
//! use fixed::FixedI8;
//! use fixed::types::extra::{U0, U4};
//!
//! // 1.5 in Q3.4 (raw bits 24) ceils up to integer 2 in Q7.0.
//! let q34 = FixedI8::<U4>::from_bits(24);
//! assert_eq!(connections::conn::ceil(&Q004Q000, q34), FixedI8::<U0>::from_bits(2));
//!
//! // `inner` widens 1 in Q7.0 back to its Q3.4 representation
//! // (raw bits 16):
//! assert_eq!(
//!     connections::conn::upper(&Q004Q000, FixedI8::<U0>::from_bits(1)),
//!     FixedI8::<U4>::from_bits(16),
//! );
//! ```
//!
//! These Conns are `ConnL` (left-Galois only) — `inner` saturates the
//! Coarse plateau onto Fine::MAX/MIN, so it isn't order-reflecting and
//! no true adjoint triple exists. See Plan 32 / `doc/design.md`.

use super::float_fixed;
use ::fixed::FixedI8;
use ::fixed::types::extra::{U0, U1, U2, U3, U4, U6, U7, U8, Unsigned};

// ── Cross-crate isos: FixedI8<U*> ↔ i8 ────────────────────────────

const fn q000i008_fwd(q: FixedI8<U0>) -> i8 {
    q.to_bits()
}
const fn q000i008_bk(i: i8) -> FixedI8<U0> {
    FixedI8::<U0>::from_bits(i)
}

const fn q007i008_fwd(q: FixedI8<U7>) -> i8 {
    q.to_bits()
}
const fn q007i008_bk(i: i8) -> FixedI8<U7> {
    FixedI8::<U7>::from_bits(i)
}

crate::iso! {
    /// `FixedI8<U0> ↔ i8` — Q8.0 lossless iso, the canonical bridge
    /// between the Q-format and std-int views of the same 8-bit signed
    /// integer storage. Degenerate Galois (`floor = ceil`).
    pub Q000I008 : FixedI8<U0> => i8 {
        forward: q000i008_fwd,
        back:    q000i008_bk,
    }
}

crate::iso! {
    /// `FixedI8<U7> ↔ i8` — signed normalized Q1.7 lossless bit iso.
    /// Numeric Q values cover `[-1, 1 - 2^-7]`; the primitive carries
    /// the same two's-complement storage bits.
    pub Q007I008 : FixedI8<U7> => i8 {
        forward: q007i008_fwd,
        back:    q007i008_bk,
    }
}

// ── Q-format ladder over `FixedI8<Frac>` ───────────────────────────

/// `I### = FixedI8<U<frac>>` — i8-backed binary fixed-point with
/// `<frac>` fractional bits.
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
        pub const $const_name: $crate::conn::Conn<FixedI8<$FineFrac>, FixedI8<$CoarseFrac>> = {
            const SHIFT: u32 = <$FineFrac as Unsigned>::U32 - <$CoarseFrac as Unsigned>::U32;
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
                FixedI8::<$CoarseFrac>::from_bits(res as i8)
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
                FixedI8::<$FineFrac>::from_bits(saturated)
            }

            // (Plan 32) ConnL only: `_inner` saturates the Coarse plateau
            // onto FINE_MAX/MIN — non-injective, so no true triple
            // exists. The L-Galois adjunction `ceil ⊣ inner` holds; the
            // R-side `inner ⊣ floor` would require an `_inner` that's
            // simultaneously order-reflecting, which can't be satisfied
            // when the Coarse range exceeds Fine range. Shipped as
            // ConnL accordingly.
            $crate::conn::Conn::new_l(ceil, inner)
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

// ── f32 → FixedI8<U<frac>> narrowing ───────────────────────────────
//
// Host bit-width 8 ≤ f32 mantissa 24, so every Conn is a full
// adjoint triple. `Q<frac>` = `FixedI8<U<frac>>` (signed Q-format
// with `<frac>` fractional bits, sign + (8-frac) integer bits).

float_fixed!(pub F032Q000, f32, FixedI8, U0, i8);
float_fixed!(pub F032Q001, f32, FixedI8, U1, i8);
float_fixed!(pub F032Q002, f32, FixedI8, U2, i8);
float_fixed!(pub F032Q003, f32, FixedI8, U3, i8);
float_fixed!(pub F032Q004, f32, FixedI8, U4, i8);
float_fixed!(pub F032Q006, f32, FixedI8, U6, i8);
float_fixed!(pub F032Q008, f32, FixedI8, U8, i8);

// ── f64 → FixedI8<U<frac>> narrowing ───────────────────────────────
//
// Host bit-width 8 ≤ f64 mantissa 53, so every Conn is a full
// adjoint triple.

float_fixed!(pub F064Q000, f64, FixedI8, U0, i8);
float_fixed!(pub F064Q001, f64, FixedI8, U1, i8);
float_fixed!(pub F064Q002, f64, FixedI8, U2, i8);
float_fixed!(pub F064Q003, f64, FixedI8, U3, i8);
float_fixed!(pub F064Q004, f64, FixedI8, U4, i8);
float_fixed!(pub F064Q006, f64, FixedI8, U6, i8);
float_fixed!(pub F064Q008, f64, FixedI8, U8, i8);

// ── f16 → FixedI8<U<frac>> narrowing ───────────────────────────────
//
// Host bit-width 8 ≤ f16 mantissa 11, so every Conn is a full
// adjoint triple. Gated on `feature = "f16"` (nightly).

#[cfg(feature = "f16")]
float_fixed!(pub F016Q000, f16, FixedI8, U0, i8);
#[cfg(feature = "f16")]
float_fixed!(pub F016Q001, f16, FixedI8, U1, i8);
#[cfg(feature = "f16")]
float_fixed!(pub F016Q002, f16, FixedI8, U2, i8);
#[cfg(feature = "f16")]
float_fixed!(pub F016Q003, f16, FixedI8, U3, i8);
#[cfg(feature = "f16")]
float_fixed!(pub F016Q004, f16, FixedI8, U4, i8);
#[cfg(feature = "f16")]
float_fixed!(pub F016Q006, f16, FixedI8, U6, i8);
#[cfg(feature = "f16")]
float_fixed!(pub F016Q008, f16, FixedI8, U8, i8);

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

    // ── Cross-crate iso (Q000I008) spot checks ─────────────────────

    #[test]
    fn q000i008_round_trips_both_ways() {
        for &v in &[i8::MIN, -1, 0, 1, 42, i8::MAX] {
            let q = FixedI8::<U0>::from_bits(v);
            assert_eq!(crate::conn::ceil(&Q000I008, q), v);
            assert_eq!(crate::conn::floor(&Q000I008, q), v);
            assert_eq!(crate::conn::upper(&Q000I008, v), q);
            assert_eq!(crate::conn::lower(&Q000I008, v), q);
            // Iso: ceil ∘ inner = identity, inner ∘ ceil = identity.
            assert_eq!(
                crate::conn::ceil(&Q000I008, crate::conn::upper(&Q000I008, v)),
                v
            );
            assert_eq!(
                crate::conn::upper(&Q000I008, crate::conn::ceil(&Q000I008, q)),
                q
            );
        }
    }

    proptest! {
        // Q000I008 is an iso — both Galois laws must hold.
        #[test]
        fn q000i008_galois_l(a_bits in any::<i8>(), b in any::<i8>()) {
            let a = FixedI8::<U0>::from_bits(a_bits);
            prop_assert!(conn_laws::galois_l(&Q000I008.conn_l(), a, b));
        }

        #[test]
        fn q000i008_galois_r(a_bits in any::<i8>(), b in any::<i8>()) {
            let a = FixedI8::<U0>::from_bits(a_bits);
            prop_assert!(conn_laws::galois_r(&Q000I008.conn_r(), a, b));
        }

        #[test]
        fn q000i008_round_trip_both_directions(v in any::<i8>()) {
            let q = FixedI8::<U0>::from_bits(v);
            prop_assert_eq!(crate::conn::upper(&Q000I008, crate::conn::ceil(&Q000I008, q)), q);
            prop_assert_eq!(crate::conn::ceil(&Q000I008, crate::conn::upper(&Q000I008, v)), v);
            prop_assert_eq!(crate::conn::lower(&Q000I008, crate::conn::floor(&Q000I008, q)), q);
            prop_assert_eq!(crate::conn::floor(&Q000I008, crate::conn::lower(&Q000I008, v)), v);
        }

        #[test]
        fn q007i008_round_trip_both_directions(v in any::<i8>()) {
            let q = FixedI8::<U7>::from_bits(v);
            prop_assert_eq!(crate::conn::upper(&Q007I008, crate::conn::ceil(&Q007I008, q)), q);
            prop_assert_eq!(crate::conn::ceil(&Q007I008, crate::conn::upper(&Q007I008, v)), v);
            prop_assert_eq!(crate::conn::lower(&Q007I008, crate::conn::floor(&Q007I008, q)), q);
            prop_assert_eq!(crate::conn::floor(&Q007I008, crate::conn::lower(&Q007I008, v)), v);
        }
    }

    // ── §4 Q-format spot checks ────────────────────────────────────

    #[test]
    fn spot_q004q000_on_grid() {
        // 1.5 in Q4.4 (bits 24) — Q8.0 ceil rounds up to 2.
        let q44 = FixedI8::<U4>::from_bits(24);
        assert_eq!(
            crate::conn::ceil(&Q004Q000, q44),
            FixedI8::<U0>::from_bits(2)
        );
        assert_eq!(
            crate::conn::upper(&Q004Q000, FixedI8::<U0>::from_bits(1)),
            FixedI8::<U4>::from_bits(16)
        );
    }

    #[test]
    fn spot_q004q000_negative() {
        let q44 = FixedI8::<U4>::from_bits(-24);
        assert_eq!(
            crate::conn::ceil(&Q004Q000, q44),
            FixedI8::<U0>::from_bits(-1)
        );
    }

    #[test]
    fn spot_q008q000_degenerate() {
        // SHIFT = 8, RATIO = 256. Only Coarse(0) round-trips; |bits| ≥ 1
        // saturates inner.
        assert_eq!(
            crate::conn::upper(&Q008Q000, FixedI8::<U0>::from_bits(0)),
            FixedI8::<U8>::from_bits(0),
        );
        assert_eq!(
            crate::conn::upper(&Q008Q000, FixedI8::<U0>::from_bits(1)),
            FixedI8::<U8>::from_bits(i8::MAX),
        );
        assert_eq!(
            crate::conn::upper(&Q008Q000, FixedI8::<U0>::from_bits(-1)),
            FixedI8::<U8>::from_bits(i8::MIN),
        );
    }

    #[test]
    fn spot_boundary_fixups() {
        // Fine::MIN boundary fixup exercised on Q004Q000 (RATIO = 16).
        // (Plan 32: `floor` no longer exists; the Fine::MAX `floor`
        // fixup that previously asserted `Coarse::MAX` was removed
        // along with the broken `floor_le_ceil` it created.)
        let fmin = FixedI8::<U4>::from_bits(i8::MIN);
        assert_eq!(
            crate::conn::ceil(&Q004Q000, fmin),
            FixedI8::<U0>::from_bits(i8::MIN)
        );
    }

    // 21 conns × 5 properties = 105 generated proptests, via the
    // shared `crate::law_battery!` macro. (Plan 32 demoted these
    // Conns from triple to ConnL — `subset: l_only`.)
    macro_rules! props_for_pair {
        ($mod_name:ident, $conn:ident, $FineFrac:ty, $CoarseFrac:ty) => {
            $crate::law_battery! {
                mod $mod_name,
                conn: $conn,
                fine:   prop_oneof![
                    1 => Just(FixedI8::<$FineFrac>::from_bits(i8::MIN)),
                    1 => Just(FixedI8::<$FineFrac>::from_bits(i8::MAX)),
                    1 => Just(FixedI8::<$FineFrac>::from_bits(0)),
                    8 => any::<i8>().prop_map(FixedI8::<$FineFrac>::from_bits),
                ],
                coarse: prop_oneof![
                    1 => Just(FixedI8::<$CoarseFrac>::from_bits(i8::MIN)),
                    1 => Just(FixedI8::<$CoarseFrac>::from_bits(i8::MAX)),
                    1 => Just(FixedI8::<$CoarseFrac>::from_bits(0)),
                    8 => any::<i8>().prop_map(FixedI8::<$CoarseFrac>::from_bits),
                ],
                subset: l_only,
            }
        };
    }

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

    // The f32/f64 → Q-format Galois proptest battery (196 generated
    // tests across 14 Conns) lives in
    // `tests/fixed_i8_float_q_galois.rs`. Hosting it as an
    // integration test keeps the lib-test rustc invocation under
    // CI's container memory budget — same workaround as the
    // unsigned-host Q→Q ladders use.
}
