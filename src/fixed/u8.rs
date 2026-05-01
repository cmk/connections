//! Binary fixed-point ladder over `fixed::FixedU8<Frac>`.
//!
//! Frac level set: `{U0, U1, U2, U3, U4, U6, U7, U8}` → 28 ordered pairs
//! `(Fine, Coarse)` with `Fine > Coarse`. Mirrors [`super::i8`] with two
//! adaptations:
//!
//! - The backing type is `FixedU8<Frac>` (u8) instead of `FixedI8<Frac>`
//!   (i8). Inner widens through u16 (next-larger unsigned).
//! - The signed `if x.to_bits() == FINE_MIN { return Coarse::MIN; }`
//!   guard in `ceil` is unnecessary — unsigned has no negative range.
//!   The `floor(FINE_MAX) = Coarse::MAX` guard remains, for the same
//!   Galois-law reason as in the signed module: `inner` saturates at
//!   `u8::MAX`, so floor at the saturation plateau must return
//!   `Coarse::MAX` to keep the lower adjoint lawful.
//!
//! `U7` (= Q1.7) is the canonical 7-bit MIDI velocity / 7-bit DSP
//! amplitude format, included alongside the mirror-of-signed levels.

use super::{int_uint, int_uint_narrow, nz_uint_ext, uint_uint_narrow};
use ::fixed::FixedU8;
use ::fixed::types::extra::{U0, U1, U2, U3, U4, U6, U7, U8, Unsigned};
use core::num::NonZeroU8;

// ── §1 std-int Conns landing on `u8` ────────────────────────────────
//
// `u8` is the narrowest unsigned primitive — nothing widens *into* it.
// Same-width cross-sign clip (`I008U008`), U→U narrowing
// (`uint_uint_narrow!`), and I→U narrowing (`int_uint_narrow!`).

int_uint!(I008U008, i8, u8);

uint_uint_narrow!(U016U008, u16, u8);
uint_uint_narrow!(U032U008, u32, u8);
uint_uint_narrow!(U064U008, u64, u8);
uint_uint_narrow!(U128U008, u128, u8);

int_uint_narrow!(I016U008, i16, u8);
int_uint_narrow!(I032U008, i32, u8);
int_uint_narrow!(I064U008, i64, u8);
int_uint_narrow!(I128U008, i128, u8);

// ── §2 u8 ↔ NonZeroU8 ────────────────────────────────────

nz_uint_ext!(U008N008, u8, NonZeroU8);

// ── §3 cross-crate iso: FixedU8<U0> ↔ u8 ───────────────────────────

const fn q000u008_fwd(q: FixedU8<U0>) -> u8 {
    q.to_bits()
}
const fn q000u008_bk(i: u8) -> FixedU8<U0> {
    FixedU8::<U0>::from_bits(i)
}

crate::iso! {
    /// `FixedU8<U0> ↔ u8` — Q8.0 unsigned lossless iso. Degenerate Galois.
    pub Q000U008 : FixedU8<U0> => u8 {
        forward: q000u008_fwd,
        back:    q000u008_bk,
    }
}

// ── §4 Q-format ladder over `FixedU8<Frac>` ─────────────────────────

/// `U<frac> = FixedU8<U<frac>>` — u8-backed binary fixed-point with
/// `<frac>` fractional bits. Frac digits are zero-padded to 3 chars
/// to fit the X123Y456 conn-name shape.
pub type U000 = FixedU8<U0>;
pub type U001 = FixedU8<U1>;
pub type U002 = FixedU8<U2>;
pub type U003 = FixedU8<U3>;
pub type U004 = FixedU8<U4>;
pub type U006 = FixedU8<U6>;
pub type U007 = FixedU8<U7>;
pub type U008 = FixedU8<U8>;

macro_rules! fix_fix_u8 {
    ($const_name:ident, $FineFrac:ty, $CoarseFrac:ty) => {
#[rustfmt::skip]
        #[doc = concat!(
            "`FixedU8<",
            stringify!($FineFrac),
            "> → FixedU8<",
            stringify!($CoarseFrac),
            ">` frac-level convert (u8-backed)."
        )]
        pub struct $const_name;

        impl $const_name {
            const SHIFT: u32 = <$FineFrac as Unsigned>::U32 - <$CoarseFrac as Unsigned>::U32;
            // u16 covers SHIFT ∈ [1, 8]: 1 << 8 = 256 fits, and
            // u8::MAX × 256 = 65 280 < u16::MAX = 65 535.
            const RATIO: u16 = 1_u16 << Self::SHIFT;
            const FINE_MAX: u8 = u8::MAX;

            const fn _ceil(x: FixedU8<$FineFrac>) -> FixedU8<$CoarseFrac> {
                let bits = x.to_bits() as u16;
                let q = bits / Self::RATIO;
                let r = bits % Self::RATIO;
                // `res ≤ ⌈bits / Self::RATIO⌉ ≤ ⌈u8::MAX / 2⌉ = 128` since
                // Self::RATIO ≥ 2 (Fine has more frac bits than Coarse, so
                // SHIFT ≥ 1). The `as u8` cast is therefore lossless.
                let res = if r != 0 { q + 1 } else { q };
                FixedU8::from_bits(res as u8)
            }

            const fn _inner(x: FixedU8<$CoarseFrac>) -> FixedU8<$FineFrac> {
                let res = (x.to_bits() as u16) * Self::RATIO;
                let saturated = if res > Self::FINE_MAX as u16 {
                    Self::FINE_MAX
                } else {
                    res as u8
                };
                FixedU8::from_bits(saturated)
            }
        }

        // (Plan 32) ConnL only — `_inner` non-injective at saturation.
        impl $crate::conn::ViewL<FixedU8<$FineFrac>, FixedU8<$CoarseFrac>> for $const_name {
            const L: $crate::conn::ConnL<FixedU8<$FineFrac>, FixedU8<$CoarseFrac>> =
                $crate::conn::Conn::new_l($const_name::_ceil, $const_name::_inner);
        }
    };
}

// 28 ordered pairs from {U0, U1, U2, U3, U4, U6, U7, U8}.
fix_fix_u8!(Q001Q000, U1, U0);
fix_fix_u8!(Q002Q000, U2, U0);
fix_fix_u8!(Q003Q000, U3, U0);
fix_fix_u8!(Q004Q000, U4, U0);
fix_fix_u8!(Q006Q000, U6, U0);
fix_fix_u8!(Q007Q000, U7, U0);
fix_fix_u8!(Q008Q000, U8, U0);
fix_fix_u8!(Q002Q001, U2, U1);
fix_fix_u8!(Q003Q001, U3, U1);
fix_fix_u8!(Q004Q001, U4, U1);
fix_fix_u8!(Q006Q001, U6, U1);
fix_fix_u8!(Q007Q001, U7, U1);
fix_fix_u8!(Q008Q001, U8, U1);
fix_fix_u8!(Q003Q002, U3, U2);
fix_fix_u8!(Q004Q002, U4, U2);
fix_fix_u8!(Q006Q002, U6, U2);
fix_fix_u8!(Q007Q002, U7, U2);
fix_fix_u8!(Q008Q002, U8, U2);
fix_fix_u8!(Q004Q003, U4, U3);
fix_fix_u8!(Q006Q003, U6, U3);
fix_fix_u8!(Q007Q003, U7, U3);
fix_fix_u8!(Q008Q003, U8, U3);
fix_fix_u8!(Q006Q004, U6, U4);
fix_fix_u8!(Q007Q004, U7, U4);
fix_fix_u8!(Q008Q004, U8, U4);
fix_fix_u8!(Q007Q006, U7, U6);
fix_fix_u8!(Q008Q006, U8, U6);
fix_fix_u8!(Q008Q007, U8, U7);

// ────────────────────────────────────────────────────────────────────
// Tests
// ────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    #[allow(unused_imports)]
    use crate::conn::{ViewL, ViewR};
    use crate::prop::conn as conn_laws;
    use proptest::prelude::*;

    // ── §1 std-int spot checks (merged from former int/u8.rs) ──────

    #[test]
    fn i008u008_ceil_clips_negatives_to_zero() {
        assert_eq!(I008U008.ceil(-5), 0);
        assert_eq!(I008U008.ceil(i8::MIN), 0);
    }

    #[test]
    fn i008u008_ceil_passes_non_negative() {
        assert_eq!(I008U008.ceil(0), 0);
        assert_eq!(I008U008.ceil(127), 127);
    }

    #[test]
    fn i008u008_inner_saturates_at_source_max() {
        assert_eq!(I008U008.inner(u8::MAX), i8::MAX);
        assert_eq!(I008U008.inner(127), 127);
        assert_eq!(I008U008.inner(50), 50);
    }

    #[test]
    fn u_to_u8_saturate() {
        assert_eq!(U016U008.ceil(u16::MAX), u8::MAX);
        assert_eq!(U032U008.ceil(u32::MAX), u8::MAX);
        assert_eq!(U064U008.ceil(u64::MAX), u8::MAX);
        assert_eq!(U128U008.ceil(u128::MAX), u8::MAX);
    }

    #[test]
    fn u_to_u8_inner_fine_max_fixup() {
        assert_eq!(U016U008.inner(u8::MAX), u16::MAX);
        assert_eq!(U032U008.inner(u8::MAX), u32::MAX);
        assert_eq!(U064U008.inner(u8::MAX), u64::MAX);
        assert_eq!(U128U008.inner(u8::MAX), u128::MAX);
        assert_eq!(U016U008.inner(0), 0_u16);
        assert_eq!(U016U008.inner(254), 254_u16);
    }

    #[test]
    fn i_to_u8_neg_clip() {
        assert_eq!(I016U008.ceil(-1), 0);
        assert_eq!(I016U008.ceil(i16::MIN), 0);
        assert_eq!(I128U008.ceil(i128::MIN), 0);
    }

    #[test]
    fn i_to_u8_high_saturate() {
        assert_eq!(I016U008.ceil(i16::MAX), u8::MAX);
        assert_eq!(I032U008.ceil(i32::MAX), u8::MAX);
        assert_eq!(I128U008.ceil(i128::MAX), u8::MAX);
    }

    #[test]
    fn i_to_u8_inner_fine_max_fixup() {
        assert_eq!(I016U008.inner(u8::MAX), i16::MAX);
        assert_eq!(I128U008.inner(u8::MAX), i128::MAX);
        assert_eq!(I016U008.inner(0), 0_i16);
        assert_eq!(I016U008.inner(100), 100_i16);
    }

    // ── §2 u8 ↔ NonZeroU8 spot checks ──────────────────────────────

    #[test]
    fn u008n008_zero_saturates_to_one() {
        // Unsigned: there is no NonZero ≤ 0; 0 saturates to NonZero(1).
        // floor = ceil because new_left collapses both adjoints.
        let one = NonZeroU8::new(1).unwrap();
        assert_eq!(U008N008.ceil(0_u8), one);
        assert_eq!(U008N008.ceil(0_u8), one);
    }

    #[test]
    fn u008n008_nonzero_round_trip() {
        for &v in &[1, 50, u8::MAX] {
            let nz = NonZeroU8::new(v).unwrap();
            assert_eq!(U008N008.ceil(v), nz);
            assert_eq!(U008N008.ceil(v), nz);
        }
    }

    #[test]
    fn u008n008_inner_is_total_embedding() {
        for &v in &[1, 50, u8::MAX] {
            let nz = NonZeroU8::new(v).unwrap();
            assert_eq!(U008N008.inner(nz), v);
        }
    }

    // ── §3 cross-crate iso (Q000U008) spot checks ──────────────────

    #[test]
    fn q000u008_round_trips_both_ways() {
        for &v in &[0_u8, 1, 42, u8::MAX] {
            let q = FixedU8::<U0>::from_bits(v);
            assert_eq!(Q000U008.ceil(q), v);
            assert_eq!(Q000U008.floor(q), v);
            assert_eq!(Q000U008.inner(v), q);
            assert_eq!(Q000U008.ceil(Q000U008.inner(v)), v);
            assert_eq!(Q000U008.inner(Q000U008.ceil(q)), q);
        }
    }

    // ── Property tests covering U008N008 (NonZero) and Q000U008 (iso)

    fn arb_nz_u8() -> impl Strategy<Value = NonZeroU8> {
        any::<u8>().prop_filter_map("non-zero u8", NonZeroU8::new)
    }

    proptest! {
        // U008N008: source is u8, target is NonZeroU8. Left-Galois
        // holds. Right-Galois fails at the unsigned bottom plateau:
        // floor(0) = NonZero(1), so `inner(NonZero(1)) ≤ 0 ⟺
        // NonZero(1) ≤ floor(0)` reduces to `false ⟺ true`. Only
        // galois_l is asserted.
        #[test]
        fn u008n008_galois_l(a in any::<u8>(), b in arb_nz_u8()) {
            prop_assert!(conn_laws::galois_l(&U008N008::L, a, b));
        }

        #[test]
        fn u008n008_inner_then_ceil_recovers_nonzero(nz in arb_nz_u8()) {
            prop_assert_eq!(U008N008.ceil(U008N008.inner(nz)), nz);
            prop_assert_eq!(U008N008.ceil(U008N008.inner(nz)), nz);
        }

        // Q000U008 iso — both Galois laws hold.
        #[test]
        fn q000u008_galois_l(a_bits in any::<u8>(), b in any::<u8>()) {
            let a = FixedU8::<U0>::from_bits(a_bits);
            prop_assert!(conn_laws::galois_l(&Q000U008::L, a, b));
        }

        #[test]
        fn q000u008_galois_r(a_bits in any::<u8>(), b in any::<u8>()) {
            let a = FixedU8::<U0>::from_bits(a_bits);
            prop_assert!(conn_laws::galois_r(&Q000U008::R, a, b));
        }

        #[test]
        fn q000u008_round_trip_both_directions(v in any::<u8>()) {
            let q = FixedU8::<U0>::from_bits(v);
            prop_assert_eq!(Q000U008.ceil(Q000U008.inner(v)), v);
            prop_assert_eq!(Q000U008.inner(Q000U008.ceil(q)), q);
        }
    }

    // ── §4 Q-format spot checks ────────────────────────────────────

    /// MIDI velocity 64 — the canonical mid-range velocity, exactly
    /// 0.5 in Q1.7 (`U007`) — embeds via `Q008Q007.inner` to 128
    /// (= 0.5 in Q0.8 / `U008`). `U008` is the Fine side (more
    /// fractional bits) and `U007` is the Coarse side.
    #[test]
    fn spot_midi_velocity_q17_to_q08() {
        let velocity_64 = FixedU8::<U7>::from_bits(64);
        let pixel = Q008Q007.inner(velocity_64);
        assert_eq!(pixel, FixedU8::<U8>::from_bits(128));
        // Round-trip Q0.8 → Q1.7 via ceil. (Plan 32: ConnL only.)
        assert_eq!(Q008Q007.ceil(pixel), velocity_64);
    }

    /// MIDI max velocity 127 (= 127/128 = 0.992... in Q1.7) embeds
    /// via inner to 254 in Q0.8 (= 127/128 of 256).
    #[test]
    fn spot_q17_max_velocity_to_q08() {
        let velocity_max = FixedU8::<U7>::from_bits(127);
        assert_eq!(Q008Q007.inner(velocity_max), FixedU8::<U8>::from_bits(254));
    }

    #[test]
    fn spot_q004q000_on_grid() {
        // 1.5 in Q4.4 (bits 24) — Q8.0 ceil rounds up to 2.
        let q44 = FixedU8::<U4>::from_bits(24);
        assert_eq!(Q004Q000.ceil(q44), FixedU8::<U0>::from_bits(2));
        assert_eq!(
            Q004Q000.inner(FixedU8::<U0>::from_bits(1)),
            FixedU8::<U4>::from_bits(16)
        );
    }

    #[test]
    fn spot_q008q000_degenerate() {
        // SHIFT = 8, RATIO = 256. Only Coarse(0) round-trips; bits ≥ 1
        // saturates inner at u8::MAX.
        assert_eq!(
            Q008Q000.inner(FixedU8::<U0>::from_bits(0)),
            FixedU8::<U8>::from_bits(0),
        );
        assert_eq!(
            Q008Q000.inner(FixedU8::<U0>::from_bits(1)),
            FixedU8::<U8>::from_bits(u8::MAX),
        );
        assert_eq!(
            Q008Q000.inner(FixedU8::<U0>::from_bits(255)),
            FixedU8::<U8>::from_bits(u8::MAX),
        );
    }

    #[test]
    fn spot_boundary_fixups() {
        // (Plan 32: floor removed — the Fine::MAX `floor` fixup that
        // returned `Coarse::MAX` was the source of the
        // `floor_le_ceil` violation that demoted these to ConnL.)
        // No FINE_MIN fixup needed: u8::MIN = 0; ceil(0) = 0 falls out
        // of the natural division (0 / 16 = 0, remainder 0).
        let fmin = FixedU8::<U4>::from_bits(0);
        assert_eq!(Q004Q000.ceil(fmin), FixedU8::<U0>::from_bits(0));
    }

    // The Galois proptest battery (252 generated tests across 28
    // ordered pairs) lives in `tests/conn_fixed_u08_galois.rs` —
    // hosting it as an integration test keeps the lib-test rustc
    // invocation under CI's container memory budget.
}
