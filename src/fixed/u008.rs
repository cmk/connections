//! Binary fixed-point ladder over `fixed::FixedU8<Frac>`.
//!
//! Frac level set: `{F0, F1, F2, F3, F4, F6, F7, F8}` → 28 ordered pairs
//! `(Fine, Coarse)` with `Fine > Coarse`. Mirrors [`super::i008`] with two
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
//! `F7` (= Q1.7) is the canonical 7-bit MIDI velocity / 7-bit DSP
//! amplitude format, included alongside the mirror-of-signed levels.

#[allow(unused_imports)]
use super::{LE, ext_int, nz_uint_ext, uint_int_sat, uint_uint};
#[cfg(test)]
#[allow(unused_imports)]
use crate::fixed::{
    i008::I008U008, i016::I016U008, i032::I032U008, i064::I064U008, i128::I128U008, u016::U016U008,
    u032::U032U008, u064::U064U008, u128::U128U008,
};
use ::fixed::FixedU8;
use ::fixed::types::extra::{
    U0 as F0, U1 as F1, U2 as F2, U3 as F3, U4 as F4, U6 as F6, U7 as F7, U8 as F8, Unsigned,
};
use core::num::NonZeroU8;

// - std-int Conns sourced from `u8` --------------------------------

ext_int!(U008I016, u8, i16);
ext_int!(U008I032, u8, i32);
ext_int!(U008I064, u8, i64);
ext_int!(U008I128, u8, i128);
uint_int_sat!(U008I008, u8, i8);

uint_uint!(U008U016, u8, u16);
uint_uint!(U008U032, u8, u32);
uint_uint!(U008U064, u8, u64);
uint_uint!(U008U128, u8, u128);

// ── §2 u8 ↔ NonZeroU8 ────────────────────────────────────

nz_uint_ext!(U008N008, u8, NonZeroU8);

// ── §3 cross-crate iso: FixedU8<F0> ↔ u8 ───────────────────────────

const fn q000u008_fwd(q: FixedU8<F0>) -> u8 {
    q.to_bits()
}
const fn q000u008_bk(i: u8) -> FixedU8<F0> {
    FixedU8::<F0>::from_bits(i)
}

crate::iso! {
    /// `FixedU8<F0> ↔ u8` — Q8.0 unsigned lossless iso. Degenerate Galois.
    pub Q000U008 : FixedU8<F0> => u8 {
        forward: q000u008_fwd,
        back:    q000u008_bk,
    }
}

// ── Sortable big-endian byte encodings ─────────────────────

const fn u8_to_be01(x: u8) -> [u8; 1] {
    [x]
}
const fn be01_to_u8(b: [u8; 1]) -> u8 {
    b[0]
}

crate::iso! {
    /// `u8 ↔ [u8; 1]` — trivial big-endian iso.
    ///
    /// Both directions are bit-exact; byte-lex order is u8 numeric
    /// order at one byte width.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::conn::{ConnL, ConnR};
    /// use connections::fixed::u008::U008BE01;
    ///
    /// assert_eq!(U008BE01.ceil(0x42_u8), [0x42]);
    /// assert_eq!(U008BE01.upper([0x42]), 0x42_u8);
    /// ```
    pub U008BE01 : u8 => [u8; 1] {
        forward: u8_to_be01,
        back:    be01_to_u8,
    }
}

const fn bool_to_be01(x: bool) -> [u8; 1] {
    [x as u8]
}

/// Lossy back: any non-zero byte is `true`, only `[0]` is `false`.
/// This makes `BOOLBE01` a one-sided `conn_l!` (not an iso) — the
/// `roundtrip_ceil` law fails for bytes `0x02..=0xFF` (they all
/// collapse to `true → [1]`). Galois L still holds: `ceil(true) = [1]`
/// and `inner` returns `true` exactly for `b ≥ [1]`, so the threshold
/// `b ≥ ceil(a)` matches `inner(b) ≥ a` for both `a` values.
const fn be01_to_bool(b: [u8; 1]) -> bool {
    b[0] != 0
}

crate::conn_l! {
    /// `bool → [u8; 1]` — one-sided projection.
    ///
    /// Forward emits `[0]` for `false` and `[1]` for `true`. Back
    /// (`inner`) treats any non-zero byte as `true`, which means
    /// the byte side is non-injective: this Conn is **not** a
    /// full iso. Shipped as a one-sided left-Galois Conn so the
    /// adjoint law `ceil(a) ≤ b ⟺ a ≤ inner(b)` is the only
    /// thing claimed.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::conn::ConnL;
    /// use connections::fixed::u008::BOOLBE01;
    ///
    /// assert_eq!(BOOLBE01.ceil(false), [0]);
    /// assert_eq!(BOOLBE01.ceil(true),  [1]);
    /// assert_eq!(BOOLBE01.upper([0]),   false);
    /// assert_eq!(BOOLBE01.upper([1]),   true);
    /// // Non-canonical encodings collapse to true:
    /// assert_eq!(BOOLBE01.upper([0xFF]), true);
    /// ```
    pub BOOLBE01 : bool => [u8; 1] {
        ceil:  bool_to_be01,
        inner: be01_to_bool,
    }
}

// ── Sortable little-endian byte encodings ──────────────────

const fn u8_to_le01(x: u8) -> LE<1> {
    LE([x])
}
const fn le01_to_u8(b: LE<1>) -> u8 {
    b.0[0]
}

crate::iso! {
    /// `u8 ↔ LE<1>` — trivial little-endian iso with numeric-sort ordering.
    pub U008LE01 : u8 => LE<1> {
        forward: u8_to_le01,
        back:    le01_to_u8,
    }
}

const fn bool_to_le01(x: bool) -> LE<1> {
    LE([x as u8])
}

/// Lossy back: any non-zero byte is `true`, only `LE([0])` is `false`.
/// This mirrors [`BOOLBE01`] under the `LE<1>` wrapper. `BOOLLE01` is
/// one-sided, so the byte-side `roundtrip_ceil` law is intentionally not
/// claimed: non-canonical encodings such as `LE([2])` collapse to
/// `true → LE([1])`. The left-Galois law still holds because `LE<1>`
/// orders the same way as `[u8; 1]`.
const fn le01_to_bool(b: LE<1>) -> bool {
    b.0[0] != 0
}

crate::conn_l! {
    /// `bool → LE<1>` — one-sided little-endian projection.
    ///
    /// Forward emits `LE([0])` for `false` and `LE([1])` for `true`.
    /// Back (`inner`) treats any non-zero byte as `true`, which means
    /// the byte side is non-injective: this Conn is **not** a full iso.
    /// Shipped as a one-sided left-Galois Conn so the adjoint law
    /// `ceil(a) ≤ b ⟺ a ≤ inner(b)` is the only thing claimed.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::conn::ConnL;
    /// use connections::fixed::{LE, u008::BOOLLE01};
    ///
    /// assert_eq!(BOOLLE01.ceil(false), LE([0]));
    /// assert_eq!(BOOLLE01.ceil(true),  LE([1]));
    /// assert_eq!(BOOLLE01.upper(LE([0])), false);
    /// assert_eq!(BOOLLE01.upper(LE([1])), true);
    /// // Non-canonical encodings collapse to true:
    /// assert_eq!(BOOLLE01.upper(LE([0xFF])), true);
    /// ```
    pub BOOLLE01 : bool => LE<1> {
        ceil:  bool_to_le01,
        inner: le01_to_bool,
    }
}

// ── §4 Q-format ladder over `FixedU8<Frac>` ─────────────────────────

/// `U### = FixedU8<U<frac>>` — u8-backed binary fixed-point with
/// `<frac>` fractional bits.
pub type U000 = FixedU8<F0>;
pub type U001 = FixedU8<F1>;
pub type U002 = FixedU8<F2>;
pub type U003 = FixedU8<F3>;
pub type U004 = FixedU8<F4>;
pub type U006 = FixedU8<F6>;
pub type U007 = FixedU8<F7>;
pub type U008 = FixedU8<F8>;

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
        pub const $const_name: $crate::conn::Conn<FixedU8<$FineFrac>, FixedU8<$CoarseFrac>> = {
            const SHIFT: u32 = <$FineFrac as Unsigned>::U32 - <$CoarseFrac as Unsigned>::U32;
            // u16 covers SHIFT ∈ [1, 8]: 1 << 8 = 256 fits, and
            // u8::MAX × 256 = 65 280 < u16::MAX = 65 535.
            const RATIO: u16 = 1_u16 << SHIFT;
            const FINE_MAX: u8 = u8::MAX;

            fn ceil(x: FixedU8<$FineFrac>) -> FixedU8<$CoarseFrac> {
                let bits = x.to_bits() as u16;
                let q = bits / RATIO;
                let r = bits % RATIO;
                // `res ≤ ⌈bits / RATIO⌉ ≤ ⌈u8::MAX / 2⌉ = 128` since
                // RATIO ≥ 2 (Fine has more frac bits than Coarse, so
                // SHIFT ≥ 1). The `as u8` cast is therefore lossless.
                let res = if r != 0 { q + 1 } else { q };
                FixedU8::from_bits(res as u8)
            }

            fn inner(x: FixedU8<$CoarseFrac>) -> FixedU8<$FineFrac> {
                let res = (x.to_bits() as u16) * RATIO;
                let saturated = if res > FINE_MAX as u16 {
                    FINE_MAX
                } else {
                    res as u8
                };
                FixedU8::from_bits(saturated)
            }

            // (Plan 32) ConnL only — `_inner` non-injective at saturation.
            $crate::conn::Conn::new_l(ceil, inner)
        };
    };
}

// 28 ordered pairs from {F0, F1, F2, F3, F4, F6, F7, F8}.
fix_fix_u8!(Q001Q000, F1, F0);
fix_fix_u8!(Q002Q000, F2, F0);
fix_fix_u8!(Q003Q000, F3, F0);
fix_fix_u8!(Q004Q000, F4, F0);
fix_fix_u8!(Q006Q000, F6, F0);
fix_fix_u8!(Q007Q000, F7, F0);
fix_fix_u8!(Q008Q000, F8, F0);
fix_fix_u8!(Q002Q001, F2, F1);
fix_fix_u8!(Q003Q001, F3, F1);
fix_fix_u8!(Q004Q001, F4, F1);
fix_fix_u8!(Q006Q001, F6, F1);
fix_fix_u8!(Q007Q001, F7, F1);
fix_fix_u8!(Q008Q001, F8, F1);
fix_fix_u8!(Q003Q002, F3, F2);
fix_fix_u8!(Q004Q002, F4, F2);
fix_fix_u8!(Q006Q002, F6, F2);
fix_fix_u8!(Q007Q002, F7, F2);
fix_fix_u8!(Q008Q002, F8, F2);
fix_fix_u8!(Q004Q003, F4, F3);
fix_fix_u8!(Q006Q003, F6, F3);
fix_fix_u8!(Q007Q003, F7, F3);
fix_fix_u8!(Q008Q003, F8, F3);
fix_fix_u8!(Q006Q004, F6, F4);
fix_fix_u8!(Q007Q004, F7, F4);
fix_fix_u8!(Q008Q004, F8, F4);
fix_fix_u8!(Q007Q006, F7, F6);
fix_fix_u8!(Q008Q006, F8, F6);
fix_fix_u8!(Q008Q007, F8, F7);

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
        assert_eq!(I008U008.upper(u8::MAX), i8::MAX);
        assert_eq!(I008U008.upper(127), 127);
        assert_eq!(I008U008.upper(50), 50);
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
        assert_eq!(U016U008.upper(u8::MAX), u16::MAX);
        assert_eq!(U032U008.upper(u8::MAX), u32::MAX);
        assert_eq!(U064U008.upper(u8::MAX), u64::MAX);
        assert_eq!(U128U008.upper(u8::MAX), u128::MAX);
        assert_eq!(U016U008.upper(0), 0_u16);
        assert_eq!(U016U008.upper(254), 254_u16);
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
        assert_eq!(I016U008.upper(u8::MAX), i16::MAX);
        assert_eq!(I128U008.upper(u8::MAX), i128::MAX);
        assert_eq!(I016U008.upper(0), 0_i16);
        assert_eq!(I016U008.upper(100), 100_i16);
    }

    // ── §2 u8 ↔ NonZeroU8 spot checks ──────────────────────────────

    #[test]
    fn u008n008_zero_saturates_to_one() {
        // Unsigned: there is no NonZero ≤ 0; 0 saturates to NonZero(1)
        // (the smallest representable NonZero in the L-Galois sense).
        let one = NonZeroU8::new(1).unwrap();
        assert_eq!(U008N008.ceil(0_u8), one);
    }

    #[test]
    fn u008n008_nonzero_round_trip() {
        for &v in &[1, 50, u8::MAX] {
            let nz = NonZeroU8::new(v).unwrap();
            assert_eq!(U008N008.ceil(v), nz);
        }
    }

    #[test]
    fn u008n008_inner_is_total_embedding() {
        for &v in &[1, 50, u8::MAX] {
            let nz = NonZeroU8::new(v).unwrap();
            assert_eq!(U008N008.upper(nz), v);
        }
    }

    // ── §3 cross-crate iso (Q000U008) spot checks ──────────────────

    #[test]
    fn q000u008_round_trips_both_ways() {
        for &v in &[0_u8, 1, 42, u8::MAX] {
            let q = FixedU8::<F0>::from_bits(v);
            assert_eq!(Q000U008.ceil(q), v);
            assert_eq!(Q000U008.floor(q), v);
            assert_eq!(Q000U008.upper(v), q);
            assert_eq!(Q000U008.ceil(Q000U008.upper(v)), v);
            assert_eq!(Q000U008.upper(Q000U008.ceil(q)), q);
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
            prop_assert!(conn_laws::galois_l(&U008N008.conn_l(), a, b));
        }

        #[test]
        fn u008n008_inner_then_ceil_recovers_nonzero(nz in arb_nz_u8()) {
            prop_assert_eq!(U008N008.ceil(U008N008.upper(nz)), nz);
        }

        // Q000U008 iso — both Galois laws hold.
        #[test]
        fn q000u008_galois_l(a_bits in any::<u8>(), b in any::<u8>()) {
            let a = FixedU8::<F0>::from_bits(a_bits);
            prop_assert!(conn_laws::galois_l(&Q000U008.conn_l(), a, b));
        }

        #[test]
        fn q000u008_galois_r(a_bits in any::<u8>(), b in any::<u8>()) {
            let a = FixedU8::<F0>::from_bits(a_bits);
            prop_assert!(conn_laws::galois_r(&Q000U008.conn_r(), a, b));
        }

        #[test]
        fn q000u008_round_trip_both_directions(v in any::<u8>()) {
            let q = FixedU8::<F0>::from_bits(v);
            prop_assert_eq!(Q000U008.ceil(Q000U008.upper(v)), v);
            prop_assert_eq!(Q000U008.upper(Q000U008.ceil(q)), q);
        }
    }

    // ── §4 Q-format spot checks ────────────────────────────────────

    /// MIDI velocity 64 — the canonical mid-range velocity, exactly
    /// 0.5 in Q1.7 (`U007`) — embeds via `Q008Q007.upper` to 128
    /// (= 0.5 in Q0.8 / `U008`). `U008` is the Fine side (more
    /// fractional bits) and `U007` is the Coarse side.
    #[test]
    fn spot_midi_velocity_q17_to_q08() {
        let velocity_64 = FixedU8::<F7>::from_bits(64);
        let pixel = Q008Q007.upper(velocity_64);
        assert_eq!(pixel, FixedU8::<F8>::from_bits(128));
        // Round-trip Q0.8 → Q1.7 via ceil. (Plan 32: ConnL only.)
        assert_eq!(Q008Q007.ceil(pixel), velocity_64);
    }

    /// MIDI max velocity 127 (= 127/128 = 0.992... in Q1.7) embeds
    /// via inner to 254 in Q0.8 (= 127/128 of 256).
    #[test]
    fn spot_q17_max_velocity_to_q08() {
        let velocity_max = FixedU8::<F7>::from_bits(127);
        assert_eq!(Q008Q007.upper(velocity_max), FixedU8::<F8>::from_bits(254));
    }

    #[test]
    fn spot_q004q000_on_grid() {
        // 1.5 in Q4.4 (bits 24) — Q8.0 ceil rounds up to 2.
        let q44 = FixedU8::<F4>::from_bits(24);
        assert_eq!(Q004Q000.ceil(q44), FixedU8::<F0>::from_bits(2));
        assert_eq!(
            Q004Q000.upper(FixedU8::<F0>::from_bits(1)),
            FixedU8::<F4>::from_bits(16)
        );
    }

    #[test]
    fn spot_q008q000_degenerate() {
        // SHIFT = 8, RATIO = 256. Only Coarse(0) round-trips; bits ≥ 1
        // saturates inner at u8::MAX.
        assert_eq!(
            Q008Q000.upper(FixedU8::<F0>::from_bits(0)),
            FixedU8::<F8>::from_bits(0),
        );
        assert_eq!(
            Q008Q000.upper(FixedU8::<F0>::from_bits(1)),
            FixedU8::<F8>::from_bits(u8::MAX),
        );
        assert_eq!(
            Q008Q000.upper(FixedU8::<F0>::from_bits(255)),
            FixedU8::<F8>::from_bits(u8::MAX),
        );
    }

    #[test]
    fn spot_boundary_fixups() {
        // (Plan 32: floor removed — the Fine::MAX `floor` fixup that
        // returned `Coarse::MAX` was the source of the
        // `floor_le_ceil` violation that demoted these to ConnL.)
        // No FINE_MIN fixup needed: u8::MIN = 0; ceil(0) = 0 falls out
        // of the natural division (0 / 16 = 0, remainder 0).
        let fmin = FixedU8::<F4>::from_bits(0);
        assert_eq!(Q004Q000.ceil(fmin), FixedU8::<F0>::from_bits(0));
    }

    #[test]
    fn bool_le_upper_is_greatest_preimage_with_ceil_below_byte() {
        for byte in 0..=u8::MAX {
            let b = LE([byte]);
            let upper = BOOLLE01.upper(b);
            let greatest_preimage = BOOLLE01.ceil(true) <= b;

            assert_eq!(upper, byte != 0);
            assert_eq!(upper, greatest_preimage);
            assert!(BOOLLE01.ceil(upper) <= b);

            if !upper {
                assert!(BOOLLE01.ceil(true) > b);
            }
        }
    }

    // ── BE byte-encoding tests ─────────────────────────────

    fn arb_byte1() -> impl Strategy<Value = [u8; 1]> {
        prop_oneof![
            Just([0u8]),
            Just([u8::MAX]),
            Just([0x80u8]),
            any::<[u8; 1]>()
        ]
    }

    fn arb_lebyte1() -> impl Strategy<Value = LE<1>> {
        arb_byte1().prop_map(LE)
    }

    proptest! {
        #[test]
        fn u008_be_iso_roundtrip_l(a in prop_oneof![Just(0u8), Just(u8::MAX), any::<u8>()]) {
            prop_assert!(conn_laws::iso_roundtrip_l(&U008BE01.conn_l(), a));
        }

        #[test]
        fn u008_be_roundtrip_ceil(b in arb_byte1()) {
            prop_assert!(conn_laws::roundtrip_ceil(&U008BE01.conn_l(), b));
        }

        #[test]
        fn u008_be_galois_l(a in any::<u8>(), b in arb_byte1()) {
            prop_assert!(conn_laws::galois_l(&U008BE01.conn_l(), a, b));
        }

        #[test]
        fn u008_be_galois_r(a in any::<u8>(), b in arb_byte1()) {
            prop_assert!(conn_laws::galois_r(&U008BE01.conn_r(), a, b));
        }

        #[test]
        fn u008_be_floor_le_ceil(a in any::<u8>()) {
            prop_assert!(conn_laws::floor_le_ceil(&U008BE01, a));
        }

        #[test]
        fn u008_be_order_preserving(a in any::<u8>(), b in any::<u8>()) {
            prop_assert_eq!(a.cmp(&b), U008BE01.ceil(a).cmp(&U008BE01.ceil(b)));
        }

        #[test]
        fn bool_be_galois_l(a: bool, b in arb_byte1()) {
            prop_assert!(conn_laws::galois_l(&BOOLBE01, a, b));
        }

        #[test]
        fn bool_be_host_roundtrip_l(a: bool) {
            prop_assert!(conn_laws::iso_roundtrip_l(&BOOLBE01, a));
        }

        #[test]
        fn bool_be_order_preserving(a: bool, b: bool) {
            prop_assert_eq!(a.cmp(&b), BOOLBE01.ceil(a).cmp(&BOOLBE01.ceil(b)));
        }

        #[test]
        fn u008_le_iso_roundtrip_l(a in prop_oneof![Just(0u8), Just(u8::MAX), any::<u8>()]) {
            prop_assert!(conn_laws::iso_roundtrip_l(&U008LE01.conn_l(), a));
        }

        #[test]
        fn u008_le_roundtrip_ceil(b in arb_lebyte1()) {
            prop_assert!(conn_laws::roundtrip_ceil(&U008LE01.conn_l(), b));
        }

        #[test]
        fn u008_le_galois_l(a in any::<u8>(), b in arb_lebyte1()) {
            prop_assert!(conn_laws::galois_l(&U008LE01.conn_l(), a, b));
        }

        #[test]
        fn u008_le_galois_r(a in any::<u8>(), b in arb_lebyte1()) {
            prop_assert!(conn_laws::galois_r(&U008LE01.conn_r(), a, b));
        }

        #[test]
        fn u008_le_floor_le_ceil(a in any::<u8>()) {
            prop_assert!(conn_laws::floor_le_ceil(&U008LE01, a));
        }

        #[test]
        fn u008_le_order_preserving(a in any::<u8>(), b in any::<u8>()) {
            prop_assert_eq!(a.cmp(&b), U008LE01.ceil(a).cmp(&U008LE01.ceil(b)));
        }

        #[test]
        fn bool_le_galois_l(a: bool, b in arb_lebyte1()) {
            prop_assert!(conn_laws::galois_l(&BOOLLE01, a, b));
        }

        #[test]
        fn bool_le_host_roundtrip_l(a: bool) {
            prop_assert!(conn_laws::iso_roundtrip_l(&BOOLLE01, a));
        }

        #[test]
        fn bool_le_kernel_l_for_noncanonical_true_bytes(b in arb_lebyte1().prop_filter("noncanonical true byte", |b| b.0[0] > 1)) {
            prop_assert_eq!(BOOLLE01.upper(b), true);
            prop_assert_eq!(BOOLLE01.ceil(BOOLLE01.upper(b)), LE([1]));
            prop_assert!(conn_laws::kernel_l(&BOOLLE01, b));
            prop_assert!(!conn_laws::roundtrip_ceil(&BOOLLE01, b));
        }

        #[test]
        fn bool_le_order_preserving(a: bool, b: bool) {
            prop_assert_eq!(a.cmp(&b), BOOLLE01.ceil(a).cmp(&BOOLLE01.ceil(b)));
        }
    }

    // The Galois proptest battery (252 generated tests across 28
    // ordered pairs) lives in `tests/fixed_u8_galois.rs` —
    // hosting it as an integration test keeps the lib-test rustc
    // invocation under CI's container memory budget.
}
