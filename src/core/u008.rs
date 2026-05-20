//! `u8`-source std-int Conns plus the `u8 ↔ NonZeroU8` adjoint and
//! sortable big- / little-endian byte encodings.
//!
//! Q-format / cross-crate isos to `FixedU8<F>` live next door in
//! `crate::fixed::u008`. The bool ↔ byte projections live in
//! [`crate::core::bool`].

#[allow(unused_imports)]
use crate::core::LE;
use crate::core::{ext_int, nz_uint_ext, nz_uint_widen, uint_int_sat, uint_uint};
use ::core::num::{NonZeroU8, NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU128};

// ── §1 std-int Conns sourced from `u8` ────────────────────────────

ext_int!(U008I016, u8, i16);
ext_int!(U008I032, u8, i32);
ext_int!(U008I064, u8, i64);
ext_int!(U008I128, u8, i128);
uint_int_sat!(U008I008, u8, i8);

uint_uint!(U008U016, u8, u16);
uint_uint!(U008U032, u8, u32);
uint_uint!(U008U064, u8, u64);
uint_uint!(U008U128, u8, u128);

// ── §3 u8 ↔ NonZeroU8 ─────────────────────────────────────────────

nz_uint_ext!(U008N008, u8, NonZeroU8);

// ── NonZero unsigned widenings ────────────────────────────────────

nz_uint_widen!(N008N016, NonZeroU8, u8, NonZeroU16, u16);
nz_uint_widen!(N008N032, NonZeroU8, u8, NonZeroU32, u32);
nz_uint_widen!(N008N064, NonZeroU8, u8, NonZeroU64, u64);
nz_uint_widen!(N008N128, NonZeroU8, u8, NonZeroU128, u128);

// ── Sortable big-endian byte encodings ────────────────────────────

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
    /// use connections::core::u008::U008BE01;
    ///
    /// assert_eq!(U008BE01.ceil(0x42_u8), [0x42]);
    /// assert_eq!(U008BE01.upper([0x42]), 0x42_u8);
    /// ```
    pub U008BE01 : u8 => [u8; 1] {
        forward: u8_to_be01,
        back:    be01_to_u8,
    }
}

// ── Sortable little-endian byte encodings ─────────────────────────

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

// ────────────────────────────────────────────────────────────────────
// Tests
// ────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    #[allow(unused_imports)]
    use crate::conn::{ConnL, ConnR};
    #[allow(unused_imports)]
    use crate::core::{
        i008::I008U008, i016::I016U008, i032::I032U008, i064::I064U008, i128::I128U008,
        u016::U016U008, u032::U032U008, u064::U064U008, u128::U128U008,
    };
    use crate::prop::conn as conn_laws;
    use proptest::prelude::*;

    // ── §1 std-int spot checks ─────────────────────────────────────

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

    // ── §3 u8 ↔ NonZeroU8 spot checks ──────────────────────────────

    #[test]
    fn u008n008_zero_saturates_to_one() {
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

    fn arb_nz_u8() -> impl Strategy<Value = NonZeroU8> {
        any::<u8>().prop_filter_map("non-zero u8", NonZeroU8::new)
    }

    proptest! {
        #[test]
        fn u008n008_galois_l(a in any::<u8>(), b in arb_nz_u8()) {
            prop_assert!(conn_laws::galois_l(&U008N008.conn_l(), a, b));
        }

        #[test]
        fn u008n008_inner_then_ceil_recovers_nonzero(nz in arb_nz_u8()) {
            prop_assert_eq!(U008N008.ceil(U008N008.upper(nz)), nz);
        }
    }

    // ── NonZero unsigned widening (N###N###) spot + property checks ─

    #[test]
    fn n008n016_widens_losslessly_at_boundary() {
        let one = NonZeroU8::new(1).unwrap();
        let max = NonZeroU8::new(u8::MAX).unwrap();
        assert_eq!(N008N016.ceil(one), NonZeroU16::new(1).unwrap());
        assert_eq!(N008N016.ceil(max), NonZeroU16::new(u8::MAX as u16).unwrap());
    }

    #[test]
    fn n008n016_inner_saturates_above_source_max() {
        // Any NonZeroU16 above u8::MAX saturates to NonZeroU8::MAX.
        let big = NonZeroU16::new(u16::MAX).unwrap();
        assert_eq!(N008N016.upper(big), NonZeroU8::new(u8::MAX).unwrap());
        // Just-above-cap saturates too.
        let just_above = NonZeroU16::new(u8::MAX as u16 + 1).unwrap();
        assert_eq!(N008N016.upper(just_above), NonZeroU8::new(u8::MAX).unwrap());
        // In-range survives.
        let in_range = NonZeroU16::new(42).unwrap();
        assert_eq!(N008N016.upper(in_range), NonZeroU8::new(42).unwrap());
    }

    fn arb_nz_u16() -> impl Strategy<Value = NonZeroU16> {
        any::<u16>().prop_filter_map("non-zero u16", NonZeroU16::new)
    }
    fn arb_nz_u32() -> impl Strategy<Value = NonZeroU32> {
        any::<u32>().prop_filter_map("non-zero u32", NonZeroU32::new)
    }
    fn arb_nz_u64() -> impl Strategy<Value = NonZeroU64> {
        any::<u64>().prop_filter_map("non-zero u64", NonZeroU64::new)
    }
    fn arb_nz_u128() -> impl Strategy<Value = NonZeroU128> {
        any::<u128>().prop_filter_map("non-zero u128", NonZeroU128::new)
    }

    proptest! {
        #[test]
        fn n008n016_galois_l(a in arb_nz_u8(), b in arb_nz_u16()) {
            prop_assert!(conn_laws::galois_l(&N008N016.conn_l(), a, b));
        }
        #[test]
        fn n008n016_round_trip_below_cap(n in arb_nz_u8()) {
            prop_assert_eq!(N008N016.upper(N008N016.ceil(n)), n);
        }
        #[test]
        fn n008n032_galois_l(a in arb_nz_u8(), b in arb_nz_u32()) {
            prop_assert!(conn_laws::galois_l(&N008N032.conn_l(), a, b));
        }
        #[test]
        fn n008n064_galois_l(a in arb_nz_u8(), b in arb_nz_u64()) {
            prop_assert!(conn_laws::galois_l(&N008N064.conn_l(), a, b));
        }
        #[test]
        fn n008n128_galois_l(a in arb_nz_u8(), b in arb_nz_u128()) {
            prop_assert!(conn_laws::galois_l(&N008N128.conn_l(), a, b));
        }
    }

    // ── BE / LE byte-encoding tests ────────────────────────────────

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
    }
}
