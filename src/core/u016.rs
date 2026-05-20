//! `u16`-source std-int Conns plus the `u16 ↔ NonZeroU16` adjoint and
//! sortable big- / little-endian byte encodings.
//!
//! Q-format / cross-crate isos to `FixedU16<F>` live next door in
//! `crate::fixed::u016`.

#[allow(unused_imports)]
use crate::core::LE;
use crate::core::{
    ext_int, nz_uint_ext, nz_uint_narrow, nz_uint_widen, uint_int_sat, uint_uint, uint_uint_narrow,
};
use ::core::num::{NonZeroU8, NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU128};

// ── §1 std-int Conns sourced from `u16` ───────────────────────────

ext_int!(U016I032, u16, i32);
ext_int!(U016I064, u16, i64);
ext_int!(U016I128, u16, i128);
uint_int_sat!(U016I008, u16, i8);
uint_int_sat!(U016I016, u16, i16);

uint_uint_narrow!(U016U008, u16, u8);
uint_uint!(U016U032, u16, u32);
uint_uint!(U016U064, u16, u64);
uint_uint!(U016U128, u16, u128);

// ── §3 u16 ↔ NonZeroU16 ───────────────────────────────────────────

nz_uint_ext!(U016N016, u16, NonZeroU16);

// ── NonZero unsigned narrowings ───────────────────────────────────

nz_uint_narrow!(N016N008, NonZeroU16, u16, NonZeroU8, u8);

// ── NonZero unsigned widenings ────────────────────────────────────

nz_uint_widen!(N016N032, NonZeroU16, u16, NonZeroU32, u32);
nz_uint_widen!(N016N064, NonZeroU16, u16, NonZeroU64, u64);
nz_uint_widen!(N016N128, NonZeroU16, u16, NonZeroU128, u128);

// ── Sortable big-endian byte encodings ────────────────────────────

const fn u16_to_be02(x: u16) -> [u8; 2] {
    x.to_be_bytes()
}
const fn be02_to_u16(b: [u8; 2]) -> u16 {
    u16::from_be_bytes(b)
}

crate::iso! {
    /// `u16 ↔ [u8; 2]` — big-endian iso. Byte-lex order matches u16 order.
    pub U016BE02 : u16 => [u8; 2] {
        forward: u16_to_be02,
        back:    be02_to_u16,
    }
}

// ── Sortable little-endian byte encodings ─────────────────────────

const fn u16_to_le02(x: u16) -> LE<2> {
    LE(x.to_le_bytes())
}
const fn le02_to_u16(b: LE<2>) -> u16 {
    u16::from_le_bytes(b.0)
}

crate::iso! {
    /// `u16 ↔ LE<2>` — little-endian iso with numeric-sort ordering.
    pub U016LE02 : u16 => LE<2> {
        forward: u16_to_le02,
        back:    le02_to_u16,
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
        i008::I008U016, i016::I016U016, i032::I032U016, i064::I064U016, i128::I128U016,
        u008::U008U016, u032::U032U016, u064::U064U016, u128::U128U016,
    };
    use crate::prop::conn as conn_laws;
    use proptest::prelude::*;

    #[test]
    fn u008u016_ceil_widens_losslessly() {
        assert_eq!(U008U016.ceil(0u8), 0u16);
        assert_eq!(U008U016.ceil(u8::MAX), u8::MAX as u16);
    }

    #[test]
    fn u008u016_inner_saturates_at_source_max() {
        assert_eq!(U008U016.upper(u16::MAX), u8::MAX);
        assert_eq!(U008U016.upper(50), 50);
    }

    #[test]
    fn i016u016_galois_at_mid_positive() {
        for (a, b) in [(50i16, 100u16), (50i16, 49u16), (100i16, 100u16)] {
            assert_eq!(
                I016U016.ceil(a) <= b,
                a <= I016U016.upper(b),
                "I016U016 galois_upper @ ({a}, {b})"
            );
        }
    }

    #[test]
    fn i008u016_inner_saturates() {
        assert_eq!(I008U016.upper(u16::MAX), i8::MAX);
        assert_eq!(I008U016.upper(127), 127);
    }

    #[test]
    fn u_to_u16_saturate_and_fixup() {
        assert_eq!(U032U016.ceil(u32::MAX), u16::MAX);
        assert_eq!(U128U016.ceil(u128::MAX), u16::MAX);
        assert_eq!(U032U016.upper(u16::MAX), u32::MAX);
        assert_eq!(U064U016.upper(u16::MAX), u64::MAX);
        assert_eq!(U128U016.upper(u16::MAX), u128::MAX);
        assert_eq!(U032U016.upper(60_000), 60_000_u32);
    }

    #[test]
    fn i_to_u16_neg_high_fixup() {
        assert_eq!(I032U016.ceil(-1), 0);
        assert_eq!(I032U016.ceil(i32::MIN), 0);
        assert_eq!(I032U016.ceil(i32::MAX), u16::MAX);
        assert_eq!(I128U016.ceil(i128::MAX), u16::MAX);
        assert_eq!(I032U016.upper(u16::MAX), i32::MAX);
        assert_eq!(I128U016.upper(u16::MAX), i128::MAX);
    }

    // ── NonZero unsigned narrowing (N016N008) spot + property ─────

    fn arb_nz_u8() -> impl Strategy<Value = NonZeroU8> {
        any::<u8>().prop_filter_map("non-zero u8", NonZeroU8::new)
    }
    fn arb_nz_u16() -> impl Strategy<Value = NonZeroU16> {
        any::<u16>().prop_filter_map("non-zero u16", NonZeroU16::new)
    }

    #[test]
    fn n016n008_saturates_above_target_max() {
        let big = NonZeroU16::new(u16::MAX).unwrap();
        let just_above = NonZeroU16::new(u8::MAX as u16 + 1).unwrap();
        let in_range = NonZeroU16::new(42).unwrap();
        assert_eq!(N016N008.ceil(big), NonZeroU8::new(u8::MAX).unwrap());
        assert_eq!(N016N008.ceil(just_above), NonZeroU8::new(u8::MAX).unwrap());
        assert_eq!(N016N008.ceil(in_range), NonZeroU8::new(42).unwrap());
        // FINE_MAX fixup: inner(NZ(u8::MAX)) = NZ(u16::MAX)
        assert_eq!(
            N016N008.upper(NonZeroU8::new(u8::MAX).unwrap()),
            NonZeroU16::new(u16::MAX).unwrap()
        );
    }

    proptest! {
        #[test]
        fn n016n008_galois_l(a in arb_nz_u16(), b in arb_nz_u8()) {
            prop_assert!(conn_laws::galois_l(&N016N008.conn_l(), a, b));
        }
    }

    fn arb_byte2() -> impl Strategy<Value = [u8; 2]> {
        prop_oneof![Just([0; 2]), Just([0xFF; 2]), any::<[u8; 2]>()]
    }

    fn arb_lebyte2() -> impl Strategy<Value = LE<2>> {
        arb_byte2().prop_map(LE)
    }

    proptest! {
        #[test]
        fn u16_be_iso_roundtrip_l(a in prop_oneof![Just(0u16), Just(u16::MAX), any::<u16>()]) {
            prop_assert!(conn_laws::iso_roundtrip_l(&U016BE02.conn_l(), a));
        }
        #[test]
        fn u16_be_roundtrip_ceil(b in arb_byte2()) {
            prop_assert!(conn_laws::roundtrip_ceil(&U016BE02.conn_l(), b));
        }
        #[test]
        fn u16_be_galois_l(a in any::<u16>(), b in arb_byte2()) {
            prop_assert!(conn_laws::galois_l(&U016BE02.conn_l(), a, b));
        }
        #[test]
        fn u16_be_galois_r(a in any::<u16>(), b in arb_byte2()) {
            prop_assert!(conn_laws::galois_r(&U016BE02.conn_r(), a, b));
        }
        #[test]
        fn u16_be_floor_le_ceil(a in any::<u16>()) {
            prop_assert!(conn_laws::floor_le_ceil(&U016BE02, a));
        }
        #[test]
        fn u16_be_order_preserving(a in any::<u16>(), b in any::<u16>()) {
            prop_assert_eq!(a.cmp(&b), U016BE02.ceil(a).cmp(&U016BE02.ceil(b)));
        }

        #[test]
        fn u016_le_iso_roundtrip_l(a in prop_oneof![Just(0u16), Just(u16::MAX), any::<u16>()]) {
            prop_assert!(conn_laws::iso_roundtrip_l(&U016LE02.conn_l(), a));
        }

        #[test]
        fn u016_le_roundtrip_ceil(b in arb_lebyte2()) {
            prop_assert!(conn_laws::roundtrip_ceil(&U016LE02.conn_l(), b));
        }

        #[test]
        fn u016_le_galois_l(a in any::<u16>(), b in arb_lebyte2()) {
            prop_assert!(conn_laws::galois_l(&U016LE02.conn_l(), a, b));
        }

        #[test]
        fn u016_le_galois_r(a in any::<u16>(), b in arb_lebyte2()) {
            prop_assert!(conn_laws::galois_r(&U016LE02.conn_r(), a, b));
        }

        #[test]
        fn u016_le_floor_le_ceil(a in any::<u16>()) {
            prop_assert!(conn_laws::floor_le_ceil(&U016LE02, a));
        }

        #[test]
        fn u016_le_order_preserving(a in any::<u16>(), b in any::<u16>()) {
            prop_assert_eq!(a.cmp(&b), U016LE02.ceil(a).cmp(&U016LE02.ceil(b)));
        }
    }
}
