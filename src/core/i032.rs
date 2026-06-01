//! `i32`-source std-int Conns plus the `i32 ↔ NonZeroI32` adjoint and
//! two's-complement big- / little-endian byte encodings.
//!
//! Q-format / cross-crate isos to `FixedI32<F>` live next door in
//! `crate::fixed::i032`.

#[allow(unused_imports)]
use crate::core::{B2, L2, LX};
use crate::core::{ext_int, int_int_narrow, int_uint, int_uint_narrow, nz_int_ext, nz_int_narrow};
use ::core::num::{NonZeroI8, NonZeroI16, NonZeroI32};

// ── §1 std-int Conns sourced from `i32` ───────────────────────────

int_int_narrow!(I032I008, i32, i8);
int_int_narrow!(I032I016, i32, i16);
ext_int!(I032I064, i32, i64);
ext_int!(I032I128, i32, i128);

int_uint_narrow!(I032U008, i32, u8);
int_uint_narrow!(I032U016, i32, u16);
int_uint!(I032U032, i32, u32);
int_uint!(I032U064, i32, u64);
int_uint!(I032U128, i32, u128);

// ── §3 i32 ↔ NonZeroI32 ───────────────────────────────────────────

nz_int_ext!(I032N032, i32, NonZeroI32);

// ── NonZero signed narrowings ─────────────────────────────────────

nz_int_narrow!(N032N008, NonZeroI32, i32, NonZeroI8, i8);
nz_int_narrow!(N032N016, NonZeroI32, i32, NonZeroI16, i16);

// ── Two's-complement big-endian byte encodings ────────────────────

const fn i32_to_be04(x: i32) -> B2<4> {
    B2(x.to_be_bytes())
}
const fn be04_to_i32(b: B2<4>) -> i32 {
    i32::from_be_bytes(b.0)
}

crate::iso! {
    /// `i32 ↔ B2<4>` — raw two's-complement big-endian iso.
    pub I032BE04 : i32 => B2<4> {
        forward: i32_to_be04,
        back:    be04_to_i32,
    }
}

// ── Two's-complement little-endian byte encodings ─────────────────

const fn i32_to_le04(x: i32) -> L2<4> {
    L2(x.to_le_bytes())
}
const fn le04_to_i32(b: L2<4>) -> i32 {
    i32::from_le_bytes(b.0)
}

crate::iso! {
    /// `i32 ↔ L2<4>` — raw two's-complement little-endian iso.
    pub I032LE04 : i32 => L2<4> {
        forward: i32_to_le04,
        back:    le04_to_i32,
    }
}

// ── Lex-key big-endian encoding (LX) ──────────────────────────────

const fn i32_to_lx04(x: i32) -> LX<4> {
    LX((x as u32).wrapping_add(0x8000_0000).to_be_bytes())
}
const fn lx04_to_i32(b: LX<4>) -> i32 {
    u32::from_be_bytes(b.0).wrapping_sub(0x8000_0000) as i32
}

crate::iso! {
    /// `i32 ↔ LX<4>` — bias-encoded big-endian iso whose raw byte
    /// `Ord` matches signed numeric order. See [`I008LX01`] for the
    /// design rationale.
    ///
    /// [`I008LX01`]: crate::core::i008::I008LX01
    pub I032LX04 : i32 => LX<4> {
        forward: i32_to_lx04,
        back:    lx04_to_i32,
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
        i008::I008I032, i016::I016I032, i064::I064I032, i128::I128I032, u008::U008I032,
        u016::U016I032, u032::U032I032, u064::U064I032, u128::U128I032,
    };
    use crate::extended::Extended;
    use crate::prop::conn as conn_laws;
    use proptest::prelude::*;

    #[test]
    fn i008i032_round_trip_at_finite_boundaries() {
        assert_eq!(
            crate::conn::ceil(&I008I032, Extended::Finite(i8::MIN)),
            -128
        );
        assert_eq!(crate::conn::ceil(&I008I032, Extended::Finite(i8::MAX)), 127);
        assert_eq!(
            crate::conn::upper(&I008I032, -128),
            Extended::Finite(i8::MIN)
        );
        assert_eq!(
            crate::conn::upper(&I008I032, 127),
            Extended::Finite(i8::MAX)
        );
    }

    #[test]
    fn u016i032_inner_partitions() {
        assert_eq!(crate::conn::upper(&U016I032, -1), Extended::NegInf);
        assert_eq!(crate::conn::upper(&U016I032, 0), Extended::Finite(0));
        assert_eq!(
            crate::conn::upper(&U016I032, 65_535),
            Extended::Finite(u16::MAX)
        );
        assert_eq!(crate::conn::upper(&U016I032, 65_536), Extended::PosInf);
    }

    #[test]
    fn i_to_i32_saturate() {
        assert_eq!(crate::conn::ceil(&I064I032, i64::MAX), i32::MAX);
        assert_eq!(crate::conn::ceil(&I064I032, i64::MIN), i32::MIN);
        assert_eq!(crate::conn::ceil(&I128I032, i128::MAX), i32::MAX);
        assert_eq!(crate::conn::ceil(&I128I032, i128::MIN), i32::MIN);
    }

    #[test]
    fn i_to_i32_inner_fine_max_fixup() {
        assert_eq!(crate::conn::upper(&I064I032, i32::MAX), i64::MAX);
        assert_eq!(crate::conn::upper(&I128I032, i32::MAX), i128::MAX);
    }

    #[test]
    fn u_to_i32_neg_and_high() {
        assert_eq!(crate::conn::lower(&U032I032, -1), 0_u32);
        assert_eq!(crate::conn::floor(&U064I032, u64::MAX), i32::MAX);
        assert_eq!(crate::conn::lower(&U128I032, i32::MIN), 0_u128);
    }

    // ── NonZero signed narrowing (N032N###) spot + property ───────

    fn arb_nz_i8() -> impl Strategy<Value = NonZeroI8> {
        any::<i8>().prop_filter_map("non-zero i8", NonZeroI8::new)
    }
    fn arb_nz_i16() -> impl Strategy<Value = NonZeroI16> {
        any::<i16>().prop_filter_map("non-zero i16", NonZeroI16::new)
    }
    fn arb_nz_i32() -> impl Strategy<Value = NonZeroI32> {
        any::<i32>().prop_filter_map("non-zero i32", NonZeroI32::new)
    }

    proptest! {
        #[test]
        fn n032n008_galois_l(a in arb_nz_i32(), b in arb_nz_i8()) {
            prop_assert!(conn_laws::galois_l(&N032N008.conn_l(), a, b));
        }
        #[test]
        fn n032n016_galois_l(a in arb_nz_i32(), b in arb_nz_i16()) {
            prop_assert!(conn_laws::galois_l(&N032N016.conn_l(), a, b));
        }
    }

    fn arb_byte4() -> impl Strategy<Value = B2<4>> {
        prop_oneof![Just([0; 4]), Just([0xFF; 4]), any::<[u8; 4]>()].prop_map(B2)
    }

    fn arb_lebyte4() -> impl Strategy<Value = L2<4>> {
        prop_oneof![Just([0; 4]), Just([0xFF; 4]), any::<[u8; 4]>()].prop_map(L2)
    }

    proptest! {
        #[test]
        fn i32_b2_iso_roundtrip_l(a in prop_oneof![Just(i32::MIN), Just(0i32), Just(i32::MAX), any::<i32>()]) {
            prop_assert!(conn_laws::iso_roundtrip_l(&I032BE04.conn_l(), a));
        }
        #[test]
        fn i32_b2_roundtrip_ceil(b in arb_byte4()) {
            prop_assert!(conn_laws::roundtrip_ceil(&I032BE04.conn_l(), b));
        }
        #[test]
        fn i32_b2_galois_l(a in any::<i32>(), b in arb_byte4()) {
            prop_assert!(conn_laws::galois_l(&I032BE04.conn_l(), a, b));
        }
        #[test]
        fn i32_b2_galois_r(a in any::<i32>(), b in arb_byte4()) {
            prop_assert!(conn_laws::galois_r(&I032BE04.conn_r(), a, b));
        }
        #[test]
        fn i32_b2_floor_le_ceil(a in any::<i32>()) {
            prop_assert!(conn_laws::floor_le_ceil(&I032BE04, a));
        }
        #[test]
        fn i32_b2_order_preserving(a in any::<i32>(), b in any::<i32>()) {
            prop_assert_eq!(a.cmp(&b), crate::conn::ceil(&I032BE04, a).cmp(&crate::conn::ceil(&I032BE04, b)));
        }

        #[test]
        fn i032_l2_iso_roundtrip_l(a in prop_oneof![Just(i32::MIN), Just(0i32), Just(i32::MAX), any::<i32>()]) {
            prop_assert!(conn_laws::iso_roundtrip_l(&I032LE04.conn_l(), a));
        }

        #[test]
        fn i032_l2_roundtrip_ceil(b in arb_lebyte4()) {
            prop_assert!(conn_laws::roundtrip_ceil(&I032LE04.conn_l(), b));
        }

        #[test]
        fn i032_l2_galois_l(a in any::<i32>(), b in arb_lebyte4()) {
            prop_assert!(conn_laws::galois_l(&I032LE04.conn_l(), a, b));
        }

        #[test]
        fn i032_l2_galois_r(a in any::<i32>(), b in arb_lebyte4()) {
            prop_assert!(conn_laws::galois_r(&I032LE04.conn_r(), a, b));
        }

        #[test]
        fn i032_l2_floor_le_ceil(a in any::<i32>()) {
            prop_assert!(conn_laws::floor_le_ceil(&I032LE04, a));
        }

        #[test]
        fn i032_l2_order_preserving(a in any::<i32>(), b in any::<i32>()) {
            prop_assert_eq!(a.cmp(&b), crate::conn::ceil(&I032LE04, a).cmp(&crate::conn::ceil(&I032LE04, b)));
        }
    }

    // ── LX (lex-sortable big-endian) byte-encoding tests ──────────

    fn arb_lxbyte4() -> impl Strategy<Value = LX<4>> {
        prop_oneof![
            Just([0; 4]),
            Just([0x80, 0x00, 0x00, 0x00]),
            Just([0xFF; 4]),
            any::<[u8; 4]>()
        ]
        .prop_map(LX)
    }

    #[test]
    fn i032lx04_boundary_bytes() {
        assert_eq!(
            crate::conn::ceil(&I032LX04, i32::MIN),
            LX([0x00, 0x00, 0x00, 0x00])
        );
        assert_eq!(
            crate::conn::ceil(&I032LX04, 0_i32),
            LX([0x80, 0x00, 0x00, 0x00])
        );
        assert_eq!(
            crate::conn::ceil(&I032LX04, i32::MAX),
            LX([0xFF, 0xFF, 0xFF, 0xFF])
        );
        assert_eq!(
            crate::conn::upper(&I032LX04, LX([0x00, 0x00, 0x00, 0x00])),
            i32::MIN
        );
        assert_eq!(
            crate::conn::upper(&I032LX04, LX([0x80, 0x00, 0x00, 0x00])),
            0_i32
        );
        assert_eq!(
            crate::conn::upper(&I032LX04, LX([0xFF, 0xFF, 0xFF, 0xFF])),
            i32::MAX
        );
    }

    proptest! {
        #[test]
        fn i032_lx_iso_roundtrip_l(
            a in prop_oneof![Just(i32::MIN), Just(0i32), Just(i32::MAX), any::<i32>()]
        ) {
            prop_assert!(conn_laws::iso_roundtrip_l(&I032LX04.conn_l(), a));
        }
        #[test]
        fn i032_lx_roundtrip_ceil(b in arb_lxbyte4()) {
            prop_assert!(conn_laws::roundtrip_ceil(&I032LX04.conn_l(), b));
        }
        #[test]
        fn i032_lx_galois_l(a in any::<i32>(), b in arb_lxbyte4()) {
            prop_assert!(conn_laws::galois_l(&I032LX04.conn_l(), a, b));
        }
        #[test]
        fn i032_lx_galois_r(a in any::<i32>(), b in arb_lxbyte4()) {
            prop_assert!(conn_laws::galois_r(&I032LX04.conn_r(), a, b));
        }
        #[test]
        fn i032_lx_floor_le_ceil(a in any::<i32>()) {
            prop_assert!(conn_laws::floor_le_ceil(&I032LX04, a));
        }
        #[test]
        fn i032_lx_signed_cmp_matches_raw_byte_cmp(a in any::<i32>(), b in any::<i32>()) {
            let ka = crate::conn::ceil(&I032LX04, a).0;
            let kb = crate::conn::ceil(&I032LX04, b).0;
            prop_assert_eq!(a.cmp(&b), ka.cmp(&kb));
        }
    }
}
