//! `i16`-source std-int Conns plus the `i16 ↔ NonZeroI16` adjoint and
//! two's-complement big- / little-endian byte encodings.
//!
//! Q-format / cross-crate isos to `FixedI16<F>` live next door in
//! `crate::fixed::i016`.

#[allow(unused_imports)]
use crate::core::{B2, L2, LX};
use crate::core::{ext_int, int_int_narrow, int_uint, int_uint_narrow, nz_int_ext, nz_int_narrow};
use ::core::num::{NonZeroI8, NonZeroI16};

// ── §1 std-int Conns sourced from `i16` ───────────────────────────

int_int_narrow!(I016I008, i16, i8);
ext_int!(I016I032, i16, i32);
ext_int!(I016I064, i16, i64);
ext_int!(I016I128, i16, i128);

int_uint_narrow!(I016U008, i16, u8);
int_uint!(I016U016, i16, u16);
int_uint!(I016U032, i16, u32);
int_uint!(I016U064, i16, u64);
int_uint!(I016U128, i16, u128);

// ── §3 i16 ↔ NonZeroI16 ───────────────────────────────────────────

nz_int_ext!(I016N016, i16, NonZeroI16);

// ── NonZero signed narrowings ─────────────────────────────────────

nz_int_narrow!(N016N008, NonZeroI16, i16, NonZeroI8, i8);

// ── Two's-complement big-endian byte encodings ────────────────────

const fn i16_to_be02(x: i16) -> B2<2> {
    B2(x.to_be_bytes())
}
const fn be02_to_i16(b: B2<2>) -> i16 {
    i16::from_be_bytes(b.0)
}

crate::iso! {
    /// `i16 ↔ B2<2>` — raw two's-complement big-endian iso.
    pub I016BE02 : i16 => B2<2> {
        forward: i16_to_be02,
        back:    be02_to_i16,
    }
}

// ── Two's-complement little-endian byte encodings ─────────────────

const fn i16_to_le02(x: i16) -> L2<2> {
    L2(x.to_le_bytes())
}
const fn le02_to_i16(b: L2<2>) -> i16 {
    i16::from_le_bytes(b.0)
}

crate::iso! {
    /// `i16 ↔ L2<2>` — raw two's-complement little-endian iso.
    pub I016LE02 : i16 => L2<2> {
        forward: i16_to_le02,
        back:    le02_to_i16,
    }
}

// ── Lex-key big-endian encoding (LX) ──────────────────────────────

const fn i16_to_lx02(x: i16) -> LX<2> {
    LX((x as u16).wrapping_add(0x8000).to_be_bytes())
}
const fn lx02_to_i16(b: LX<2>) -> i16 {
    u16::from_be_bytes(b.0).wrapping_sub(0x8000) as i16
}

crate::iso! {
    /// `i16 ↔ LX<2>` — bias-encoded big-endian iso whose raw byte
    /// `Ord` matches signed numeric order. See [`I008LX01`] for the
    /// design rationale.
    ///
    /// [`I008LX01`]: crate::core::i008::I008LX01
    pub I016LX02 : i16 => LX<2> {
        forward: i16_to_lx02,
        back:    lx02_to_i16,
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
        i008::I008I016, i032::I032I016, i064::I064I016, i128::I128I016, u008::U008I016,
        u016::U016I016, u032::U032I016, u064::U064I016, u128::U128I016,
    };
    use crate::extended::Extended;
    use crate::prop::conn as conn_laws;
    use proptest::prelude::*;

    #[test]
    fn i008i016_ceil_at_boundaries() {
        assert_eq!(crate::conn::ceil(&I008I016, Extended::NegInf), i16::MIN);
        assert_eq!(crate::conn::ceil(&I008I016, Extended::PosInf), 128);
        assert_eq!(crate::conn::ceil(&I008I016, Extended::Finite(0)), 0);
        assert_eq!(
            crate::conn::ceil(&I008I016, Extended::Finite(i8::MIN)),
            -128
        );
        assert_eq!(crate::conn::ceil(&I008I016, Extended::Finite(i8::MAX)), 127);
    }

    #[test]
    fn i008i016_inner_partitions_target_range() {
        assert_eq!(crate::conn::upper(&I008I016, -129), Extended::NegInf);
        assert_eq!(crate::conn::upper(&I008I016, i16::MIN), Extended::NegInf);
        assert_eq!(crate::conn::upper(&I008I016, 128), Extended::PosInf);
        assert_eq!(crate::conn::upper(&I008I016, i16::MAX), Extended::PosInf);
        assert_eq!(
            crate::conn::upper(&I008I016, -128),
            Extended::Finite(i8::MIN)
        );
        assert_eq!(crate::conn::upper(&I008I016, 0), Extended::Finite(0));
        assert_eq!(
            crate::conn::upper(&I008I016, 127),
            Extended::Finite(i8::MAX)
        );
    }

    #[test]
    fn u008i016_ceil_at_boundaries() {
        assert_eq!(crate::conn::ceil(&U008I016, Extended::NegInf), i16::MIN);
        assert_eq!(crate::conn::ceil(&U008I016, Extended::PosInf), 256);
        assert_eq!(crate::conn::ceil(&U008I016, Extended::Finite(0)), 0);
        assert_eq!(crate::conn::ceil(&U008I016, Extended::Finite(255)), 255);
    }

    #[test]
    fn u008i016_inner_partitions_target_range() {
        assert_eq!(crate::conn::upper(&U008I016, -1), Extended::NegInf);
        assert_eq!(crate::conn::upper(&U008I016, i16::MIN), Extended::NegInf);
        assert_eq!(crate::conn::upper(&U008I016, 256), Extended::PosInf);
        assert_eq!(crate::conn::upper(&U008I016, i16::MAX), Extended::PosInf);
        assert_eq!(crate::conn::upper(&U008I016, 0), Extended::Finite(0));
        assert_eq!(crate::conn::upper(&U008I016, 50), Extended::Finite(50));
        assert_eq!(crate::conn::upper(&U008I016, 255), Extended::Finite(255));
    }

    #[test]
    fn i_to_i16_saturate() {
        assert_eq!(crate::conn::ceil(&I032I016, i32::MAX), i16::MAX);
        assert_eq!(crate::conn::ceil(&I032I016, i32::MIN), i16::MIN);
        assert_eq!(crate::conn::ceil(&I128I016, i128::MAX), i16::MAX);
        assert_eq!(crate::conn::ceil(&I128I016, i128::MIN), i16::MIN);
    }

    #[test]
    fn i_to_i16_inner_fine_max_fixup() {
        assert_eq!(crate::conn::upper(&I032I016, i16::MAX), i32::MAX);
        assert_eq!(crate::conn::upper(&I064I016, i16::MAX), i64::MAX);
        assert_eq!(crate::conn::upper(&I128I016, i16::MAX), i128::MAX);
        assert_eq!(crate::conn::upper(&I032I016, 0), 0_i32);
        assert_eq!(crate::conn::upper(&I032I016, i16::MIN), i16::MIN as i32);
    }

    #[test]
    fn u_to_i16_neg_and_high() {
        assert_eq!(crate::conn::lower(&U016I016, -1), 0_u16);
        assert_eq!(crate::conn::lower(&U016I016, i16::MIN), 0_u16);
        assert_eq!(crate::conn::floor(&U016I016, u16::MAX), i16::MAX);
        assert_eq!(crate::conn::floor(&U128I016, u128::MAX), i16::MAX);
    }

    // ── NonZero signed narrowing (N016N008) spot + property ───────

    fn arb_nz_i8() -> impl Strategy<Value = NonZeroI8> {
        any::<i8>().prop_filter_map("non-zero i8", NonZeroI8::new)
    }
    fn arb_nz_i16() -> impl Strategy<Value = NonZeroI16> {
        any::<i16>().prop_filter_map("non-zero i16", NonZeroI16::new)
    }

    #[test]
    fn n016n008_saturates_both_plateaus() {
        let big_pos = NonZeroI16::new(i16::MAX).unwrap();
        let big_neg = NonZeroI16::new(i16::MIN).unwrap();
        let in_range = NonZeroI16::new(42).unwrap();
        assert_eq!(
            crate::conn::ceil(&N016N008, big_pos),
            NonZeroI8::new(i8::MAX).unwrap()
        );
        assert_eq!(
            crate::conn::ceil(&N016N008, big_neg),
            NonZeroI8::new(i8::MIN).unwrap()
        );
        assert_eq!(
            crate::conn::ceil(&N016N008, in_range),
            NonZeroI8::new(42).unwrap()
        );
        // FINE_MAX fixup: inner(NZ(i8::MAX)) = NZ(i16::MAX)
        assert_eq!(
            crate::conn::upper(&N016N008, NonZeroI8::new(i8::MAX).unwrap()),
            NonZeroI16::new(i16::MAX).unwrap()
        );
        assert_eq!(
            crate::conn::upper(&N016N008, NonZeroI8::new(i8::MIN).unwrap()),
            NonZeroI16::new(i8::MIN as i16).unwrap()
        );
    }

    proptest! {
        #[test]
        fn n016n008_galois_l(a in arb_nz_i16(), b in arb_nz_i8()) {
            prop_assert!(conn_laws::galois_l(&N016N008.conn_l(), a, b));
        }
    }

    fn arb_byte2() -> impl Strategy<Value = B2<2>> {
        prop_oneof![Just([0; 2]), Just([0xFF; 2]), any::<[u8; 2]>()].prop_map(B2)
    }

    fn arb_lebyte2() -> impl Strategy<Value = L2<2>> {
        prop_oneof![Just([0; 2]), Just([0xFF; 2]), any::<[u8; 2]>()].prop_map(L2)
    }

    proptest! {
        #[test]
        fn i16_b2_iso_roundtrip_l(a in prop_oneof![Just(i16::MIN), Just(0i16), Just(i16::MAX), any::<i16>()]) {
            prop_assert!(conn_laws::iso_roundtrip_l(&I016BE02.conn_l(), a));
        }
        #[test]
        fn i16_b2_roundtrip_ceil(b in arb_byte2()) {
            prop_assert!(conn_laws::roundtrip_ceil(&I016BE02.conn_l(), b));
        }
        #[test]
        fn i16_b2_galois_l(a in any::<i16>(), b in arb_byte2()) {
            prop_assert!(conn_laws::galois_l(&I016BE02.conn_l(), a, b));
        }
        #[test]
        fn i16_b2_galois_r(a in any::<i16>(), b in arb_byte2()) {
            prop_assert!(conn_laws::galois_r(&I016BE02.conn_r(), a, b));
        }
        #[test]
        fn i16_b2_floor_le_ceil(a in any::<i16>()) {
            prop_assert!(conn_laws::floor_le_ceil(&I016BE02, a));
        }
        #[test]
        fn i16_b2_order_preserving(a in any::<i16>(), b in any::<i16>()) {
            prop_assert_eq!(a.cmp(&b), crate::conn::ceil(&I016BE02, a).cmp(&crate::conn::ceil(&I016BE02, b)));
        }

        #[test]
        fn i016_l2_iso_roundtrip_l(a in prop_oneof![Just(i16::MIN), Just(0i16), Just(i16::MAX), any::<i16>()]) {
            prop_assert!(conn_laws::iso_roundtrip_l(&I016LE02.conn_l(), a));
        }

        #[test]
        fn i016_l2_roundtrip_ceil(b in arb_lebyte2()) {
            prop_assert!(conn_laws::roundtrip_ceil(&I016LE02.conn_l(), b));
        }

        #[test]
        fn i016_l2_galois_l(a in any::<i16>(), b in arb_lebyte2()) {
            prop_assert!(conn_laws::galois_l(&I016LE02.conn_l(), a, b));
        }

        #[test]
        fn i016_l2_galois_r(a in any::<i16>(), b in arb_lebyte2()) {
            prop_assert!(conn_laws::galois_r(&I016LE02.conn_r(), a, b));
        }

        #[test]
        fn i016_l2_floor_le_ceil(a in any::<i16>()) {
            prop_assert!(conn_laws::floor_le_ceil(&I016LE02, a));
        }

        #[test]
        fn i016_l2_order_preserving(a in any::<i16>(), b in any::<i16>()) {
            prop_assert_eq!(a.cmp(&b), crate::conn::ceil(&I016LE02, a).cmp(&crate::conn::ceil(&I016LE02, b)));
        }
    }

    // ── LX (lex-sortable big-endian) byte-encoding tests ──────────

    fn arb_lxbyte2() -> impl Strategy<Value = LX<2>> {
        prop_oneof![
            Just([0; 2]),
            Just([0x80, 0x00]),
            Just([0xFF; 2]),
            any::<[u8; 2]>()
        ]
        .prop_map(LX)
    }

    #[test]
    fn i016lx02_boundary_bytes() {
        assert_eq!(crate::conn::ceil(&I016LX02, i16::MIN), LX([0x00, 0x00]));
        assert_eq!(crate::conn::ceil(&I016LX02, 0_i16), LX([0x80, 0x00]));
        assert_eq!(crate::conn::ceil(&I016LX02, i16::MAX), LX([0xFF, 0xFF]));
        assert_eq!(crate::conn::upper(&I016LX02, LX([0x00, 0x00])), i16::MIN);
        assert_eq!(crate::conn::upper(&I016LX02, LX([0x80, 0x00])), 0_i16);
        assert_eq!(crate::conn::upper(&I016LX02, LX([0xFF, 0xFF])), i16::MAX);
    }

    proptest! {
        #[test]
        fn i016_lx_iso_roundtrip_l(
            a in prop_oneof![Just(i16::MIN), Just(0i16), Just(i16::MAX), any::<i16>()]
        ) {
            prop_assert!(conn_laws::iso_roundtrip_l(&I016LX02.conn_l(), a));
        }
        #[test]
        fn i016_lx_roundtrip_ceil(b in arb_lxbyte2()) {
            prop_assert!(conn_laws::roundtrip_ceil(&I016LX02.conn_l(), b));
        }
        #[test]
        fn i016_lx_galois_l(a in any::<i16>(), b in arb_lxbyte2()) {
            prop_assert!(conn_laws::galois_l(&I016LX02.conn_l(), a, b));
        }
        #[test]
        fn i016_lx_galois_r(a in any::<i16>(), b in arb_lxbyte2()) {
            prop_assert!(conn_laws::galois_r(&I016LX02.conn_r(), a, b));
        }
        #[test]
        fn i016_lx_floor_le_ceil(a in any::<i16>()) {
            prop_assert!(conn_laws::floor_le_ceil(&I016LX02, a));
        }
        // The I016LX02 contract: signed numeric compare ⟺ raw byte
        // lex compare on the bias-encoded bytes.
        #[test]
        fn i016_lx_signed_cmp_matches_raw_byte_cmp(a in any::<i16>(), b in any::<i16>()) {
            let ka = crate::conn::ceil(&I016LX02, a).0;
            let kb = crate::conn::ceil(&I016LX02, b).0;
            prop_assert_eq!(a.cmp(&b), ka.cmp(&kb));
        }
    }
}
