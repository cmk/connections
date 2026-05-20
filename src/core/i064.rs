//! `i64`-source std-int Conns plus the `i64 ↔ NonZeroI64` adjoint and
//! two's-complement big- / little-endian byte encodings.
//!
//! Q-format / cross-crate isos to `FixedI64<F>` live next door in
//! `crate::fixed::i064`.

#[allow(unused_imports)]
use crate::core::{B2, L2, LX};
use crate::core::{ext_int, int_int_narrow, int_uint, int_uint_narrow, nz_int_ext, nz_int_narrow};
use ::core::num::{NonZeroI8, NonZeroI16, NonZeroI32, NonZeroI64};

// ── §1 std-int Conns sourced from `i64` ───────────────────────────

int_int_narrow!(I064I008, i64, i8);
int_int_narrow!(I064I016, i64, i16);
int_int_narrow!(I064I032, i64, i32);
ext_int!(I064I128, i64, i128);

int_uint_narrow!(I064U008, i64, u8);
int_uint_narrow!(I064U016, i64, u16);
int_uint_narrow!(I064U032, i64, u32);
int_uint!(I064U064, i64, u64);
int_uint!(I064U128, i64, u128);

// ── §3 i64 ↔ NonZeroI64 ───────────────────────────────────────────

nz_int_ext!(I064N064, i64, NonZeroI64);

// ── NonZero signed narrowings ─────────────────────────────────────

nz_int_narrow!(N064N008, NonZeroI64, i64, NonZeroI8, i8);
nz_int_narrow!(N064N016, NonZeroI64, i64, NonZeroI16, i16);
nz_int_narrow!(N064N032, NonZeroI64, i64, NonZeroI32, i32);

// ── Two's-complement big-endian byte encodings ────────────────────

const fn i64_to_be08(x: i64) -> B2<8> {
    B2(x.to_be_bytes())
}
const fn be08_to_i64(b: B2<8>) -> i64 {
    i64::from_be_bytes(b.0)
}

crate::iso! {
    /// `i64 ↔ B2<8>` — raw two's-complement big-endian iso.
    pub I064BE08 : i64 => B2<8> {
        forward: i64_to_be08,
        back:    be08_to_i64,
    }
}

// ── Two's-complement little-endian byte encodings ─────────────────

const fn i64_to_le08(x: i64) -> L2<8> {
    L2(x.to_le_bytes())
}
const fn le08_to_i64(b: L2<8>) -> i64 {
    i64::from_le_bytes(b.0)
}

crate::iso! {
    /// `i64 ↔ L2<8>` — raw two's-complement little-endian iso.
    pub I064LE08 : i64 => L2<8> {
        forward: i64_to_le08,
        back:    le08_to_i64,
    }
}

// ── Lex-key big-endian encoding (LX) ──────────────────────────────

const fn i64_to_lx08(x: i64) -> LX<8> {
    LX((x as u64).wrapping_add(0x8000_0000_0000_0000).to_be_bytes())
}
const fn lx08_to_i64(b: LX<8>) -> i64 {
    u64::from_be_bytes(b.0).wrapping_sub(0x8000_0000_0000_0000) as i64
}

crate::iso! {
    /// `i64 ↔ LX<8>` — bias-encoded big-endian iso whose raw byte
    /// `Ord` matches signed numeric order. See [`I008LX01`] for the
    /// design rationale.
    ///
    /// [`I008LX01`]: crate::core::i008::I008LX01
    pub I064LX08 : i64 => LX<8> {
        forward: i64_to_lx08,
        back:    lx08_to_i64,
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
        i008::I008I064, i016::I016I064, i032::I032I064, i128::I128I064, u008::U008I064,
        u016::U016I064, u032::U032I064, u064::U064I064, u128::U128I064,
    };
    use crate::extended::Extended;
    use crate::prop::conn as conn_laws;
    use proptest::prelude::*;

    #[test]
    fn i032i064_extends_to_one_above() {
        assert_eq!(I032I064.ceil(Extended::PosInf), (i32::MAX as i64) + 1);
        assert_eq!(I032I064.ceil(Extended::NegInf), i64::MIN);
    }

    #[test]
    fn u032i064_extends_to_one_above() {
        assert_eq!(U032I064.ceil(Extended::PosInf), 4_294_967_296);
        assert_eq!(U032I064.ceil(Extended::NegInf), i64::MIN);
    }

    #[test]
    fn i128i064_saturate_and_fixup() {
        assert_eq!(I128I064.ceil(i128::MAX), i64::MAX);
        assert_eq!(I128I064.ceil(i128::MIN), i64::MIN);
        assert_eq!(I128I064.upper(i64::MAX), i128::MAX);
        assert_eq!(I128I064.upper(i64::MIN), i64::MIN as i128);
    }

    #[test]
    fn u_to_i64_neg_and_high() {
        assert_eq!(U064I064.lower(-1), 0_u64);
        assert_eq!(U064I064.floor(u64::MAX), i64::MAX);
        assert_eq!(U128I064.lower(i64::MIN), 0_u128);
        assert_eq!(U128I064.floor(u128::MAX), i64::MAX);
    }

    // (Reference to I008I064/I016I064 is via the import above; the
    // signed-i64-source proptests for byte encodings appear next.)

    // ── NonZero signed narrowing (N064N###) spot + property ───────

    fn arb_nz_i8() -> impl Strategy<Value = NonZeroI8> {
        any::<i8>().prop_filter_map("non-zero i8", NonZeroI8::new)
    }
    fn arb_nz_i16() -> impl Strategy<Value = NonZeroI16> {
        any::<i16>().prop_filter_map("non-zero i16", NonZeroI16::new)
    }
    fn arb_nz_i32() -> impl Strategy<Value = NonZeroI32> {
        any::<i32>().prop_filter_map("non-zero i32", NonZeroI32::new)
    }
    fn arb_nz_i64() -> impl Strategy<Value = NonZeroI64> {
        any::<i64>().prop_filter_map("non-zero i64", NonZeroI64::new)
    }

    proptest! {
        #[test]
        fn n064n008_galois_l(a in arb_nz_i64(), b in arb_nz_i8()) {
            prop_assert!(conn_laws::galois_l(&N064N008.conn_l(), a, b));
        }
        #[test]
        fn n064n016_galois_l(a in arb_nz_i64(), b in arb_nz_i16()) {
            prop_assert!(conn_laws::galois_l(&N064N016.conn_l(), a, b));
        }
        #[test]
        fn n064n032_galois_l(a in arb_nz_i64(), b in arb_nz_i32()) {
            prop_assert!(conn_laws::galois_l(&N064N032.conn_l(), a, b));
        }
    }

    fn arb_byte8() -> impl Strategy<Value = B2<8>> {
        prop_oneof![Just([0; 8]), Just([0xFF; 8]), any::<[u8; 8]>()].prop_map(B2)
    }

    fn arb_lebyte8() -> impl Strategy<Value = L2<8>> {
        prop_oneof![Just([0; 8]), Just([0xFF; 8]), any::<[u8; 8]>()].prop_map(L2)
    }

    proptest! {
        #[test]
        fn i64_b2_iso_roundtrip_l(a in prop_oneof![Just(i64::MIN), Just(0i64), Just(i64::MAX), any::<i64>()]) {
            prop_assert!(conn_laws::iso_roundtrip_l(&I064BE08.conn_l(), a));
        }
        #[test]
        fn i64_b2_roundtrip_ceil(b in arb_byte8()) {
            prop_assert!(conn_laws::roundtrip_ceil(&I064BE08.conn_l(), b));
        }
        #[test]
        fn i64_b2_galois_l(a in any::<i64>(), b in arb_byte8()) {
            prop_assert!(conn_laws::galois_l(&I064BE08.conn_l(), a, b));
        }
        #[test]
        fn i64_b2_galois_r(a in any::<i64>(), b in arb_byte8()) {
            prop_assert!(conn_laws::galois_r(&I064BE08.conn_r(), a, b));
        }
        #[test]
        fn i64_b2_floor_le_ceil(a in any::<i64>()) {
            prop_assert!(conn_laws::floor_le_ceil(&I064BE08, a));
        }
        #[test]
        fn i64_b2_order_preserving(a in any::<i64>(), b in any::<i64>()) {
            prop_assert_eq!(a.cmp(&b), I064BE08.ceil(a).cmp(&I064BE08.ceil(b)));
        }

        #[test]
        fn i064_l2_iso_roundtrip_l(a in prop_oneof![Just(i64::MIN), Just(0i64), Just(i64::MAX), any::<i64>()]) {
            prop_assert!(conn_laws::iso_roundtrip_l(&I064LE08.conn_l(), a));
        }

        #[test]
        fn i064_l2_roundtrip_ceil(b in arb_lebyte8()) {
            prop_assert!(conn_laws::roundtrip_ceil(&I064LE08.conn_l(), b));
        }

        #[test]
        fn i064_l2_galois_l(a in any::<i64>(), b in arb_lebyte8()) {
            prop_assert!(conn_laws::galois_l(&I064LE08.conn_l(), a, b));
        }

        #[test]
        fn i064_l2_galois_r(a in any::<i64>(), b in arb_lebyte8()) {
            prop_assert!(conn_laws::galois_r(&I064LE08.conn_r(), a, b));
        }

        #[test]
        fn i064_l2_floor_le_ceil(a in any::<i64>()) {
            prop_assert!(conn_laws::floor_le_ceil(&I064LE08, a));
        }

        #[test]
        fn i064_l2_order_preserving(a in any::<i64>(), b in any::<i64>()) {
            prop_assert_eq!(a.cmp(&b), I064LE08.ceil(a).cmp(&I064LE08.ceil(b)));
        }
    }

    // ── LX (lex-sortable big-endian) byte-encoding tests ──────────

    fn arb_lxbyte8() -> impl Strategy<Value = LX<8>> {
        prop_oneof![
            Just([0; 8]),
            Just([0x80, 0, 0, 0, 0, 0, 0, 0]),
            Just([0xFF; 8]),
            any::<[u8; 8]>()
        ]
        .prop_map(LX)
    }

    #[test]
    fn i064lx08_boundary_bytes() {
        assert_eq!(I064LX08.ceil(i64::MIN), LX([0x00; 8]));
        assert_eq!(I064LX08.ceil(0_i64), LX([0x80, 0, 0, 0, 0, 0, 0, 0]));
        assert_eq!(I064LX08.ceil(i64::MAX), LX([0xFF; 8]));
        assert_eq!(I064LX08.upper(LX([0x00; 8])), i64::MIN);
        assert_eq!(I064LX08.upper(LX([0x80, 0, 0, 0, 0, 0, 0, 0])), 0_i64);
        assert_eq!(I064LX08.upper(LX([0xFF; 8])), i64::MAX);
    }

    proptest! {
        #[test]
        fn i064_lx_iso_roundtrip_l(
            a in prop_oneof![Just(i64::MIN), Just(0i64), Just(i64::MAX), any::<i64>()]
        ) {
            prop_assert!(conn_laws::iso_roundtrip_l(&I064LX08.conn_l(), a));
        }
        #[test]
        fn i064_lx_roundtrip_ceil(b in arb_lxbyte8()) {
            prop_assert!(conn_laws::roundtrip_ceil(&I064LX08.conn_l(), b));
        }
        #[test]
        fn i064_lx_galois_l(a in any::<i64>(), b in arb_lxbyte8()) {
            prop_assert!(conn_laws::galois_l(&I064LX08.conn_l(), a, b));
        }
        #[test]
        fn i064_lx_galois_r(a in any::<i64>(), b in arb_lxbyte8()) {
            prop_assert!(conn_laws::galois_r(&I064LX08.conn_r(), a, b));
        }
        #[test]
        fn i064_lx_floor_le_ceil(a in any::<i64>()) {
            prop_assert!(conn_laws::floor_le_ceil(&I064LX08, a));
        }
        #[test]
        fn i064_lx_signed_cmp_matches_raw_byte_cmp(a in any::<i64>(), b in any::<i64>()) {
            let ka = I064LX08.ceil(a).0;
            let kb = I064LX08.ceil(b).0;
            prop_assert_eq!(a.cmp(&b), ka.cmp(&kb));
        }
    }
}
