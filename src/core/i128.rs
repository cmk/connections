//! `i128`-source std-int Conns plus the `i128 ↔ NonZeroI128` adjoint and
//! two's-complement big- / little-endian byte encodings.
//!
//! Q-format / cross-crate isos to `FixedI128<F>` live next door in
//! `crate::fixed::i128`.

#[allow(unused_imports)]
use crate::core::{B2, L2, LX};
use crate::core::{int_int_narrow, int_uint, int_uint_narrow, nz_int_ext, nz_int_narrow};
use ::core::num::{NonZeroI8, NonZeroI16, NonZeroI32, NonZeroI64, NonZeroI128};

// ── §1 std-int Conns sourced from `i128` ──────────────────────────

int_int_narrow!(I128I008, i128, i8);
int_int_narrow!(I128I016, i128, i16);
int_int_narrow!(I128I032, i128, i32);
int_int_narrow!(I128I064, i128, i64);

int_uint_narrow!(I128U008, i128, u8);
int_uint_narrow!(I128U016, i128, u16);
int_uint_narrow!(I128U032, i128, u32);
int_uint_narrow!(I128U064, i128, u64);
int_uint!(I128U128, i128, u128);

// ── §3 i128 ↔ NonZeroI128 ─────────────────────────────────────────

nz_int_ext!(I128N128, i128, NonZeroI128);

// ── NonZero signed narrowings ─────────────────────────────────────

nz_int_narrow!(N128N008, NonZeroI128, i128, NonZeroI8, i8);
nz_int_narrow!(N128N016, NonZeroI128, i128, NonZeroI16, i16);
nz_int_narrow!(N128N032, NonZeroI128, i128, NonZeroI32, i32);
nz_int_narrow!(N128N064, NonZeroI128, i128, NonZeroI64, i64);

// ── Two's-complement big-endian byte encodings ────────────────────

const fn i128_to_be16(x: i128) -> B2<16> {
    B2(x.to_be_bytes())
}
const fn be16_to_i128(b: B2<16>) -> i128 {
    i128::from_be_bytes(b.0)
}

crate::iso! {
    /// `i128 ↔ B2<16>` — raw two's-complement big-endian iso.
    pub I128BE16 : i128 => B2<16> {
        forward: i128_to_be16,
        back:    be16_to_i128,
    }
}

// ── Two's-complement little-endian byte encodings ─────────────────

const fn i128_to_le16(x: i128) -> L2<16> {
    L2(x.to_le_bytes())
}
const fn le16_to_i128(b: L2<16>) -> i128 {
    i128::from_le_bytes(b.0)
}

crate::iso! {
    /// `i128 ↔ L2<16>` — raw two's-complement little-endian iso.
    pub I128LE16 : i128 => L2<16> {
        forward: i128_to_le16,
        back:    le16_to_i128,
    }
}

// ── Lex-key big-endian encoding (LX) ──────────────────────────────

const fn i128_to_lx16(x: i128) -> LX<16> {
    LX((x as u128)
        .wrapping_add(0x8000_0000_0000_0000_0000_0000_0000_0000)
        .to_be_bytes())
}
const fn lx16_to_i128(b: LX<16>) -> i128 {
    u128::from_be_bytes(b.0).wrapping_sub(0x8000_0000_0000_0000_0000_0000_0000_0000) as i128
}

crate::iso! {
    /// `i128 ↔ LX<16>` — bias-encoded big-endian iso whose raw byte
    /// `Ord` matches signed numeric order. See [`I008LX01`] for the
    /// design rationale.
    ///
    /// [`I008LX01`]: crate::core::i008::I008LX01
    pub I128LX16 : i128 => LX<16> {
        forward: i128_to_lx16,
        back:    lx16_to_i128,
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
        i008::I008I128, i016::I016I128, i032::I032I128, i064::I064I128, u008::U008I128,
        u016::U016I128, u032::U032I128, u064::U064I128, u128::U128I128,
    };
    use crate::extended::Extended;
    use crate::prop::conn as conn_laws;
    use proptest::prelude::*;

    #[test]
    fn i064i128_extends_to_one_above() {
        assert_eq!(
            crate::conn::ceil(&I064I128, Extended::PosInf),
            (i64::MAX as i128) + 1
        );
        assert_eq!(crate::conn::ceil(&I064I128, Extended::NegInf), i128::MIN);
    }

    #[test]
    fn u064i128_extends_to_one_above() {
        assert_eq!(
            crate::conn::ceil(&U064I128, Extended::PosInf),
            (u64::MAX as i128) + 1
        );
        assert_eq!(crate::conn::ceil(&U064I128, Extended::NegInf), i128::MIN);
    }

    #[test]
    fn u128i128_neg_and_high() {
        assert_eq!(crate::conn::lower(&U128I128, -1), 0_u128);
        assert_eq!(crate::conn::lower(&U128I128, i128::MIN), 0_u128);
        assert_eq!(crate::conn::floor(&U128I128, u128::MAX), i128::MAX);
        assert_eq!(
            crate::conn::floor(&U128I128, crate::conn::lower(&U128I128, 50)),
            50
        );
        assert_eq!(
            crate::conn::floor(&U128I128, crate::conn::lower(&U128I128, i128::MAX)),
            i128::MAX
        );
    }

    // ── NonZero signed narrowing (N128N###) spot + property ──────

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
    fn arb_nz_i128() -> impl Strategy<Value = NonZeroI128> {
        any::<i128>().prop_filter_map("non-zero i128", NonZeroI128::new)
    }

    proptest! {
        #[test]
        fn n128n008_galois_l(a in arb_nz_i128(), b in arb_nz_i8()) {
            prop_assert!(conn_laws::galois_l(&N128N008.conn_l(), a, b));
        }
        #[test]
        fn n128n016_galois_l(a in arb_nz_i128(), b in arb_nz_i16()) {
            prop_assert!(conn_laws::galois_l(&N128N016.conn_l(), a, b));
        }
        #[test]
        fn n128n032_galois_l(a in arb_nz_i128(), b in arb_nz_i32()) {
            prop_assert!(conn_laws::galois_l(&N128N032.conn_l(), a, b));
        }
        #[test]
        fn n128n064_galois_l(a in arb_nz_i128(), b in arb_nz_i64()) {
            prop_assert!(conn_laws::galois_l(&N128N064.conn_l(), a, b));
        }
    }

    fn arb_byte16() -> impl Strategy<Value = B2<16>> {
        prop_oneof![Just([0; 16]), Just([0xFF; 16]), any::<[u8; 16]>()].prop_map(B2)
    }

    fn arb_lebyte16() -> impl Strategy<Value = L2<16>> {
        prop_oneof![Just([0; 16]), Just([0xFF; 16]), any::<[u8; 16]>()].prop_map(L2)
    }

    proptest! {
        #[test]
        fn i128_b2_iso_roundtrip_l(a in prop_oneof![Just(i128::MIN), Just(0i128), Just(i128::MAX), any::<i128>()]) {
            prop_assert!(conn_laws::iso_roundtrip_l(&I128BE16.conn_l(), a));
        }
        #[test]
        fn i128_b2_roundtrip_ceil(b in arb_byte16()) {
            prop_assert!(conn_laws::roundtrip_ceil(&I128BE16.conn_l(), b));
        }
        #[test]
        fn i128_b2_galois_l(a in any::<i128>(), b in arb_byte16()) {
            prop_assert!(conn_laws::galois_l(&I128BE16.conn_l(), a, b));
        }
        #[test]
        fn i128_b2_galois_r(a in any::<i128>(), b in arb_byte16()) {
            prop_assert!(conn_laws::galois_r(&I128BE16.conn_r(), a, b));
        }
        #[test]
        fn i128_b2_floor_le_ceil(a in any::<i128>()) {
            prop_assert!(conn_laws::floor_le_ceil(&I128BE16, a));
        }
        #[test]
        fn i128_b2_order_preserving(a in any::<i128>(), b in any::<i128>()) {
            prop_assert_eq!(a.cmp(&b), crate::conn::ceil(&I128BE16, a).cmp(&crate::conn::ceil(&I128BE16, b)));
        }

        #[test]
        fn i128_l2_iso_roundtrip_l(a in prop_oneof![Just(i128::MIN), Just(0i128), Just(i128::MAX), any::<i128>()]) {
            prop_assert!(conn_laws::iso_roundtrip_l(&I128LE16.conn_l(), a));
        }
        #[test]
        fn i128_l2_roundtrip_ceil(b in arb_lebyte16()) {
            prop_assert!(conn_laws::roundtrip_ceil(&I128LE16.conn_l(), b));
        }
        #[test]
        fn i128_l2_galois_l(a in any::<i128>(), b in arb_lebyte16()) {
            prop_assert!(conn_laws::galois_l(&I128LE16.conn_l(), a, b));
        }
        #[test]
        fn i128_l2_galois_r(a in any::<i128>(), b in arb_lebyte16()) {
            prop_assert!(conn_laws::galois_r(&I128LE16.conn_r(), a, b));
        }
        #[test]
        fn i128_l2_floor_le_ceil(a in any::<i128>()) {
            prop_assert!(conn_laws::floor_le_ceil(&I128LE16, a));
        }
        #[test]
        fn i128_l2_order_preserving(a in any::<i128>(), b in any::<i128>()) {
            prop_assert_eq!(a.cmp(&b), crate::conn::ceil(&I128LE16, a).cmp(&crate::conn::ceil(&I128LE16, b)));
        }
    }

    // ── LX (lex-sortable big-endian) byte-encoding tests ──────────

    fn arb_lxbyte16() -> impl Strategy<Value = LX<16>> {
        let mid = {
            let mut a = [0u8; 16];
            a[0] = 0x80;
            a
        };
        prop_oneof![
            Just([0; 16]),
            Just(mid),
            Just([0xFF; 16]),
            any::<[u8; 16]>()
        ]
        .prop_map(LX)
    }

    #[test]
    fn i128lx16_boundary_bytes() {
        let mid = {
            let mut a = [0u8; 16];
            a[0] = 0x80;
            a
        };
        assert_eq!(crate::conn::ceil(&I128LX16, i128::MIN), LX([0x00; 16]));
        assert_eq!(crate::conn::ceil(&I128LX16, 0_i128), LX(mid));
        assert_eq!(crate::conn::ceil(&I128LX16, i128::MAX), LX([0xFF; 16]));
        assert_eq!(crate::conn::upper(&I128LX16, LX([0x00; 16])), i128::MIN);
        assert_eq!(crate::conn::upper(&I128LX16, LX(mid)), 0_i128);
        assert_eq!(crate::conn::upper(&I128LX16, LX([0xFF; 16])), i128::MAX);
    }

    proptest! {
        #[test]
        fn i128_lx_iso_roundtrip_l(
            a in prop_oneof![Just(i128::MIN), Just(0i128), Just(i128::MAX), any::<i128>()]
        ) {
            prop_assert!(conn_laws::iso_roundtrip_l(&I128LX16.conn_l(), a));
        }
        #[test]
        fn i128_lx_roundtrip_ceil(b in arb_lxbyte16()) {
            prop_assert!(conn_laws::roundtrip_ceil(&I128LX16.conn_l(), b));
        }
        #[test]
        fn i128_lx_galois_l(a in any::<i128>(), b in arb_lxbyte16()) {
            prop_assert!(conn_laws::galois_l(&I128LX16.conn_l(), a, b));
        }
        #[test]
        fn i128_lx_galois_r(a in any::<i128>(), b in arb_lxbyte16()) {
            prop_assert!(conn_laws::galois_r(&I128LX16.conn_r(), a, b));
        }
        #[test]
        fn i128_lx_floor_le_ceil(a in any::<i128>()) {
            prop_assert!(conn_laws::floor_le_ceil(&I128LX16, a));
        }
        #[test]
        fn i128_lx_signed_cmp_matches_raw_byte_cmp(a in any::<i128>(), b in any::<i128>()) {
            let ka = crate::conn::ceil(&I128LX16, a).0;
            let kb = crate::conn::ceil(&I128LX16, b).0;
            prop_assert_eq!(a.cmp(&b), ka.cmp(&kb));
        }
    }
}
