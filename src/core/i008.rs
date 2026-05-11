//! `i8`-source std-int Conns plus the `i8 ↔ NonZeroI8` adjoint and
//! two's-complement big- / little-endian byte encodings.
//!
//! Q-format / cross-crate isos to `FixedI8<F>` live next door in
//! [`crate::fixed::i008`].

#[allow(unused_imports)]
use crate::core::{B2, L2};
use crate::core::{ext_int, int_uint, nz_int_ext};
use ::core::num::NonZeroI8;

// ── §1 std-int Conns sourced from `i8` ────────────────────────────

ext_int!(I008I016, i8, i16);
ext_int!(I008I032, i8, i32);
ext_int!(I008I064, i8, i64);
ext_int!(I008I128, i8, i128);

int_uint!(I008U008, i8, u8);
int_uint!(I008U016, i8, u16);
int_uint!(I008U032, i8, u32);
int_uint!(I008U064, i8, u64);
int_uint!(I008U128, i8, u128);

// ── §3 i8 ↔ NonZeroI8 ─────────────────────────────────────────────

nz_int_ext!(I008N008, i8, NonZeroI8);

// ── Two's-complement big-endian byte encodings ────────────────────

const fn i8_to_be01(x: i8) -> B2<1> {
    B2([x as u8])
}
const fn be01_to_i8(b: B2<1>) -> i8 {
    b.0[0] as i8
}

crate::iso! {
    /// `i8 ↔ B2<1>` — raw two's-complement big-endian iso.
    ///
    /// The wrapper orders raw two's-complement bytes by decoded signed
    /// value, so the raw byte map remains lawful as an iso.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::conn::{ConnL, ConnR};
    /// use connections::B2;
    /// use connections::core::i008::I008BE01;
    ///
    /// assert_eq!(I008BE01.ceil(i8::MIN), B2([0x80]));
    /// assert_eq!(I008BE01.ceil(0_i8),    B2([0x00]));
    /// assert_eq!(I008BE01.ceil(i8::MAX), B2([0x7F]));
    /// assert_eq!(I008BE01.upper(B2([0x80])), i8::MIN);
    /// ```
    pub I008BE01 : i8 => B2<1> {
        forward: i8_to_be01,
        back:    be01_to_i8,
    }
}

// ── Two's-complement little-endian byte encodings ─────────────────

const fn i8_to_le01(x: i8) -> L2<1> {
    L2([x as u8])
}
const fn le01_to_i8(b: L2<1>) -> i8 {
    b.0[0] as i8
}

crate::iso! {
    /// `i8 ↔ L2<1>` — raw two's-complement little-endian iso.
    pub I008LE01 : i8 => L2<1> {
        forward: i8_to_le01,
        back:    le01_to_i8,
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
        i016::I016I008, i032::I032I008, i064::I064I008, i128::I128I008, u008::U008I008,
        u016::U016I008, u032::U032I008, u064::U064I008, u128::U128I008,
    };
    use crate::prop::conn as conn_laws;
    use proptest::prelude::*;

    // ── §1 std-int spot checks ─────────────────────────────────────

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
            assert_eq!(I016I008.ceil(I016I008.upper(b)), b);
            assert_eq!(I032I008.ceil(I032I008.upper(b)), b);
            assert_eq!(I064I008.ceil(I064I008.upper(b)), b);
            assert_eq!(I128I008.ceil(I128I008.upper(b)), b);
        }
    }

    #[test]
    fn i_to_i_inner_fine_max_fixup() {
        assert_eq!(I016I008.upper(i8::MAX), i16::MAX);
        assert_eq!(I032I008.upper(i8::MAX), i32::MAX);
        assert_eq!(I064I008.upper(i8::MAX), i64::MAX);
        assert_eq!(I128I008.upper(i8::MAX), i128::MAX);
        assert_eq!(I016I008.upper(126), 126_i16);
        assert_eq!(I016I008.upper(i8::MIN), i8::MIN as i16);
    }

    #[test]
    fn u_to_i_neg_collapse() {
        assert_eq!(U008I008.lower(-1), 0_u8);
        assert_eq!(U008I008.lower(i8::MIN), 0_u8);
        assert_eq!(U016I008.lower(-1), 0_u16);
        assert_eq!(U128I008.lower(-50), 0_u128);
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
            assert_eq!(U008I008.floor(U008I008.lower(b)), b);
            assert_eq!(U016I008.floor(U016I008.lower(b)), b);
            assert_eq!(U128I008.floor(U128I008.lower(b)), b);
        }
    }

    // ── §3 i8 ↔ NonZeroI8 spot checks ──────────────────────────────

    #[test]
    fn i008n008_floor_ceil_split_at_zero() {
        // Asymmetric-adjoint at zero: floor lands on the largest
        // NonZero ≤ 0 (-1); ceil lands on the smallest NonZero ≥ 0 (+1).
        assert_eq!(I008N008.floor(0_i8), NonZeroI8::new(-1).unwrap());
        assert_eq!(I008N008.ceil(0_i8), NonZeroI8::new(1).unwrap());
    }

    #[test]
    fn i008n008_finite_nonzero_round_trip() {
        for &v in &[i8::MIN, -50, -1, 1, 50, i8::MAX] {
            let nz = NonZeroI8::new(v).unwrap();
            assert_eq!(I008N008.ceil(v), nz);
            assert_eq!(I008N008.floor(v), nz);
        }
    }

    #[test]
    fn i008n008_inner_is_total_embedding() {
        for &v in &[i8::MIN, -1, 1, i8::MAX] {
            let nz = NonZeroI8::new(v).unwrap();
            assert_eq!(I008N008.upper(nz), v);
        }
    }

    fn arb_nz_i8() -> impl Strategy<Value = NonZeroI8> {
        any::<i8>().prop_filter_map("non-zero i8", NonZeroI8::new)
    }

    proptest! {
        // I008N008: source is i8, target is NonZeroI8. Both Galois
        // laws hold — the asymmetric floor/ceil at v=0 brackets the
        // target's puncture between -1 and +1.
        #[test]
        fn i008n008_galois_l(a in any::<i8>(), b in arb_nz_i8()) {
            prop_assert!(conn_laws::galois_l(&I008N008.conn_l(), a, b));
        }

        #[test]
        fn i008n008_galois_r(a in any::<i8>(), b in arb_nz_i8()) {
            prop_assert!(conn_laws::galois_r(&I008N008.conn_r(), a, b));
        }

        #[test]
        fn i008n008_inner_then_ceil_recovers_nonzero(nz in arb_nz_i8()) {
            prop_assert_eq!(I008N008.ceil(I008N008.upper(nz)), nz);
            prop_assert_eq!(I008N008.floor(I008N008.upper(nz)), nz);
        }
    }

    // ── B2 / L2 byte-encoding tests ────────────────────────────────

    fn arb_byte1() -> impl Strategy<Value = B2<1>> {
        prop_oneof![
            Just([0; 1]),
            Just([0xFF; 1]),
            Just([0x80]),
            any::<[u8; 1]>()
        ]
        .prop_map(B2)
    }

    fn arb_lebyte1() -> impl Strategy<Value = L2<1>> {
        prop_oneof![
            Just([0; 1]),
            Just([0xFF; 1]),
            Just([0x80]),
            any::<[u8; 1]>()
        ]
        .prop_map(L2)
    }

    proptest! {
        #[test]
        fn i008_b2_iso_roundtrip_l(a in prop_oneof![Just(i8::MIN), Just(0i8), Just(i8::MAX), any::<i8>()]) {
            prop_assert!(conn_laws::iso_roundtrip_l(&I008BE01.conn_l(), a));
        }
        #[test]
        fn i008_b2_roundtrip_ceil(b in arb_byte1()) {
            prop_assert!(conn_laws::roundtrip_ceil(&I008BE01.conn_l(), b));
        }
        #[test]
        fn i008_b2_galois_l(a in any::<i8>(), b in arb_byte1()) {
            prop_assert!(conn_laws::galois_l(&I008BE01.conn_l(), a, b));
        }
        #[test]
        fn i008_b2_galois_r(a in any::<i8>(), b in arb_byte1()) {
            prop_assert!(conn_laws::galois_r(&I008BE01.conn_r(), a, b));
        }
        #[test]
        fn i008_b2_floor_le_ceil(a in any::<i8>()) {
            prop_assert!(conn_laws::floor_le_ceil(&I008BE01, a));
        }
        #[test]
        fn i008_b2_order_preserving(a in any::<i8>(), b in any::<i8>()) {
            prop_assert_eq!(a.cmp(&b), I008BE01.ceil(a).cmp(&I008BE01.ceil(b)));
        }

        #[test]
        fn i008_l2_iso_roundtrip_l(a in prop_oneof![Just(i8::MIN), Just(0i8), Just(i8::MAX), any::<i8>()]) {
            prop_assert!(conn_laws::iso_roundtrip_l(&I008LE01.conn_l(), a));
        }

        #[test]
        fn i008_l2_roundtrip_ceil(b in arb_lebyte1()) {
            prop_assert!(conn_laws::roundtrip_ceil(&I008LE01.conn_l(), b));
        }

        #[test]
        fn i008_l2_galois_l(a in any::<i8>(), b in arb_lebyte1()) {
            prop_assert!(conn_laws::galois_l(&I008LE01.conn_l(), a, b));
        }

        #[test]
        fn i008_l2_galois_r(a in any::<i8>(), b in arb_lebyte1()) {
            prop_assert!(conn_laws::galois_r(&I008LE01.conn_r(), a, b));
        }

        #[test]
        fn i008_l2_floor_le_ceil(a in any::<i8>()) {
            prop_assert!(conn_laws::floor_le_ceil(&I008LE01, a));
        }

        #[test]
        fn i008_l2_order_preserving(a in any::<i8>(), b in any::<i8>()) {
            prop_assert_eq!(a.cmp(&b), I008LE01.ceil(a).cmp(&I008LE01.ceil(b)));
        }
    }
}
