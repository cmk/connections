//! `bool` → byte projections.
//!
//! Houses `BOOLBE01` and `BOOLLE01`, the one-sided projections from
//! `bool` into a single big- or little-endian byte. Both are
//! left-Galois rather than full isos: any non-zero byte projects back
//! to `true`, so `[2..=0xFF]` collapses on the back direction.

#[allow(unused_imports)]
use crate::core::LE;

const fn bool_to_be01(x: bool) -> [u8; 1] {
    [x as u8]
}

/// Lossy back: any non-zero byte is `true`, only `[0]` is `false`.
/// This makes `BOOLBE01` a one-sided `conn_l!` (not an iso) — the
/// `roundtrip_ceil` law fails for bytes `0x02..=0xFF` (they all
/// collapse to `true → [1]`). Galois L still holds.
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
    /// use connections::core::bool::BOOLBE01;
    ///
    /// assert_eq!(connections::conn::ceil(&BOOLBE01, false), [0]);
    /// assert_eq!(connections::conn::ceil(&BOOLBE01, true),  [1]);
    /// assert_eq!(connections::conn::upper(&BOOLBE01, [0]),   false);
    /// assert_eq!(connections::conn::upper(&BOOLBE01, [1]),   true);
    /// // Non-canonical encodings collapse to true:
    /// assert_eq!(connections::conn::upper(&BOOLBE01, [0xFF]), true);
    /// ```
    pub BOOLBE01 : bool => [u8; 1] {
        ceil:  bool_to_be01,
        inner: be01_to_bool,
    }
}

const fn bool_to_le01(x: bool) -> LE<1> {
    LE([x as u8])
}

/// Lossy back: any non-zero byte is `true`, only `LE([0])` is `false`.
/// Mirrors [`BOOLBE01`] under the `LE<1>` wrapper.
const fn le01_to_bool(b: LE<1>) -> bool {
    b.0[0] != 0
}

crate::conn_l! {
    /// `bool → LE<1>` — one-sided little-endian projection.
    ///
    /// Forward emits `LE([0])` for `false` and `LE([1])` for `true`.
    /// Back (`inner`) treats any non-zero byte as `true`, which means
    /// the byte side is non-injective: this Conn is **not** a full iso.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::core::{LE, bool::BOOLLE01};
    ///
    /// assert_eq!(connections::conn::ceil(&BOOLLE01, false), LE([0]));
    /// assert_eq!(connections::conn::ceil(&BOOLLE01, true),  LE([1]));
    /// assert_eq!(connections::conn::upper(&BOOLLE01, LE([0])), false);
    /// assert_eq!(connections::conn::upper(&BOOLLE01, LE([1])), true);
    /// // Non-canonical encodings collapse to true:
    /// assert_eq!(connections::conn::upper(&BOOLLE01, LE([0xFF])), true);
    /// ```
    pub BOOLLE01 : bool => LE<1> {
        ceil:  bool_to_le01,
        inner: le01_to_bool,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[allow(unused_imports)]
    use crate::conn::ConnL;
    use crate::prop::conn as conn_laws;
    use proptest::prelude::*;

    #[test]
    fn bool_le_upper_is_greatest_preimage_with_ceil_below_byte() {
        for byte in 0..=u8::MAX {
            let b = LE([byte]);
            let upper = crate::conn::upper(&BOOLLE01, b);
            let greatest_preimage = crate::conn::ceil(&BOOLLE01, true) <= b;

            assert_eq!(upper, byte != 0);
            assert_eq!(upper, greatest_preimage);
            assert!(crate::conn::ceil(&BOOLLE01, upper) <= b);

            if !upper {
                assert!(crate::conn::ceil(&BOOLLE01, true) > b);
            }
        }
    }

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
        fn bool_be_galois_l(a: bool, b in arb_byte1()) {
            prop_assert!(conn_laws::galois_l(&BOOLBE01, a, b));
        }

        #[test]
        fn bool_be_host_roundtrip_l(a: bool) {
            prop_assert!(conn_laws::iso_roundtrip_l(&BOOLBE01, a));
        }

        #[test]
        fn bool_be_order_preserving(a: bool, b: bool) {
            prop_assert_eq!(a.cmp(&b), crate::conn::ceil(&BOOLBE01, a).cmp(&crate::conn::ceil(&BOOLBE01, b)));
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
            prop_assert_eq!(crate::conn::upper(&BOOLLE01, b), true);
            prop_assert_eq!(crate::conn::ceil(&BOOLLE01, crate::conn::upper(&BOOLLE01, b)), LE([1]));
            prop_assert!(conn_laws::kernel_l(&BOOLLE01, b));
            prop_assert!(!conn_laws::roundtrip_ceil(&BOOLLE01, b));
        }

        #[test]
        fn bool_le_order_preserving(a: bool, b: bool) {
            prop_assert_eq!(a.cmp(&b), crate::conn::ceil(&BOOLLE01, a).cmp(&crate::conn::ceil(&BOOLLE01, b)));
        }
    }
}
