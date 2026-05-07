//! Kani harnesses for [`crate::byte::four`] — 4-byte sortable byte-encoding isos.
//!
//! `U032OBYT`, `I032OBYT`, `F032OBYT`. T0 (full domain). The
//! `order_preserving` predicate uses two symbolic inputs — 64
//! symbolic bits — comparable to the `F064F032` walk-step proofs in
//! `float_walk.rs`. Expected to verify in minutes; if CBMC stalls,
//! drop to T1 by adding `kani::assume(a.abs() < 1024)` style bounds
//! and document in Plan 47 §Review.

use crate::conn::{ConnL, ConnR};
use crate::prop::conn as conn_laws;

macro_rules! prove_iso_obyt {
    ($mod_name:ident, $CONN:path, $T:ty) => {
        mod $mod_name {
            use super::*;

            #[kani::proof]
            fn galois_l() {
                let a: $T = kani::any();
                let b: [u8; 4] = kani::any();
                assert!(conn_laws::galois_l(&$CONN.conn_l(), a, b));
            }

            #[kani::proof]
            fn galois_r() {
                let a: $T = kani::any();
                let b: [u8; 4] = kani::any();
                assert!(conn_laws::galois_r(&$CONN.conn_r(), a, b));
            }

            #[kani::proof]
            fn iso_roundtrip_l() {
                let a: $T = kani::any();
                assert!(conn_laws::iso_roundtrip_l(&$CONN.conn_l(), a));
            }

            #[kani::proof]
            fn roundtrip_ceil() {
                let b: [u8; 4] = kani::any();
                assert!(conn_laws::roundtrip_ceil(&$CONN.conn_l(), b));
            }

            #[kani::proof]
            fn floor_le_ceil() {
                let a: $T = kani::any();
                assert!(conn_laws::floor_le_ceil(&$CONN, a));
            }

            #[kani::proof]
            fn order_preserving() {
                let a: $T = kani::any();
                let b: $T = kani::any();
                let host_ord = a.cmp(&b);
                let byte_ord = $CONN.ceil(a).cmp(&$CONN.ceil(b));
                assert!(host_ord == byte_ord);
            }
        }
    };
}

prove_iso_obyt!(u032_obyt, crate::byte::U032OBYT, u32);
prove_iso_obyt!(i032_obyt, crate::byte::I032OBYT, i32);

// ── F032OBYT — host comparison must use IEEE 754 totalOrder ─────────
//
// Plain `f32::cmp` doesn't exist (PartialOrd only); the order we want
// the byte encoding to match is `f32::total_cmp`. We can't reuse
// `prove_iso_obyt!` for this (the macro hardcodes `.cmp(&_)`).
// Iso-roundtrip on `f32` also can't use `iso_roundtrip_l` directly
// because the predicate uses `==` which fails on NaN; check on bits.

mod f032_obyt {
    use super::*;
    use crate::byte::F032OBYT;

    // Note: `conn_laws::galois_l/r` require `A: Eq`, which `f32` does not
    // implement. The classical Galois law `(ceil(a) <= b) == (a <= upper(b))`
    // also fails for IEEE floats whenever either side compares against a NaN
    // (NaN is unordered with `<=`, breaking the bool-equality of the two
    // sides). The order law that DOES hold is over `f32::total_cmp`, which is
    // verified by `order_preserving_total` below. The inline `galois_*_total`
    // harnesses here exercise the totalOrder analog of Galois.

    /// Total-order Galois L: `cmp(ceil(a), b) ≤ Equal ⟺ total_cmp(a, upper(b)) ≤ Equal`.
    #[kani::proof]
    fn galois_l_total() {
        let a_bits: u32 = kani::any();
        let b: [u8; 4] = kani::any();
        let a = f32::from_bits(a_bits);
        let c = F032OBYT.conn_l();
        let lhs = c.ceil(a) <= b; // [u8;4] is totally ordered; this is fine.
        let rhs = a.total_cmp(&c.upper(b)).is_le();
        assert!(lhs == rhs);
    }

    /// Total-order Galois R analog.
    #[kani::proof]
    fn galois_r_total() {
        let a_bits: u32 = kani::any();
        let b: [u8; 4] = kani::any();
        let a = f32::from_bits(a_bits);
        let c = F032OBYT.conn_r();
        let lhs = c.lower(b).total_cmp(&a).is_le();
        let rhs = b <= c.floor(a);
        assert!(lhs == rhs);
    }

    #[kani::proof]
    fn roundtrip_bits() {
        // ceil ∘ inner = id on bytes, AND inner ∘ ceil preserves bit pattern
        // (NaN payloads survive). Test on bits to dodge NaN!=NaN.
        let bits: u32 = kani::any();
        let a = f32::from_bits(bits);
        assert!(F032OBYT.upper(F032OBYT.ceil(a)).to_bits() == bits);
    }

    #[kani::proof]
    fn roundtrip_ceil() {
        let b: [u8; 4] = kani::any();
        assert!(conn_laws::roundtrip_ceil(&F032OBYT.conn_l(), b));
    }

    #[kani::proof]
    fn order_preserving_total() {
        // Match against IEEE 754 totalOrder, the spec the byte encoding implements.
        let a_bits: u32 = kani::any();
        let b_bits: u32 = kani::any();
        let a = f32::from_bits(a_bits);
        let b = f32::from_bits(b_bits);
        let host_ord = a.total_cmp(&b);
        let byte_ord = F032OBYT.ceil(a).cmp(&F032OBYT.ceil(b));
        assert!(host_ord == byte_ord);
    }
}
