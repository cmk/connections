//! Kani harnesses for [`crate::iso!`] — the cross-crate `Q<frac> ↔
//! intN` lossless isos. These are degenerate Galois connections
//! (`ceil = floor`) so both L and R laws must hold, and additionally
//! both round-trips must be exact (`inner ∘ ceil = id_A`,
//! `ceil ∘ inner = id_B`).

use crate::conn::{ConnL, ConnR};
use crate::prop::conn as conn_laws;
use ::fixed::types::extra::{U0, U7, U15, U31, U63, U127};
use ::fixed::{FixedI8, FixedI16, FixedI32, FixedI64, FixedI128};
use ::fixed::{FixedU8, FixedU16, FixedU32, FixedU64, FixedU128};

/// Emit iso harnesses (signed primitive form) for one `iso!` Conn.
///
/// `$FX` is the `fixed`-crate Q.0 wrapper (e.g. `FixedI8<U0>`); `$P`
/// is the std primitive (e.g. `i8`). Both endpoints are at the same
/// bit-width so the iso round-trips both ways exactly.
macro_rules! prove_iso {
    ($mod_name:ident, $CONN:path, $FX:ty, $P:ty) => {
        mod $mod_name {
            use super::*;

            #[kani::proof]
            fn galois_l() {
                let bits: $P = kani::any();
                let a = <$FX>::from_bits(bits);
                let b: $P = kani::any();
                assert!(conn_laws::galois_l(&$CONN.conn_l(), a, b));
            }

            #[kani::proof]
            fn galois_r() {
                let bits: $P = kani::any();
                let a = <$FX>::from_bits(bits);
                let b: $P = kani::any();
                assert!(conn_laws::galois_r(&$CONN.conn_r(), a, b));
            }

            // Both directions of the iso are exact.
            #[kani::proof]
            fn iso_roundtrip_l() {
                let bits: $P = kani::any();
                let a = <$FX>::from_bits(bits);
                assert!(conn_laws::iso_roundtrip_l(&$CONN.conn_l(), a));
            }

            #[kani::proof]
            fn roundtrip_ceil() {
                let b: $P = kani::any();
                assert!(conn_laws::roundtrip_ceil(&$CONN.conn_l(), b));
            }

            #[kani::proof]
            fn idempotent_l() {
                let bits: $P = kani::any();
                let a = <$FX>::from_bits(bits);
                assert!(conn_laws::idempotent_l(&$CONN.conn_l(), a));
            }
        }
    };
}

// ── Signed isos ─────────────────────────────────────────────────────
use crate::fixed::i008 as fi008;
use crate::fixed::i016 as fi016;
use crate::fixed::i032 as fi032;
use crate::fixed::i064 as fi064;
use crate::fixed::i128 as fi128;

prove_iso!(q000i008, fi008::Q000I008, FixedI8<U0>, i8);
prove_iso!(q000i016, fi016::Q000I016, FixedI16<U0>, i16);
prove_iso!(q000i032, fi032::Q000I032, FixedI32<U0>, i32);
prove_iso!(q000i064, fi064::Q000I064, FixedI64<U0>, i64);
prove_iso!(q000i128, fi128::Q000I128, FixedI128<U0>, i128);
prove_iso!(q007i008, fi008::Q007I008, FixedI8<U7>, i8);
prove_iso!(q015i016, fi016::Q015I016, FixedI16<U15>, i16);
prove_iso!(q031i032, fi032::Q031I032, FixedI32<U31>, i32);
prove_iso!(q063i064, fi064::Q063I064, FixedI64<U63>, i64);
prove_iso!(q127i128, fi128::Q127I128, FixedI128<U127>, i128);

// ── Unsigned isos ───────────────────────────────────────────────────
use crate::fixed::u008 as fu008;
use crate::fixed::u016 as fu016;
use crate::fixed::u032 as fu032;
use crate::fixed::u064 as fu064;
use crate::fixed::u128 as fu128;

prove_iso!(q000u008, fu008::Q000U008, FixedU8<U0>, u8);
prove_iso!(q000u016, fu016::Q000U016, FixedU16<U0>, u16);
prove_iso!(q000u032, fu032::Q000U032, FixedU32<U0>, u32);
prove_iso!(q000u064, fu064::Q000U064, FixedU64<U0>, u64);
prove_iso!(q000u128, fu128::Q000U128, FixedU128<U0>, u128);
