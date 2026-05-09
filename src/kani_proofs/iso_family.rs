//! Kani harnesses for [`crate::iso!`] — the cross-crate `intN ↔
//! Q<frac=0>` lossless isos. These are degenerate Galois connections
//! (`ceil = floor`) so both L and R laws must hold, and additionally
//! both round-trips must be exact (`inner ∘ ceil = id_A`,
//! `ceil ∘ inner = id_B`).

use crate::conn::{ConnL, ConnR};
use crate::prop::conn as conn_laws;
use ::fixed::types::extra::U0;
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
                let a: $P = kani::any();
                let bits: $P = kani::any();
                let b = <$FX>::from_bits(bits);
                assert!(conn_laws::galois_l(&$CONN.conn_l(), a, b));
            }

            #[kani::proof]
            fn galois_r() {
                let a: $P = kani::any();
                let bits: $P = kani::any();
                let b = <$FX>::from_bits(bits);
                assert!(conn_laws::galois_r(&$CONN.conn_r(), a, b));
            }

            // Both directions of the iso are exact.
            #[kani::proof]
            fn iso_roundtrip_l() {
                let a: $P = kani::any();
                assert!(conn_laws::iso_roundtrip_l(&$CONN.conn_l(), a));
            }

            #[kani::proof]
            fn roundtrip_ceil() {
                let bits: $P = kani::any();
                let b = <$FX>::from_bits(bits);
                assert!(conn_laws::roundtrip_ceil(&$CONN.conn_l(), b));
            }

            #[kani::proof]
            fn idempotent_l() {
                let a: $P = kani::any();
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

prove_iso!(i008q000, fi008::I008Q000, FixedI8<U0>, i8);
prove_iso!(i016q000, fi016::I016Q000, FixedI16<U0>, i16);
prove_iso!(i032q000, fi032::I032Q000, FixedI32<U0>, i32);
prove_iso!(i064q000, fi064::I064Q000, FixedI64<U0>, i64);
prove_iso!(i128q000, fi128::I128Q000, FixedI128<U0>, i128);

// ── Unsigned isos ───────────────────────────────────────────────────
use crate::fixed::u008 as fu008;
use crate::fixed::u016 as fu016;
use crate::fixed::u032 as fu032;
use crate::fixed::u064 as fu064;
use crate::fixed::u128 as fu128;

prove_iso!(u008q000, fu008::U008Q000, FixedU8<U0>, u8);
prove_iso!(u016q000, fu016::U016Q000, FixedU16<U0>, u16);
prove_iso!(u032q000, fu032::U032Q000, FixedU32<U0>, u32);
prove_iso!(u064q000, fu064::U064Q000, FixedU64<U0>, u64);
prove_iso!(u128q000, fu128::U128Q000, FixedU128<U0>, u128);
