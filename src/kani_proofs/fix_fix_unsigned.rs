//! Kani harnesses for `fix_fix_uN!` — the per-host-width unsigned
//! Q-format ladder. Same shape as the signed siblings (left-Galois
//! only), with the unsigned bit pattern flowing through `from_bits`.
//!
//! Coverage strategy: full ladder for u8 (28 pairs) and u16 (28 pairs);
//! boundary pairs for u32 / u64 / u128.

use crate::conn::ConnL;
use crate::prop::conn as conn_laws;
use ::fixed::FixedU8;
use ::fixed::FixedU16;
use ::fixed::FixedU32;
use ::fixed::FixedU64;
use ::fixed::FixedU128;
use ::fixed::types::extra::*;

macro_rules! prove_fix_fix_u {
    ($mod_name:ident, $CONN:path, $FX_FINE:ty, $FX_COARSE:ty, $BITS:ty) => {
        mod $mod_name {
            use super::*;

            #[kani::proof]
            fn galois_l() {
                let fbits: $BITS = kani::any();
                let cbits: $BITS = kani::any();
                let a = <$FX_FINE>::from_bits(fbits);
                let b = <$FX_COARSE>::from_bits(cbits);
                assert!(conn_laws::galois_l(&$CONN.conn_l(), a, b));
            }

            // `prop::conn::monotone_l` returns `true` vacuously for
            // `a1 > a2`; unconstrained `kani::any()` inputs are sound.
            // Same convention as the signed Q-format harnesses.
            #[kani::proof]
            fn monotone_l() {
                let b1: $BITS = kani::any();
                let b2: $BITS = kani::any();
                let a1 = <$FX_FINE>::from_bits(b1);
                let a2 = <$FX_FINE>::from_bits(b2);
                assert!(conn_laws::monotone_l(&$CONN.conn_l(), a1, a2));
            }

            #[kani::proof]
            fn closure_l() {
                let bits: $BITS = kani::any();
                let a = <$FX_FINE>::from_bits(bits);
                assert!(conn_laws::closure_l(&$CONN.conn_l(), a));
            }

            #[kani::proof]
            fn kernel_l() {
                let bits: $BITS = kani::any();
                let b = <$FX_COARSE>::from_bits(bits);
                assert!(conn_laws::kernel_l(&$CONN.conn_l(), b));
            }

            #[kani::proof]
            fn idempotent_l() {
                let bits: $BITS = kani::any();
                let a = <$FX_FINE>::from_bits(bits);
                assert!(conn_laws::idempotent_l(&$CONN.conn_l(), a));
            }
        }
    };
}

// ── u8-backed (full ladder, 28 Conns × 5 props = 140 proofs) ────────
use crate::fixed::u8 as fu8;

prove_fix_fix_u!(u8_q001q000, fu8::Q001Q000, FixedU8<U1>, FixedU8<U0>, u8);
prove_fix_fix_u!(u8_q002q000, fu8::Q002Q000, FixedU8<U2>, FixedU8<U0>, u8);
prove_fix_fix_u!(u8_q003q000, fu8::Q003Q000, FixedU8<U3>, FixedU8<U0>, u8);
prove_fix_fix_u!(u8_q004q000, fu8::Q004Q000, FixedU8<U4>, FixedU8<U0>, u8);
prove_fix_fix_u!(u8_q006q000, fu8::Q006Q000, FixedU8<U6>, FixedU8<U0>, u8);
prove_fix_fix_u!(u8_q007q000, fu8::Q007Q000, FixedU8<U7>, FixedU8<U0>, u8);
prove_fix_fix_u!(u8_q008q000, fu8::Q008Q000, FixedU8<U8>, FixedU8<U0>, u8);
prove_fix_fix_u!(u8_q002q001, fu8::Q002Q001, FixedU8<U2>, FixedU8<U1>, u8);
prove_fix_fix_u!(u8_q003q001, fu8::Q003Q001, FixedU8<U3>, FixedU8<U1>, u8);
prove_fix_fix_u!(u8_q004q001, fu8::Q004Q001, FixedU8<U4>, FixedU8<U1>, u8);
prove_fix_fix_u!(u8_q006q001, fu8::Q006Q001, FixedU8<U6>, FixedU8<U1>, u8);
prove_fix_fix_u!(u8_q007q001, fu8::Q007Q001, FixedU8<U7>, FixedU8<U1>, u8);
prove_fix_fix_u!(u8_q008q001, fu8::Q008Q001, FixedU8<U8>, FixedU8<U1>, u8);
prove_fix_fix_u!(u8_q003q002, fu8::Q003Q002, FixedU8<U3>, FixedU8<U2>, u8);
prove_fix_fix_u!(u8_q004q002, fu8::Q004Q002, FixedU8<U4>, FixedU8<U2>, u8);
prove_fix_fix_u!(u8_q006q002, fu8::Q006Q002, FixedU8<U6>, FixedU8<U2>, u8);
prove_fix_fix_u!(u8_q007q002, fu8::Q007Q002, FixedU8<U7>, FixedU8<U2>, u8);
prove_fix_fix_u!(u8_q008q002, fu8::Q008Q002, FixedU8<U8>, FixedU8<U2>, u8);
prove_fix_fix_u!(u8_q004q003, fu8::Q004Q003, FixedU8<U4>, FixedU8<U3>, u8);
prove_fix_fix_u!(u8_q006q003, fu8::Q006Q003, FixedU8<U6>, FixedU8<U3>, u8);
prove_fix_fix_u!(u8_q007q003, fu8::Q007Q003, FixedU8<U7>, FixedU8<U3>, u8);
prove_fix_fix_u!(u8_q008q003, fu8::Q008Q003, FixedU8<U8>, FixedU8<U3>, u8);
prove_fix_fix_u!(u8_q006q004, fu8::Q006Q004, FixedU8<U6>, FixedU8<U4>, u8);
prove_fix_fix_u!(u8_q007q004, fu8::Q007Q004, FixedU8<U7>, FixedU8<U4>, u8);
prove_fix_fix_u!(u8_q008q004, fu8::Q008Q004, FixedU8<U8>, FixedU8<U4>, u8);
prove_fix_fix_u!(u8_q007q006, fu8::Q007Q006, FixedU8<U7>, FixedU8<U6>, u8);
prove_fix_fix_u!(u8_q008q006, fu8::Q008Q006, FixedU8<U8>, FixedU8<U6>, u8);
prove_fix_fix_u!(u8_q008q007, fu8::Q008Q007, FixedU8<U8>, FixedU8<U7>, u8);

// ── u16-backed (full ladder, 28 Conns × 5 props = 140 proofs) ───────
use crate::fixed::u16 as fu16;

prove_fix_fix_u!(
    u16_q002q000,
    fu16::Q002Q000,
    FixedU16<U2>,
    FixedU16<U0>,
    u16
);
prove_fix_fix_u!(
    u16_q004q000,
    fu16::Q004Q000,
    FixedU16<U4>,
    FixedU16<U0>,
    u16
);
prove_fix_fix_u!(
    u16_q008q000,
    fu16::Q008Q000,
    FixedU16<U8>,
    FixedU16<U0>,
    u16
);
prove_fix_fix_u!(
    u16_q012q000,
    fu16::Q012Q000,
    FixedU16<U12>,
    FixedU16<U0>,
    u16
);
prove_fix_fix_u!(
    u16_q014q000,
    fu16::Q014Q000,
    FixedU16<U14>,
    FixedU16<U0>,
    u16
);
prove_fix_fix_u!(
    u16_q015q000,
    fu16::Q015Q000,
    FixedU16<U15>,
    FixedU16<U0>,
    u16
);
prove_fix_fix_u!(
    u16_q016q000,
    fu16::Q016Q000,
    FixedU16<U16>,
    FixedU16<U0>,
    u16
);
prove_fix_fix_u!(
    u16_q004q002,
    fu16::Q004Q002,
    FixedU16<U4>,
    FixedU16<U2>,
    u16
);
prove_fix_fix_u!(
    u16_q008q002,
    fu16::Q008Q002,
    FixedU16<U8>,
    FixedU16<U2>,
    u16
);
prove_fix_fix_u!(
    u16_q012q002,
    fu16::Q012Q002,
    FixedU16<U12>,
    FixedU16<U2>,
    u16
);
prove_fix_fix_u!(
    u16_q014q002,
    fu16::Q014Q002,
    FixedU16<U14>,
    FixedU16<U2>,
    u16
);
prove_fix_fix_u!(
    u16_q015q002,
    fu16::Q015Q002,
    FixedU16<U15>,
    FixedU16<U2>,
    u16
);
prove_fix_fix_u!(
    u16_q016q002,
    fu16::Q016Q002,
    FixedU16<U16>,
    FixedU16<U2>,
    u16
);
prove_fix_fix_u!(
    u16_q008q004,
    fu16::Q008Q004,
    FixedU16<U8>,
    FixedU16<U4>,
    u16
);
prove_fix_fix_u!(
    u16_q012q004,
    fu16::Q012Q004,
    FixedU16<U12>,
    FixedU16<U4>,
    u16
);
prove_fix_fix_u!(
    u16_q014q004,
    fu16::Q014Q004,
    FixedU16<U14>,
    FixedU16<U4>,
    u16
);
prove_fix_fix_u!(
    u16_q015q004,
    fu16::Q015Q004,
    FixedU16<U15>,
    FixedU16<U4>,
    u16
);
prove_fix_fix_u!(
    u16_q016q004,
    fu16::Q016Q004,
    FixedU16<U16>,
    FixedU16<U4>,
    u16
);
prove_fix_fix_u!(
    u16_q012q008,
    fu16::Q012Q008,
    FixedU16<U12>,
    FixedU16<U8>,
    u16
);
prove_fix_fix_u!(
    u16_q014q008,
    fu16::Q014Q008,
    FixedU16<U14>,
    FixedU16<U8>,
    u16
);
prove_fix_fix_u!(
    u16_q015q008,
    fu16::Q015Q008,
    FixedU16<U15>,
    FixedU16<U8>,
    u16
);
prove_fix_fix_u!(
    u16_q016q008,
    fu16::Q016Q008,
    FixedU16<U16>,
    FixedU16<U8>,
    u16
);
prove_fix_fix_u!(
    u16_q014q012,
    fu16::Q014Q012,
    FixedU16<U14>,
    FixedU16<U12>,
    u16
);
prove_fix_fix_u!(
    u16_q015q012,
    fu16::Q015Q012,
    FixedU16<U15>,
    FixedU16<U12>,
    u16
);
prove_fix_fix_u!(
    u16_q016q012,
    fu16::Q016Q012,
    FixedU16<U16>,
    FixedU16<U12>,
    u16
);
prove_fix_fix_u!(
    u16_q015q014,
    fu16::Q015Q014,
    FixedU16<U15>,
    FixedU16<U14>,
    u16
);
prove_fix_fix_u!(
    u16_q016q014,
    fu16::Q016Q014,
    FixedU16<U16>,
    FixedU16<U14>,
    u16
);
prove_fix_fix_u!(
    u16_q016q015,
    fu16::Q016Q015,
    FixedU16<U16>,
    FixedU16<U15>,
    u16
);

// ── u32-backed (boundary pairs only) ────────────────────────────────
use crate::fixed::u32 as fu32;

prove_fix_fix_u!(
    u32_q032q000,
    fu32::Q032Q000,
    FixedU32<U32>,
    FixedU32<U0>,
    u32
);
prove_fix_fix_u!(
    u32_q032q016,
    fu32::Q032Q016,
    FixedU32<U32>,
    FixedU32<U16>,
    u32
);
prove_fix_fix_u!(
    u32_q032q031,
    fu32::Q032Q031,
    FixedU32<U32>,
    FixedU32<U31>,
    u32
);

// ── u64-backed (boundary pairs only) ────────────────────────────────
use crate::fixed::u64 as fu64;

prove_fix_fix_u!(
    u64_q064q000,
    fu64::Q064Q000,
    FixedU64<U64>,
    FixedU64<U0>,
    u64
);
prove_fix_fix_u!(
    u64_q064q032,
    fu64::Q064Q032,
    FixedU64<U64>,
    FixedU64<U32>,
    u64
);
prove_fix_fix_u!(
    u64_q064q063,
    fu64::Q064Q063,
    FixedU64<U64>,
    FixedU64<U63>,
    u64
);

// ── u128-backed (boundary pairs only) ───────────────────────────────
use crate::fixed::u128 as fu128;

prove_fix_fix_u!(
    u128_q128q000,
    fu128::Q128Q000,
    FixedU128<U128>,
    FixedU128<U0>,
    u128
);
prove_fix_fix_u!(
    u128_q128q064,
    fu128::Q128Q064,
    FixedU128<U128>,
    FixedU128<U64>,
    u128
);
prove_fix_fix_u!(
    u128_q128q127,
    fu128::Q128Q127,
    FixedU128<U128>,
    FixedU128<U127>,
    u128
);
