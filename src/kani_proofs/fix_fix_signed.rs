//! Kani harnesses for `fix_fix_iN!` — the per-host-width signed Q-format
//! ladder (e.g. `FixedI8<U4> → FixedI8<U0>`). These are **left-Galois
//! only** (per Plan 32) because `_inner` saturates the Coarse plateau
//! onto Fine::MAX/MIN — non-injective, so no adjoint triple exists.
//!
//! Coverage strategy (by host width):
//!
//! * **i8 / i16** — full ladder. The 8/16-bit symbolic state spaces are
//!   tiny enough that CBMC dispatches each harness in milliseconds.
//! * **i32 / i64 / i128** — boundary pairs only (`Q_max → Q_0`,
//!   `Q_max → Q_(max-1)`, plus a representative middle rung). Wider
//!   bit-widths multiply the SMT state-space exponentially; the
//!   structurally-identical harness for narrower widths covers the
//!   logic, and these wider cases anchor it at the bit-width
//!   extremes.

use crate::conn::ConnL;
use crate::prop::conn as conn_laws;
use ::fixed::FixedI8;
use ::fixed::FixedI16;
use ::fixed::FixedI32;
use ::fixed::FixedI64;
use ::fixed::FixedI128;
use ::fixed::types::extra::*;

/// Emit the five L-Galois harnesses for one `fix_fix_iN!` Conn.
///
/// `$FX_FINE` / `$FX_COARSE` are the full Q-format types
/// (e.g. `FixedI8<U4>`); `$BITS` is the underlying primitive type
/// used as the symbolic input (e.g. `i8`).
macro_rules! prove_fix_fix {
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
            // Same convention as the integer harnesses in
            // `int_narrow.rs`.
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

// ── i8-backed (full ladder, 21 Conns × 5 props = 105 proofs) ────────
use crate::fixed::i008 as fi008;

prove_fix_fix!(i8_q001q000, fi008::Q001Q000, FixedI8<U1>, FixedI8<U0>, i8);
prove_fix_fix!(i8_q002q000, fi008::Q002Q000, FixedI8<U2>, FixedI8<U0>, i8);
prove_fix_fix!(i8_q003q000, fi008::Q003Q000, FixedI8<U3>, FixedI8<U0>, i8);
prove_fix_fix!(i8_q004q000, fi008::Q004Q000, FixedI8<U4>, FixedI8<U0>, i8);
prove_fix_fix!(i8_q006q000, fi008::Q006Q000, FixedI8<U6>, FixedI8<U0>, i8);
prove_fix_fix!(i8_q008q000, fi008::Q008Q000, FixedI8<U8>, FixedI8<U0>, i8);
prove_fix_fix!(i8_q002q001, fi008::Q002Q001, FixedI8<U2>, FixedI8<U1>, i8);
prove_fix_fix!(i8_q003q001, fi008::Q003Q001, FixedI8<U3>, FixedI8<U1>, i8);
prove_fix_fix!(i8_q004q001, fi008::Q004Q001, FixedI8<U4>, FixedI8<U1>, i8);
prove_fix_fix!(i8_q006q001, fi008::Q006Q001, FixedI8<U6>, FixedI8<U1>, i8);
prove_fix_fix!(i8_q008q001, fi008::Q008Q001, FixedI8<U8>, FixedI8<U1>, i8);
prove_fix_fix!(i8_q003q002, fi008::Q003Q002, FixedI8<U3>, FixedI8<U2>, i8);
prove_fix_fix!(i8_q004q002, fi008::Q004Q002, FixedI8<U4>, FixedI8<U2>, i8);
prove_fix_fix!(i8_q006q002, fi008::Q006Q002, FixedI8<U6>, FixedI8<U2>, i8);
prove_fix_fix!(i8_q008q002, fi008::Q008Q002, FixedI8<U8>, FixedI8<U2>, i8);
prove_fix_fix!(i8_q004q003, fi008::Q004Q003, FixedI8<U4>, FixedI8<U3>, i8);
prove_fix_fix!(i8_q006q003, fi008::Q006Q003, FixedI8<U6>, FixedI8<U3>, i8);
prove_fix_fix!(i8_q008q003, fi008::Q008Q003, FixedI8<U8>, FixedI8<U3>, i8);
prove_fix_fix!(i8_q006q004, fi008::Q006Q004, FixedI8<U6>, FixedI8<U4>, i8);
prove_fix_fix!(i8_q008q004, fi008::Q008Q004, FixedI8<U8>, FixedI8<U4>, i8);
prove_fix_fix!(i8_q008q006, fi008::Q008Q006, FixedI8<U8>, FixedI8<U6>, i8);

// ── i16-backed (full ladder) ────────────────────────────────────────
use crate::fixed::i016 as fi016;

prove_fix_fix!(
    i16_q002q000,
    fi016::Q002Q000,
    FixedI16<U2>,
    FixedI16<U0>,
    i16
);
prove_fix_fix!(
    i16_q004q000,
    fi016::Q004Q000,
    FixedI16<U4>,
    FixedI16<U0>,
    i16
);
prove_fix_fix!(
    i16_q008q000,
    fi016::Q008Q000,
    FixedI16<U8>,
    FixedI16<U0>,
    i16
);
prove_fix_fix!(
    i16_q012q000,
    fi016::Q012Q000,
    FixedI16<U12>,
    FixedI16<U0>,
    i16
);
prove_fix_fix!(
    i16_q016q000,
    fi016::Q016Q000,
    FixedI16<U16>,
    FixedI16<U0>,
    i16
);
prove_fix_fix!(
    i16_q004q002,
    fi016::Q004Q002,
    FixedI16<U4>,
    FixedI16<U2>,
    i16
);
prove_fix_fix!(
    i16_q008q002,
    fi016::Q008Q002,
    FixedI16<U8>,
    FixedI16<U2>,
    i16
);
prove_fix_fix!(
    i16_q012q002,
    fi016::Q012Q002,
    FixedI16<U12>,
    FixedI16<U2>,
    i16
);
prove_fix_fix!(
    i16_q016q002,
    fi016::Q016Q002,
    FixedI16<U16>,
    FixedI16<U2>,
    i16
);
prove_fix_fix!(
    i16_q008q004,
    fi016::Q008Q004,
    FixedI16<U8>,
    FixedI16<U4>,
    i16
);
prove_fix_fix!(
    i16_q012q004,
    fi016::Q012Q004,
    FixedI16<U12>,
    FixedI16<U4>,
    i16
);
prove_fix_fix!(
    i16_q016q004,
    fi016::Q016Q004,
    FixedI16<U16>,
    FixedI16<U4>,
    i16
);
prove_fix_fix!(
    i16_q012q008,
    fi016::Q012Q008,
    FixedI16<U12>,
    FixedI16<U8>,
    i16
);
prove_fix_fix!(
    i16_q016q008,
    fi016::Q016Q008,
    FixedI16<U16>,
    FixedI16<U8>,
    i16
);
prove_fix_fix!(
    i16_q016q012,
    fi016::Q016Q012,
    FixedI16<U16>,
    FixedI16<U12>,
    i16
);

// ── i32-backed (boundary pairs only — see header) ───────────────────
use crate::fixed::i032 as fi032;

prove_fix_fix!(
    i32_q032q000,
    fi032::Q032Q000,
    FixedI32<U32>,
    FixedI32<U0>,
    i32
);
prove_fix_fix!(
    i32_q032q016,
    fi032::Q032Q016,
    FixedI32<U32>,
    FixedI32<U16>,
    i32
);
prove_fix_fix!(
    i32_q032q024,
    fi032::Q032Q024,
    FixedI32<U32>,
    FixedI32<U24>,
    i32
);
prove_fix_fix!(
    i32_q016q000,
    fi032::Q016Q000,
    FixedI32<U16>,
    FixedI32<U0>,
    i32
);

// ── i64-backed (boundary pairs only) ────────────────────────────────
use crate::fixed::i064 as fi064;

prove_fix_fix!(
    i64_q064q000,
    fi064::Q064Q000,
    FixedI64<U64>,
    FixedI64<U0>,
    i64
);
prove_fix_fix!(
    i64_q064q032,
    fi064::Q064Q032,
    FixedI64<U64>,
    FixedI64<U32>,
    i64
);
prove_fix_fix!(
    i64_q064q048,
    fi064::Q064Q048,
    FixedI64<U64>,
    FixedI64<U48>,
    i64
);

// ── i128-backed (boundary pairs only) ───────────────────────────────
use crate::fixed::i128 as fi128;

prove_fix_fix!(
    i128_q128q000,
    fi128::Q128Q000,
    FixedI128<U128>,
    FixedI128<U0>,
    i128
);
prove_fix_fix!(
    i128_q128q064,
    fi128::Q128Q064,
    FixedI128<U128>,
    FixedI128<U64>,
    i128
);
prove_fix_fix!(
    i128_q128q096,
    fi128::Q128Q096,
    FixedI128<U128>,
    FixedI128<U96>,
    i128
);
