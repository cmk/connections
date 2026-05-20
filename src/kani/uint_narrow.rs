//! Kani harnesses for [`crate::uint_uint_narrow!`] (`uN → uM`
//! narrowing) and [`crate::int_uint_narrow!`] (`iN → uM` cross-sign
//! narrowing). Both are single-sided left-Galois `pub const Conn<A, B>`.

use crate::prop::conn as conn_laws;

/// Six L-Galois harnesses for one `*_narrow!` Conn (matches the
/// `int_int_narrow!` battery, including `roundtrip_ceil`).
macro_rules! prove_uint_narrow {
    ($mod_name:ident, $CONN:path, $A:ty, $B:ty) => {
        mod $mod_name {
            use super::*;

            #[kani::proof]
            fn galois_l() {
                let a: $A = kani::any();
                let b: $B = kani::any();
                assert!(conn_laws::galois_l(&$CONN, a, b));
            }

            #[kani::proof]
            fn monotone_l() {
                let a1: $A = kani::any();
                let a2: $A = kani::any();
                assert!(conn_laws::monotone_l(&$CONN, a1, a2));
            }

            #[kani::proof]
            fn closure_l() {
                let a: $A = kani::any();
                assert!(conn_laws::closure_l(&$CONN, a));
            }

            #[kani::proof]
            fn kernel_l() {
                let b: $B = kani::any();
                assert!(conn_laws::kernel_l(&$CONN, b));
            }

            #[kani::proof]
            fn idempotent_l() {
                let a: $A = kani::any();
                assert!(conn_laws::idempotent_l(&$CONN, a));
            }

            #[kani::proof]
            fn roundtrip_ceil() {
                let b: $B = kani::any();
                assert!(conn_laws::roundtrip_ceil(&$CONN, b));
            }
        }
    };
}

// Per AGENTS.md `## Conn placement`, U###U### narrowing and I###U###
// narrowing Conns both live in their source (wider) module — tie-break
// rule (2). The harnesses below import per-source so the path matches
// the actual hosting after the Plan-26 `core/`/`fixed/` split.

use crate::core::i016 as ci016;
use crate::core::i032 as ci032;
use crate::core::i064 as ci064;
use crate::core::i128 as ci128;
use crate::core::u016 as cu016;
use crate::core::u032 as cu032;
use crate::core::u064 as cu064;
use crate::core::u128 as cu128;

// ── uint_uint_narrow! (source-keyed) ────────────────────────────────

prove_uint_narrow!(uun_u016u008, cu016::U016U008, u16, u8);

prove_uint_narrow!(uun_u032u008, cu032::U032U008, u32, u8);
prove_uint_narrow!(uun_u032u016, cu032::U032U016, u32, u16);

prove_uint_narrow!(uun_u064u008, cu064::U064U008, u64, u8);
prove_uint_narrow!(uun_u064u016, cu064::U064U016, u64, u16);
prove_uint_narrow!(uun_u064u032, cu064::U064U032, u64, u32);

prove_uint_narrow!(uun_u128u008, cu128::U128U008, u128, u8);
prove_uint_narrow!(uun_u128u016, cu128::U128U016, u128, u16);
prove_uint_narrow!(uun_u128u032, cu128::U128U032, u128, u32);
prove_uint_narrow!(uun_u128u064, cu128::U128U064, u128, u64);

// ── int_uint_narrow! (source-keyed) ─────────────────────────────────

prove_uint_narrow!(iun_i016u008, ci016::I016U008, i16, u8);

prove_uint_narrow!(iun_i032u008, ci032::I032U008, i32, u8);
prove_uint_narrow!(iun_i032u016, ci032::I032U016, i32, u16);

prove_uint_narrow!(iun_i064u008, ci064::I064U008, i64, u8);
prove_uint_narrow!(iun_i064u016, ci064::I064U016, i64, u16);
prove_uint_narrow!(iun_i064u032, ci064::I064U032, i64, u32);

prove_uint_narrow!(iun_i128u008, ci128::I128U008, i128, u8);
prove_uint_narrow!(iun_i128u016, ci128::I128U016, i128, u16);
prove_uint_narrow!(iun_i128u032, ci128::I128U032, i128, u32);
prove_uint_narrow!(iun_i128u064, ci128::I128U064, i128, u64);
