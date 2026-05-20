//! Kani harnesses for [`crate::uint_int_sat!`] — `uN → iM` non-widening
//! saturating cast (`bits(N) ≥ bits(M)`). Single-sided **right-Galois**
//! (the saturation plateau lives on the target side).
//!
//! Mirrors `single_sided_right_props!` in `tests/int_i*_galois.rs`.

use crate::prop::conn as conn_laws;

/// Emit the five R-Galois harnesses for one `uint_int_sat!` Conn.
macro_rules! prove_uint_sat {
    ($mod_name:ident, $CONN:path, $A:ty, $B:ty) => {
        mod $mod_name {
            use super::*;

            #[kani::proof]
            fn galois_r() {
                let a: $A = kani::any();
                let b: $B = kani::any();
                assert!(conn_laws::galois_r(&$CONN, a, b));
            }

            // `prop::conn::monotone_r` returns `true` vacuously for
            // `b1 > b2`; unconstrained `kani::any()` inputs are sound.
            // Mirrors the same convention as the L-side harnesses in
            // `int_narrow.rs`.
            #[kani::proof]
            fn monotone_r() {
                let b1: $B = kani::any();
                let b2: $B = kani::any();
                assert!(conn_laws::monotone_r(&$CONN, b1, b2));
            }

            #[kani::proof]
            fn closure_r() {
                let a: $A = kani::any();
                assert!(conn_laws::closure_r(&$CONN, a));
            }

            #[kani::proof]
            fn kernel_r() {
                let b: $B = kani::any();
                assert!(conn_laws::kernel_r(&$CONN, b));
            }

            #[kani::proof]
            fn idempotent_r() {
                let b: $B = kani::any();
                assert!(conn_laws::idempotent_r(&$CONN, b));
            }

            // `roundtrip_floor` is intentionally omitted.
            //
            // The predicate `floor(inner(b)) == b` requires `inner`'s
            // image to cover every `b: $B`. For `uint_int_sat!`,
            // `inner` clips the negative half of `$B` to `0_$A`, so
            // for any negative `b`, `floor(inner(b)) = 0 ≠ b`. Kani
            // surfaces this immediately; CBMC produced a counterexample
            // at `b = -1` for every Conn in the family. The property
            // simply does not hold for right-Galois single-sided
            // Conns whose source side is unsigned. The Galois law
            // (`galois_r`) and the monotonicity / closure / kernel
            // / idempotence laws all hold and are verified above.
        }
    };
}

// Per AGENTS.md `## Conn placement`, U###I### Conns live in the source
// (unsigned) module. The harnesses below import per-source so the path
// matches the actual hosting after the Plan-26 `core/`/`fixed/` split.

use crate::core::u008 as cu008;
use crate::core::u016 as cu016;
use crate::core::u032 as cu032;
use crate::core::u064 as cu064;
use crate::core::u128 as cu128;

prove_uint_sat!(u008i008, cu008::U008I008, u8, i8);

prove_uint_sat!(u016i008, cu016::U016I008, u16, i8);
prove_uint_sat!(u016i016, cu016::U016I016, u16, i16);

prove_uint_sat!(u032i008, cu032::U032I008, u32, i8);
prove_uint_sat!(u032i016, cu032::U032I016, u32, i16);

prove_uint_sat!(u064i008, cu064::U064I008, u64, i8);
prove_uint_sat!(u064i016, cu064::U064I016, u64, i16);
prove_uint_sat!(u064i032, cu064::U064I032, u64, i32);
prove_uint_sat!(u064i064, cu064::U064I064, u64, i64);

prove_uint_sat!(u128i008, cu128::U128I008, u128, i8);
prove_uint_sat!(u128i016, cu128::U128I016, u128, i16);
prove_uint_sat!(u128i032, cu128::U128I032, u128, i32);
prove_uint_sat!(u128i064, cu128::U128I064, u128, i64);
prove_uint_sat!(u128i128, cu128::U128I128, u128, i128);
