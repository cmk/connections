//! Kani harnesses for [`crate::int_int_narrow!`] — `iN → iM` saturating
//! narrow (signed; `bits(N) > bits(M)`). Single-sided left-Galois.
//!
//! Mirrors the proptest battery in `tests/int_i8_galois.rs` (and the
//! per-destination `int_i{16,32,64}_galois.rs` siblings). Same five
//! laws, same `prop::conn::*` predicates — but the input is a fresh
//! `kani::any::<_>()` symbolic value rather than a sampled
//! `proptest::any!()`, so CBMC proves the law over the full bit-width
//! domain rather than a tiny sample.

use crate::prop::conn as conn_laws;

/// Emit the five L-Galois harnesses for one `int_int_narrow!` Conn.
///
/// Each harness becomes a `<conn_lower>::<law>` Kani proof:
///   * `galois_l`     — adjoint law
///   * `monotone_l`   — `a1 ≤ a2 ⟹ ceil(a1) ≤ ceil(a2)`
///   * `closure_l`    — `a ≤ inner(ceil(a))`
///   * `kernel_l`     — `ceil(inner(b)) ≤ b`
///   * `idempotent_l` — `(inner ∘ ceil)² == (inner ∘ ceil)`
///   * `roundtrip_ceil` — `ceil(inner(b)) == b` (exact-on-rounds)
macro_rules! prove_int_narrow {
    ($mod_name:ident, $CONN:path, $A:ty, $B:ty) => {
        mod $mod_name {
            use super::*;

            #[kani::proof]
            fn galois_l() {
                let a: $A = kani::any();
                let b: $B = kani::any();
                assert!(conn_laws::galois_l(&$CONN, a, b));
            }

            // `prop::conn::monotone_l` returns `true` vacuously for
            // `a1 > a2` (see `src/prop/conn.rs`), so unconstrained
            // `kani::any()` inputs are sound — no
            // `kani::assume(a1 <= a2)` needed; same for the other
            // monotonicity harnesses below.
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

// ── i8 destinations ─────────────────────────────────────────────────
use crate::fixed::i008 as fi008;

prove_int_narrow!(i016i008, fi008::I016I008, i16, i8);
prove_int_narrow!(i032i008, fi008::I032I008, i32, i8);
prove_int_narrow!(i064i008, fi008::I064I008, i64, i8);
prove_int_narrow!(i128i008, fi008::I128I008, i128, i8);

// ── i16 destinations ────────────────────────────────────────────────
use crate::fixed::i016 as fi016;

prove_int_narrow!(i032i016, fi016::I032I016, i32, i16);
prove_int_narrow!(i064i016, fi016::I064I016, i64, i16);
prove_int_narrow!(i128i016, fi016::I128I016, i128, i16);

// ── i32 destinations ────────────────────────────────────────────────
use crate::fixed::i032 as fi032;

prove_int_narrow!(i064i032, fi032::I064I032, i64, i32);
prove_int_narrow!(i128i032, fi032::I128I032, i128, i32);

// ── i64 destination ────────────────────────────────────────────────
use crate::fixed::i064 as fi064;

prove_int_narrow!(i128i064, fi064::I128I064, i128, i64);
