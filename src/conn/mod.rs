//! Galois-connection core: the `Conn<A, B>` type + its submodules.
//!
//! Submodules under `conn/` each implement a family of connections
//! for a specific domain:
//!
//! - `cast` — operations on a [`Conn`] (L/R-side accessors, lifters,
//!   and — once Sprint B lands — the two-sided rounding helpers).
//! - `int` / `uint` — integer ↔ integer connections (signed and
//!   unsigned ladders + Word↔Int cross-sign conns).
//! - `float` — float ↔ float connections; also hosts the
//!   `ExtendedFloat` wrapper type used by N5 lattice connections.
//! - `fixed` — decimal fixed-point ladder (FD00..FD12) with the
//!   adjacent and non-adjacent pair connections.
//! - `sample` — rate-typed sample-indexed time; rate ↔ rate and
//!   rate ↔ FD12 connections.

pub mod cast;
pub mod fixed;
pub mod float;
pub mod int;
pub mod sample;
pub mod uint;

/// Compose a chain of `Conn` consts into a single fresh `Conn<Src, Dst>`.
///
/// Variadic over two or more parents. Source and destination types come
/// from the binding's type annotation; the macro itself takes only the
/// parents to compose, left-to-right.
///
/// ```rust,no_run
/// use connections::compose;
/// use connections::conn::Conn;
/// use connections::conn::fixed::decimal::{FD00, FD03FD00, FD06FD03, FD09FD06, FD12, FD12FD09};
///
/// const FD12FD00_BIS: Conn<FD12, FD00> =
///     compose!(FD12FD09, FD09FD06, FD06FD03, FD03FD00);
/// ```
///
/// `ceil` and `floor` compose covariantly (left-to-right);
/// `inner` composes contravariantly (right-to-left).
///
/// The expansion uses non-capturing closures that only reference the
/// module-scope parent `const`s, so each closure coerces to an
/// `fn(_) -> _` pointer at the `Conn::new` call site — preserving
/// `Conn`'s `Copy` / `const` shape.
#[macro_export]
macro_rules! compose {
    ($first:path $(, $rest:path)+ $(,)?) => {
        $crate::conn::Conn::new(
            |a| $crate::compose!(@nest_ceil  a; $first $(, $rest)+),
            |z| $crate::compose!(@nest_inner z; $first $(, $rest)+),
            |a| $crate::compose!(@nest_floor a; $first $(, $rest)+),
        )
    };

    // ── Internal recursive arms (`@`-prefixed so the user can never
    //    invoke them directly) ────────────────────────────────────────

    // `ceil` / `floor` are covariant: wrap left-to-right, so the
    // leftmost parent runs first on the input.
    (@nest_ceil $x:expr; $last:path) => { $last.ceil($x) };
    (@nest_ceil $x:expr; $first:path $(, $rest:path)+) => {
        $crate::compose!(@nest_ceil $first.ceil($x); $($rest),+)
    };
    (@nest_floor $x:expr; $last:path) => { $last.floor($x) };
    (@nest_floor $x:expr; $first:path $(, $rest:path)+) => {
        $crate::compose!(@nest_floor $first.floor($x); $($rest),+)
    };

    // `inner` is contravariant: the rightmost parent runs first on the
    // input, so the leftmost parent's `inner` ends up on the outside.
    (@nest_inner $z:expr; $last:path) => { $last.inner($z) };
    (@nest_inner $z:expr; $first:path $(, $rest:path)+) => {
        $first.inner($crate::compose!(@nest_inner $z; $($rest),+))
    };
}

/// A Galois connection (adjoint triple) between preordered sets `A` and `B`.
///
/// Carries three monotone functions:
/// - `ceil`: lower adjoint (rounds up)
/// - `inner`: shared middle adjoint (embedding)
/// - `floor`: upper adjoint (rounds down)
///
/// For a one-sided connection (only `ceil ⊣ inner`), `floor == ceil`.
pub struct Conn<A, B> {
    pub(crate) ceil: fn(A) -> B,
    pub(crate) inner: fn(B) -> A,
    pub(crate) floor: fn(A) -> B,
}

impl<A, B> Clone for Conn<A, B> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<A, B> Copy for Conn<A, B> {}

impl<A, B> Conn<A, B> {
    /// Construct a full adjoint triple `ceil ⊣ inner ⊣ floor`.
    pub const fn new(ceil: fn(A) -> B, inner: fn(B) -> A, floor: fn(A) -> B) -> Self {
        Conn { ceil, inner, floor }
    }

    /// Construct a one-sided connection `ceil ⊣ inner` (no distinct floor).
    ///
    /// Sets `floor = ceil`, matching the Haskell `CastL` representation.
    pub const fn new_left(ceil: fn(A) -> B, inner: fn(B) -> A) -> Self {
        Conn {
            ceil,
            inner,
            floor: ceil,
        }
    }

    /// Apply the lower adjoint (ceiling / round-up).
    pub fn ceil(&self, a: A) -> B {
        (self.ceil)(a)
    }

    /// Apply the middle adjoint (embedding).
    pub fn inner(&self, b: B) -> A {
        (self.inner)(b)
    }

    /// Apply the upper adjoint (floor / round-down).
    pub fn floor(&self, a: A) -> B {
        (self.floor)(a)
    }
}

impl<T> Conn<T, T> {
    /// The identity connection: `ceil = inner = floor = id`.
    pub const fn identity() -> Self {
        fn id<T>(x: T) -> T {
            x
        }
        Conn {
            ceil: id,
            inner: id,
            floor: id,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::property::arb::arb_f64;
    use crate::property::laws;
    use proptest::prelude::*;

    #[test]
    fn identity_ceil() {
        let c = Conn::<i32, i32>::identity();
        assert_eq!(c.ceil(42), 42);
    }

    #[test]
    fn identity_inner() {
        let c = Conn::<i32, i32>::identity();
        assert_eq!(c.inner(42), 42);
    }

    #[test]
    fn identity_floor() {
        let c = Conn::<i32, i32>::identity();
        assert_eq!(c.floor(42), 42);
    }

    #[test]
    fn new_left_floor_eq_ceil() {
        fn double(x: i32) -> i64 {
            x as i64 * 2
        }
        fn halve(x: i64) -> i32 {
            (x / 2) as i32
        }
        let c = Conn::new_left(double, halve);
        // floor should behave identically to ceil
        assert_eq!(c.ceil(5), c.floor(5));
        assert_eq!(c.ceil(-3), c.floor(-3));
    }

    // ── Property tests for identity connection (i32, exercises Ord) ──

    const ID_I32: Conn<i32, i32> = Conn::identity();

    proptest! {
        #[test]
        fn galois_l(a: i32, b: i32) {
            prop_assert!(laws::conn_galois_l(&ID_I32, a, b));
        }

        #[test]
        fn closure_l(a: i32) {
            prop_assert!(laws::conn_closure_l(&ID_I32, a));
        }

        #[test]
        fn kernel_l(b: i32) {
            prop_assert!(laws::conn_kernel_l(&ID_I32, b));
        }

        #[test]
        fn monotone_l(a1: i32, a2: i32) {
            prop_assert!(laws::conn_monotone_l(&ID_I32, a1, a2));
        }

        #[test]
        fn monotone_r(b1: i32, b2: i32) {
            prop_assert!(laws::conn_monotone_r(&ID_I32, b1, b2));
        }

        #[test]
        fn idempotent(a: i32) {
            prop_assert!(laws::conn_idempotent(&ID_I32, a));
        }
    }

    // ── Property tests for identity on f64 (exercises N5 ordering) ─

    const ID_F64: Conn<f64, f64> = Conn::identity();

    proptest! {
        #[test]
        fn galois_l_f64(a in arb_f64(), b in arb_f64()) {
            prop_assert!(laws::conn_galois_l(&ID_F64, a, b));
        }

        #[test]
        fn closure_l_f64(a in arb_f64()) {
            prop_assert!(laws::conn_closure_l(&ID_F64, a));
        }

        #[test]
        fn kernel_l_f64(b in arb_f64()) {
            prop_assert!(laws::conn_kernel_l(&ID_F64, b));
        }
    }

    // ── `compose!` macro tests ───────────────────────────────────────
    //
    // Composition is a property of `Conn` itself (not of any one ladder
    // pair), so its tests live here alongside the macro definition.
    // The fixed-point ladder consts (`F??F??`) are the only Galois-
    // compliant ground truth available, so we reuse them — but the
    // properties under test are about `compose!`, not about the
    // ladder.
    //
    // Coverage:
    //
    // 1. Two-step (FD12→FD09→FD06): the macro's
    //    covariant-ceil / contravariant-inner expansion vs. hand-nested
    //    calls.
    // 2. Three-step (FD12→FD09→FD06→FD03): exercises the recursive
    //    `$rest` splicing for an odd parent count, distinct from the
    //    2- and 4-step shapes.
    // 3. Four-step (FD12→FD09→FD06→FD03→FD00): the macro vs. the
    //    hand-coded non-adjacent `FD12FD00`.
    // 4. Galois-law preservation: a macro-composed `Conn<FD12, FD00>`
    //    must satisfy the same adjoint laws as any hand-coded Conn.
    // 5. Identity laws: composing with `Conn::identity()` on either
    //    side reduces to the other parent.
    // 6. Representative-value spot checks at exact and off-boundary
    //    inputs (boundary of integer divide-by-PREC behaviour).
    //
    // Const-context coercion of the non-capturing closures inside
    // `compose!` is exercised by `COMPOSED_FD12FD00` (declared `const`).

    use crate::compose;
    use crate::conn::fixed::decimal::{
        FD00, FD03, FD03FD00, FD06, FD06FD00, FD06FD03, FD09FD06, FD12, FD12FD00, FD12FD06,
        FD12FD09, HasResolution,
    };
    use crate::property::arb::{fixed_coarse, fixed_fine, fixed_safe_fine};

    const COMPOSED_FD12FD00: Conn<FD12, FD00> = compose!(FD12FD09, FD09FD06, FD06FD03, FD03FD00);

    // Two-step variant routed through FD06 — equivalent to `FD12FD00`
    // via a different intermediate. Used by the identity-law and
    // representative-value tests below.
    const COMPOSED_FD12FD00_VIA_FD06: Conn<FD12, FD00> = compose!(FD12FD06, FD06FD00);

    // Identity bookends for the left/right identity laws.
    const ID_FD12: Conn<FD12, FD12> = Conn::identity();
    const ID_FD06: Conn<FD06, FD06> = Conn::identity();
    const LEFT_ID_COMPOSED: Conn<FD12, FD06> = compose!(ID_FD12, FD12FD06);
    const RIGHT_ID_COMPOSED: Conn<FD12, FD06> = compose!(FD12FD06, ID_FD06);

    #[test]
    fn compose_matches_hand_written_at_representative_values() {
        // Exact-boundary, off-boundary positive, off-boundary negative.
        for p in [
            0_i64,
            1,
            -1,
            1_000_000_000_000,
            -1_000_000_000_000,
            1_500_000_000_000,
            -1_500_000_000_000,
            999_999_999_999,
            -999_999_999_999,
        ] {
            let x = FD12(p);
            assert_eq!(
                COMPOSED_FD12FD00_VIA_FD06.ceil(x),
                FD12FD00.ceil(x),
                "ceil @ {p}"
            );
            assert_eq!(
                COMPOSED_FD12FD00_VIA_FD06.floor(x),
                FD12FD00.floor(x),
                "floor @ {p}"
            );
        }
        for u in [0_i64, 1, -1, 42, -42] {
            let x = FD00(u);
            assert_eq!(
                COMPOSED_FD12FD00_VIA_FD06.inner(x),
                FD12FD00.inner(x),
                "inner @ {u}"
            );
        }
    }

    #[test]
    fn compose_left_identity() {
        // id ∘ FD12FD06 must equal FD12FD06 pointwise.
        for p in [0_i64, 1, -1, 1_500_000, -1_500_000, 999_999, -999_999] {
            let x = FD12(p);
            assert_eq!(LEFT_ID_COMPOSED.ceil(x), FD12FD06.ceil(x));
            assert_eq!(LEFT_ID_COMPOSED.floor(x), FD12FD06.floor(x));
        }
        for u in [0_i64, 1, -1, 42, -42] {
            let x = FD06(u);
            assert_eq!(LEFT_ID_COMPOSED.inner(x), FD12FD06.inner(x));
        }
    }

    #[test]
    fn compose_right_identity() {
        for p in [0_i64, 1, -1, 1_500_000, -1_500_000, 999_999, -999_999] {
            let x = FD12(p);
            assert_eq!(RIGHT_ID_COMPOSED.ceil(x), FD12FD06.ceil(x));
            assert_eq!(RIGHT_ID_COMPOSED.floor(x), FD12FD06.floor(x));
        }
        for u in [0_i64, 1, -1, 42, -42] {
            let x = FD06(u);
            assert_eq!(RIGHT_ID_COMPOSED.inner(x), FD12FD06.inner(x));
        }
    }

    #[test]
    fn compose_inner_at_fd00_safe_boundary() {
        // `fixed_coarse(FD12::PREC)` narrows to |c| ≤ i64::MAX / 1e12
        // because `inner(c) = c · 1e12` overflows past that. The
        // narrowing is architectural (it applies identically to
        // `FD12FD00.inner`); confirm composed and hand-written agree at
        // and just inside the limit.
        let limit = i64::MAX / FD12::PREC;
        assert_eq!(
            COMPOSED_FD12FD00.inner(FD00(limit)),
            FD12FD00.inner(FD00(limit))
        );
        assert_eq!(
            COMPOSED_FD12FD00.inner(FD00(-limit)),
            FD12FD00.inner(FD00(-limit))
        );
        assert_eq!(
            COMPOSED_FD12FD00.inner(FD00(limit - 1)),
            FD12FD00.inner(FD00(limit - 1))
        );
        assert_eq!(
            COMPOSED_FD12FD00.inner(FD00(-limit + 1)),
            FD12FD00.inner(FD00(-limit + 1))
        );
    }

    proptest! {
        // Two-step (FD12→FD06). Source-side ceil/floor over the full
        // `bounded_fine` FD12 domain; inner round-trip over the FD06
        // coarse domain capped at i64::MAX / (FD12::PREC / FD06::PREC)
        // — `composed.inner(FD06)` multiplies through FD09 (×1e3) and
        // FD12 (×1e3), total ratio 1e6.
        #[test]
        fn compose_two_step_ceil_floor_match_nested(
            p in fixed_fine(1_000_000_000_000i64),
        ) {
            let composed: Conn<FD12, FD06> = compose!(FD12FD09, FD09FD06);
            let pico = FD12(p);
            prop_assert_eq!(composed.ceil(pico),  FD09FD06.ceil(FD12FD09.ceil(pico)));
            prop_assert_eq!(composed.floor(pico), FD09FD06.floor(FD12FD09.floor(pico)));
        }

        #[test]
        fn compose_two_step_inner_matches_nested(
            m in fixed_coarse(FD12::PREC / FD06::PREC),
        ) {
            let composed: Conn<FD12, FD06> = compose!(FD12FD09, FD09FD06);
            let micro = FD06(m);
            prop_assert_eq!(
                composed.inner(micro),
                FD12FD09.inner(FD09FD06.inner(micro)),
            );
        }

        // Three-step (FD12→FD03). Distinct expansion shape from 2 and
        // 4 — exercises the `@nest_*` recursive arms with a non-empty
        // tail of length two. The inner round-trip multiplies through
        // FD03 (×1e3) → FD06 (×1e3) → FD09 (×1e3) → FD12, total
        // ratio 1e9 = FD12::PREC / FD03::PREC, so the input must be
        // capped at i64::MAX / 1e9.
        #[test]
        fn compose_three_step_matches_nested(
            p in fixed_fine(1_000_000_000_000i64),
            m in fixed_coarse(FD12::PREC / FD03::PREC),
        ) {
            let composed: Conn<FD12, FD03> = compose!(FD12FD09, FD09FD06, FD06FD03);
            let pico  = FD12(p);
            let milli = FD03(m);
            prop_assert_eq!(
                composed.ceil(pico),
                FD06FD03.ceil(FD09FD06.ceil(FD12FD09.ceil(pico))),
            );
            prop_assert_eq!(
                composed.floor(pico),
                FD06FD03.floor(FD09FD06.floor(FD12FD09.floor(pico))),
            );
            prop_assert_eq!(
                composed.inner(milli),
                FD12FD09.inner(FD09FD06.inner(FD06FD03.inner(milli))),
            );
        }

        // Four-step (FD12→FD00). Same domain split as two-step.
        #[test]
        fn compose_four_step_ceil_floor_match_handcoded(
            p in fixed_fine(1_000_000_000_000i64),
        ) {
            let pico = FD12(p);
            prop_assert_eq!(COMPOSED_FD12FD00.ceil(pico),  FD12FD00.ceil(pico));
            prop_assert_eq!(COMPOSED_FD12FD00.floor(pico), FD12FD00.floor(pico));
        }

        #[test]
        fn compose_four_step_inner_matches_handcoded(
            u in fixed_coarse(FD12::PREC),
        ) {
            let uni = FD00(u);
            prop_assert_eq!(COMPOSED_FD12FD00.inner(uni), FD12FD00.inner(uni));
        }

        // Galois-law preservation on the macro-composed FD12→FD00 Conn.
        // Mirrors the invariants `props_for_pair!` checks; uses
        // FD12FD00's PREC (1e12) to scope the Coarse generators.
        #[test]
        fn compose_roundtrip_ceil(c in fixed_coarse(1_000_000_000_000i64)) {
            prop_assert!(laws::conn_roundtrip_ceil(&COMPOSED_FD12FD00, FD00(c)));
        }

        #[test]
        fn compose_roundtrip_floor(c in fixed_coarse(1_000_000_000_000i64)) {
            prop_assert!(laws::conn_roundtrip_floor(&COMPOSED_FD12FD00, FD00(c)));
        }

        // `floor ≤ ceil` is a general Galois-connection invariant that
        // `compose!` must preserve. The stricter `ceil − floor ≤ 1`
        // ULP property is fixed-point-ladder-specific and is already
        // covered for `FD12FD00` directly by `props_for_pair!` in
        // `src/conn/fixed.rs`; we don't re-assert it here.
        #[test]
        fn compose_floor_le_ceil(p in fixed_fine(1_000_000_000_000i64)) {
            prop_assert!(laws::conn_floor_le_ceil(&COMPOSED_FD12FD00, FD12(p)));
        }

        #[test]
        fn compose_galois_l(
            p in fixed_fine(1_000_000_000_000i64),
            c in fixed_coarse(1_000_000_000_000i64),
        ) {
            prop_assert!(laws::conn_galois_l(&COMPOSED_FD12FD00, FD12(p), FD00(c)));
        }

        #[test]
        fn compose_galois_r(
            p in fixed_fine(1_000_000_000_000i64),
            c in fixed_coarse(1_000_000_000_000i64),
        ) {
            prop_assert!(laws::conn_galois_r(&COMPOSED_FD12FD00, FD12(p), FD00(c)));
        }

        #[test]
        fn compose_idempotent(p in fixed_safe_fine(1_000_000_000_000i64)) {
            prop_assert!(laws::conn_idempotent(&COMPOSED_FD12FD00, FD12(p)));
        }
    }
}
