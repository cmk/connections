//! Galois-connection core: the `Conn<A, B>` type + its submodules.
//!
//! Submodules under `conn/` each implement a family of connections
//! for a specific domain:
//!
//! - `int` / `uint` — integer ↔ integer connections (signed and
//!   unsigned ladders + Word↔Int cross-sign conns).
//! - `float` — float ↔ float connections; also hosts the
//!   `ExtendedFloat` wrapper type used by N5 lattice connections.
//! - `fixed` — decimal fixed-point ladder (Uni..Pico) with the
//!   adjacent and non-adjacent pair connections.
//! - `sample` — rate-typed sample-indexed time; rate ↔ rate and
//!   rate ↔ pico connections.

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
/// use connections::conn::fixed::{Pico, Uni, F12F09, F09F06, F06F03, F03F00};
///
/// const F12F00_BIS: Conn<Pico, Uni> =
///     compose!(F12F09, F09F06, F06F03, F03F00);
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
        Conn { ceil, inner, floor: ceil }
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
        fn id<T>(x: T) -> T { x }
        Conn { ceil: id, inner: id, floor: id }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lattice::Ple;
    use crate::property::arb::arb_f64;
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
        fn double(x: i32) -> i64 { x as i64 * 2 }
        fn halve(x: i64) -> i32 { (x / 2) as i32 }
        let c = Conn::new_left(double, halve);
        // floor should behave identically to ceil
        assert_eq!(c.ceil(5), c.floor(5));
        assert_eq!(c.ceil(-3), c.floor(-3));
    }

    // ── Property tests for identity connection ─────────────────────

    /// Adjointness: `f(a) ≤ b ⟺ a ≤ g(b)`
    fn adjoint_id(a: i32, b: i32) -> bool {
        let c = Conn::<i32, i32>::identity();
        let fa = c.ceil(a);
        let gb = c.inner(b);
        (fa <= b) == (a <= gb)
    }

    /// Closure: `a ≤ g(f(a))`
    fn closed_id(a: i32) -> bool {
        let c = Conn::<i32, i32>::identity();
        a <= c.inner(c.ceil(a))
    }

    /// Kernel: `f(g(b)) ≤ b`
    fn kernel_id(b: i32) -> bool {
        let c = Conn::<i32, i32>::identity();
        c.ceil(c.inner(b)) <= b
    }

    /// Monotonicity: `a1 ≤ a2 ⟹ f(a1) ≤ f(a2)` and `b1 ≤ b2 ⟹ g(b1) ≤ g(b2)`
    #[allow(clippy::nonminimal_bool)]
    fn monotonic_id(a1: i32, a2: i32, b1: i32, b2: i32) -> bool {
        let c = Conn::<i32, i32>::identity();
        // Written as implication (not `a1 > a2`) to match the partial-order form.
        let mf = !(a1 <= a2) || c.ceil(a1) <= c.ceil(a2);
        let mg = !(b1 <= b2) || c.inner(b1) <= c.inner(b2);
        mf && mg
    }

    /// Idempotence: `g(f(g(f(a)))) == g(f(a))`
    fn idempotent_id(a: i32) -> bool {
        let c = Conn::<i32, i32>::identity();
        let gfa = c.inner(c.ceil(a));
        let gfgfa = c.inner(c.ceil(gfa));
        gfa == gfgfa
    }

    proptest! {
        #[test]
        fn prop_identity_adjoint(a: i32, b: i32) {
            prop_assert!(adjoint_id(a, b));
        }

        #[test]
        fn prop_identity_closed(a: i32) {
            prop_assert!(closed_id(a));
        }

        #[test]
        fn prop_identity_kernel(b: i32) {
            prop_assert!(kernel_id(b));
        }

        #[test]
        fn prop_identity_monotonic(a1: i32, a2: i32, b1: i32, b2: i32) {
            prop_assert!(monotonic_id(a1, a2, b1, b2));
        }

        #[test]
        fn prop_identity_idempotent(a: i32) {
            prop_assert!(idempotent_id(a));
        }
    }

    // ── Property tests for identity on f64 (exercises N5 ordering) ─

    fn adjoint_id_f64(a: f64, b: f64) -> bool {
        let c = Conn::<f64, f64>::identity();
        let fa = c.ceil(a);
        let gb = c.inner(b);
        fa.ple(&b) == a.ple(&gb)
    }

    fn closed_id_f64(a: f64) -> bool {
        let c = Conn::<f64, f64>::identity();
        a.ple(&c.inner(c.ceil(a)))
    }

    fn kernel_id_f64(b: f64) -> bool {
        let c = Conn::<f64, f64>::identity();
        c.ceil(c.inner(b)).ple(&b)
    }

    proptest! {
        #[test]
        fn prop_identity_f64_adjoint(a in arb_f64(), b in arb_f64()) {
            prop_assert!(adjoint_id_f64(a, b));
        }

        #[test]
        fn prop_identity_f64_closed(a in arb_f64()) {
            prop_assert!(closed_id_f64(a));
        }

        #[test]
        fn prop_identity_f64_kernel(b in arb_f64()) {
            prop_assert!(kernel_id_f64(b));
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
    // 1. Two-step (Pico→Nano→Micro): the macro's
    //    covariant-ceil / contravariant-inner expansion vs. hand-nested
    //    calls.
    // 2. Three-step (Pico→Nano→Micro→Milli): exercises the recursive
    //    `$rest` splicing for an odd parent count, distinct from the
    //    2- and 4-step shapes.
    // 3. Four-step (Pico→Nano→Micro→Milli→Uni): the macro vs. the
    //    hand-coded non-adjacent `F12F00`.
    // 4. Galois-law preservation: a macro-composed `Conn<Pico, Uni>`
    //    must satisfy the same adjoint laws as any hand-coded Conn.
    // 5. Identity laws: composing with `Conn::identity()` on either
    //    side reduces to the other parent.
    // 6. Representative-value spot checks at exact and off-boundary
    //    inputs (boundary of integer divide-by-PREC behaviour).
    //
    // Const-context coercion of the non-capturing closures inside
    // `compose!` is exercised by `COMPOSED_F12F00` (declared `const`).

    use crate::compose;
    use crate::conn::fixed::{
        HasResolution, Micro, Milli, Pico, Uni, F03F00, F06F03, F06F00, F09F06, F12F00, F12F06,
        F12F09,
    };
    use crate::property::arb::{fixed_coarse, fixed_fine, fixed_safe_fine};

    const COMPOSED_F12F00: Conn<Pico, Uni> = compose!(F12F09, F09F06, F06F03, F03F00);

    // Two-step variant routed through Micro — equivalent to `F12F00`
    // via a different intermediate. Used by the identity-law and
    // representative-value tests below.
    const COMPOSED_F12F00_VIA_MICRO: Conn<Pico, Uni> = compose!(F12F06, F06F00);

    // Identity bookends for the left/right identity laws.
    const ID_PICO: Conn<Pico, Pico> = Conn::identity();
    const ID_MICRO: Conn<Micro, Micro> = Conn::identity();
    const LEFT_ID_COMPOSED: Conn<Pico, Micro> = compose!(ID_PICO, F12F06);
    const RIGHT_ID_COMPOSED: Conn<Pico, Micro> = compose!(F12F06, ID_MICRO);

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
            let x = Pico(p);
            assert_eq!(COMPOSED_F12F00_VIA_MICRO.ceil(x), F12F00.ceil(x), "ceil @ {p}");
            assert_eq!(COMPOSED_F12F00_VIA_MICRO.floor(x), F12F00.floor(x), "floor @ {p}");
        }
        for u in [0_i64, 1, -1, 42, -42] {
            let x = Uni(u);
            assert_eq!(COMPOSED_F12F00_VIA_MICRO.inner(x), F12F00.inner(x), "inner @ {u}");
        }
    }

    #[test]
    fn compose_left_identity() {
        // id ∘ F12F06 must equal F12F06 pointwise.
        for p in [0_i64, 1, -1, 1_500_000, -1_500_000, 999_999, -999_999] {
            let x = Pico(p);
            assert_eq!(LEFT_ID_COMPOSED.ceil(x), F12F06.ceil(x));
            assert_eq!(LEFT_ID_COMPOSED.floor(x), F12F06.floor(x));
        }
        for u in [0_i64, 1, -1, 42, -42] {
            let x = Micro(u);
            assert_eq!(LEFT_ID_COMPOSED.inner(x), F12F06.inner(x));
        }
    }

    #[test]
    fn compose_right_identity() {
        for p in [0_i64, 1, -1, 1_500_000, -1_500_000, 999_999, -999_999] {
            let x = Pico(p);
            assert_eq!(RIGHT_ID_COMPOSED.ceil(x), F12F06.ceil(x));
            assert_eq!(RIGHT_ID_COMPOSED.floor(x), F12F06.floor(x));
        }
        for u in [0_i64, 1, -1, 42, -42] {
            let x = Micro(u);
            assert_eq!(RIGHT_ID_COMPOSED.inner(x), F12F06.inner(x));
        }
    }

    #[test]
    fn compose_inner_at_uni_safe_boundary() {
        // `fixed_coarse(Pico::PREC)` narrows to |c| ≤ i64::MAX / 1e12
        // because `inner(c) = c · 1e12` overflows past that. The
        // narrowing is architectural (it applies identically to
        // `F12F00.inner`); confirm composed and hand-written agree at
        // and just inside the limit.
        let limit = i64::MAX / Pico::PREC;
        assert_eq!(COMPOSED_F12F00.inner(Uni(limit)), F12F00.inner(Uni(limit)));
        assert_eq!(COMPOSED_F12F00.inner(Uni(-limit)), F12F00.inner(Uni(-limit)));
        assert_eq!(COMPOSED_F12F00.inner(Uni(limit - 1)), F12F00.inner(Uni(limit - 1)));
        assert_eq!(
            COMPOSED_F12F00.inner(Uni(-limit + 1)),
            F12F00.inner(Uni(-limit + 1))
        );
    }

    proptest! {
        // Two-step (Pico→Micro). Source-side ceil/floor over the full
        // `bounded_fine` Pico domain; inner round-trip over the Micro
        // coarse domain capped at i64::MAX / (Pico::PREC / Micro::PREC)
        // — `composed.inner(Micro)` multiplies through Nano (×1e3) and
        // Pico (×1e3), total ratio 1e6.
        #[test]
        fn compose_two_step_ceil_floor_match_nested(
            p in fixed_fine(1_000_000_000_000i64),
        ) {
            let composed: Conn<Pico, Micro> = compose!(F12F09, F09F06);
            let pico = Pico(p);
            prop_assert_eq!(composed.ceil(pico),  F09F06.ceil(F12F09.ceil(pico)));
            prop_assert_eq!(composed.floor(pico), F09F06.floor(F12F09.floor(pico)));
        }

        #[test]
        fn compose_two_step_inner_matches_nested(
            m in fixed_coarse(Pico::PREC / Micro::PREC),
        ) {
            let composed: Conn<Pico, Micro> = compose!(F12F09, F09F06);
            let micro = Micro(m);
            prop_assert_eq!(
                composed.inner(micro),
                F12F09.inner(F09F06.inner(micro)),
            );
        }

        // Three-step (Pico→Milli). Distinct expansion shape from 2 and
        // 4 — exercises the `@nest_*` recursive arms with a non-empty
        // tail of length two. The inner round-trip multiplies through
        // Milli (×1e3) → Micro (×1e3) → Nano (×1e3) → Pico, total
        // ratio 1e9 = Pico::PREC / Milli::PREC, so the input must be
        // capped at i64::MAX / 1e9.
        #[test]
        fn compose_three_step_matches_nested(
            p in fixed_fine(1_000_000_000_000i64),
            m in fixed_coarse(Pico::PREC / Milli::PREC),
        ) {
            let composed: Conn<Pico, Milli> = compose!(F12F09, F09F06, F06F03);
            let pico  = Pico(p);
            let milli = Milli(m);
            prop_assert_eq!(
                composed.ceil(pico),
                F06F03.ceil(F09F06.ceil(F12F09.ceil(pico))),
            );
            prop_assert_eq!(
                composed.floor(pico),
                F06F03.floor(F09F06.floor(F12F09.floor(pico))),
            );
            prop_assert_eq!(
                composed.inner(milli),
                F12F09.inner(F09F06.inner(F06F03.inner(milli))),
            );
        }

        // Four-step (Pico→Uni). Same domain split as two-step.
        #[test]
        fn compose_four_step_ceil_floor_match_handcoded(
            p in fixed_fine(1_000_000_000_000i64),
        ) {
            let pico = Pico(p);
            prop_assert_eq!(COMPOSED_F12F00.ceil(pico),  F12F00.ceil(pico));
            prop_assert_eq!(COMPOSED_F12F00.floor(pico), F12F00.floor(pico));
        }

        #[test]
        fn compose_four_step_inner_matches_handcoded(
            u in fixed_coarse(Pico::PREC),
        ) {
            let uni = Uni(u);
            prop_assert_eq!(COMPOSED_F12F00.inner(uni), F12F00.inner(uni));
        }

        // Galois-law preservation on the macro-composed Pico→Uni Conn.
        // Mirrors the invariants `props_for_pair!` checks; uses
        // F12F00's PREC (1e12) to scope the Coarse generators.
        #[test]
        fn compose_inner_then_ceil_is_id(c in fixed_coarse(1_000_000_000_000i64)) {
            let b = Uni(c);
            prop_assert_eq!(COMPOSED_F12F00.ceil(COMPOSED_F12F00.inner(b)), b);
        }

        #[test]
        fn compose_inner_then_floor_is_id(c in fixed_coarse(1_000_000_000_000i64)) {
            let b = Uni(c);
            prop_assert_eq!(COMPOSED_F12F00.floor(COMPOSED_F12F00.inner(b)), b);
        }

        // `floor ≤ ceil` is a general Galois-connection invariant that
        // `compose!` must preserve. The stricter `ceil − floor ≤ 1`
        // ULP property is fixed-point-ladder-specific (it depends on
        // integer division by PREC) and is already covered for
        // `F12F00` directly by `props_for_pair!` in
        // `src/conn/fixed.rs`; we don't re-assert it here.
        #[test]
        fn compose_floor_le_ceil(p in fixed_fine(1_000_000_000_000i64)) {
            let pico = Pico(p);
            let c = COMPOSED_F12F00.ceil(pico);
            let f = COMPOSED_F12F00.floor(pico);
            prop_assert!(f <= c);
        }

        #[test]
        fn compose_galois_upper(
            p in fixed_fine(1_000_000_000_000i64),
            c in fixed_coarse(1_000_000_000_000i64),
        ) {
            let pico = Pico(p);
            let uni  = Uni(c);
            prop_assert_eq!(
                COMPOSED_F12F00.ceil(pico) <= uni,
                pico <= COMPOSED_F12F00.inner(uni),
            );
        }

        #[test]
        fn compose_galois_lower(
            p in fixed_fine(1_000_000_000_000i64),
            c in fixed_coarse(1_000_000_000_000i64),
        ) {
            let pico = Pico(p);
            let uni  = Uni(c);
            prop_assert_eq!(
                COMPOSED_F12F00.inner(uni) <= pico,
                uni <= COMPOSED_F12F00.floor(pico),
            );
        }

        #[test]
        fn compose_idempotent(p in fixed_safe_fine(1_000_000_000_000i64)) {
            let pico = Pico(p);
            let once  = COMPOSED_F12F00.inner(COMPOSED_F12F00.ceil(pico));
            let twice = COMPOSED_F12F00.inner(COMPOSED_F12F00.ceil(once));
            prop_assert_eq!(once, twice);
        }
    }
}
