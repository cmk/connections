//! Galois-connection core: the `Conn<A, B>` type + its submodules.
//!
//! Submodules under `conn/` each implement a family of connections
//! for a specific domain:
//!
//! - `int` / `word` — integer ↔ integer connections (stubs for now).
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
pub mod word;

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
    use crate::property::arb_f64;
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

    // `compose!` macro tests are added in a follow-up commit; this
    // commit only introduces the macro and removes the prior
    // `compose_conn!` binary form it replaces.
}
