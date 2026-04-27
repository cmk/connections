//! Galois-connection core: the `Conn<A, B>` type + its submodules.
//!
//! Submodules under `conn/` each implement a family of connections
//! for a specific domain:
//!
//! - `cast` — operations on a [`Conn`] (L/R-side accessors, lifters,
//!   and — once Sprint B lands — the two-sided rounding helpers).
//! - `float` — float ↔ float connections; also hosts the
//!   `ExtendedFloat` wrapper type used by N5 lattice connections.
//! - `fixed` — `fixed`-crate-backed binary fixed-point ladders over
//!   `FixedI<width><Frac>` / `FixedU<width><Frac>` (per-width
//!   submodules `i8`..`i128`, `u8`..`u128`).
//! - `std` — connections rooted in `std` integer primitives. Each
//!   per-type submodule (`i8`/`i16`/`i32`/`i64`/`i128`/`u8`/`u16`/
//!   `u32`/`u64`/`u128`) hosts the Conn consts whose destination is
//!   that primitive.
//! - `time` — connections among the [`time`](https://docs.rs/time)
//!   crate's calendar / clock / duration types (8-character names —
//!   see [`crate::conn::time`]).

pub mod cast;
pub mod fixed;
pub mod float;
pub mod std;
pub mod time;

/// Compose a chain of `Conn` consts into a single fresh `Conn<Src, Dst>`.
///
/// Variadic over two or more parents. Source and destination types come
/// from the binding's type annotation; the macro itself takes only the
/// parents to compose, left-to-right.
///
/// ```rust,no_run
/// use connections::compose;
/// use connections::conn::Conn;
///
/// // Three-step compose: id ∘ id ∘ id = id (any Conn type works).
/// const ID_I32: Conn<i32, i32> = Conn::identity();
/// const COMPOSED: Conn<i32, i32> = compose!(ID_I32, ID_I32, ID_I32);
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
    /// Use this when the connection is naturally "left-Galois": the
    /// saturation plateau (if any) lives on the source side, where
    /// `ceil` collapses extra source values onto a single target. The
    /// `conn_galois_l` law (`ceil(a) ≤ b ⟺ a ≤ inner(b)`) holds; the
    /// right-Galois law generally does not.
    pub const fn new_left(ceil: fn(A) -> B, inner: fn(B) -> A) -> Self {
        Conn {
            ceil,
            inner,
            floor: ceil,
        }
    }

    /// Construct a one-sided connection `inner ⊣ floor` (no distinct ceil).
    ///
    /// Sets `ceil = floor`, the right-Galois mirror of [`Self::new_left`] —
    /// matching the Haskell `CastR` representation. Use this when the
    /// saturation plateau lives on the *target* side, where `inner`
    /// collapses extra target values onto a single source (e.g. an
    /// unsigned source clipping a signed target's negative half to
    /// `0`). The `conn_galois_r` law (`inner(b) ≤ a ⟺ b ≤ floor(a)`)
    /// holds; the left-Galois law generally does not.
    pub const fn new_right(inner: fn(B) -> A, floor: fn(A) -> B) -> Self {
        Conn {
            ceil: floor,
            inner,
            floor,
        }
    }

    /// Apply the lower adjoint (ceiling / round-up).
    #[inline]
    #[must_use]
    pub fn ceil(&self, a: A) -> B {
        (self.ceil)(a)
    }

    /// Apply the middle adjoint (embedding).
    #[inline]
    #[must_use]
    pub fn inner(&self, b: B) -> A {
        (self.inner)(b)
    }

    /// Apply the upper adjoint (floor / round-down).
    #[inline]
    #[must_use]
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

    #[test]
    fn new_right_ceil_eq_floor() {
        fn halve(x: i64) -> i32 {
            (x / 2) as i32
        }
        fn double(x: i32) -> i64 {
            x as i64 * 2
        }
        let c = Conn::new_right(halve, double);
        // ceil should behave identically to floor
        assert_eq!(c.ceil(5), c.floor(5));
        assert_eq!(c.ceil(-3), c.floor(-3));
        // and round-trip through the explicit floor/inner pair.
        assert_eq!(c.floor(5), 10);
        assert_eq!(c.inner(10), 5);
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

    // ── Property tests for identity on ExtendedFloat<f64> ─────────
    //
    // Exercises the float-aware lawful path. Raw `f64` is not `Eq`
    // (NaN ≠ NaN under standard PartialEq), so `Conn<f64, f64>` can't
    // satisfy the law-machinery bounds. `ExtendedFloat<f64>` patches
    // `PartialEq` to be reflexive at NaN and impls `Eq`, which is
    // what the laws require.

    use crate::conn::float::ExtendedFloat;

    const ID_EF64: Conn<ExtendedFloat<f64>, ExtendedFloat<f64>> = Conn::identity();

    proptest! {
        #[test]
        fn galois_l_ef64(a in arb_f64(), b in arb_f64()) {
            prop_assert!(laws::conn_galois_l(
                &ID_EF64,
                ExtendedFloat::Extend(a),
                ExtendedFloat::Extend(b),
            ));
        }

        #[test]
        fn closure_l_ef64(a in arb_f64()) {
            prop_assert!(laws::conn_closure_l(&ID_EF64, ExtendedFloat::Extend(a)));
        }

        #[test]
        fn kernel_l_ef64(b in arb_f64()) {
            prop_assert!(laws::conn_kernel_l(&ID_EF64, ExtendedFloat::Extend(b)));
        }
    }
}
