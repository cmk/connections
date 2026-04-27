//! Operations on a [`Conn`] — the L/R-side accessors, the unary/binary
//! lifters, and the curried `maximize` / `minimize` helpers.
//!
//! Port of the public surface of
//! [`Data.Connection.Cast`](https://hackage.haskell.org/package/connections/docs/Data-Connection-Cast.html)
//! from the Haskell `connections` library, **minus** the `Side` data
//! kind (`'L` / `'R`).
//!
//! ## L vs R is a naming axis, not a type axis
//!
//! In the Haskell library, `Cast 'L a b` and `Cast 'R a b` are *types*
//! distinguished by a phantom `Side` index, even though they share one
//! runtime representation. The split lets the compiler enforce that
//! `floor` / `lower` / `minimize` are only callable on `'R` and
//! `ceiling` / `upper` / `maximize` only on `'L`.
//!
//! Rust's [`Conn<A, B>`](super::Conn) carries the *full adjoint
//! triple* (`ceil ⊣ inner ⊣ floor`) in three `fn`-pointer fields, so a
//! one-sided connection is just a triple where `floor == ceil`. Both
//! L-style and R-style operations are well-defined for any `Conn`:
//! they read different fields of the same struct. We therefore expose
//! **both naming conventions** as free functions on the same type.
//!
//! - L-side names: [`upper`], [`upper1`], [`upper2`], [`ceiling`],
//!   [`ceiling1`], [`ceiling2`], [`maximize`].
//! - R-side names: [`lower`], [`lower1`], [`lower2`], [`floor`],
//!   [`floor1`], [`floor2`], [`minimize`].
//!
//! `upper` and `lower` both return `c.inner(b)` — the same field. They
//! differ in *documented contract*: `upper` names the upper adjoint of
//! the L-pair `(ceil, inner)`; `lower` names the lower adjoint of the
//! R-pair `(inner, floor)`. For a length-2 connection (where
//! `floor == ceil`), the unused side returns the same answer as the
//! used side. For a length-3 triple, the L and R sides may genuinely
//! differ in their `ceiling` / `floor` arms.
//!
//! See `doc/design.md` § "Core type" for the rationale.
//!
//! ## What's *not* here
//!
//! - **`swapL` / `swapR`**: identity in our representation — the same
//!   `Conn` answers both. No conversion function needed.
//! - **Two-sided helpers** (`round`, `truncate`, `midpoint`, `interval`,
//!   `median`): land in Sprint B alongside the `Pcompare` trait.
//! - **`mapped`**: requires HKT; per `doc/design.md` line 206, omit and
//!   specialize per container if needed downstream.

use super::Conn;

// ── L-side accessors and lifters (Cast.hs:217–312) ──────────────────

/// Apply the upper adjoint of the L-pair: `b ↦ inner(b)`.
///
/// In an adjoint pair `f ⊣ g` with `f: A → B` and `g: B → A`, this is
/// `g`. Equivalent to calling [`Conn::inner`] directly; named for the
/// L-side reading of the connection.
///
/// ```rust
/// use connections::conn::Conn;
/// use connections::conn::cast::upper;
/// let c: Conn<i32, i32> = Conn::identity();
/// assert_eq!(upper(&c, 7), 7);
/// ```
#[inline]
pub fn upper<A, B>(c: &Conn<A, B>, b: B) -> A {
    c.inner(b)
}

/// Lift a unary endofunction over `B` into one over `A` through the
/// L-pair: `a ↦ inner(f(ceil(a)))`.
///
/// The unit law `a ≤ upper1(c, id, a)` is property-tested.
#[inline]
pub fn upper1<A, B, F>(c: &Conn<A, B>, f: F, a: A) -> A
where
    F: FnOnce(B) -> B,
{
    c.inner(f(c.ceil(a)))
}

/// Lift a binary function over `B` into a binary function over `A`
/// through the L-pair: `(a1, a2) ↦ inner(f(ceil(a1), ceil(a2)))`.
#[inline]
pub fn upper2<A, B, F>(c: &Conn<A, B>, f: F, a1: A, a2: A) -> A
where
    F: FnOnce(B, B) -> B,
{
    c.inner(f(c.ceil(a1), c.ceil(a2)))
}

/// Apply the lower adjoint (ceiling): `a ↦ ceil(a)`.
///
/// Synonymous with [`Conn::ceil`] under the L-side reading.
///
/// ```rust
/// use connections::conn::Conn;
/// use connections::conn::cast::ceiling;
/// let c: Conn<i32, i32> = Conn::identity();
/// assert_eq!(ceiling(&c, 7), 7);
/// ```
#[inline]
pub fn ceiling<A, B>(c: &Conn<A, B>, a: A) -> B {
    c.ceil(a)
}

/// Lift a unary endofunction over `A` into one over `B` through the
/// L-pair: `b ↦ ceil(f(inner(b)))`.
#[inline]
pub fn ceiling1<A, B, F>(c: &Conn<A, B>, f: F, b: B) -> B
where
    F: FnOnce(A) -> A,
{
    c.ceil(f(c.inner(b)))
}

/// Lift a binary function over `A` into a binary function over `B`
/// through the L-pair: `(b1, b2) ↦ ceil(f(inner(b1), inner(b2)))`.
#[inline]
pub fn ceiling2<A, B, F>(c: &Conn<A, B>, f: F, b1: B, b2: B) -> B
where
    F: FnOnce(A, A) -> A,
{
    c.ceil(f(c.inner(b1), c.inner(b2)))
}

/// Curried form of `ceiling` over a `Conn<(A, B), C>` — the
/// "generalized maximum".
///
/// `maximize(c, a, b) = ceiling(c, (a, b))`.
#[inline]
pub fn maximize<A, B, C>(c: &Conn<(A, B), C>, a: A, b: B) -> C {
    c.ceil((a, b))
}

// ── R-side accessors and lifters (Cast.hs:314–402) ──────────────────

/// Apply the lower adjoint of the R-pair: `b ↦ inner(b)`.
///
/// In an adjoint pair `g ⊣ h` with `h: A → B` and `g: B → A`, this is
/// `g`. Equivalent to calling [`Conn::inner`] directly; named for the
/// R-side reading of the connection.
#[inline]
pub fn lower<A, B>(c: &Conn<A, B>, b: B) -> A {
    c.inner(b)
}

/// Lift a unary endofunction over `B` into one over `A` through the
/// R-pair: `a ↦ inner(f(floor(a)))`.
///
/// The counit law `lower1(c, id, a) ≤ a` is property-tested.
#[inline]
pub fn lower1<A, B, F>(c: &Conn<A, B>, f: F, a: A) -> A
where
    F: FnOnce(B) -> B,
{
    c.inner(f(c.floor(a)))
}

/// Lift a binary function over `B` into a binary function over `A`
/// through the R-pair: `(a1, a2) ↦ inner(f(floor(a1), floor(a2)))`.
#[inline]
pub fn lower2<A, B, F>(c: &Conn<A, B>, f: F, a1: A, a2: A) -> A
where
    F: FnOnce(B, B) -> B,
{
    c.inner(f(c.floor(a1), c.floor(a2)))
}

/// Apply the upper adjoint (floor): `a ↦ floor(a)`.
///
/// Synonymous with [`Conn::floor`] under the R-side reading.
#[inline]
pub fn floor<A, B>(c: &Conn<A, B>, a: A) -> B {
    c.floor(a)
}

/// Lift a unary endofunction over `A` into one over `B` through the
/// R-pair: `b ↦ floor(f(inner(b)))`.
#[inline]
pub fn floor1<A, B, F>(c: &Conn<A, B>, f: F, b: B) -> B
where
    F: FnOnce(A) -> A,
{
    c.floor(f(c.inner(b)))
}

/// Lift a binary function over `A` into a binary function over `B`
/// through the R-pair: `(b1, b2) ↦ floor(f(inner(b1), inner(b2)))`.
#[inline]
pub fn floor2<A, B, F>(c: &Conn<A, B>, f: F, b1: B, b2: B) -> B
where
    F: FnOnce(A, A) -> A,
{
    c.floor(f(c.inner(b1), c.inner(b2)))
}

/// Curried form of `floor` over a `Conn<(A, B), C>` — the
/// "generalized minimum".
///
/// `minimize(c, a, b) = floor(c, (a, b))`.
#[inline]
pub fn minimize<A, B, C>(c: &Conn<(A, B), C>, a: A, b: B) -> C {
    c.floor((a, b))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::conn::fixed::decimal::{FD09, FD12, FD12FD09};
    use crate::conn::float::ExtendedFloat;
    use crate::property::arb::{arb_f64, fixed_coarse, fixed_safe_fine};
    use crate::property::laws;
    use proptest::prelude::*;

    // ── Conn bases used across the proptest blocks below ──────────
    //
    // The three bases give us:
    //   - ID_I32: Ord path, trivially identity (every lifter reduces
    //     to f(x)).
    //   - ID_EF64: ExtendedFloat<f64> path with Bot/Top/Extend(NaN);
    //     covers the lawful float wrapper (raw f64 is not Eq).
    //   - FD12FD09: a non-trivial triple (FD12 ⊣ inner ⊣ floor with
    //     ratio 10³) so the L and R sides of the lifters can differ.
    const ID_I32: Conn<i32, i32> = Conn::identity();
    const ID_EF64: Conn<ExtendedFloat<f64>, ExtendedFloat<f64>> = Conn::identity();

    // FD12FD09 ratio (FD12 → FD09) is 10³.
    const FD12FD09_RATIO: i64 = 1_000;

    // ── Deterministic spot checks (delegation correctness) ────────

    #[test]
    fn upper_eq_inner_id() {
        assert_eq!(upper(&ID_I32, 7), ID_I32.inner(7));
    }

    #[test]
    fn lower_eq_inner_id() {
        assert_eq!(lower(&ID_I32, 7), ID_I32.inner(7));
    }

    #[test]
    fn ceiling_eq_ceil_id() {
        assert_eq!(ceiling(&ID_I32, 7), ID_I32.ceil(7));
    }

    #[test]
    fn floor_eq_floor_id() {
        assert_eq!(floor(&ID_I32, 7), ID_I32.floor(7));
    }

    #[test]
    fn upper1_id_id_is_id() {
        assert_eq!(upper1(&ID_I32, |x| x, 42), 42);
    }

    #[test]
    fn ceiling1_id_id_is_id() {
        assert_eq!(ceiling1(&ID_I32, |x| x, 42), 42);
    }

    #[test]
    fn lower1_id_id_is_id() {
        assert_eq!(lower1(&ID_I32, |x| x, 42), 42);
    }

    #[test]
    fn floor1_id_id_is_id() {
        assert_eq!(floor1(&ID_I32, |x| x, 42), 42);
    }

    #[test]
    fn upper2_id_proj_eq_inner_ceil() {
        // upper2(c, |p, _| p, a, a) == inner(ceil(a)) for any conn.
        assert_eq!(
            upper2(&ID_I32, |p, _q| p, 5, 5),
            ID_I32.inner(ID_I32.ceil(5))
        );
    }

    #[test]
    fn ceiling2_id_proj_eq_ceil_inner() {
        assert_eq!(
            ceiling2(&ID_I32, |p, _q| p, 5, 5),
            ID_I32.ceil(ID_I32.inner(5))
        );
    }

    // ── maximize / minimize on a hand-built `Conn<(i32, i32), i32>` ─
    //
    // The connection captures `(a, b) ↦ max(a, b)` for ceil and
    // `(a, b) ↦ min(a, b)` for floor, with `inner` returning the
    // diagonal `(x, x)`. This is the Haskell `ordered` connection,
    // shipped here only as a test fixture (full `ordered!` macro
    // arrives in Sprint C).

    const ORDERED_PAIR: Conn<(i32, i32), i32> = {
        fn ceil(p: (i32, i32)) -> i32 {
            p.0.max(p.1)
        }
        fn inner(x: i32) -> (i32, i32) {
            (x, x)
        }
        fn floor(p: (i32, i32)) -> i32 {
            p.0.min(p.1)
        }
        Conn::new(ceil, inner, floor)
    };

    #[test]
    fn maximize_eq_ceiling_pair() {
        assert_eq!(
            maximize(&ORDERED_PAIR, 3, 5),
            ceiling(&ORDERED_PAIR, (3, 5))
        );
        assert_eq!(maximize(&ORDERED_PAIR, 3, 5), 5);
    }

    #[test]
    fn minimize_eq_floor_pair() {
        assert_eq!(minimize(&ORDERED_PAIR, 3, 5), floor(&ORDERED_PAIR, (3, 5)));
        assert_eq!(minimize(&ORDERED_PAIR, 3, 5), 3);
    }

    // ── Proptest blocks: predicates × 3 conn bases ────────────────

    proptest! {
        // ── ID_I32 (Ord path) ─────────────────────────────────────

        #[test]
        fn upper1_unit_id_i32(a: i32) {
            prop_assert!(laws::cast_upper1_id_unit(&ID_I32, a));
        }

        #[test]
        fn lower1_counit_id_i32(a: i32) {
            prop_assert!(laws::cast_lower1_id_counit(&ID_I32, a));
        }

        #[test]
        fn ceiling1_kernel_id_i32(b: i32) {
            prop_assert!(laws::cast_ceiling1_id_kernel(&ID_I32, b));
        }

        #[test]
        fn floor1_kernel_id_i32(b: i32) {
            prop_assert!(laws::cast_floor1_id_kernel(&ID_I32, b));
        }

        #[test]
        fn upper2_diag_id_i32(a: i32) {
            prop_assert!(laws::cast_upper2_id_diag(&ID_I32, a));
        }

        #[test]
        fn lower2_diag_id_i32(a: i32) {
            prop_assert!(laws::cast_lower2_id_diag(&ID_I32, a));
        }

        #[test]
        fn ceiling2_diag_id_i32(b: i32) {
            prop_assert!(laws::cast_ceiling2_id_diag(&ID_I32, b));
        }

        #[test]
        fn floor2_diag_id_i32(b: i32) {
            prop_assert!(laws::cast_floor2_id_diag(&ID_I32, b));
        }

        // ── ID_EF64 (ExtendedFloat<f64>; covers Bot/Top/Extend(NaN)) ──

        #[test]
        fn upper1_unit_id_ef64(a in arb_f64()) {
            prop_assert!(laws::cast_upper1_id_unit(&ID_EF64, ExtendedFloat::Extend(a)));
        }

        #[test]
        fn lower1_counit_id_ef64(a in arb_f64()) {
            prop_assert!(laws::cast_lower1_id_counit(&ID_EF64, ExtendedFloat::Extend(a)));
        }

        #[test]
        fn ceiling1_kernel_id_ef64(b in arb_f64()) {
            prop_assert!(laws::cast_ceiling1_id_kernel(&ID_EF64, ExtendedFloat::Extend(b)));
        }

        #[test]
        fn floor1_kernel_id_ef64(b in arb_f64()) {
            prop_assert!(laws::cast_floor1_id_kernel(&ID_EF64, ExtendedFloat::Extend(b)));
        }

        #[test]
        fn upper2_diag_id_ef64(a in arb_f64()) {
            prop_assert!(laws::cast_upper2_id_diag(&ID_EF64, ExtendedFloat::Extend(a)));
        }

        #[test]
        fn lower2_diag_id_ef64(a in arb_f64()) {
            prop_assert!(laws::cast_lower2_id_diag(&ID_EF64, ExtendedFloat::Extend(a)));
        }

        #[test]
        fn ceiling2_diag_id_ef64(b in arb_f64()) {
            prop_assert!(laws::cast_ceiling2_id_diag(&ID_EF64, ExtendedFloat::Extend(b)));
        }

        #[test]
        fn floor2_diag_id_ef64(b in arb_f64()) {
            prop_assert!(laws::cast_floor2_id_diag(&ID_EF64, ExtendedFloat::Extend(b)));
        }

        // ── FD12FD09 (non-trivial triple, FD12 ⊣ inner ⊣ floor) ─────
        //
        // Source-side (FD12) generator choice mirrors `conn/fixed/
        // decimal.rs`: properties that round-trip through `inner`
        // (i.e. compute `inner(ceil(a))` or `inner(floor(a))`) use
        // `fixed_safe_fine`, which clamps to `|p| ≤ (i64::MAX / RATIO)
        // * RATIO` to keep the multiply-by-RATIO inside `inner` from
        // overflowing. Target-side (FD09) generators use
        // `fixed_coarse(RATIO)` which is already capped at
        // `i64::MAX / RATIO`.

        #[test]
        fn upper1_unit_f12f09(p in fixed_safe_fine(FD12FD09_RATIO)) {
            prop_assert!(laws::cast_upper1_id_unit(&FD12FD09, FD12(p)));
        }

        #[test]
        fn lower1_counit_f12f09(p in fixed_safe_fine(FD12FD09_RATIO)) {
            prop_assert!(laws::cast_lower1_id_counit(&FD12FD09, FD12(p)));
        }

        #[test]
        fn ceiling1_kernel_f12f09(n in fixed_coarse(FD12FD09_RATIO)) {
            prop_assert!(laws::cast_ceiling1_id_kernel(&FD12FD09, FD09(n)));
        }

        #[test]
        fn floor1_kernel_f12f09(n in fixed_coarse(FD12FD09_RATIO)) {
            prop_assert!(laws::cast_floor1_id_kernel(&FD12FD09, FD09(n)));
        }

        #[test]
        fn upper2_diag_f12f09(p in fixed_safe_fine(FD12FD09_RATIO)) {
            prop_assert!(laws::cast_upper2_id_diag(&FD12FD09, FD12(p)));
        }

        #[test]
        fn lower2_diag_f12f09(p in fixed_safe_fine(FD12FD09_RATIO)) {
            prop_assert!(laws::cast_lower2_id_diag(&FD12FD09, FD12(p)));
        }

        #[test]
        fn ceiling2_diag_f12f09(n in fixed_coarse(FD12FD09_RATIO)) {
            prop_assert!(laws::cast_ceiling2_id_diag(&FD12FD09, FD09(n)));
        }

        #[test]
        fn floor2_diag_f12f09(n in fixed_coarse(FD12FD09_RATIO)) {
            prop_assert!(laws::cast_floor2_id_diag(&FD12FD09, FD09(n)));
        }

        // ── maximize / minimize over `ORDERED_PAIR` (random pairs) ─

        #[test]
        fn maximize_eq_ceiling_random(a: i32, b: i32) {
            prop_assert!(laws::cast_maximize_eq_ceiling(&ORDERED_PAIR, a, b));
        }

        #[test]
        fn minimize_eq_floor_random(a: i32, b: i32) {
            prop_assert!(laws::cast_minimize_eq_floor(&ORDERED_PAIR, a, b));
        }
    }
}
