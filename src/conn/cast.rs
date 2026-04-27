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
//! ## Two-sided helpers
//!
//! [`interval`], [`midpoint`], [`round`], [`round1`], [`round2`],
//! [`truncate`], [`truncate1`], [`truncate2`], [`median`] — port of
//! the corresponding Haskell `Data.Connection.Cast` definitions.
//! These act on **both** sides of an adjoint triple at once: e.g.
//! `round` dispatches between `ceil` and `floor` based on which side
//! the input is closer to. The arithmetic helpers (`midpoint`,
//! `interval`, `round`, `truncate` and friends) carry inline
//! `Add`/`Sub`/`Div`/`From<u8>` bounds — they are restricted to
//! source types that form a numeric ring.
//!
//! ## What's *not* here
//!
//! - **`swapL` / `swapR`**: identity in our representation — the same
//!   `Conn` answers both. No conversion function needed.
//! - **`mapped`**: requires HKT; per `doc/design.md` line 206, omit and
//!   specialize per container if needed downstream.

use core::cmp::Ordering;
use core::ops::{Add, Div, Sub};

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
#[must_use]
pub fn upper<A, B>(c: &Conn<A, B>, b: B) -> A {
    c.inner(b)
}

/// Lift a unary endofunction over `B` into one over `A` through the
/// L-pair: `a ↦ inner(f(ceil(a)))`.
///
/// The unit law `a ≤ upper1(c, id, a)` is property-tested.
#[inline]
#[must_use]
pub fn upper1<A, B, F>(c: &Conn<A, B>, f: F, a: A) -> A
where
    F: FnOnce(B) -> B,
{
    c.inner(f(c.ceil(a)))
}

/// Lift a binary function over `B` into a binary function over `A`
/// through the L-pair: `(a1, a2) ↦ inner(f(ceil(a1), ceil(a2)))`.
#[inline]
#[must_use]
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
#[must_use]
pub fn ceiling<A, B>(c: &Conn<A, B>, a: A) -> B {
    c.ceil(a)
}

/// Lift a unary endofunction over `A` into one over `B` through the
/// L-pair: `b ↦ ceil(f(inner(b)))`.
#[inline]
#[must_use]
pub fn ceiling1<A, B, F>(c: &Conn<A, B>, f: F, b: B) -> B
where
    F: FnOnce(A) -> A,
{
    c.ceil(f(c.inner(b)))
}

/// Lift a binary function over `A` into a binary function over `B`
/// through the L-pair: `(b1, b2) ↦ ceil(f(inner(b1), inner(b2)))`.
#[inline]
#[must_use]
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
#[must_use]
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
#[must_use]
pub fn lower<A, B>(c: &Conn<A, B>, b: B) -> A {
    c.inner(b)
}

/// Lift a unary endofunction over `B` into one over `A` through the
/// R-pair: `a ↦ inner(f(floor(a)))`.
///
/// The counit law `lower1(c, id, a) ≤ a` is property-tested.
#[inline]
#[must_use]
pub fn lower1<A, B, F>(c: &Conn<A, B>, f: F, a: A) -> A
where
    F: FnOnce(B) -> B,
{
    c.inner(f(c.floor(a)))
}

/// Lift a binary function over `B` into a binary function over `A`
/// through the R-pair: `(a1, a2) ↦ inner(f(floor(a1), floor(a2)))`.
#[inline]
#[must_use]
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
#[must_use]
pub fn floor<A, B>(c: &Conn<A, B>, a: A) -> B {
    c.floor(a)
}

/// Lift a unary endofunction over `A` into one over `B` through the
/// R-pair: `b ↦ floor(f(inner(b)))`.
#[inline]
#[must_use]
pub fn floor1<A, B, F>(c: &Conn<A, B>, f: F, b: B) -> B
where
    F: FnOnce(A) -> A,
{
    c.floor(f(c.inner(b)))
}

/// Lift a binary function over `A` into a binary function over `B`
/// through the R-pair: `(b1, b2) ↦ floor(f(inner(b1), inner(b2)))`.
#[inline]
#[must_use]
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
#[must_use]
pub fn minimize<A, B, C>(c: &Conn<(A, B), C>, a: A, b: B) -> C {
    c.floor((a, b))
}

// ── Two-sided helpers (Haskell `Cast.hs` §interval–median) ──────────

/// Compare the two halves of the conn-bracketed interval around `x`.
///
/// Returns `Some(Less)` when `x` lies closer to `lower1(c, id, x)`,
/// `Some(Greater)` when closer to `upper1(c, id, x)`, `Some(Equal)`
/// when `x` is the exact midpoint, and `None` when the comparison
/// is undefined (e.g. NaN-bearing source values).
///
/// Faithful port of Haskell `Cast.hs::interval`:
/// `interval c x = pcompare (x - lower1 c id x) (upper1 c id x - x)`.
///
/// **Overflow:** the body subtracts `x - lower1(c, id, x)` and
/// `upper1(c, id, x) - x`. Haskell's `Num` is arbitrary-precision;
/// Rust's signed integers wrap (release) or panic (debug). On
/// identity Conns both subtractions reduce to `x - x = 0`, so the
/// risk is zero. On non-identity Conns where the bracket is far
/// from `x`, callers driving near the type's `MIN`/`MAX` should
/// either compose through a wider source type first or stay within
/// a clamped input range.
///
/// ```rust
/// use core::cmp::Ordering;
/// use connections::conn::Conn;
/// use connections::conn::cast::interval;
/// let c: Conn<i32, i32> = Conn::identity();
/// assert_eq!(interval(&c, 7), Some(Ordering::Equal));
/// ```
#[inline]
#[must_use]
pub fn interval<A, B>(c: &Conn<A, B>, x: A) -> Option<Ordering>
where
    A: Copy + PartialOrd + Sub<Output = A>,
{
    let d_lo = x - lower1(c, |b| b, x);
    let d_hi = upper1(c, |b| b, x) - x;
    d_lo.partial_cmp(&d_hi)
}

/// Return the midpoint of the conn-bracketed interval around `x`.
///
/// Computes `lo + (hi - lo) / 2` where `lo = lower1(c, id, x)` and
/// `hi = upper1(c, id, x)`. This formulation is exact for both
/// integer and floating-point sources — Haskell's `lo/2 + hi/2`
/// loses 1 bit on odd-summed integers; the offset form does not.
///
/// **Precondition:** `lo ≤ hi`. The conns this crate ships with
/// injective `inner` (i.e. those that pass `conn_floor_le_ceil`)
/// satisfy this trivially. On a saturating conn where the
/// inner-bracket can flip (`hi < lo`), `hi - lo` underflows silently
/// on signed-integer sources and produces a meaningless value; the
/// companion predicate [`crate::property::laws::cast_midpoint_between`]
/// gates on `lo ≤ hi` for exactly this reason.
///
/// The offset form sidesteps the intermediate-sum overflow that
/// `lo/2 + hi/2` would otherwise hit on near-MAX rungs, but the
/// inner subtraction `hi - lo` can itself overflow when the bracket
/// spans the full type range — callers passing such inputs should
/// route through a wider-source conn (`compose!`) first.
///
/// ```rust
/// use connections::conn::Conn;
/// use connections::conn::cast::midpoint;
/// let c: Conn<i32, i32> = Conn::identity();
/// assert_eq!(midpoint(&c, 7), 7);
/// ```
#[inline]
#[must_use]
pub fn midpoint<A, B>(c: &Conn<A, B>, x: A) -> A
where
    A: Copy + Add<Output = A> + Sub<Output = A> + Div<Output = A> + From<u8>,
{
    let lo = lower1(c, |b| b, x);
    let hi = upper1(c, |b| b, x);
    let two = A::from(2);
    lo + (hi - lo) / two
}

/// Truncate `x` toward zero through the connection: returns
/// `c.floor(x)` when `x ≥ 0`, otherwise `c.ceil(x)`.
///
/// Faithful port of Haskell `Cast.hs::truncate`:
/// `truncate c x = if x >~ 0 then floor c x else ceiling c x`.
///
/// ```rust
/// use connections::conn::Conn;
/// use connections::conn::cast::truncate;
/// let c: Conn<i32, i32> = Conn::identity();
/// assert_eq!(truncate(&c, 5), 5);
/// assert_eq!(truncate(&c, -5), -5);
/// ```
#[inline]
#[must_use]
pub fn truncate<A, B>(c: &Conn<A, B>, x: A) -> B
where
    A: Copy + PartialOrd + From<u8>,
{
    if x >= A::from(0) {
        c.floor(x)
    } else {
        c.ceil(x)
    }
}

/// Lift a unary function `f: A → A` to operate on `B`-valued inputs
/// through the connection, with the result truncated toward zero:
/// `truncate1(c, f, x) = truncate(c, f(c.inner(x)))`.
///
/// ```rust
/// use connections::conn::Conn;
/// use connections::conn::cast::truncate1;
/// let c: Conn<i32, i32> = Conn::identity();
/// assert_eq!(truncate1(&c, |a| a + 1, 5), 6);
/// ```
#[inline]
#[must_use]
pub fn truncate1<A, B, F>(c: &Conn<A, B>, f: F, x: B) -> B
where
    A: Copy + PartialOrd + From<u8>,
    F: FnOnce(A) -> A,
{
    truncate(c, f(c.inner(x)))
}

/// Lift a binary function `f: (A, A) → A` over the connection, with
/// the result truncated toward zero:
/// `truncate2(c, f, x, y) = truncate(c, f(c.inner(x), c.inner(y)))`.
///
/// ```rust
/// use connections::conn::Conn;
/// use connections::conn::cast::truncate2;
/// let c: Conn<i32, i32> = Conn::identity();
/// assert_eq!(truncate2(&c, |a, b| a + b, 3, 4), 7);
/// ```
#[inline]
#[must_use]
pub fn truncate2<A, B, F>(c: &Conn<A, B>, f: F, x: B, y: B) -> B
where
    A: Copy + PartialOrd + From<u8>,
    F: FnOnce(A, A) -> A,
{
    truncate(c, f(c.inner(x), c.inner(y)))
}

/// Round `x` to the nearest representable value across the connection,
/// with ties broken toward zero (i.e. tie cases delegate to
/// [`truncate`]).
///
/// Faithful port of Haskell `Cast.hs::round`:
/// `Some(Greater) → ceil(x)`, `Some(Less) → floor(x)`, otherwise
/// `truncate(c, x)`.
///
/// `interval(c, x)` returns `Some(Greater)` when `x` is closer to
/// the upper rung (`d_lo > d_hi`), `Some(Less)` when closer to the
/// lower rung, and `Some(Equal)` exactly at the midpoint. The
/// fall-through `_` arm catches both `Some(Equal)` (true tie) and
/// `None`.
///
/// **NaN behavior.** When `x` is a NaN-bearing source value
/// (e.g. `ExtendedFloat::Extend(f64::NAN)`), `partial_cmp` returns
/// `None` and the result is `truncate(c, x)`, which then dispatches
/// on `x >= A::from(0)`. For NaN that comparison is `false`, so
/// `round(c, NaN) = c.ceil(NaN)` — typically `Extend(NaN)`
/// preserved through `ceil` for the ExtendedFloat conns. Callers
/// that need different NaN handling should branch upstream.
///
/// ```rust
/// use connections::conn::Conn;
/// use connections::conn::cast::round;
/// let c: Conn<i32, i32> = Conn::identity();
/// assert_eq!(round(&c, 7), 7);
/// ```
#[inline]
#[must_use]
pub fn round<A, B>(c: &Conn<A, B>, x: A) -> B
where
    A: Copy + PartialOrd + Sub<Output = A> + From<u8>,
{
    match interval(c, x) {
        Some(Ordering::Greater) => c.ceil(x),
        Some(Ordering::Less) => c.floor(x),
        _ => truncate(c, x),
    }
}

/// Lift a unary function `f: A → A` to operate on `B`-valued inputs
/// through the connection, rounded to nearest with ties toward zero:
/// `round1(c, f, x) = round(c, f(c.inner(x)))`.
///
/// ```rust
/// use connections::conn::Conn;
/// use connections::conn::cast::round1;
/// let c: Conn<i32, i32> = Conn::identity();
/// assert_eq!(round1(&c, |a| a * 2, 5), 10);
/// ```
#[inline]
#[must_use]
pub fn round1<A, B, F>(c: &Conn<A, B>, f: F, x: B) -> B
where
    A: Copy + PartialOrd + Sub<Output = A> + From<u8>,
    F: FnOnce(A) -> A,
{
    round(c, f(c.inner(x)))
}

/// Lift a binary function `f: (A, A) → A` similarly:
/// `round2(c, f, x, y) = round(c, f(c.inner(x), c.inner(y)))`.
///
/// ```rust
/// use connections::conn::Conn;
/// use connections::conn::cast::round2;
/// let c: Conn<i32, i32> = Conn::identity();
/// assert_eq!(round2(&c, |a, b| a + b, 3, 4), 7);
/// ```
#[inline]
#[must_use]
pub fn round2<A, B, F>(c: &Conn<A, B>, f: F, x: B, y: B) -> B
where
    A: Copy + PartialOrd + Sub<Output = A> + From<u8>,
    F: FnOnce(A, A) -> A,
{
    round(c, f(c.inner(x), c.inner(y)))
}

/// Birkhoff's [median](https://en.wikipedia.org/wiki/Median_algebra)
/// over a `Conn<(A, A), A>`, expressed in terms of the conn's
/// "join" (`maximize`) and "meet" (`minimize`):
///
/// ```text
/// median c x y z = (x ⊔ y) ⊓ (y ⊔ z) ⊓ (z ⊔ x)
/// ```
///
/// For the natural `ordered`-style conn (`ceil = max`, `floor = min`,
/// `inner = (x, x)`), this is the standard 3-element median.
///
/// Faithful port of Haskell `Cast.hs::median`.
///
/// ```rust
/// use connections::conn::Conn;
/// use connections::conn::cast::median;
/// fn ceil(p: (i32, i32)) -> i32 { p.0.max(p.1) }
/// fn floor(p: (i32, i32)) -> i32 { p.0.min(p.1) }
/// fn inner(x: i32) -> (i32, i32) { (x, x) }
/// let c: Conn<(i32, i32), i32> = Conn::new(ceil, inner, floor);
/// assert_eq!(median(&c, 1, 2, 3), 2);
/// ```
#[inline]
#[must_use]
pub fn median<A>(c: &Conn<(A, A), A>, x: A, y: A, z: A) -> A
where
    A: Copy,
{
    let join = |p: A, q: A| maximize(c, p, q);
    let meet = |p: A, q: A| minimize(c, p, q);
    meet(meet(join(x, y), join(y, z)), join(z, x))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::conn::float::ExtendedFloat;
    use crate::property::arb::arb_f64;
    use crate::property::laws;
    use proptest::prelude::*;

    // ── Conn bases used across the proptest blocks below ──────────
    //
    // Two bases give us:
    //   - ID_I32: Ord path, trivially identity (every lifter reduces
    //     to f(x)).
    //   - ID_EF64: ExtendedFloat<f64> path with Bot/Top/Extend(NaN);
    //     covers the lawful float wrapper (raw f64 is not Eq).
    //
    // Earlier revisions also drove the cast laws against the
    // decimal-ladder Conn `FD12FD09` for L/R-asymmetry coverage on a
    // non-trivial triple. Removed alongside the decimal ladder; the
    // asymmetry now lives in per-family tests under
    // `conn::fixed::*` / `conn::time::*`.
    const ID_I32: Conn<i32, i32> = Conn::identity();
    const ID_I64: Conn<i64, i64> = Conn::identity();
    const ID_EF64: Conn<ExtendedFloat<f64>, ExtendedFloat<f64>> = Conn::identity();

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

    // ── Sprint B: two-sided helpers (deterministic spot checks) ──

    #[test]
    fn interval_id_i32_at_value_is_equal() {
        assert_eq!(interval(&ID_I32, 7), Some(core::cmp::Ordering::Equal));
    }

    #[test]
    fn midpoint_id_i32_eq_a() {
        assert_eq!(midpoint(&ID_I32, 7), 7);
        assert_eq!(midpoint(&ID_I32, -42), -42);
    }

    #[test]
    fn round_id_i32_eq_a() {
        assert_eq!(round(&ID_I32, 7), 7);
        assert_eq!(round(&ID_I32, -42), -42);
    }

    #[test]
    fn truncate_id_pos() {
        assert_eq!(truncate(&ID_I32, 5), 5);
        assert_eq!(truncate(&ID_I32, 0), 0);
    }

    #[test]
    fn truncate_id_neg() {
        assert_eq!(truncate(&ID_I32, -5), -5);
    }

    #[test]
    fn truncate1_id_id_is_id() {
        assert_eq!(truncate1(&ID_I32, |a| a, 42), 42);
    }

    #[test]
    fn round1_id_id_is_id() {
        assert_eq!(round1(&ID_I32, |a| a, 42), 42);
    }

    #[test]
    fn truncate2_id_add_pair() {
        assert_eq!(truncate2(&ID_I32, |a, b| a + b, 3, 4), 7);
        assert_eq!(truncate2(&ID_I32, |a, b| a - b, 3, 4), -1);
    }

    #[test]
    fn round2_id_add_pair() {
        assert_eq!(round2(&ID_I32, |a, b| a + b, 3, 4), 7);
        assert_eq!(round2(&ID_I32, |a, b| a * b, 3, 4), 12);
    }

    #[test]
    fn median_three_equal_ordered() {
        assert_eq!(median(&ORDERED_PAIR, 7, 7, 7), 7);
    }

    #[test]
    fn median_two_equal_ordered() {
        assert_eq!(median(&ORDERED_PAIR, 3, 3, 5), 3);
        assert_eq!(median(&ORDERED_PAIR, 5, 3, 3), 3);
    }

    #[test]
    fn median_distinct_ordered() {
        assert_eq!(median(&ORDERED_PAIR, 1, 2, 3), 2);
        assert_eq!(median(&ORDERED_PAIR, 3, 1, 2), 2);
        assert_eq!(median(&ORDERED_PAIR, 2, 3, 1), 2);
        assert_eq!(median(&ORDERED_PAIR, 5, 1, 9), 5);
    }

    // ── Proptest blocks: predicates × conn bases ──────────────────

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

        // ── maximize / minimize over `ORDERED_PAIR` (random pairs) ─

        #[test]
        fn maximize_eq_ceiling_random(a: i32, b: i32) {
            prop_assert!(laws::cast_maximize_eq_ceiling(&ORDERED_PAIR, a, b));
        }

        #[test]
        fn minimize_eq_floor_random(a: i32, b: i32) {
            prop_assert!(laws::cast_minimize_eq_floor(&ORDERED_PAIR, a, b));
        }

        // ── Sprint B: two-sided helpers ────────────────────────────
        //
        // Identity Conns have `lower1(c, id, x) == upper1(c, id, x)
        // == x`, so the inner subtractions in `interval` reduce to
        // `x - x = 0`, the offset in `midpoint` reduces to `0 / 2 =
        // 0`, and no arithmetic between distinct values occurs.
        // Every Sprint-B predicate driven over `ID_I32` / `ID_I64`
        // is therefore safe over the full primitive range. When
        // non-identity Conn coverage lands (separate sprint), the
        // proptests for those bases will need clamps appropriate to
        // the bracket width.

        #[test]
        fn interval_at_midpoint_id_i32(a: i32) {
            prop_assert!(laws::cast_interval_at_midpoint_eq_or_none(&ID_I32, a));
        }

        #[test]
        fn interval_at_midpoint_id_i64(a: i64) {
            prop_assert!(laws::cast_interval_at_midpoint_eq_or_none(&ID_I64, a));
        }

        #[test]
        fn midpoint_between_id_i32(a: i32) {
            prop_assert!(laws::cast_midpoint_between(&ID_I32, a));
        }

        #[test]
        fn midpoint_between_id_i64(a: i64) {
            prop_assert!(laws::cast_midpoint_between(&ID_I64, a));
        }

        #[test]
        fn round_picks_endpoint_id_i32(a: i32) {
            prop_assert!(laws::cast_round_picks_endpoint(&ID_I32, a));
        }

        #[test]
        fn round_picks_endpoint_id_i64(a: i64) {
            prop_assert!(laws::cast_round_picks_endpoint(&ID_I64, a));
        }

        #[test]
        fn truncate_picks_endpoint_id_i32(a: i32) {
            prop_assert!(laws::cast_truncate_picks_endpoint(&ID_I32, a));
        }

        #[test]
        fn truncate_picks_endpoint_id_i64(a: i64) {
            prop_assert!(laws::cast_truncate_picks_endpoint(&ID_I64, a));
        }

        #[test]
        fn truncate_toward_zero_id_i32(a: i32) {
            prop_assert!(laws::cast_truncate_toward_zero(&ID_I32, a));
        }

        #[test]
        fn truncate_toward_zero_id_i64(a: i64) {
            prop_assert!(laws::cast_truncate_toward_zero(&ID_I64, a));
        }

        #[test]
        fn round1_id_unit_id_i32(a: i32) {
            prop_assert!(laws::cast_round1_id_unit(&ID_I32, a));
        }

        #[test]
        fn truncate1_id_unit_id_i32(a: i32) {
            prop_assert!(laws::cast_truncate1_id_unit(&ID_I32, a));
        }

        // Birkhoff median axioms over ORDERED_PAIR. The fn signature
        // is `<A: Copy>(c: &Conn<(A, A), A>, ...)`, so it would
        // compile on `ExtendedFloat<f64>` — coverage there is
        // deferred only because no `ORDERED_PAIR_EF64` fixture
        // exists. A future sprint can add one to extend median
        // coverage to NaN-bearing inputs.

        #[test]
        fn median_idempotent_ordered(x: i32, y: i32) {
            prop_assert!(laws::cast_median_idempotent(&ORDERED_PAIR, x, y));
        }

        #[test]
        fn median_rotate_ordered(x: i32, y: i32, z: i32) {
            prop_assert!(laws::cast_median_rotate(&ORDERED_PAIR, x, y, z));
        }

        #[test]
        fn median_swap_yz_ordered(x: i32, y: i32, z: i32) {
            prop_assert!(laws::cast_median_swap_yz(&ORDERED_PAIR, x, y, z));
        }
    }
}
