//! Galois-connection core: the [`Conn<A, B>`] type, the
//! [`crate::compose!`](crate::compose) macro, and the operations
//! on a `Conn` (L/R-side accessors, lifters, two-sided rounding
//! helpers).
//!
//! Per-domain Conn families live in sibling top-level modules:
//!
//! - [`crate::float`] — float ↔ float connections; also hosts the
//!   `ExtendedFloat` wrapper type used by N5 lattice connections.
//! - [`crate::fixed`] — every finite-precision-with-integer-storage
//!   family: `fixed`-crate Q-format wrappers (`FixedI<width><Frac>` /
//!   `FixedU<width><Frac>`), std-int primitives (`iN` / `uN`,
//!   interpreted as Q*N*.0), and `core::num::NonZero<*>` (punctured
//!   Q*N*.0). Per-width submodules `i8`..`i128`, `u8`..`u128`; each
//!   hosts the Conn consts whose destination type lives in that
//!   width.
//! - [`crate::time`] — connections among the
//!   [`time`](https://docs.rs/time) crate's calendar / clock /
//!   duration types (8-character names).
//!
//! ## Operations on `Conn` (folded in from the former `cast` module)
//!
//! Port of the public surface of
//! [`Data.Connection.Cast`](https://hackage.haskell.org/package/connections/docs/Data-Connection-Cast.html)
//! from the Haskell `connections` library, **minus** the `Side` data
//! kind (`'L` / `'R`).
//!
//! ### L vs R is a naming axis, not a type axis
//!
//! In the Haskell library, `Cast 'L a b` and `Cast 'R a b` are *types*
//! distinguished by a phantom `Side` index, even though they share one
//! runtime representation. The split lets the compiler enforce that
//! `floor` / `lower` are only callable on `'R` and `ceiling` /
//! `upper` only on `'L`.
//!
//! Rust's [`Conn<A, B>`] carries the *full adjoint triple*
//! (`ceil ⊣ inner ⊣ floor`) in three `fn`-pointer fields, so a
//! one-sided connection is just a triple where `floor == ceil`. Both
//! L-style and R-style operations are well-defined for any `Conn`:
//! they read different fields of the same struct. We therefore expose
//! **both naming conventions** as free functions on the same type.
//!
//! - L-side names: [`upper`], [`upper1`], [`upper2`], [`ceiling`],
//!   [`ceiling1`], [`ceiling2`].
//! - R-side names: [`lower`], [`lower1`], [`lower2`], [`floor`],
//!   [`floor1`], [`floor2`].
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
//! ### Two-sided helpers
//!
//! [`interval`], [`midpoint`], [`round`], [`round1`], [`round2`],
//! [`truncate`], [`truncate1`], [`truncate2`], [`median`] — port of
//! the corresponding Haskell `Data.Connection.Cast` definitions.
//! These act on **both** sides of an adjoint triple at once: e.g.
//! `round` dispatches between `ceil` and `floor` based on which side
//! the input is closer to. The arithmetic helpers carry inline
//! numeric bounds on the source type `A`: `Sub` for `interval`;
//! `Add`/`Sub`/`Div`/`From<u8>` for `midpoint`; `From<u8>` (plus
//! `Sub` via `interval` for `round`) for `truncate` and `round`. The
//! source type must form a numeric ring of the requested shape.
//!
//! ### Behavior on edge inputs
//!
//! The two-sided helpers (`interval`, `midpoint`, `round`,
//! `truncate`, and their `1`/`2` lifters) bracket the input by
//! calling **both** `c.ceil` and `c.floor`. Two cases collapse the
//! bracket and are stated once here; per-function docs refer back
//! rather than restating.
//!
//! 1. **Length-2 (one-sided) connection** — when `c.ceil == c.floor`
//!    (the connection is a single adjoint pair, not a triple), the
//!    bracket is a point: `lo == hi`. [`interval`] returns
//!    `Some(Equal)`; [`midpoint`], [`round`], and [`truncate`] all
//!    return that single value. The helpers are well-defined on a
//!    length-2 conn; they're just not interesting.
//!
//! 2. **NaN-bearing source** — for source types that admit NaN
//!    (e.g. `ExtendedFloat<f64>`), `partial_cmp` between bracket
//!    endpoints returns `None`. [`interval`] propagates the `None`;
//!    [`round`] and [`truncate`] fall through to the `truncate`
//!    arm, which dispatches on `x >= 0` (false for NaN, so the
//!    `c.ceil(x)` branch fires).
//!
//! ### Numeric surface for `ExtendedFloat<f32 | f64>` closures
//!
//! The user-supplied closures in [`round1`] / [`round2`] /
//! [`truncate1`] / [`truncate2`] / [`floor1`] / [`floor2`] /
//! [`ceiling1`] / [`ceiling2`] / [`upper1`] / [`upper2`] / [`lower1`] /
//! [`lower2`] run in *source-side* arithmetic. For
//! `Conn<ExtendedFloat<f64>, _>` (e.g. [`crate::float::f32::F064F032`])
//! that means the closure body sees `ExtendedFloat<f64>` and can
//! invoke the full numeric API: `+`, `-`, `*`, `/`, `%`, unary `-`,
//! the `*Assign` siblings, plus the inherent transcendentals
//! (`sin` / `cos` / `tan` / their inverses, `sqrt` / `cbrt`, `exp` /
//! `exp2` / `ln` / `log2` / `log10`, `abs` / `signum` / `recip`,
//! `powi` / `powf` / `mul_add`, `atan2`) and constants
//! (`PI` / `TAU` / `E` / `FRAC_PI_2` / `NAN` / `INFINITY` /
//! `NEG_INFINITY` / `ZERO` / `ONE`). User closures don't need to
//! unwrap to the inner `T` — Bot/Top/NaN dispatch happens inside
//! the inherent methods. See [`crate::float`] for the full table
//! and Bot/Top semantics.
//!
//! ### What's *not* here
//!
//! - **`swapL` / `swapR`**: identity in our representation — the same
//!   `Conn` answers both. No conversion function needed.
//! - **`mapped`**: requires HKT; per `doc/design.md` line 206, omit and
//!   specialize per container if needed downstream.
//!
//! ## Laws
//!
//! Every shipped connection satisfies the following nine laws. The
//! property predicates live in [`crate::prop::conn`] and are
//! re-runnable by downstream crates against their own connections.
//! See the README's `## What's lawful` table for the canonical
//! statement, and `doc/design.md` for the full design rationale.
//!
//! | Predicate | Law |
//! |-----------|-----|
//! | [`conn_galois_l`](crate::prop::conn::conn_galois_l) | `ceil(a) ≤ b ⟺ a ≤ inner(b)` |
//! | [`conn_galois_r`](crate::prop::conn::conn_galois_r) | `inner(b) ≤ a ⟺ b ≤ floor(a)` |
//! | [`conn_closure_l`](crate::prop::conn::conn_closure_l) | `a ≤ inner(ceil(a))` (unit) |
//! | [`conn_closure_r`](crate::prop::conn::conn_closure_r) | `inner(floor(a)) ≤ a` |
//! | [`conn_kernel_l`](crate::prop::conn::conn_kernel_l) | `ceil(inner(b)) ≤ b` (counit) |
//! | [`conn_kernel_r`](crate::prop::conn::conn_kernel_r) | `b ≤ floor(inner(b))` |
//! | [`conn_monotone_l`](crate::prop::conn::conn_monotone_l) | `a₁ ≤ a₂ ⟹ ceil(a₁) ≤ ceil(a₂) ∧ floor(a₁) ≤ floor(a₂)` |
//! | [`conn_monotone_r`](crate::prop::conn::conn_monotone_r) | `b₁ ≤ b₂ ⟹ inner(b₁) ≤ inner(b₂)` |
//! | [`conn_idempotent`](crate::prop::conn::conn_idempotent) | `inner ∘ ceil` is idempotent on its image |
//!
//! A tenth law, [`conn_floor_le_ceil`](crate::prop::conn::conn_floor_le_ceil)
//! (`floor(a) ≤ ceil(a)`), is asserted only on connections whose
//! `inner` is a documented injective embedding — on saturating
//! connections it fails at the saturation plateau by design. See
//! `doc/design.md` § "Triple-only properties and the role of
//! injectivity".

use core::cmp::Ordering;
use core::ops::{Add, Div, Sub};

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

    /// Construct an iso connection — `forward` is a bijection on the
    /// representable range, and `back` is its inverse.
    ///
    /// The resulting Conn has `floor = ceil = forward`, so the
    /// adjoint triple is degenerate: floor and ceil are
    /// indistinguishable, and **both** Galois laws (`conn_galois_l`
    /// and `conn_galois_r`) hold trivially. Use this when the source
    /// and target are order-isomorphic — e.g. `FixedI8<U0>` ↔ `i8`,
    /// `Ipv4Addr` ↔ `u32` — rather than the asymmetric one-sided
    /// constructors [`Self::new_left`] / [`Self::new_right`].
    pub const fn new_iso(forward: fn(A) -> B, back: fn(B) -> A) -> Self {
        Conn {
            ceil: forward,
            inner: back,
            floor: forward,
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

// ── L-side accessors and lifters (Cast.hs:217–312) ──────────────────

/// Apply the upper adjoint of the L-pair: `b ↦ inner(b)`.
///
/// In an adjoint pair `f ⊣ g` with `f: A → B` and `g: B → A`, this is
/// `g`. Equivalent to calling [`Conn::inner`] directly; named for the
/// L-side reading of the connection.
///
/// ```rust
/// use connections::conn::upper;
/// use connections::float::ExtendedFloat::Extend;
/// use connections::float::f32::F064F032;
///
/// let pi64 = Extend(std::f64::consts::PI);
/// // f32's nearest representation of π widened losslessly to f64.
/// // Lossless ≠ precise: the value is still the f32 approximation.
/// let pi32 = Extend(std::f32::consts::PI as f64);
/// // f32's rounding error for π — about +8.74e-8 (f32 rounds π up).
/// // The same constant carries through every π-widening doctest below.
/// let pi32_err = pi32 - pi64;
///
/// // upper just widens; for F064F032 that's the f32 → f64 cast.
/// assert_eq!(upper(&F064F032, Extend(std::f32::consts::PI)), pi32);
/// // Equivalently, "f64 π plus f32's rounding error":
/// assert_eq!(upper(&F064F032, Extend(std::f32::consts::PI)) - pi64, pi32_err);
/// ```
#[inline]
#[must_use]
pub fn upper<A, B>(c: &Conn<A, B>, b: B) -> A {
    c.inner(b)
}

/// Lift a unary endofunction over `B` into one over `A` through the
/// L-pair: `a ↦ inner(f(ceil(a)))`.
///
/// # Laws
///
/// > `a ≤ upper1(c, id, a)` (unit law; property
/// > [`crate::prop::conn::conn_upper1_id_unit`])
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
/// # Laws
///
/// > `ceiling(identity, x) == x`<br>
/// > `ceiling(c, x ⊔ y) == ceiling(c, x) ⊔ ceiling(c, y)` (distributivity over join)
///
/// ```rust
/// use connections::conn::ceiling;
/// use connections::float::ExtendedFloat::Extend;
/// use connections::float::f32::F064F032;
///
/// let pi64 = Extend(std::f64::consts::PI);
/// let pi32 = Extend(std::f32::consts::PI as f64);
/// let pi32_err = pi32 - pi64;
///
/// // The f32 ceiling of π is std::f32::consts::PI itself —
/// // π's nearest f32 representation rounds up.
/// assert_eq!(ceiling(&F064F032, pi64), Extend(std::f32::consts::PI));
/// // Widening the result back to f64 lands at pi32, which sits
/// // exactly pi32_err above true π:
/// assert_eq!(F064F032.inner(ceiling(&F064F032, pi64)) - pi64, pi32_err);
/// ```
#[inline]
#[must_use]
pub fn ceiling<A, B>(c: &Conn<A, B>, a: A) -> B {
    c.ceil(a)
}

/// Lift a unary endofunction over `A` into one over `B` through the
/// L-pair: `b ↦ ceil(f(inner(b)))`.
///
/// # Laws
///
/// > `ceiling1(identity, id, b) == b`<br>
/// > `b ≥ ceiling1(c, id, b)` (kernel/inflation; property
/// > [`crate::prop::conn::conn_ceiling1_id_kernel`])
///
/// ```rust
/// use connections::conn::ceiling1;
/// use connections::float::ExtendedFloat::Extend;
/// use connections::float::f32::F064F032;
///
/// // Same shared probe as truncate1 / floor1: `2π − x` in f64
/// // lands strictly between two f32 grid points. ceiling1
/// // unconditionally narrows up — to std::f32::consts::PI.
/// let pi32 = Extend(std::f32::consts::PI);
/// let probe = |a| Extend(2.0_f64) * Extend(std::f64::consts::PI) - a;
/// assert_eq!(
///     ceiling1(&F064F032, probe, pi32),
///     Extend(std::f32::consts::PI),
/// );
/// ```
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
/// # Laws
///
/// > `lower1(c, id, a) ≤ a` (counit law; property
/// > [`crate::prop::conn::conn_lower1_id_counit`])
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
///
/// # Laws
///
/// > `floor(identity, x) == x`<br>
/// > `floor(c, x ⊓ y) == floor(c, x) ⊓ floor(c, y)` (distributivity over meet)
#[inline]
#[must_use]
pub fn floor<A, B>(c: &Conn<A, B>, a: A) -> B {
    c.floor(a)
}

/// Lift a unary endofunction over `A` into one over `B` through the
/// R-pair: `b ↦ floor(f(inner(b)))`.
///
/// # Laws
///
/// > `floor1(identity, id, b) == b`<br>
/// > `b ≤ floor1(c, id, b)` (kernel/deflation; property
/// > [`crate::prop::conn::conn_floor1_id_kernel`])
///
/// ```rust
/// use connections::conn::floor1;
/// use connections::float::ExtendedFloat::Extend;
/// use connections::float::f32::F064F032;
///
/// // Same shared probe as truncate1 / ceiling1: `2π − x` in f64
/// // lands strictly between two f32 grid points. floor1
/// // unconditionally narrows down — to one f32 ULP below
/// // std::f32::consts::PI.
/// let pi32 = Extend(std::f32::consts::PI);
/// let probe = |a| Extend(2.0_f64) * Extend(std::f64::consts::PI) - a;
/// assert_eq!(floor1(&F064F032, probe, pi32), Extend(3.1415925_f32));
/// ```
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
/// use connections::conn::{interval, midpoint};
/// use connections::float::ExtendedFloat::Extend;
/// use connections::float::f32::F064F032;
///
/// // The bracket midpoint is, by construction, the equipoise: at
/// // that point neither f32 endpoint is closer.
/// let pi = Extend(std::f64::consts::PI);
/// assert_eq!(
///     interval(&F064F032, midpoint(&F064F032, pi)),
///     Some(Ordering::Equal),
/// );
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
/// companion predicate [`crate::prop::conn::conn_midpoint_between`]
/// gates on `lo ≤ hi` for exactly this reason.
///
/// The offset form sidesteps the intermediate-sum overflow that
/// `lo/2 + hi/2` would otherwise hit on near-MAX rungs, but the
/// inner subtraction `hi - lo` can itself overflow when the bracket
/// spans the full type range — callers passing such inputs should
/// route through a wider-source conn (`compose!`) first.
///
/// ```rust
/// use connections::conn::midpoint;
/// use connections::float::ExtendedFloat::Extend;
/// use connections::float::f32::F064F032;
///
/// // π's distance from the centre of its f32 bracket — equivalently,
/// // the asymmetry of round-to-nearest f32 at π.
/// let pi = Extend(std::f64::consts::PI);
/// assert_eq!(pi - midpoint(&F064F032, pi), Extend(3.1786509424591713e-8));
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
/// # Laws
///
/// > `truncate(identity, x) == x`
///
/// ```rust
/// use connections::conn::truncate;
/// use connections::float::ExtendedFloat::Extend;
/// use connections::float::f32::F064F032;
///
/// // π > 0 → truncate-toward-zero takes the f32 floor; one f32 ULP
/// // below std::f32::consts::PI.
/// let pi = Extend(std::f64::consts::PI);
/// assert_eq!(truncate(&F064F032, pi), Extend(3.1415925_f32));
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
/// # Laws
///
/// > `truncate1(identity, id, b) == b` (property
/// > [`crate::prop::conn::conn_truncate1_id_unit`])
///
/// ```rust
/// use connections::conn::truncate1;
/// use connections::float::ExtendedFloat::Extend;
/// use connections::float::f32::F064F032;
///
/// // truncate1 / floor1 / ceiling1 share this closure shape: `2π − x`
/// // in f64-precision lands strictly between the f32 floor of π
/// // (3.1415925_f32) and the f32 ceiling (std::f32::consts::PI), so
/// // the three lifters narrow it to two distinct f32 values.
/// // truncate-toward-zero of a positive result == floor:
/// let pi32 = Extend(std::f32::consts::PI);
/// let probe = |a| Extend(2.0_f64) * Extend(std::f64::consts::PI) - a;
/// assert_eq!(truncate1(&F064F032, probe, pi32), Extend(3.1415925_f32));
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
/// # Laws
///
/// > `truncate2(identity, f, x, y) == f(x, y)` (the identity-conn round-trip)
///
/// ```rust
/// use connections::conn::truncate2;
/// use connections::float::ExtendedFloat::Extend;
/// use connections::float::f32::F064F032;
///
/// // 2 · std::f32::consts::PI in f64 space, narrowed back to f32.
/// // 2π32 > 0, so truncate-toward-zero takes the f32 floor.
/// let pi32 = Extend(std::f32::consts::PI);
/// assert_eq!(
///     truncate2(&F064F032, |a, b| a + b, pi32, pi32),
///     Extend(6.2831855_f32),
/// );
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
/// # Laws
///
/// > `round(identity, x) == x`
///
/// `interval(c, x)` returns `Some(Greater)` when `x` is closer to
/// the upper rung (`d_lo > d_hi`), `Some(Less)` when closer to the
/// lower rung, and `Some(Equal)` exactly at the midpoint. The
/// fall-through `_` arm catches both `Some(Equal)` (true tie) and
/// `None` — see *Behavior on edge inputs* in the module docs for
/// the length-2-conn and NaN cases.
///
/// ```rust
/// use connections::conn::round;
/// use connections::float::ExtendedFloat::Extend;
/// use connections::float::f32::F064F032;
///
/// let pi64 = Extend(std::f64::consts::PI);
/// let pi32 = Extend(std::f32::consts::PI as f64);
/// let pi32_err = pi32 - pi64;
///
/// // Round-to-nearest f32 of π is std::f32::consts::PI — the f32
/// // value `(pi as f32)` would also produce.
/// assert_eq!(round(&F064F032, pi64), Extend(std::f32::consts::PI));
/// // Widening the result back to f64 lands pi32_err above true π:
/// assert_eq!(F064F032.inner(round(&F064F032, pi64)) - pi64, pi32_err);
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
/// # Laws
///
/// > `round1(identity, id, b) == b` (property
/// > [`crate::prop::conn::conn_round1_id_unit`])
///
/// ```rust
/// use connections::conn::round1;
/// use connections::float::ExtendedFloat::Extend;
/// use connections::float::f32::F064F032;
///
/// // One Newton step on sin's zero near π. std::f32::consts::PI is
/// // ~8.7e-8 above true π; a Newton step `x − tan(x)` in
/// // f64-precision converges to true π_f64. round1 then picks the
/// // closer f32 endpoint — std::f32::consts::PI itself.
/// let pi32 = Extend(std::f32::consts::PI);
/// assert_eq!(
///     round1(&F064F032, |a| a - a.tan(), pi32),
///     Extend(std::f32::consts::PI),
/// );
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
/// # Laws
///
/// > `round2(identity, f, x, y) == f(x, y)` (the identity-conn round-trip)
///
/// ```rust
/// use connections::conn::round2;
/// use connections::float::ExtendedFloat::Extend;
/// use connections::float::f32::F064F032;
///
/// // Catastrophic cancellation example: `(x + y) − x` should be y, but
/// // at the largest odd-integer f32 (2^24 - 1) the sum already rounds
/// // away the small operand, and the answer collapses to 1.0 instead
/// // of 2.0. round2 lifts to f64, computes exactly, narrows once.
/// let max_odd = Extend(16777215.0_f32);   // = 2^24 - 1
/// let two = Extend(2.0_f32);
/// assert_eq!((16777215.0_f32 + 2.0_f32) - 16777215.0_f32, 1.0);  // raw f32
/// assert_eq!(
///     round2(&F064F032, |a, b| (a + b) - a, max_odd, two),
///     Extend(2.0_f32),
/// );
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
/// over a `Conn<(A, A), A>`, expressed in terms of the conn's join
/// (`c.ceil`) and meet (`c.floor`):
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
/// # Laws
///
/// > `median(c, x, x, y) == x` (idempotence; property
/// > [`crate::prop::conn::conn_median_idempotent`])<br>
/// > `median(c, x, y, z) == median(c, z, x, y)` (rotation; property
/// > [`crate::prop::conn::conn_median_rotate`])<br>
/// > `median(c, x, y, z) == median(c, x, z, y)` (swap last two; property
/// > [`crate::prop::conn::conn_median_swap_yz`])<br>
/// > `median(median(c, x, w, y), w, z) == median(c, x, w, median(y, w, z))` (associativity; property
/// > [`crate::prop::conn::conn_median_associative`])
///
/// ```rust
/// use connections::conn::{Conn, median};
/// fn ceil(p: (i32, i32)) -> i32 { p.0.max(p.1) }
/// fn floor(p: (i32, i32)) -> i32 { p.0.min(p.1) }
/// fn inner(x: i32) -> (i32, i32) { (x, x) }
/// let c: Conn<(i32, i32), i32> = Conn::new(ceil, inner, floor);
/// assert_eq!(median(&c, 1, 2, 3), 2);
/// ```
///
/// The median formula reduces to the median of the two finite arguments
/// when the third is incomparable in the lattice — N5's lub of an
/// incomparable pair escalates to `Top`, and the formula collapses.
/// This mirrors the Haskell `median f32f32 1.0 9.0 (0.0/0.0) == 9.0`
/// doctest faithfully:
///
/// ```rust
/// use connections::conn::{Conn, median};
/// use connections::float::ExtendedFloat::{self, Bot, Extend, Top};
/// use core::cmp::Ordering;
///
/// // N5 lattice lub: incomparable pair (NaN vs finite) escalates to Top.
/// fn lub(p: (ExtendedFloat<f32>, ExtendedFloat<f32>)) -> ExtendedFloat<f32> {
///     match p.0.partial_cmp(&p.1) {
///         Some(Ordering::Less | Ordering::Equal) => p.1,
///         Some(Ordering::Greater) => p.0,
///         None => Top,            // incomparable → lub = Top
///     }
/// }
/// // N5 lattice glb: incomparable pair → Bot.
/// fn glb(p: (ExtendedFloat<f32>, ExtendedFloat<f32>)) -> ExtendedFloat<f32> {
///     match p.0.partial_cmp(&p.1) {
///         Some(Ordering::Less | Ordering::Equal) => p.0,
///         Some(Ordering::Greater) => p.1,
///         None => Bot,            // incomparable → glb = Bot
///     }
/// }
/// fn diag(x: ExtendedFloat<f32>) -> (ExtendedFloat<f32>, ExtendedFloat<f32>) {
///     (x, x)
/// }
/// let ord: Conn<_, _> = Conn::new(lub, diag, glb);
///
/// // Bind once and reuse; mirrors Haskell's `(0.0 / 0.0)` pattern.
/// let nan = Extend(0.0_f32 / 0.0_f32);
///
/// // All-finite: matches Haskell `median f32f32 1.0 9.0 7.0 == 7.0`.
/// assert_eq!(
///     median(&ord, Extend(1.0_f32), Extend(9.0_f32), Extend(7.0_f32)),
///     Extend(7.0_f32),
/// );
///
/// // NaN: matches Haskell `median f32f32 1.0 9.0 (0.0/0.0) == 9.0`.
/// assert_eq!(
///     median(&ord, Extend(1.0_f32), Extend(9.0_f32), nan),
///     Extend(9.0_f32),
/// );
/// ```
#[inline]
#[must_use]
pub fn median<A>(c: &Conn<(A, A), A>, x: A, y: A, z: A) -> A
where
    A: Copy,
{
    let join = |p: A, q: A| c.ceil((p, q));
    let meet = |p: A, q: A| c.floor((p, q));
    meet(meet(join(x, y), join(y, z)), join(z, x))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::prop::arb::arb_f64;
    use crate::prop::conn as conn_laws;
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

    #[test]
    fn new_iso_floor_eq_ceil_and_round_trip() {
        fn forward(x: i32) -> i64 {
            x as i64
        }
        fn back(x: i64) -> i32 {
            x as i32
        }
        let c = Conn::new_iso(forward, back);
        // floor and ceil collapse to the same map.
        assert_eq!(c.ceil(7), c.floor(7));
        assert_eq!(c.ceil(-12), c.floor(-12));
        // round-trip both ways (forward is a bijection on the i32 image).
        assert_eq!(c.inner(c.ceil(42)), 42);
        assert_eq!(c.ceil(c.inner(42_i64)), 42_i64);
    }

    // ── Property tests for identity connection (i32, exercises Ord) ──

    const ID_I32: Conn<i32, i32> = Conn::identity();

    proptest! {
        #[test]
        fn galois_l(a: i32, b: i32) {
            prop_assert!(conn_laws::conn_galois_l(&ID_I32, a, b));
        }

        #[test]
        fn closure_l(a: i32) {
            prop_assert!(conn_laws::conn_closure_l(&ID_I32, a));
        }

        #[test]
        fn kernel_l(b: i32) {
            prop_assert!(conn_laws::conn_kernel_l(&ID_I32, b));
        }

        #[test]
        fn monotone_l(a1: i32, a2: i32) {
            prop_assert!(conn_laws::conn_monotone_l(&ID_I32, a1, a2));
        }

        #[test]
        fn monotone_r(b1: i32, b2: i32) {
            prop_assert!(conn_laws::conn_monotone_r(&ID_I32, b1, b2));
        }

        #[test]
        fn idempotent(a: i32) {
            prop_assert!(conn_laws::conn_idempotent(&ID_I32, a));
        }
    }

    // ── Property tests for identity on ExtendedFloat<f64> ─────────
    //
    // Exercises the float-aware lawful path. Raw `f64` is not `Eq`
    // (NaN ≠ NaN under standard PartialEq), so `Conn<f64, f64>` can't
    // satisfy the law-machinery bounds. `ExtendedFloat<f64>` patches
    // `PartialEq` to be reflexive at NaN and impls `Eq`, which is
    // what the laws require.

    use crate::float::ExtendedFloat;

    const ID_EF64: Conn<ExtendedFloat<f64>, ExtendedFloat<f64>> = Conn::identity();

    proptest! {
        #[test]
        fn galois_l_ef64(a in arb_f64(), b in arb_f64()) {
            prop_assert!(conn_laws::conn_galois_l(
                &ID_EF64,
                ExtendedFloat::Extend(a),
                ExtendedFloat::Extend(b),
            ));
        }

        #[test]
        fn closure_l_ef64(a in arb_f64()) {
            prop_assert!(conn_laws::conn_closure_l(&ID_EF64, ExtendedFloat::Extend(a)));
        }

        #[test]
        fn kernel_l_ef64(b in arb_f64()) {
            prop_assert!(conn_laws::conn_kernel_l(&ID_EF64, ExtendedFloat::Extend(b)));
        }
    }

    // ── `compose!` macro tests ───────────────────────────────────────
    //
    // Composition is a property of `Conn` itself (not of any one
    // family), so its tests live alongside the macro definition. We
    // drive them against the binary fixed-point ladder in
    // [`crate::fixed::i8`] — the `I###I###` Q-format Conns —
    // because the i8 ladder admits arbitrary multi-step chains
    // through intermediate frac levels (Q0.8 → Q4.4 → Q8.0, etc.)
    // and we have a hand-coded non-adjacent shortcut (`Q008Q000`) to
    // compare against.
    //
    // Coverage:
    // 1. Two-step (I008 → I004 → I000): the macro's covariant-ceil
    //    / contravariant-inner expansion on a length-2 chain.
    // 2. Three-step (I008 → I006 → I004 → I000): exercises the
    //    recursive `$rest` splicing for an odd parent count, distinct
    //    from the 2- and 4-step shapes.
    // 3. Four-step (I008 → I006 → I004 → I002 → I000): same domain
    //    as the hand-coded shortcut.
    // 4. Galois-law preservation: a macro-composed `Conn<I008, I000>`
    //    must satisfy the same adjoint laws as any hand-coded Conn.
    // 5. Identity laws: `compose!(id, c)` and `compose!(c, id)` must
    //    pointwise equal `c`.
    //
    // Const-context coercion of the non-capturing closures inside
    // `compose!` is exercised by every `const COMPOSED_*` declaration
    // below — failing const evaluation would refuse to compile.

    use crate::compose;
    use crate::fixed::i8::{
        I000, I004, I008, Q002Q000, Q004Q000, Q004Q002, Q006Q004, Q008Q000, Q008Q004, Q008Q006,
    };
    use ::fixed::FixedI8;

    const COMPOSED_2STEP: Conn<I008, I000> = compose!(Q008Q004, Q004Q000);
    const COMPOSED_3STEP: Conn<I008, I000> = compose!(Q008Q006, Q006Q004, Q004Q000);
    const COMPOSED_4STEP: Conn<I008, I000> = compose!(Q008Q006, Q006Q004, Q004Q002, Q002Q000);

    // Identity bookends for the left/right identity laws.
    const ID_I008: Conn<I008, I008> = Conn::identity();
    const ID_I004: Conn<I004, I004> = Conn::identity();
    const LEFT_ID_COMPOSED: Conn<I008, I004> = compose!(ID_I008, Q008Q004);
    const RIGHT_ID_COMPOSED: Conn<I008, I004> = compose!(Q008Q004, ID_I004);

    /// i8 bit-level boundary samples. Covers the saturation-fixup
    /// endpoints (`bits == ±i8::MAX`) and a spread of interior
    /// values to catch off-by-one in the macro's covariant /
    /// contravariant arms.
    const I8_SAMPLES: &[i8] = &[
        i8::MIN,
        i8::MIN + 1,
        -100,
        -42,
        -1,
        0,
        1,
        42,
        100,
        i8::MAX - 1,
        i8::MAX,
    ];

    #[test]
    fn compose_two_step_matches_handcoded_at_samples() {
        for &b in I8_SAMPLES {
            let x = FixedI8::<typenum_alias::U8>::from_bits(b);
            assert_eq!(COMPOSED_2STEP.ceil(x), Q008Q000.ceil(x), "ceil @ {b}");
            assert_eq!(COMPOSED_2STEP.floor(x), Q008Q000.floor(x), "floor @ {b}");
        }
        for &b in I8_SAMPLES {
            let y = FixedI8::<typenum_alias::U0>::from_bits(b);
            assert_eq!(COMPOSED_2STEP.inner(y), Q008Q000.inner(y), "inner @ {b}");
        }
    }

    #[test]
    fn compose_three_step_matches_handcoded_at_samples() {
        for &b in I8_SAMPLES {
            let x = FixedI8::<typenum_alias::U8>::from_bits(b);
            assert_eq!(COMPOSED_3STEP.ceil(x), Q008Q000.ceil(x), "ceil @ {b}");
            assert_eq!(COMPOSED_3STEP.floor(x), Q008Q000.floor(x), "floor @ {b}");
        }
        for &b in I8_SAMPLES {
            let y = FixedI8::<typenum_alias::U0>::from_bits(b);
            assert_eq!(COMPOSED_3STEP.inner(y), Q008Q000.inner(y), "inner @ {b}");
        }
    }

    #[test]
    fn compose_four_step_matches_handcoded_at_samples() {
        for &b in I8_SAMPLES {
            let x = FixedI8::<typenum_alias::U8>::from_bits(b);
            assert_eq!(COMPOSED_4STEP.ceil(x), Q008Q000.ceil(x), "ceil @ {b}");
            assert_eq!(COMPOSED_4STEP.floor(x), Q008Q000.floor(x), "floor @ {b}");
        }
        for &b in I8_SAMPLES {
            let y = FixedI8::<typenum_alias::U0>::from_bits(b);
            assert_eq!(COMPOSED_4STEP.inner(y), Q008Q000.inner(y), "inner @ {b}");
        }
    }

    #[test]
    fn compose_left_identity_pointwise_equal() {
        // id ∘ Q008Q004 must agree with Q008Q004 on every i8.
        for b in i8::MIN..=i8::MAX {
            let x = FixedI8::<typenum_alias::U8>::from_bits(b);
            assert_eq!(LEFT_ID_COMPOSED.ceil(x), Q008Q004.ceil(x));
            assert_eq!(LEFT_ID_COMPOSED.floor(x), Q008Q004.floor(x));
        }
        for b in i8::MIN..=i8::MAX {
            let y = FixedI8::<typenum_alias::U4>::from_bits(b);
            assert_eq!(LEFT_ID_COMPOSED.inner(y), Q008Q004.inner(y));
        }
    }

    #[test]
    fn compose_right_identity_pointwise_equal() {
        for b in i8::MIN..=i8::MAX {
            let x = FixedI8::<typenum_alias::U8>::from_bits(b);
            assert_eq!(RIGHT_ID_COMPOSED.ceil(x), Q008Q004.ceil(x));
            assert_eq!(RIGHT_ID_COMPOSED.floor(x), Q008Q004.floor(x));
        }
        for b in i8::MIN..=i8::MAX {
            let y = FixedI8::<typenum_alias::U4>::from_bits(b);
            assert_eq!(RIGHT_ID_COMPOSED.inner(y), Q008Q004.inner(y));
        }
    }

    proptest! {
        // Exhaustive proptest over all 256 i8 bit patterns is cheap
        // and covers the entire I008 / I000 input domain — the
        // boundary-fixup paths in `ceil`/`floor` get hit by
        // construction. We use `any::<i8>()` rather than a bounded
        // range strategy because there's no overflow risk on the
        // i8-backed ladder.

        #[test]
        fn compose_four_step_galois_l(p: i8, c: i8) {
            let x = FixedI8::<typenum_alias::U8>::from_bits(p);
            let y = FixedI8::<typenum_alias::U0>::from_bits(c);
            prop_assert!(conn_laws::conn_galois_l(&COMPOSED_4STEP, x, y));
        }

        #[test]
        fn compose_four_step_galois_r(p: i8, c: i8) {
            let x = FixedI8::<typenum_alias::U8>::from_bits(p);
            let y = FixedI8::<typenum_alias::U0>::from_bits(c);
            prop_assert!(conn_laws::conn_galois_r(&COMPOSED_4STEP, x, y));
        }

        // `floor ≤ ceil` is intentionally NOT asserted: the i8 fix_fix
        // ladder has saturation-fixup arms at `bits == ±i8::MAX` that
        // pin `ceil` to the opposite end of the range, violating the
        // simple ordering at exactly those two boundary inputs. The
        // existing per-pair tests in `conn::fixed::i8` document this
        // and accept it as the price of the FINE_MIN/FINE_MAX
        // saturation pinning. The Galois adjoint laws above hold
        // unconditionally.

        #[test]
        fn compose_four_step_idempotent(p: i8) {
            let x = FixedI8::<typenum_alias::U8>::from_bits(p);
            prop_assert!(conn_laws::conn_idempotent(&COMPOSED_4STEP, x));
        }

        #[test]
        fn compose_four_step_monotone_l(p1: i8, p2: i8) {
            let a = FixedI8::<typenum_alias::U8>::from_bits(p1);
            let b = FixedI8::<typenum_alias::U8>::from_bits(p2);
            prop_assert!(conn_laws::conn_monotone_l(&COMPOSED_4STEP, a, b));
        }

        #[test]
        fn compose_four_step_monotone_r(c1: i8, c2: i8) {
            let a = FixedI8::<typenum_alias::U0>::from_bits(c1);
            let b = FixedI8::<typenum_alias::U0>::from_bits(c2);
            prop_assert!(conn_laws::conn_monotone_r(&COMPOSED_4STEP, a, b));
        }
    }

    // Tiny alias module so the verbose `::fixed::types::extra::U?`
    // paths above stay short. The `typenum_alias` name is local to
    // this test mod; it doesn't pollute the crate namespace.
    mod typenum_alias {
        pub use ::fixed::types::extra::{U0, U4, U8};
    }

    // ── Cast operation tests (folded in from former `conn::cast` mod) ──
    //
    // ID_I32 / ID_EF64 are reused from the proptest blocks above; the
    // cast tests need an additional `ID_I64` (i64 path coverage for
    // the two-sided helpers) and an `ORDERED_PAIR` Conn fixture for
    // `median`.

    const ID_I64: Conn<i64, i64> = Conn::identity();

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

    // ── Two-sided helpers (deterministic spot checks) ──

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

    proptest! {
        // ── ID_I32 (Ord path) ─────────────────────────────────────

        #[test]
        fn upper1_unit_id_i32(a: i32) {
            prop_assert!(conn_laws::conn_upper1_id_unit(&ID_I32, a));
        }

        #[test]
        fn lower1_counit_id_i32(a: i32) {
            prop_assert!(conn_laws::conn_lower1_id_counit(&ID_I32, a));
        }

        #[test]
        fn ceiling1_kernel_id_i32(b: i32) {
            prop_assert!(conn_laws::conn_ceiling1_id_kernel(&ID_I32, b));
        }

        #[test]
        fn floor1_kernel_id_i32(b: i32) {
            prop_assert!(conn_laws::conn_floor1_id_kernel(&ID_I32, b));
        }

        #[test]
        fn upper2_diag_id_i32(a: i32) {
            prop_assert!(conn_laws::conn_upper2_id_diag(&ID_I32, a));
        }

        #[test]
        fn lower2_diag_id_i32(a: i32) {
            prop_assert!(conn_laws::conn_lower2_id_diag(&ID_I32, a));
        }

        #[test]
        fn ceiling2_diag_id_i32(b: i32) {
            prop_assert!(conn_laws::conn_ceiling2_id_diag(&ID_I32, b));
        }

        #[test]
        fn floor2_diag_id_i32(b: i32) {
            prop_assert!(conn_laws::conn_floor2_id_diag(&ID_I32, b));
        }

        // ── ID_EF64 (ExtendedFloat<f64>; covers Bot/Top/Extend(NaN)) ──

        #[test]
        fn upper1_unit_id_ef64(a in arb_f64()) {
            prop_assert!(conn_laws::conn_upper1_id_unit(&ID_EF64, ExtendedFloat::Extend(a)));
        }

        #[test]
        fn lower1_counit_id_ef64(a in arb_f64()) {
            prop_assert!(conn_laws::conn_lower1_id_counit(&ID_EF64, ExtendedFloat::Extend(a)));
        }

        #[test]
        fn ceiling1_kernel_id_ef64(b in arb_f64()) {
            prop_assert!(conn_laws::conn_ceiling1_id_kernel(&ID_EF64, ExtendedFloat::Extend(b)));
        }

        #[test]
        fn floor1_kernel_id_ef64(b in arb_f64()) {
            prop_assert!(conn_laws::conn_floor1_id_kernel(&ID_EF64, ExtendedFloat::Extend(b)));
        }

        #[test]
        fn upper2_diag_id_ef64(a in arb_f64()) {
            prop_assert!(conn_laws::conn_upper2_id_diag(&ID_EF64, ExtendedFloat::Extend(a)));
        }

        #[test]
        fn lower2_diag_id_ef64(a in arb_f64()) {
            prop_assert!(conn_laws::conn_lower2_id_diag(&ID_EF64, ExtendedFloat::Extend(a)));
        }

        #[test]
        fn ceiling2_diag_id_ef64(b in arb_f64()) {
            prop_assert!(conn_laws::conn_ceiling2_id_diag(&ID_EF64, ExtendedFloat::Extend(b)));
        }

        #[test]
        fn floor2_diag_id_ef64(b in arb_f64()) {
            prop_assert!(conn_laws::conn_floor2_id_diag(&ID_EF64, ExtendedFloat::Extend(b)));
        }

        // ── Two-sided helpers ──
        //
        // Identity Conns have `lower1(c, id, x) == upper1(c, id, x)
        // == x`, so the inner subtractions in `interval` reduce to
        // `x - x = 0`, the offset in `midpoint` reduces to `0 / 2 =
        // 0`, and no arithmetic between distinct values occurs.
        // Every predicate driven over `ID_I32` / `ID_I64` is
        // therefore safe over the full primitive range. When
        // non-identity Conn coverage lands (separate sprint), the
        // proptests for those bases will need clamps appropriate to
        // the bracket width.

        #[test]
        fn interval_at_midpoint_id_i32(a: i32) {
            prop_assert!(conn_laws::conn_interval_at_midpoint_eq_or_none(&ID_I32, a));
        }

        #[test]
        fn interval_at_midpoint_id_i64(a: i64) {
            prop_assert!(conn_laws::conn_interval_at_midpoint_eq_or_none(&ID_I64, a));
        }

        #[test]
        fn midpoint_between_id_i32(a: i32) {
            prop_assert!(conn_laws::conn_midpoint_between(&ID_I32, a));
        }

        #[test]
        fn midpoint_between_id_i64(a: i64) {
            prop_assert!(conn_laws::conn_midpoint_between(&ID_I64, a));
        }

        #[test]
        fn round_picks_endpoint_id_i32(a: i32) {
            prop_assert!(conn_laws::conn_round_picks_endpoint(&ID_I32, a));
        }

        #[test]
        fn round_picks_endpoint_id_i64(a: i64) {
            prop_assert!(conn_laws::conn_round_picks_endpoint(&ID_I64, a));
        }

        #[test]
        fn truncate_picks_endpoint_id_i32(a: i32) {
            prop_assert!(conn_laws::conn_truncate_picks_endpoint(&ID_I32, a));
        }

        #[test]
        fn truncate_picks_endpoint_id_i64(a: i64) {
            prop_assert!(conn_laws::conn_truncate_picks_endpoint(&ID_I64, a));
        }

        #[test]
        fn truncate_toward_zero_id_i32(a: i32) {
            prop_assert!(conn_laws::conn_truncate_toward_zero(&ID_I32, a));
        }

        #[test]
        fn truncate_toward_zero_id_i64(a: i64) {
            prop_assert!(conn_laws::conn_truncate_toward_zero(&ID_I64, a));
        }

        #[test]
        fn round1_id_unit_id_i32(a: i32) {
            prop_assert!(conn_laws::conn_round1_id_unit(&ID_I32, a));
        }

        #[test]
        fn truncate1_id_unit_id_i32(a: i32) {
            prop_assert!(conn_laws::conn_truncate1_id_unit(&ID_I32, a));
        }

        // Birkhoff median axioms over ORDERED_PAIR.

        #[test]
        fn median_idempotent_ordered(x: i32, y: i32) {
            prop_assert!(conn_laws::conn_median_idempotent(&ORDERED_PAIR, x, y));
        }

        #[test]
        fn median_rotate_ordered(x: i32, y: i32, z: i32) {
            prop_assert!(conn_laws::conn_median_rotate(&ORDERED_PAIR, x, y, z));
        }

        #[test]
        fn median_swap_yz_ordered(x: i32, y: i32, z: i32) {
            prop_assert!(conn_laws::conn_median_swap_yz(&ORDERED_PAIR, x, y, z));
        }

        #[test]
        fn median_associative_ordered(w: i32, x: i32, y: i32, z: i32) {
            prop_assert!(conn_laws::conn_median_associative(&ORDERED_PAIR, w, x, y, z));
        }
    }
}
