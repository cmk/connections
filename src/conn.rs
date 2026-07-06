//! Galois-connection core: the [`Conn<A, B, K>`] type, the kind
//! markers [`L`] and [`R`], the [`ConnL`] / [`ConnR`] / [`ConnK`]
//! capability traits for adjoint connections, and the operations on
//! a `Conn` (kind-gated accessors and lifters, plus two-sided
//! rounding helpers on [`ConnK`]).
//!
//! ## Representation
//!
//! A Galois connection is a pair of monotone functions `f: A → B`
//! and `g: B → A`, such that `f(a) ≤ b ⟺  a ≤ g(b)` for all pairs
//! of inputs `(a, b)`. A picture is worth 1000 words:
//!
//! ```text
//! A  ←  B
//!    g
//!
//! 3  ↔  3
//!
//!
//! 2  ←  2
//!    ↰
//!    ↳
//! 1  →  1
//!
//!    f
//! A  →  B
//! ```
//!
//! Each row is a `(a, b)` pair; arrows show the action of `f` (A → B,
//! bottom legend) and `g` (B → A, top legend). Lone arrows mark
//! single function mappings (`f(1) = 1`, `g(2) = 2`); the `↔` marks a
//! matched pair where both functions agree (`f(3) = 3`, `g(3) = 3`); the
//! adjacent `↰ ↳` glyphs depict the *lens* `f(2) ↔ g(1)` — two
//! non-crossing arrows `↰ ↳` between rows 2 and 1 are the 'geometric
//! signature' of adjointness.
//!
//! [`Conn<A, B, K>`] holds *exactly two* fn-pointer fields, and the
//! kind tag `K` (defaulting to [`L`]) determines which adjoint role
//! each field plays. Kind-specific inherent methods enforce the
//! discipline at the type level: calling `.floor(...)` on an
//! `Conn<_, _, L>` is a compile error (the method only exists on
//! `Conn<_, _, R>`); same for `.ceil(...)` on `R`.
//!
//! An **adjoint triple** `f ⊣ g ⊣ h` is two adjunctions sharing the
//! middle function `g`: an L-Galois pair `(f, g)` and an R-Galois pair
//! `(g, h)` over the same `(A, B)`. Triples are *not* a third kind of
//! `Conn`; they are zero-sized marker types implementing both the
//! [`ConnL`] and [`ConnR`] capability traits (and so [`ConnK`], the
//! super-trait `ConnL + ConnR`). The "third function" — the adjoint
//! that distinguishes a triple from a one-sided Conn — lives as a
//! free function in module scope, referenced from the marker's
//! projections; no struct in the crate stores three fns.
//!
//! Each capability trait carries exactly one method: the polarity
//! **swap**. `ConnL::swap_l` reads the marker's L-pair over the
//! reversed `(B, A)` as an R-Galois value; `ConnR::swap_r` is the
//! dual. `Conn` *values* do not implement the traits — a value already
//! is its own view, and its swap is the inherent `const fn`
//! ([`Conn::swap_l`] / [`Conn::swap_r`]). One name, disjoint
//! receivers, no duplication. Markers also expose the swaps as
//! inherent `const fn`s (emitted by [`conn_k!`](crate::conn_k) and
//! friends), which is what `const` composition uses:
//! `compose!(U032BE04.swap_r(), ...)`. The direct views are the public
//! [`view_l`] / [`view_r`] free functions — each the marker's swap
//! methods composed into a round trip, law-guaranteed equal to the
//! raw double swap (see `prop::conn::swap_involutive_l`).
//!
//! Two-sided operations ([`round`], [`truncate`], [`interval`],
//! [`median`], plus the `1` / `2` lifters) bind on [`ConnK`]
//! (`= ConnL + ConnR`), so they are callable only on triple markers,
//! not on one-sided Conns. One-sided accessors (`ceil` / `upper` /
//! `floor` / `lower` and their lifters) are kind-gated inherent
//! methods on the value type.

use core::cmp::Ordering;
use core::marker::PhantomData;
use core::ops::Sub;

use crate::interval::Interval;

// ── Kind markers ─────────────────────────────────────────────────────

mod kind {
    mod sealed {
        pub trait Sealed {}
    }

    /// Sealed marker trait: the kind universe is exactly `{L, R}`.
    pub trait Kind: sealed::Sealed + Copy + 'static {}

    /// Left-Galois kind tag.
    #[derive(Copy, Clone, Debug)]
    pub struct L;
    /// Right-Galois kind tag.
    #[derive(Copy, Clone, Debug)]
    pub struct R;

    impl sealed::Sealed for L {}
    impl Kind for L {}
    impl sealed::Sealed for R {}
    impl Kind for R {}
}

pub use kind::{Kind, L, R};

// ── Conn struct ──────────────────────────────────────────────────────

/// A Galois connection between preordered sets `A` and `B`, kind-tagged
/// by `K` (defaults to [`L`]).
///
/// Holds two `fn`-pointer fields whose adjoint roles depend on the kind:
///
/// | Kind  | `f`              | `g`              | Galois law                |
/// |-------|------------------|------------------|---------------------------|
/// | [`L`] | lower (`ceil`)   | upper (`upper`)  | `f(a) ≤ b ⟺ a ≤ g(b)`     |
/// | [`R`] | upper (`floor`)  | lower (`lower`)  | `g(b) ≤ a ⟺ b ≤ f(a)`     |
pub struct Conn<A, B, K: Kind = L> {
    f: fn(A) -> B,
    g: fn(B) -> A,
    _k: PhantomData<fn() -> K>,
}

impl<A, B, K: Kind> Copy for Conn<A, B, K> {}
impl<A, B, K: Kind> Clone for Conn<A, B, K> {
    fn clone(&self) -> Self {
        *self
    }
}

// `PhantomData<fn() -> K>` is invariant in `K` but is universally
// `Eq` / `Hash`; the only state distinguishing two `Conn` values is the
// `(f, g)` fn-pointer pair. Fn-pointer equality is reference-identity
// on the same monomorphisation.
impl<A, B, K: Kind> PartialEq for Conn<A, B, K> {
    fn eq(&self, other: &Self) -> bool {
        core::ptr::fn_addr_eq(self.f, other.f) && core::ptr::fn_addr_eq(self.g, other.g)
    }
}
impl<A, B, K: Kind> Eq for Conn<A, B, K> {}

impl<A, B, K: Kind> core::fmt::Debug for Conn<A, B, K> {
    fn fmt(&self, fmtr: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            fmtr,
            "Conn<{} → {}, {}>",
            core::any::type_name::<A>(),
            core::any::type_name::<B>(),
            core::any::type_name::<K>(),
        )
    }
}

// ── Constructors and inherent ops on L-Conns ─────────────────────────

impl<A, B> Conn<A, B, L> {
    /// Construct a left-Galois connection `ceil ⊣ inner`.
    pub const fn new_l(ceil: fn(A) -> B, inner: fn(B) -> A) -> Self {
        Conn {
            f: ceil,
            g: inner,
            _k: PhantomData,
        }
    }

    /// Slot-swap: `Conn<A, B, L> → Conn<B, A, R>`.
    ///
    /// The same `(f, g)` pair satisfies the R-Galois law over the
    /// swapped pair `(B, A)`. Zero-cost type-level relabel.
    pub const fn swap_l(self) -> Conn<B, A, R> {
        Conn {
            f: self.g,
            g: self.f,
            _k: PhantomData,
        }
    }
}

impl<A: Copy, B: Copy> Conn<A, B, L> {
    /// Apply the lower adjoint (round-up): `a ↦ f(a)`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::conn::view_l;
    /// use connections::float::ExtendedFloat::Extend;
    /// use connections::core::f064::F064F032;
    ///
    /// let pi64 = Extend(std::f64::consts::PI);
    /// let pi32 = Extend(std::f32::consts::PI as f64);
    /// let pi32_err = pi32 - pi64;
    ///
    /// // The f32 ceiling of π is std::f32::consts::PI itself —
    /// // π's nearest f32 representation rounds up.
    /// assert_eq!(view_l(&F064F032).ceil(pi64), Extend(std::f32::consts::PI));
    /// // Widening the result back to f64 lands at pi32, which sits
    /// // exactly pi32_err above true π:
    /// assert_eq!(view_l(&F064F032).upper(view_l(&F064F032).ceil(pi64)) - pi64, pi32_err);
    /// ```
    #[inline]
    #[must_use]
    pub fn ceil(self, a: A) -> B {
        (self.f)(a)
    }

    /// Apply the upper adjoint (embedding): `b ↦ g(b)`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::conn::view_l;
    /// use connections::float::ExtendedFloat::Extend;
    /// use connections::core::f064::F064F032;
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
    /// assert_eq!(view_l(&F064F032).upper(Extend(std::f32::consts::PI)), pi32);
    /// // Equivalently, "f64 π plus f32's rounding error":
    /// assert_eq!(view_l(&F064F032).upper(Extend(std::f32::consts::PI)) - pi64, pi32_err);
    /// ```
    #[inline]
    #[must_use]
    pub fn upper(self, b: B) -> A {
        (self.g)(b)
    }

    /// Lift a unary endofunction over `B` into one over `A` through
    /// the L-pair: `a ↦ g(h(f(a)))`.
    #[inline]
    #[must_use]
    pub fn upper1<H>(self, h: H, a: A) -> A
    where
        H: FnOnce(B) -> B,
    {
        (self.g)(h((self.f)(a)))
    }

    /// Lift a binary function over `B` through the L-pair.
    #[inline]
    #[must_use]
    pub fn upper2<H>(self, h: H, a1: A, a2: A) -> A
    where
        H: FnOnce(B, B) -> B,
    {
        (self.g)(h((self.f)(a1), (self.f)(a2)))
    }

    /// Lift a unary endofunction over `A` into one over `B` through
    /// the L-pair: `b ↦ f(h(g(b)))`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::conn::view_l;
    /// use connections::float::ExtendedFloat::Extend;
    /// use connections::core::f064::F064F032;
    ///
    /// // ceil1 / floor1 / truncate1 share this closure shape: `2π − x`
    /// // in f64-precision lands strictly between two f32 grid points.
    /// // ceil1 unconditionally narrows up — to std::f32::consts::PI.
    /// let pi32 = Extend(std::f32::consts::PI);
    /// let probe = |a| Extend(2.0_f64) * Extend(std::f64::consts::PI) - a;
    /// assert_eq!(
    ///     view_l(&F064F032).ceil1(probe, pi32),
    ///     Extend(std::f32::consts::PI),
    /// );
    /// ```
    #[inline]
    #[must_use]
    pub fn ceil1<H>(self, h: H, b: B) -> B
    where
        H: FnOnce(A) -> A,
    {
        (self.f)(h((self.g)(b)))
    }

    /// Lift a binary function over `A` through the L-pair.
    #[inline]
    #[must_use]
    pub fn ceil2<H>(self, h: H, b1: B, b2: B) -> B
    where
        H: FnOnce(A, A) -> A,
    {
        (self.f)(h((self.g)(b1), (self.g)(b2)))
    }
}

// ── Constructors and inherent ops on R-Conns ─────────────────────────

impl<A, B> Conn<A, B, R> {
    /// Construct a right-Galois connection `inner ⊣ floor`.
    ///
    /// Argument order mirrors Haskell's `CastR`: `inner` (the lower
    /// adjoint `g: B → A`) first, `floor` (the upper adjoint
    /// `f: A → B`) second.
    pub const fn new_r(inner: fn(B) -> A, floor: fn(A) -> B) -> Self {
        Conn {
            f: floor,
            g: inner,
            _k: PhantomData,
        }
    }

    /// Slot-swap: `Conn<A, B, R> → Conn<B, A, L>`.
    pub const fn swap_r(self) -> Conn<B, A, L> {
        Conn {
            f: self.g,
            g: self.f,
            _k: PhantomData,
        }
    }
}

impl<A: Copy, B: Copy> Conn<A, B, R> {
    /// Apply the upper adjoint (round-down): `a ↦ f(a)`.
    #[inline]
    #[must_use]
    pub fn floor(self, a: A) -> B {
        (self.f)(a)
    }

    /// Apply the lower adjoint (embedding): `b ↦ g(b)`.
    #[inline]
    #[must_use]
    pub fn lower(self, b: B) -> A {
        (self.g)(b)
    }

    /// Lift a unary endofunction over `B` into one over `A` through
    /// the R-pair.
    #[inline]
    #[must_use]
    pub fn lower1<H>(self, h: H, a: A) -> A
    where
        H: FnOnce(B) -> B,
    {
        (self.g)(h((self.f)(a)))
    }

    /// Lift a binary function over `B` through the R-pair.
    #[inline]
    #[must_use]
    pub fn lower2<H>(self, h: H, a1: A, a2: A) -> A
    where
        H: FnOnce(B, B) -> B,
    {
        (self.g)(h((self.f)(a1), (self.f)(a2)))
    }

    /// Lift a unary endofunction over `A` into one over `B` through
    /// the R-pair: `b ↦ f(h(g(b)))`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::conn::view_r;
    /// use connections::float::ExtendedFloat::Extend;
    /// use connections::core::f064::F064F032;
    ///
    /// // Same shared probe as ceil1 / truncate1: `2π − x` in f64
    /// // lands strictly between two f32 grid points. floor1
    /// // unconditionally narrows down — to one f32 ULP below
    /// // std::f32::consts::PI.
    /// let pi32 = Extend(std::f32::consts::PI);
    /// let probe = |a| Extend(2.0_f64) * Extend(std::f64::consts::PI) - a;
    /// assert_eq!(
    ///     view_r(&F064F032).floor1(probe, pi32),
    ///     Extend(3.1415925_f32),
    /// );
    /// ```
    #[inline]
    #[must_use]
    pub fn floor1<H>(self, h: H, b: B) -> B
    where
        H: FnOnce(A) -> A,
    {
        (self.f)(h((self.g)(b)))
    }

    /// Lift a binary function over `A` through the R-pair.
    #[inline]
    #[must_use]
    pub fn floor2<H>(self, h: H, b1: B, b2: B) -> B
    where
        H: FnOnce(A, A) -> A,
    {
        (self.f)(h((self.g)(b1), (self.g)(b2)))
    }
}

// ── Principal-filter / -ideal predicates ────────────────────────────

impl<A: Copy, B: Copy> Conn<A, B, L> {
    /// Membership in the principal filter generated by `a`:
    /// `b ∈ filter_l(a) ⟺ ceil(a) ≤ b`.
    ///
    /// The principal filter generated by `a ∈ A` is the upward-closed
    /// set `{ b ∈ B : ceil(a) ≤ b }`. Since `ceil` is monotonic and
    /// every B-value above `ceil(a)` satisfies the L-Galois law for
    /// some A-value above `a`, this characterises the
    /// upward-closure on the B side.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::conn::view_l;
    /// use connections::float::ExtendedFloat::Extend;
    /// use connections::core::f064::F064F032;
    ///
    /// let l = view_l(&F064F032);
    /// let pi64 = Extend(std::f64::consts::PI);
    /// // The f32 ceiling of pi64 is std::f32::consts::PI; equality
    /// // witnesses the lower edge of the filter.
    /// assert!(l.filter_l(pi64, Extend(std::f32::consts::PI)));
    /// // Anything strictly larger is also in the filter
    /// // (upward-closed):
    /// assert!(l.filter_l(pi64, Extend(4.0_f32)));
    /// // Strictly smaller f32s are not.
    /// assert!(!l.filter_l(pi64, Extend(3.0_f32)));
    /// ```
    #[inline]
    #[must_use]
    pub fn filter_l(self, a: A, b: B) -> bool
    where
        B: PartialOrd,
    {
        self.ceil(a) <= b
    }
}

impl<A: Copy, B: Copy> Conn<A, B, R> {
    /// Membership in the principal ideal generated by `a`:
    /// `b ∈ filter_r(a) ⟺ b ≤ floor(a)`.
    ///
    /// The principal ideal generated by `a ∈ A` is the
    /// downward-closed set `{ b ∈ B : b ≤ floor(a) }` — the dual
    /// of [`Conn::filter_l`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::conn::view_r;
    /// use connections::float::ExtendedFloat::Extend;
    /// use connections::core::f064::F064F032;
    ///
    /// let r = view_r(&F064F032);
    /// let pi64 = Extend(std::f64::consts::PI);
    /// // The f32 floor of pi64 is 3.1415925; that's the upper edge
    /// // of the ideal.
    /// assert!(r.filter_r(pi64, Extend(3.1415925_f32)));
    /// // Anything smaller is also in the ideal (downward-closed):
    /// assert!(r.filter_r(pi64, Extend(3.0_f32)));
    /// // The f32 ceiling (next f32 above) is not.
    /// assert!(!r.filter_r(pi64, Extend(std::f32::consts::PI)));
    /// ```
    #[inline]
    #[must_use]
    pub fn filter_r(self, a: A, b: B) -> bool
    where
        B: PartialOrd,
    {
        b <= self.floor(a)
    }
}

// ── Identity ─────────────────────────────────────────────────────────

impl<X, K: Kind> Conn<X, X, K> {
    /// The identity connection: `f = g = id`. Kind-generic — the same
    /// body satisfies both Galois laws, so the identity exists directly
    /// at either polarity (`Conn::<X, X, R>::identity()` needs no swap
    /// workaround). `Conn<X, X>` infers `K = L` by the type default.
    pub const fn identity() -> Self {
        const fn id_<X>(x: X) -> X {
            x
        }
        Conn {
            f: id_::<X>,
            g: id_::<X>,
            _k: PhantomData,
        }
    }
}

// ── ConnL / ConnR / ConnK capability traits ──────────────────────────

/// Capability trait: types carrying an `L`-Galois connection between
/// `A` and `B`, exposed through its polarity swap and a uniform
/// accessor API.
///
/// Implementors are the adjoint-triple markers (zero-sized unit
/// structs from [`conn_k!`](crate::conn_k) / [`iso!`](crate::iso) /
/// [`compose_k!`](crate::compose_k)) *and* one-sided `Conn<A, B, L>`
/// values (through the blanket impl below). The one required method,
/// [`swap_l`](ConnL::swap_l), is the categorical content: the marker's
/// L-pair `(f, g)` read over the swapped pair `(B, A)`, where it
/// satisfies the R-Galois law. Everything else —
/// [`view_l`](ConnL::view_l), [`ceil`](ConnL::ceil),
/// [`upper`](ConnL::upper), and the `*1`/`*2` lifters — is a provided
/// method routed through the L-view, so a marker answers `M.ceil(a)`
/// directly with no projection step.
///
/// The provided methods are **not** `const` (trait methods can't be on
/// stable Rust). In `const` position spell the view as the public
/// double swap `t.swap_l().swap_r()`, or call a marker's inherent
/// `const fn view_l()` / a value's inherent `const fn ceil()` — those
/// stay `const` and shadow the trait defaults on concrete receivers.
///
/// `Conn` *values* also implement this trait, but a value receiver
/// resolves `.ceil(a)` / `.swap_l()` to the inherent `const fn`
/// ([`Conn::swap_l`]) rather than the trait default — inherent methods
/// win method resolution — so const composition is unaffected.
///
/// Laws (`prop::conn`): the swaps are involutive up to fn-pointer
/// identity — `view_l(t) == t.view_l()` on markers, and
/// `c.swap_l().swap_r() == c` on values.
pub trait ConnL {
    /// The connection's source type.
    type A: Copy;
    /// The connection's target type.
    type B: Copy;

    /// The swapped L-view: the same pair over `(B, A)` in R polarity.
    /// The single required method; every other method defaults through
    /// it.
    fn swap_l(&self) -> Conn<Self::B, Self::A, R>;

    /// The direct L-view as a `Conn<A, B, L>` value. Fn-pointer-identical
    /// to a marker's inherent `const fn view_l()` by the swap-involution
    /// law (`prop::conn::swap_involutive_l`).
    #[inline]
    #[must_use]
    fn view_l(&self) -> Conn<Self::A, Self::B, L> {
        self.swap_l().swap_r()
    }

    /// Apply the lower adjoint (round-up) through the L-view: `a ↦ f(a)`.
    #[inline]
    #[must_use]
    fn ceil(&self, a: Self::A) -> Self::B {
        self.view_l().ceil(a)
    }

    /// Apply the upper adjoint (embedding) through the L-view: `b ↦ g(b)`.
    #[inline]
    #[must_use]
    fn upper(&self, b: Self::B) -> Self::A {
        self.view_l().upper(b)
    }

    /// Lift a unary endofunction over `B` through the L-pair:
    /// `a ↦ g(h(f(a)))`.
    #[inline]
    #[must_use]
    fn upper1<H>(&self, h: H, a: Self::A) -> Self::A
    where
        H: FnOnce(Self::B) -> Self::B,
    {
        self.view_l().upper1(h, a)
    }

    /// Lift a binary function over `B` through the L-pair.
    #[inline]
    #[must_use]
    fn upper2<H>(&self, h: H, a1: Self::A, a2: Self::A) -> Self::A
    where
        H: FnOnce(Self::B, Self::B) -> Self::B,
    {
        self.view_l().upper2(h, a1, a2)
    }

    /// Lift a unary endofunction over `A` through the L-pair:
    /// `b ↦ f(h(g(b)))`.
    #[inline]
    #[must_use]
    fn ceil1<H>(&self, h: H, b: Self::B) -> Self::B
    where
        H: FnOnce(Self::A) -> Self::A,
    {
        self.view_l().ceil1(h, b)
    }

    /// Lift a binary function over `A` through the L-pair.
    #[inline]
    #[must_use]
    fn ceil2<H>(&self, h: H, b1: Self::B, b2: Self::B) -> Self::B
    where
        H: FnOnce(Self::A, Self::A) -> Self::A,
    {
        self.view_l().ceil2(h, b1, b2)
    }
}

/// Capability trait: types carrying an `R`-Galois connection between
/// `A` and `B`, exposed through its polarity swap and a uniform
/// accessor API. Counterpart to [`ConnL`]; the direct R-view is
/// [`view_r`](ConnR::view_r), and [`floor`](ConnR::floor) /
/// [`lower`](ConnR::lower) / the `*1`/`*2` lifters route through it, so
/// a marker answers `M.floor(a)` directly. In `const` position spell
/// the view as the public double swap `t.swap_r().swap_l()`, or call a
/// marker's inherent `const fn view_r()`.
pub trait ConnR {
    /// The connection's source type.
    type A: Copy;
    /// The connection's target type.
    type B: Copy;

    /// The swapped R-view: the same pair over `(B, A)` in L polarity.
    /// The single required method; every other method defaults through
    /// it.
    fn swap_r(&self) -> Conn<Self::B, Self::A, L>;

    /// The direct R-view as a `Conn<A, B, R>` value. Fn-pointer-identical
    /// to a marker's inherent `const fn view_r()` by the swap-involution
    /// law (`prop::conn::swap_involutive_r`).
    #[inline]
    #[must_use]
    fn view_r(&self) -> Conn<Self::A, Self::B, R> {
        self.swap_r().swap_l()
    }

    /// Apply the upper adjoint (round-down) through the R-view: `a ↦ f(a)`.
    #[inline]
    #[must_use]
    fn floor(&self, a: Self::A) -> Self::B {
        self.view_r().floor(a)
    }

    /// Apply the lower adjoint (embedding) through the R-view: `b ↦ g(b)`.
    #[inline]
    #[must_use]
    fn lower(&self, b: Self::B) -> Self::A {
        self.view_r().lower(b)
    }

    /// Lift a unary endofunction over `B` through the R-pair.
    #[inline]
    #[must_use]
    fn lower1<H>(&self, h: H, a: Self::A) -> Self::A
    where
        H: FnOnce(Self::B) -> Self::B,
    {
        self.view_r().lower1(h, a)
    }

    /// Lift a binary function over `B` through the R-pair.
    #[inline]
    #[must_use]
    fn lower2<H>(&self, h: H, a1: Self::A, a2: Self::A) -> Self::A
    where
        H: FnOnce(Self::B, Self::B) -> Self::B,
    {
        self.view_r().lower2(h, a1, a2)
    }

    /// Lift a unary endofunction over `A` through the R-pair:
    /// `b ↦ f(h(g(b)))`.
    #[inline]
    #[must_use]
    fn floor1<H>(&self, h: H, b: Self::B) -> Self::B
    where
        H: FnOnce(Self::A) -> Self::A,
    {
        self.view_r().floor1(h, b)
    }

    /// Lift a binary function over `A` through the R-pair.
    #[inline]
    #[must_use]
    fn floor2<H>(&self, h: H, b1: Self::B, b2: Self::B) -> Self::B
    where
        H: FnOnce(Self::A, Self::A) -> Self::A,
    {
        self.view_r().floor2(h, b1, b2)
    }
}

/// Convenience super-trait: a type is a [`ConnK`] iff it implements
/// *both* [`ConnL`] and [`ConnR`] over the same `(A, B)`. Adjoint-
/// triple markers (and triple-shaped composed markers) implement
/// `ConnK` automatically via the blanket below; one-sided values
/// (`Conn<A, B, L>` and `Conn<A, B, R>`) do **not** — which is
/// correct, since a one-sided Conn isn't a triple.
///
/// The cross-trait equality `ConnR<A = <Self as ConnL>::A,
/// B = <Self as ConnL>::B>` is what makes the `(A, B)` pair *the
/// same* on both sides — without it, a `T: ConnL + ConnR` could
/// pair an `L`-side over `(i32, i64)` with an `R`-side over
/// `(i32, u32)` and still satisfy `ConnL + ConnR` separately. The
/// equality bound forbids that and is the type-level statement of
/// the functional dependency `T → (A, B)`.
pub trait ConnK: ConnL + ConnR<A = <Self as ConnL>::A, B = <Self as ConnL>::B> {
    /// Bracket of `x`: the closed interval `[lo, hi] ⊆ A` whose members
    /// share `x`'s B-cell. Method form of the free [`interval`] fn; see
    /// it for the `Empty`/`Closed` contract.
    #[inline]
    #[must_use]
    fn interval(&self, x: <Self as ConnL>::A) -> Interval<<Self as ConnL>::A>
    where
        <Self as ConnL>::A: PartialOrd,
    {
        interval(self, x)
    }

    /// Truncate `x` toward zero through the triple. Method form of
    /// [`truncate`].
    #[inline]
    #[must_use]
    fn truncate(&self, x: <Self as ConnL>::A) -> <Self as ConnL>::B
    where
        <Self as ConnL>::A: PartialOrd + From<u8>,
    {
        truncate(self, x)
    }

    /// Lift a unary `h: A → A`, truncated toward zero. Method form of
    /// [`truncate1`].
    #[inline]
    #[must_use]
    fn truncate1<H>(&self, h: H, x: <Self as ConnL>::B) -> <Self as ConnL>::B
    where
        <Self as ConnL>::A: PartialOrd + From<u8>,
        H: FnOnce(<Self as ConnL>::A) -> <Self as ConnL>::A,
    {
        truncate1(self, h, x)
    }

    /// Lift a binary `h: (A, A) → A`, truncated toward zero. Method form
    /// of [`truncate2`].
    #[inline]
    #[must_use]
    fn truncate2<H>(&self, h: H, x: <Self as ConnL>::B, y: <Self as ConnL>::B) -> <Self as ConnL>::B
    where
        <Self as ConnL>::A: PartialOrd + From<u8>,
        H: FnOnce(<Self as ConnL>::A, <Self as ConnL>::A) -> <Self as ConnL>::A,
    {
        truncate2(self, h, x, y)
    }

    /// Round `x` to nearest, ties toward zero. Method form of [`round`].
    #[inline]
    #[must_use]
    fn round(&self, x: <Self as ConnL>::A) -> <Self as ConnL>::B
    where
        <Self as ConnL>::A: PartialOrd + Sub<Output = <Self as ConnL>::A> + From<u8>,
    {
        round(self, x)
    }

    /// Lift a unary `h: A → A`, rounded to nearest. Method form of
    /// [`round1`].
    #[inline]
    #[must_use]
    fn round1<H>(&self, h: H, x: <Self as ConnL>::B) -> <Self as ConnL>::B
    where
        <Self as ConnL>::A: PartialOrd + Sub<Output = <Self as ConnL>::A> + From<u8>,
        H: FnOnce(<Self as ConnL>::A) -> <Self as ConnL>::A,
    {
        round1(self, h, x)
    }

    /// Lift a binary `h: (A, A) → A`, rounded to nearest. Method form of
    /// [`round2`].
    #[inline]
    #[must_use]
    fn round2<H>(&self, h: H, x: <Self as ConnL>::B, y: <Self as ConnL>::B) -> <Self as ConnL>::B
    where
        <Self as ConnL>::A: PartialOrd + Sub<Output = <Self as ConnL>::A> + From<u8>,
        H: FnOnce(<Self as ConnL>::A, <Self as ConnL>::A) -> <Self as ConnL>::A,
    {
        round2(self, h, x, y)
    }

    /// Birkhoff median over a diagonal triple `A = (B, B)`. Method form
    /// of the free [`median`] fn; only callable on the diagonal markers
    /// (`N5Float`-shaped) it already required.
    #[inline]
    #[must_use]
    fn median(
        &self,
        x: <Self as ConnL>::B,
        y: <Self as ConnL>::B,
        z: <Self as ConnL>::B,
    ) -> <Self as ConnL>::B
    where
        Self: ConnL<A = (<Self as ConnL>::B, <Self as ConnL>::B)>,
    {
        median(self, x, y, z)
    }
}
impl<T> ConnK for T where T: ConnL + ConnR<A = <T as ConnL>::A, B = <T as ConnL>::B> {}

// One-sided `Conn` values join the capability traits so the same
// method surface works on values and markers alike. A value is only
// *one* of `ConnL` / `ConnR` (never both), so it never becomes `ConnK`
// — the two-sided helpers stay triple-only, which is correct. Value
// receivers still resolve `.ceil` / `.swap_l` to the inherent `const
// fn` (inherent wins method resolution), so const composition is
// untouched.
impl<A: Copy, B: Copy> ConnL for Conn<A, B, L> {
    type A = A;
    type B = B;
    #[inline]
    fn swap_l(&self) -> Conn<B, A, R> {
        Conn::swap_l(*self)
    }
}
impl<A: Copy, B: Copy> ConnR for Conn<A, B, R> {
    type A = A;
    type B = B;
    #[inline]
    fn swap_r(&self) -> Conn<B, A, L> {
        Conn::swap_r(*self)
    }
}

// ── Two-sided helpers (bound on ConnK) ────────────────────────────────

/// Direct L-view of a triple bound, derived through the public swaps.
/// Now a thin forwarder to the [`ConnL::view_l`] method; retained for
/// source back-compat and for the `&Conn`-receiver call sites (law
/// predicates). Fn-pointer-identical to a marker's inherent `const fn
/// view_l()` by the swap-involution law
/// (`prop::conn::swap_involutive_l`) — same view, three spellings: the
/// free `view_l(t)`, the `t.view_l()` method, and the marker's public
/// inherent `const fn view_l()` (the `const` form).
pub fn view_l<T, A: Copy, B: Copy>(t: &T) -> Conn<A, B, L>
where
    T: ?Sized + ConnL<A = A, B = B>,
{
    t.view_l()
}

/// Direct R-view of a triple bound; dual of [`view_l`]. Forwards to the
/// [`ConnR::view_r`] method.
pub fn view_r<T, A: Copy, B: Copy>(t: &T) -> Conn<A, B, R>
where
    T: ?Sized + ConnR<A = A, B = B>,
{
    t.view_r()
}

/// Bracket of `x` under conn `t`: the closed interval `[lo, hi] ⊆ A`
/// of values sharing `x`'s B-cell.
///
/// Returns [`Interval::Empty`] when the **`ConnK` sandwich
/// inequality** `lo ≤ x ≤ hi` fails. The Galois laws give
/// `floor(x) ≤ ceil(x)` on the B-side, but lifting that back to
/// `A` requires the middle adjoint to be shared between the L-
/// and R-views, which the type system does not enforce: a user
/// can implement `ConnL` and `ConnR` independently with
/// incompatible widening functions. Genuinely partially-ordered
/// `A` (e.g. antichain pairs) can also produce incomparable
/// `lo` / `hi`. In either case the bracket cannot meaningfully
/// represent `x`'s `B`-cell, so we surface it as `Empty` rather
/// than fabricate a misleading `Closed`.
///
/// **Postcondition for `Closed` results**: `lo ≤ x ≤ hi`.
/// Downstream consumers (`round`, `bracket_contains_x`, etc.) may
/// rely on this without an extra runtime check.
///
/// # Examples
///
/// ```rust
/// use connections::interval::Interval;
/// use connections::conn::interval;
/// use connections::float::ExtendedFloat::Extend;
/// use connections::core::f064::F064F032;
///
/// // True π_f64 is bracketed by two adjacent f64 grid values that
/// // share an f32 cell; the bracket contains pi64.
/// let pi64 = Extend(std::f64::consts::PI);
/// assert!(interval(&F064F032, pi64).contains(&pi64));
///
/// // An exact f32 grid value (pi32 widened back to f64) has a
/// // degenerate (singleton) bracket.
/// let pi32 = Extend(std::f32::consts::PI as f64);
/// assert_eq!(
///     interval(&F064F032, pi32),
///     Interval::Closed { lo: pi32, hi: pi32 }
/// );
/// ```
#[inline]
#[must_use]
pub fn interval<T, A, B>(t: &T, x: A) -> Interval<A>
where
    T: ?Sized + ConnL<A = A, B = B> + ConnR<A = A, B = B>,
    A: Copy + PartialOrd,
    B: Copy,
{
    let lo = view_r(t).lower1(|b| b, x);
    let hi = view_l(t).upper1(|b| b, x);
    // Route through `Interval::new` defensively: a contract-broken
    // `PartialOrd` (non-transitive) could in principle satisfy
    // `lo ≤ x ∧ x ≤ hi` while `lo > hi`. The extra `partial_cmp`
    // is cheap and keeps `Interval::Closed`'s `lo ≤ hi` invariant
    // intact regardless of caller PartialOrd hygiene.
    if lo <= x && x <= hi {
        Interval::new(lo, hi)
    } else {
        Interval::Empty
    }
}

/// Truncate `x` toward zero through the triple: returns
/// `view_r(t).floor(x)` when `x ≥ 0`, otherwise
/// `view_l(t).ceil(x)`.
///
/// # Examples
///
/// ```rust
/// use connections::conn::truncate;
/// use connections::float::ExtendedFloat::Extend;
/// use connections::core::f064::F064F032;
///
/// // π > 0 → truncate-toward-zero takes the f32 floor; one f32 ULP
/// // below std::f32::consts::PI.
/// let pi = Extend(std::f64::consts::PI);
/// assert_eq!(truncate(&F064F032, pi), Extend(3.1415925_f32));
/// ```
#[inline]
#[must_use]
pub fn truncate<T, A, B>(t: &T, x: A) -> B
where
    T: ?Sized + ConnL<A = A, B = B> + ConnR<A = A, B = B>,
    A: Copy + PartialOrd + From<u8>,
    B: Copy,
{
    if x >= A::from(0) {
        view_r(t).floor(x)
    } else {
        view_l(t).ceil(x)
    }
}

/// Lift a unary function `h: A → A` through the triple, with the
/// result truncated toward zero.
///
/// We widen `x: B → A` via the L-view's `upper`, but `truncate` then
/// routes the positive branch through the R-view's `floor` and the
/// negative through the L-view's `ceil`. Choosing the L-view's
/// `upper` here is canonical: in any lawful triple, the L-view's
/// `g` field and the R-view's `g` field are both the same shared
/// middle adjoint, so widening through either view yields the same
/// value. We pick L by convention.
///
/// # Examples
///
/// ```rust
/// use connections::conn::truncate1;
/// use connections::float::ExtendedFloat::Extend;
/// use connections::core::f064::F064F032;
///
/// // truncate1 / floor1 / ceil1 share this closure shape: `2π − x`
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
pub fn truncate1<T, A, B, H>(t: &T, h: H, x: B) -> B
where
    T: ?Sized + ConnL<A = A, B = B> + ConnR<A = A, B = B>,
    A: Copy + PartialOrd + From<u8>,
    B: Copy,
    H: FnOnce(A) -> A,
{
    truncate(t, h(view_l(t).upper(x)))
}

/// Lift a binary function `h: (A, A) → A` through the triple, with
/// the result truncated toward zero.
///
/// # Examples
///
/// ```rust
/// use connections::conn::truncate2;
/// use connections::float::ExtendedFloat::Extend;
/// use connections::core::f064::F064F032;
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
pub fn truncate2<T, A, B, H>(t: &T, h: H, x: B, y: B) -> B
where
    T: ?Sized + ConnL<A = A, B = B> + ConnR<A = A, B = B>,
    A: Copy + PartialOrd + From<u8>,
    B: Copy,
    H: FnOnce(A, A) -> A,
{
    let l = view_l(t);
    truncate(t, h(l.upper(x), l.upper(y)))
}

/// Round `x` to the nearest representable value across the triple,
/// with ties broken toward zero.
///
/// # Examples
///
/// ```rust
/// use connections::conn::view_l;
/// use connections::conn::round;
/// use connections::float::ExtendedFloat::Extend;
/// use connections::core::f064::F064F032;
///
/// let pi64 = Extend(std::f64::consts::PI);
/// let pi32 = Extend(std::f32::consts::PI as f64);
/// let pi32_err = pi32 - pi64;
///
/// // Round-to-nearest f32 of π is std::f32::consts::PI — the f32
/// // value `(pi as f32)` would also produce.
/// assert_eq!(round(&F064F032, pi64), Extend(std::f32::consts::PI));
/// // Widening the result back to f64 lands pi32_err above true π:
/// assert_eq!(view_l(&F064F032).upper(round(&F064F032, pi64)) - pi64, pi32_err);
/// ```
#[inline]
#[must_use]
pub fn round<T, A, B>(t: &T, x: A) -> B
where
    T: ?Sized + ConnL<A = A, B = B> + ConnR<A = A, B = B>,
    A: Copy + PartialOrd + Sub<Output = A> + From<u8>,
    B: Copy,
{
    // `Closed` carries `lo ≤ x ≤ hi` as a postcondition (see
    // [`interval`]); `x - lo` and `hi - x` are non-negative for
    // any sensible `A: Sub`. `Empty` signals a malformed triple
    // or antichain endpoints — fall back to truncate.
    match interval(t, x) {
        Interval::Closed { lo, hi } => match (x - lo).partial_cmp(&(hi - x)) {
            Some(Ordering::Greater) => view_l(t).ceil(x),
            Some(Ordering::Less) => view_r(t).floor(x),
            _ => truncate(t, x),
        },
        Interval::Empty => truncate(t, x),
    }
}

/// Lift a unary function `h: A → A` through the triple, rounded to
/// nearest with ties toward zero.
///
/// # Examples
///
/// ```rust
/// use connections::conn::round1;
/// use connections::float::ExtendedFloat::Extend;
/// use connections::core::f064::F064F032;
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
pub fn round1<T, A, B, H>(t: &T, h: H, x: B) -> B
where
    T: ?Sized + ConnL<A = A, B = B> + ConnR<A = A, B = B>,
    A: Copy + PartialOrd + Sub<Output = A> + From<u8>,
    B: Copy,
    H: FnOnce(A) -> A,
{
    round(t, h(view_l(t).upper(x)))
}

/// Lift a binary function `h: (A, A) → A` through the triple,
/// rounded to nearest with ties toward zero.
///
/// # Examples
///
/// ```rust
/// use connections::conn::round2;
/// use connections::float::ExtendedFloat::Extend;
/// use connections::core::f064::F064F032;
///
/// // Catastrophic cancellation example: `(x + y) − x` should be y, but
/// // at the largest odd-integer f32 (2^24 - 1) the sum already rounds
/// // away the small operand, and the answer collapses to 1.0 instead
/// // of 2.0. round2 lifts to f64, computes exactly, narrows once.
/// let max_odd = Extend(16777215.0_f32);   // = 2^24 - 1
/// let two = Extend(2.0_f32);
/// assert_eq!((16777215.0_f32 + 2.0_f32) - 16777215.0_f32, 1.0); // raw f32
/// assert_eq!(
///     round2(&F064F032, |a, b| (a + b) - a, max_odd, two),
///     Extend(2.0_f32),
/// );
/// ```
#[inline]
#[must_use]
pub fn round2<T, A, B, H>(t: &T, h: H, x: B, y: B) -> B
where
    T: ?Sized + ConnL<A = A, B = B> + ConnR<A = A, B = B>,
    A: Copy + PartialOrd + Sub<Output = A> + From<u8>,
    B: Copy,
    H: FnOnce(A, A) -> A,
{
    let l = view_l(t);
    round(t, h(l.upper(x), l.upper(y)))
}

/// Birkhoff median over a diagonal triple `T: ConnK` with `A = (B, B)`,
/// using the triple's L-view ceil as join and R-view floor as meet.
/// Also available as the [`ConnK::median`] method (`t.median(x, y, z)`).
///
/// # Examples
///
/// On a totally-ordered i32 lattice (`max`/`min`/diag), `median`
/// reduces to the standard 3-element numeric median:
///
/// ```rust
/// use connections::{conn_k, conn::median};
///
/// fn ceil_max(p: (i32, i32)) -> i32 { p.0.max(p.1) }
/// fn dup(x: i32) -> (i32, i32) { (x, x) }
/// fn floor_min(p: (i32, i32)) -> i32 { p.0.min(p.1) }
/// conn_k! {
///     OrdI32 : (i32, i32) => i32 {
///         ceil:  ceil_max,
///         inner: dup,
///         floor: floor_min,
///     }
/// }
///
/// fn main() {
///     assert_eq!(median(&OrdI32, 1, 2, 3), 2);
/// }
/// ```
///
/// On the partially-ordered N5 lattice over `ExtendedFloat<f32>`, an
/// incomparable pair (NaN vs finite) escalates `lub` to `Top` and
/// `glb` to `Bot`; the formula then collapses to the median of the
/// two finite values:
///
/// ```rust
/// use connections::{conn_k, conn::median};
/// use connections::float::ExtendedFloat::{self, Bot, Extend, Top};
/// use core::cmp::Ordering;
///
/// fn lub(p: (ExtendedFloat<f32>, ExtendedFloat<f32>)) -> ExtendedFloat<f32> {
///     match p.0.partial_cmp(&p.1) {
///         Some(Ordering::Less | Ordering::Equal) => p.1,
///         Some(Ordering::Greater) => p.0,
///         None => Top,
///     }
/// }
/// fn glb(p: (ExtendedFloat<f32>, ExtendedFloat<f32>)) -> ExtendedFloat<f32> {
///     match p.0.partial_cmp(&p.1) {
///         Some(Ordering::Less | Ordering::Equal) => p.0,
///         Some(Ordering::Greater) => p.1,
///         None => Bot,
///     }
/// }
/// fn diag(x: ExtendedFloat<f32>) -> (ExtendedFloat<f32>, ExtendedFloat<f32>) {
///     (x, x)
/// }
/// conn_k! {
///     N5Float : (ExtendedFloat<f32>, ExtendedFloat<f32>) => ExtendedFloat<f32> {
///         ceil:  lub,
///         inner: diag,
///         floor: glb,
///     }
/// }
///
/// fn main() {
///     let nan = Extend(0.0_f32 / 0.0_f32);
///
///     // All finite — matches the standard numeric median.
///     assert_eq!(
///         median(&N5Float, Extend(1.0_f32), Extend(9.0_f32), Extend(7.0_f32)),
///         Extend(7.0_f32),
///     );
///
///     // NaN argument: incomparable, so the formula collapses to the
///     // median of the two finite values.
///     assert_eq!(
///         median(&N5Float, Extend(1.0_f32), Extend(9.0_f32), nan),
///         Extend(9.0_f32),
///     );
/// }
/// ```
#[inline]
#[must_use]
pub fn median<T, A>(t: &T, x: A, y: A, z: A) -> A
where
    T: ?Sized + ConnL<A = (A, A), B = A> + ConnR<A = (A, A), B = A>,
    A: Copy,
{
    let join = |p: A, q: A| view_l(t).ceil((p, q));
    let meet = |p: A, q: A| view_r(t).floor((p, q));
    meet(meet(join(x, y), join(y, z)), join(z, x))
}

// ── Composition macros ───────────────────────────────────────────────

/// Compose a chain of L-Conn paths into a single fresh `Conn<Src, Dst>`.
///
/// Variadic over two or more parents. The expansion uses non-capturing
/// closures referencing the parent paths so each closure coerces to
/// an `fn(_) -> _` pointer at the `Conn::new_l` call site.
#[macro_export]
macro_rules! compose_l {
    ($first:expr, $($rest:expr),+ $(,)?) => {
        $crate::conn::Conn::new_l(
            |a| $crate::compose_l!(@nest_f a; $first $(, $rest)+),
            |z| $crate::compose_l!(@nest_g z; $first $(, $rest)+),
        )
    };

    (@nest_f $x:expr; $last:expr) => { $last.ceil($x) };
    (@nest_f $x:expr; $first:expr $(, $rest:expr)+) => {
        $crate::compose_l!(@nest_f $first.ceil($x); $($rest),+)
    };

    (@nest_g $z:expr; $last:expr) => { $last.upper($z) };
    (@nest_g $z:expr; $first:expr $(, $rest:expr)+) => {
        $first.upper($crate::compose_l!(@nest_g $z; $($rest),+))
    };
}

/// Compose a chain of R-Conn expressions into a single fresh `Conn<Src, Dst, R>`.
#[macro_export]
macro_rules! compose_r {
    ($first:expr, $($rest:expr),+ $(,)?) => {
        $crate::conn::Conn::new_r(
            |z| $crate::compose_r!(@nest_g z; $first $(, $rest)+),
            |a| $crate::compose_r!(@nest_f a; $first $(, $rest)+),
        )
    };

    (@nest_f $x:expr; $last:expr) => { $last.floor($x) };
    (@nest_f $x:expr; $first:expr $(, $rest:expr)+) => {
        $crate::compose_r!(@nest_f $first.floor($x); $($rest),+)
    };

    (@nest_g $z:expr; $last:expr) => { $last.lower($z) };
    (@nest_g $z:expr; $first:expr $(, $rest:expr)+) => {
        $first.lower($crate::compose_r!(@nest_g $z; $($rest),+))
    };
}

/// Forwarding alias for [`compose_l!`](crate::compose_l) — mirrors the `K = L` default
/// of [`Conn`]. Use when composing L-side conns and you'd rather not
/// spell the side explicitly. Error spans may point at this
/// forwarder rather than [`compose_l!`](crate::compose_l) directly.
///
/// # Examples
///
/// ```rust,no_run
/// use connections::compose;
/// use connections::conn::Conn;
///
/// // Three-step compose: id ∘ id ∘ id = id (any Conn type works).
/// const ID_I32: Conn<i32, i32> = Conn::identity();
/// const COMPOSED: Conn<i32, i32> = compose!(ID_I32, ID_I32, ID_I32);
/// ```
#[macro_export]
macro_rules! compose {
    ($($t:tt)*) => { $crate::compose_l!($($t)*) };
}

/// Declaration-form macro: compose two adjoint-triple markers into a
/// fresh triple marker. The composed marker is a unit struct with
/// freshly-built `ConnL` and `ConnR` impls whose `conn_l` / `conn_r`
/// methods build the projection via [`compose_l!`](crate::compose_l) / [`compose_r!`](crate::compose_r)
/// over the parents' views.
///
/// ```
/// # use connections::compose_k;
/// # use connections::core::f032::F032U008;
/// # use connections::core::f064::F064F032;
/// # use connections::extended::Extended;
/// # use connections::float::{F032, F064};
/// // Compose `F064F032 : F064 ⇒ F032` with `F032U008 : F032 ⇒ Extended<u8>`
/// // into one fresh triple marker for the whole `F064 ⇒ Extended<u8>` chain.
/// compose_k!(Chain : F064 => F032 => Extended<u8> = F064F032, F032U008);
/// # let _ = Chain;
/// ```
#[macro_export]
macro_rules! compose_k {
    (
        $(#[$meta:meta])*
        $vis:vis $name:ident : $A:ty => $B:ty => $C:ty = $t1:path, $t2:path $(,)?
    ) => {
        $(#[$meta])*
        #[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Default)]
        $vis struct $name;
        impl $name {
            /// The composed L-view. `const`-projectable: the closure
            /// coercion happens in a `const` item, the supported
            /// composition position.
            #[allow(dead_code)]
            #[inline]
            #[must_use]
            $vis const fn view_l(self) -> $crate::conn::Conn<$A, $C, $crate::conn::L> {
                const COMPOSED: $crate::conn::Conn<$A, $C, $crate::conn::L> =
                    $crate::compose_l!($t1.swap_l().swap_r(), $t2.swap_l().swap_r());
                COMPOSED
            }
            /// The composed R-view. `const`-projectable.
            #[allow(dead_code)]
            #[inline]
            #[must_use]
            $vis const fn view_r(self) -> $crate::conn::Conn<$A, $C, $crate::conn::R> {
                const COMPOSED: $crate::conn::Conn<$A, $C, $crate::conn::R> =
                    $crate::compose_r!($t1.swap_r().swap_l(), $t2.swap_r().swap_l());
                COMPOSED
            }
            /// The swapped composed L-view. `const`-projectable.
            #[allow(dead_code)]
            #[inline]
            #[must_use]
            $vis const fn swap_l(self) -> $crate::conn::Conn<$C, $A, $crate::conn::R> {
                self.view_l().swap_l()
            }
            /// The swapped composed R-view. `const`-projectable.
            #[allow(dead_code)]
            #[inline]
            #[must_use]
            $vis const fn swap_r(self) -> $crate::conn::Conn<$C, $A, $crate::conn::L> {
                self.view_r().swap_r()
            }
        }
        impl $crate::conn::ConnL for $name {
            type A = $A;
            type B = $C;
            #[inline]
            fn swap_l(&self) -> $crate::conn::Conn<$C, $A, $crate::conn::R> {
                // Path call binds the inherent `const fn swap_l` (inherent
                // wins over the trait default), avoiding infinite recursion
                // through the `&self`-receiver trait `view_l`.
                $name::swap_l(*self)
            }
        }
        impl $crate::conn::ConnR for $name {
            type A = $A;
            type B = $C;
            #[inline]
            fn swap_r(&self) -> $crate::conn::Conn<$C, $A, $crate::conn::L> {
                $name::swap_r(*self)
            }
        }
    };
}

/// Declaration-form macro: ship a new adjoint-triple marker from
/// three free-function paths `(ceil, inner, floor)`.
///
/// ```
/// # use connections::conn_k;
/// # use std::num::NonZeroI8;
/// # fn ceil(v: i8)  -> NonZeroI8 { NonZeroI8::new(if v == 0 { 1 } else { v }).unwrap() }
/// # fn floor(v: i8) -> NonZeroI8 { NonZeroI8::new(if v == 0 { -1 } else { v }).unwrap() }
/// # fn inner(nz: NonZeroI8) -> i8 { nz.get() }
/// // A lawful adjoint triple: `ceil` / `floor` sandwich 0 between
/// // `NonZero(+1)` and `NonZero(-1)`, and `inner` is the total
/// // embedding — exactly how `core::i008::I008N008` is built.
/// conn_k! {
///     pub I008N008 : i8 => NonZeroI8 {
///         ceil:  ceil,
///         inner: inner,
///         floor: floor,
///     }
/// }
/// # let _ = I008N008;
/// ```
#[macro_export]
macro_rules! conn_k {
    (
        $(#[$meta:meta])*
        $vis:vis $name:ident : $A:ty => $B:ty {
            ceil:  $ceil:expr,
            inner: $inner:expr,
            floor: $floor:expr $(,)?
        }
    ) => {
        $(#[$meta])*
        #[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Default)]
        $vis struct $name;
        impl $name {
            /// The L-view `(ceil, inner)`. `const`-projectable, so the
            /// marker composes in `const` position.
            #[allow(dead_code)]
            #[inline]
            #[must_use]
            $vis const fn view_l(self) -> $crate::conn::Conn<$A, $B, $crate::conn::L> {
                $crate::conn::Conn::new_l($ceil, $inner)
            }
            /// The R-view `(inner, floor)`. `const`-projectable.
            #[allow(dead_code)]
            #[inline]
            #[must_use]
            $vis const fn view_r(self) -> $crate::conn::Conn<$A, $B, $crate::conn::R> {
                $crate::conn::Conn::new_r($inner, $floor)
            }
            /// The swapped L-view over the reversed pair.
            /// `const`-projectable.
            #[allow(dead_code)]
            #[inline]
            #[must_use]
            $vis const fn swap_l(self) -> $crate::conn::Conn<$B, $A, $crate::conn::R> {
                self.view_l().swap_l()
            }
            /// The swapped R-view over the reversed pair.
            /// `const`-projectable.
            #[allow(dead_code)]
            #[inline]
            #[must_use]
            $vis const fn swap_r(self) -> $crate::conn::Conn<$B, $A, $crate::conn::L> {
                self.view_r().swap_r()
            }
        }
        impl $crate::conn::ConnL for $name {
            type A = $A;
            type B = $B;
            #[inline]
            fn swap_l(&self) -> $crate::conn::Conn<$B, $A, $crate::conn::R> {
                // Inherent `const fn swap_l` (path call), not the trait
                // `view_l` default — see the compose_k! note above.
                $name::swap_l(*self)
            }
        }
        impl $crate::conn::ConnR for $name {
            type A = $A;
            type B = $B;
            #[inline]
            fn swap_r(&self) -> $crate::conn::Conn<$B, $A, $crate::conn::L> {
                $name::swap_r(*self)
            }
        }
    };
}

/// Declaration-form macro: ship a degenerate-Galois iso (lossless
/// bijection) from a single `(forward, back)` function pair.
///
/// Equivalent to [`conn_k!`](crate::conn_k) with `ceil = floor = forward`; the macro
/// name itself flags the bijection so the body fields read as
/// `forward` / `back` rather than `ceil` / `inner` / `floor`. Both
/// [`ConnL`] and [`ConnR`] are implemented; every iso law
/// (`galois_l`, `galois_r`, `floor_le_ceil`, `idempotent`, …) holds
/// trivially.
///
/// ```
/// # use connections::iso;
/// # use std::net::Ipv4Addr;
/// # fn u32_to_v4(x: u32) -> Ipv4Addr { Ipv4Addr::from(x) }
/// # fn v4_to_u32(a: Ipv4Addr) -> u32 { u32::from(a) }
/// iso! {
///     pub U032IPV4 : u32 => Ipv4Addr {
///         forward: u32_to_v4,
///         back:    v4_to_u32,
///     }
/// }
/// # let _ = U032IPV4;
/// ```
#[macro_export]
macro_rules! iso {
    (
        $(#[$meta:meta])*
        $vis:vis $name:ident : $A:ty => $B:ty {
            forward: $fwd:expr,
            back:    $bk:expr $(,)?
        }
    ) => {
        $crate::conn_k! {
            $(#[$meta])*
            $vis $name : $A => $B {
                ceil:  $fwd,
                inner: $bk,
                floor: $fwd,
            }
        }
    };
}

/// Declaration-form macro: ship a one-sided left-Galois `Conn`
/// (`ceil ⊣ inner`) as a `pub const` of type [`Conn<A, B>`].
///
/// Named-field syntax mirrors [`conn_k!`](crate::conn_k) / [`iso!`](crate::iso) and removes the
/// argument-order footgun on [`Conn::new_l`]: the field labels make
/// it impossible to swap `ceil` and `inner` accidentally (and the
/// `_l` / `_r` macro-name split prevents picking the wrong kind).
///
/// Unlike [`conn_k!`](crate::conn_k), this macro emits the `Conn` value directly —
/// not a marker struct with [`ConnL`] / [`ConnR`] impls — because no
/// adjoint triple exists for one-sided connections. Use [`conn_k!`](crate::conn_k)
/// when both `ceil` and `floor` are available and the inner
/// embedding is order-reflecting; use this macro when only the
/// left half of the adjunction holds.
///
/// ```
/// # use connections::conn_l;
/// # fn ceil(x: i16) -> i8 {
/// #     if x > i8::MAX as i16 { i8::MAX } else if x < i8::MIN as i16 { i8::MIN } else { x as i8 }
/// # }
/// # fn inner(x: i8) -> i16 { if x == i8::MAX { i16::MAX } else { x as i16 } }
/// // A lawful left-Galois narrowing: `ceil` saturates `i16` into `i8`
/// // and `inner` widens back with the source-side `MAX` fixup —
/// // exactly how `core::i016::I016I008` is built.
/// conn_l! {
///     pub I016I008 : i16 => i8 {
///         ceil:  ceil,
///         inner: inner,
///     }
/// }
/// # let _ = I016I008;
/// ```
#[macro_export]
macro_rules! conn_l {
    (
        $(#[$meta:meta])*
        $vis:vis $name:ident : $A:ty => $B:ty {
            ceil:  $ceil:expr,
            inner: $inner:expr $(,)?
        }
    ) => {
        $(#[$meta])*
        $vis const $name: $crate::conn::Conn<$A, $B> =
            $crate::conn::Conn::new_l($ceil, $inner);
    };
}

/// Declaration-form macro: ship a one-sided right-Galois `Conn`
/// (`inner ⊣ floor`) as a `pub const` of type [`Conn<A, B, R>`].
///
/// Named-field syntax mirrors [`conn_k!`](crate::conn_k) / [`iso!`](crate::iso) and removes the
/// argument-order footgun on [`Conn::new_r`] — whose positional
/// shape `(inner, floor)` (mirroring Haskell's `CastR`) is the
/// reverse of [`Conn::new_l`]'s `(ceil, inner)`. Field labels make
/// the order self-documenting.
///
/// ```
/// # use connections::conn_r;
/// # fn inner(x: i8) -> u8 { if x < 0 { 0 } else { x as u8 } }
/// # fn floor(x: u8) -> i8 { if x > i8::MAX as u8 { i8::MAX } else { x as i8 } }
/// // A lawful right-Galois cross-sign cast: `inner` clips `i8`'s
/// // negative half to `0`, and `floor` saturates `u8` above `i8::MAX`
/// // — exactly how `core::u008::U008I008` is built.
/// conn_r! {
///     pub U008I008 : u8 => i8 {
///         inner: inner,
///         floor: floor,
///     }
/// }
/// # let _ = U008I008;
/// ```
#[macro_export]
macro_rules! conn_r {
    (
        $(#[$meta:meta])*
        $vis:vis $name:ident : $A:ty => $B:ty {
            inner: $inner:expr,
            floor: $floor:expr $(,)?
        }
    ) => {
        $(#[$meta])*
        $vis const $name: $crate::conn::Conn<$A, $B, $crate::conn::R> =
            $crate::conn::Conn::new_r($inner, $floor);
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    // ── Conn type smoke test ─────────────────────────────────────────

    #[test]
    fn kind_default_l() {
        // K = L is the default, so `Conn<A,B>` ≡ `Conn<A,B,L>`.
        const _L: Conn<i64, i32> = Conn::new_l(|x| x as i32, |x| x as i64);
        const _R: Conn<i64, i32, R> = Conn::new_r(|x| x as i64, |x| x as i32);
    }

    // ── conn_k! macro instantiation ──────────────────────────────────

    const fn _id_i32_ceil(x: i32) -> i32 {
        x
    }
    const fn _id_i32_inner(x: i32) -> i32 {
        x
    }
    const fn _id_i32_floor(x: i32) -> i32 {
        x
    }

    crate::conn_k! {
        TripleIdI32 : i32 => i32 {
            ceil:  _id_i32_ceil,
            inner: _id_i32_inner,
            floor: _id_i32_floor,
        }
    }

    #[test]
    fn triple_marker_zero_sized() {
        assert_eq!(core::mem::size_of::<TripleIdI32>(), 0);
    }

    #[test]
    fn triple_uses_both_views() {
        // Reach for both views and confirm they round-trip through
        // the shared inner.
        assert_eq!(TripleIdI32.view_l().ceil(7_i32), 7_i32);
        assert_eq!(TripleIdI32.view_r().floor(7_i32), 7_i32);
        assert_eq!(TripleIdI32.view_l().upper(7_i32), 7_i32);
        assert_eq!(TripleIdI32.view_r().lower(7_i32), 7_i32);
    }

    // ── compose_k! macro instantiation ───────────────────────────────

    crate::conn_k! {
        TripleAdd1 : i32 => i32 {
            ceil:  _add1,
            inner: _sub1,
            floor: _add1,
        }
    }
    const fn _add1(x: i32) -> i32 {
        x.wrapping_add(1)
    }
    const fn _sub1(x: i32) -> i32 {
        x.wrapping_sub(1)
    }

    crate::compose_k! {
        ComposedI32 : i32 => i32 => i32 = TripleIdI32, TripleAdd1
    }

    // ── iso! macro instantiation ─────────────────────────────────────

    const fn _i32_to_u32(x: i32) -> u32 {
        x as u32
    }
    const fn _u32_to_i32(x: u32) -> i32 {
        x as i32
    }

    crate::iso! {
        IsoI32U32 : i32 => u32 {
            forward: _i32_to_u32,
            back:    _u32_to_i32,
        }
    }

    #[test]
    fn iso_marker_zero_sized() {
        assert_eq!(core::mem::size_of::<IsoI32U32>(), 0);
    }

    #[test]
    fn iso_floor_eq_ceil() {
        // iso! sets floor = ceil = forward, so both adjoints agree on
        // every input (the defining property of a degenerate Galois
        // iso).
        for x in [i32::MIN, -1, 0, 1, 42, i32::MAX] {
            assert_eq!(IsoI32U32.view_l().ceil(x), IsoI32U32.view_r().floor(x));
        }
    }

    #[test]
    fn iso_round_trip_both_directions() {
        for x in [i32::MIN, -1, 0, 1, 42, i32::MAX] {
            let y = IsoI32U32.view_l().ceil(x);
            assert_eq!(IsoI32U32.view_l().upper(y), x);
        }
        for y in [0_u32, 1, 42, u32::MAX] {
            let x = IsoI32U32.view_l().upper(y);
            assert_eq!(IsoI32U32.view_l().ceil(x), y);
        }
    }

    #[test]
    fn compose_triple_marker() {
        // Composed triple's L-view: ceil(x) = TripleAdd1.ceil(TripleIdI32.ceil(x)) = x + 1
        assert_eq!(ComposedI32.view_l().ceil(0_i32), 1_i32);
        // Composed triple's R-view: floor(x) = TripleAdd1.floor(TripleIdI32.floor(x)) = x + 1
        assert_eq!(ComposedI32.view_r().floor(0_i32), 1_i32);
    }

    // ── Variadic compose_l! chain (3 operands, const-context) ────────

    const ID_L: Conn<i32, i32> = Conn::identity();
    const COMPOSED_3WAY: Conn<i32, i32> = crate::compose_l!(ID_L, ID_L, ID_L);

    #[test]
    fn compose_l_three_arg_chain() {
        // id ∘ id ∘ id over the L-side stays identity. Proves the
        // variadic `:expr` arm parses with 3 operands and produces a
        // valid `const` expression.
        assert_eq!(COMPOSED_3WAY.ceil(42_i32), 42_i32);
        assert_eq!(COMPOSED_3WAY.upper(7_i32), 7_i32);
    }

    #[test]
    fn compose_alias_matches_compose_l() {
        // The bare `compose!` is a forwarder to `compose_l!`; both
        // shapes must produce the same const value.
        const VIA_ALIAS: Conn<i32, i32> = crate::compose!(ID_L, ID_L);
        const VIA_LEFT: Conn<i32, i32> = crate::compose_l!(ID_L, ID_L);
        assert_eq!(VIA_ALIAS.ceil(42_i32), VIA_LEFT.ceil(42_i32));
        assert_eq!(VIA_ALIAS.upper(7_i32), VIA_LEFT.upper(7_i32));
    }

    #[test]
    fn compose_alias_matches_compose_l_three_operands() {
        // Variadic forward — three operands through the alias must
        // match three operands through `compose_l!` directly.
        const VIA_ALIAS: Conn<i32, i32> = crate::compose!(ID_L, ID_L, ID_L);
        const VIA_LEFT: Conn<i32, i32> = crate::compose_l!(ID_L, ID_L, ID_L);
        assert_eq!(VIA_ALIAS.ceil(42_i32), VIA_LEFT.ceil(42_i32));
        assert_eq!(VIA_ALIAS.upper(7_i32), VIA_LEFT.upper(7_i32));
    }

    // ── conn_l! / conn_r! macro instantiation ────────────────────────

    const fn _i64_to_i32(x: i64) -> i32 {
        x as i32
    }
    const fn _i32_to_i64(x: i32) -> i64 {
        x as i64
    }

    crate::conn_l! {
        CONNLI64I32 : i64 => i32 {
            ceil:  _i64_to_i32,
            inner: _i32_to_i64,
        }
    }

    crate::conn_r! {
        CONNRI64I32 : i64 => i32 {
            inner: _i32_to_i64,
            floor: _i64_to_i32,
        }
    }

    #[test]
    fn conn_l_macro_expands_to_new_l() {
        // Hand-written reference and the macro-built const must agree
        // on both adjoint slots for representative inputs.
        const REF: Conn<i64, i32> = Conn::new_l(_i64_to_i32, _i32_to_i64);
        for a in [i64::MIN, -1, 0, 1, 42, i64::MAX] {
            assert_eq!(CONNLI64I32.ceil(a), REF.ceil(a));
        }
        for b in [i32::MIN, -1, 0, 1, 42, i32::MAX] {
            assert_eq!(CONNLI64I32.upper(b), REF.upper(b));
        }
    }

    #[test]
    fn conn_r_macro_expands_to_new_r() {
        // `Conn::new_r` argument order is `(inner, floor)` — the
        // mirror of `new_l`'s `(ceil, inner)`. The macro reorders for
        // the constructor; this test confirms slots match a hand-
        // written reference.
        const REF: Conn<i64, i32, R> = Conn::new_r(_i32_to_i64, _i64_to_i32);
        for a in [i64::MIN, -1, 0, 1, 42, i64::MAX] {
            assert_eq!(CONNRI64I32.floor(a), REF.floor(a));
        }
        for b in [i32::MIN, -1, 0, 1, 42, i32::MAX] {
            assert_eq!(CONNRI64I32.lower(b), REF.lower(b));
        }
    }

    // ── Trait smoke test: markers dispatch generically via swap ──────

    #[test]
    fn marker_traits_dispatch_via_swap() {
        // The traits carry exactly the swap; a generic consumer derives
        // the direct views via `view_l` / `view_r` (the law-guaranteed
        // double swap).
        conn_k! {
            SmokeI64I32 : i64 => i32 {
                ceil:  _i64_to_i32,
                inner: _i32_to_i64,
                floor: _i64_to_i32,
            }
        }
        fn use_as_conn_l<T: ConnL<A = i64, B = i32>>(t: &T, a: i64) -> i32 {
            view_l(t).ceil(a)
        }
        fn use_as_conn_r<T: ConnR<A = i64, B = i32>>(t: &T, a: i64) -> i32 {
            view_r(t).floor(a)
        }
        assert_eq!(use_as_conn_l(&SmokeI64I32, 42_i64), 42_i32);
        assert_eq!(use_as_conn_r(&SmokeI64I32, 42_i64), 42_i32);
        // One concept, one name, two forms: the generic free fn and the
        // marker's inherent projection agree exactly (fn-pointer identity).
        assert_eq!(view_l(&SmokeI64I32), SmokeI64I32.view_l());
        assert_eq!(view_r(&SmokeI64I32), SmokeI64I32.view_r());
    }

    // ── swap_l / swap_r involution proptests ─────────────────────────

    use proptest::prelude::*;

    const fn _double(x: i32) -> i64 {
        (x as i64).wrapping_mul(2)
    }
    const fn _halve(x: i64) -> i32 {
        (x / 2) as i32
    }
    const ROUND_TRIP_L: Conn<i32, i64> = Conn::new_l(_double, _halve);
    const ROUND_TRIP_R: Conn<i32, i64, R> = Conn::new_r(_halve, _double);

    proptest! {
        #[test]
        fn swap_round_trip_l(a: i32, b: i64) {
            // (swap_r ∘ swap_l)(c) preserves the fn pair on every input.
            let c = ROUND_TRIP_L;
            let c2: Conn<i32, i64> = c.swap_l().swap_r();
            prop_assert_eq!(c.ceil(a), c2.ceil(a));
            prop_assert_eq!(c.upper(b), c2.upper(b));
        }

        #[test]
        fn swap_round_trip_r(a: i32, b: i64) {
            let c = ROUND_TRIP_R;
            let c2: Conn<i32, i64, R> = c.swap_r().swap_l();
            prop_assert_eq!(c.floor(a), c2.floor(a));
            prop_assert_eq!(c.lower(b), c2.lower(b));
        }
    }
}
