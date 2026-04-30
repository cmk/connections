//! Galois-connection core: the [`Conn<A, B, K>`] type, the kind
//! markers [`L`] and [`R`], the [`ViewL`] / [`ViewR`] / [`Triple`]
//! projection traits for adjoint triples, and the operations on a
//! `Conn` (kind-gated accessors and lifters, plus two-sided rounding
//! helpers on `Triple`).
//!
//! ## Representation
//!
//! A Galois connection is mathematically a pair of monotone functions
//! `(f, g)` with `f: A → B` and `g: B → A` satisfying one of two
//! adjunction laws:
//!
//! - **Left-Galois (`L`):** `f(a) ≤ b ⟺ a ≤ g(b)`.  `f` is the lower
//!   adjoint (round-up / `ceiling`); `g` is the upper adjoint (the
//!   embedding / `upper`).
//! - **Right-Galois (`R`):** `g(b) ≤ a ⟺ b ≤ f(a)`.  `g` is the
//!   lower adjoint (`lower`); `f` is the upper adjoint (round-down /
//!   `floor`).
//!
//! [`Conn<A, B, K>`] holds *exactly two* fn-pointer fields, and the
//! kind tag `K` (defaulting to [`L`]) determines which adjoint role
//! each field plays. Kind-specific inherent methods enforce the
//! discipline at the type level: calling `.floor(...)` on an
//! `Conn<_, _, L>` is a compile error (the method only exists on
//! `Conn<_, _, R>`); same for `.ceiling(...)` on `R`.
//!
//! An **adjoint triple** `f ⊣ g ⊣ h` is two adjunctions sharing the
//! middle function `g`: an L-Galois pair `(f, g)` and an R-Galois pair
//! `(g, h)` over the same `(A, B)`. Triples are *not* a third kind of
//! `Conn`; instead they are zero-sized marker types implementing the
//! [`ViewL`] / [`ViewR`] projection traits, whose associated consts
//! [`ViewL::L`] and [`ViewR::R`] are the L-view and R-view `Conn`s of
//! the triple. The "third function" — the adjoint that distinguishes
//! a triple from a one-sided Conn — lives as a free function in module
//! scope, referenced from the marker's trait-impl bodies; no struct
//! in the crate stores three fns.
//!
//! Two-sided operations ([`round`], [`truncate`], [`interval`],
//! [`midpoint`], [`median`], plus the `1` / `2` lifters) bind on
//! [`Triple`] (`= ViewL + ViewR`), so they are callable only on
//! triple markers, not on one-sided Conns.

use core::cmp::Ordering;
use core::marker::PhantomData;
use core::ops::{Add, Div, Sub};

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

/// Type alias: a left-Galois `Conn`.
pub type ConnL<A, B> = Conn<A, B, L>;
/// Type alias: a right-Galois `Conn`.
pub type ConnR<A, B> = Conn<A, B, R>;

// ── Conn struct ──────────────────────────────────────────────────────

/// A Galois connection between preordered sets `A` and `B`, kind-tagged
/// by `K` (defaults to [`L`]).
///
/// Holds two `fn`-pointer fields whose adjoint roles depend on the kind:
///
/// | Kind | `f`           | `g`           | Galois law                           |
/// |------|---------------|---------------|--------------------------------------|
/// | [`L`] | lower (`ceiling`)  | upper (`upper`) | `f(a) ≤ b ⟺ a ≤ g(b)`              |
/// | [`R`] | upper (`floor`)   | lower (`lower`) | `g(b) ≤ a ⟺ b ≤ f(a)`              |
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
    #[inline]
    #[must_use]
    pub fn ceiling(self, a: A) -> B {
        (self.f)(a)
    }

    /// Apply the upper adjoint (embedding): `b ↦ g(b)`.
    #[inline]
    #[must_use]
    pub fn upper(self, b: B) -> A {
        (self.g)(b)
    }

    /// Backwards-compat alias for [`Self::ceiling`].
    #[inline]
    #[must_use]
    pub fn ceil(self, a: A) -> B {
        (self.f)(a)
    }

    /// Backwards-compat alias for [`Self::upper`].
    #[inline]
    #[must_use]
    pub fn inner(self, b: B) -> A {
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
    #[inline]
    #[must_use]
    pub fn ceiling1<H>(self, h: H, b: B) -> B
    where
        H: FnOnce(A) -> A,
    {
        (self.f)(h((self.g)(b)))
    }

    /// Lift a binary function over `A` through the L-pair.
    #[inline]
    #[must_use]
    pub fn ceiling2<H>(self, h: H, b1: B, b2: B) -> B
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

    /// Backwards-compat alias for [`Self::lower`].
    #[inline]
    #[must_use]
    pub fn inner(self, b: B) -> A {
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

// ── Identity ─────────────────────────────────────────────────────────

impl<X> Conn<X, X, L> {
    /// The identity connection: `f = g = id`. L-kinded by default
    /// (every identity connection trivially satisfies both Galois
    /// laws; pick L by convention).
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

// ── ViewL / ViewR / Triple traits for adjoint triples ────────────────

/// Projection trait: types implementing this carry an `L`-view of an
/// adjoint connection between `A` and `B`. Adjoint-triple markers
/// implement this alongside [`ViewR`].
///
/// Default methods dispatch through [`Self::L`] so values that
/// implement [`ViewL`] gain `.ceiling()` / `.upper()` (and the
/// back-compat aliases `.ceil()` / `.inner()`) directly.
pub trait ViewL<A: Copy, B: Copy> {
    /// The L-view: an `L`-kinded `Conn<A, B>`.
    const L: ConnL<A, B>;

    /// Apply the L-view's lower adjoint.
    #[inline]
    #[must_use]
    fn ceiling(&self, a: A) -> B {
        Self::L.ceiling(a)
    }
    /// Apply the L-view's upper adjoint (embedding).
    #[inline]
    #[must_use]
    fn upper(&self, b: B) -> A {
        Self::L.upper(b)
    }
    /// Backwards-compat alias for [`Self::ceiling`].
    #[inline]
    #[must_use]
    fn ceil(&self, a: A) -> B {
        Self::L.ceiling(a)
    }
    /// Backwards-compat alias for [`Self::upper`].
    #[inline]
    #[must_use]
    fn inner(&self, b: B) -> A {
        Self::L.upper(b)
    }
}

/// Projection trait: types implementing this carry an `R`-view of an
/// adjoint connection between `A` and `B`. Adjoint-triple markers
/// implement this alongside [`ViewL`].
///
/// Default methods give values that implement [`ViewR`] direct
/// `.floor()` / `.lower()` access.
pub trait ViewR<A: Copy, B: Copy> {
    /// The R-view: an `R`-kinded `Conn<A, B>`.
    const R: ConnR<A, B>;

    /// Apply the R-view's upper adjoint.
    #[inline]
    #[must_use]
    fn floor(&self, a: A) -> B {
        Self::R.floor(a)
    }
    /// Apply the R-view's lower adjoint (embedding).
    #[inline]
    #[must_use]
    fn lower(&self, b: B) -> A {
        Self::R.lower(b)
    }
}

/// Convenience super-trait: a type is a [`Triple`] iff it implements
/// *both* [`ViewL`] and [`ViewR`] over the same `(A, B)`. Two-sided
/// operations bind on this trait.
pub trait Triple<A: Copy, B: Copy>: ViewL<A, B> + ViewR<A, B> {}
impl<T, A: Copy, B: Copy> Triple<A, B> for T where T: ViewL<A, B> + ViewR<A, B> {}

// ── Two-sided helpers (bound on Triple) ──────────────────────────────

/// Compare the two halves of the conn-bracketed interval around `x`
/// for an adjoint triple `T`.
#[inline]
#[must_use]
pub fn interval<T, A, B>(_t: &T, x: A) -> Option<Ordering>
where
    T: Triple<A, B>,
    A: Copy + PartialOrd + Sub<Output = A>,
    B: Copy,
{
    let d_lo = x - <T as ViewR<A, B>>::R.lower1(|b| b, x);
    let d_hi = <T as ViewL<A, B>>::L.upper1(|b| b, x) - x;
    d_lo.partial_cmp(&d_hi)
}

/// Return the midpoint of the conn-bracketed interval around `x`.
#[inline]
#[must_use]
pub fn midpoint<T, A, B>(_t: &T, x: A) -> A
where
    T: Triple<A, B>,
    A: Copy + Add<Output = A> + Sub<Output = A> + Div<Output = A> + From<u8>,
    B: Copy,
{
    let lo = <T as ViewR<A, B>>::R.lower1(|b| b, x);
    let hi = <T as ViewL<A, B>>::L.upper1(|b| b, x);
    let two = A::from(2);
    lo + (hi - lo) / two
}

/// Truncate `x` toward zero through the triple: returns
/// `T::R.floor(x)` when `x ≥ 0`, otherwise `T::L.ceiling(x)`.
#[inline]
#[must_use]
pub fn truncate<T, A, B>(_t: &T, x: A) -> B
where
    T: Triple<A, B>,
    A: Copy + PartialOrd + From<u8>,
    B: Copy,
{
    if x >= A::from(0) {
        <T as ViewR<A, B>>::R.floor(x)
    } else {
        <T as ViewL<A, B>>::L.ceiling(x)
    }
}

/// Lift a unary function `h: A → A` through the triple, with the
/// result truncated toward zero.
#[inline]
#[must_use]
pub fn truncate1<T, A, B, H>(t: &T, h: H, x: B) -> B
where
    T: Triple<A, B>,
    A: Copy + PartialOrd + From<u8>,
    B: Copy,
    H: FnOnce(A) -> A,
{
    truncate(t, h(<T as ViewL<A, B>>::L.upper(x)))
}

/// Lift a binary function `h: (A, A) → A` through the triple, with
/// the result truncated toward zero.
#[inline]
#[must_use]
pub fn truncate2<T, A, B, H>(t: &T, h: H, x: B, y: B) -> B
where
    T: Triple<A, B>,
    A: Copy + PartialOrd + From<u8>,
    B: Copy,
    H: FnOnce(A, A) -> A,
{
    let l = <T as ViewL<A, B>>::L;
    truncate(t, h(l.upper(x), l.upper(y)))
}

/// Round `x` to the nearest representable value across the triple,
/// with ties broken toward zero.
#[inline]
#[must_use]
pub fn round<T, A, B>(t: &T, x: A) -> B
where
    T: Triple<A, B>,
    A: Copy + PartialOrd + Sub<Output = A> + From<u8>,
    B: Copy,
{
    match interval(t, x) {
        Some(Ordering::Greater) => <T as ViewL<A, B>>::L.ceiling(x),
        Some(Ordering::Less) => <T as ViewR<A, B>>::R.floor(x),
        _ => truncate(t, x),
    }
}

/// Lift a unary function `h: A → A` through the triple, rounded to
/// nearest with ties toward zero.
#[inline]
#[must_use]
pub fn round1<T, A, B, H>(t: &T, h: H, x: B) -> B
where
    T: Triple<A, B>,
    A: Copy + PartialOrd + Sub<Output = A> + From<u8>,
    B: Copy,
    H: FnOnce(A) -> A,
{
    round(t, h(<T as ViewL<A, B>>::L.upper(x)))
}

/// Lift a binary function `h: (A, A) → A` through the triple,
/// rounded to nearest with ties toward zero.
#[inline]
#[must_use]
pub fn round2<T, A, B, H>(t: &T, h: H, x: B, y: B) -> B
where
    T: Triple<A, B>,
    A: Copy + PartialOrd + Sub<Output = A> + From<u8>,
    B: Copy,
    H: FnOnce(A, A) -> A,
{
    let l = <T as ViewL<A, B>>::L;
    round(t, h(l.upper(x), l.upper(y)))
}

/// Birkhoff median over a triple `T: Triple<(A, A), A>`, using the
/// triple's L-view ceiling as join and R-view floor as meet.
#[inline]
#[must_use]
pub fn median<T, A>(_t: &T, x: A, y: A, z: A) -> A
where
    T: Triple<(A, A), A>,
    A: Copy,
{
    let join = |p: A, q: A| <T as ViewL<(A, A), A>>::L.ceiling((p, q));
    let meet = |p: A, q: A| <T as ViewR<(A, A), A>>::R.floor((p, q));
    meet(meet(join(x, y), join(y, z)), join(z, x))
}

// ── Composition macros ───────────────────────────────────────────────

/// Compose a chain of L-Conn paths into a single fresh `ConnL<Src, Dst>`.
///
/// Variadic over two or more parents. The expansion uses non-capturing
/// closures referencing the parent paths so each closure coerces to
/// an `fn(_) -> _` pointer at the `Conn::new_l` call site.
#[macro_export]
macro_rules! compose_l {
    ($first:path $(, $rest:path)+ $(,)?) => {
        $crate::conn::Conn::new_l(
            |a| $crate::compose_l!(@nest_f a; $first $(, $rest)+),
            |z| $crate::compose_l!(@nest_g z; $first $(, $rest)+),
        )
    };

    (@nest_f $x:expr; $last:path) => { $last.ceiling($x) };
    (@nest_f $x:expr; $first:path $(, $rest:path)+) => {
        $crate::compose_l!(@nest_f $first.ceiling($x); $($rest),+)
    };

    (@nest_g $z:expr; $last:path) => { $last.upper($z) };
    (@nest_g $z:expr; $first:path $(, $rest:path)+) => {
        $first.upper($crate::compose_l!(@nest_g $z; $($rest),+))
    };
}

/// Compose a chain of R-Conn paths into a single fresh `ConnR<Src, Dst>`.
#[macro_export]
macro_rules! compose_r {
    ($first:path $(, $rest:path)+ $(,)?) => {
        $crate::conn::Conn::new_r(
            |z| $crate::compose_r!(@nest_g z; $first $(, $rest)+),
            |a| $crate::compose_r!(@nest_f a; $first $(, $rest)+),
        )
    };

    (@nest_f $x:expr; $last:path) => { $last.floor($x) };
    (@nest_f $x:expr; $first:path $(, $rest:path)+) => {
        $crate::compose_r!(@nest_f $first.floor($x); $($rest),+)
    };

    (@nest_g $z:expr; $last:path) => { $last.lower($z) };
    (@nest_g $z:expr; $first:path $(, $rest:path)+) => {
        $first.lower($crate::compose_r!(@nest_g $z; $($rest),+))
    };
}

/// Declaration-form macro: compose two adjoint-triple markers into a
/// fresh triple marker. The composed marker is a unit struct with
/// freshly-built `ViewL` and `ViewR` impls whose associated consts
/// come from [`compose_l!`] / [`compose_r!`] over the parents' views.
///
/// ```ignore
/// compose!(F064F016 : F064 => F032 => F016 = F064F032, F032F016);
/// ```
#[macro_export]
macro_rules! compose {
    ($name:ident : $A:ty => $B:ty => $C:ty = $t1:path, $t2:path $(,)?) => {
        pub struct $name;
        impl $crate::conn::ViewL<$A, $C> for $name {
            const L: $crate::conn::ConnL<$A, $C> = $crate::compose_l!(
                <$t1 as $crate::conn::ViewL<$A, $B>>::L,
                <$t2 as $crate::conn::ViewL<$B, $C>>::L,
            );
        }
        impl $crate::conn::ViewR<$A, $C> for $name {
            const R: $crate::conn::ConnR<$A, $C> = $crate::compose_r!(
                <$t1 as $crate::conn::ViewR<$A, $B>>::R,
                <$t2 as $crate::conn::ViewR<$B, $C>>::R,
            );
        }
    };
}

/// Declaration-form macro: ship a new adjoint-triple marker from
/// three free-function paths `(ceil, inner, floor)`.
///
/// ```ignore
/// triple! {
///     pub F064F032 : F064 => F032 {
///         ceil:  ceil_f64_to_f32,
///         inner: inner_f32_to_f64,
///         floor: floor_f64_to_f32,
///     }
/// }
/// ```
#[macro_export]
macro_rules! triple {
    (
        $(#[$meta:meta])*
        $vis:vis $name:ident : $A:ty => $B:ty {
            ceil:  $ceil:expr,
            inner: $inner:expr,
            floor: $floor:expr $(,)?
        }
    ) => {
        $(#[$meta])*
        $vis struct $name;
        impl $crate::conn::ViewL<$A, $B> for $name {
            const L: $crate::conn::ConnL<$A, $B> =
                $crate::conn::Conn::new_l($ceil, $inner);
        }
        impl $crate::conn::ViewR<$A, $B> for $name {
            const R: $crate::conn::ConnR<$A, $B> =
                $crate::conn::Conn::new_r($inner, $floor);
        }
    };
}
