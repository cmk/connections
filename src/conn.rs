//! Galois-connection core: the [`Conn<A, B, K>`] type, the kind
//! markers [`L`] and [`R`], the [`ConnL`] / [`ConnR`] / [`ConnK`]
//! capability traits for adjoint connections, and the operations on
//! a `Conn` (kind-gated accessors and lifters, plus two-sided
//! rounding helpers on [`ConnK`]).
//!
//! ## Representation
//!
//! A Galois connection is mathematically a pair of monotone functions
//! `(f, g)` with `f: A → B` and `g: B → A` satisfying one of two
//! adjunction laws:
//!
//! - **Left-Galois (`L`):** `f(a) ≤ b ⟺ a ≤ g(b)`.  `f` is the lower
//!   adjoint (round-up / `ceil`); `g` is the upper adjoint (the
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
//! trait-impl bodies; no struct in the crate stores three fns.
//!
//! The trait names match the value-type spellings on purpose: the
//! blanket impl `impl ConnL for Conn<A, B, L>` makes every L-side
//! value satisfy [`ConnL`], same on the R side. So a generic bound
//! `T: ConnL<A, B>` accepts both triple markers and raw `Conn<A,B,L>`
//! values uniformly. The value type is spelled `Conn<A, B>` in
//! L-default position and `Conn<A, B, R>` on the R side.
//!
//! Two-sided operations ([`round`], [`truncate`], [`interval`],
//! [`midpoint`], [`median`], plus the `1` / `2` lifters) bind on
//! [`ConnK`] (`= ConnL + ConnR`), so they are callable only on
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
    pub fn ceil(self, a: A) -> B {
        (self.f)(a)
    }

    /// Apply the upper adjoint (embedding): `b ↦ g(b)`.
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

// ── ConnL / ConnR / ConnK capability traits ──────────────────────────

/// Capability trait: types implementing this carry an `L`-Galois
/// connection between `A` and `B`.
///
/// Two flavors of implementor:
/// 1. **ConnK markers** (zero-sized unit structs from [`conn_k!`] /
///    [`iso!`] / [`compose_k!`]) — they provide an L-view alongside
///    an R-view, gaining `.ceil()` / `.upper()` directly.
/// 2. **The value type itself** — a blanket impl on `Conn<A, B, L>`
///    (see below) means every L-Conn value is also a `ConnL`, so
///    generic bounds `T: ConnL<A, B>` accept both shapes uniformly.
///
/// `conn_l(&self) -> Conn<A, B, L>` is the projection. Default
/// methods dispatch through it: `ceil` is the lower adjoint
/// (rounds up), `upper` is the upper adjoint (the embedding).
///
/// Method-shape (rather than `const L: Conn<A, B, L>`) is required so
/// the blanket impl on `Conn<A, B, L>` can return `*self` — const
/// slots in trait impls cannot read instance state. For zero-sized
/// triple markers, the impl body inlines to two fn-pointer
/// constants, the same machine code a const slot would have produced.
pub trait ConnL<A: Copy, B: Copy> {
    /// The L-Galois projection: an `L`-kinded [`Conn<A, B>`].
    fn conn_l(&self) -> Conn<A, B, L>;

    /// Apply the lower adjoint (round-up): `a ↦ f(a)`.
    #[inline]
    #[must_use]
    fn ceil(&self, a: A) -> B {
        self.conn_l().ceil(a)
    }
    /// Apply the upper adjoint (embedding): `b ↦ g(b)`.
    #[inline]
    #[must_use]
    fn upper(&self, b: B) -> A {
        self.conn_l().upper(b)
    }
}

/// Capability trait: types implementing this carry an `R`-Galois
/// connection between `A` and `B`. Counterpart to [`ConnL`].
///
/// `conn_r(&self) -> Conn<A, B, R>` is the projection. Default
/// methods dispatch through it: `floor` is the upper adjoint
/// (rounds down), `lower` is the lower adjoint (the embedding).
pub trait ConnR<A: Copy, B: Copy> {
    /// The R-Galois projection: an `R`-kinded [`Conn<A, B, R>`].
    fn conn_r(&self) -> Conn<A, B, R>;

    /// Apply the upper adjoint (round-down): `a ↦ f(a)`.
    #[inline]
    #[must_use]
    fn floor(&self, a: A) -> B {
        self.conn_r().floor(a)
    }
    /// Apply the lower adjoint (embedding): `b ↦ g(b)`.
    #[inline]
    #[must_use]
    fn lower(&self, b: B) -> A {
        self.conn_r().lower(b)
    }
}

// ── Blanket impls: every Conn value satisfies its kind's trait ────────

impl<A: Copy, B: Copy> ConnL<A, B> for Conn<A, B, L> {
    #[inline]
    fn conn_l(&self) -> Conn<A, B, L> {
        *self
    }
}
impl<A: Copy, B: Copy> ConnR<A, B> for Conn<A, B, R> {
    #[inline]
    fn conn_r(&self) -> Conn<A, B, R> {
        *self
    }
}

/// Convenience super-trait: a type is a [`ConnK`] iff it implements
/// *both* [`ConnL`] and [`ConnR`] over the same `(A, B)`. Adjoint-
/// triple markers (and triple-shaped composed markers) implement
/// `ConnK` automatically via the blanket below; one-sided values
/// (`Conn<A, B, L>` and `Conn<A, B, R>`) do **not** — which is
/// correct, since a one-sided Conn isn't a triple.
pub trait ConnK<A: Copy, B: Copy>: ConnL<A, B> + ConnR<A, B> {}
impl<T, A: Copy, B: Copy> ConnK<A, B> for T where T: ConnL<A, B> + ConnR<A, B> {}

// ── Two-sided helpers (bound on ConnK) ────────────────────────────────

/// Compare the two halves of the conn-bracketed interval around `x`
/// for an adjoint triple `T`.
#[inline]
#[must_use]
pub fn interval<T, A, B>(t: &T, x: A) -> Option<Ordering>
where
    T: ConnK<A, B>,
    A: Copy + PartialOrd + Sub<Output = A>,
    B: Copy,
{
    let d_lo = x - t.conn_r().lower1(|b| b, x);
    let d_hi = t.conn_l().upper1(|b| b, x) - x;
    d_lo.partial_cmp(&d_hi)
}

/// Return the midpoint of the conn-bracketed interval around `x`.
#[inline]
#[must_use]
pub fn midpoint<T, A, B>(t: &T, x: A) -> A
where
    T: ConnK<A, B>,
    A: Copy + Add<Output = A> + Sub<Output = A> + Div<Output = A> + From<u8>,
    B: Copy,
{
    let lo = t.conn_r().lower1(|b| b, x);
    let hi = t.conn_l().upper1(|b| b, x);
    let two = A::from(2);
    lo + (hi - lo) / two
}

/// Truncate `x` toward zero through the triple: returns
/// `t.conn_r().floor(x)` when `x ≥ 0`, otherwise
/// `t.conn_l().ceil(x)`.
#[inline]
#[must_use]
pub fn truncate<T, A, B>(t: &T, x: A) -> B
where
    T: ConnK<A, B>,
    A: Copy + PartialOrd + From<u8>,
    B: Copy,
{
    if x >= A::from(0) {
        t.conn_r().floor(x)
    } else {
        t.conn_l().ceil(x)
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
#[inline]
#[must_use]
pub fn truncate1<T, A, B, H>(t: &T, h: H, x: B) -> B
where
    T: ConnK<A, B>,
    A: Copy + PartialOrd + From<u8>,
    B: Copy,
    H: FnOnce(A) -> A,
{
    truncate(t, h(t.conn_l().upper(x)))
}

/// Lift a binary function `h: (A, A) → A` through the triple, with
/// the result truncated toward zero.
#[inline]
#[must_use]
pub fn truncate2<T, A, B, H>(t: &T, h: H, x: B, y: B) -> B
where
    T: ConnK<A, B>,
    A: Copy + PartialOrd + From<u8>,
    B: Copy,
    H: FnOnce(A, A) -> A,
{
    let l = t.conn_l();
    truncate(t, h(l.upper(x), l.upper(y)))
}

/// Round `x` to the nearest representable value across the triple,
/// with ties broken toward zero.
#[inline]
#[must_use]
pub fn round<T, A, B>(t: &T, x: A) -> B
where
    T: ConnK<A, B>,
    A: Copy + PartialOrd + Sub<Output = A> + From<u8>,
    B: Copy,
{
    match interval(t, x) {
        Some(Ordering::Greater) => t.conn_l().ceil(x),
        Some(Ordering::Less) => t.conn_r().floor(x),
        _ => truncate(t, x),
    }
}

/// Lift a unary function `h: A → A` through the triple, rounded to
/// nearest with ties toward zero.
#[inline]
#[must_use]
pub fn round1<T, A, B, H>(t: &T, h: H, x: B) -> B
where
    T: ConnK<A, B>,
    A: Copy + PartialOrd + Sub<Output = A> + From<u8>,
    B: Copy,
    H: FnOnce(A) -> A,
{
    round(t, h(t.conn_l().upper(x)))
}

/// Lift a binary function `h: (A, A) → A` through the triple,
/// rounded to nearest with ties toward zero.
#[inline]
#[must_use]
pub fn round2<T, A, B, H>(t: &T, h: H, x: B, y: B) -> B
where
    T: ConnK<A, B>,
    A: Copy + PartialOrd + Sub<Output = A> + From<u8>,
    B: Copy,
    H: FnOnce(A, A) -> A,
{
    let l = t.conn_l();
    round(t, h(l.upper(x), l.upper(y)))
}

/// Birkhoff median over a triple `T: ConnK<(A, A), A>`, using the
/// triple's L-view ceil as join and R-view floor as meet.
#[inline]
#[must_use]
pub fn median<T, A>(t: &T, x: A, y: A, z: A) -> A
where
    T: ConnK<(A, A), A>,
    A: Copy,
{
    let join = |p: A, q: A| t.conn_l().ceil((p, q));
    let meet = |p: A, q: A| t.conn_r().floor((p, q));
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

/// Forwarding alias for [`compose_l!`] — mirrors the `K = L` default
/// of [`Conn`]. Use when composing L-side conns and you'd rather not
/// spell the side explicitly. Error spans may point at this
/// forwarder rather than [`compose_l!`] directly.
///
/// ```ignore
/// const FOO: Conn<A, C> = compose!(BAR_AB, BAZ_BC);
/// ```
#[macro_export]
macro_rules! compose {
    ($($t:tt)*) => { $crate::compose_l!($($t)*) };
}

/// Declaration-form macro: compose two adjoint-triple markers into a
/// fresh triple marker. The composed marker is a unit struct with
/// freshly-built `ConnL` and `ConnR` impls whose `conn_l` / `conn_r`
/// methods build the projection via [`compose_l!`] / [`compose_r!`]
/// over the parents' views.
///
/// ```ignore
/// compose_k!(F064F016 : F064 => F032 => F016 = F064F032, F032F016);
/// ```
#[macro_export]
macro_rules! compose_k {
    ($name:ident : $A:ty => $B:ty => $C:ty = $t1:path, $t2:path $(,)?) => {
        pub struct $name;
        impl $crate::conn::ConnL<$A, $C> for $name {
            #[inline]
            fn conn_l(&self) -> $crate::conn::Conn<$A, $C, $crate::conn::L> {
                $crate::compose_l!(
                    <$t1 as $crate::conn::ConnL<$A, $B>>::conn_l(&$t1),
                    <$t2 as $crate::conn::ConnL<$B, $C>>::conn_l(&$t2),
                )
            }
        }
        impl $crate::conn::ConnR<$A, $C> for $name {
            #[inline]
            fn conn_r(&self) -> $crate::conn::Conn<$A, $C, $crate::conn::R> {
                $crate::compose_r!(
                    <$t1 as $crate::conn::ConnR<$A, $B>>::conn_r(&$t1),
                    <$t2 as $crate::conn::ConnR<$B, $C>>::conn_r(&$t2),
                )
            }
        }
    };
}

/// Declaration-form macro: ship a new adjoint-triple marker from
/// three free-function paths `(ceil, inner, floor)`.
///
/// ```ignore
/// conn_k! {
///     pub F064F032 : F064 => F032 {
///         ceil:  ceil_f64_to_f32,
///         inner: inner_f32_to_f64,
///         floor: floor_f64_to_f32,
///     }
/// }
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
        $vis struct $name;
        impl $crate::conn::ConnL<$A, $B> for $name {
            #[inline]
            fn conn_l(&self) -> $crate::conn::Conn<$A, $B, $crate::conn::L> {
                $crate::conn::Conn::new_l($ceil, $inner)
            }
        }
        impl $crate::conn::ConnR<$A, $B> for $name {
            #[inline]
            fn conn_r(&self) -> $crate::conn::Conn<$A, $B, $crate::conn::R> {
                $crate::conn::Conn::new_r($inner, $floor)
            }
        }
    };
}

/// Declaration-form macro: ship a degenerate-Galois iso (lossless
/// bijection) from a single `(forward, back)` function pair.
///
/// Equivalent to [`conn_k!`] with `ceil = floor = forward`; the macro
/// name itself flags the bijection so the body fields read as
/// `forward` / `back` rather than `ceil` / `inner` / `floor`. Both
/// [`ConnL`] and [`ConnR`] are implemented; every iso law
/// (`galois_l`, `galois_r`, `floor_le_ceil`, `idempotent`, …) holds
/// trivially.
///
/// ```ignore
/// iso! {
///     pub U032IPV4 : u32 => Ipv4Addr {
///         forward: u32_to_v4,
///         back:    v4_to_u32,
///     }
/// }
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
/// Named-field syntax mirrors [`conn_k!`] / [`iso!`] and removes the
/// argument-order footgun on [`Conn::new_l`]: the field labels make
/// it impossible to swap `ceil` and `inner` accidentally (and the
/// `_l` / `_r` macro-name split prevents picking the wrong kind).
///
/// Unlike [`conn_k!`], this macro emits the `Conn` value directly —
/// not a marker struct with [`ConnL`] / [`ConnR`] impls — because no
/// adjoint triple exists for one-sided connections. Use [`conn_k!`]
/// when both `ceil` and `floor` are available and the inner
/// embedding is order-reflecting; use this macro when only the
/// left half of the adjunction holds.
///
/// ```ignore
/// conn_l! {
///     pub TIMENANO : Extended<Time> => i64 {
///         ceil:  time_to_ns,
///         inner: ns_to_time,
///     }
/// }
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
/// Named-field syntax mirrors [`conn_k!`] / [`iso!`] and removes the
/// argument-order footgun on [`Conn::new_r`] — whose positional
/// shape `(inner, floor)` (mirroring Haskell's `CastR`) is the
/// reverse of [`Conn::new_l`]'s `(ceil, inner)`. Field labels make
/// the order self-documenting.
///
/// ```ignore
/// conn_r! {
///     pub UFOO : u8 => i8 {
///         inner: u_to_i,
///         floor: i_to_u,
///     }
/// }
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
        assert_eq!(TripleIdI32.ceil(7_i32), 7_i32);
        assert_eq!(TripleIdI32.floor(7_i32), 7_i32);
        assert_eq!(TripleIdI32.upper(7_i32), 7_i32);
        assert_eq!(TripleIdI32.lower(7_i32), 7_i32);
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
            assert_eq!(IsoI32U32.ceil(x), IsoI32U32.floor(x));
        }
    }

    #[test]
    fn iso_round_trip_both_directions() {
        for x in [i32::MIN, -1, 0, 1, 42, i32::MAX] {
            let y = IsoI32U32.ceil(x);
            assert_eq!(IsoI32U32.upper(y), x);
        }
        for y in [0_u32, 1, 42, u32::MAX] {
            let x = IsoI32U32.upper(y);
            assert_eq!(IsoI32U32.ceil(x), y);
        }
    }

    #[test]
    fn compose_triple_marker() {
        // Composed triple's L-view: ceil(x) = TripleAdd1.ceil(TripleIdI32.ceil(x)) = x + 1
        assert_eq!(ComposedI32.ceil(0_i32), 1_i32);
        // Composed triple's R-view: floor(x) = TripleAdd1.floor(TripleIdI32.floor(x)) = x + 1
        assert_eq!(ComposedI32.floor(0_i32), 1_i32);
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

    // ── Blanket-impl smoke test: a Conn value satisfies its trait ────

    #[test]
    fn conn_value_impls_trait() {
        // The blanket impls let a raw `Conn<_,_,L>` value flow through
        // a `T: ConnL<_,_>` bound. Same on the R side.
        fn use_as_conn_l<T: ConnL<i64, i32>>(t: &T, a: i64) -> i32 {
            t.ceil(a)
        }
        fn use_as_conn_r<T: ConnR<i64, i32>>(t: &T, a: i64) -> i32 {
            t.floor(a)
        }
        assert_eq!(use_as_conn_l(&CONNLI64I32, 42_i64), 42_i32);
        assert_eq!(use_as_conn_r(&CONNRI64I32, 42_i64), 42_i32);
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
