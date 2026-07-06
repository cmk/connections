//! `Extended<T>` wraps a totally-ordered `T` with `NegInf` (bottom) and
//! `PosInf` (top). Used as the target of connections whose target type
//! cannot represent the full range of the source — e.g. a float source
//! feeding into a bounded integer rung saturates to `NegInf`/`PosInf`
//! when the finite range is exceeded.
//!
//! `Extended` is a pure range-extension wrapper; it does not participate
//! in float NaN handling — that lives in
//! [`crate::float::ExtendedFloat`].
//!
//! ## Functor-lift macros
//!
//! When chaining a Conn whose endpoint is already `Extended<…>` with one
//! whose corresponding side is a bare type, the chain fails to type-check.
//! [`lift_l!`](crate::lift_l) / [`lift_r!`](crate::lift_r) /
//! [`lift_k!`](crate::lift_k) wrap **both** endpoints of the bare-side
//! Conn so the chain composes. The lift is the categorical functor-lift
//! of the parent through `Extended`: synthetic markers map identically
//! (`NegInf ↦ NegInf`, `PosInf ↦ PosInf`), and the `Finite` arm
//! dispatches through the parent. Every law in
//! [`crate::prop::conn`] that holds on the parent carries to the lifted
//! Conn for free.
//!
//! ### Combining with `compose_*!`
//!
//! The lift macros are designed to interoperate with the existing
//! [`compose_l!`](crate::compose_l) / [`compose_r!`](crate::compose_r) /
//! [`compose_k!`](crate::compose_k) family. The output shape determines
//! which `compose_*!` accepts each form:
//!
//! - `lift_l!(parent)` returns a [`Conn<Extended<A>, Extended<B>, L>`]
//!   *value*. It composes into [`compose_l!`](crate::compose_l) as
//!   either operand. The macro takes `$parent:path` (a `pub const`
//!   Conn or a unit-struct marker), so the lift is always a const
//!   expression — the whole compose chain const-evaluates if its
//!   other operands are also const.
//! - `lift_r!(parent)` returns a [`Conn<…, R>`] value; same story for
//!   [`compose_r!`](crate::compose_r).
//! - `lift_k!(NAME : A => B = parent)` emits a unit-struct **marker**
//!   that impls `ConnL`+`ConnR` (i.e. `ConnK`). Such a marker flows
//!   into all three forms — [`compose_l!`](crate::compose_l) /
//!   [`compose_r!`](crate::compose_r) via its views (the inherent
//!   `view_l` / `view_r`, crate-local to wherever the marker is
//!   declared; from another crate, the public
//!   [`view_l`](crate::conn::view_l)`(&M)` /
//!   [`view_r`](crate::conn::view_r)`(&M)` free functions), and
//!   [`compose_k!`](crate::compose_k) directly as a path operand.
//! - The output of [`compose_k!`](crate::compose_k) is itself a `ConnK`
//!   marker, so chains can nest arbitrarily — `lift_k!` over the result
//!   of a `compose_k!`, or vice versa.
//!
//! Const-init combo (`lift_l!` value into `compose_l!`):
//!
//! ```
//! use connections::compose_l;
//! use connections::conn::{Conn, L};
//! use connections::extended::Extended;
//! use connections::lift_l;
//!
//! const ID:     Conn<i64, i64, L>                     = Conn::identity();
//! const LIFTED: Conn<Extended<i64>, Extended<i64>, L> = lift_l!(ID);
//! const ID_E:   Conn<Extended<i64>, Extended<i64>, L> = Conn::identity();
//!
//! // compose_l! splices the lifted Conn into a chain whose other leg
//! // already operates on Extended<i64>. Const-init throughout.
//! const CHAIN: Conn<Extended<i64>, Extended<i64>, L> =
//!     compose_l!(LIFTED, ID_E);
//!
//! assert_eq!(CHAIN.ceil(Extended::Finite(7)),  Extended::Finite(7));
//! assert_eq!(CHAIN.upper(Extended::PosInf),    Extended::PosInf);
//! ```
//!
//! Marker combo (`lift_k!` marker into `compose_k!`, then back into
//! `compose_l!`):
//!
//! ```text
//! use connections::compose_k;
//! use connections::conn::{Conn, L};
//! use connections::extended::Extended;
//! use connections::fixed::i016::Q000I016;
//! use connections::{compose_l, lift_k};
//! use fixed::FixedI16;
//! use fixed::types::extra::U0;
//!
//! // Lift the iso Q000I016 through Extended on both sides.
//! lift_k!(EXTQ : FixedI16<U0> => i16 = Q000I016);
//!
//! // compose_k! takes the lift_k! marker as a path operand, chains
//! // it with another ConnK marker (here: the same lift again,
//! // standing in for any Extended<FixedI16<U0>> ↔ Extended<X> bridge),
//! // and emits a fresh marker for the composed chain.
//! compose_k!(CHAIN_K : Extended<i16> => Extended<FixedI16<U0>> => Extended<FixedI16<U0>>
//!            = EXTQ, EXTQ_IDENTITY);
//!
//! // Stand-in identity bridge to make the doctest self-contained.
//! // Declared through conn_k! — compose_k! operands need the
//! // macro-emitted crate-local views, so markers are declared with
//! // the declaration macros, never hand-rolled trait impls.
//! const fn ext_id(x: Extended<FixedI16<U0>>) -> Extended<FixedI16<U0>> { x }
//! connections::conn_k! {
//!     EXTQ_IDENTITY : Extended<FixedI16<U0>> => Extended<FixedI16<U0>> {
//!         ceil:  ext_id,
//!         inner: ext_id,
//!         floor: ext_id,
//!     }
//! }
//!
//! // The composed marker can flow back into compose_l! as either
//! // operand at runtime via `.view_l()`.
//! let final_chain = compose_l!(CHAIN_K.view_l(), EXTQ_IDENTITY.view_l());
//! let q = FixedI16::<U0>::from_bits(7);
//! assert_eq!(final_chain.ceil(Extended::Finite(7_i16)), Extended::Finite(q));
//! ```
//!
//! [`Conn<Extended<A>, Extended<B>, L>`]: crate::conn::Conn
//! [`Conn<…, R>`]: crate::conn::Conn

/// A totally-ordered `T` extended with synthetic `NegInf` (bottom) and
/// `PosInf` (top) sentinels.
///
/// Used as the target of connections whose source type cannot fit
/// inside the destination — e.g. an `Extended<i8> → i16` widening lifts
/// the source's `MIN`/`MAX` into the open interval `(NegInf, PosInf)`,
/// leaving the synthetic markers free to record overflow on the way
/// back through `inner`. The order is `NegInf < every Finite(t) < PosInf`,
/// making `Extended<T>` a bounded total order whenever `T` is one.
///
/// `Extended` is a *pure range-extension* wrapper; it does not encode
/// float NaN. NaN-bearing types live in
/// [`crate::float::ExtendedFloat`], which carries an `Extend(t)` arm
/// instead and threads NaN through the N5 lattice.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Extended<T> {
    /// Synthetic bottom: less than every `Finite(t)` and less than `PosInf`.
    NegInf,
    /// A value of the underlying type, with its native order.
    Finite(T),
    /// Synthetic top: greater than every `Finite(t)` and greater than `NegInf`.
    PosInf,
}

impl<T> Extended<T> {
    /// Catamorphism: collapse an `Extended<T>` to a `U` by supplying
    /// one value per variant.
    ///
    /// The Rust analogue of Haskell's
    /// `extended :: Extended a -> b -> b -> (a -> b) -> b`. Argument
    /// order follows Rust's closure-last convention
    /// (`Iterator::fold`, `Option::map_or`).
    ///
    /// Endpoint arms are evaluated eagerly. For lazy endpoints, see
    /// [`Extended::fold_with`].
    ///
    /// ```
    /// use connections::extended::Extended;
    ///
    /// fn classify(x: Extended<i64>) -> &'static str {
    ///     x.fold("below", "above", |_| "in range")
    /// }
    /// assert_eq!(classify(Extended::NegInf), "below");
    /// assert_eq!(classify(Extended::Finite(7)), "in range");
    /// assert_eq!(classify(Extended::PosInf), "above");
    /// ```
    pub fn fold<U>(self, neg_inf: U, pos_inf: U, f: impl FnOnce(T) -> U) -> U {
        match self {
            Extended::NegInf => neg_inf,
            Extended::Finite(t) => f(t),
            Extended::PosInf => pos_inf,
        }
    }

    /// Lazy variant of [`Extended::fold`]: all three arms are wrapped
    /// in [`FnOnce`] closures and only the matched arm is called.
    /// Use when any endpoint default is expensive to compute.
    pub fn fold_with<U>(
        self,
        neg_inf: impl FnOnce() -> U,
        pos_inf: impl FnOnce() -> U,
        f: impl FnOnce(T) -> U,
    ) -> U {
        match self {
            Extended::NegInf => neg_inf(),
            Extended::Finite(t) => f(t),
            Extended::PosInf => pos_inf(),
        }
    }
}

impl<T: PartialOrd> PartialOrd for Extended<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        use Extended::*;
        use std::cmp::Ordering::*;
        match (self, other) {
            (NegInf, NegInf) => Some(Equal),
            (PosInf, PosInf) => Some(Equal),
            (NegInf, _) => Some(Less),
            (_, NegInf) => Some(Greater),
            (_, PosInf) => Some(Less),
            (PosInf, _) => Some(Greater),
            (Finite(a), Finite(b)) => a.partial_cmp(b),
        }
    }
}

impl<T: Ord> Ord for Extended<T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // Safe: PartialOrd on Extended returns Some for any Ord T.
        self.partial_cmp(other).unwrap()
    }
}

// ── Functor-lift macros ────────────────────────────────────────────
//
// The macros below specialise the Haskell `mapped :: Functor f =>
// Cast k a b -> Cast k (f a) (f b)` to `f = Extended`. Rust without
// HKT can't write a generic functor-lift, but `Extended` is the only
// crate-wide saturation functor where the lift is meaningful, so a
// concrete-functor specialisation is all that's needed.
//
// Macro form (rather than free fn) because `Conn<A, B, K>` stores
// `fn(_) -> _` pointer fields — Rust fn-pointers can't capture
// environment, so a free fn `lift_l(parent: Conn<A, B, L>) -> Conn<…>`
// can't synthesise the lifted `fn` from `parent.f`. Each macro
// expansion emits a non-capturing closure that references the parent
// through a stable path (a `pub const` or unit-marker), so the
// closure coerces to a fn-pointer at compile time. Same trick the
// `compose_l!` / `compose_k!` family already uses.

/// Lift an L-Galois `Conn` (or any [`ConnL`](crate::conn::ConnL) impl)
/// through the [`Extended`] functor.
///
/// Produces a fresh `Conn<Extended<A>, Extended<B>, L>` whose
/// synthetic markers map identically (`NegInf → NegInf`,
/// `PosInf → PosInf`) and whose `Finite` arm dispatches through the
/// parent's `ceil` / `upper`.
///
/// **Argument constraint:** `$parent` must be a *stable path* — a
/// `pub const` Conn value or a unit-struct marker that impls
/// [`ConnL`](crate::conn::ConnL). The fragment specifier is `:path`,
/// matching `lift_k!`'s constraint, which (a) prevents the
/// double-evaluation hazard that an `:expr` fragment would allow
/// (the parent is referenced inside two separate fn-pointer-coerced
/// closures, so a non-path expression like `build_conn()` would be
/// re-evaluated on each `ceil` / `upper` call), and (b) gives a
/// parse-time error rather than the deferred fn-pointer-coercion
/// type error you'd get from a let-bound `Conn` value. To lift
/// something built at runtime, bind it to a `const` first (or use
/// `lift_k!` with a marker parent).
///
/// # Examples
///
/// ```
/// use connections::conn::{Conn, L};
/// use connections::extended::Extended;
/// use connections::lift_l;
///
/// const ID: Conn<i64, i64, L> = Conn::identity();
/// const LIFTED: Conn<Extended<i64>, Extended<i64>, L> = lift_l!(ID);
///
/// assert_eq!(LIFTED.ceil(Extended::NegInf), Extended::NegInf);
/// assert_eq!(LIFTED.ceil(Extended::PosInf), Extended::PosInf);
/// assert_eq!(LIFTED.ceil(Extended::Finite(7_i64)), Extended::Finite(7_i64));
/// ```
#[macro_export]
macro_rules! lift_l {
    ($parent:expr) => {
        $crate::conn::Conn::new_l(
            |a| match a {
                $crate::extended::Extended::NegInf => $crate::extended::Extended::NegInf,
                $crate::extended::Extended::Finite(x) => {
                    $crate::extended::Extended::Finite(($parent).ceil(x))
                }
                $crate::extended::Extended::PosInf => $crate::extended::Extended::PosInf,
            },
            |b| match b {
                $crate::extended::Extended::NegInf => $crate::extended::Extended::NegInf,
                $crate::extended::Extended::Finite(y) => {
                    $crate::extended::Extended::Finite(($parent).upper(y))
                }
                $crate::extended::Extended::PosInf => $crate::extended::Extended::PosInf,
            },
        )
    };
}

/// Lift an R-Galois `Conn` (or any [`ConnR`](crate::conn::ConnR) impl)
/// through the [`Extended`] functor. Mirrors [`lift_l!`](crate::lift_l):
/// produces a fresh `Conn<Extended<A>, Extended<B>, R>` whose
/// synthetic markers map identically and whose `Finite` arm
/// dispatches through the parent's `lower` / `floor`.
///
/// `$parent` is `:path` for the same reasons as
/// [`lift_l!`](crate::lift_l) — see that macro's docs for the
/// double-evaluation rationale.
///
/// # Examples
///
/// ```
/// use connections::conn::{Conn, L, R};
/// use connections::extended::Extended;
/// use connections::lift_r;
///
/// const ID_R: Conn<i64, i64, R> = Conn::identity();
/// const LIFTED: Conn<Extended<i64>, Extended<i64>, R> = lift_r!(ID_R);
///
/// assert_eq!(LIFTED.floor(Extended::NegInf), Extended::NegInf);
/// assert_eq!(LIFTED.floor(Extended::PosInf), Extended::PosInf);
/// assert_eq!(LIFTED.floor(Extended::Finite(7_i64)), Extended::Finite(7_i64));
/// ```
#[macro_export]
macro_rules! lift_r {
    ($parent:expr) => {
        $crate::conn::Conn::new_r(
            |b| match b {
                $crate::extended::Extended::NegInf => $crate::extended::Extended::NegInf,
                $crate::extended::Extended::Finite(y) => {
                    $crate::extended::Extended::Finite(($parent).lower(y))
                }
                $crate::extended::Extended::PosInf => $crate::extended::Extended::PosInf,
            },
            |a| match a {
                $crate::extended::Extended::NegInf => $crate::extended::Extended::NegInf,
                $crate::extended::Extended::Finite(x) => {
                    $crate::extended::Extended::Finite(($parent).floor(x))
                }
                $crate::extended::Extended::PosInf => $crate::extended::Extended::PosInf,
            },
        )
    };
}

/// Declaration-form macro: lift a [`ConnK`](crate::conn::ConnK) parent
/// (an iso or other triple marker) through the [`Extended`] functor,
/// emitting a fresh unit-struct marker that impls
/// [`ConnL`](crate::conn::ConnL) **and**
/// [`ConnR`](crate::conn::ConnR) on
/// `Extended<A>` ↔ `Extended<B>`.
///
/// `$parent` must impl `ConnK` (i.e. be either a triple marker
/// or both `ConnL` and `ConnR` over the same `(A, B)`); the parent's
/// laws carry to the emitted marker by construction.
///
/// # Examples
///
/// ```
/// # use connections::{iso, lift_k};
/// # use connections::conn::{view_l, view_r};
/// # use connections::extended::Extended;
/// # const fn id(x: i32) -> i32 { x }
/// # iso! { pub Same : i32 => i32 { forward: id, back: id } }
/// // Lift a `ConnK` parent (here the identity iso `Same : i32 ↔ i32`)
/// // through `Extended` on both sides. The lifted marker maps the
/// // synthetic `NegInf` / `PosInf` sentinels identically and dispatches
/// // the `Finite` arm through the parent.
/// lift_k!(ExtSame : i32 => i32 = Same);
///
/// // From outside the crate, name a marker's view with `view_l` / `view_r`.
/// assert_eq!(view_l(&ExtSame).ceil(Extended::NegInf), Extended::NegInf);
/// assert_eq!(view_r(&ExtSame).floor(Extended::PosInf), Extended::PosInf);
/// assert_eq!(view_l(&ExtSame).ceil(Extended::Finite(42)), Extended::Finite(42));
/// ```
#[macro_export]
macro_rules! lift_k {
    ($name:ident : $A:ty => $B:ty = $parent:path $(,)?) => {
        #[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Default)]
        pub struct $name;
        impl $name {
            /// The lifted L-view. `const`-projectable: the closure
            /// coercion happens in a `const` item.
            #[allow(dead_code)]
            #[inline]
            #[must_use]
            pub(crate) const fn view_l(
                self,
            ) -> $crate::conn::Conn<
                $crate::extended::Extended<$A>,
                $crate::extended::Extended<$B>,
                $crate::conn::L,
            > {
                const LIFTED: $crate::conn::Conn<
                    $crate::extended::Extended<$A>,
                    $crate::extended::Extended<$B>,
                    $crate::conn::L,
                > = $crate::lift_l!($parent.swap_l().swap_r());
                LIFTED
            }
            /// The lifted R-view. `const`-projectable.
            #[allow(dead_code)]
            #[inline]
            #[must_use]
            pub(crate) const fn view_r(
                self,
            ) -> $crate::conn::Conn<
                $crate::extended::Extended<$A>,
                $crate::extended::Extended<$B>,
                $crate::conn::R,
            > {
                const LIFTED: $crate::conn::Conn<
                    $crate::extended::Extended<$A>,
                    $crate::extended::Extended<$B>,
                    $crate::conn::R,
                > = $crate::lift_r!($parent.swap_r().swap_l());
                LIFTED
            }
            /// The swapped lifted L-view. `const`-projectable.
            #[allow(dead_code)]
            #[inline]
            #[must_use]
            pub const fn swap_l(
                self,
            ) -> $crate::conn::Conn<
                $crate::extended::Extended<$B>,
                $crate::extended::Extended<$A>,
                $crate::conn::R,
            > {
                self.view_l().swap_l()
            }
            /// The swapped lifted R-view. `const`-projectable.
            #[allow(dead_code)]
            #[inline]
            #[must_use]
            pub const fn swap_r(
                self,
            ) -> $crate::conn::Conn<
                $crate::extended::Extended<$B>,
                $crate::extended::Extended<$A>,
                $crate::conn::L,
            > {
                self.view_r().swap_r()
            }
        }
        impl $crate::conn::ConnL for $name {
            type A = $crate::extended::Extended<$A>;
            type B = $crate::extended::Extended<$B>;
            #[inline]
            fn swap_l(
                &self,
            ) -> $crate::conn::Conn<
                $crate::extended::Extended<$B>,
                $crate::extended::Extended<$A>,
                $crate::conn::R,
            > {
                self.view_l().swap_l()
            }
        }
        impl $crate::conn::ConnR for $name {
            type A = $crate::extended::Extended<$A>;
            type B = $crate::extended::Extended<$B>;
            #[inline]
            fn swap_r(
                &self,
            ) -> $crate::conn::Conn<
                $crate::extended::Extended<$B>,
                $crate::extended::Extended<$A>,
                $crate::conn::L,
            > {
                self.view_r().swap_r()
            }
        }
    };
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::prop::arb::arb_extended_i64;
    use proptest::prelude::*;
    use std::cell::Cell;

    #[test]
    fn extended_fold_neg_inf() {
        assert_eq!(Extended::<i64>::NegInf.fold(0, 99, |t| t + 1), 0);
    }

    #[test]
    fn extended_fold_finite() {
        assert_eq!(Extended::Finite(3i64).fold(0, 99, |t| t + 1), 4);
    }

    #[test]
    fn extended_fold_pos_inf() {
        assert_eq!(Extended::<i64>::PosInf.fold(0, 99, |t| t + 1), 99);
    }

    #[test]
    fn extended_fold_with_skips_unselected_arms() {
        // For each variant, assert the unselected closures are never
        // invoked. Cell flags flip iff their closure ran.
        let variants: [Extended<i64>; 3] =
            [Extended::NegInf, Extended::Finite(7), Extended::PosInf];
        for x in variants {
            let neg_called = Cell::new(false);
            let pos_called = Cell::new(false);
            let fin_called = Cell::new(false);
            let _ = x.fold_with(
                || {
                    neg_called.set(true);
                    0
                },
                || {
                    pos_called.set(true);
                    0
                },
                |_| {
                    fin_called.set(true);
                    0
                },
            );
            match x {
                Extended::NegInf => {
                    assert!(neg_called.get());
                    assert!(!pos_called.get() && !fin_called.get());
                }
                Extended::Finite(_) => {
                    assert!(fin_called.get());
                    assert!(!neg_called.get() && !pos_called.get());
                }
                Extended::PosInf => {
                    assert!(pos_called.get());
                    assert!(!neg_called.get() && !fin_called.get());
                }
            }
        }
    }

    proptest! {
        // `fold_with (const gx) (const gy) f` agrees with
        // `fold gx gy f` — i.e. strict and non-strict catamorphisms
        // pick the same arm.
        #[test]
        fn extended_fold_with_const_agrees_with_fold(
            x in arb_extended_i64(),
            gx in any::<i64>(),
            gy in any::<i64>(),
        ) {
            let f = |t: i64| t.wrapping_mul(3).wrapping_add(1);
            let lazy = x.fold_with(|| gx, || gy, f);
            let strict = x.fold(gx, gy, f);
            prop_assert_eq!(lazy, strict);
        }
    }

    #[test]
    fn standard_order_on_finite() {
        let a: Extended<i64> = Extended::Finite(1);
        let b: Extended<i64> = Extended::Finite(2);
        assert!(a < b);
        assert!(b > a);
    }

    #[test]
    fn neginf_is_bottom() {
        let m: Extended<i64> = Extended::NegInf;
        let f: Extended<i64> = Extended::Finite(-9_999_999);
        assert!(m < f);
        assert!(f > m);
    }

    #[test]
    fn posinf_is_top() {
        let p: Extended<i64> = Extended::PosInf;
        let f: Extended<i64> = Extended::Finite(9_999_999);
        assert!(f < p);
        assert!(p > f);
    }

    #[test]
    fn neginf_below_posinf() {
        let m: Extended<i64> = Extended::NegInf;
        let p: Extended<i64> = Extended::PosInf;
        assert!(m < p);
    }

    #[test]
    fn extended_eq_reflexive_on_infinities() {
        let m: Extended<i64> = Extended::NegInf;
        let p: Extended<i64> = Extended::PosInf;
        assert_eq!(m, Extended::NegInf);
        assert_eq!(p, Extended::PosInf);
    }
}

// ── Functor-lift tests ─────────────────────────────────────────────
//
// The lift macros (`lift_l!` / `lift_r!` / `lift_k!`) preserve every
// `prop::conn::*` law of the parent: synthetic markers map identically
// (so the laws hold trivially there) and the `Finite` arm dispatches
// through the parent (so its laws carry pointwise). This module
// drives that argument empirically:
//
// 1. Spot-check that synthetic-arm equality holds by construction.
// 2. Drive lifted `Conn::identity::<i64>` through the `l_only` battery —
//    the simplest non-trivial L-only fixture, exercises arms-and-Finite.
// 3. Drive lifted `Q000I016` (an iso ConnK from `fixed::i016`) through
//    the `full` battery — exercises both ConnL and ConnR sides plus
//    `floor_le_ceil`, the full triple-marker law set.
// 4. Smoke-test that a `lift_l!` value composes into a `compose_l!`
//    chain at const-init position, and that a `lift_k!` marker
//    composes at runtime — together these cover the linklab
//    `F64_SECS_EPOCH_VIA_UTC` chain shape against in-tree types only.

#[cfg(all(test, feature = "fixed"))]
mod lift_tests {
    use super::*;
    use crate::conn::{Conn, L, R};
    use crate::fixed::i016::Q000I016;
    use ::fixed::FixedI16;
    use ::fixed::types::extra::U0;
    use proptest::prelude::*;

    // ── Strategy helpers ───────────────────────────────────────────

    /// `Extended<T>` over `NegInf`, `PosInf`, and `Finite(_)` with
    /// 1:1:3 weighting (matching `prop::arb::extended_float_*`).
    fn arb_extended<T, S>(inner: S) -> impl Strategy<Value = Extended<T>>
    where
        T: core::fmt::Debug + Clone + 'static,
        S: Strategy<Value = T> + 'static,
    {
        prop_oneof![
            1 => Just(Extended::NegInf),
            1 => Just(Extended::PosInf),
            3 => inner.prop_map(Extended::Finite),
        ]
    }

    fn arb_ext_i64() -> impl Strategy<Value = Extended<i64>> {
        arb_extended(any::<i64>())
    }

    fn arb_ext_q000() -> impl Strategy<Value = Extended<FixedI16<U0>>> {
        arb_extended(any::<i16>().prop_map(FixedI16::<U0>::from_bits))
    }

    fn arb_ext_i16() -> impl Strategy<Value = Extended<i16>> {
        arb_extended(any::<i16>())
    }

    // ── Synthetic-arm spot checks ──────────────────────────────────

    #[test]
    fn lift_l_identity_synthetic_arms() {
        const ID: Conn<i64, i64, L> = Conn::identity();
        const LIFTED: Conn<Extended<i64>, Extended<i64>, L> = lift_l!(ID);
        assert_eq!(LIFTED.ceil(Extended::NegInf), Extended::NegInf);
        assert_eq!(LIFTED.ceil(Extended::PosInf), Extended::PosInf);
        assert_eq!(LIFTED.upper(Extended::NegInf), Extended::NegInf);
        assert_eq!(LIFTED.upper(Extended::PosInf), Extended::PosInf);
    }

    #[test]
    fn lift_r_identity_synthetic_arms() {
        const ID_R: Conn<i64, i64, R> = Conn::identity();
        const LIFTED: Conn<Extended<i64>, Extended<i64>, R> = lift_r!(ID_R);
        assert_eq!(LIFTED.floor(Extended::NegInf), Extended::NegInf);
        assert_eq!(LIFTED.floor(Extended::PosInf), Extended::PosInf);
        assert_eq!(LIFTED.lower(Extended::NegInf), Extended::NegInf);
        assert_eq!(LIFTED.lower(Extended::PosInf), Extended::PosInf);
    }

    #[test]
    fn lift_l_identity_finite_passthrough() {
        const ID: Conn<i64, i64, L> = Conn::identity();
        const LIFTED: Conn<Extended<i64>, Extended<i64>, L> = lift_l!(ID);
        assert_eq!(LIFTED.ceil(Extended::Finite(7)), Extended::Finite(7));
        assert_eq!(LIFTED.upper(Extended::Finite(-3)), Extended::Finite(-3));
    }

    // Marker that lifts the iso `Q000I016 : FixedI16<U0> ↔ i16` to
    // `Extended<FixedI16<U0>> ↔ Extended<i16>`. Used by the law
    // battery below and the synthetic-arm spot checks.
    lift_k!(EXTQ000I016 : FixedI16<U0> => i16 = Q000I016);

    #[test]
    fn lift_k_q000i016_synthetic_arms() {
        // Both views agree on the synthetic arms (and on identity at
        // Finite values, since Q000I016 is an iso).
        assert_eq!(
            EXTQ000I016.view_l().ceil(Extended::NegInf),
            Extended::NegInf
        );
        assert_eq!(
            EXTQ000I016.view_l().ceil(Extended::PosInf),
            Extended::PosInf
        );
        assert_eq!(
            EXTQ000I016.view_r().floor(Extended::NegInf),
            Extended::NegInf
        );
        assert_eq!(
            EXTQ000I016.view_r().floor(Extended::PosInf),
            Extended::PosInf
        );
        assert_eq!(
            EXTQ000I016.view_l().upper(Extended::NegInf),
            Extended::NegInf
        );
        assert_eq!(
            EXTQ000I016.view_r().lower(Extended::PosInf),
            Extended::PosInf
        );
    }

    #[test]
    fn lift_k_q000i016_finite_dispatches_through_parent() {
        let q = FixedI16::<U0>::from_bits(42);
        // Parent's ceil/upper agree on Finite values:
        assert_eq!(
            EXTQ000I016.view_l().ceil(Extended::Finite(q)),
            Extended::Finite(42_i16)
        );
        assert_eq!(
            EXTQ000I016.view_l().upper(Extended::Finite(42_i16)),
            Extended::Finite(q)
        );
        assert_eq!(
            EXTQ000I016.view_r().floor(Extended::Finite(q)),
            Extended::Finite(42_i16)
        );
        assert_eq!(
            EXTQ000I016.view_r().lower(Extended::Finite(42_i16)),
            Extended::Finite(q)
        );
    }

    // ── Const-init smoke: lift_l! works in const context ──────────

    #[test]
    fn lift_l_const_init_smoke() {
        const ID: Conn<i64, i64, L> = Conn::identity();
        const LIFTED: Conn<Extended<i64>, Extended<i64>, L> = lift_l!(ID);
        // Reading a const inside a fn proves it const-evaluated.
        assert_eq!(LIFTED.ceil(Extended::Finite(0)), Extended::Finite(0));
    }

    // ── Property batteries ─────────────────────────────────────────
    //
    // `law_battery!` synthesises proptest cases from the `prop::conn`
    // predicates against the supplied `conn:` and the `fine:` /
    // `coarse:` strategies. We drive the lifted Conns through it the
    // same way the rest of the crate's tests drive native ones.

    // Lifted identity over Extended<i64>: l_only (Conn<_,_,L>).
    // `lift_l!` requires `:path`, so the parent Conn is pre-bound to
    // a `const` rather than inlined as `Conn::<…>::identity()`.
    const ID_I64: Conn<i64, i64, L> = Conn::identity();
    const LIFTED_ID_I64: Conn<Extended<i64>, Extended<i64>, L> = lift_l!(ID_I64);

    crate::law_battery! {
        mod lifted_id_i64,
        conn: LIFTED_ID_I64,
        fine:   arb_ext_i64(),
        coarse: arb_ext_i64(),
        subset: l_only,
    }

    // Lifted iso over Extended<FixedI16<U0>> ↔ Extended<i16>: full.
    crate::law_battery! {
        mod lifted_q000i016,
        conn: EXTQ000I016,
        fine:   arb_ext_q000(),
        coarse: arb_ext_i16(),
    }

    // ── T5 smoke: lift integrates into compose_l! chains ──────────
    //
    // Mirrors the linklab `F64_SECS_EPOCH_VIA_UTC` chain shape — a
    // Conn whose endpoint is `Extended<…>` composed with a lifted
    // bridge — against `connections`-internal types only. Two flavors:
    //
    // - **Const-init** (`lift_l!` value composing with an `Extended`-
    //   sided identity at const position). Proves the lift produces
    //   a const Conn that flows through `compose_l!` without leaving
    //   const context.
    // - **Runtime** (`lift_k!` marker composing with an identity-
    //   shaped Conn value). Proves a marker emitted by `lift_k!`
    //   integrates into the runtime `compose_l!` form via
    //   `marker.view_l()`.

    #[test]
    fn lift_l_compose_chain_const_smoke() {
        const ID_I64: Conn<i64, i64, L> = Conn::identity();
        const LIFTED: Conn<Extended<i64>, Extended<i64>, L> = lift_l!(ID_I64);
        const ID_EXT: Conn<Extended<i64>, Extended<i64>, L> = Conn::identity();
        // The chain: Extended<i64> → Extended<i64> → Extended<i64>.
        // Const-init through compose_l!; the lift slot replaces the
        // motivating-use-case L-only Conn that lands in `Extended<…>`.
        const CHAIN: Conn<Extended<i64>, Extended<i64>, L> = crate::compose_l!(LIFTED, ID_EXT);
        assert_eq!(CHAIN.ceil(Extended::Finite(7)), Extended::Finite(7));
        assert_eq!(CHAIN.upper(Extended::PosInf), Extended::PosInf);
    }

    #[test]
    fn lift_k_compose_chain_runtime_smoke() {
        // EXTQ000I016 is a `lift_k!` marker. Its `.view_l()` returns a
        // `Conn<Extended<FixedI16<U0>>, Extended<i16>, L>` at runtime —
        // sufficient for the runtime form of `compose_l!`. The chain
        // proves a `lift_k!`-emitted marker integrates with the
        // surrounding compose plumbing.
        //
        // `compose_l!` is `:expr`-fragmented, not `:path`-fragmented
        // like `lift_l!`/`lift_r!`. Its real constraint is that each
        // operand expression must compile to a non-capturing closure
        // body (so the macro-synthesised closures coerce to
        // `fn(_) -> _`). Method-call expressions like
        // `EXTQ000I016.view_l()` qualify because `EXTQ000I016` is a
        // unit-struct path with static dispatch — the closure body
        // re-evaluates `.view_l()` on every invocation but captures
        // nothing from local scope. A function-scope `const` like
        // `ID_EXT_I16` qualifies for the same reason. A `let`-bound
        // local `Conn` value would NOT qualify — it would force a
        // capture and fail fn-pointer coercion.
        const ID_EXT_I16: Conn<Extended<i16>, Extended<i16>, L> = Conn::identity();
        let chain: Conn<Extended<FixedI16<U0>>, Extended<i16>, L> =
            crate::compose_l!(EXTQ000I016.view_l(), ID_EXT_I16);
        let q = FixedI16::<U0>::from_bits(99);
        assert_eq!(chain.ceil(Extended::Finite(q)), Extended::Finite(99_i16));
        assert_eq!(chain.ceil(Extended::NegInf), Extended::NegInf);
    }
}
