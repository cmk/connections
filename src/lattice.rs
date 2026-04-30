//! Lattice hierarchy.
//!
//! This module defines the trait hierarchy for bounded lattices,
//! Heyting algebras, co-Heyting algebras, symmetric (De Morgan)
//! algebras, and Boolean algebras.
//!
//! The hierarchy mirrors the Haskell `connections` library's
//! `Data.Lattice` module. See `doc/design.md` §"Lattice hierarchy"
//! for the full diagram.
//!
//! Ordering laws use the standard library's `Eq + PartialOrd` rather
//! than a crate-local trait. The fix for IEEE-float NaN's
//! non-reflexivity lives in [`crate::float::ExtendedFloat`],
//! whose patched `PartialEq` makes `Extend(NaN) == Extend(NaN)` and
//! satisfies `Eq`. Floats flow through the laws by wrapping into
//! `ExtendedFloat<T>`; raw `f32`/`f64` cannot satisfy `Eq` and are
//! rejected at compile time.

// ── Lattice traits ────────────────────────────────────────────────

/// Join-semilattice: least upper bound with a bottom element.
///
/// A lattice is a partially ordered set in which every two elements
/// have a unique join (least upper bound / supremum) and a unique
/// meet (greatest lower bound / infimum).
///
/// A bounded lattice adds unique elements [`bot`](Join::bot) and
/// [`top`](Meet::top), which serve as identities to `join` and
/// `meet`, respectively.
///
/// Laws:
///
/// ```text
/// x.join(&Self::bot()) == x                      // neutrality
/// x.join(&y.join(z))   == x.join(y).join(z)      // associativity
/// x.join(y)            == y.join(x)               // commutativity
/// x.join(x)            == x                       // idempotency
/// x.join(y).meet(y)    == y                       // absorption
/// ```
///
/// See <https://en.wikipedia.org/wiki/Lattice_(order)>.
pub trait Join: PartialOrd {
    /// The unique bottom element. `x.join(&Self::bot()) == x` for
    /// all x.
    fn bot() -> Self;

    /// Least upper bound (supremum).
    fn join(&self, other: &Self) -> Self;
}

/// Meet-semilattice: greatest lower bound with a top element.
///
/// Dual of [`Join`]. See [`Join`] for the full lattice law listing.
///
/// Laws:
///
/// ```text
/// x.meet(&Self::top()) == x                      // neutrality
/// x.meet(&y.meet(z))   == x.meet(y).meet(z)      // associativity
/// x.meet(y)            == y.meet(x)               // commutativity
/// x.meet(x)            == x                       // idempotency
/// x.meet(y).join(y)    == y                       // absorption
/// ```
pub trait Meet: PartialOrd {
    /// The unique top element. `x.meet(&Self::top()) == x` for all x.
    fn top() -> Self;

    /// Greatest lower bound (infimum).
    fn meet(&self, other: &Self) -> Self;
}

// ── Heyting algebra ───────────────────────────────────────────────

/// Heyting algebra: bounded distributive lattice with implication.
///
/// A Heyting algebra is a bounded, distributive lattice equipped
/// with an implication operation. The dual lattice of open subsets
/// of a topological space is the primordial example.
///
/// Implication from `a` is the upper adjoint of conjunction with `a`:
///
/// ```text
/// x.meet(a) ⊑ b  ⟺  x ⊑ a.imp(b)
/// ```
///
/// Laws:
///
/// ```text
/// x.meet(y) <= z  <=>  x <= y.imp(z)             // adjunction
/// x.imp(y) <= x.imp(y.join(z))                    // monotone in 2nd
/// x.join(z).imp(y) <= x.imp(y)                    // antitone in 1st
/// x <= y  =>  z.imp(x) <= z.imp(y)                // monotone under ⊑
/// y <= x.imp(x.meet(y))                            // weakening
/// x <= y  <=>  x.imp(y) == top                    // order characterisation
/// x.meet(y).imp(z) == x.imp(y.imp(z))             // currying
/// x.imp(y.meet(z)) == x.imp(y).meet(x.imp(z))     // distributes over meet
/// x.meet(x.imp(y)) == x.meet(y)                   // modus ponens
/// ```
///
/// Note: Heyting algebras need not obey the law of the excluded
/// middle (`x.join(x.neg()) == top`). That holds only in Boolean
/// algebras.
///
/// See <https://ncatlab.org/nlab/show/Heyting+algebra>.
pub trait Heyting: Join + Meet {
    /// Heyting implication (logical implication):
    ///
    /// `imp(a, b)` = ∨{x : x ∧ a ⊑ b}
    ///
    /// ```text
    /// bot.imp(bot) == top
    /// bot.imp(top) == top
    /// top.imp(bot) == bot
    /// top.imp(top) == top
    /// ```
    fn imp(&self, other: &Self) -> Self;

    /// Heyting negation (pseudo-complement): `self.imp(bot)`.
    ///
    /// The largest element whose meet with `self` is bottom.
    ///
    /// Laws:
    ///
    /// ```text
    /// bot.neg() == top
    /// top.neg() == bot
    /// x <= x.neg().neg()                           // double neg monad
    /// x.neg().join(y) <= x.imp(y)
    /// x.imp(y).neg() == x.neg().neg().meet(y.neg()) // de Morgan
    /// x.join(y).neg() == x.neg().meet(y.neg())      // de Morgan
    /// x.meet(x.neg()) == bot                        // non-contradiction
    /// x.neg().neg().neg() == x.neg()                // triple neg
    /// x.neg().neg().mid() == top
    /// ```
    ///
    /// Some logics may in addition obey
    /// [De Morgan conditions](https://ncatlab.org/nlab/show/De+Morgan+Heyting+algebra).
    fn neg(&self) -> Self
    where
        Self: Sized,
    {
        self.imp(&Self::bot())
    }

    /// The (not necessarily excluded) middle operator:
    /// `self.join(self.neg())`.
    ///
    /// Equals `top` only in a Boolean algebra.
    /// `x.neg().neg().mid() == top` always holds.
    fn mid(&self) -> Self
    where
        Self: Sized,
    {
        self.join(&self.neg())
    }
}

// ── Co-Heyting algebra ────────────────────────────────────────────

/// Co-Heyting algebra: bounded distributive lattice with
/// coimplication (subtraction). Dual of [`Heyting`].
///
/// The lattice of closed subsets of a topological space is the
/// primordial example.
///
/// Coimplication to `a` is the lower adjoint of disjunction with `a`:
///
/// ```text
/// a.coimp(b) ⊑ c  ⟺  a ⊑ b.join(c)
/// ```
///
/// Laws:
///
/// ```text
/// x.coimp(y) <= z  <=>  x <= y.join(z)            // adjunction
/// x.meet(z).coimp(y) <= x.coimp(y)                 // monotone in 1st
/// x >= y  =>  x.coimp(z) >= y.coimp(z)             // monotone under ⊑
/// x >= x.coimp(y)                                   // bounded by self
/// x >= y  <=>  y.coimp(x) == bot                   // order characterisation
/// x.coimp(y.meet(z)) >= x.coimp(y)
/// z.coimp(x.join(y)) == z.coimp(x).coimp(y)        // co-currying
/// y.join(z).coimp(x) == y.coimp(x).join(z.coimp(x)) // distributes over join
/// x.join(y.coimp(x)) == x.join(y)                   // absorption
/// ```
///
/// Note: co-Heyting algebras need not obey the law of
/// non-contradiction (`x.meet(x.coneg()) == bot`). That holds only
/// in Boolean algebras.
///
/// See <https://ncatlab.org/nlab/show/co-Heyting+algebra>.
pub trait Coheyting: Join + Meet {
    /// Co-Heyting coimplication (logical co-implication / subtraction):
    ///
    /// `coimp(a, b)` = ∧{x : a ⊑ b ∨ x}
    ///
    /// ```text
    /// bot.coimp(bot) == bot
    /// bot.coimp(top) == bot
    /// top.coimp(bot) == top
    /// top.coimp(top) == bot
    /// ```
    ///
    /// For many collection types (e.g. `Set`), `coimp` coincides with
    /// set difference.
    fn coimp(&self, other: &Self) -> Self;

    /// Co-Heyting co-negation: `top.coimp(self)`.
    ///
    /// The smallest element whose join with `self` is top.
    ///
    /// Laws:
    ///
    /// ```text
    /// bot.coneg() == top
    /// top.coneg() == bot
    /// x >= x.coneg().coneg()                       // double coneg comonad
    /// x.coneg().coimp(y) == x.coneg().coneg().join(y.coneg()) // de Morgan
    /// x.meet(y).coneg() == x.coneg().join(y.coneg()) // de Morgan
    /// x.join(x.coneg()) == top                      // excluded middle
    /// x.coneg().coneg().coneg() == x.coneg()        // triple coneg
    /// x.coneg().coneg().comid() == bot
    /// ```
    fn coneg(&self) -> Self
    where
        Self: Sized,
    {
        Self::top().coimp(self)
    }

    /// Co-Heyting co-middle
    /// ([boundary](https://ncatlab.org/nlab/show/co-Heyting+boundary)):
    /// `self.meet(self.coneg())`.
    ///
    /// Not necessarily bottom — equals bottom only in a Boolean
    /// algebra. Satisfies the Leibniz rule:
    ///
    /// ```text
    /// x == x.comid().join(x.coneg().coneg())        // decomposition
    /// (x.meet(y)).comid() == x.comid().meet(y)
    ///                        .join(x.meet(y.comid())) // Leibniz
    /// x.join(y).comid().join(x.meet(y).comid())
    ///     == x.comid().join(y.comid())               // additivity
    /// ```
    fn comid(&self) -> Self
    where
        Self: Sized,
    {
        self.meet(&self.coneg())
    }
}

// ── Symmetric / Boolean ───────────────────────────────────────────

/// Symmetric Heyting algebra: a
/// [De Morgan](https://ncatlab.org/nlab/show/De+Morgan+Heyting+algebra)
/// bi-Heyting algebra with an idempotent, antitone negation operator.
///
/// Laws:
///
/// ```text
/// x <= y  =>  y.not() <= x.not()                  // antitone
/// x.not().not() == x                               // involution
/// x.coimp(y) == y.not().imp(&x.not()).not()         // coimp from imp
/// x.imp(y)  == y.not().coimp(&x.not()).not()        // imp from coimp
/// ```
///
/// And:
///
/// ```text
/// convr(x) <= convl(x)
/// ```
///
/// with equality occurring iff the algebra is Boolean.
///
/// Derived identities:
///
/// ```text
/// neg(x) == convr(not(x)) == not(convl(x))
/// coneg(x) == not(convr(x)) == convl(not(x))
/// neg(neg(x)) == convr(convl(x))
/// coneg(coneg(x)) == convl(convr(x))
/// ```
pub trait Symmetric: Heyting + Coheyting {
    /// Symmetric negation (complement).
    ///
    /// Involutive: `x.not().not() == x`.
    ///
    /// Unlike Heyting [`neg`](Heyting::neg) or co-Heyting
    /// [`coneg`](Coheyting::coneg), symmetric `not` is its own
    /// inverse.
    fn not(&self) -> Self;

    /// Exclusive or: `self.join(other).meet(self.meet(other).not())`.
    ///
    /// ```text
    /// x.xor(y) == x.join(y).meet(x.meet(y).not())
    /// ```
    fn xor(&self, other: &Self) -> Self
    where
        Self: Sized,
    {
        self.join(other).meet(&self.meet(other).not())
    }
}

/// Left converse operator: `top.coimp(&x.not())`.
///
/// ```text
/// convl(x.join(y)) == convl(x).join(convl(y))
/// convl(x.meet(y)) == coneg(coneg(convl(x).meet(convl(y))))
/// ```
pub fn convl<T: Symmetric + Sized>(x: &T) -> T {
    T::top().coimp(&x.not())
}

/// Right converse operator: `x.not().imp(&T::bot())`.
///
/// ```text
/// convr(x.meet(y)) == convr(x).meet(convr(y))
/// convr(x.join(y)) == neg(neg(convr(x).join(convr(y))))
/// ```
pub fn convr<T: Symmetric + Sized>(x: &T) -> T {
    x.not().imp(&T::bot())
}

/// Boolean algebra: symmetric Heyting algebra satisfying both the
/// law of excluded middle and the law of non-contradiction.
///
/// [Boolean algebras](https://ncatlab.org/nlab/show/Boolean+algebra)
/// are symmetric Heyting algebras where:
///
/// ```text
/// x.join(x.neg()) == top                           // excluded middle
/// x.meet(x.coneg()) == bot                         // non-contradiction
/// ```
///
/// If the algebra is Boolean, then `neg == not == coneg`.
pub trait Boolean: Symmetric {}

// ── Canonical Conn helpers ──────────────────────────────────────

/// The canonical `Conn<A, bool>` for any bounded lattice `A`.
///
/// Embeds the 2-element chain `false < true` as `bot < top`. The
/// adjoint asymmetry pushes the source's bottom and top to the
/// matching ends of `bool`:
///
/// - `ceil(a) = true` for every `a ≠ bot`; `ceil(bot) = false`.
/// - `floor(a) = false` for every `a ≠ top`; `floor(top) = true`.
/// - `inner(false) = bot`, `inner(true) = top`.
///
/// Port of the Haskell `connections` library's `bndbin :: (Eq a,
/// Bounded a) => Cast k a Bool`, with [`Join`] + [`Meet`] standing
/// in for Haskell's `Bounded` (Rust has no stdlib `Bounded` trait
/// and this crate intentionally doesn't introduce one — the
/// lattice-side bounds already give us what we need).
///
/// Both Galois laws hold:
///
/// - `ceil(a) ≤ b ⟺ a ≤ inner(b)`. At `b = false` the RHS is `a ≤
///   bot`, equivalent to `a == bot`; the LHS is `ceil(a) ≤ false`,
///   equivalent to `ceil(a) == false`. Both reduce to `a == bot`.
/// - `inner(b) ≤ a ⟺ b ≤ floor(a)`. Dual derivation pinned at `b
///   = true` and `a == top`.
///
/// Naming follows the 8-char Conn convention: `LATT` (4L+0D) on the
/// source side stands for "abstract bounded lattice", `BOOL` (4L+0D)
/// on the target. Defined as a generic function rather than a `pub
/// const` because Rust consts can't carry type parameters.
///
/// The bounds require `Copy` because `Conn::new` stores `fn(A) -> B`
/// pointers and the source value flows through a function call.
/// `'static` keeps the function pointer well-formed under
/// monomorphization.
///
/// # Example
///
/// ```rust,ignore
/// use connections::lattice::LATTBOOL;
/// use core::cmp::Ordering;
///
/// // `Ordering` impls `Join + Meet` (3-element chain Less < Equal < Greater).
/// let c = LATTBOOL::<Ordering>();
/// assert_eq!(c.ceil(Ordering::Less),     false); // bot → false
/// assert_eq!(c.ceil(Ordering::Equal),    true);  // not-bot → true
/// assert_eq!(c.ceil(Ordering::Greater),  true);
/// assert_eq!(c.floor(Ordering::Less),    false);
/// assert_eq!(c.floor(Ordering::Equal),   false); // not-top → false
/// assert_eq!(c.floor(Ordering::Greater), true);  // top → true
/// assert_eq!(c.inner(false),             Ordering::Less);
/// assert_eq!(c.inner(true),              Ordering::Greater);
/// ```
#[allow(non_snake_case)]
pub fn LATTBOOL<A>() -> crate::conn::ConnL<A, bool>
where
    A: Join + Meet + Copy + 'static,
{
    fn ceil<A: Join + PartialEq>(i: A) -> bool {
        i != A::bot()
    }
    fn inner<A: Join + Meet>(x: bool) -> A {
        if x { A::top() } else { A::bot() }
    }
    crate::conn::Conn::new_l(ceil::<A>, inner::<A>)
}

// ── `Join + Meet` impls for primitive lattices ──────────────────

// `core::cmp::Ordering` is the canonical 3-element bounded chain
// (`Less < Equal < Greater`). Implementing `Join + Meet` makes it
// the smallest non-trivial test surface for the generic
// [`LATTBOOL`] helper.
impl Join for core::cmp::Ordering {
    fn bot() -> Self {
        core::cmp::Ordering::Less
    }
    fn join(&self, other: &Self) -> Self {
        core::cmp::max(*self, *other)
    }
}

impl Meet for core::cmp::Ordering {
    fn top() -> Self {
        core::cmp::Ordering::Greater
    }
    fn meet(&self, other: &Self) -> Self {
        core::cmp::min(*self, *other)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[allow(unused_imports)]
    use crate::conn::{ViewL, ViewR};
    use crate::float::ExtendedFloat;
    use crate::prop::arb::{arb_f32, arb_f64};
    use crate::prop::conn as conn_laws;
    use crate::prop::lattice as lattice_laws;
    use core::cmp::Ordering;
    use proptest::prelude::*;

    // ── Spot checks (ExtendedFloat — the lawful float wrapper) ─────
    //
    // Raw `f32`/`f64` are *not* `Eq` (NaN ≠ NaN under their standard
    // `PartialEq`), so they cannot be used with the lattice predicates.
    // Wrap into `ExtendedFloat<T>`, whose patched `PartialEq` makes
    // `Extend(NaN) == Extend(NaN)` and synthesises Bot/Top as the
    // lattice extremes. The N5-specific cells (`NaN ≤ +∞`,
    // `-∞ ≤ NaN`) are deliberately not asserted: ExtendedFloat
    // preserves NaN's incomparability with every finite (including
    // ±∞), and uses Bot/Top for the lattice ends instead.

    #[test]
    fn nan_reflexive_ef64() {
        let n: ExtendedFloat<f64> = ExtendedFloat::Extend(f64::NAN);
        assert_eq!(n, ExtendedFloat::Extend(f64::NAN));
    }

    #[test]
    fn bot_below_finite() {
        assert!(ExtendedFloat::<f64>::Bot <= ExtendedFloat::Extend(0.0));
        assert!(ExtendedFloat::<f64>::Bot <= ExtendedFloat::Extend(f64::NAN));
    }

    #[test]
    fn finite_below_top() {
        assert!(ExtendedFloat::Extend(0.0_f64) <= ExtendedFloat::<f64>::Top);
        assert!(ExtendedFloat::Extend(f64::NAN) <= ExtendedFloat::<f64>::Top);
    }

    #[test]
    fn normal_ordering_preserved() {
        assert!(ExtendedFloat::Extend(1.0_f64) <= ExtendedFloat::Extend(2.0));
        assert!(ExtendedFloat::Extend(2.0_f64) > ExtendedFloat::Extend(1.0));
    }

    // ── Partial-order property tests (ExtendedFloat<f32> / <f64>) ─

    fn ef64() -> impl Strategy<Value = ExtendedFloat<f64>> {
        prop_oneof![
            1 => Just(ExtendedFloat::Bot),
            1 => Just(ExtendedFloat::Top),
            8 => arb_f64().prop_map(ExtendedFloat::Extend),
        ]
    }

    fn ef32() -> impl Strategy<Value = ExtendedFloat<f32>> {
        prop_oneof![
            1 => Just(ExtendedFloat::Bot),
            1 => Just(ExtendedFloat::Top),
            8 => arb_f32().prop_map(ExtendedFloat::Extend),
        ]
    }

    proptest! {
        #[test]
        fn reflexive_ef64(x in ef64()) {
            prop_assert!(lattice_laws::lattice_reflexive(&x));
        }

        #[test]
        fn reflexive_ef32(x in ef32()) {
            prop_assert!(lattice_laws::lattice_reflexive(&x));
        }

        #[test]
        fn transitive_ef64(x in ef64(), y in ef64(), z in ef64()) {
            prop_assert!(lattice_laws::lattice_transitive(&x, &y, &z));
        }

        #[test]
        fn transitive_ef32(x in ef32(), y in ef32(), z in ef32()) {
            prop_assert!(lattice_laws::lattice_transitive(&x, &y, &z));
        }

        #[test]
        fn antisymmetric_ef64(x in ef64(), y in ef64()) {
            prop_assert!(lattice_laws::lattice_antisymmetric(&x, &y));
        }

        #[test]
        fn bot_ef64(x in ef64()) {
            prop_assert!(lattice_laws::lattice_bot(&ExtendedFloat::<f64>::Bot, &x));
        }

        #[test]
        fn top_ef64(x in ef64()) {
            prop_assert!(lattice_laws::lattice_top(&ExtendedFloat::<f64>::Top, &x));
        }

        #[test]
        fn bot_ef32(x in ef32()) {
            prop_assert!(lattice_laws::lattice_bot(&ExtendedFloat::<f32>::Bot, &x));
        }

        #[test]
        fn top_ef32(x in ef32()) {
            prop_assert!(lattice_laws::lattice_top(&ExtendedFloat::<f32>::Top, &x));
        }
    }

    // ── `Ordering` lattice impls + `LATTBOOL` exercise ──────────
    //
    // `Ordering` is the smallest non-trivial concrete `Join + Meet`
    // type in the crate, so it doubles as the test surface for the
    // generic [`LATTBOOL`] helper above. The `LATTBOOL::<Ordering>()`
    // Conn is a full triple in the bndbin shape.

    #[test]
    fn ordering_lattice_bot_top() {
        assert_eq!(<Ordering as Join>::bot(), Ordering::Less);
        assert_eq!(<Ordering as Meet>::top(), Ordering::Greater);
        assert_eq!(Ordering::Less.join(&Ordering::Greater), Ordering::Greater);
        assert_eq!(Ordering::Less.meet(&Ordering::Greater), Ordering::Less);
    }

    #[test]
    fn lattbool_ordering_spot() {
        let c = LATTBOOL::<Ordering>();
        assert!(!c.ceil(Ordering::Less));
        assert!(c.ceil(Ordering::Equal));
        assert!(c.ceil(Ordering::Greater));
        assert_eq!(c.inner(false), Ordering::Less);
        assert_eq!(c.inner(true), Ordering::Greater);
    }

    proptest! {
        #[test]
        fn ordering_lattice_bot_law(o in crate::prop::arb::arb_ordering()) {
            prop_assert!(lattice_laws::lattice_bot(&<Ordering as Join>::bot(), &o));
        }

        #[test]
        fn ordering_lattice_top_law(o in crate::prop::arb::arb_ordering()) {
            prop_assert!(lattice_laws::lattice_top(&<Ordering as Meet>::top(), &o));
        }

        #[test]
        fn lattbool_ordering_galois_l(o in crate::prop::arb::arb_ordering(), b in any::<bool>()) {
            let c = LATTBOOL::<Ordering>();
            prop_assert!(conn_laws::galois_l(&c, o, b));
        }

        // galois_r and floor_le_ceil deleted under Sprint B kind discipline:
        // LATTBOOL is now a one-sided ConnL.

        #[test]
        fn lattbool_ordering_idempotent(o in crate::prop::arb::arb_ordering()) {
            let c = LATTBOOL::<Ordering>();
            prop_assert!(conn_laws::idempotent(&c, o));
        }
    }
}
