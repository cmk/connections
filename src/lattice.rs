//! Lattice hierarchy and the N5 preorder on IEEE floats.
//!
//! This module defines the trait hierarchy for bounded lattices,
//! Heyting algebras, co-Heyting algebras, symmetric (De Morgan)
//! algebras, and Boolean algebras, plus the N5 partial order
//! [`Ple`] used by the float connections.
//!
//! The hierarchy mirrors the Haskell `connections` library's
//! `Data.Lattice` module. See `doc/design.md` §"Lattice hierarchy"
//! for the full diagram.

/// Partial less-or-equal under the N5 lattice ordering.
///
/// Extends the standard float ordering so that:
/// - NaN is reflexive: `ple(NaN, NaN)` is true
/// - NaN is below +∞: `ple(NaN, +∞)` is true
/// - NaN is above -∞: `ple(-∞, NaN)` is true
/// - NaN is incomparable with all finite values and with each ±∞
///   in the other direction
///
/// This recovers the N5 lattice shape used in the Haskell
/// `connections` library.
pub trait Ple {
    fn ple(&self, other: &Self) -> bool;
}

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

// ── Ple implementations ──────────────────────────────────────────

impl Ple for f32 {
    fn ple(&self, other: &Self) -> bool {
        n5_le_f32(*self, *other)
    }
}

impl Ple for f64 {
    fn ple(&self, other: &Self) -> bool {
        n5_le_f64(*self, *other)
    }
}

/// N5 ordering for f32.
fn n5_le_f32(x: f32, y: f32) -> bool {
    if x.is_nan() && y.is_nan() {
        true
    } else if x.is_nan() {
        y == f32::INFINITY
    } else if y.is_nan() {
        x == f32::NEG_INFINITY
    } else {
        x <= y
    }
}

/// N5 ordering for f64.
fn n5_le_f64(x: f64, y: f64) -> bool {
    if x.is_nan() && y.is_nan() {
        true
    } else if x.is_nan() {
        y == f64::INFINITY
    } else if y.is_nan() {
        x == f64::NEG_INFINITY
    } else {
        x <= y
    }
}

// Blanket impls for totally ordered types — ple is just <=.
impl Ple for i8 {
    fn ple(&self, other: &Self) -> bool {
        self <= other
    }
}
impl Ple for i16 {
    fn ple(&self, other: &Self) -> bool {
        self <= other
    }
}
impl Ple for i32 {
    fn ple(&self, other: &Self) -> bool {
        self <= other
    }
}
impl Ple for i64 {
    fn ple(&self, other: &Self) -> bool {
        self <= other
    }
}
impl Ple for u8 {
    fn ple(&self, other: &Self) -> bool {
        self <= other
    }
}
impl Ple for u16 {
    fn ple(&self, other: &Self) -> bool {
        self <= other
    }
}
impl Ple for u32 {
    fn ple(&self, other: &Self) -> bool {
        self <= other
    }
}
impl Ple for u64 {
    fn ple(&self, other: &Self) -> bool {
        self <= other
    }
}

// `ExtendedFloat<T>`: its `PartialOrd` is the N5 ordering with the
// NaN-self-equality patch (see `impl_float_ext!` in
// `crate::conn::float`), so a delegating `Ple` impl is correct.
impl<T> Ple for crate::conn::float::ExtendedFloat<T>
where
    Self: PartialOrd,
{
    fn ple(&self, other: &Self) -> bool {
        matches!(
            self.partial_cmp(other),
            Some(core::cmp::Ordering::Less | core::cmp::Ordering::Equal),
        )
    }
}

// `Extended<T>`: derived `PartialOrd` lifts `T: PartialOrd` while
// fixing `NegInf < Finite < PosInf`. Delegate.
impl<T: PartialOrd> Ple for crate::extended::Extended<T> {
    fn ple(&self, other: &Self) -> bool {
        matches!(
            self.partial_cmp(other),
            Some(core::cmp::Ordering::Less | core::cmp::Ordering::Equal),
        )
    }
}

#[cfg(test)]
mod tests {
    use crate::conn::float::ExtendedFloat;
    use crate::property::arb::{arb_f32, arb_f64};
    use crate::property::laws;
    use proptest::prelude::*;

    // ── Spot checks (ExtendedFloat — the lawful float wrapper) ─────
    //
    // Raw `f32`/`f64` are *not* `Eq` (NaN ≠ NaN under their standard
    // `PartialEq`), so they cannot be used with the lattice predicates.
    // Wrap into `ExtendedFloat<T>`, whose patched `PartialEq` makes
    // `Finite(NaN) == Finite(NaN)` and synthesises Bot/Top as the
    // lattice extremes. The N5-specific cells (`NaN ≤ +∞`,
    // `-∞ ≤ NaN`) are deliberately not asserted: ExtendedFloat
    // preserves NaN's incomparability with every finite (including
    // ±∞), and uses Bot/Top for the lattice ends instead.

    #[test]
    fn nan_reflexive_ef64() {
        let n: ExtendedFloat<f64> = ExtendedFloat::Finite(f64::NAN);
        assert_eq!(n, ExtendedFloat::Finite(f64::NAN));
    }

    #[test]
    fn bot_below_finite() {
        assert!(ExtendedFloat::<f64>::Bot <= ExtendedFloat::Finite(0.0));
        assert!(ExtendedFloat::<f64>::Bot <= ExtendedFloat::Finite(f64::NAN));
    }

    #[test]
    fn finite_below_top() {
        assert!(ExtendedFloat::Finite(0.0_f64) <= ExtendedFloat::<f64>::Top);
        assert!(ExtendedFloat::Finite(f64::NAN) <= ExtendedFloat::<f64>::Top);
    }

    #[test]
    fn normal_ordering_preserved() {
        assert!(ExtendedFloat::Finite(1.0_f64) <= ExtendedFloat::Finite(2.0));
        assert!(ExtendedFloat::Finite(2.0_f64) > ExtendedFloat::Finite(1.0));
    }

    // ── Partial-order property tests (ExtendedFloat<f32> / <f64>) ─

    fn ef64() -> impl Strategy<Value = ExtendedFloat<f64>> {
        prop_oneof![
            1 => Just(ExtendedFloat::Bot),
            1 => Just(ExtendedFloat::Top),
            8 => arb_f64().prop_map(ExtendedFloat::Finite),
        ]
    }

    fn ef32() -> impl Strategy<Value = ExtendedFloat<f32>> {
        prop_oneof![
            1 => Just(ExtendedFloat::Bot),
            1 => Just(ExtendedFloat::Top),
            8 => arb_f32().prop_map(ExtendedFloat::Finite),
        ]
    }

    proptest! {
        #[test]
        fn reflexive_ef64(x in ef64()) {
            prop_assert!(laws::lattice_reflexive(&x));
        }

        #[test]
        fn reflexive_ef32(x in ef32()) {
            prop_assert!(laws::lattice_reflexive(&x));
        }

        #[test]
        fn transitive_ef64(x in ef64(), y in ef64(), z in ef64()) {
            prop_assert!(laws::lattice_transitive(&x, &y, &z));
        }

        #[test]
        fn transitive_ef32(x in ef32(), y in ef32(), z in ef32()) {
            prop_assert!(laws::lattice_transitive(&x, &y, &z));
        }

        #[test]
        fn antisymmetric_ef64(x in ef64(), y in ef64()) {
            prop_assert!(laws::lattice_antisymmetric(&x, &y));
        }

        #[test]
        fn bot_ef64(x in ef64()) {
            prop_assert!(laws::lattice_bot(&ExtendedFloat::<f64>::Bot, &x));
        }

        #[test]
        fn top_ef64(x in ef64()) {
            prop_assert!(laws::lattice_top(&ExtendedFloat::<f64>::Top, &x));
        }

        #[test]
        fn bot_ef32(x in ef32()) {
            prop_assert!(laws::lattice_bot(&ExtendedFloat::<f32>::Bot, &x));
        }

        #[test]
        fn top_ef32(x in ef32()) {
            prop_assert!(laws::lattice_top(&ExtendedFloat::<f32>::Top, &x));
        }
    }
}
