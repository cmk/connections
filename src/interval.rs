//! Order-theoretic intervals: a closed `[lo, hi]` interval in a
//! preordered set, with an `Empty` variant covering the
//! incomparable case.
//!
//! Ports `Data.Order.Interval` from the Haskell `connections` crate.
//! The bracket of an element under a [`ConnK`](crate::conn::ConnK)
//! triple is one canonical source — see [`interval`](crate::conn::interval).

use core::cmp::Ordering;

/// An interval in a preordered set `A`.
///
/// An interval is a subset `I ⊆ A` closed under bracketing:
///
/// > ∀ x, y ∈ I, z ∈ A.  x ≤ z ≤ y ⇒ z ∈ I.
///
/// The `Empty` variant arises naturally when [`Interval::new`] is
/// called with endpoints that are not preorder-comparable
/// (e.g. `f64::NAN`) or out of order.
///
/// # Examples
///
/// ```rust
/// use connections::Interval;
///
/// let i = Interval::new(1, 3);
/// assert!(i.contains(&2));
/// assert!(!i.contains(&5));
///
/// // Out-of-order endpoints collapse to Empty.
/// assert_eq!(Interval::new(3, 1), Interval::Empty);
///
/// // NaN is not preorder-comparable to itself, so an interval
/// // with NaN endpoints is Empty.
/// let nan = f64::NAN;
/// assert_eq!(Interval::new(nan, nan), Interval::<f64>::Empty);
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub enum Interval<A> {
    /// The empty interval, containing nothing.
    #[default]
    Empty,
    /// A non-empty closed interval `[lo, hi]` with `lo ≤ hi`.
    Bounded {
        /// Lower endpoint (inclusive).
        lo: A,
        /// Upper endpoint (inclusive).
        hi: A,
    },
}

impl<A> Interval<A> {
    /// The empty interval. Equivalent to writing
    /// [`Interval::Empty`] directly — a fn-form constructor for
    /// callers that prefer it.
    #[inline]
    #[must_use]
    pub const fn empty() -> Self {
        Interval::Empty
    }

    /// A singleton interval containing only `a`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::Interval;
    /// let i = Interval::singleton(7_i32);
    /// assert!(i.contains(&7));
    /// assert!(!i.contains(&8));
    /// ```
    #[inline]
    #[must_use]
    pub fn singleton(a: A) -> Self
    where
        A: Clone,
    {
        Interval::Bounded {
            lo: a.clone(),
            hi: a,
        }
    }

    /// Construct an interval from a pair of endpoints. Endpoints
    /// are preorder-sorted; if `x` and `y` are not comparable
    /// (e.g. `NaN` vs `NaN`, or an antichain pair in a partial
    /// order) or out of order, the result is [`Interval::Empty`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::Interval;
    /// // In-order endpoints retained:
    /// assert!(matches!(
    ///     Interval::new(1, 3),
    ///     Interval::Bounded { lo: 1, hi: 3 }
    /// ));
    /// // Reversed endpoints collapse:
    /// assert_eq!(Interval::new(3, 1), Interval::<i32>::Empty);
    /// // Equal endpoints produce a singleton.
    /// assert!(matches!(
    ///     Interval::new(2, 2),
    ///     Interval::Bounded { lo: 2, hi: 2 }
    /// ));
    /// ```
    #[inline]
    #[must_use]
    pub fn new(x: A, y: A) -> Self
    where
        A: PartialOrd,
    {
        match x.partial_cmp(&y) {
            Some(Ordering::Less | Ordering::Equal) => Interval::Bounded { lo: x, hi: y },
            _ => Interval::Empty,
        }
    }

    /// Extract the endpoints of a bounded interval; returns `None`
    /// for [`Interval::Empty`].
    #[inline]
    #[must_use]
    pub fn endpts(self) -> Option<(A, A)> {
        match self {
            Interval::Empty => None,
            Interval::Bounded { lo, hi } => Some((lo, hi)),
        }
    }

    /// True iff `p` lies in the closed interval `[lo, hi]`.
    /// `Empty` contains nothing.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::Interval;
    /// assert!(Interval::new(1, 3).contains(&2));
    /// assert!(!Interval::<i32>::Empty.contains(&0));
    /// ```
    #[inline]
    #[must_use]
    pub fn contains(&self, p: &A) -> bool
    where
        A: PartialOrd,
    {
        match self {
            Interval::Empty => false,
            Interval::Bounded { lo, hi } => lo <= p && p <= hi,
        }
    }

    /// Map over an interval, re-sorting the result. A
    /// non-monotonic `f` may collapse the result to
    /// [`Interval::Empty`] because the new endpoints are re-checked
    /// via [`Interval::new`] — this is intentional, and the same
    /// behaviour as the Haskell original.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::Interval;
    /// // Monotone +1: endpoints map and remain in order.
    /// assert!(matches!(
    ///     Interval::new(1_i32, 3).imap(|x| x + 1),
    ///     Interval::Bounded { lo: 2, hi: 4 }
    /// ));
    /// // Antimonotone negate over a non-singleton: lo and hi
    /// // swap, so `Interval::new` sees a reversed pair and
    /// // collapses to Empty.
    /// assert_eq!(
    ///     Interval::new(1_i32, 3).imap(|x| -x),
    ///     Interval::<i32>::Empty
    /// );
    /// // Singletons survive any function.
    /// assert!(matches!(
    ///     Interval::singleton(2_i32).imap(|x| -x),
    ///     Interval::Bounded { lo: -2, hi: -2 }
    /// ));
    /// ```
    #[inline]
    #[must_use]
    pub fn imap<B, F>(self, f: F) -> Interval<B>
    where
        F: Fn(A) -> B,
        B: PartialOrd,
    {
        match self {
            Interval::Empty => Interval::Empty,
            Interval::Bounded { lo, hi } => Interval::new(f(lo), f(hi)),
        }
    }
}

/// Containment preorder: `Empty ≤ everything`; `Bounded i₁ ≤
/// Bounded i₂ ⟺ i₂ ⊇ i₁` (i.e. `lo₂ ≤ lo₁ && hi₁ ≤ hi₂`).
///
/// Two `Bounded` intervals neither of which contains the other
/// (e.g. `[1,4]` vs `[2,5]`) are incomparable, returning `None`.
impl<A: PartialOrd> PartialOrd for Interval<A> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self, other) {
            (Interval::Empty, Interval::Empty) => Some(Ordering::Equal),
            (Interval::Empty, Interval::Bounded { .. }) => Some(Ordering::Less),
            (Interval::Bounded { .. }, Interval::Empty) => Some(Ordering::Greater),
            (Interval::Bounded { lo: l1, hi: h1 }, Interval::Bounded { lo: l2, hi: h2 }) => {
                // i1 ⊆ i2 iff l2 ≤ l1 && h1 ≤ h2.
                let l_cmp = l2.partial_cmp(l1)?;
                let h_cmp = h1.partial_cmp(h2)?;
                let i1_in_i2 = matches!(l_cmp, Ordering::Less | Ordering::Equal)
                    && matches!(h_cmp, Ordering::Less | Ordering::Equal);
                let i2_in_i1 = matches!(l_cmp, Ordering::Greater | Ordering::Equal)
                    && matches!(h_cmp, Ordering::Greater | Ordering::Equal);
                match (i1_in_i2, i2_in_i1) {
                    (true, true) => Some(Ordering::Equal),
                    (true, false) => Some(Ordering::Less),
                    (false, true) => Some(Ordering::Greater),
                    (false, false) => None,
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_is_default() {
        let i: Interval<i32> = Interval::default();
        assert_eq!(i, Interval::Empty);
    }

    #[test]
    fn empty_below_bounded_in_containment() {
        let e: Interval<i32> = Interval::Empty;
        let b = Interval::new(1, 3);
        assert_eq!(e.partial_cmp(&b), Some(Ordering::Less));
        assert_eq!(b.partial_cmp(&e), Some(Ordering::Greater));
    }

    #[test]
    fn containment_strict() {
        // [2,4] ⊆ [1,5]
        let small = Interval::new(2, 4);
        let big = Interval::new(1, 5);
        assert_eq!(small.partial_cmp(&big), Some(Ordering::Less));
        assert_eq!(big.partial_cmp(&small), Some(Ordering::Greater));
    }

    #[test]
    fn antichain_in_containment_order() {
        // [1,4] vs [2,5] — neither contains the other.
        let a = Interval::new(1, 4);
        let b = Interval::new(2, 5);
        assert_eq!(a.partial_cmp(&b), None);
    }

    #[test]
    fn contains_excludes_outside() {
        let i = Interval::new(1, 3);
        assert!(!i.contains(&0));
        assert!(i.contains(&1));
        assert!(i.contains(&3));
        assert!(!i.contains(&4));
    }
}
