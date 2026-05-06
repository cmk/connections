//! Property predicates for [`Interval<A>`](crate::Interval).
//!
//! Each predicate is a pure `bool`-returning fn over the type;
//! downstream callers wrap them in their own `proptest!` blocks.
//! In-crate proptests at the bottom of this file exercise each
//! predicate over `i32` to guard against regressions in the
//! `Interval` core itself.

use crate::Interval;
use core::cmp::Ordering;

/// `Interval::new(x, y)` is `Closed` iff `x ≤ y` (preorder-wise),
/// `Empty` otherwise (incomparable or out-of-order endpoints).
pub fn new_orientation<A: Copy + PartialOrd>(x: A, y: A) -> bool {
    let i = Interval::new(x, y);
    matches!(
        (x.partial_cmp(&y), i),
        (
            Some(Ordering::Less | Ordering::Equal),
            Interval::Closed { .. }
        ) | (Some(Ordering::Greater) | None, Interval::Empty)
    )
}

/// A singleton always contains its own element.
pub fn singleton_contains_self<A: Clone + PartialOrd>(a: A) -> bool {
    Interval::singleton(a.clone()).contains(&a)
}

/// `Interval::Empty.contains(p) == false` for every `p`.
pub fn empty_contains_nothing<A: PartialOrd>(p: &A) -> bool {
    !Interval::<A>::Empty.contains(p)
}

/// Identity-mapping any interval is the identity:
/// `i.imap(|a| a) == i`.
pub fn imap_identity_preserves<A: Copy + PartialOrd>(x: A, y: A) -> bool {
    let i = Interval::new(x, y);
    i.imap(|a| a) == i
}

/// Strictly-monotone shift preserves the interval: for any
/// `f(a) = a.saturating_add(k)` (monotonic non-decreasing over
/// `i64`), `i.imap(f)` matches the variant-wise mapping of `f`.
///
/// Total over `Interval<i64>` — no caller contract. Empty inputs
/// pass trivially (both sides are `Empty`); `Closed { lo, hi }`
/// exercises the real invariant. Unlike [`imap_identity_preserves`],
/// this distinguishes a correct `imap` from one that secretly
/// assumed `f = id`.
pub fn imap_saturating_add_preserves(i: Interval<i64>, k: i64) -> bool {
    let f = |a: i64| a.saturating_add(k);
    let expected = match i {
        Interval::Empty => Interval::Empty,
        Interval::Closed { lo, hi } => Interval::new(f(lo), f(hi)),
    };
    i.imap(f) == expected
}

/// Containment-preorder is reflexive: `i ≤ i` (i.e. `Some(Equal)`).
pub fn containment_preorder_reflex<A: PartialOrd>(i: &Interval<A>) -> bool {
    matches!(i.partial_cmp(i), Some(Ordering::Equal))
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    /// Generate an arbitrary `Interval<i32>` covering both variants
    /// (10% `Empty`, 90% `Closed` over a sorted random pair). Without
    /// the explicit `Empty` arm, proptest would only see `Empty` for
    /// `lo > hi` cases that `Interval::new` collapses, and the
    /// `Closed` bias would crowd out the `Empty` reflexivity case.
    fn arb_interval_i32() -> impl Strategy<Value = Interval<i32>> {
        prop_oneof![
            1 => Just(Interval::Empty),
            9 => (any::<i32>(), any::<i32>()).prop_map(|(a, b)| {
                let (lo, hi) = if a <= b { (a, b) } else { (b, a) };
                Interval::Closed { lo, hi }
            }),
        ]
    }

    /// As above but for `i64`, used by the `imap_saturating_add`
    /// proptest.
    fn arb_interval_i64() -> impl Strategy<Value = Interval<i64>> {
        prop_oneof![
            1 => Just(Interval::Empty),
            9 => (any::<i64>(), any::<i64>()).prop_map(|(a, b)| {
                let (lo, hi) = if a <= b { (a, b) } else { (b, a) };
                Interval::Closed { lo, hi }
            }),
        ]
    }

    proptest! {
        #[test]
        fn prop_new_orientation(x: i32, y: i32) {
            prop_assert!(new_orientation(x, y));
        }

        #[test]
        fn prop_singleton_contains_self(a: i32) {
            prop_assert!(singleton_contains_self(a));
        }

        #[test]
        fn prop_empty_contains_nothing(p: i32) {
            prop_assert!(empty_contains_nothing(&p));
        }

        #[test]
        fn prop_imap_identity_preserves(x: i32, y: i32) {
            prop_assert!(imap_identity_preserves(x, y));
        }

        #[test]
        fn prop_imap_saturating_add_preserves(i in arb_interval_i64(), k: i64) {
            prop_assert!(imap_saturating_add_preserves(i, k));
        }

        #[test]
        fn prop_containment_preorder_reflex(i in arb_interval_i32()) {
            prop_assert!(containment_preorder_reflex(&i));
        }
    }
}
