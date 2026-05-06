//! Property predicates for [`Interval<A>`](crate::Interval).
//!
//! Each predicate is a pure `bool`-returning fn over the type;
//! downstream callers wrap them in their own `proptest!` blocks.
//! In-crate proptests at the bottom of this file exercise each
//! predicate over `i32` to guard against regressions in the
//! `Interval` core itself.

use crate::Interval;
use core::cmp::Ordering;

/// `Interval::new(x, y)` is `Bounded` iff `x ≤ y` (preorder-wise),
/// `Empty` otherwise (incomparable or out-of-order endpoints).
pub fn new_orientation<A: Copy + PartialOrd>(x: A, y: A) -> bool {
    let i = Interval::new(x, y);
    matches!(
        (x.partial_cmp(&y), i),
        (
            Some(Ordering::Less | Ordering::Equal),
            Interval::Bounded { .. }
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

/// Strictly-monotone shift preserves the bracket: for any
/// `f(a) = a.saturating_add(k)` (which is monotonic non-decreasing
/// over `i64`), `i.imap(f) == Interval::new(f(lo), f(hi))`.
///
/// Unlike [`imap_identity_preserves`], this exercises the case where
/// `f` actually moves the endpoints — distinguishing a correct `imap`
/// from one that secretly assumed `f = id`.
pub fn imap_saturating_add_preserves(lo: i64, hi: i64, k: i64) -> bool {
    let i = Interval::new(lo, hi);
    let f = |a: i64| a.saturating_add(k);
    let mapped = i.imap(f);
    match i {
        Interval::Empty => mapped == Interval::Empty,
        Interval::Bounded { lo, hi } => mapped == Interval::new(f(lo), f(hi)),
    }
}

/// Containment-preorder is reflexive: `i ≤ i` (i.e. `Some(Equal)`).
pub fn containment_preorder_reflex<A: PartialOrd>(i: &Interval<A>) -> bool {
    matches!(i.partial_cmp(i), Some(Ordering::Equal))
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

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
        fn prop_imap_saturating_add_preserves(lo: i64, hi: i64, k: i64) {
            prop_assert!(imap_saturating_add_preserves(lo, hi, k));
        }

        #[test]
        fn prop_containment_preorder_reflex_bounded(x: i32, y: i32) {
            let i = Interval::new(x, y);
            prop_assert!(containment_preorder_reflex(&i));
        }
    }

    #[test]
    fn empty_is_reflexive_in_containment_order() {
        let i: Interval<i32> = Interval::Empty;
        assert!(containment_preorder_reflex(&i));
    }
}
