//! `Extended<T>` wraps a totally-ordered `T` with `NegInf` (bottom) and
//! `PosInf` (top). Used as the target of connections whose target type
//! cannot represent the full range of the source — e.g. a float source
//! feeding into a bounded integer rung saturates to `NegInf`/`PosInf`
//! when the finite range is exceeded.
//!
//! `Extended` is a pure range-extension wrapper; it does not participate
//! in float NaN handling — that lives in
//! [`crate::float::ExtendedFloat`].

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

    /// Lazy variant of [`Extended::fold`]: each arm is produced on
    /// demand. Mirrors `Option::map_or_else`.
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
