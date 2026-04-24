//! `Extended<T>` wraps a totally-ordered `T` with `NegInf` (bottom) and
//! `PosInf` (top). Used as the target of connections whose target type
//! cannot represent the full range of the source — e.g. a float source
//! feeding into a bounded integer rung saturates to `NegInf`/`PosInf`
//! when the finite range is exceeded.
//!
//! `Extended` is a pure range-extension wrapper; it does not participate
//! in float NaN handling — that lives in [`crate::float_ext::FloatExt`].

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Extended<T> {
    NegInf,
    Finite(T),
    PosInf,
}

impl<T: PartialOrd> PartialOrd for Extended<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        use std::cmp::Ordering::*;
        use Extended::*;
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
