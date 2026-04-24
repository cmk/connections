//! `FloatExt<T>` extends an IEEE float type with synthetic `Bot` and
//! `Top` elements outside the float range, recovering the N5 lattice
//! structure the Galois-connection machinery requires.
//!
//! Rust's built-in float `PartialOrd` is a partial order: NaN is
//! incomparable with every value including itself, and there are no
//! canonical top/bottom elements. `FloatExt` addresses both:
//!
//! - `Bot ≤ x` and `x ≤ Top` for every `x` (including `NaN`, `±∞`).
//! - `Finite(NaN)` is reflexive: `Finite(NaN) == Finite(NaN)` and
//!   `Finite(NaN).partial_cmp(&Finite(NaN)) == Some(Equal)`.
//! - `Finite(NaN)` remains incomparable with every other `Finite(_)`
//!   value (including `±∞`) — that comparison returns `None`.
//!
//! The N5 lattice (`-∞ ≤ NaN ≤ +∞`, NaN incomparable with finites) is
//! obtained from this shape: the synthetic `Bot` / `Top` form the
//! lattice's bottom/top; NaN's reflexivity closes the preorder; its
//! incomparability with finites is inherited unchanged from
//! `PartialOrd` on the wrapped `T`.

use std::cmp::Ordering;

#[derive(Copy, Clone, Debug)]
pub enum FloatExt<T> {
    Bot,
    Finite(T),
    Top,
}

macro_rules! impl_float_ext {
    ($T:ty) => {
        impl PartialEq for FloatExt<$T> {
            fn eq(&self, other: &Self) -> bool {
                use FloatExt::*;
                match (self, other) {
                    (Bot, Bot) | (Top, Top) => true,
                    (Finite(a), Finite(b)) => {
                        if a.is_nan() && b.is_nan() {
                            true
                        } else {
                            a == b
                        }
                    }
                    _ => false,
                }
            }
        }

        impl PartialOrd for FloatExt<$T> {
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                use FloatExt::*;
                match (self, other) {
                    (Bot, Bot) | (Top, Top) => Some(Ordering::Equal),
                    (Bot, _) => Some(Ordering::Less),
                    (_, Bot) => Some(Ordering::Greater),
                    (_, Top) => Some(Ordering::Less),
                    (Top, _) => Some(Ordering::Greater),
                    (Finite(a), Finite(b)) => {
                        if a.is_nan() && b.is_nan() {
                            Some(Ordering::Equal)
                        } else {
                            a.partial_cmp(b)
                        }
                    }
                }
            }
        }
    };
}

impl_float_ext!(f32);
impl_float_ext!(f64);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bot_below_everything_f64() {
        assert!(FloatExt::<f64>::Bot < FloatExt::Finite(0.0));
        assert!(FloatExt::<f64>::Bot < FloatExt::Finite(f64::NEG_INFINITY));
        assert!(FloatExt::<f64>::Bot < FloatExt::Finite(f64::NAN));
        assert!(FloatExt::<f64>::Bot < FloatExt::<f64>::Top);
    }

    #[test]
    fn top_above_everything_f64() {
        assert!(FloatExt::Finite(0.0_f64) < FloatExt::<f64>::Top);
        assert!(FloatExt::Finite(f64::INFINITY) < FloatExt::<f64>::Top);
        assert!(FloatExt::Finite(f64::NAN) < FloatExt::<f64>::Top);
    }

    #[test]
    fn nan_reflexive_f64() {
        let n: FloatExt<f64> = FloatExt::Finite(f64::NAN);
        assert_eq!(n, FloatExt::Finite(f64::NAN));
        assert_eq!(n.partial_cmp(&FloatExt::Finite(f64::NAN)), Some(Ordering::Equal));
    }

    #[test]
    fn nan_incomparable_with_finite_f64() {
        let n: FloatExt<f64> = FloatExt::Finite(f64::NAN);
        assert!(n.partial_cmp(&FloatExt::Finite(1.0)).is_none());
        assert!(FloatExt::Finite(1.0_f64).partial_cmp(&n).is_none());
    }

    #[test]
    fn nan_incomparable_with_infinity_f64() {
        let n: FloatExt<f64> = FloatExt::Finite(f64::NAN);
        let i: FloatExt<f64> = FloatExt::Finite(f64::INFINITY);
        assert!(n.partial_cmp(&i).is_none());
        assert!(i.partial_cmp(&n).is_none());
    }

    #[test]
    fn standard_order_preserved_f64() {
        assert!(FloatExt::Finite(1.0_f64) < FloatExt::Finite(2.0));
        assert!(FloatExt::Finite(f64::NEG_INFINITY) < FloatExt::Finite(0.0_f64));
        assert!(FloatExt::Finite(0.0_f64) < FloatExt::Finite(f64::INFINITY));
    }

    #[test]
    fn f32_same_shape() {
        let n: FloatExt<f32> = FloatExt::Finite(f32::NAN);
        assert_eq!(n, FloatExt::Finite(f32::NAN));
        assert!(FloatExt::<f32>::Bot < n);
        assert!(n < FloatExt::<f32>::Top);
        assert!(n.partial_cmp(&FloatExt::Finite(1.0_f32)).is_none());
    }
}
