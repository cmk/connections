//! Galois connections among the [`time`](https://docs.rs/time) crate's
//! calendar / clock / duration types.
//!
//! # Naming convention
//!
//! Constants in this module use an **8-character** name in place of the
//! 6-character `XYYZZZ` shape used by the integer / fixed / sample
//! ladders. Each half is four characters drawn from one of:
//!
//! | half pattern | shape                                       | example |
//! |--------------|---------------------------------------------|---------|
//! | `A123`       | 1 letter + 3 digits                         | `F009`  |
//! | `AB12`       | 2 letters + 2 digits                        | `DR01`  |
//! | `ABC1`       | 3 letters + 1 digit                         | `DUR0`  |
//! | `ABCD`       | 4 letters                                   | `DATE`  |
//!
//! The two halves of a constant name need not share the same pattern.
//! All constants in this module use the all-letter `ABCDXWYZ` shape
//! because the source/target types are domain-typed (`Date`, `Time`,
//! `Duration`, `PrimitiveDateTime`) rather than tier-coded.
//!
//! # Constants (added incrementally — see [`crate::doc/plans`])
//!
//! Pending — see the sprint plan. Each constant ships with a runnable
//! `# Examples` doctest and a `proptest!` block driving the laws in
//! [`crate::property::laws`].
//!
//! # Verification
//!
//! Every `Conn` constant is exercised in `#[cfg(test)] mod tests` by
//! the full Galois law battery from [`crate::property::laws`]. The
//! [`Ple`](crate::lattice::Ple) impls below delegate to the time
//! crate's existing total `Ord` — no NaN handling is needed.
//!
//! ```rust
//! use time::{Date, Month};
//! let d = Date::from_calendar_date(2000, Month::January, 1).unwrap();
//! assert_eq!(d.year(), 2000);
//! ```

use crate::lattice::Ple;
use time::{Date, Duration, PrimitiveDateTime, Time};

// ── Ple impls ────────────────────────────────────────────────────
//
// Each time crate type below has a total `Ord` (no NaN, no
// not-a-number sentinel), so its `Ple` is just the standard `<=`.
// No N5 patching needed.

impl Ple for Date {
    fn ple(&self, other: &Self) -> bool { self <= other }
}

impl Ple for Time {
    fn ple(&self, other: &Self) -> bool { self <= other }
}

impl Ple for Duration {
    fn ple(&self, other: &Self) -> bool { self <= other }
}

impl Ple for PrimitiveDateTime {
    fn ple(&self, other: &Self) -> bool { self <= other }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::property::arb::{arb_date, arb_duration, arb_primitive_dt, arb_time};
    use crate::property::laws;
    use proptest::prelude::*;

    // ── Preorder laws ────────────────────────────────────────────
    //
    // `Date`, `Time`, `Duration`, `PrimitiveDateTime` all have total
    // `Ord`, so reflexivity / transitivity / antisymmetry follow
    // directly. The bot/top probes drive `lattice_bot` / `lattice_top`
    // against each type's natural extremes.

    mod date_preorder {
        use super::*;

        proptest! {
            #[test]
            fn reflexive(x in arb_date()) {
                prop_assert!(laws::lattice_reflexive(&x));
            }

            #[test]
            fn transitive(x in arb_date(), y in arb_date(), z in arb_date()) {
                prop_assert!(laws::lattice_transitive(&x, &y, &z));
            }

            #[test]
            fn antisymmetric(x in arb_date(), y in arb_date()) {
                prop_assert!(laws::lattice_antisymmetric(&x, &y, &Date::MAX, &Date::MIN));
            }

            #[test]
            fn bot(x in arb_date()) {
                prop_assert!(laws::lattice_bot(&Date::MIN, &x));
            }

            #[test]
            fn top(x in arb_date()) {
                prop_assert!(laws::lattice_top(&Date::MAX, &x));
            }
        }
    }

    mod time_preorder {
        use super::*;

        proptest! {
            #[test]
            fn reflexive(x in arb_time()) {
                prop_assert!(laws::lattice_reflexive(&x));
            }

            #[test]
            fn transitive(x in arb_time(), y in arb_time(), z in arb_time()) {
                prop_assert!(laws::lattice_transitive(&x, &y, &z));
            }

            #[test]
            fn antisymmetric(x in arb_time(), y in arb_time()) {
                let top = Time::from_hms_nano(23, 59, 59, 999_999_999).unwrap();
                prop_assert!(laws::lattice_antisymmetric(&x, &y, &top, &Time::MIDNIGHT));
            }

            #[test]
            fn bot(x in arb_time()) {
                prop_assert!(laws::lattice_bot(&Time::MIDNIGHT, &x));
            }

            #[test]
            fn top(x in arb_time()) {
                // 23:59:59.999_999_999 is the supremum of representable Time.
                let top = Time::from_hms_nano(23, 59, 59, 999_999_999).unwrap();
                prop_assert!(laws::lattice_top(&top, &x));
            }
        }
    }

    mod duration_preorder {
        use super::*;

        proptest! {
            #[test]
            fn reflexive(x in arb_duration()) {
                prop_assert!(laws::lattice_reflexive(&x));
            }

            #[test]
            fn transitive(x in arb_duration(), y in arb_duration(), z in arb_duration()) {
                prop_assert!(laws::lattice_transitive(&x, &y, &z));
            }

            #[test]
            fn antisymmetric(x in arb_duration(), y in arb_duration()) {
                prop_assert!(laws::lattice_antisymmetric(
                    &x, &y, &Duration::MAX, &Duration::MIN,
                ));
            }

            #[test]
            fn bot(x in arb_duration()) {
                prop_assert!(laws::lattice_bot(&Duration::MIN, &x));
            }

            #[test]
            fn top(x in arb_duration()) {
                prop_assert!(laws::lattice_top(&Duration::MAX, &x));
            }
        }
    }

    mod primitive_dt_preorder {
        use super::*;

        proptest! {
            #[test]
            fn reflexive(x in arb_primitive_dt()) {
                prop_assert!(laws::lattice_reflexive(&x));
            }

            #[test]
            fn transitive(
                x in arb_primitive_dt(),
                y in arb_primitive_dt(),
                z in arb_primitive_dt(),
            ) {
                prop_assert!(laws::lattice_transitive(&x, &y, &z));
            }

            #[test]
            fn antisymmetric(x in arb_primitive_dt(), y in arb_primitive_dt()) {
                prop_assert!(laws::lattice_antisymmetric(
                    &x, &y, &PrimitiveDateTime::MAX, &PrimitiveDateTime::MIN,
                ));
            }

            #[test]
            fn bot(x in arb_primitive_dt()) {
                prop_assert!(laws::lattice_bot(&PrimitiveDateTime::MIN, &x));
            }

            #[test]
            fn top(x in arb_primitive_dt()) {
                prop_assert!(laws::lattice_top(&PrimitiveDateTime::MAX, &x));
            }
        }
    }
}
