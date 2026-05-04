//! Calendar-`Date` connections.
//!
//! Hosts [`DATEJDAY`] — the proleptic-Gregorian Julian-day Conn over
//! `Extended<Date>` and `i32`.

use crate::extended::Extended;
use time::Date;

const MIN_JD: i32 = Date::MIN.to_julian_day();
const MAX_JD: i32 = Date::MAX.to_julian_day();

fn datejday_ceil(d: Extended<Date>) -> i32 {
    match d {
        // ceil(NegInf): smallest b with NegInf ≤ inner(b) — every b qualifies.
        Extended::NegInf => i32::MIN,
        Extended::Finite(date) => date.to_julian_day(),
        // ceil(PosInf): smallest b with inner(b) = PosInf, i.e. b > MAX_JD.
        Extended::PosInf => MAX_JD + 1,
    }
}

fn datejday_inner(jd: i32) -> Extended<Date> {
    if jd < MIN_JD {
        Extended::NegInf
    } else if jd > MAX_JD {
        Extended::PosInf
    } else {
        match Date::from_julian_day(jd) {
            Ok(d) => Extended::Finite(d),
            Err(_) => unreachable!("jd in [MIN_JD, MAX_JD]"),
        }
    }
}

crate::conn_l! {
    /// `Extended<Date> → i32` — the proleptic-Gregorian Julian-day
    /// connection.
    ///
    /// One-sided left-Galois Conn (`Conn::new_l(ceil, inner)`):
    /// `inner: i32 → Extended<Date>` saturates `i32` values outside
    /// `[Date::MIN.to_julian_day(), Date::MAX.to_julian_day()]` onto
    /// `Extended::NegInf` / `Extended::PosInf`, which makes `inner`
    /// non-order-reflecting at the synthetic extremes. The constructor
    /// wires `floor = ceil` as a fn pointer so `floor(a) ≤ ceil(a)`
    /// holds structurally over the full source domain.
    ///
    /// On the `Finite` portion this is an exact bijection: for any
    /// `Date` `d`, `ceil(Finite(d)) == d.to_julian_day()`, and `inner`
    /// recovers `d` from its Julian day. `Date` admits no sub-day
    /// fraction, so `ceil` and `floor` agree on Finite inputs.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::time::DATEJDAY;
    /// use connections::extended::Extended;
    /// use time::{Date, Month};
    ///
    /// let epoch = Date::from_calendar_date(1970, Month::January, 1).unwrap();
    /// assert_eq!(DATEJDAY.ceil(Extended::Finite(epoch)), 2_440_588);
    /// assert_eq!(DATEJDAY.inner(2_440_588), Extended::Finite(epoch));
    ///
    /// // Out-of-range julian day saturates to PosInf.
    /// assert_eq!(DATEJDAY.inner(i32::MAX), Extended::PosInf);
    /// ```
    pub DATEJDAY : Extended<Date> => i32 {
        ceil:  datejday_ceil,
        inner: datejday_inner,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[allow(unused_imports)]
    use crate::conn::{ViewL, ViewR};
    use crate::prop::arb::{arb_date, arb_extended_date, arb_jd_in_range};
    use crate::prop::{conn as conn_laws, lattice as lattice_laws};
    use proptest::prelude::*;
    use time::Month;

    const MIN_JD: i32 = Date::MIN.to_julian_day();
    const MAX_JD: i32 = Date::MAX.to_julian_day();

    // ── Preorder laws on `Date` ─────────────────────────────────
    //
    // `Date` has total `Ord`, so reflexivity / transitivity /
    // antisymmetry follow directly. The bot/top probes drive
    // `lattice_bot` / `lattice_top` against `Date::{MIN, MAX}`.

    mod date_preorder {
        use super::*;

        proptest! {
            #[test]
            fn reflexive(x in arb_date()) {
                prop_assert!(lattice_laws::lattice_reflexive(&x));
            }

            #[test]
            fn transitive(x in arb_date(), y in arb_date(), z in arb_date()) {
                prop_assert!(lattice_laws::lattice_transitive(&x, &y, &z));
            }

            #[test]
            fn antisymmetric(x in arb_date(), y in arb_date()) {
                prop_assert!(lattice_laws::lattice_antisymmetric(&x, &y));
            }

            #[test]
            fn bot(x in arb_date()) {
                prop_assert!(lattice_laws::lattice_bot(&Date::MIN, &x));
            }

            #[test]
            fn top(x in arb_date()) {
                prop_assert!(lattice_laws::lattice_top(&Date::MAX, &x));
            }
        }
    }

    // ── DATEJDAY spot checks ────────────────────────────────────

    #[test]
    fn epoch_is_2440588() {
        let epoch = Date::from_calendar_date(1970, Month::January, 1).unwrap();
        assert_eq!(DATEJDAY.ceil(Extended::Finite(epoch)), 2_440_588);
        assert_eq!(DATEJDAY.inner(2_440_588), Extended::Finite(epoch));
    }

    #[test]
    fn min_max_round_trip() {
        assert_eq!(
            DATEJDAY.inner(Date::MIN.to_julian_day()),
            Extended::Finite(Date::MIN),
        );
        assert_eq!(
            DATEJDAY.inner(Date::MAX.to_julian_day()),
            Extended::Finite(Date::MAX),
        );
    }

    #[test]
    fn saturation_extremes() {
        assert_eq!(DATEJDAY.inner(i32::MAX), Extended::PosInf);
        assert_eq!(DATEJDAY.inner(i32::MIN), Extended::NegInf);
        assert_eq!(DATEJDAY.inner(MIN_JD - 1), Extended::NegInf);
        assert_eq!(DATEJDAY.inner(MAX_JD + 1), Extended::PosInf);

        assert_eq!(DATEJDAY.ceil(Extended::NegInf), i32::MIN);
        assert_eq!(DATEJDAY.ceil(Extended::PosInf), MAX_JD + 1);
        // `new_left` wires `floor = ceil` structurally.
        assert_eq!(DATEJDAY.ceil(Extended::NegInf), i32::MIN);
        assert_eq!(DATEJDAY.ceil(Extended::PosInf), MAX_JD + 1);
    }

    // ── DATEJDAY Galois law battery (one-sided L) ───────────────
    //
    // Roundtrip law uses `arb_jd_in_range` (bounded to the finite
    // Date range) because saturation makes the round-trip non-strict
    // outside `[MIN_JD, MAX_JD]`.

    proptest! {
        #[test]
        fn galois_l(d in arb_extended_date(), b in any::<i32>()) {
            prop_assert!(conn_laws::galois_l(&DATEJDAY, d, b));
        }

        #[test]
        fn closure_l(d in arb_extended_date()) {
            prop_assert!(conn_laws::closure_l(&DATEJDAY, d));
        }

        #[test]
        fn kernel_l(b in any::<i32>()) {
            prop_assert!(conn_laws::kernel_l(&DATEJDAY, b));
        }

        #[test]
        fn monotone_l(a in arb_extended_date(), b in arb_extended_date()) {
            prop_assert!(conn_laws::monotone_l(&DATEJDAY, a, b));
        }

        #[test]
        fn idempotent(d in arb_extended_date()) {
            prop_assert!(conn_laws::idempotent(&DATEJDAY, d));
        }

        #[test]
        fn roundtrip_ceil(b in arb_jd_in_range()) {
            prop_assert!(conn_laws::roundtrip_ceil(&DATEJDAY, b));
        }
    }
}
