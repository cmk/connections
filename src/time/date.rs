//! Calendar-`Date` connections.
//!
//! Hosts [`DATEJDAY`] — the proleptic-Gregorian Julian-day Conn over
//! `Extended<Date>` and `i32`.

use crate::conn::Conn;
use crate::extended::Extended;
use time::Date;

/// `Extended<Date> → i32` — the proleptic-Gregorian Julian-day
/// connection.
///
/// On the `Finite` portion this is an exact bijection: for any
/// `Date` `d`, `ceil(Finite(d)) == floor(Finite(d)) == d.to_julian_day()`,
/// and `inner` recovers `d` from its Julian day. The two adjoints
/// agree because `to_julian_day` is monotone and `Date` admits no
/// sub-day fraction.
///
/// `i32` Julian days outside `[Date::MIN.to_julian_day(),
/// Date::MAX.to_julian_day()]` saturate to `Extended::NegInf` /
/// `Extended::PosInf` so the Galois laws hold over the full `i32`
/// rung. The saturation thresholds (a single "off-by-one" rung
/// outside the finite range) are dictated by the adjoint laws — see
/// the `Conn::new(ceil, inner, floor)` body for the per-variant
/// rationale.
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
/// assert_eq!(DATEJDAY.floor(Extended::Finite(epoch)), 2_440_588);
/// assert_eq!(DATEJDAY.inner(2_440_588), Extended::Finite(epoch));
///
/// // Out-of-range julian day saturates to PosInf.
/// assert_eq!(DATEJDAY.inner(i32::MAX), Extended::PosInf);
/// ```
pub const DATEJDAY: Conn<Extended<Date>, i32> = {
    const MIN_JD: i32 = Date::MIN.to_julian_day();
    const MAX_JD: i32 = Date::MAX.to_julian_day();

    fn ceil(d: Extended<Date>) -> i32 {
        match d {
            // ceil(NegInf): smallest b with NegInf ≤ inner(b) — every b qualifies.
            Extended::NegInf => i32::MIN,
            Extended::Finite(date) => date.to_julian_day(),
            // ceil(PosInf): smallest b with inner(b) = PosInf, i.e. b > MAX_JD.
            Extended::PosInf => MAX_JD + 1,
        }
    }

    fn inner(jd: i32) -> Extended<Date> {
        if jd < MIN_JD {
            Extended::NegInf
        } else if jd > MAX_JD {
            Extended::PosInf
        } else {
            // Bounds-checked above; from_julian_day cannot fail.
            match Date::from_julian_day(jd) {
                Ok(d) => Extended::Finite(d),
                Err(_) => unreachable!("jd in [MIN_JD, MAX_JD]"),
            }
        }
    }

    fn floor(d: Extended<Date>) -> i32 {
        match d {
            // floor(NegInf): largest b with inner(b) ≤ NegInf, i.e. b < MIN_JD.
            Extended::NegInf => MIN_JD - 1,
            Extended::Finite(date) => date.to_julian_day(),
            // floor(PosInf): largest b with inner(b) ≤ PosInf — every b qualifies.
            Extended::PosInf => i32::MAX,
        }
    }

    Conn::new(ceil, inner, floor)
};

#[cfg(test)]
mod tests {
    use super::*;
    use crate::property::arb::{arb_date, arb_extended_date, arb_jd_in_range};
    use crate::property::laws;
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
                prop_assert!(laws::lattice_reflexive(&x));
            }

            #[test]
            fn transitive(x in arb_date(), y in arb_date(), z in arb_date()) {
                prop_assert!(laws::lattice_transitive(&x, &y, &z));
            }

            #[test]
            fn antisymmetric(x in arb_date(), y in arb_date()) {
                prop_assert!(laws::lattice_antisymmetric(&x, &y));
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

    // ── DATEJDAY spot checks ────────────────────────────────────

    #[test]
    fn epoch_is_2440588() {
        let epoch = Date::from_calendar_date(1970, Month::January, 1).unwrap();
        assert_eq!(DATEJDAY.ceil(Extended::Finite(epoch)), 2_440_588);
        assert_eq!(DATEJDAY.floor(Extended::Finite(epoch)), 2_440_588);
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
        assert_eq!(DATEJDAY.floor(Extended::NegInf), MIN_JD - 1);
        assert_eq!(DATEJDAY.floor(Extended::PosInf), i32::MAX);
    }

    // ── DATEJDAY Galois law battery ─────────────────────────────
    //
    // Roundtrip laws use `arb_jd_in_range` (bounded to the finite
    // Date range) because saturation makes the round-trip non-strict
    // outside `[MIN_JD, MAX_JD]`.

    proptest! {
        #[test]
        fn galois_l(d in arb_extended_date(), b in any::<i32>()) {
            prop_assert!(laws::conn_galois_l(&DATEJDAY, d, b));
        }

        #[test]
        fn galois_r(d in arb_extended_date(), b in any::<i32>()) {
            prop_assert!(laws::conn_galois_r(&DATEJDAY, d, b));
        }

        #[test]
        fn closure_l(d in arb_extended_date()) {
            prop_assert!(laws::conn_closure_l(&DATEJDAY, d));
        }

        #[test]
        fn closure_r(d in arb_extended_date()) {
            prop_assert!(laws::conn_closure_r(&DATEJDAY, d));
        }

        #[test]
        fn kernel_l(b in any::<i32>()) {
            prop_assert!(laws::conn_kernel_l(&DATEJDAY, b));
        }

        #[test]
        fn kernel_r(b in any::<i32>()) {
            prop_assert!(laws::conn_kernel_r(&DATEJDAY, b));
        }

        #[test]
        fn monotone_l(a in arb_extended_date(), b in arb_extended_date()) {
            prop_assert!(laws::conn_monotone_l(&DATEJDAY, a, b));
        }

        #[test]
        fn monotone_r(a in any::<i32>(), b in any::<i32>()) {
            prop_assert!(laws::conn_monotone_r(&DATEJDAY, a, b));
        }

        // `conn_floor_le_ceil` does **not** hold in general for
        // Extended-source connections: at `Extended::NegInf` the
        // adjoint definitions force `ceil = i32::MIN` and
        // `floor = MIN_JD − 1`, so `floor > ceil`. Same shape as
        // `conn::int::U008I016` and the other Extended-source ints
        // — see their test mod for prior precedent.

        #[test]
        fn idempotent(d in arb_extended_date()) {
            prop_assert!(laws::conn_idempotent(&DATEJDAY, d));
        }

        // Round-trip laws hold only on the finite portion of the
        // i32 rung — saturation collapses out-of-range jd to ±Inf,
        // so ceil(inner(b)) ≠ b for those.
        #[test]
        fn roundtrip_ceil(b in arb_jd_in_range()) {
            prop_assert!(laws::conn_roundtrip_ceil(&DATEJDAY, b));
        }

        #[test]
        fn roundtrip_floor(b in arb_jd_in_range()) {
            prop_assert!(laws::conn_roundtrip_floor(&DATEJDAY, b));
        }
    }
}
