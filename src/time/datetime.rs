//! Naive `PrimitiveDateTime` connections.
//!
//! Hosts [`PDTMDATE`] — drops sub-day time fragments to a calendar-
//! date rung.

use crate::conn::Conn;
use crate::extended::Extended;
use time::{Date, PrimitiveDateTime, Time};

/// `PrimitiveDateTime → Extended<Date>` — naive datetime ↔ calendar
/// date, rounding sub-day fractions.
///
/// On the interior:
/// - `floor(p) = Finite(p.date())` — drop the time part.
/// - `ceil(p) = Finite(p.date())` if `p.time() == Time::MIDNIGHT`,
///   otherwise `Finite(p.date().next_day().unwrap())`.
/// - `inner(Finite(d))` = `PrimitiveDateTime::new(d, Time::MIDNIGHT)`.
///
/// `Extended::NegInf` / `Extended::PosInf` saturate at
/// `PrimitiveDateTime::MIN` / `MAX`. `inner` is non-injective at the
/// extremes (`NegInf` and `Finite(Date::MIN)` both decode to
/// `PrimitiveDateTime::MIN`) so adjacent ceil/floor at those points
/// disagree on whether to step into the saturation arm.
///
/// # Examples
///
/// ```rust
/// use connections::time::PDTMDATE;
/// use connections::extended::Extended;
/// use time::{Date, Month, PrimitiveDateTime, Time};
///
/// let day = Date::from_calendar_date(2026, Month::April, 26).unwrap();
///
/// // Midnight: ceil = floor = same day.
/// let p_midnight = PrimitiveDateTime::new(day, Time::MIDNIGHT);
/// assert_eq!(PDTMDATE.ceil(p_midnight),  Extended::Finite(day));
/// assert_eq!(PDTMDATE.floor(p_midnight), Extended::Finite(day));
///
/// // Any later time: ceil rolls forward to next day.
/// let p_later = PrimitiveDateTime::new(day, Time::from_hms(0, 0, 1).unwrap());
/// assert_eq!(PDTMDATE.ceil(p_later),  Extended::Finite(day.next_day().unwrap()));
/// assert_eq!(PDTMDATE.floor(p_later), Extended::Finite(day));
///
/// assert_eq!(PDTMDATE.inner(Extended::Finite(day)), p_midnight);
/// ```
pub const PDTMDATE: Conn<PrimitiveDateTime, Extended<Date>> = {
    fn ceil(p: PrimitiveDateTime) -> Extended<Date> {
        if p.eq(&PrimitiveDateTime::MIN) {
            return Extended::NegInf;
        }
        let d = p.date();
        if p.time().eq(&Time::MIDNIGHT) {
            return Extended::Finite(d);
        }
        // time() > MIDNIGHT — round up to the next day.
        match d.next_day() {
            Some(next) => Extended::Finite(next),
            None => Extended::PosInf,
        }
    }

    fn inner(b: Extended<Date>) -> PrimitiveDateTime {
        match b {
            Extended::NegInf => PrimitiveDateTime::MIN,
            Extended::Finite(d) => PrimitiveDateTime::new(d, Time::MIDNIGHT),
            Extended::PosInf => PrimitiveDateTime::MAX,
        }
    }

    fn floor(p: PrimitiveDateTime) -> Extended<Date> {
        if p.eq(&PrimitiveDateTime::MAX) {
            return Extended::PosInf;
        }
        Extended::Finite(p.date())
    }

    Conn::new(ceil, inner, floor)
};

#[cfg(test)]
mod tests {
    use super::*;
    use crate::prop::arb::{arb_date, arb_extended_date, arb_primitive_dt};
    use crate::prop::{conn as conn_laws, lattice as lattice_laws};
    use proptest::prelude::*;
    use time::Month;

    // ── Preorder laws on `PrimitiveDateTime` ────────────────────

    mod primitive_dt_preorder {
        use super::*;

        proptest! {
            #[test]
            fn reflexive(x in arb_primitive_dt()) {
                prop_assert!(lattice_laws::lattice_reflexive(&x));
            }

            #[test]
            fn transitive(
                x in arb_primitive_dt(),
                y in arb_primitive_dt(),
                z in arb_primitive_dt(),
            ) {
                prop_assert!(lattice_laws::lattice_transitive(&x, &y, &z));
            }

            #[test]
            fn antisymmetric(x in arb_primitive_dt(), y in arb_primitive_dt()) {
                prop_assert!(lattice_laws::lattice_antisymmetric(&x, &y));
            }

            #[test]
            fn bot(x in arb_primitive_dt()) {
                prop_assert!(lattice_laws::lattice_bot(&PrimitiveDateTime::MIN, &x));
            }

            #[test]
            fn top(x in arb_primitive_dt()) {
                prop_assert!(lattice_laws::lattice_top(&PrimitiveDateTime::MAX, &x));
            }
        }
    }

    // ── PDTMDATE spot checks ────────────────────────────────────

    #[test]
    fn midnight_fixes_date() {
        let d = Date::from_calendar_date(2000, Month::January, 1).unwrap();
        let p = PrimitiveDateTime::new(d, Time::MIDNIGHT);
        assert_eq!(PDTMDATE.ceil(p), Extended::Finite(d));
        assert_eq!(PDTMDATE.floor(p), Extended::Finite(d));
        assert_eq!(PDTMDATE.inner(Extended::Finite(d)), p);
    }

    #[test]
    fn one_ns_after_midnight_ceils_to_next_day() {
        let d = Date::from_calendar_date(2000, Month::January, 1).unwrap();
        let p = PrimitiveDateTime::new(d, Time::from_hms_nano(0, 0, 0, 1).unwrap());
        assert_eq!(PDTMDATE.ceil(p), Extended::Finite(d.next_day().unwrap()));
        assert_eq!(PDTMDATE.floor(p), Extended::Finite(d));
    }

    #[test]
    fn extremes() {
        assert_eq!(PDTMDATE.ceil(PrimitiveDateTime::MIN), Extended::NegInf);
        assert_eq!(
            PDTMDATE.floor(PrimitiveDateTime::MIN),
            Extended::Finite(Date::MIN)
        );
        assert_eq!(PDTMDATE.ceil(PrimitiveDateTime::MAX), Extended::PosInf);
        assert_eq!(PDTMDATE.floor(PrimitiveDateTime::MAX), Extended::PosInf);

        assert_eq!(PDTMDATE.inner(Extended::NegInf), PrimitiveDateTime::MIN);
        assert_eq!(PDTMDATE.inner(Extended::PosInf), PrimitiveDateTime::MAX);
    }

    #[test]
    fn date_max_with_subday_ceils_to_posinf() {
        let p = PrimitiveDateTime::new(Date::MAX, Time::from_hms_nano(0, 0, 0, 1).unwrap());
        assert_eq!(PDTMDATE.ceil(p), Extended::PosInf);
        assert_eq!(PDTMDATE.floor(p), Extended::Finite(Date::MAX));
    }

    // ── PDTMDATE Galois law battery ─────────────────────────────

    proptest! {
        #[test]
        fn galois_l(p in arb_primitive_dt(), b in arb_extended_date()) {
            prop_assert!(conn_laws::conn_galois_l(&PDTMDATE, p, b));
        }

        #[test]
        fn galois_r(p in arb_primitive_dt(), b in arb_extended_date()) {
            prop_assert!(conn_laws::conn_galois_r(&PDTMDATE, p, b));
        }

        #[test]
        fn closure_l(p in arb_primitive_dt()) {
            prop_assert!(conn_laws::conn_closure_l(&PDTMDATE, p));
        }

        #[test]
        fn closure_r(p in arb_primitive_dt()) {
            prop_assert!(conn_laws::conn_closure_r(&PDTMDATE, p));
        }

        #[test]
        fn kernel_l(b in arb_extended_date()) {
            prop_assert!(conn_laws::conn_kernel_l(&PDTMDATE, b));
        }

        #[test]
        fn kernel_r(b in arb_extended_date()) {
            prop_assert!(conn_laws::conn_kernel_r(&PDTMDATE, b));
        }

        #[test]
        fn monotone_l(a in arb_primitive_dt(), b in arb_primitive_dt()) {
            prop_assert!(conn_laws::conn_monotone_l(&PDTMDATE, a, b));
        }

        #[test]
        fn monotone_r(a in arb_extended_date(), b in arb_extended_date()) {
            prop_assert!(conn_laws::conn_monotone_r(&PDTMDATE, a, b));
        }

        #[test]
        fn idempotent(p in arb_primitive_dt()) {
            prop_assert!(conn_laws::conn_idempotent(&PDTMDATE, p));
        }

        // ulp_bound: extractor collapses NegInf into the same
        // rung as Finite(Date::MIN) (because inner saturates
        // both onto PDT::MIN, so they're a single equivalence
        // class) and lifts PosInf to MAX_JD + 1. This keeps
        // ceil ≥ floor for every input.
        #[test]
        fn ulp_bound(p in arb_primitive_dt()) {
            let max_jd = Date::MAX.to_julian_day() as i64;
            let min_jd = Date::MIN.to_julian_day() as i64;
            let extractor = move |b: Extended<Date>| -> i64 {
                match b {
                    Extended::NegInf => min_jd,
                    Extended::Finite(d) => d.to_julian_day() as i64,
                    Extended::PosInf => max_jd + 1,
                }
            };
            prop_assert!(conn_laws::conn_ulp_bound(&PDTMDATE, p, extractor));
        }

        // Roundtrip on Finite Date with d > Date::MIN. At
        // exactly d = Date::MIN, `inner(Finite(MIN))` = PDT::MIN
        // and `ceil(PDT::MIN)` = NegInf (Galois-forced — same
        // equivalence class as Finite(MIN), but distinct
        // representatives); ceil's roundtrip is therefore
        // non-strict at the lower extreme. `roundtrip_floor`
        // is unaffected because `floor(PDT::MIN)` returns
        // `Finite(MIN)` directly.
        #[test]
        fn roundtrip_ceil(d in arb_date().prop_filter("excludes Date::MIN", |d| *d != Date::MIN)) {
            prop_assert!(conn_laws::conn_roundtrip_ceil(&PDTMDATE, Extended::Finite(d)));
        }

        #[test]
        fn roundtrip_floor(d in arb_date()) {
            prop_assert!(conn_laws::conn_roundtrip_floor(&PDTMDATE, Extended::Finite(d)));
        }
    }
}
