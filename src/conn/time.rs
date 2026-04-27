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

use crate::conn::Conn;
use crate::extended::Extended;
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

// ── DATEJDAY ─────────────────────────────────────────────────────

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
/// use connections::conn::time::DATEJDAY;
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

// ── TIMENANO ─────────────────────────────────────────────────────

/// `Extended<Time> → i64` — clock time ↔ nanoseconds-since-midnight.
///
/// On the `Finite` portion this is an exact bijection: every
/// `Time` value corresponds to exactly one `i64` in
/// `[0, 86_400 × 10⁹)`, and every such `i64` decodes to a unique
/// `Time`. `i64` values outside that range saturate to
/// `Extended::NegInf` (negative ns) / `Extended::PosInf`
/// (≥ 86_400 × 10⁹ ns).
///
/// `ceil(Finite(t)) == floor(Finite(t))` because `Time` carries no
/// finer-than-nanosecond fraction. The two adjoints differ only on
/// the saturation arms — see the per-variant rationale in the
/// `Conn::new(ceil, inner, floor)` body.
///
/// # Examples
///
/// ```rust
/// use connections::conn::time::TIMENANO;
/// use connections::extended::Extended;
/// use time::Time;
///
/// assert_eq!(TIMENANO.ceil(Extended::Finite(Time::MIDNIGHT)), 0);
/// assert_eq!(
///     TIMENANO.ceil(Extended::Finite(
///         Time::from_hms_nano(23, 59, 59, 999_999_999).unwrap(),
///     )),
///     86_399_999_999_999,
/// );
/// assert_eq!(
///     TIMENANO.inner(43_200_000_000_000),
///     Extended::Finite(Time::from_hms(12, 0, 0).unwrap()),
/// );
///
/// // Out-of-range nanoseconds saturate.
/// assert_eq!(TIMENANO.inner(-1), Extended::NegInf);
/// assert_eq!(TIMENANO.inner(86_400_000_000_000), Extended::PosInf);
/// ```
pub const TIMENANO: Conn<Extended<Time>, i64> = {
    const NS_PER_HOUR: i64 = 3_600_000_000_000;
    const NS_PER_MIN: i64 = 60_000_000_000;
    const NS_PER_SEC: i64 = 1_000_000_000;
    const NS_MAX: i64 = 86_400 * NS_PER_SEC - 1;

    fn time_to_ns(t: Time) -> i64 {
        // `as_hms_nano` returns (h, m, s, ns) — total ≤ NS_MAX, fits i64.
        let (h, m, s, ns) = t.as_hms_nano();
        h as i64 * NS_PER_HOUR
            + m as i64 * NS_PER_MIN
            + s as i64 * NS_PER_SEC
            + ns as i64
    }

    fn ns_to_time(ns: i64) -> Time {
        // Caller has already bounded `ns` to [0, NS_MAX].
        let h = (ns / NS_PER_HOUR) as u8;
        let m = ((ns / NS_PER_MIN) % 60) as u8;
        let s = ((ns / NS_PER_SEC) % 60) as u8;
        let n = (ns % NS_PER_SEC) as u32;
        match Time::from_hms_nano(h, m, s, n) {
            Ok(t) => t,
            Err(_) => unreachable!("ns in [0, NS_MAX] decomposes to valid HMS-nano"),
        }
    }

    fn ceil(t: Extended<Time>) -> i64 {
        match t {
            Extended::NegInf => i64::MIN,
            Extended::Finite(time) => time_to_ns(time),
            Extended::PosInf => NS_MAX + 1,
        }
    }

    fn inner(ns: i64) -> Extended<Time> {
        if ns < 0 {
            Extended::NegInf
        } else if ns > NS_MAX {
            Extended::PosInf
        } else {
            Extended::Finite(ns_to_time(ns))
        }
    }

    fn floor(t: Extended<Time>) -> i64 {
        match t {
            Extended::NegInf => -1,
            Extended::Finite(time) => time_to_ns(time),
            Extended::PosInf => i64::MAX,
        }
    }

    Conn::new(ceil, inner, floor)
};

// ── TIMESECS ─────────────────────────────────────────────────────

/// `Extended<Time> → i64` — clock time ↔ whole seconds since
/// midnight (the first proper-Galois time conn: `ceil` and `floor`
/// disagree on sub-second inputs).
///
/// On the `Finite` portion:
/// - `floor(Finite(t))` = `t.hour() * 3600 + t.minute() * 60 +
///   t.second()` — truncates the sub-second part.
/// - `ceil(Finite(t))` equals `floor` when `t.nanosecond() == 0`,
///   otherwise `floor + 1`.
/// - `inner(secs)` = `Finite(Time::from_hms(...))` for
///   `secs ∈ [0, 86_400)`.
///
/// `i64` rung values outside `[0, 86_400)` saturate to
/// `Extended::NegInf` (negative seconds) / `Extended::PosInf` (≥
/// 86_400 s).
///
/// # Examples
///
/// ```rust
/// use connections::conn::time::TIMESECS;
/// use connections::extended::Extended;
/// use time::Time;
///
/// // Exact second: ceil = floor.
/// let noon = Time::from_hms(12, 0, 0).unwrap();
/// assert_eq!(TIMESECS.ceil(Extended::Finite(noon)), 43_200);
/// assert_eq!(TIMESECS.floor(Extended::Finite(noon)), 43_200);
///
/// // Sub-second: ceil rounds up by one, floor truncates.
/// let mid_minute = Time::from_hms_nano(12, 0, 0, 1).unwrap();
/// assert_eq!(TIMESECS.ceil(Extended::Finite(mid_minute)),  43_201);
/// assert_eq!(TIMESECS.floor(Extended::Finite(mid_minute)), 43_200);
///
/// assert_eq!(TIMESECS.inner(43_200), Extended::Finite(noon));
/// ```
pub const TIMESECS: Conn<Extended<Time>, i64> = {
    const SECS_MAX: i64 = 86_400 - 1;

    fn whole_sec(t: Time) -> i64 {
        let (h, m, s, _ns) = t.as_hms_nano();
        h as i64 * 3600 + m as i64 * 60 + s as i64
    }

    fn ceil(t: Extended<Time>) -> i64 {
        match t {
            Extended::NegInf => i64::MIN,
            Extended::Finite(time) => {
                let s = whole_sec(time);
                if time.nanosecond() != 0 { s + 1 } else { s }
            }
            Extended::PosInf => SECS_MAX + 1,
        }
    }

    fn inner(secs: i64) -> Extended<Time> {
        if secs < 0 {
            Extended::NegInf
        } else if secs > SECS_MAX {
            Extended::PosInf
        } else {
            // secs in [0, 86_399]; HMS decomposition is in range.
            let s = secs as u32;
            let h = (s / 3600) as u8;
            let m = ((s / 60) % 60) as u8;
            let sec = (s % 60) as u8;
            match Time::from_hms(h, m, sec) {
                Ok(t) => Extended::Finite(t),
                Err(_) => unreachable!("secs in [0, SECS_MAX] decomposes to valid HMS"),
            }
        }
    }

    fn floor(t: Extended<Time>) -> i64 {
        match t {
            Extended::NegInf => -1,
            Extended::Finite(time) => whole_sec(time),
            Extended::PosInf => i64::MAX,
        }
    }

    Conn::new(ceil, inner, floor)
};

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

    // ── DATEJDAY ────────────────────────────────────────────────
    //
    // Galois-connection laws over `Extended<Date> ↔ i32` Julian
    // days. Roundtrip laws use `arb_jd_in_range` (bounded to the
    // finite Date range) because saturation makes the round-trip
    // non-strict outside `[MIN_JD, MAX_JD]`.

    mod datejday {
        use super::*;
        use crate::property::arb::{arb_extended_date, arb_jd_in_range};
        use time::Month;

        const MIN_JD: i32 = Date::MIN.to_julian_day();
        const MAX_JD: i32 = Date::MAX.to_julian_day();

        // ── Spot checks ─────────────────────────────────────────

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

        // ── Galois law battery ─────────────────────────────────

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
            // `conn::int::U08I16` and the other Extended-source ints
            // — see their test mod for prior precedent.

            #[test]
            fn idempotent(d in arb_extended_date()) {
                prop_assert!(laws::conn_idempotent(&DATEJDAY, d));
            }

            // Round-trip laws hold only on the finite portion of
            // the i32 rung — saturation collapses out-of-range jd
            // to ±Inf, so ceil(inner(b)) ≠ b for those.
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

    // ── TIMENANO ────────────────────────────────────────────────

    mod timenano {
        use super::*;
        use crate::property::arb::{arb_extended_time, arb_ns_in_range};

        const NS_MAX: i64 = 86_400 * 1_000_000_000 - 1;

        // ── Spot checks ─────────────────────────────────────────

        #[test]
        fn midnight_is_zero() {
            assert_eq!(TIMENANO.ceil(Extended::Finite(Time::MIDNIGHT)), 0);
            assert_eq!(TIMENANO.floor(Extended::Finite(Time::MIDNIGHT)), 0);
            assert_eq!(TIMENANO.inner(0), Extended::Finite(Time::MIDNIGHT));
        }

        #[test]
        fn end_of_day() {
            let last = Time::from_hms_nano(23, 59, 59, 999_999_999).unwrap();
            assert_eq!(TIMENANO.ceil(Extended::Finite(last)), NS_MAX);
            assert_eq!(TIMENANO.floor(Extended::Finite(last)), NS_MAX);
            assert_eq!(TIMENANO.inner(NS_MAX), Extended::Finite(last));
        }

        #[test]
        fn noon_round_trip() {
            let noon = Time::from_hms(12, 0, 0).unwrap();
            assert_eq!(TIMENANO.inner(43_200_000_000_000), Extended::Finite(noon));
            assert_eq!(TIMENANO.ceil(Extended::Finite(noon)), 43_200_000_000_000);
        }

        #[test]
        fn saturation_extremes() {
            assert_eq!(TIMENANO.inner(-1), Extended::NegInf);
            assert_eq!(TIMENANO.inner(i64::MIN), Extended::NegInf);
            assert_eq!(TIMENANO.inner(NS_MAX + 1), Extended::PosInf);
            assert_eq!(TIMENANO.inner(i64::MAX), Extended::PosInf);

            assert_eq!(TIMENANO.ceil(Extended::NegInf), i64::MIN);
            assert_eq!(TIMENANO.ceil(Extended::PosInf), NS_MAX + 1);
            assert_eq!(TIMENANO.floor(Extended::NegInf), -1);
            assert_eq!(TIMENANO.floor(Extended::PosInf), i64::MAX);
        }

        // ── Galois law battery ─────────────────────────────────

        proptest! {
            #[test]
            fn galois_l(t in arb_extended_time(), b in any::<i64>()) {
                prop_assert!(laws::conn_galois_l(&TIMENANO, t, b));
            }

            #[test]
            fn galois_r(t in arb_extended_time(), b in any::<i64>()) {
                prop_assert!(laws::conn_galois_r(&TIMENANO, t, b));
            }

            #[test]
            fn closure_l(t in arb_extended_time()) {
                prop_assert!(laws::conn_closure_l(&TIMENANO, t));
            }

            #[test]
            fn closure_r(t in arb_extended_time()) {
                prop_assert!(laws::conn_closure_r(&TIMENANO, t));
            }

            #[test]
            fn kernel_l(b in any::<i64>()) {
                prop_assert!(laws::conn_kernel_l(&TIMENANO, b));
            }

            #[test]
            fn kernel_r(b in any::<i64>()) {
                prop_assert!(laws::conn_kernel_r(&TIMENANO, b));
            }

            #[test]
            fn monotone_l(a in arb_extended_time(), b in arb_extended_time()) {
                prop_assert!(laws::conn_monotone_l(&TIMENANO, a, b));
            }

            #[test]
            fn monotone_r(a in any::<i64>(), b in any::<i64>()) {
                prop_assert!(laws::conn_monotone_r(&TIMENANO, a, b));
            }

            // `floor_le_ceil` not driven — same Extended-source
            // saturation reason as DATEJDAY (see comment there).

            #[test]
            fn idempotent(t in arb_extended_time()) {
                prop_assert!(laws::conn_idempotent(&TIMENANO, t));
            }

            #[test]
            fn roundtrip_ceil(b in arb_ns_in_range()) {
                prop_assert!(laws::conn_roundtrip_ceil(&TIMENANO, b));
            }

            #[test]
            fn roundtrip_floor(b in arb_ns_in_range()) {
                prop_assert!(laws::conn_roundtrip_floor(&TIMENANO, b));
            }
        }
    }

    // ── TIMESECS ────────────────────────────────────────────────

    mod timesecs {
        use super::*;
        use crate::property::arb::{arb_extended_time, arb_secs_in_range};

        // ── Spot checks ─────────────────────────────────────────

        #[test]
        fn midnight_is_zero() {
            assert_eq!(TIMESECS.ceil(Extended::Finite(Time::MIDNIGHT)), 0);
            assert_eq!(TIMESECS.floor(Extended::Finite(Time::MIDNIGHT)), 0);
            assert_eq!(TIMESECS.inner(0), Extended::Finite(Time::MIDNIGHT));
        }

        #[test]
        fn exact_second_ceil_eq_floor() {
            let noon = Time::from_hms(12, 0, 0).unwrap();
            assert_eq!(TIMESECS.ceil(Extended::Finite(noon)), 43_200);
            assert_eq!(TIMESECS.floor(Extended::Finite(noon)), 43_200);
        }

        #[test]
        fn subsec_rounds_up() {
            let one_ns_after_noon = Time::from_hms_nano(12, 0, 0, 1).unwrap();
            assert_eq!(TIMESECS.ceil(Extended::Finite(one_ns_after_noon)), 43_201);
            assert_eq!(TIMESECS.floor(Extended::Finite(one_ns_after_noon)), 43_200);
        }

        #[test]
        fn end_of_day() {
            let last = Time::from_hms_nano(23, 59, 59, 999_999_999).unwrap();
            assert_eq!(TIMESECS.ceil(Extended::Finite(last)), 86_400);
            assert_eq!(TIMESECS.floor(Extended::Finite(last)), 86_399);
        }

        #[test]
        fn saturation_extremes() {
            assert_eq!(TIMESECS.inner(-1), Extended::NegInf);
            assert_eq!(TIMESECS.inner(86_400), Extended::PosInf);
            assert_eq!(TIMESECS.ceil(Extended::NegInf), i64::MIN);
            assert_eq!(TIMESECS.ceil(Extended::PosInf), 86_400);
            assert_eq!(TIMESECS.floor(Extended::NegInf), -1);
            assert_eq!(TIMESECS.floor(Extended::PosInf), i64::MAX);
        }

        // ── Galois law battery ─────────────────────────────────

        proptest! {
            #[test]
            fn galois_l(t in arb_extended_time(), b in any::<i64>()) {
                prop_assert!(laws::conn_galois_l(&TIMESECS, t, b));
            }

            #[test]
            fn galois_r(t in arb_extended_time(), b in any::<i64>()) {
                prop_assert!(laws::conn_galois_r(&TIMESECS, t, b));
            }

            #[test]
            fn closure_l(t in arb_extended_time()) {
                prop_assert!(laws::conn_closure_l(&TIMESECS, t));
            }

            #[test]
            fn closure_r(t in arb_extended_time()) {
                prop_assert!(laws::conn_closure_r(&TIMESECS, t));
            }

            #[test]
            fn kernel_l(b in any::<i64>()) {
                prop_assert!(laws::conn_kernel_l(&TIMESECS, b));
            }

            #[test]
            fn kernel_r(b in any::<i64>()) {
                prop_assert!(laws::conn_kernel_r(&TIMESECS, b));
            }

            #[test]
            fn monotone_l(a in arb_extended_time(), b in arb_extended_time()) {
                prop_assert!(laws::conn_monotone_l(&TIMESECS, a, b));
            }

            #[test]
            fn monotone_r(a in any::<i64>(), b in any::<i64>()) {
                prop_assert!(laws::conn_monotone_r(&TIMESECS, a, b));
            }

            #[test]
            fn idempotent(t in arb_extended_time()) {
                prop_assert!(laws::conn_idempotent(&TIMESECS, t));
            }

            // ulp_bound is meaningful only on the Finite portion —
            // the saturation arms drive `floor`/`ceil` to opposite
            // i64 extremes, which are not "1 ULP" apart.
            #[test]
            fn ulp_bound_finite(t in arb_time()) {
                prop_assert!(laws::conn_ulp_bound(
                    &TIMESECS,
                    Extended::Finite(t),
                    |s| s,
                ));
            }

            #[test]
            fn roundtrip_ceil(b in arb_secs_in_range()) {
                prop_assert!(laws::conn_roundtrip_ceil(&TIMESECS, b));
            }

            #[test]
            fn roundtrip_floor(b in arb_secs_in_range()) {
                prop_assert!(laws::conn_roundtrip_floor(&TIMESECS, b));
            }
        }
    }
}
