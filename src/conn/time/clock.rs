//! Clock-`Time` connections.
//!
//! Hosts the two `Extended<Time>`-source conns:
//!
//! - [`TIMENANO`] — exact bijection on nanoseconds since midnight.
//! - [`TIMESECS`] — whole seconds since midnight, with sub-second
//!   rounding.

use crate::conn::Conn;
use crate::extended::Extended;
use time::Time;

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
    use crate::property::arb::{arb_extended_time, arb_ns_in_range, arb_secs_in_range, arb_time};
    use crate::property::laws;
    use proptest::prelude::*;

    // ── Preorder laws on `Time` ─────────────────────────────────

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
                prop_assert!(laws::lattice_antisymmetric(&x, &y));
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

    // ── TIMENANO ────────────────────────────────────────────────

    mod timenano {
        use super::*;

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
