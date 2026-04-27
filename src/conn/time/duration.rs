//! Signed-`Duration` connections.
//!
//! Hosts:
//! - [`DURNSECS`] — signed time-span ↔ whole seconds via an
//!   `Extended<i64>` rung (the rung is extended because ceil at
//!   `Duration::MAX` and floor at `Duration::MIN` overflow `i64`).
//! - [`DURNFD09`] — signed time-span ↔ nanosecond fixed-point.
//!   `Duration` is exact at nanosecond resolution, but `Duration`'s
//!   range exceeds `FD09`'s (i64 nanos ≈ ±292 years), so
//!   out-of-`FD09` Durations saturate to `Extended::NegInf` /
//!   `PosInf` on the rung side.

use crate::conn::Conn;
use crate::conn::fixed::decimal::FD09;
use crate::extended::Extended;
use time::Duration;

/// `Duration → Extended<i64>` — signed time span ↔ whole seconds.
///
/// `Duration` already covers the full `i64`-second range, so the
/// rung is `Extended<i64>` rather than plain `i64`: ceiling
/// `Duration::MAX` (which has a positive sub-second part) needs
/// "i64::MAX + 1", and flooring `Duration::MIN` (negative sub-second)
/// needs "i64::MIN − 1" — the saturation arms.
///
/// On the interior:
/// - `floor(d)` truncates toward zero-of-subsecond:
///   `whole_seconds(d) − (1 if subsec_nanoseconds(d) < 0 else 0)`.
/// - `ceil(d)` rounds away from the same:
///   `whole_seconds(d) + (1 if subsec_nanoseconds(d) > 0 else 0)`.
/// - `inner(Finite(s))` = `Duration::seconds(s)` (exact embedding).
///
/// Saturation arms (`Extended::NegInf` / `Extended::PosInf`) handle
/// `Duration::MIN` / `Duration::MAX` and the i64 overflow at the
/// signed-rounding edges. `inner(NegInf) = Duration::MIN` and
/// `inner(PosInf) = Duration::MAX` (both saturating).
///
/// # Examples
///
/// ```rust
/// use connections::conn::time::DURNSECS;
/// use connections::extended::Extended;
/// use time::Duration;
///
/// let half = Duration::seconds(5) + Duration::nanoseconds(1);
/// assert_eq!(DURNSECS.ceil(half),  Extended::Finite(6));
/// assert_eq!(DURNSECS.floor(half), Extended::Finite(5));
///
/// // Negative sub-second: ceil rounds toward zero, floor away.
/// let neg = Duration::seconds(-5) - Duration::nanoseconds(1);
/// assert_eq!(DURNSECS.ceil(neg),  Extended::Finite(-5));
/// assert_eq!(DURNSECS.floor(neg), Extended::Finite(-6));
///
/// assert_eq!(DURNSECS.inner(Extended::Finite(42)), Duration::seconds(42));
/// ```
pub const DURNSECS: Conn<Duration, Extended<i64>> = {
    fn ceil(d: Duration) -> Extended<i64> {
        if d.eq(&Duration::MIN) {
            // Forced by Galois: inner(NegInf) saturates to
            // Duration::MIN, so the smallest b with d ≤ inner(b) is
            // NegInf.
            return Extended::NegInf;
        }
        let w = d.whole_seconds();
        let n = d.subsec_nanoseconds();
        if n > 0 {
            match w.checked_add(1) {
                Some(s) => Extended::Finite(s),
                None => Extended::PosInf,
            }
        } else {
            Extended::Finite(w)
        }
    }

    fn inner(b: Extended<i64>) -> Duration {
        match b {
            Extended::NegInf => Duration::MIN,
            Extended::Finite(s) => Duration::seconds(s),
            Extended::PosInf => Duration::MAX,
        }
    }

    fn floor(d: Duration) -> Extended<i64> {
        if d.eq(&Duration::MAX) {
            // Galois dual of the ceil(MIN) case.
            return Extended::PosInf;
        }
        let w = d.whole_seconds();
        let n = d.subsec_nanoseconds();
        if n < 0 {
            match w.checked_sub(1) {
                Some(s) => Extended::Finite(s),
                None => Extended::NegInf,
            }
        } else {
            Extended::Finite(w)
        }
    }

    Conn::new(ceil, inner, floor)
};

#[cfg(test)]
mod tests {
    use super::*;
    use crate::property::arb::{arb_duration, arb_extended_i64};
    use crate::property::laws;
    use proptest::prelude::*;

    // ── Preorder laws on `Duration` ─────────────────────────────

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
                prop_assert!(laws::lattice_antisymmetric(&x, &y));
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

    // ── DURNSECS spot checks ────────────────────────────────────

    #[test]
    fn zero_is_zero() {
        assert_eq!(DURNSECS.ceil(Duration::ZERO), Extended::Finite(0));
        assert_eq!(DURNSECS.floor(Duration::ZERO), Extended::Finite(0));
        assert_eq!(DURNSECS.inner(Extended::Finite(0)), Duration::ZERO);
    }

    #[test]
    fn positive_subsec_rounds_up() {
        let d = Duration::seconds(5) + Duration::nanoseconds(1);
        assert_eq!(DURNSECS.ceil(d), Extended::Finite(6));
        assert_eq!(DURNSECS.floor(d), Extended::Finite(5));
    }

    #[test]
    fn negative_subsec_rounds_toward_zero() {
        // -5.000_000_001 s → ceil = -5, floor = -6
        let d = Duration::seconds(-5) - Duration::nanoseconds(1);
        assert_eq!(DURNSECS.ceil(d), Extended::Finite(-5));
        assert_eq!(DURNSECS.floor(d), Extended::Finite(-6));
    }

    #[test]
    fn extreme_durations() {
        assert_eq!(DURNSECS.ceil(Duration::MAX), Extended::PosInf);
        assert_eq!(DURNSECS.floor(Duration::MAX), Extended::PosInf);
        assert_eq!(DURNSECS.ceil(Duration::MIN), Extended::NegInf);
        assert_eq!(DURNSECS.floor(Duration::MIN), Extended::NegInf);
    }

    #[test]
    fn inner_saturates_extended() {
        assert_eq!(DURNSECS.inner(Extended::NegInf), Duration::MIN);
        assert_eq!(DURNSECS.inner(Extended::PosInf), Duration::MAX);
    }

    // ── DURNSECS Galois law battery ─────────────────────────────

    proptest! {
        #[test]
        fn galois_l(d in arb_duration(), b in arb_extended_i64()) {
            prop_assert!(laws::conn_galois_l(&DURNSECS, d, b));
        }

        #[test]
        fn galois_r(d in arb_duration(), b in arb_extended_i64()) {
            prop_assert!(laws::conn_galois_r(&DURNSECS, d, b));
        }

        #[test]
        fn closure_l(d in arb_duration()) {
            prop_assert!(laws::conn_closure_l(&DURNSECS, d));
        }

        #[test]
        fn closure_r(d in arb_duration()) {
            prop_assert!(laws::conn_closure_r(&DURNSECS, d));
        }

        #[test]
        fn kernel_l(b in arb_extended_i64()) {
            prop_assert!(laws::conn_kernel_l(&DURNSECS, b));
        }

        #[test]
        fn kernel_r(b in arb_extended_i64()) {
            prop_assert!(laws::conn_kernel_r(&DURNSECS, b));
        }

        #[test]
        fn monotone_l(a in arb_duration(), b in arb_duration()) {
            prop_assert!(laws::conn_monotone_l(&DURNSECS, a, b));
        }

        #[test]
        fn monotone_r(a in arb_extended_i64(), b in arb_extended_i64()) {
            prop_assert!(laws::conn_monotone_r(&DURNSECS, a, b));
        }

        #[test]
        fn idempotent(d in arb_duration()) {
            prop_assert!(laws::conn_idempotent(&DURNSECS, d));
        }

        // ulp_bound: extractor flattens NegInf→i64::MIN,
        // PosInf→i64::MAX. At Duration::MAX/MIN both ceil and
        // floor saturate to the same sentinel (diff = 0); on
        // the interior diff ∈ {0, 1}.
        #[test]
        fn ulp_bound(d in arb_duration()) {
            let extractor = |b: Extended<i64>| -> i64 {
                match b {
                    Extended::NegInf => i64::MIN,
                    Extended::Finite(s) => s,
                    Extended::PosInf => i64::MAX,
                }
            };
            prop_assert!(laws::conn_ulp_bound(&DURNSECS, d, extractor));
        }

        // Roundtrip on Finite rung values: inner is exact for
        // any i64 second, and ceil/floor of the result is
        // identity.
        #[test]
        fn roundtrip_ceil(s in any::<i64>()) {
            prop_assert!(laws::conn_roundtrip_ceil(&DURNSECS, Extended::Finite(s)));
        }

        #[test]
        fn roundtrip_floor(s in any::<i64>()) {
            prop_assert!(laws::conn_roundtrip_floor(&DURNSECS, Extended::Finite(s)));
        }
    }
}

/// `Duration → Extended<FD09>` — signed time-span ↔ nanosecond
/// fixed-point.
///
/// `Duration`'s native sub-second resolution is the nanosecond, so
/// the `Finite` portion is an exact bijection with `FD09` (which
/// stores i64 nanoseconds). However `Duration`'s range
/// (`±i64` seconds + `±10⁹` nanos ≈ ±2.9 × 10²⁰ s) far exceeds
/// `FD09`'s (`±i64` nanos ≈ ±292 years), so Durations outside the
/// FD09-representable window saturate to `Extended::NegInf` /
/// `PosInf` on the rung. The asymmetric saturation arms at
/// `Duration::MIN`/`MAX` are forced by the Galois adjoint laws,
/// matching `DURNSECS`'s pattern.
///
/// On the interior:
/// - `inner(Finite(fd09))` = `Duration::nanoseconds(fd09.0)`
///   (always representable since `Duration` is wider).
/// - `ceil(d)` and `floor(d)` agree on Durations whose
///   `whole_nanoseconds()` fits `i64`; both return
///   `Finite(FD09(nanos))`.
///
/// # Examples
///
/// ```rust
/// use connections::conn::time::DURNFD09;
/// use connections::conn::fixed::decimal::FD09;
/// use connections::extended::Extended;
/// use time::Duration;
///
/// // 1 second exactly = 10⁹ nanoseconds.
/// assert_eq!(DURNFD09.ceil(Duration::seconds(1)), Extended::Finite(FD09(1_000_000_000)));
/// assert_eq!(DURNFD09.floor(Duration::seconds(1)), Extended::Finite(FD09(1_000_000_000)));
/// assert_eq!(DURNFD09.inner(Extended::Finite(FD09(1_000_000_000))), Duration::seconds(1));
///
/// // Out-of-range Duration saturates.
/// assert_eq!(DURNFD09.ceil(Duration::MAX), Extended::PosInf);
/// assert_eq!(DURNFD09.floor(Duration::MIN), Extended::NegInf);
/// ```
pub const DURNFD09: Conn<Duration, Extended<FD09>> = {
    fn ceil(d: Duration) -> Extended<FD09> {
        if d.eq(&Duration::MIN) {
            // Galois-forced: inner(NegInf) saturates to Duration::MIN,
            // so the smallest b with d ≤ inner(b) is NegInf itself.
            return Extended::NegInf;
        }
        let nanos = d.whole_nanoseconds();
        if nanos > i64::MAX as i128 {
            // d strictly exceeds FD09::MAX's Duration; ceil walks up
            // past the finite range, lands on PosInf.
            Extended::PosInf
        } else if nanos < i64::MIN as i128 {
            // d below FD09::MIN's Duration but above Duration::MIN —
            // ceil rounds back toward FD09::MIN since Finite(FD09::MIN)
            // is the smallest finite rung whose `inner` ≥ d.
            Extended::Finite(FD09(i64::MIN))
        } else {
            Extended::Finite(FD09(nanos as i64))
        }
    }

    fn inner(b: Extended<FD09>) -> Duration {
        match b {
            Extended::NegInf => Duration::MIN,
            Extended::Finite(fd) => Duration::nanoseconds(fd.0),
            Extended::PosInf => Duration::MAX,
        }
    }

    fn floor(d: Duration) -> Extended<FD09> {
        if d.eq(&Duration::MAX) {
            return Extended::PosInf;
        }
        let nanos = d.whole_nanoseconds();
        if nanos < i64::MIN as i128 {
            Extended::NegInf
        } else if nanos > i64::MAX as i128 {
            Extended::Finite(FD09(i64::MAX))
        } else {
            Extended::Finite(FD09(nanos as i64))
        }
    }

    Conn::new(ceil, inner, floor)
};

#[cfg(test)]
mod fd09_tests {
    use super::*;
    use crate::property::arb::{arb_duration, extended_fd09};
    use crate::property::laws;
    use proptest::prelude::*;

    // ── DURNFD09 spot checks ────────────────────────────────────

    #[test]
    fn one_second() {
        let d = Duration::seconds(1);
        assert_eq!(DURNFD09.ceil(d), Extended::Finite(FD09(1_000_000_000)));
        assert_eq!(DURNFD09.floor(d), Extended::Finite(FD09(1_000_000_000)));
        assert_eq!(DURNFD09.inner(Extended::Finite(FD09(1_000_000_000))), d);
    }

    #[test]
    fn one_nanosecond() {
        let d = Duration::nanoseconds(1);
        assert_eq!(DURNFD09.ceil(d), Extended::Finite(FD09(1)));
        assert_eq!(DURNFD09.floor(d), Extended::Finite(FD09(1)));
        assert_eq!(DURNFD09.inner(Extended::Finite(FD09(1))), d);
    }

    #[test]
    fn zero() {
        assert_eq!(DURNFD09.ceil(Duration::ZERO), Extended::Finite(FD09(0)));
        assert_eq!(DURNFD09.floor(Duration::ZERO), Extended::Finite(FD09(0)));
        assert_eq!(DURNFD09.inner(Extended::Finite(FD09(0))), Duration::ZERO);
    }

    #[test]
    fn fd09_extremes_round_trip() {
        // FD09(i64::MAX) ↔ Duration::nanoseconds(i64::MAX).
        let d_max_fd09 = Duration::nanoseconds(i64::MAX);
        assert_eq!(DURNFD09.ceil(d_max_fd09), Extended::Finite(FD09(i64::MAX)));
        assert_eq!(DURNFD09.floor(d_max_fd09), Extended::Finite(FD09(i64::MAX)));
        assert_eq!(DURNFD09.inner(Extended::Finite(FD09(i64::MAX))), d_max_fd09);

        let d_min_fd09 = Duration::nanoseconds(i64::MIN);
        assert_eq!(DURNFD09.ceil(d_min_fd09), Extended::Finite(FD09(i64::MIN)));
        assert_eq!(DURNFD09.floor(d_min_fd09), Extended::Finite(FD09(i64::MIN)));
        assert_eq!(DURNFD09.inner(Extended::Finite(FD09(i64::MIN))), d_min_fd09);
    }

    #[test]
    fn duration_extremes_saturate() {
        assert_eq!(DURNFD09.ceil(Duration::MAX), Extended::PosInf);
        assert_eq!(DURNFD09.floor(Duration::MAX), Extended::PosInf);
        assert_eq!(DURNFD09.ceil(Duration::MIN), Extended::NegInf);
        assert_eq!(DURNFD09.floor(Duration::MIN), Extended::NegInf);
        assert_eq!(DURNFD09.inner(Extended::NegInf), Duration::MIN);
        assert_eq!(DURNFD09.inner(Extended::PosInf), Duration::MAX);
    }

    #[test]
    fn just_past_fd09_max() {
        // d is one nanosecond past Duration::nanoseconds(i64::MAX),
        // so its whole_nanoseconds = i64::MAX + 1 (overflows i64).
        let d = Duration::nanoseconds(i64::MAX) + Duration::nanoseconds(1);
        assert_eq!(DURNFD09.ceil(d), Extended::PosInf);
        assert_eq!(DURNFD09.floor(d), Extended::Finite(FD09(i64::MAX)));
    }

    // ── Galois law battery ─────────────────────────────────────

    proptest! {
        #[test]
        fn galois_l(d in arb_duration(), b in extended_fd09()) {
            prop_assert!(laws::conn_galois_l(&DURNFD09, d, b));
        }

        #[test]
        fn galois_r(d in arb_duration(), b in extended_fd09()) {
            prop_assert!(laws::conn_galois_r(&DURNFD09, d, b));
        }

        #[test]
        fn closure_l(d in arb_duration()) {
            prop_assert!(laws::conn_closure_l(&DURNFD09, d));
        }

        #[test]
        fn closure_r(d in arb_duration()) {
            prop_assert!(laws::conn_closure_r(&DURNFD09, d));
        }

        #[test]
        fn kernel_l(b in extended_fd09()) {
            prop_assert!(laws::conn_kernel_l(&DURNFD09, b));
        }

        #[test]
        fn kernel_r(b in extended_fd09()) {
            prop_assert!(laws::conn_kernel_r(&DURNFD09, b));
        }

        #[test]
        fn monotone_l(a in arb_duration(), b in arb_duration()) {
            prop_assert!(laws::conn_monotone_l(&DURNFD09, a, b));
        }

        #[test]
        fn monotone_r(a in extended_fd09(), b in extended_fd09()) {
            prop_assert!(laws::conn_monotone_r(&DURNFD09, a, b));
        }

        #[test]
        fn idempotent(d in arb_duration()) {
            prop_assert!(laws::conn_idempotent(&DURNFD09, d));
        }

        // Round-trip on Finite rung values inside FD09's i64 range.
        #[test]
        fn roundtrip_ceil(n in any::<i64>()) {
            prop_assert!(laws::conn_roundtrip_ceil(&DURNFD09, Extended::Finite(FD09(n))));
        }

        #[test]
        fn roundtrip_floor(n in any::<i64>()) {
            prop_assert!(laws::conn_roundtrip_floor(&DURNFD09, Extended::Finite(FD09(n))));
        }
    }
}
