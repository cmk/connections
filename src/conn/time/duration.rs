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
//! - [`F064DURN`] / [`F032DURN`] — IEEE float seconds ↔ Duration.
//!   Walks happen on the Duration rung (1ns ULPs); ULP-bounded
//!   correction loops driven by the `def_walk_helpers!` macro
//!   handle the float-precision plateau where multiple Durations
//!   map to the same f-value.

use crate::conn::Conn;
use crate::conn::float::{ExtendedFloat, F032, F064, def_walk_helpers};
use crate::conn::std::i64::decimal::FD09;
use crate::extended::Extended;
use time::Duration;

// ── Duration ULP shift + float widen helpers ─────────────────────
//
// Used by `def_walk_helpers!` to drive the F???DURN bridges: walks
// happen on the Duration rung (1ns increments via `shift_duration`)
// with comparisons in float space (`Duration::as_seconds_f???`).

/// Shift `d` by `n` nanoseconds. Saturates at `Duration::MIN` /
/// `Duration::MAX` so the macro's "if shift didn't move, terminate"
/// guard fires correctly at the boundaries.
pub(crate) fn shift_duration(n: i32, d: Duration) -> Duration {
    let cur_ns = d.whole_nanoseconds();
    let new_ns = cur_ns.saturating_add(n as i128);
    let max_ns = Duration::MAX.whole_nanoseconds();
    let min_ns = Duration::MIN.whole_nanoseconds();
    if new_ns >= max_ns {
        Duration::MAX
    } else if new_ns <= min_ns {
        Duration::MIN
    } else {
        // Truncated division: i128's `/` rounds toward zero. For
        // negative new_ns this places the subsec_nanoseconds
        // coherently with the seconds (both non-positive).
        let secs = (new_ns / 1_000_000_000) as i64;
        let subsec = (new_ns % 1_000_000_000) as i32;
        Duration::new(secs, subsec)
    }
}

#[inline]
fn duration_to_f64(d: Duration) -> f64 {
    d.as_seconds_f64()
}

#[inline]
fn duration_to_f32(d: Duration) -> f32 {
    d.as_seconds_f32()
}

def_walk_helpers!(
    f64_durn_walks,
    f64,
    Duration,
    shift_duration,
    duration_to_f64
);
def_walk_helpers!(
    f32_durn_walks,
    f32,
    Duration,
    shift_duration,
    duration_to_f32
);

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
/// use connections::conn::std::i64::decimal::FD09;
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

/// `F064 → Extended<Duration>` — IEEE binary64 seconds ↔ Duration.
///
/// Walks happen on the Duration rung (1ns ULPs); the float side is
/// the comparison frame. `inner(Finite(d))` widens via
/// `Duration::as_seconds_f64()`. The walk-correction loops emitted
/// by `def_walk_helpers!` handle the f64-precision plateau where
/// multiple Durations map to the same f64 (which begins around
/// |Duration| > 2⁵³ ns ≈ 104 days).
///
/// Saturation arms:
/// - `ceil(Bot)` = `NegInf`, `floor(Bot)` = `NegInf` (Bot is
///   synthetic-below-everything).
/// - `ceil(Top)` = `PosInf`, `floor(Top)` = `PosInf`.
/// - `ceil(Extend(NaN))` = `PosInf`, `floor(Extend(NaN))` = `NegInf`
///   (under N5: NaN ≤ Top, Bot ≤ NaN, NaN incomparable with finite).
/// - `ceil(Extend(+∞))` = `PosInf`, `floor(Extend(+∞))` =
///   `Finite(Duration::MAX)`. Symmetric for `-∞`. The asymmetry
///   between `ceil` and `floor` at `Extend(±∞)` is the same shape
///   as every Extended-source Conn in this module (DATEJDAY,
///   TIMENANO, DURNSECS, …): `ExtendedFloat<f64>` carries a
///   synthetic `Top` strictly above `Extend(f64::INFINITY)`, which
///   forces `inner(PosInf) = Top` to satisfy Galois at the
///   `(Top, PosInf)` input pair.
///
/// # Examples
///
/// ```rust
/// use connections::conn::time::F064DURN;
/// use connections::conn::float::ExtendedFloat;
/// use connections::extended::Extended;
/// use time::Duration;
///
/// // 0.5 seconds round-trips exactly.
/// let half = ExtendedFloat::Extend(0.5_f64);
/// assert_eq!(F064DURN.ceil(half),  Extended::Finite(Duration::milliseconds(500)));
/// assert_eq!(F064DURN.floor(half), Extended::Finite(Duration::milliseconds(500)));
/// assert_eq!(F064DURN.inner(Extended::Finite(Duration::milliseconds(500))),
///            ExtendedFloat::Extend(0.5));
///
/// // NaN saturates ceil to PosInf, floor to NegInf.
/// assert_eq!(F064DURN.ceil(ExtendedFloat::Extend(f64::NAN)),  Extended::PosInf);
/// assert_eq!(F064DURN.floor(ExtendedFloat::Extend(f64::NAN)), Extended::NegInf);
/// ```
pub const F064DURN: Conn<F064, Extended<Duration>> = {
    fn ceil(x: F064) -> Extended<Duration> {
        let v = match x {
            ExtendedFloat::Bot => return Extended::NegInf,
            ExtendedFloat::Top => return Extended::PosInf,
            ExtendedFloat::Extend(v) => v,
        };
        if v.is_nan() {
            return Extended::PosInf;
        }
        if v == f64::INFINITY {
            return Extended::PosInf;
        }
        if v == f64::NEG_INFINITY {
            return Extended::Finite(Duration::MIN);
        }
        let max_secs = Duration::MAX.as_seconds_f64();
        let min_secs = Duration::MIN.as_seconds_f64();
        if v > max_secs {
            return Extended::PosInf;
        }
        if v < min_secs {
            return Extended::Finite(Duration::MIN);
        }
        let est = Duration::saturating_seconds_f64(v);
        let est_widen = est.as_seconds_f64();
        let (z, _) = if est_widen >= v {
            f64_durn_walks::descend_to_ceil(est, v)
        } else {
            f64_durn_walks::ascend_to_ceil(est, v)
        };
        Extended::Finite(z)
    }

    fn inner(d: Extended<Duration>) -> F064 {
        match d {
            Extended::NegInf => ExtendedFloat::Bot,
            Extended::Finite(dur) => ExtendedFloat::Extend(dur.as_seconds_f64()),
            Extended::PosInf => ExtendedFloat::Top,
        }
    }

    fn floor(x: F064) -> Extended<Duration> {
        let v = match x {
            ExtendedFloat::Bot => return Extended::NegInf,
            ExtendedFloat::Top => return Extended::PosInf,
            ExtendedFloat::Extend(v) => v,
        };
        if v.is_nan() {
            return Extended::NegInf;
        }
        if v == f64::INFINITY {
            return Extended::Finite(Duration::MAX);
        }
        if v == f64::NEG_INFINITY {
            return Extended::NegInf;
        }
        let max_secs = Duration::MAX.as_seconds_f64();
        let min_secs = Duration::MIN.as_seconds_f64();
        if v > max_secs {
            return Extended::Finite(Duration::MAX);
        }
        if v < min_secs {
            return Extended::NegInf;
        }
        let est = Duration::saturating_seconds_f64(v);
        let est_widen = est.as_seconds_f64();
        let (z, _) = if est_widen <= v {
            f64_durn_walks::ascend_to_floor(est, v)
        } else {
            f64_durn_walks::descend_to_floor(est, v)
        };
        Extended::Finite(z)
    }

    Conn::new(ceil, inner, floor)
};

/// `F032 → Extended<Duration>` — IEEE binary32 seconds ↔ Duration.
///
/// Mirrors [`F064DURN`]'s shape with `f32` precision. The f32 plateau
/// (range of Durations mapping to the same `f32`) is much wider than
/// f64's: at magnitude ~1 s it is ~120 ns; at magnitude ~10³ s it is
/// ~10⁵ ns. Proptest strategies bound the float-side finite slot to
/// `|x| ≤ 10` (see [`crate::property::arb::arb_f32_bounded`]) so the
/// per-call ULP-walk budget stays small.
///
/// # Examples
///
/// ```rust
/// use connections::conn::time::F032DURN;
/// use connections::conn::float::ExtendedFloat;
/// use connections::extended::Extended;
/// use time::Duration;
///
/// // 1.0 s lies in an f32 plateau ~120 ns wide. ceil and floor return
/// // the bottom and top of that plateau respectively; both round-trip
/// // to `1.0_f32` via `inner` and bracket `Duration::seconds(1)`.
/// let one = ExtendedFloat::Extend(1.0_f32);
/// let exact = Duration::seconds(1);
/// if let (Extended::Finite(c), Extended::Finite(f)) =
///     (F032DURN.ceil(one), F032DURN.floor(one))
/// {
///     assert!(c <= exact && exact <= f);
///     assert_eq!(c.as_seconds_f32(), 1.0_f32);
///     assert_eq!(f.as_seconds_f32(), 1.0_f32);
/// }
/// ```
pub const F032DURN: Conn<F032, Extended<Duration>> = {
    fn ceil(x: F032) -> Extended<Duration> {
        let v = match x {
            ExtendedFloat::Bot => return Extended::NegInf,
            ExtendedFloat::Top => return Extended::PosInf,
            ExtendedFloat::Extend(v) => v,
        };
        if v.is_nan() {
            return Extended::PosInf;
        }
        if v == f32::INFINITY {
            return Extended::PosInf;
        }
        if v == f32::NEG_INFINITY {
            return Extended::Finite(Duration::MIN);
        }
        let max_secs = Duration::MAX.as_seconds_f32();
        let min_secs = Duration::MIN.as_seconds_f32();
        if v > max_secs {
            return Extended::PosInf;
        }
        if v < min_secs {
            return Extended::Finite(Duration::MIN);
        }
        let est = Duration::saturating_seconds_f32(v);
        let est_widen = est.as_seconds_f32();
        let (z, _) = if est_widen >= v {
            f32_durn_walks::descend_to_ceil(est, v)
        } else {
            f32_durn_walks::ascend_to_ceil(est, v)
        };
        Extended::Finite(z)
    }

    fn inner(d: Extended<Duration>) -> F032 {
        match d {
            Extended::NegInf => ExtendedFloat::Bot,
            Extended::Finite(dur) => ExtendedFloat::Extend(dur.as_seconds_f32()),
            Extended::PosInf => ExtendedFloat::Top,
        }
    }

    fn floor(x: F032) -> Extended<Duration> {
        let v = match x {
            ExtendedFloat::Bot => return Extended::NegInf,
            ExtendedFloat::Top => return Extended::PosInf,
            ExtendedFloat::Extend(v) => v,
        };
        if v.is_nan() {
            return Extended::NegInf;
        }
        if v == f32::INFINITY {
            return Extended::Finite(Duration::MAX);
        }
        if v == f32::NEG_INFINITY {
            return Extended::NegInf;
        }
        let max_secs = Duration::MAX.as_seconds_f32();
        let min_secs = Duration::MIN.as_seconds_f32();
        if v > max_secs {
            return Extended::Finite(Duration::MAX);
        }
        if v < min_secs {
            return Extended::NegInf;
        }
        let est = Duration::saturating_seconds_f32(v);
        let est_widen = est.as_seconds_f32();
        let (z, _) = if est_widen <= v {
            f32_durn_walks::ascend_to_floor(est, v)
        } else {
            f32_durn_walks::descend_to_floor(est, v)
        };
        Extended::Finite(z)
    }

    Conn::new(ceil, inner, floor)
};

#[cfg(test)]
mod float_durn_tests {
    use super::*;
    use crate::property::arb::{
        arb_extended_duration_bounded_f32, arb_extended_duration_bounded_f64, extended_float_f32,
        extended_float_f64,
    };
    use crate::property::laws;
    use proptest::prelude::*;

    // ── F064DURN spot checks ────────────────────────────────────

    #[test]
    fn f64_zero() {
        let zero = ExtendedFloat::Extend(0.0_f64);
        assert_eq!(F064DURN.ceil(zero), Extended::Finite(Duration::ZERO));
        assert_eq!(F064DURN.floor(zero), Extended::Finite(Duration::ZERO));
        assert_eq!(F064DURN.inner(Extended::Finite(Duration::ZERO)), zero);
    }

    #[test]
    fn f64_half_second() {
        // 0.5 s is exactly representable in f64 and Duration.
        let half = ExtendedFloat::Extend(0.5_f64);
        let half_d = Duration::milliseconds(500);
        assert_eq!(F064DURN.ceil(half), Extended::Finite(half_d));
        assert_eq!(F064DURN.floor(half), Extended::Finite(half_d));
        assert_eq!(F064DURN.inner(Extended::Finite(half_d)), half);
    }

    #[test]
    fn f64_nan_arms() {
        let nan = ExtendedFloat::Extend(f64::NAN);
        assert_eq!(F064DURN.ceil(nan), Extended::PosInf);
        assert_eq!(F064DURN.floor(nan), Extended::NegInf);
    }

    #[test]
    fn f64_infinity_arms() {
        let pos_inf = ExtendedFloat::Extend(f64::INFINITY);
        assert_eq!(F064DURN.ceil(pos_inf), Extended::PosInf);
        assert_eq!(F064DURN.floor(pos_inf), Extended::Finite(Duration::MAX));

        let neg_inf = ExtendedFloat::Extend(f64::NEG_INFINITY);
        assert_eq!(F064DURN.ceil(neg_inf), Extended::Finite(Duration::MIN));
        assert_eq!(F064DURN.floor(neg_inf), Extended::NegInf);
    }

    #[test]
    fn f64_bot_top_arms() {
        assert_eq!(F064DURN.ceil(ExtendedFloat::Bot), Extended::NegInf);
        assert_eq!(F064DURN.floor(ExtendedFloat::Bot), Extended::NegInf);
        assert_eq!(F064DURN.ceil(ExtendedFloat::Top), Extended::PosInf);
        assert_eq!(F064DURN.floor(ExtendedFloat::Top), Extended::PosInf);
        assert_eq!(F064DURN.inner(Extended::NegInf), ExtendedFloat::Bot);
        assert_eq!(F064DURN.inner(Extended::PosInf), ExtendedFloat::Top);
    }

    // ── F032DURN spot checks ────────────────────────────────────

    #[test]
    fn f32_zero() {
        let zero = ExtendedFloat::Extend(0.0_f32);
        assert_eq!(F032DURN.ceil(zero), Extended::Finite(Duration::ZERO));
        assert_eq!(F032DURN.floor(zero), Extended::Finite(Duration::ZERO));
        assert_eq!(F032DURN.inner(Extended::Finite(Duration::ZERO)), zero);
    }

    #[test]
    fn f32_one_second_brackets_plateau() {
        // f32 ULP at 1.0 ≈ 1.19e-7 s, so multiple Durations near
        // `Duration::seconds(1)` widen to exactly `1.0_f32`. ceil
        // returns the bottom of that plateau, floor the top — both
        // round-trip through `inner` to `1.0_f32`, and both bracket
        // `Duration::seconds(1)`.
        let one = ExtendedFloat::Extend(1.0_f32);
        let exact = Duration::seconds(1);
        let c = F032DURN.ceil(one);
        let f = F032DURN.floor(one);
        assert!(matches!(c, Extended::Finite(_)));
        assert!(matches!(f, Extended::Finite(_)));
        if let (Extended::Finite(cd), Extended::Finite(fd)) = (c, f) {
            assert!(cd <= exact && exact <= fd, "ceil={cd:?} floor={fd:?}");
            assert_eq!(cd.as_seconds_f32(), 1.0_f32);
            assert_eq!(fd.as_seconds_f32(), 1.0_f32);
        }
    }

    #[test]
    fn f32_nan_arms() {
        let nan = ExtendedFloat::Extend(f32::NAN);
        assert_eq!(F032DURN.ceil(nan), Extended::PosInf);
        assert_eq!(F032DURN.floor(nan), Extended::NegInf);
    }

    #[test]
    fn f32_infinity_arms() {
        let pos_inf = ExtendedFloat::Extend(f32::INFINITY);
        assert_eq!(F032DURN.ceil(pos_inf), Extended::PosInf);
        assert_eq!(F032DURN.floor(pos_inf), Extended::Finite(Duration::MAX));

        let neg_inf = ExtendedFloat::Extend(f32::NEG_INFINITY);
        assert_eq!(F032DURN.ceil(neg_inf), Extended::Finite(Duration::MIN));
        assert_eq!(F032DURN.floor(neg_inf), Extended::NegInf);
    }

    #[test]
    fn f32_bot_top_arms() {
        assert_eq!(F032DURN.ceil(ExtendedFloat::Bot), Extended::NegInf);
        assert_eq!(F032DURN.floor(ExtendedFloat::Bot), Extended::NegInf);
        assert_eq!(F032DURN.ceil(ExtendedFloat::Top), Extended::PosInf);
        assert_eq!(F032DURN.floor(ExtendedFloat::Top), Extended::PosInf);
        assert_eq!(F032DURN.inner(Extended::NegInf), ExtendedFloat::Bot);
        assert_eq!(F032DURN.inner(Extended::PosInf), ExtendedFloat::Top);
    }

    // ── Galois law battery — F064DURN ──────────────────────────
    //
    // The float-side strategies bound `Extend(_)` to `|x| ≤ 1e9` (see
    // `arb_f??_bounded`) so the per-call ULP-walk budget stays small:
    // at |x| ≤ 1e9 s the f64 ULP is ≈ 1.2e-7 s ≈ 119 ns, so each walk
    // terminates in ≤ ~120 steps.

    proptest! {
        #![proptest_config(ProptestConfig {
            cases: 64,
            max_shrink_iters: 200,
            .. ProptestConfig::default()
        })]

        #[test]
        fn f64_galois_l(a in extended_float_f64(), b in arb_extended_duration_bounded_f64()) {
            prop_assert!(laws::conn_galois_l(&F064DURN, a, b));
        }

        #[test]
        fn f64_galois_r(a in extended_float_f64(), b in arb_extended_duration_bounded_f64()) {
            prop_assert!(laws::conn_galois_r(&F064DURN, a, b));
        }

        #[test]
        fn f64_closure_l(a in extended_float_f64()) {
            prop_assert!(laws::conn_closure_l(&F064DURN, a));
        }

        #[test]
        fn f64_closure_r(a in extended_float_f64()) {
            prop_assert!(laws::conn_closure_r(&F064DURN, a));
        }

        #[test]
        fn f64_kernel_l(b in arb_extended_duration_bounded_f64()) {
            prop_assert!(laws::conn_kernel_l(&F064DURN, b));
        }

        #[test]
        fn f64_kernel_r(b in arb_extended_duration_bounded_f64()) {
            prop_assert!(laws::conn_kernel_r(&F064DURN, b));
        }

        #[test]
        fn f64_monotone_l(a1 in extended_float_f64(), a2 in extended_float_f64()) {
            prop_assert!(laws::conn_monotone_l(&F064DURN, a1, a2));
        }

        #[test]
        fn f64_monotone_r(b1 in arb_extended_duration_bounded_f64(), b2 in arb_extended_duration_bounded_f64()) {
            prop_assert!(laws::conn_monotone_r(&F064DURN, b1, b2));
        }

        #[test]
        fn f64_idempotent(a in extended_float_f64()) {
            prop_assert!(laws::conn_idempotent(&F064DURN, a));
        }
    }

    // ── Galois law battery — F032DURN ──────────────────────────

    proptest! {
        #![proptest_config(ProptestConfig {
            cases: 64,
            max_shrink_iters: 200,
            .. ProptestConfig::default()
        })]

        #[test]
        fn f32_galois_l(a in extended_float_f32(), b in arb_extended_duration_bounded_f32()) {
            prop_assert!(laws::conn_galois_l(&F032DURN, a, b));
        }

        #[test]
        fn f32_galois_r(a in extended_float_f32(), b in arb_extended_duration_bounded_f32()) {
            prop_assert!(laws::conn_galois_r(&F032DURN, a, b));
        }

        #[test]
        fn f32_closure_l(a in extended_float_f32()) {
            prop_assert!(laws::conn_closure_l(&F032DURN, a));
        }

        #[test]
        fn f32_closure_r(a in extended_float_f32()) {
            prop_assert!(laws::conn_closure_r(&F032DURN, a));
        }

        #[test]
        fn f32_kernel_l(b in arb_extended_duration_bounded_f32()) {
            prop_assert!(laws::conn_kernel_l(&F032DURN, b));
        }

        #[test]
        fn f32_kernel_r(b in arb_extended_duration_bounded_f32()) {
            prop_assert!(laws::conn_kernel_r(&F032DURN, b));
        }

        #[test]
        fn f32_monotone_l(a1 in extended_float_f32(), a2 in extended_float_f32()) {
            prop_assert!(laws::conn_monotone_l(&F032DURN, a1, a2));
        }

        #[test]
        fn f32_monotone_r(b1 in arb_extended_duration_bounded_f32(), b2 in arb_extended_duration_bounded_f32()) {
            prop_assert!(laws::conn_monotone_r(&F032DURN, b1, b2));
        }

        #[test]
        fn f32_idempotent(a in extended_float_f32()) {
            prop_assert!(laws::conn_idempotent(&F032DURN, a));
        }
    }
}
