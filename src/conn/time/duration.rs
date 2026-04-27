//! Signed-`Duration` connections.
//!
//! Hosts [`DURNSECS`] — signed time-span ↔ whole seconds via an
//! `Extended<i64>` rung (the rung is extended because ceil at
//! `Duration::MAX` and floor at `Duration::MIN` overflow `i64`).

use crate::conn::Conn;
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
