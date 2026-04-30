//! Time-span connections — both signed (`time::Duration`) and unsigned
//! (`std::time::Duration`).
//!
//! Hosts:
//! - [`DURNSECS`] — signed `time::Duration` ↔ whole seconds via an
//!   `Extended<i64>` rung (the rung is extended because ceil at
//!   `Duration::MAX` and floor at `Duration::MIN` overflow `i64`).
//! - [`F064DURN`] / [`F032DURN`] — IEEE float seconds ↔ `time::Duration`.
//!   Walks happen on the Duration rung (1ns ULPs); ULP-bounded
//!   correction loops driven by the `def_walk_helpers!` macro
//!   handle the float-precision plateau where multiple Durations
//!   map to the same f-value.
//! - [`STDRU064`] / [`STDRU128`] — unsigned `std::time::Duration` ↔
//!   whole seconds (`u64`) and exact nanoseconds (`u128`). Both wrap
//!   the source side in `Extended` so `inner(NegInf)` lands on the
//!   synthetic source bottom rather than collapsing onto
//!   `StdDuration::ZERO` (which would force the surprising
//!   `ceil(ZERO) = NegInf` arm a non-wrapped source would inherit).
//! - [`F064STDR`] / [`F032STDR`] — IEEE float seconds ↔ `StdDuration`.
//!   Same shape as `F???DURN` but the unsigned rung means a finite
//!   negative float input projects to `ceil = Finite(ZERO)` and
//!   `floor = NegInf`.
//!
//! ## Signed vs unsigned rung
//!
//! | Conn family   | Source                  | Target          | Below-zero arm                |
//! |---------------|-------------------------|-----------------|-------------------------------|
//! | `DURNSECS`    | `Duration`              | `Extended<i64>` | rung NegInf at `MIN` overflow |
//! | `STDRU064/128`| `Extended<StdDuration>` | `Extended<u??>` | source NegInf (synthetic)     |

#[cfg(test)]
#[allow(unused_imports)]
use crate::conn::Conn;
use crate::extended::Extended;
use crate::float::{ExtendedFloat, F032, F064, def_walk_helpers};
use std::time::Duration as StdDuration;
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
/// use connections::conn::{ViewL, ViewR};
/// use connections::time::DURNSECS;
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
pub struct DURNSECS;

impl DURNSECS {
    fn _ceil(d: Duration) -> Extended<i64> {
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

    fn _inner(b: Extended<i64>) -> Duration {
        match b {
            Extended::NegInf => Duration::MIN,
            Extended::Finite(s) => Duration::seconds(s),
            Extended::PosInf => Duration::MAX,
        }
    }

    fn _floor(d: Duration) -> Extended<i64> {
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
}

impl crate::conn::ViewL<Duration, Extended<i64>> for DURNSECS {
    const L: crate::conn::ConnL<Duration, Extended<i64>> =
        crate::conn::Conn::new_l(DURNSECS::_ceil, DURNSECS::_inner);
}
impl crate::conn::ViewR<Duration, Extended<i64>> for DURNSECS {
    const R: crate::conn::ConnR<Duration, Extended<i64>> =
        crate::conn::Conn::new_r(DURNSECS::_inner, DURNSECS::_floor);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::conn::{ViewL, ViewR};
    use crate::prop::arb::{arb_duration, arb_extended_i64};
    use crate::prop::{conn as conn_laws, lattice as lattice_laws};
    use proptest::prelude::*;

    // ── Preorder laws on `Duration` ─────────────────────────────

    mod duration_preorder {
        use super::*;
        #[allow(unused_imports)]
        use crate::conn::{ViewL, ViewR};

        proptest! {
            #[test]
            fn reflexive(x in arb_duration()) {
                prop_assert!(lattice_laws::lattice_reflexive(&x));
            }

            #[test]
            fn transitive(x in arb_duration(), y in arb_duration(), z in arb_duration()) {
                prop_assert!(lattice_laws::lattice_transitive(&x, &y, &z));
            }

            #[test]
            fn antisymmetric(x in arb_duration(), y in arb_duration()) {
                prop_assert!(lattice_laws::lattice_antisymmetric(&x, &y));
            }

            #[test]
            fn bot(x in arb_duration()) {
                prop_assert!(lattice_laws::lattice_bot(&Duration::MIN, &x));
            }

            #[test]
            fn top(x in arb_duration()) {
                prop_assert!(lattice_laws::lattice_top(&Duration::MAX, &x));
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
            prop_assert!(conn_laws::galois_l(&DURNSECS::L, d, b));
        }

        #[test]
        fn galois_r(d in arb_duration(), b in arb_extended_i64()) {
            prop_assert!(conn_laws::galois_r(&DURNSECS::R, d, b));
        }

        #[test]
        fn closure_l(d in arb_duration()) {
            prop_assert!(conn_laws::closure_l(&DURNSECS::L, d));
        }

        #[test]
        fn closure_r(d in arb_duration()) {
            prop_assert!(conn_laws::closure_r(&DURNSECS::R, d));
        }

        #[test]
        fn kernel_l(b in arb_extended_i64()) {
            prop_assert!(conn_laws::kernel_l(&DURNSECS::L, b));
        }

        #[test]
        fn kernel_r(b in arb_extended_i64()) {
            prop_assert!(conn_laws::kernel_r(&DURNSECS::R, b));
        }

        #[test]
        fn monotone_l(a in arb_duration(), b in arb_duration()) {
            prop_assert!(conn_laws::monotone_l(&DURNSECS::L, a, b));
        }

        #[test]
        fn monotone_r(a in arb_extended_i64(), b in arb_extended_i64()) {
            prop_assert!(conn_laws::monotone_r(&DURNSECS::R, a, b));
        }

        #[test]
        fn idempotent(d in arb_duration()) {
            prop_assert!(conn_laws::idempotent(&DURNSECS::L, d));
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
            prop_assert!(conn_laws::ulp_bound(&DURNSECS, d, extractor));
        }

        // Roundtrip on Finite rung values: inner is exact for
        // any i64 second, and ceil/floor of the result is
        // identity.
        #[test]
        fn roundtrip_ceil(s in any::<i64>()) {
            prop_assert!(conn_laws::roundtrip_ceil(&DURNSECS::L, Extended::Finite(s)));
        }

        #[test]
        fn roundtrip_floor(s in any::<i64>()) {
            prop_assert!(conn_laws::roundtrip_floor(&DURNSECS::R, Extended::Finite(s)));
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
/// use connections::conn::{ViewL, ViewR};
/// use connections::time::F064DURN;
/// use connections::float::ExtendedFloat;
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
pub struct F064DURN;

impl F064DURN {
    fn _ceil(x: F064) -> Extended<Duration> {
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
        // Use `<=` not `<`: when `v == min_secs` (e.g., the round-trip
        // `inner(ceil(NEG_INFINITY))`), Duration::MIN is the smallest d
        // with d.as_seconds_f64() ≥ v_min, so it IS the correct ceil.
        // The walk would converge to Duration::MIN anyway but takes
        // ~2 × 10¹² nanosecond-steps at this magnitude (the f64
        // plateau at |v| ≈ 9.2e18 is ~2049 s wide). Fast-path it.
        if v <= min_secs {
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

    fn _inner(d: Extended<Duration>) -> F064 {
        match d {
            Extended::NegInf => ExtendedFloat::Bot,
            Extended::Finite(dur) => ExtendedFloat::Extend(dur.as_seconds_f64()),
            Extended::PosInf => ExtendedFloat::Top,
        }
    }

    fn _floor(x: F064) -> Extended<Duration> {
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
        // Use `>=` not `>`: when `v == max_secs` (e.g., the round-trip
        // `inner(floor(INFINITY))`), Duration::MAX is the largest d
        // with d.as_seconds_f64() ≤ v_max, so it IS the correct floor.
        // Fast-path it; the walk would otherwise climb ~2 × 10¹² ns
        // (the f64 plateau is ~2049 s wide at this magnitude).
        if v >= max_secs {
            return Extended::Finite(Duration::MAX);
        }
        // Asymmetric with the `>=` check above: `<` is intentional.
        // floor of a value below the range saturates to NegInf, not
        // Finite(Duration::MIN). At v == min_secs the walk converges
        // to Duration::MIN (top of the v_min plateau in floor's
        // direction); only v < min_secs is "off the bottom".
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
}

impl crate::conn::ViewL<F064, Extended<Duration>> for F064DURN {
    const L: crate::conn::ConnL<F064, Extended<Duration>> =
        crate::conn::Conn::new_l(F064DURN::_ceil, F064DURN::_inner);
}
impl crate::conn::ViewR<F064, Extended<Duration>> for F064DURN {
    const R: crate::conn::ConnR<F064, Extended<Duration>> =
        crate::conn::Conn::new_r(F064DURN::_inner, F064DURN::_floor);
}

/// `F032 → Extended<Duration>` — IEEE binary32 seconds ↔ Duration.
///
/// Mirrors [`F064DURN`]'s shape with `f32` precision. The f32 plateau
/// (range of Durations mapping to the same `f32`) is much wider than
/// f64's: at magnitude ~1 s it is ~120 ns; at magnitude ~10³ s it is
/// ~10⁵ ns. Proptest strategies bound the float-side finite slot to
/// `|x| ≤ 10` (see [`crate::prop::arb::arb_f32_bounded`]) so the
/// per-call ULP-walk budget stays small.
///
/// # Examples
///
/// ```rust
/// use connections::conn::{ViewL, ViewR};
/// use connections::time::F032DURN;
/// use connections::float::ExtendedFloat;
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
pub struct F032DURN;

impl F032DURN {
    fn _ceil(x: F032) -> Extended<Duration> {
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
        // See F064DURN.ceil for rationale: `<=` so the round-trip
        // value `inner(ceil(NEG_INFINITY)) = Duration::MIN.as_f32()`
        // fast-paths to Duration::MIN. The f32 plateau at this
        // magnitude is ~10²¹ nanoseconds wide; without this fast-path
        // the walk takes ~70 seconds per call.
        if v <= min_secs {
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

    fn _inner(d: Extended<Duration>) -> F032 {
        match d {
            Extended::NegInf => ExtendedFloat::Bot,
            Extended::Finite(dur) => ExtendedFloat::Extend(dur.as_seconds_f32()),
            Extended::PosInf => ExtendedFloat::Top,
        }
    }

    fn _floor(x: F032) -> Extended<Duration> {
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
        // See F064DURN.floor for rationale: `>=` so the round-trip
        // value `inner(floor(INFINITY)) = Duration::MAX.as_f32()`
        // fast-paths to Duration::MAX. Same plateau-walk argument as
        // ceil's `v <= min_secs` fix.
        if v >= max_secs {
            return Extended::Finite(Duration::MAX);
        }
        // Asymmetric with the `>=` check above: `<` is intentional.
        // See F064DURN.floor for the rationale (floor of a value
        // strictly below v_min saturates to NegInf; v == min_secs
        // would walk to Duration::MIN, but that's covered by the
        // walk path, not this guard).
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
}

impl crate::conn::ViewL<F032, Extended<Duration>> for F032DURN {
    const L: crate::conn::ConnL<F032, Extended<Duration>> =
        crate::conn::Conn::new_l(F032DURN::_ceil, F032DURN::_inner);
}
impl crate::conn::ViewR<F032, Extended<Duration>> for F032DURN {
    const R: crate::conn::ConnR<F032, Extended<Duration>> =
        crate::conn::Conn::new_r(F032DURN::_inner, F032DURN::_floor);
}

// ── std::time::Duration helpers ──────────────────────────────────

/// Shift `d` by `n` nanoseconds with saturation at `StdDuration::ZERO`
/// (no negative arm) and `StdDuration::MAX`. Used by
/// `def_walk_helpers!` for the `F???STDR` bridges.
pub(crate) fn shift_std_duration(n: i32, d: StdDuration) -> StdDuration {
    let cur = d.as_nanos();
    let max = StdDuration::MAX.as_nanos();
    let new = if n >= 0 {
        cur.saturating_add(n as u128)
    } else {
        cur.saturating_sub(n.unsigned_abs() as u128)
    };
    if new >= max {
        return StdDuration::MAX;
    }
    let secs = (new / 1_000_000_000) as u64;
    let subsec = (new % 1_000_000_000) as u32;
    StdDuration::new(secs, subsec)
}

#[inline]
fn std_duration_to_f64(d: StdDuration) -> f64 {
    d.as_secs_f64()
}

#[inline]
fn std_duration_to_f32(d: StdDuration) -> f32 {
    d.as_secs_f32()
}

def_walk_helpers!(
    f64_stdr_walks,
    f64,
    StdDuration,
    shift_std_duration,
    std_duration_to_f64
);
def_walk_helpers!(
    f32_stdr_walks,
    f32,
    StdDuration,
    shift_std_duration,
    std_duration_to_f32
);

/// `Extended<StdDuration> → Extended<u64>` — unsigned time span ↔
/// whole seconds.
///
/// Rung saturation arms (`Extended::PosInf`) catch the
/// `StdDuration::MAX` overflow where `as_secs() == u64::MAX` and a
/// non-zero sub-second part would push past `u64::MAX`. The source is
/// also wrapped (`Extended<StdDuration>`) so the synthetic `NegInf`
/// has a synthetic representative on each side rather than collapsing
/// onto `StdDuration::ZERO` — keeping the natural `ceil(Finite(ZERO))
/// = Finite(0)` arm.
///
/// On Finite source values:
/// - `floor(Finite(d)) = Finite(d.as_secs())`. No overflow possible
///   since `as_secs()` returns `u64`.
/// - `ceil(Finite(d)) = Finite(d.as_secs() + (subsec > 0 ? 1 : 0))`,
///   saturating to `PosInf` when `as_secs() == u64::MAX && subsec > 0`.
/// - `inner(Finite(s)) = Finite(StdDuration::from_secs(s))`.
///
/// Synthetic-arm round-trips: `inner(NegInf) = NegInf`,
/// `inner(PosInf) = PosInf`; `ceil(NegInf) = NegInf`, `ceil(PosInf) =
/// PosInf` (and likewise `floor`).
///
/// # Examples
///
/// ```rust
/// use connections::conn::{ViewL, ViewR};
/// use connections::time::STDRU064;
/// use connections::extended::Extended;
/// use std::time::Duration as StdDuration;
///
/// let half = StdDuration::from_secs(5) + StdDuration::from_nanos(1);
/// assert_eq!(STDRU064.ceil(Extended::Finite(half)),  Extended::Finite(6));
/// assert_eq!(STDRU064.floor(Extended::Finite(half)), Extended::Finite(5));
///
/// // Sub-second part at MAX overflows u64::MAX seconds → PosInf.
/// assert_eq!(STDRU064.ceil(Extended::Finite(StdDuration::MAX)), Extended::PosInf);
/// assert_eq!(STDRU064.floor(Extended::Finite(StdDuration::MAX)), Extended::Finite(u64::MAX));
///
/// assert_eq!(STDRU064.inner(Extended::Finite(42)),
///            Extended::Finite(StdDuration::from_secs(42)));
/// assert_eq!(STDRU064.inner(Extended::PosInf), Extended::PosInf);
/// ```
pub struct STDRU064;

impl STDRU064 {
    fn _ceil(d: Extended<StdDuration>) -> Extended<u64> {
        match d {
            Extended::NegInf => Extended::NegInf,
            Extended::PosInf => Extended::PosInf,
            Extended::Finite(d) => {
                let w = d.as_secs();
                let n = d.subsec_nanos();
                if n > 0 {
                    match w.checked_add(1) {
                        Some(s) => Extended::Finite(s),
                        None => Extended::PosInf,
                    }
                } else {
                    Extended::Finite(w)
                }
            }
        }
    }

    fn _inner(b: Extended<u64>) -> Extended<StdDuration> {
        match b {
            Extended::NegInf => Extended::NegInf,
            Extended::PosInf => Extended::PosInf,
            Extended::Finite(s) => Extended::Finite(StdDuration::from_secs(s)),
        }
    }

    fn _floor(d: Extended<StdDuration>) -> Extended<u64> {
        match d {
            Extended::NegInf => Extended::NegInf,
            Extended::PosInf => Extended::PosInf,
            Extended::Finite(d) => Extended::Finite(d.as_secs()),
        }
    }
}

impl crate::conn::ViewL<Extended<StdDuration>, Extended<u64>> for STDRU064 {
    const L: crate::conn::ConnL<Extended<StdDuration>, Extended<u64>> =
        crate::conn::Conn::new_l(STDRU064::_ceil, STDRU064::_inner);
}
impl crate::conn::ViewR<Extended<StdDuration>, Extended<u64>> for STDRU064 {
    const R: crate::conn::ConnR<Extended<StdDuration>, Extended<u64>> =
        crate::conn::Conn::new_r(STDRU064::_inner, STDRU064::_floor);
}

/// `Extended<StdDuration> → Extended<u128>` — unsigned time span ↔
/// nanoseconds.
///
/// On the Finite slot this is a bijection: `floor = ceil = Finite(d
/// .as_nanos())` and `inner` round-trips back exactly. The widest
/// `StdDuration` is `MAX`, whose `as_nanos()` is well within `u128`
/// (≈ 1.84×10²⁸ vs `u128::MAX` ≈ 3.4×10³⁸), so no rung-side overflow
/// is possible from a Finite source.
///
/// Inputs `Finite(n)` with `n > StdDuration::MAX.as_nanos()` clamp to
/// `Finite(StdDuration::MAX)` on `inner` (Galois pins this to the
/// largest representative ≤ the synthetic top).
///
/// # Examples
///
/// ```rust
/// use connections::conn::{ViewL, ViewR};
/// use connections::time::STDRU128;
/// use connections::extended::Extended;
/// use std::time::Duration as StdDuration;
///
/// let one_and_a_half = StdDuration::from_nanos(1_500_000_000);
/// assert_eq!(STDRU128.ceil(Extended::Finite(one_and_a_half)),
///            Extended::Finite(1_500_000_000_u128));
/// assert_eq!(STDRU128.floor(Extended::Finite(one_and_a_half)),
///            Extended::Finite(1_500_000_000_u128));
///
/// // `inner` is exact on the representable range and round-trips both ways.
/// let n = 1_500_000_000_u128;
/// assert_eq!(STDRU128.inner(Extended::Finite(n)),
///            Extended::Finite(StdDuration::from_nanos(n as u64)));
///
/// // Above StdDuration::MAX.as_nanos(), inner saturates.
/// assert_eq!(STDRU128.inner(Extended::Finite(u128::MAX)),
///            Extended::Finite(StdDuration::MAX));
/// ```
pub struct STDRU128;

impl STDRU128 {
    fn _ceil(d: Extended<StdDuration>) -> Extended<u128> {
        match d {
            Extended::NegInf => Extended::NegInf,
            Extended::PosInf => Extended::PosInf,
            Extended::Finite(d) => Extended::Finite(d.as_nanos()),
        }
    }

    fn _inner(b: Extended<u128>) -> Extended<StdDuration> {
        match b {
            Extended::NegInf => Extended::NegInf,
            Extended::PosInf => Extended::PosInf,
            Extended::Finite(n) => {
                let max_nanos = StdDuration::MAX.as_nanos();
                // Strict `>` so the boundary `n == max_nanos` goes
                // through the arithmetic path. Both paths produce
                // `StdDuration::MAX` at that exact value (since
                // `max_nanos.divmod(1e9) = (u64::MAX, 999_999_999)`),
                // so the bijection on the representable range is
                // sharper than an `>=` saturation guard would suggest.
                if n > max_nanos {
                    return Extended::Finite(StdDuration::MAX);
                }
                let secs = (n / 1_000_000_000) as u64;
                let subsec = (n % 1_000_000_000) as u32;
                Extended::Finite(StdDuration::new(secs, subsec))
            }
        }
    }

    fn _floor(d: Extended<StdDuration>) -> Extended<u128> {
        Self::_ceil(d)
    }
}

impl crate::conn::ViewL<Extended<StdDuration>, Extended<u128>> for STDRU128 {
    const L: crate::conn::ConnL<Extended<StdDuration>, Extended<u128>> =
        crate::conn::Conn::new_l(STDRU128::_ceil, STDRU128::_inner);
}
impl crate::conn::ViewR<Extended<StdDuration>, Extended<u128>> for STDRU128 {
    const R: crate::conn::ConnR<Extended<StdDuration>, Extended<u128>> =
        crate::conn::Conn::new_r(STDRU128::_inner, STDRU128::_floor);
}

/// `F064 → Extended<StdDuration>` — IEEE binary64 seconds ↔
/// `std::time::Duration`.
///
/// Mirrors [`F064DURN`]'s walk-on-rung shape but with an unsigned rung.
/// The asymmetry shows up at negative finite floats: `inner(NegInf) =
/// Bot` (synthetic source bottom) so Galois forces `ceil(Extend(v < 0))
/// = Finite(StdDuration::ZERO)` (the smallest representative ≥ a
/// negative input) and `floor(Extend(v < 0)) = NegInf` (no rung
/// representative ≤ a negative input).
///
/// Saturation arms otherwise match `F064DURN`: NaN sends `ceil` to
/// `PosInf` and `floor` to `NegInf`; `Bot`/`Top` round-trip through the
/// synthetic rung extremes.
///
/// # Examples
///
/// ```rust
/// use connections::conn::{ViewL, ViewR};
/// use connections::time::F064STDR;
/// use connections::float::ExtendedFloat;
/// use connections::extended::Extended;
/// use std::time::Duration as StdDuration;
///
/// // 0.5 s round-trips exactly.
/// let half = ExtendedFloat::Extend(0.5_f64);
/// assert_eq!(F064STDR.ceil(half),  Extended::Finite(StdDuration::from_millis(500)));
/// assert_eq!(F064STDR.floor(half), Extended::Finite(StdDuration::from_millis(500)));
///
/// // Negative float: ceil saturates up to ZERO; floor saturates down
/// // to NegInf because the unsigned rung has no negative representative.
/// let neg = ExtendedFloat::Extend(-0.5_f64);
/// assert_eq!(F064STDR.ceil(neg),  Extended::Finite(StdDuration::ZERO));
/// assert_eq!(F064STDR.floor(neg), Extended::NegInf);
/// ```
pub struct F064STDR;

impl F064STDR {
    fn _ceil(x: F064) -> Extended<StdDuration> {
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
        // Negative finites and -∞ — no representative ≤ them on the
        // unsigned rung (other than the synthetic NegInf, which `inner`
        // sends to Bot, not Extend(neg)). Galois pins ceil to ZERO.
        if v <= 0.0 {
            return Extended::Finite(StdDuration::ZERO);
        }
        let max_secs = StdDuration::MAX.as_secs_f64();
        if v > max_secs {
            return Extended::PosInf;
        }
        let est = StdDuration::from_secs_f64(v);
        let est_widen = est.as_secs_f64();
        let (z, _) = if est_widen >= v {
            f64_stdr_walks::descend_to_ceil(est, v)
        } else {
            f64_stdr_walks::ascend_to_ceil(est, v)
        };
        Extended::Finite(z)
    }

    fn _inner(d: Extended<StdDuration>) -> F064 {
        match d {
            Extended::NegInf => ExtendedFloat::Bot,
            Extended::Finite(dur) => ExtendedFloat::Extend(dur.as_secs_f64()),
            Extended::PosInf => ExtendedFloat::Top,
        }
    }

    fn _floor(x: F064) -> Extended<StdDuration> {
        let v = match x {
            ExtendedFloat::Bot => return Extended::NegInf,
            ExtendedFloat::Top => return Extended::PosInf,
            ExtendedFloat::Extend(v) => v,
        };
        if v.is_nan() {
            return Extended::NegInf;
        }
        if v == f64::INFINITY {
            return Extended::Finite(StdDuration::MAX);
        }
        // Negative finite floats and `Extend(-∞)` have no rung
        // representative ≤ them on the unsigned side, so floor
        // saturates to the synthetic `NegInf`.
        if v < 0.0 {
            return Extended::NegInf;
        }
        let max_secs = StdDuration::MAX.as_secs_f64();
        // See F064DURN.floor for the `>=` rationale: the f64 plateau at
        // |v| ≈ 1.84e19 spans billions of seconds, and without a fast
        // path the walk would crawl one ns at a time.
        if v >= max_secs {
            return Extended::Finite(StdDuration::MAX);
        }
        let est = StdDuration::from_secs_f64(v);
        let est_widen = est.as_secs_f64();
        let (z, _) = if est_widen <= v {
            f64_stdr_walks::ascend_to_floor(est, v)
        } else {
            f64_stdr_walks::descend_to_floor(est, v)
        };
        Extended::Finite(z)
    }
}

impl crate::conn::ViewL<F064, Extended<StdDuration>> for F064STDR {
    const L: crate::conn::ConnL<F064, Extended<StdDuration>> =
        crate::conn::Conn::new_l(F064STDR::_ceil, F064STDR::_inner);
}
impl crate::conn::ViewR<F064, Extended<StdDuration>> for F064STDR {
    const R: crate::conn::ConnR<F064, Extended<StdDuration>> =
        crate::conn::Conn::new_r(F064STDR::_inner, F064STDR::_floor);
}

/// `F032 → Extended<StdDuration>` — IEEE binary32 seconds ↔
/// `std::time::Duration`.
///
/// Mirrors [`F064STDR`] with `f32` precision; same negative-input
/// asymmetry. Proptest strategies bound the float-side finite slot to
/// `|x| ≤ 10` (see [`crate::prop::arb::arb_f32_bounded`]) so the
/// per-call ULP-walk budget stays small.
///
/// # Examples
///
/// ```rust
/// use connections::conn::{ViewL, ViewR};
/// use connections::time::F032STDR;
/// use connections::float::ExtendedFloat;
/// use connections::extended::Extended;
/// use std::time::Duration as StdDuration;
///
/// // 1.0 s lies in an f32 plateau ~120 ns wide; ceil and floor return
/// // the bottom and top of that plateau respectively.
/// let one = ExtendedFloat::Extend(1.0_f32);
/// let exact = StdDuration::from_secs(1);
/// if let (Extended::Finite(c), Extended::Finite(f)) =
///     (F032STDR.ceil(one), F032STDR.floor(one))
/// {
///     assert!(c <= exact && exact <= f);
///     assert_eq!(c.as_secs_f32(), 1.0_f32);
///     assert_eq!(f.as_secs_f32(), 1.0_f32);
/// }
/// ```
pub struct F032STDR;

impl F032STDR {
    fn _ceil(x: F032) -> Extended<StdDuration> {
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
        if v <= 0.0 {
            return Extended::Finite(StdDuration::ZERO);
        }
        let max_secs = StdDuration::MAX.as_secs_f32();
        if v > max_secs {
            return Extended::PosInf;
        }
        let est = StdDuration::from_secs_f32(v);
        let est_widen = est.as_secs_f32();
        let (z, _) = if est_widen >= v {
            f32_stdr_walks::descend_to_ceil(est, v)
        } else {
            f32_stdr_walks::ascend_to_ceil(est, v)
        };
        Extended::Finite(z)
    }

    fn _inner(d: Extended<StdDuration>) -> F032 {
        match d {
            Extended::NegInf => ExtendedFloat::Bot,
            Extended::Finite(dur) => ExtendedFloat::Extend(dur.as_secs_f32()),
            Extended::PosInf => ExtendedFloat::Top,
        }
    }

    fn _floor(x: F032) -> Extended<StdDuration> {
        let v = match x {
            ExtendedFloat::Bot => return Extended::NegInf,
            ExtendedFloat::Top => return Extended::PosInf,
            ExtendedFloat::Extend(v) => v,
        };
        if v.is_nan() {
            return Extended::NegInf;
        }
        if v == f32::INFINITY {
            return Extended::Finite(StdDuration::MAX);
        }
        if v < 0.0 {
            return Extended::NegInf;
        }
        let max_secs = StdDuration::MAX.as_secs_f32();
        if v >= max_secs {
            return Extended::Finite(StdDuration::MAX);
        }
        let est = StdDuration::from_secs_f32(v);
        let est_widen = est.as_secs_f32();
        let (z, _) = if est_widen <= v {
            f32_stdr_walks::ascend_to_floor(est, v)
        } else {
            f32_stdr_walks::descend_to_floor(est, v)
        };
        Extended::Finite(z)
    }
}

impl crate::conn::ViewL<F032, Extended<StdDuration>> for F032STDR {
    const L: crate::conn::ConnL<F032, Extended<StdDuration>> =
        crate::conn::Conn::new_l(F032STDR::_ceil, F032STDR::_inner);
}
impl crate::conn::ViewR<F032, Extended<StdDuration>> for F032STDR {
    const R: crate::conn::ConnR<F032, Extended<StdDuration>> =
        crate::conn::Conn::new_r(F032STDR::_inner, F032STDR::_floor);
}

#[cfg(test)]
mod float_durn_tests {
    use super::*;
    #[allow(unused_imports)]
    use crate::conn::{ViewL, ViewR};
    use crate::prop::arb::{
        arb_extended_duration_bounded_f32, arb_extended_duration_bounded_f64, extended_float_f32,
        extended_float_f64,
    };
    use crate::prop::conn as conn_laws;
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

    // Regression guard for the v == min_secs fast-path in ceil. The
    // f64 representation of Duration::MIN.as_seconds_f64() — call it
    // v_min — is what `inner(ceil(NEG_INFINITY))` produces. Without
    // the `<=` boundary check, the second `ceil` on this value walks
    // the f64 plateau at this magnitude (~2049 s ≈ 2 × 10¹² ns) one
    // nanosecond at a time, taking ~70 seconds in debug. With the
    // fix this finishes in nanoseconds.
    #[test]
    fn f64_ceil_min_secs_fast_path() {
        let v_min = ExtendedFloat::Extend(Duration::MIN.as_seconds_f64());
        assert_eq!(F064DURN.ceil(v_min), Extended::Finite(Duration::MIN));
    }

    #[test]
    fn f64_floor_max_secs_fast_path() {
        let v_max = ExtendedFloat::Extend(Duration::MAX.as_seconds_f64());
        assert_eq!(F064DURN.floor(v_max), Extended::Finite(Duration::MAX));
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

    // F032DURN twin of the F064DURN regression guards. f32 plateau at
    // |v| ≈ 9.2e18 is even wider than f64's, so a missing fast-path
    // here would walk billions of nanoseconds.
    #[test]
    fn f32_ceil_min_secs_fast_path() {
        let v_min = ExtendedFloat::Extend(Duration::MIN.as_seconds_f32());
        assert_eq!(F032DURN.ceil(v_min), Extended::Finite(Duration::MIN));
    }

    #[test]
    fn f32_floor_max_secs_fast_path() {
        let v_max = ExtendedFloat::Extend(Duration::MAX.as_seconds_f32());
        assert_eq!(F032DURN.floor(v_max), Extended::Finite(Duration::MAX));
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
            prop_assert!(conn_laws::galois_l(&F064DURN::L, a, b));
        }

        #[test]
        fn f64_galois_r(a in extended_float_f64(), b in arb_extended_duration_bounded_f64()) {
            prop_assert!(conn_laws::galois_r(&F064DURN::R, a, b));
        }

        #[test]
        fn f64_closure_l(a in extended_float_f64()) {
            prop_assert!(conn_laws::closure_l(&F064DURN::L, a));
        }

        #[test]
        fn f64_closure_r(a in extended_float_f64()) {
            prop_assert!(conn_laws::closure_r(&F064DURN::R, a));
        }

        #[test]
        fn f64_kernel_l(b in arb_extended_duration_bounded_f64()) {
            prop_assert!(conn_laws::kernel_l(&F064DURN::L, b));
        }

        #[test]
        fn f64_kernel_r(b in arb_extended_duration_bounded_f64()) {
            prop_assert!(conn_laws::kernel_r(&F064DURN::R, b));
        }

        #[test]
        fn f64_monotone_l(a1 in extended_float_f64(), a2 in extended_float_f64()) {
            prop_assert!(conn_laws::monotone_l(&F064DURN::L, a1, a2));
        }

        #[test]
        fn f64_monotone_r(b1 in arb_extended_duration_bounded_f64(), b2 in arb_extended_duration_bounded_f64()) {
            prop_assert!(conn_laws::monotone_r(&F064DURN::R, b1, b2));
        }

        #[test]
        fn f64_idempotent(a in extended_float_f64()) {
            prop_assert!(conn_laws::idempotent(&F064DURN::L, a));
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
            prop_assert!(conn_laws::galois_l(&F032DURN::L, a, b));
        }

        #[test]
        fn f32_galois_r(a in extended_float_f32(), b in arb_extended_duration_bounded_f32()) {
            prop_assert!(conn_laws::galois_r(&F032DURN::R, a, b));
        }

        #[test]
        fn f32_closure_l(a in extended_float_f32()) {
            prop_assert!(conn_laws::closure_l(&F032DURN::L, a));
        }

        #[test]
        fn f32_closure_r(a in extended_float_f32()) {
            prop_assert!(conn_laws::closure_r(&F032DURN::R, a));
        }

        #[test]
        fn f32_kernel_l(b in arb_extended_duration_bounded_f32()) {
            prop_assert!(conn_laws::kernel_l(&F032DURN::L, b));
        }

        #[test]
        fn f32_kernel_r(b in arb_extended_duration_bounded_f32()) {
            prop_assert!(conn_laws::kernel_r(&F032DURN::R, b));
        }

        #[test]
        fn f32_monotone_l(a1 in extended_float_f32(), a2 in extended_float_f32()) {
            prop_assert!(conn_laws::monotone_l(&F032DURN::L, a1, a2));
        }

        #[test]
        fn f32_monotone_r(b1 in arb_extended_duration_bounded_f32(), b2 in arb_extended_duration_bounded_f32()) {
            prop_assert!(conn_laws::monotone_r(&F032DURN::R, b1, b2));
        }

        #[test]
        fn f32_idempotent(a in extended_float_f32()) {
            prop_assert!(conn_laws::idempotent(&F032DURN::L, a));
        }
    }
}

// ── STDR* Conn tests ────────────────────────────────────────────

#[cfg(test)]
mod stdr_tests {
    use super::*;
    #[allow(unused_imports)]
    use crate::conn::{ViewL, ViewR};
    use crate::prop::arb::{
        arb_extended_std_duration, arb_extended_std_duration_bounded_f32,
        arb_extended_std_duration_bounded_f64, arb_extended_stdr_nanos_in_range, arb_extended_u64,
        extended_float_f32, extended_float_f64,
    };
    use crate::prop::conn as conn_laws;
    use proptest::prelude::*;

    // ── STDRU064 spot checks ────────────────────────────────────

    #[test]
    fn stdru064_zero() {
        let z = Extended::Finite(StdDuration::ZERO);
        assert_eq!(STDRU064.ceil(z), Extended::Finite(0_u64));
        assert_eq!(STDRU064.floor(z), Extended::Finite(0_u64));
        assert_eq!(STDRU064.inner(Extended::Finite(0_u64)), z);
    }

    #[test]
    fn stdru064_positive_subsec_rounds_up() {
        let d = Extended::Finite(StdDuration::from_secs(5) + StdDuration::from_nanos(1));
        assert_eq!(STDRU064.ceil(d), Extended::Finite(6_u64));
        assert_eq!(STDRU064.floor(d), Extended::Finite(5_u64));
    }

    #[test]
    fn stdru064_max_overflows_ceil() {
        let m = Extended::Finite(StdDuration::MAX);
        assert_eq!(STDRU064.ceil(m), Extended::PosInf);
        assert_eq!(STDRU064.floor(m), Extended::Finite(u64::MAX));
    }

    #[test]
    fn stdru064_synthetic_arms() {
        assert_eq!(STDRU064.ceil(Extended::NegInf), Extended::NegInf);
        assert_eq!(STDRU064.ceil(Extended::PosInf), Extended::PosInf);
        assert_eq!(STDRU064.floor(Extended::NegInf), Extended::NegInf);
        assert_eq!(STDRU064.floor(Extended::PosInf), Extended::PosInf);
        assert_eq!(STDRU064.inner(Extended::NegInf), Extended::NegInf);
        assert_eq!(STDRU064.inner(Extended::PosInf), Extended::PosInf);
    }

    // ── STDRU128 spot checks ────────────────────────────────────

    #[test]
    fn stdru128_one_and_a_half() {
        let d = Extended::Finite(StdDuration::from_nanos(1_500_000_000));
        assert_eq!(STDRU128.ceil(d), Extended::Finite(1_500_000_000_u128));
        assert_eq!(STDRU128.floor(d), Extended::Finite(1_500_000_000_u128));
    }

    #[test]
    fn stdru128_max_no_overflow() {
        let m = Extended::Finite(StdDuration::MAX);
        let m_nanos = StdDuration::MAX.as_nanos();
        assert_eq!(STDRU128.ceil(m), Extended::Finite(m_nanos));
        assert_eq!(STDRU128.floor(m), Extended::Finite(m_nanos));
    }

    #[test]
    fn stdru128_inner_saturates_above_max() {
        assert_eq!(
            STDRU128.inner(Extended::Finite(u128::MAX)),
            Extended::Finite(StdDuration::MAX)
        );
        let above = StdDuration::MAX.as_nanos() + 1;
        assert_eq!(
            STDRU128.inner(Extended::Finite(above)),
            Extended::Finite(StdDuration::MAX)
        );
    }

    #[test]
    fn stdru128_synthetic_arms() {
        assert_eq!(STDRU128.ceil(Extended::NegInf), Extended::NegInf);
        assert_eq!(STDRU128.ceil(Extended::PosInf), Extended::PosInf);
        assert_eq!(STDRU128.inner(Extended::NegInf), Extended::NegInf);
        assert_eq!(STDRU128.inner(Extended::PosInf), Extended::PosInf);
    }

    // ── STDRU064 / STDRU128 Galois law battery ──────────────────

    proptest! {
        #[test]
        fn stdru064_galois_l(d in arb_extended_std_duration(), b in arb_extended_u64()) {
            prop_assert!(conn_laws::galois_l(&STDRU064::L, d, b));
        }

        #[test]
        fn stdru064_galois_r(d in arb_extended_std_duration(), b in arb_extended_u64()) {
            prop_assert!(conn_laws::galois_r(&STDRU064::R, d, b));
        }

        #[test]
        fn stdru064_closure_l(d in arb_extended_std_duration()) {
            prop_assert!(conn_laws::closure_l(&STDRU064::L, d));
        }

        #[test]
        fn stdru064_closure_r(d in arb_extended_std_duration()) {
            prop_assert!(conn_laws::closure_r(&STDRU064::R, d));
        }

        #[test]
        fn stdru064_kernel_l(b in arb_extended_u64()) {
            prop_assert!(conn_laws::kernel_l(&STDRU064::L, b));
        }

        #[test]
        fn stdru064_kernel_r(b in arb_extended_u64()) {
            prop_assert!(conn_laws::kernel_r(&STDRU064::R, b));
        }

        #[test]
        fn stdru064_monotone_l(a in arb_extended_std_duration(), b in arb_extended_std_duration()) {
            prop_assert!(conn_laws::monotone_l(&STDRU064::L, a, b));
        }

        #[test]
        fn stdru064_monotone_r(a in arb_extended_u64(), b in arb_extended_u64()) {
            prop_assert!(conn_laws::monotone_r(&STDRU064::R, a, b));
        }

        #[test]
        fn stdru064_idempotent(d in arb_extended_std_duration()) {
            prop_assert!(conn_laws::idempotent(&STDRU064::L, d));
        }

        #[test]
        fn stdru128_galois_l(d in arb_extended_std_duration(), b in arb_extended_stdr_nanos_in_range()) {
            prop_assert!(conn_laws::galois_l(&STDRU128::L, d, b));
        }

        #[test]
        fn stdru128_galois_r(d in arb_extended_std_duration(), b in arb_extended_stdr_nanos_in_range()) {
            prop_assert!(conn_laws::galois_r(&STDRU128::R, d, b));
        }

        #[test]
        fn stdru128_closure_l(d in arb_extended_std_duration()) {
            prop_assert!(conn_laws::closure_l(&STDRU128::L, d));
        }

        #[test]
        fn stdru128_closure_r(d in arb_extended_std_duration()) {
            prop_assert!(conn_laws::closure_r(&STDRU128::R, d));
        }

        #[test]
        fn stdru128_kernel_l(b in arb_extended_stdr_nanos_in_range()) {
            prop_assert!(conn_laws::kernel_l(&STDRU128::L, b));
        }

        #[test]
        fn stdru128_kernel_r(b in arb_extended_stdr_nanos_in_range()) {
            prop_assert!(conn_laws::kernel_r(&STDRU128::R, b));
        }

        #[test]
        fn stdru128_monotone_l(a in arb_extended_std_duration(), b in arb_extended_std_duration()) {
            prop_assert!(conn_laws::monotone_l(&STDRU128::L, a, b));
        }

        #[test]
        fn stdru128_monotone_r(a in arb_extended_stdr_nanos_in_range(), b in arb_extended_stdr_nanos_in_range()) {
            prop_assert!(conn_laws::monotone_r(&STDRU128::R, a, b));
        }

        #[test]
        fn stdru128_idempotent(d in arb_extended_std_duration()) {
            prop_assert!(conn_laws::idempotent(&STDRU128::L, d));
        }

        // STDRU128 is a bijection on the representable Finite range
        // — for any rung n ≤ MAX.as_nanos(), `ceil(inner(Finite(n)))
        // == Finite(n)`. Above the range, `inner` saturates and the
        // round-trip drops back to MAX.as_nanos().
        #[test]
        fn stdru128_round_trip(n in 0_u128..=StdDuration::MAX.as_nanos()) {
            prop_assert!(conn_laws::roundtrip_ceil(&STDRU128::L, Extended::Finite(n)));
            prop_assert!(conn_laws::roundtrip_floor(&STDRU128::R, Extended::Finite(n)));
        }
    }

    // ── F064STDR spot checks ────────────────────────────────────

    #[test]
    fn f64_stdr_zero() {
        let zero = ExtendedFloat::Extend(0.0_f64);
        assert_eq!(F064STDR.ceil(zero), Extended::Finite(StdDuration::ZERO));
        assert_eq!(F064STDR.floor(zero), Extended::Finite(StdDuration::ZERO));
        assert_eq!(F064STDR.inner(Extended::Finite(StdDuration::ZERO)), zero);
    }

    #[test]
    fn f64_stdr_half_second() {
        let half = ExtendedFloat::Extend(0.5_f64);
        let half_d = StdDuration::from_millis(500);
        assert_eq!(F064STDR.ceil(half), Extended::Finite(half_d));
        assert_eq!(F064STDR.floor(half), Extended::Finite(half_d));
        assert_eq!(F064STDR.inner(Extended::Finite(half_d)), half);
    }

    #[test]
    fn f64_stdr_inner_one_second() {
        let one_d = Extended::Finite(StdDuration::from_secs(1));
        assert_eq!(F064STDR.inner(one_d), ExtendedFloat::Extend(1.0_f64));
    }

    #[test]
    fn f64_stdr_negative_input_asymmetric() {
        let neg = ExtendedFloat::Extend(-0.5_f64);
        assert_eq!(F064STDR.ceil(neg), Extended::Finite(StdDuration::ZERO));
        assert_eq!(F064STDR.floor(neg), Extended::NegInf);
    }

    #[test]
    fn f64_stdr_nan_arms() {
        let nan = ExtendedFloat::Extend(f64::NAN);
        assert_eq!(F064STDR.ceil(nan), Extended::PosInf);
        assert_eq!(F064STDR.floor(nan), Extended::NegInf);
    }

    #[test]
    fn f64_stdr_infinity_arms() {
        let pos_inf = ExtendedFloat::Extend(f64::INFINITY);
        assert_eq!(F064STDR.ceil(pos_inf), Extended::PosInf);
        assert_eq!(F064STDR.floor(pos_inf), Extended::Finite(StdDuration::MAX));

        let neg_inf = ExtendedFloat::Extend(f64::NEG_INFINITY);
        assert_eq!(F064STDR.ceil(neg_inf), Extended::Finite(StdDuration::ZERO));
        assert_eq!(F064STDR.floor(neg_inf), Extended::NegInf);
    }

    #[test]
    fn f64_stdr_bot_top_arms() {
        assert_eq!(F064STDR.ceil(ExtendedFloat::Bot), Extended::NegInf);
        assert_eq!(F064STDR.floor(ExtendedFloat::Bot), Extended::NegInf);
        assert_eq!(F064STDR.ceil(ExtendedFloat::Top), Extended::PosInf);
        assert_eq!(F064STDR.floor(ExtendedFloat::Top), Extended::PosInf);
        assert_eq!(F064STDR.inner(Extended::NegInf), ExtendedFloat::Bot);
        assert_eq!(F064STDR.inner(Extended::PosInf), ExtendedFloat::Top);
    }

    #[test]
    fn f64_stdr_floor_max_secs_fast_path() {
        let v_max = ExtendedFloat::Extend(StdDuration::MAX.as_secs_f64());
        assert_eq!(F064STDR.floor(v_max), Extended::Finite(StdDuration::MAX));
    }

    // ── F032STDR spot checks ────────────────────────────────────

    #[test]
    fn f32_stdr_zero() {
        let zero = ExtendedFloat::Extend(0.0_f32);
        assert_eq!(F032STDR.ceil(zero), Extended::Finite(StdDuration::ZERO));
        assert_eq!(F032STDR.floor(zero), Extended::Finite(StdDuration::ZERO));
    }

    #[test]
    fn f32_stdr_one_second_brackets_plateau() {
        let one = ExtendedFloat::Extend(1.0_f32);
        let exact = StdDuration::from_secs(1);
        let c = F032STDR.ceil(one);
        let f = F032STDR.floor(one);
        if let (Extended::Finite(cd), Extended::Finite(fd)) = (c, f) {
            assert!(cd <= exact && exact <= fd, "ceil={cd:?} floor={fd:?}");
            assert_eq!(cd.as_secs_f32(), 1.0_f32);
            assert_eq!(fd.as_secs_f32(), 1.0_f32);
        } else {
            panic!("expected Finite both, got ceil={c:?} floor={f:?}");
        }
    }

    #[test]
    fn f32_stdr_negative_input_asymmetric() {
        let neg = ExtendedFloat::Extend(-0.5_f32);
        assert_eq!(F032STDR.ceil(neg), Extended::Finite(StdDuration::ZERO));
        assert_eq!(F032STDR.floor(neg), Extended::NegInf);
    }

    #[test]
    fn f32_stdr_nan_arms() {
        let nan = ExtendedFloat::Extend(f32::NAN);
        assert_eq!(F032STDR.ceil(nan), Extended::PosInf);
        assert_eq!(F032STDR.floor(nan), Extended::NegInf);
    }

    #[test]
    fn f32_stdr_infinity_arms() {
        let pos_inf = ExtendedFloat::Extend(f32::INFINITY);
        assert_eq!(F032STDR.ceil(pos_inf), Extended::PosInf);
        assert_eq!(F032STDR.floor(pos_inf), Extended::Finite(StdDuration::MAX));

        let neg_inf = ExtendedFloat::Extend(f32::NEG_INFINITY);
        assert_eq!(F032STDR.ceil(neg_inf), Extended::Finite(StdDuration::ZERO));
        assert_eq!(F032STDR.floor(neg_inf), Extended::NegInf);
    }

    #[test]
    fn f32_stdr_floor_max_secs_fast_path() {
        let v_max = ExtendedFloat::Extend(StdDuration::MAX.as_secs_f32());
        assert_eq!(F032STDR.floor(v_max), Extended::Finite(StdDuration::MAX));
    }

    // ── F064STDR / F032STDR Galois law battery ──────────────────

    proptest! {
        #![proptest_config(ProptestConfig {
            cases: 64,
            max_shrink_iters: 200,
            .. ProptestConfig::default()
        })]

        #[test]
        fn f64_stdr_galois_l(a in extended_float_f64(), b in arb_extended_std_duration_bounded_f64()) {
            prop_assert!(conn_laws::galois_l(&F064STDR::L, a, b));
        }

        #[test]
        fn f64_stdr_galois_r(a in extended_float_f64(), b in arb_extended_std_duration_bounded_f64()) {
            prop_assert!(conn_laws::galois_r(&F064STDR::R, a, b));
        }

        #[test]
        fn f64_stdr_closure_l(a in extended_float_f64()) {
            prop_assert!(conn_laws::closure_l(&F064STDR::L, a));
        }

        #[test]
        fn f64_stdr_closure_r(a in extended_float_f64()) {
            prop_assert!(conn_laws::closure_r(&F064STDR::R, a));
        }

        #[test]
        fn f64_stdr_kernel_l(b in arb_extended_std_duration_bounded_f64()) {
            prop_assert!(conn_laws::kernel_l(&F064STDR::L, b));
        }

        #[test]
        fn f64_stdr_kernel_r(b in arb_extended_std_duration_bounded_f64()) {
            prop_assert!(conn_laws::kernel_r(&F064STDR::R, b));
        }

        #[test]
        fn f64_stdr_monotone_l(a1 in extended_float_f64(), a2 in extended_float_f64()) {
            prop_assert!(conn_laws::monotone_l(&F064STDR::L, a1, a2));
        }

        #[test]
        fn f64_stdr_monotone_r(b1 in arb_extended_std_duration_bounded_f64(), b2 in arb_extended_std_duration_bounded_f64()) {
            prop_assert!(conn_laws::monotone_r(&F064STDR::R, b1, b2));
        }

        #[test]
        fn f64_stdr_idempotent(a in extended_float_f64()) {
            prop_assert!(conn_laws::idempotent(&F064STDR::L, a));
        }

        // Negative finite inputs project to ZERO under ceil — Galois-
        // forced because the unsigned rung has no representative below
        // ZERO and `inner(NegInf) = Bot` (synthetic source bottom).
        #[test]
        fn f64_stdr_negative_input_ceil_to_zero(v in -1.0e9_f64..0.0_f64) {
            let a = ExtendedFloat::Extend(v);
            prop_assert_eq!(F064STDR.ceil(a), Extended::Finite(StdDuration::ZERO));
        }

        // Plateau invariant for the F064STDR walk machinery: at any
        // whole-second `StdDuration` `d`, `v = d.as_secs_f64()` is exact
        // and the f64 plateau around `v` brackets `d`. ceil walks down to
        // the smallest plateau member, floor walks up to the largest;
        // both endpoints widen back to exactly `v` and bracket `d`.
        // Exercises the `def_walk_helpers!`-emitted ULP loops at every
        // magnitude up to 10⁹ s where the plateau widens from a single
        // ns at low magnitudes to ~220 ns at the bound.
        #[test]
        fn f64_stdr_plateau(s in 0_u64..=1_000_000_000_u64) {
            let d = StdDuration::from_secs(s);
            let v = d.as_secs_f64();
            let a = ExtendedFloat::Extend(v);
            if let (Extended::Finite(c), Extended::Finite(f)) =
                (F064STDR.ceil(a), F064STDR.floor(a))
            {
                prop_assert!(c <= d && d <= f, "ceil={c:?} d={d:?} floor={f:?}");
                prop_assert_eq!(c.as_secs_f64(), v);
                prop_assert_eq!(f.as_secs_f64(), v);
            } else {
                panic!("expected Finite ceil/floor at v={v}");
            }
        }

        #[test]
        fn f32_stdr_galois_l(a in extended_float_f32(), b in arb_extended_std_duration_bounded_f32()) {
            prop_assert!(conn_laws::galois_l(&F032STDR::L, a, b));
        }

        #[test]
        fn f32_stdr_galois_r(a in extended_float_f32(), b in arb_extended_std_duration_bounded_f32()) {
            prop_assert!(conn_laws::galois_r(&F032STDR::R, a, b));
        }

        #[test]
        fn f32_stdr_closure_l(a in extended_float_f32()) {
            prop_assert!(conn_laws::closure_l(&F032STDR::L, a));
        }

        #[test]
        fn f32_stdr_closure_r(a in extended_float_f32()) {
            prop_assert!(conn_laws::closure_r(&F032STDR::R, a));
        }

        #[test]
        fn f32_stdr_kernel_l(b in arb_extended_std_duration_bounded_f32()) {
            prop_assert!(conn_laws::kernel_l(&F032STDR::L, b));
        }

        #[test]
        fn f32_stdr_kernel_r(b in arb_extended_std_duration_bounded_f32()) {
            prop_assert!(conn_laws::kernel_r(&F032STDR::R, b));
        }

        #[test]
        fn f32_stdr_monotone_l(a1 in extended_float_f32(), a2 in extended_float_f32()) {
            prop_assert!(conn_laws::monotone_l(&F032STDR::L, a1, a2));
        }

        #[test]
        fn f32_stdr_monotone_r(b1 in arb_extended_std_duration_bounded_f32(), b2 in arb_extended_std_duration_bounded_f32()) {
            prop_assert!(conn_laws::monotone_r(&F032STDR::R, b1, b2));
        }

        #[test]
        fn f32_stdr_idempotent(a in extended_float_f32()) {
            prop_assert!(conn_laws::idempotent(&F032STDR::L, a));
        }
    }
}
