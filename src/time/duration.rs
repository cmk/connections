//! Time-span connections — both signed (`time::Duration`) and unsigned
//! (`std::time::Duration`).
//!
//! Hosts:
//! - [`TDURSECS`] — signed `time::Duration` ↔ whole seconds via an
//!   `Extended<i64>` rung (the rung is extended because ceil at
//!   `Duration::MAX` and floor at `Duration::MIN` overflow `i64`).
//! - [`F064TDUR`] / [`F032TDUR`] — IEEE float seconds ↔ `time::Duration`.
//!   Walks happen on the Duration rung (1ns ULPs); ULP-bounded
//!   correction loops driven by the `def_walk_helpers!` macro
//!   handle the float-precision plateau where multiple Durations
//!   map to the same f-value.
//! - [`SDURU064`] / [`SDURU128`] — unsigned `std::time::Duration` ↔
//!   whole seconds (`u64`) and exact nanoseconds (`u128`). Both wrap
//!   the source side in `Extended` so `inner(NegInf)` lands on the
//!   synthetic source bottom rather than collapsing onto
//!   `StdDuration::ZERO` (which would force the surprising
//!   `ceil(ZERO) = NegInf` arm a non-wrapped source would inherit).
//! - [`F064SDUR`] / [`F032SDUR`] — IEEE float seconds ↔ `StdDuration`.
//!   Same shape as `F???TDUR` but the unsigned rung means a finite
//!   negative float input projects to `ceil = Finite(ZERO)` and
//!   `floor = NegInf`.
//!
//! ## Signed vs unsigned rung
//!
//! | Conn family   | Source                  | Target          | Below-zero arm                |
//! |---------------|-------------------------|-----------------|-------------------------------|
//! | `TDURSECS`    | `Duration`              | `Extended<i64>` | rung NegInf at `MIN` overflow |
//! | `SDURU064/128`| `Extended<StdDuration>` | `Extended<u??>` | source NegInf (synthetic)     |

#[cfg(test)]
#[allow(unused_imports)]
use crate::conn::Conn;
use crate::extended::Extended;
use crate::float::{ExtendedFloat, F032, F064, def_walk_helpers};
use std::time::Duration as StdDuration;
use time::Duration;

// ── Duration ULP shift + float widen helpers ─────────────────────
//
// Used by `def_walk_helpers!` to drive the F???TDUR bridges: walks
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

/// Total nanoseconds as i128 — `Duration` is already exact in this
/// representation so the round-trip with `tdur_from_ns` is loss-free
/// inside `[Duration::MIN, Duration::MAX]`.
#[inline]
fn tdur_to_ns(d: Duration) -> i128 {
    d.whole_nanoseconds()
}

/// Saturating reconstruction of a `Duration` from total nanoseconds;
/// clamps at `Duration::{MIN,MAX}` outside its representable range.
#[inline]
fn tdur_from_ns(n: i128) -> Duration {
    let max_ns = Duration::MAX.whole_nanoseconds();
    let min_ns = Duration::MIN.whole_nanoseconds();
    if n >= max_ns {
        Duration::MAX
    } else if n <= min_ns {
        Duration::MIN
    } else {
        // Truncated i128 division rounds toward zero, so the sign
        // matches between secs and subsec_nanoseconds.
        let secs = (n / 1_000_000_000) as i64;
        let subsec = (n % 1_000_000_000) as i32;
        Duration::new(secs, subsec)
    }
}

def_walk_helpers!(
    f64_tdur_walks,
    f64,
    Duration,
    shift_duration,
    duration_to_f64,
    tdur_to_ns,
    tdur_from_ns
);
def_walk_helpers!(
    f32_tdur_walks,
    f32,
    Duration,
    shift_duration,
    duration_to_f32,
    tdur_to_ns,
    tdur_from_ns
);

fn tdursecs_ceil(d: Duration) -> Extended<i64> {
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

fn tdursecs_inner(b: Extended<i64>) -> Duration {
    match b {
        Extended::NegInf => Duration::MIN,
        Extended::Finite(s) => Duration::seconds(s),
        Extended::PosInf => Duration::MAX,
    }
}

fn tdursecs_floor(d: Duration) -> Extended<i64> {
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

crate::conn_k! {
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
    /// use connections::conn::{ConnL, ConnR};
    /// use connections::time::TDURSECS;
    /// use connections::extended::Extended;
    /// use time::Duration;
    ///
    /// let half = Duration::seconds(5) + Duration::nanoseconds(1);
    /// assert_eq!(TDURSECS.ceil(half),  Extended::Finite(6));
    /// assert_eq!(TDURSECS.floor(half), Extended::Finite(5));
    ///
    /// // Negative sub-second: ceil rounds toward zero, floor away.
    /// let neg = Duration::seconds(-5) - Duration::nanoseconds(1);
    /// assert_eq!(TDURSECS.ceil(neg),  Extended::Finite(-5));
    /// assert_eq!(TDURSECS.floor(neg), Extended::Finite(-6));
    ///
    /// assert_eq!(TDURSECS.upper(Extended::Finite(42)), Duration::seconds(42));
    /// ```
    pub TDURSECS : Duration => Extended<i64> {
        ceil:  tdursecs_ceil,
        inner: tdursecs_inner,
        floor: tdursecs_floor,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::conn::{ConnL, ConnR};
    use crate::prop::arb::{arb_duration, arb_extended_i64};
    use crate::prop::{conn as conn_laws, lattice as lattice_laws};
    use proptest::prelude::*;

    // ── Preorder laws on `Duration` ─────────────────────────────

    mod duration_preorder {
        use super::*;
        #[allow(unused_imports)]
        use crate::conn::{ConnL, ConnR};

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

    // ── TDURSECS spot checks ────────────────────────────────────

    #[test]
    fn zero_is_zero() {
        assert_eq!(TDURSECS.ceil(Duration::ZERO), Extended::Finite(0));
        assert_eq!(TDURSECS.floor(Duration::ZERO), Extended::Finite(0));
        assert_eq!(TDURSECS.upper(Extended::Finite(0)), Duration::ZERO);
    }

    #[test]
    fn positive_subsec_rounds_up() {
        let d = Duration::seconds(5) + Duration::nanoseconds(1);
        assert_eq!(TDURSECS.ceil(d), Extended::Finite(6));
        assert_eq!(TDURSECS.floor(d), Extended::Finite(5));
    }

    #[test]
    fn negative_subsec_rounds_toward_zero() {
        // -5.000_000_001 s → ceil = -5, floor = -6
        let d = Duration::seconds(-5) - Duration::nanoseconds(1);
        assert_eq!(TDURSECS.ceil(d), Extended::Finite(-5));
        assert_eq!(TDURSECS.floor(d), Extended::Finite(-6));
    }

    #[test]
    fn extreme_durations() {
        assert_eq!(TDURSECS.ceil(Duration::MAX), Extended::PosInf);
        assert_eq!(TDURSECS.floor(Duration::MAX), Extended::PosInf);
        assert_eq!(TDURSECS.ceil(Duration::MIN), Extended::NegInf);
        assert_eq!(TDURSECS.floor(Duration::MIN), Extended::NegInf);
    }

    #[test]
    fn inner_saturates_extended() {
        assert_eq!(TDURSECS.upper(Extended::NegInf), Duration::MIN);
        assert_eq!(TDURSECS.upper(Extended::PosInf), Duration::MAX);
    }

    // ── TDURSECS Galois law battery ─────────────────────────────

    crate::law_battery! {
        mod tdursecs_laws,
        conn: TDURSECS,
        fine:   arb_duration(),
        coarse: arb_extended_i64(),
    }

    proptest! {
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
            prop_assert!(conn_laws::ulp_bound(&TDURSECS, d, extractor));
        }

        // Roundtrip on Finite rung values: inner is exact for
        // any i64 second, and ceil/floor of the result is
        // identity.
        #[test]
        fn roundtrip_ceil(s in any::<i64>()) {
            prop_assert!(conn_laws::roundtrip_ceil(&TDURSECS.conn_l(), Extended::Finite(s)));
        }

        #[test]
        fn roundtrip_floor(s in any::<i64>()) {
            prop_assert!(conn_laws::roundtrip_floor(&TDURSECS.conn_r(), Extended::Finite(s)));
        }
    }
}
fn f064tdur_ceil(x: F064) -> Extended<Duration> {
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
    let (z, _) = f64_tdur_walks::solve_to_ceil(est, v);
    Extended::Finite(z)
}

fn f064tdur_inner(d: Extended<Duration>) -> F064 {
    match d {
        Extended::NegInf => ExtendedFloat::Bot,
        Extended::Finite(dur) => ExtendedFloat::Extend(dur.as_seconds_f64()),
        Extended::PosInf => ExtendedFloat::Top,
    }
}

crate::conn_l! {
    /// `F064 → Extended<Duration>` — IEEE binary64 seconds ↔ Duration
    /// (left-Galois).
    ///
    /// Walks happen on the Duration rung (1ns ULPs); the float side is
    /// the comparison frame. `inner(Finite(d))` widens via
    /// `Duration::as_seconds_f64()`, which is non-injective above
    /// |Duration| > 2⁵³ ns ≈ 104 days (multiple Durations map to the same
    /// f64). That non-injectivity → not order-reflecting → no true triple,
    /// so shipped as `ConnL`. (Plan 32.)
    ///
    /// Saturation arms:
    /// - `ceil(Bot)` = `NegInf` (Bot is synthetic-below-everything).
    /// - `ceil(Top)` = `PosInf`.
    /// - `ceil(Extend(NaN))` = `PosInf` (under N5: NaN ≤ Top, Bot ≤ NaN,
    ///   NaN incomparable with finite).
    /// - `ceil(Extend(+∞))` = `PosInf`. Symmetric for `-∞` →
    ///   `Finite(Duration::MIN)`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::time::F064TDUR;
    /// use connections::float::ExtendedFloat;
    /// use connections::extended::Extended;
    /// use time::Duration;
    ///
    /// // 0.5 seconds round-trips exactly.
    /// let half = ExtendedFloat::Extend(0.5_f64);
    /// assert_eq!(F064TDUR.ceil(half), Extended::Finite(Duration::milliseconds(500)));
    /// assert_eq!(F064TDUR.upper(Extended::Finite(Duration::milliseconds(500))),
    ///            ExtendedFloat::Extend(0.5));
    ///
    /// // NaN saturates ceil to PosInf.
    /// assert_eq!(F064TDUR.ceil(ExtendedFloat::Extend(f64::NAN)), Extended::PosInf);
    /// ```
    pub F064TDUR : F064 => Extended<Duration> {
        ceil:  f064tdur_ceil,
        inner: f064tdur_inner,
    }
}

fn f032tdur_ceil(x: F032) -> Extended<Duration> {
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
    // See f064tdur_ceil for rationale: `<=` so the round-trip
    // value `inner(ceil(NEG_INFINITY)) = Duration::MIN.as_f32()`
    // fast-paths to Duration::MIN. The f32 plateau at this
    // magnitude is ~10²¹ nanoseconds wide; without this fast-path
    // the walk takes ~70 seconds per call.
    if v <= min_secs {
        return Extended::Finite(Duration::MIN);
    }
    let est = Duration::saturating_seconds_f32(v);
    let (z, _) = f32_tdur_walks::solve_to_ceil(est, v);
    Extended::Finite(z)
}

fn f032tdur_inner(d: Extended<Duration>) -> F032 {
    match d {
        Extended::NegInf => ExtendedFloat::Bot,
        Extended::Finite(dur) => ExtendedFloat::Extend(dur.as_seconds_f32()),
        Extended::PosInf => ExtendedFloat::Top,
    }
}

crate::conn_l! {
    /// `F032 → Extended<Duration>` — IEEE binary32 seconds ↔ Duration
    /// (left-Galois).
    ///
    /// Mirrors [`F064TDUR`]'s shape with `f32` precision. The f32 plateau
    /// (range of Durations mapping to the same `f32`) is much wider than
    /// f64's: at magnitude ~1 s it is ~120 ns; at magnitude ~10³ s it is
    /// ~10⁵ ns. Inner is non-injective on every plateau → not order-
    /// reflecting → no true triple. Shipped as `ConnL`. (Plan 32.)
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::time::F032TDUR;
    /// use connections::float::ExtendedFloat;
    /// use connections::extended::Extended;
    /// use time::Duration;
    ///
    /// // 1.0 s in f32 ceils to the bottom of the f32 plateau covering 1.0.
    /// let one = ExtendedFloat::Extend(1.0_f32);
    /// if let Extended::Finite(c) = F032TDUR.ceil(one) {
    ///     assert_eq!(c.as_seconds_f32(), 1.0_f32);
    /// }
    /// ```
    pub F032TDUR : F032 => Extended<Duration> {
        ceil:  f032tdur_ceil,
        inner: f032tdur_inner,
    }
}

// ── std::time::Duration helpers ──────────────────────────────────

/// Shift `d` by `n` nanoseconds with saturation at `StdDuration::ZERO`
/// (no negative arm) and `StdDuration::MAX`. Used by
/// `def_walk_helpers!` for the `F???SDUR` bridges.
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

/// Total nanoseconds as i128. `StdDuration` is unsigned, so the value
/// is always ≥ 0; the i128 envelope (≈ 1.7 × 10³⁸) easily covers
/// `StdDuration::MAX.as_nanos()` ≈ 1.84 × 10²⁸.
#[inline]
fn sdur_to_ns(d: StdDuration) -> i128 {
    d.as_nanos() as i128
}

/// Saturating reconstruction; clamps below zero to `ZERO` and above
/// `StdDuration::MAX.as_nanos()` to `MAX`.
#[inline]
fn sdur_from_ns(n: i128) -> StdDuration {
    if n <= 0 {
        return StdDuration::ZERO;
    }
    let n_u = n as u128;
    if n_u >= StdDuration::MAX.as_nanos() {
        return StdDuration::MAX;
    }
    let secs = (n_u / 1_000_000_000) as u64;
    let subsec = (n_u % 1_000_000_000) as u32;
    StdDuration::new(secs, subsec)
}

def_walk_helpers!(
    f64_sdur_walks,
    f64,
    StdDuration,
    shift_std_duration,
    std_duration_to_f64,
    sdur_to_ns,
    sdur_from_ns
);
def_walk_helpers!(
    f32_sdur_walks,
    f32,
    StdDuration,
    shift_std_duration,
    std_duration_to_f32,
    sdur_to_ns,
    sdur_from_ns
);

fn sduru064_ceil(d: Extended<StdDuration>) -> Extended<u64> {
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

fn sduru064_inner(b: Extended<u64>) -> Extended<StdDuration> {
    match b {
        Extended::NegInf => Extended::NegInf,
        Extended::PosInf => Extended::PosInf,
        Extended::Finite(s) => Extended::Finite(StdDuration::from_secs(s)),
    }
}

crate::conn_l! {
    /// `Extended<StdDuration> → Extended<u64>` — unsigned time span ↔
    /// whole seconds (left-Galois).
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
    /// - `ceil(Finite(d)) = Finite(d.as_secs() + (subsec > 0 ? 1 : 0))`,
    ///   saturating to `PosInf` when `as_secs() == u64::MAX && subsec > 0`.
    /// - `inner(Finite(s)) = Finite(StdDuration::from_secs(s))`.
    ///
    /// Synthetic-arm round-trips: `inner(NegInf) = NegInf`,
    /// `inner(PosInf) = PosInf`; `ceil(NegInf) = NegInf`, `ceil(PosInf) =
    /// PosInf`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::conn::ConnL;
    /// use connections::time::SDURU064;
    /// use connections::extended::Extended;
    /// use std::time::Duration as StdDuration;
    ///
    /// let half = StdDuration::from_secs(5) + StdDuration::from_nanos(1);
    /// assert_eq!(SDURU064.ceil(Extended::Finite(half)),  Extended::Finite(6));
    ///
    /// // Sub-second part at MAX overflows u64::MAX seconds → PosInf.
    /// assert_eq!(SDURU064.ceil(Extended::Finite(StdDuration::MAX)), Extended::PosInf);
    ///
    /// assert_eq!(SDURU064.upper(Extended::Finite(42)),
    ///            Extended::Finite(StdDuration::from_secs(42)));
    /// assert_eq!(SDURU064.upper(Extended::PosInf), Extended::PosInf);
    /// ```
    pub SDURU064 : Extended<StdDuration> => Extended<u64> {
        ceil:  sduru064_ceil,
        inner: sduru064_inner,
    }
}

fn sduru128_ceil(d: Extended<StdDuration>) -> Extended<u128> {
    match d {
        Extended::NegInf => Extended::NegInf,
        Extended::PosInf => Extended::PosInf,
        Extended::Finite(d) => Extended::Finite(d.as_nanos()),
    }
}

fn sduru128_inner(b: Extended<u128>) -> Extended<StdDuration> {
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

crate::conn_l! {
    /// `Extended<StdDuration> → Extended<u128>` — unsigned time span ↔
    /// nanoseconds (left-Galois).
    ///
    /// On the Finite range `[0, StdDuration::MAX.as_nanos()]` this is a
    /// bijection: `ceil(Finite(d)) = Finite(d.as_nanos())` and `inner`
    /// round-trips back exactly. The widest `StdDuration` is `MAX`, whose
    /// `as_nanos()` is well within `u128` (≈ 1.84×10²⁸ vs `u128::MAX` ≈
    /// 3.4×10³⁸), so no rung-side overflow is possible from a Finite source.
    ///
    /// Inputs `Finite(n)` with `n > StdDuration::MAX.as_nanos()` clamp to
    /// `Finite(StdDuration::MAX)` on `inner` (Galois pins this to the
    /// largest representative ≤ the synthetic top).
    ///
    /// **One-sided.** Shipped as `ConnL` rather than a `conn_k!` marker
    /// because `inner` collapses the entire above-max plateau
    /// (`Finite(n > max_nanos)`) onto `Finite(StdDuration::MAX)` and so is
    /// not order-reflecting; the L-Galois adjunction `ceil ⊣ inner` holds
    /// on the full domain, but no `floor` function admits the dual
    /// adjunction `inner ⊣ floor` simultaneously. See `doc/design.md` and
    /// Plan 32 for the rounding-sandwich derivation.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::time::SDURU128;
    /// use connections::extended::Extended;
    /// use std::time::Duration as StdDuration;
    ///
    /// let one_and_a_half = StdDuration::from_nanos(1_500_000_000);
    /// assert_eq!(SDURU128.ceil(Extended::Finite(one_and_a_half)),
    ///            Extended::Finite(1_500_000_000_u128));
    ///
    /// // `inner` is exact on the representable range and round-trips back.
    /// let n = 1_500_000_000_u128;
    /// assert_eq!(SDURU128.upper(Extended::Finite(n)),
    ///            Extended::Finite(StdDuration::from_nanos(n as u64)));
    ///
    /// // Above StdDuration::MAX.as_nanos(), inner saturates to MAX.
    /// assert_eq!(SDURU128.upper(Extended::Finite(u128::MAX)),
    ///            Extended::Finite(StdDuration::MAX));
    /// ```
    pub SDURU128 : Extended<StdDuration> => Extended<u128> {
        ceil:  sduru128_ceil,
        inner: sduru128_inner,
    }
}

fn f064sdur_ceil(x: F064) -> Extended<StdDuration> {
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
    if v >= max_secs {
        return if v == max_secs {
            Extended::Finite(StdDuration::MAX)
        } else {
            Extended::PosInf
        };
    }
    let est = StdDuration::from_secs_f64(v);
    let (z, _) = f64_sdur_walks::solve_to_ceil(est, v);
    Extended::Finite(z)
}

fn f064sdur_inner(d: Extended<StdDuration>) -> F064 {
    match d {
        Extended::NegInf => ExtendedFloat::Bot,
        Extended::Finite(dur) => ExtendedFloat::Extend(dur.as_secs_f64()),
        Extended::PosInf => ExtendedFloat::Top,
    }
}

crate::conn_l! {
    /// `F064 → Extended<StdDuration>` — IEEE binary64 seconds ↔
    /// `std::time::Duration` (left-Galois).
    ///
    /// Mirrors [`F064TDUR`]'s walk-on-rung shape with an unsigned rung.
    /// `inner` is non-injective on the f64 plateau (multiple StdDurations
    /// map to the same f64 above ~104 days), so not order-reflecting and
    /// no true triple. Shipped as `ConnL`. (Plan 32.)
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::time::F064SDUR;
    /// use connections::float::ExtendedFloat;
    /// use connections::extended::Extended;
    /// use std::time::Duration as StdDuration;
    ///
    /// // 0.5 s round-trips exactly.
    /// let half = ExtendedFloat::Extend(0.5_f64);
    /// assert_eq!(F064SDUR.ceil(half), Extended::Finite(StdDuration::from_millis(500)));
    ///
    /// // Negative float: ceil saturates up to ZERO (unsigned rung has
    /// // no negative representative).
    /// let neg = ExtendedFloat::Extend(-0.5_f64);
    /// assert_eq!(F064SDUR.ceil(neg), Extended::Finite(StdDuration::ZERO));
    /// ```
    pub F064SDUR : F064 => Extended<StdDuration> {
        ceil:  f064sdur_ceil,
        inner: f064sdur_inner,
    }
}

fn f032sdur_ceil(x: F032) -> Extended<StdDuration> {
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
    if v >= max_secs {
        return if v == max_secs {
            Extended::Finite(StdDuration::MAX)
        } else {
            Extended::PosInf
        };
    }
    let est = StdDuration::from_secs_f32(v);
    let (z, _) = f32_sdur_walks::solve_to_ceil(est, v);
    Extended::Finite(z)
}

fn f032sdur_inner(d: Extended<StdDuration>) -> F032 {
    match d {
        Extended::NegInf => ExtendedFloat::Bot,
        Extended::Finite(dur) => ExtendedFloat::Extend(dur.as_secs_f32()),
        Extended::PosInf => ExtendedFloat::Top,
    }
}

crate::conn_l! {
    /// `F032 → Extended<StdDuration>` — IEEE binary32 seconds ↔
    /// `std::time::Duration` (left-Galois).
    ///
    /// Mirrors [`F064SDUR`] with `f32` precision. The f32 plateau makes
    /// `inner` non-injective on every multi-Duration plateau, so no true
    /// triple. Shipped as `ConnL`. (Plan 32.)
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::time::F032SDUR;
    /// use connections::float::ExtendedFloat;
    /// use connections::extended::Extended;
    /// use std::time::Duration as StdDuration;
    ///
    /// // 1.0 s in f32 ceils to the bottom of the f32 plateau covering 1.0.
    /// let one = ExtendedFloat::Extend(1.0_f32);
    /// if let Extended::Finite(c) = F032SDUR.ceil(one) {
    ///     assert_eq!(c.as_secs_f32(), 1.0_f32);
    /// }
    /// ```
    pub F032SDUR : F032 => Extended<StdDuration> {
        ceil:  f032sdur_ceil,
        inner: f032sdur_inner,
    }
}

// ── Proof-only walk + solver step probes ───────────────────────────
//
// Two parallel families of Kani exposers per Conn:
//
// * `*_walk_steps_for_proof` — calls the legacy ULP walk
//   (`ascend_to_ceil` / `descend_to_ceil`). Production no longer
//   reaches these for the duration Conns (the solver replaced
//   them), but the walk fns are still emitted by `def_walk_helpers!`
//   and called from this module's `*_solve_matches_walk_in_safe_range`
//   proptests as cross-checks. The matching Kani harnesses prove
//   `walk_steps ≤ 1` exhaustively on a bounded slice, guarding the
//   walk fns against silent regressions.
//
// * `*_solve_steps_for_proof` — calls `solve_to_ceil`, the new
//   production path. The matching Kani harnesses prove
//   `solve_steps ≤ SOLVE_STEP_BOUND` (= 44) exhaustively on the
//   same slice. The solver bound is structural (loop body halves
//   the bracket each iteration) but the harness is still useful as
//   the SMT-blessed seal.
//
// All shims omit production fast-paths; matching `kani::assume`s
// live in the harness.

#[cfg(kani)]
pub(crate) fn f64_tdur_ceil_walk_steps_for_proof(v: f64) -> (Duration, u32) {
    let est = Duration::saturating_seconds_f64(v);
    let est_widen = est.as_seconds_f64();
    if est_widen >= v {
        f64_tdur_walks::descend_to_ceil(est, v)
    } else {
        f64_tdur_walks::ascend_to_ceil(est, v)
    }
}

#[cfg(kani)]
pub(crate) fn f32_tdur_ceil_walk_steps_for_proof(v: f32) -> (Duration, u32) {
    let est = Duration::saturating_seconds_f32(v);
    let est_widen = est.as_seconds_f32();
    if est_widen >= v {
        f32_tdur_walks::descend_to_ceil(est, v)
    } else {
        f32_tdur_walks::ascend_to_ceil(est, v)
    }
}

#[cfg(kani)]
pub(crate) fn f64_sdur_ceil_walk_steps_for_proof(v: f64) -> (StdDuration, u32) {
    // Mirror production's `v <= 0.0` fast-path so the exposer is
    // panic-free at the function boundary regardless of whether the
    // calling harness `kani::assume`s positivity.
    // `StdDuration::from_secs_f64` panics on negative inputs.
    if v <= 0.0 {
        return (StdDuration::ZERO, 0);
    }
    let est = StdDuration::from_secs_f64(v);
    let est_widen = est.as_secs_f64();
    if est_widen >= v {
        f64_sdur_walks::descend_to_ceil(est, v)
    } else {
        f64_sdur_walks::ascend_to_ceil(est, v)
    }
}

#[cfg(kani)]
pub(crate) fn f32_sdur_ceil_walk_steps_for_proof(v: f32) -> (StdDuration, u32) {
    if v <= 0.0 {
        return (StdDuration::ZERO, 0);
    }
    let est = StdDuration::from_secs_f32(v);
    let est_widen = est.as_secs_f32();
    if est_widen >= v {
        f32_sdur_walks::descend_to_ceil(est, v)
    } else {
        f32_sdur_walks::ascend_to_ceil(est, v)
    }
}

#[cfg(kani)]
pub(crate) fn f64_tdur_ceil_solve_steps_for_proof(v: f64) -> (Duration, u32) {
    let est = Duration::saturating_seconds_f64(v);
    f64_tdur_walks::solve_to_ceil(est, v)
}

#[cfg(kani)]
pub(crate) fn f32_tdur_ceil_solve_steps_for_proof(v: f32) -> (Duration, u32) {
    let est = Duration::saturating_seconds_f32(v);
    f32_tdur_walks::solve_to_ceil(est, v)
}

#[cfg(kani)]
pub(crate) fn f64_sdur_ceil_solve_steps_for_proof(v: f64) -> (StdDuration, u32) {
    if v <= 0.0 {
        return (StdDuration::ZERO, 0);
    }
    let est = StdDuration::from_secs_f64(v);
    f64_sdur_walks::solve_to_ceil(est, v)
}

#[cfg(kani)]
pub(crate) fn f32_sdur_ceil_solve_steps_for_proof(v: f32) -> (StdDuration, u32) {
    if v <= 0.0 {
        return (StdDuration::ZERO, 0);
    }
    let est = StdDuration::from_secs_f32(v);
    f32_sdur_walks::solve_to_ceil(est, v)
}

#[cfg(test)]
mod float_tdur_tests {
    use super::*;
    #[allow(unused_imports)]
    use crate::conn::ConnL;
    use crate::prop::arb::{
        arb_extended_duration_bounded_f32, arb_extended_duration_bounded_f64, extended_float_f32,
        extended_float_f64,
    };

    // ── F064TDUR spot checks ────────────────────────────────────

    #[test]
    fn f64_zero() {
        let zero = ExtendedFloat::Extend(0.0_f64);
        assert_eq!(F064TDUR.ceil(zero), Extended::Finite(Duration::ZERO));
        assert_eq!(F064TDUR.upper(Extended::Finite(Duration::ZERO)), zero);
    }

    #[test]
    fn f64_half_second() {
        // 0.5 s is exactly representable in f64 and Duration.
        let half = ExtendedFloat::Extend(0.5_f64);
        let half_d = Duration::milliseconds(500);
        assert_eq!(F064TDUR.ceil(half), Extended::Finite(half_d));
        assert_eq!(F064TDUR.upper(Extended::Finite(half_d)), half);
    }

    #[test]
    fn f64_nan_arms() {
        let nan = ExtendedFloat::Extend(f64::NAN);
        assert_eq!(F064TDUR.ceil(nan), Extended::PosInf);
    }

    #[test]
    fn f64_infinity_arms() {
        let pos_inf = ExtendedFloat::Extend(f64::INFINITY);
        assert_eq!(F064TDUR.ceil(pos_inf), Extended::PosInf);

        let neg_inf = ExtendedFloat::Extend(f64::NEG_INFINITY);
        assert_eq!(F064TDUR.ceil(neg_inf), Extended::Finite(Duration::MIN));
    }

    #[test]
    fn f64_bot_top_arms() {
        assert_eq!(F064TDUR.ceil(ExtendedFloat::Bot), Extended::NegInf);
        assert_eq!(F064TDUR.ceil(ExtendedFloat::Top), Extended::PosInf);
        assert_eq!(F064TDUR.upper(Extended::NegInf), ExtendedFloat::Bot);
        assert_eq!(F064TDUR.upper(Extended::PosInf), ExtendedFloat::Top);
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
        assert_eq!(F064TDUR.ceil(v_min), Extended::Finite(Duration::MIN));
    }

    // (Plan 32: F064TDUR demoted to ConnL; floor() removed.)

    // ── F032TDUR spot checks (ConnL — no floor()) ──────────────

    #[test]
    fn f32_zero() {
        let zero = ExtendedFloat::Extend(0.0_f32);
        assert_eq!(F032TDUR.ceil(zero), Extended::Finite(Duration::ZERO));
        assert_eq!(F032TDUR.upper(Extended::Finite(Duration::ZERO)), zero);
    }

    #[test]
    fn f32_one_second_in_plateau() {
        // f32 ULP at 1.0 ≈ 1.19e-7 s. ceil returns the bottom of the
        // plateau covering 1.0; widen back yields 1.0_f32 exactly.
        let one = ExtendedFloat::Extend(1.0_f32);
        if let Extended::Finite(cd) = F032TDUR.ceil(one) {
            assert_eq!(cd.as_seconds_f32(), 1.0_f32);
        } else {
            panic!("ceil(1.0) should be Finite");
        }
    }

    #[test]
    fn f32_nan_arms() {
        let nan = ExtendedFloat::Extend(f32::NAN);
        assert_eq!(F032TDUR.ceil(nan), Extended::PosInf);
    }

    #[test]
    fn f32_infinity_arms() {
        let pos_inf = ExtendedFloat::Extend(f32::INFINITY);
        assert_eq!(F032TDUR.ceil(pos_inf), Extended::PosInf);

        let neg_inf = ExtendedFloat::Extend(f32::NEG_INFINITY);
        assert_eq!(F032TDUR.ceil(neg_inf), Extended::Finite(Duration::MIN));
    }

    #[test]
    fn f32_ceil_min_secs_fast_path() {
        let v_min = ExtendedFloat::Extend(Duration::MIN.as_seconds_f32());
        assert_eq!(F032TDUR.ceil(v_min), Extended::Finite(Duration::MIN));
    }

    #[test]
    fn f32_bot_top_arms() {
        assert_eq!(F032TDUR.ceil(ExtendedFloat::Bot), Extended::NegInf);
        assert_eq!(F032TDUR.ceil(ExtendedFloat::Top), Extended::PosInf);
        assert_eq!(F032TDUR.upper(Extended::NegInf), ExtendedFloat::Bot);
        assert_eq!(F032TDUR.upper(Extended::PosInf), ExtendedFloat::Top);
    }

    // ── Galois L-side battery — F064TDUR / F032TDUR ────────────
    //
    // F064TDUR/F032TDUR are ConnL (Plan 32 demoted them — `inner` is
    // non-injective on the f64/f32 plateau, so no true triple). Hand-
    // rolled proptest because law_battery! is marker-only and these
    // are bare ConnL consts. Float-side strategies bound `Extend(_)`
    // to |x| ≤ 1e9 (f64) / 10 (f32) so per-call walk budget stays
    // small.

    use crate::prop::conn as float_tdur_conn_laws;
    use ::proptest::prelude::*;

    proptest! {
        #![proptest_config(ProptestConfig { cases: 64, .. ProptestConfig::default() })]
        #[test]
        fn f064tdur_galois_l(a in extended_float_f64(),
                             b in arb_extended_duration_bounded_f64()) {
            prop_assert!(float_tdur_conn_laws::galois_l(&F064TDUR, a, b));
        }
        #[test]
        fn f064tdur_closure_l(a in extended_float_f64()) {
            prop_assert!(float_tdur_conn_laws::closure_l(&F064TDUR, a));
        }
        #[test]
        fn f064tdur_kernel_l(b in arb_extended_duration_bounded_f64()) {
            prop_assert!(float_tdur_conn_laws::kernel_l(&F064TDUR, b));
        }
        #[test]
        fn f064tdur_monotone_l(a1 in extended_float_f64(), a2 in extended_float_f64()) {
            prop_assert!(float_tdur_conn_laws::monotone_l(&F064TDUR, a1, a2));
        }
        #[test]
        fn f064tdur_idempotent(a in extended_float_f64()) {
            prop_assert!(float_tdur_conn_laws::idempotent_l(&F064TDUR, a));
        }
        #[test]
        fn f032tdur_galois_l(a in extended_float_f32(),
                             b in arb_extended_duration_bounded_f32()) {
            prop_assert!(float_tdur_conn_laws::galois_l(&F032TDUR, a, b));
        }
        #[test]
        fn f032tdur_closure_l(a in extended_float_f32()) {
            prop_assert!(float_tdur_conn_laws::closure_l(&F032TDUR, a));
        }
        #[test]
        fn f032tdur_kernel_l(b in arb_extended_duration_bounded_f32()) {
            prop_assert!(float_tdur_conn_laws::kernel_l(&F032TDUR, b));
        }
        #[test]
        fn f032tdur_monotone_l(a1 in extended_float_f32(), a2 in extended_float_f32()) {
            prop_assert!(float_tdur_conn_laws::monotone_l(&F032TDUR, a1, a2));
        }
        #[test]
        fn f032tdur_idempotent(a in extended_float_f32()) {
            prop_assert!(float_tdur_conn_laws::idempotent_l(&F032TDUR, a));
        }
    }

    // ── solve_to_ceil termination + walk-equivalence ─────────────
    //
    // The walk used to take ~10¹² ns-steps at extremes; solve_to_ceil
    // is structurally bounded to ⌈log₂(2 × 2⁴²)⌉ = 43 iterations.
    // These tests exercise both the bound (interior of the MAX rim,
    // where the walk would hang) and equivalence to the legacy walk
    // on the safe range (|v| ≤ 1e6, where the walk converges in ≤ 2
    // steps and the solver agrees on the answer).

    #[test]
    fn f64_tdur_solve_terminates_at_max_rim() {
        // v == Duration::MAX.as_seconds_f64(): the rim fast-path
        // (`if v > max_secs`) is `>`, not `>=`, so this exact value
        // falls through to the solver. Pre-solver this walked
        // ~10¹² ns of plateau; solver finishes in ≤ 44 iterations.
        let max_secs = Duration::MAX.as_seconds_f64();
        let _ = F064TDUR.ceil(ExtendedFloat::Extend(max_secs));
    }

    #[test]
    fn f32_tdur_solve_terminates_at_max_rim() {
        let max_secs = Duration::MAX.as_seconds_f32();
        let _ = F032TDUR.ceil(ExtendedFloat::Extend(max_secs));
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(256))]

        // For inputs in the safe range, solve_to_ceil should agree
        // with the legacy walk dispatch — both compute the smallest
        // Duration `z` whose `as_seconds_f64() >= v`.
        #[test]
        fn f64_tdur_solve_matches_walk_in_safe_range(v in -1.0e6_f64..1.0e6_f64) {
            let est = Duration::saturating_seconds_f64(v);
            let est_widen = est.as_seconds_f64();
            let (walk_z, _) = if est_widen >= v {
                f64_tdur_walks::descend_to_ceil(est, v)
            } else {
                f64_tdur_walks::ascend_to_ceil(est, v)
            };
            let (solve_z, steps) = f64_tdur_walks::solve_to_ceil(est, v);
            prop_assert_eq!(solve_z, walk_z);
            prop_assert!(steps <= 44, "solve_to_ceil took {steps} steps");
        }

        // f32 plateau widens to ~120 ns by 1 s magnitude and ~10⁵ ns
        // by 10³ s; tightening to |v| ≤ 1 keeps the legacy walk's
        // cross-check fast (≤ ~120 walk steps per case).
        #[test]
        fn f32_tdur_solve_matches_walk_in_safe_range(v in -1.0_f32..1.0_f32) {
            let est = Duration::saturating_seconds_f32(v);
            let est_widen = est.as_seconds_f32();
            let (walk_z, _) = if est_widen >= v {
                f32_tdur_walks::descend_to_ceil(est, v)
            } else {
                f32_tdur_walks::ascend_to_ceil(est, v)
            };
            let (solve_z, steps) = f32_tdur_walks::solve_to_ceil(est, v);
            prop_assert_eq!(solve_z, walk_z);
            prop_assert!(steps <= 44, "solve_to_ceil took {steps} steps");
        }
    }
}

// ── SDUR* Conn tests ────────────────────────────────────────────

#[cfg(test)]
mod sdur_tests {
    use super::*;
    #[allow(unused_imports)]
    use crate::conn::ConnL;
    use crate::prop::arb::{
        arb_extended_std_duration, arb_extended_std_duration_bounded_f32,
        arb_extended_std_duration_bounded_f64, arb_extended_u64, arb_extended_u128,
        extended_float_f32, extended_float_f64,
    };
    use crate::prop::conn as conn_laws;
    use proptest::prelude::*;

    // ── SDURU064 spot checks ────────────────────────────────────

    #[test]
    fn sduru064_zero() {
        let z = Extended::Finite(StdDuration::ZERO);
        assert_eq!(SDURU064.ceil(z), Extended::Finite(0_u64));
        assert_eq!(SDURU064.upper(Extended::Finite(0_u64)), z);
    }

    #[test]
    fn sduru064_positive_subsec_rounds_up() {
        let d = Extended::Finite(StdDuration::from_secs(5) + StdDuration::from_nanos(1));
        assert_eq!(SDURU064.ceil(d), Extended::Finite(6_u64));
    }

    #[test]
    fn sduru064_max_overflows_ceil() {
        let m = Extended::Finite(StdDuration::MAX);
        assert_eq!(SDURU064.ceil(m), Extended::PosInf);
    }

    #[test]
    fn sduru064_synthetic_arms() {
        assert_eq!(SDURU064.ceil(Extended::NegInf), Extended::NegInf);
        assert_eq!(SDURU064.ceil(Extended::PosInf), Extended::PosInf);
        assert_eq!(SDURU064.upper(Extended::NegInf), Extended::NegInf);
        assert_eq!(SDURU064.upper(Extended::PosInf), Extended::PosInf);
    }

    // ── SDURU128 spot checks (ConnL — no `.floor()` method) ──────

    #[test]
    fn sduru128_one_and_a_half() {
        let d = Extended::Finite(StdDuration::from_nanos(1_500_000_000));
        assert_eq!(SDURU128.ceil(d), Extended::Finite(1_500_000_000_u128));
    }

    #[test]
    fn sduru128_max_no_overflow() {
        let m = Extended::Finite(StdDuration::MAX);
        let m_nanos = StdDuration::MAX.as_nanos();
        assert_eq!(SDURU128.ceil(m), Extended::Finite(m_nanos));
    }

    #[test]
    fn sduru128_inner_saturates_above_max() {
        assert_eq!(
            SDURU128.upper(Extended::Finite(u128::MAX)),
            Extended::Finite(StdDuration::MAX)
        );
        let above = StdDuration::MAX.as_nanos() + 1;
        assert_eq!(
            SDURU128.upper(Extended::Finite(above)),
            Extended::Finite(StdDuration::MAX)
        );
    }

    #[test]
    fn sduru128_synthetic_arms() {
        assert_eq!(SDURU128.ceil(Extended::NegInf), Extended::NegInf);
        assert_eq!(SDURU128.ceil(Extended::PosInf), Extended::PosInf);
        assert_eq!(SDURU128.upper(Extended::NegInf), Extended::NegInf);
        assert_eq!(SDURU128.upper(Extended::PosInf), Extended::PosInf);
    }

    // Boundary kernel_l checks: with sduru128 demoted to ConnL, the
    // L-side adjunction holds on the FULL `Extended<u128>` rung
    // (including `Finite(n > max_nanos)` where the prior `conn_k!`
    // shape silently broke `kernel_r`). Pin those boundaries here
    // so future regressions surface immediately.
    #[test]
    fn sduru128_kernel_l_at_above_max_boundary() {
        let max_nanos = StdDuration::MAX.as_nanos();
        for b in [
            Extended::Finite(0_u128),
            Extended::Finite(max_nanos),
            Extended::Finite(max_nanos + 1),
            Extended::Finite(u128::MAX),
        ] {
            assert!(
                conn_laws::kernel_l(&SDURU128, b),
                "kernel_l violated at b = {:?}",
                b
            );
        }
    }

    // ── SDURU064 / SDURU128 Galois law battery ──────────────────

    crate::law_battery! {
        mod sduru064_laws,
        conn: SDURU064,
        fine:   arb_extended_std_duration(),
        coarse: arb_extended_u64(),
        subset: l_only,
    }

    // SDURU128 is now ConnL — exercise L-side laws over the FULL
    // Extended<u128> rung (no in-range filter). The `coarse` strategy
    // `arb_extended_u128()` includes `Finite(u128::MAX)`, which under
    // the prior `conn_k!` shape would have surfaced a `kernel_r`
    // violation. With ConnL, only L-side laws apply and they hold on
    // the full domain. Pattern matches TIMENANO/ODTMNANO (bare ConnL
    // const, hand-rolled proptest! since law_battery! is marker-only).
    proptest! {
        #[test]
        fn sduru128_galois_l(d in arb_extended_std_duration(), b in arb_extended_u128()) {
            prop_assert!(conn_laws::galois_l(&SDURU128, d, b));
        }

        #[test]
        fn sduru128_closure_l(d in arb_extended_std_duration()) {
            prop_assert!(conn_laws::closure_l(&SDURU128, d));
        }

        #[test]
        fn sduru128_kernel_l(b in arb_extended_u128()) {
            prop_assert!(conn_laws::kernel_l(&SDURU128, b));
        }

        #[test]
        fn sduru128_monotone_l(a in arb_extended_std_duration(),
                               b in arb_extended_std_duration()) {
            prop_assert!(conn_laws::monotone_l(&SDURU128, a, b));
        }

        #[test]
        fn sduru128_idempotent(d in arb_extended_std_duration()) {
            prop_assert!(conn_laws::idempotent(&SDURU128, d));
        }

        // Bijection on the representable Finite range — for any rung
        // n ≤ MAX.as_nanos(), `ceil(inner(Finite(n))) == Finite(n)`.
        // (No `roundtrip_floor` test: SDURU128 is ConnL, so
        // `.floor()` doesn't exist.)
        #[test]
        fn sduru128_round_trip(n in 0_u128..=StdDuration::MAX.as_nanos()) {
            prop_assert!(conn_laws::roundtrip_ceil(&SDURU128, Extended::Finite(n)));
        }
    }

    // ── F064SDUR / F032SDUR spot checks (ConnL — no floor()) ──

    #[test]
    fn f64_sdur_zero() {
        let zero = ExtendedFloat::Extend(0.0_f64);
        assert_eq!(F064SDUR.ceil(zero), Extended::Finite(StdDuration::ZERO));
        assert_eq!(F064SDUR.upper(Extended::Finite(StdDuration::ZERO)), zero);
    }

    #[test]
    fn f64_sdur_half_second() {
        let half = ExtendedFloat::Extend(0.5_f64);
        let half_d = StdDuration::from_millis(500);
        assert_eq!(F064SDUR.ceil(half), Extended::Finite(half_d));
        assert_eq!(F064SDUR.upper(Extended::Finite(half_d)), half);
    }

    #[test]
    fn f64_sdur_inner_one_second() {
        let one_d = Extended::Finite(StdDuration::from_secs(1));
        assert_eq!(F064SDUR.upper(one_d), ExtendedFloat::Extend(1.0_f64));
    }

    #[test]
    fn f64_sdur_negative_input() {
        let neg = ExtendedFloat::Extend(-0.5_f64);
        assert_eq!(F064SDUR.ceil(neg), Extended::Finite(StdDuration::ZERO));
    }

    #[test]
    fn f64_sdur_nan_arms() {
        let nan = ExtendedFloat::Extend(f64::NAN);
        assert_eq!(F064SDUR.ceil(nan), Extended::PosInf);
    }

    #[test]
    fn f64_sdur_infinity_arms() {
        let pos_inf = ExtendedFloat::Extend(f64::INFINITY);
        assert_eq!(F064SDUR.ceil(pos_inf), Extended::PosInf);

        let neg_inf = ExtendedFloat::Extend(f64::NEG_INFINITY);
        assert_eq!(F064SDUR.ceil(neg_inf), Extended::Finite(StdDuration::ZERO));
    }

    #[test]
    fn f64_sdur_bot_top_arms() {
        assert_eq!(F064SDUR.ceil(ExtendedFloat::Bot), Extended::NegInf);
        assert_eq!(F064SDUR.ceil(ExtendedFloat::Top), Extended::PosInf);
        assert_eq!(F064SDUR.upper(Extended::NegInf), ExtendedFloat::Bot);
        assert_eq!(F064SDUR.upper(Extended::PosInf), ExtendedFloat::Top);
    }

    #[test]
    fn f64_sdur_max_sentinel_is_total() {
        let max = Extended::Finite(StdDuration::MAX);
        let sentinel = ExtendedFloat::Extend(StdDuration::MAX.as_secs_f64());

        assert_eq!(F064SDUR.upper(max), sentinel);
        assert_eq!(F064SDUR.ceil(sentinel), max);
        assert!(conn_laws::kernel_l(&F064SDUR, max));
    }

    #[test]
    fn f64_sdur_max_float_sentinel_is_total() {
        let sentinel = ExtendedFloat::Extend(StdDuration::MAX.as_secs_f64());

        assert_eq!(F064SDUR.ceil(sentinel), Extended::Finite(StdDuration::MAX));
        assert!(conn_laws::kernel_l(
            &F064SDUR,
            Extended::Finite(StdDuration::MAX)
        ));
    }

    #[test]
    fn f32_sdur_zero() {
        let zero = ExtendedFloat::Extend(0.0_f32);
        assert_eq!(F032SDUR.ceil(zero), Extended::Finite(StdDuration::ZERO));
    }

    #[test]
    fn f32_sdur_negative_input() {
        let neg = ExtendedFloat::Extend(-0.5_f32);
        assert_eq!(F032SDUR.ceil(neg), Extended::Finite(StdDuration::ZERO));
    }

    #[test]
    fn f32_sdur_nan_arms() {
        let nan = ExtendedFloat::Extend(f32::NAN);
        assert_eq!(F032SDUR.ceil(nan), Extended::PosInf);
    }

    #[test]
    fn f32_sdur_infinity_arms() {
        let pos_inf = ExtendedFloat::Extend(f32::INFINITY);
        assert_eq!(F032SDUR.ceil(pos_inf), Extended::PosInf);

        let neg_inf = ExtendedFloat::Extend(f32::NEG_INFINITY);
        assert_eq!(F032SDUR.ceil(neg_inf), Extended::Finite(StdDuration::ZERO));
    }

    #[test]
    fn f32_sdur_max_sentinel_is_total() {
        let max = Extended::Finite(StdDuration::MAX);
        let sentinel = ExtendedFloat::Extend(StdDuration::MAX.as_secs_f32());

        assert_eq!(F032SDUR.upper(max), sentinel);
        assert_eq!(F032SDUR.ceil(sentinel), max);
        assert!(conn_laws::kernel_l(&F032SDUR, max));
    }

    #[test]
    fn f32_sdur_max_float_sentinel_is_total() {
        let sentinel = ExtendedFloat::Extend(StdDuration::MAX.as_secs_f32());

        assert_eq!(F032SDUR.ceil(sentinel), Extended::Finite(StdDuration::MAX));
        assert!(conn_laws::kernel_l(
            &F032SDUR,
            Extended::Finite(StdDuration::MAX)
        ));
    }

    // ── F064SDUR / F032SDUR L-side battery (ConnL, hand-rolled) ──

    proptest! {
        #![proptest_config(ProptestConfig { cases: 64, .. ProptestConfig::default() })]
        #[test]
        fn f064sdur_galois_l(a in extended_float_f64(),
                             b in arb_extended_std_duration_bounded_f64()) {
            prop_assert!(conn_laws::galois_l(&F064SDUR, a, b));
        }
        #[test]
        fn f064sdur_closure_l(a in extended_float_f64()) {
            prop_assert!(conn_laws::closure_l(&F064SDUR, a));
        }
        #[test]
        fn f064sdur_kernel_l(b in arb_extended_std_duration_bounded_f64()) {
            prop_assert!(conn_laws::kernel_l(&F064SDUR, b));
        }
        #[test]
        fn f064sdur_monotone_l(a1 in extended_float_f64(), a2 in extended_float_f64()) {
            prop_assert!(conn_laws::monotone_l(&F064SDUR, a1, a2));
        }
        #[test]
        fn f064sdur_idempotent(a in extended_float_f64()) {
            prop_assert!(conn_laws::idempotent_l(&F064SDUR, a));
        }
        #[test]
        fn f032sdur_galois_l(a in extended_float_f32(),
                             b in arb_extended_std_duration_bounded_f32()) {
            prop_assert!(conn_laws::galois_l(&F032SDUR, a, b));
        }
        #[test]
        fn f032sdur_closure_l(a in extended_float_f32()) {
            prop_assert!(conn_laws::closure_l(&F032SDUR, a));
        }
        #[test]
        fn f032sdur_kernel_l(b in arb_extended_std_duration_bounded_f32()) {
            prop_assert!(conn_laws::kernel_l(&F032SDUR, b));
        }
        #[test]
        fn f032sdur_monotone_l(a1 in extended_float_f32(), a2 in extended_float_f32()) {
            prop_assert!(conn_laws::monotone_l(&F032SDUR, a1, a2));
        }
        #[test]
        fn f032sdur_idempotent(a in extended_float_f32()) {
            prop_assert!(conn_laws::idempotent_l(&F032SDUR, a));
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig {
            cases: 64,
            max_shrink_iters: 200,
            .. ProptestConfig::default()
        })]

        // Negative finite inputs project to ZERO under ceil — Galois-
        // forced because the unsigned rung has no representative below
        // ZERO and `inner(NegInf) = Bot` (synthetic source bottom).
        #[test]
        fn f64_sdur_negative_input_ceil_to_zero(v in -1.0e9_f64..0.0_f64) {
            let a = ExtendedFloat::Extend(v);
            prop_assert_eq!(F064SDUR.ceil(a), Extended::Finite(StdDuration::ZERO));
        }

        // Plateau invariant for F064SDUR's ceil walk: at any whole-second
        // StdDuration `d`, `v = d.as_secs_f64()` is exact and the f64
        // plateau around `v` brackets `d`. ceil walks down to the
        // smallest plateau member, which widens back to exactly `v` and
        // is ≤ `d`. (Plan 32 demoted F064SDUR to ConnL — `floor` removed
        // because the plateau structure is exactly what makes `inner`
        // non-injective.)
        #[test]
        fn f64_sdur_plateau(s in 0_u64..=1_000_000_000_u64) {
            let d = StdDuration::from_secs(s);
            let v = d.as_secs_f64();
            let a = ExtendedFloat::Extend(v);
            if let Extended::Finite(c) = F064SDUR.ceil(a) {
                prop_assert!(c <= d, "ceil={c:?} d={d:?}");
                prop_assert_eq!(c.as_secs_f64(), v);
            } else {
                panic!("expected Finite ceil at v={v}");
            }
        }

        #[test]
        fn f64_sdur_solve_matches_walk_in_safe_range(v in 1.0e-3_f64..1.0e6_f64) {
            let est = StdDuration::from_secs_f64(v);
            let est_widen = est.as_secs_f64();
            let (walk_z, _) = if est_widen >= v {
                f64_sdur_walks::descend_to_ceil(est, v)
            } else {
                f64_sdur_walks::ascend_to_ceil(est, v)
            };
            let (solve_z, steps) = f64_sdur_walks::solve_to_ceil(est, v);
            prop_assert_eq!(solve_z, walk_z);
            prop_assert!(steps <= 44, "solve_to_ceil took {steps} steps");
        }

        // f32 walk slows past ~1 s magnitude — see TDUR comment.
        #[test]
        fn f32_sdur_solve_matches_walk_in_safe_range(v in 1.0e-3_f32..1.0_f32) {
            let est = StdDuration::from_secs_f32(v);
            let est_widen = est.as_secs_f32();
            let (walk_z, _) = if est_widen >= v {
                f32_sdur_walks::descend_to_ceil(est, v)
            } else {
                f32_sdur_walks::ascend_to_ceil(est, v)
            };
            let (solve_z, steps) = f32_sdur_walks::solve_to_ceil(est, v);
            prop_assert_eq!(solve_z, walk_z);
            prop_assert!(steps <= 44, "solve_to_ceil took {steps} steps");
        }
    }

    // ── solve_to_ceil termination at walk-pathological magnitudes ─
    //
    // At `|v| ≥ 1e10` seconds the f64 plateau is wider than 2³⁰ ns,
    // so the legacy walk would take ≳10⁹ iterations. The solver
    // terminates in ≤ 44. `from_secs_f{64,32}` is well-defined here
    // (the StdDuration::MAX rim itself is unsafe — stdlib's
    // `from_secs_f64` panics on overflow — so the solver's behavior
    // at the absolute saturation rim is gated by the upstream
    // fast-path, not exercised here).

    #[test]
    fn f64_sdur_solve_terminates_walk_pathological_magnitude() {
        let _ = F064SDUR.ceil(ExtendedFloat::Extend(1.0e10_f64));
    }

    #[test]
    fn f32_sdur_solve_terminates_walk_pathological_magnitude() {
        // f32 ULP at 1e6 s is ~1e-1 s ≈ 10⁸ ns — already well into the
        // walk-pathological band.
        let _ = F032SDUR.ceil(ExtendedFloat::Extend(1.0e6_f32));
    }
}
