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
//!   whole seconds (`u64`) and exact nanoseconds (`u128`). Both
//!   endpoints are bare (no `Extended`); `ceil` saturates at the
//!   rung's max and `inner` synthetic-promotes the rung's max value
//!   to `StdDuration::MAX` so Galois L holds. SDURU064 is `conn_l!`
//!   only (no `floor` — the synthetic-promote breaks the dual law).
//! - [`F064SDUR`] / [`F032SDUR`] — IEEE float seconds ↔ `StdDuration`
//!   (codomain is bare `StdDuration`, not `Extended`). `ceil`
//!   saturates negative finites and `Bot` to `ZERO`, and `Top` /
//!   `+∞` / `NaN` to `MAX`. `inner` synthetic-promotes
//!   `StdDuration::MAX → ExtendedFloat::Top`.
//!
//! ## Signed vs unsigned rung
//!
//! | Conn family   | Source                  | Target          | Below-zero arm                |
//! |---------------|-------------------------|-----------------|-------------------------------|
//! | `TDURSECS`    | `Duration`              | `Extended<i64>` | rung NegInf at `MIN` overflow |
//! | `SDURU064/128`| `StdDuration`           | `u??`           | saturating ceil at the rung max |

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

def_walk_helpers!(
    f64_tdur_walks,
    f64,
    Duration,
    shift_duration,
    duration_to_f64
);
def_walk_helpers!(
    f32_tdur_walks,
    f32,
    Duration,
    shift_duration,
    duration_to_f32
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
    let est_widen = est.as_seconds_f64();
    let (z, _) = if est_widen >= v {
        f64_tdur_walks::descend_to_ceil(est, v)
    } else {
        f64_tdur_walks::ascend_to_ceil(est, v)
    };
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
    let est_widen = est.as_seconds_f32();
    let (z, _) = if est_widen >= v {
        f32_tdur_walks::descend_to_ceil(est, v)
    } else {
        f32_tdur_walks::ascend_to_ceil(est, v)
    };
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

def_walk_helpers!(
    f64_sdur_walks,
    f64,
    StdDuration,
    shift_std_duration,
    std_duration_to_f64
);
def_walk_helpers!(
    f32_sdur_walks,
    f32,
    StdDuration,
    shift_std_duration,
    std_duration_to_f32
);

fn sduru064_ceil(d: StdDuration) -> u64 {
    let w = d.as_secs();
    let n = d.subsec_nanos();
    if n > 0 { w.saturating_add(1) } else { w }
}

fn sduru064_inner(s: u64) -> StdDuration {
    // Synthetic-top promotion: `u64::MAX` maps to `StdDuration::MAX`
    // (= u64::MAX seconds + 999_999_999 nanos) rather than the natural
    // `from_secs(u64::MAX)` (= u64::MAX seconds + 0 nanos). This is
    // what makes Galois L hold across the `ceil` saturation arm: at
    // any `StdDuration` whose `.as_secs() == u64::MAX && subsec > 0`,
    // `ceil` saturates to `u64::MAX` and `inner(u64::MAX)` must round
    // back to a value `≥ d`, which only `MAX` does.
    if s == u64::MAX {
        StdDuration::MAX
    } else {
        StdDuration::from_secs(s)
    }
}

crate::conn_l! {
    /// `StdDuration → u64` — unsigned time span ↔ whole seconds
    /// (left-Galois).
    ///
    /// `ceil(d) = d.as_secs() + (subsec > 0 ? 1 : 0)`, saturating to
    /// `u64::MAX` at the `StdDuration::MAX` overflow boundary (where
    /// `as_secs() == u64::MAX` and `subsec > 0`).
    ///
    /// `inner(s) = StdDuration::from_secs(s)`, with synthetic-top
    /// promotion of `inner(u64::MAX) = StdDuration::MAX` so Galois L
    /// holds across the `ceil` saturation arm.
    ///
    /// **One-sided.** Demoted from `conn_k!` to `conn_l!` because the
    /// synthetic-top promotion breaks the dual `inner ⊣ floor`
    /// adjunction: `floor(MAX_d - 1ns) = u64::MAX` but
    /// `inner(u64::MAX) = MAX_d > MAX_d - 1ns`, so no `floor`
    /// satisfies both adjoints simultaneously.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::conn::ConnL;
    /// use connections::time::SDURU064;
    /// use std::time::Duration as StdDuration;
    ///
    /// let half = StdDuration::from_secs(5) + StdDuration::from_nanos(1);
    /// assert_eq!(SDURU064.ceil(half), 6);
    ///
    /// // Sub-second part at MAX saturates u64::MAX seconds → u64::MAX.
    /// assert_eq!(SDURU064.ceil(StdDuration::MAX), u64::MAX);
    ///
    /// // Round-trips via `upper` (same function as `inner`).
    /// assert_eq!(SDURU064.upper(42), StdDuration::from_secs(42));
    ///
    /// // Synthetic-top promotion at `u64::MAX`.
    /// assert_eq!(SDURU064.upper(u64::MAX), StdDuration::MAX);
    /// ```
    pub SDURU064 : StdDuration => u64 {
        ceil:  sduru064_ceil,
        inner: sduru064_inner,
    }
}

fn sduru128_ceil(d: StdDuration) -> u128 {
    d.as_nanos()
}

fn sduru128_inner(n: u128) -> StdDuration {
    let max_nanos = StdDuration::MAX.as_nanos();
    if n > max_nanos {
        return StdDuration::MAX;
    }
    let secs = (n / 1_000_000_000) as u64;
    let subsec = (n % 1_000_000_000) as u32;
    StdDuration::new(secs, subsec)
}

crate::conn_l! {
    /// `StdDuration → u128` — unsigned time span ↔ nanoseconds
    /// (left-Galois).
    ///
    /// On `[0, StdDuration::MAX.as_nanos()]` this is a bijection:
    /// `ceil(d) = d.as_nanos()` and `inner` round-trips back exactly.
    /// The widest `StdDuration` is `MAX`, whose `as_nanos()` is well
    /// within `u128` (≈ 1.84×10²⁸ vs `u128::MAX` ≈ 3.4×10³⁸), so
    /// `ceil` never overflows.
    ///
    /// Inputs `n > StdDuration::MAX.as_nanos()` clamp to
    /// `StdDuration::MAX` on `inner` (Galois pins this to the largest
    /// representative ≤ the synthetic top).
    ///
    /// **One-sided.** Shipped as `ConnL` rather than `conn_k!` because
    /// `inner` collapses the entire above-max plateau (`n > max_nanos`)
    /// onto `MAX` and so is not order-reflecting; the L-Galois
    /// adjunction `ceil ⊣ inner` holds on the full domain, but no
    /// `floor` admits the dual `inner ⊣ floor` simultaneously. See
    /// `doc/design.md` and Plan 32 for the rounding-sandwich derivation.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::time::SDURU128;
    /// use std::time::Duration as StdDuration;
    ///
    /// let one_and_a_half = StdDuration::from_nanos(1_500_000_000);
    /// assert_eq!(SDURU128.ceil(one_and_a_half), 1_500_000_000_u128);
    ///
    /// // `inner` is exact on the representable range and round-trips back.
    /// let n = 1_500_000_000_u128;
    /// assert_eq!(SDURU128.upper(n), StdDuration::from_nanos(n as u64));
    ///
    /// // Above StdDuration::MAX.as_nanos(), inner saturates to MAX.
    /// assert_eq!(SDURU128.upper(u128::MAX), StdDuration::MAX);
    /// ```
    pub SDURU128 : StdDuration => u128 {
        ceil:  sduru128_ceil,
        inner: sduru128_inner,
    }
}

fn f064sdur_ceil(x: F064) -> StdDuration {
    let v = match x {
        ExtendedFloat::Bot => return StdDuration::ZERO,
        ExtendedFloat::Top => return StdDuration::MAX,
        ExtendedFloat::Extend(v) => v,
    };
    if v.is_nan() {
        return StdDuration::MAX;
    }
    if v == f64::INFINITY {
        return StdDuration::MAX;
    }
    if v <= 0.0 {
        return StdDuration::ZERO;
    }
    let max_secs = StdDuration::MAX.as_secs_f64();
    if v >= max_secs {
        return StdDuration::MAX;
    }
    let est = StdDuration::from_secs_f64(v);
    let est_widen = est.as_secs_f64();
    let (z, _) = if est_widen >= v {
        f64_sdur_walks::descend_to_ceil(est, v)
    } else {
        f64_sdur_walks::ascend_to_ceil(est, v)
    };
    z
}

fn f064sdur_inner(d: StdDuration) -> F064 {
    // Synthetic-top promotion: `StdDuration::MAX` maps to `Top` rather
    // than `Extend(MAX.as_secs_f64())`. This is what makes Galois L
    // hold across the `ceil` saturation arm — inputs at or above
    // `MAX_secs_f64` saturate to `MAX`, and `inner(MAX)` must round
    // back to a value `≥ Top` for the equivalence to close.
    if d == StdDuration::MAX {
        ExtendedFloat::Top
    } else {
        ExtendedFloat::Extend(d.as_secs_f64())
    }
}

crate::conn_l! {
    /// `F064 → StdDuration` — IEEE binary64 seconds ↔ `std::time::Duration`
    /// (left-Galois).
    ///
    /// Mirrors [`F064TDUR`]'s walk-on-rung shape with an unsigned rung.
    /// `inner` is non-injective on the f64 plateau (multiple StdDurations
    /// map to the same f64 above ~104 days), so not order-reflecting and
    /// no true triple. Shipped as `ConnL`. (Plan 32.)
    ///
    /// `ceil` saturates negative finites and `Bot` to `StdDuration::ZERO`,
    /// and `Top` / `+∞` / `NaN` to `StdDuration::MAX`. `inner`
    /// synthetic-promotes `StdDuration::MAX → ExtendedFloat::Top`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::time::F064SDUR;
    /// use connections::float::ExtendedFloat;
    /// use std::time::Duration as StdDuration;
    ///
    /// // 0.5 s round-trips exactly.
    /// let half = ExtendedFloat::Extend(0.5_f64);
    /// assert_eq!(F064SDUR.ceil(half), StdDuration::from_millis(500));
    ///
    /// // Negative float: ceil saturates down to ZERO (unsigned rung).
    /// let neg = ExtendedFloat::Extend(-0.5_f64);
    /// assert_eq!(F064SDUR.ceil(neg), StdDuration::ZERO);
    ///
    /// // Top / +∞ / NaN saturate up to MAX.
    /// assert_eq!(F064SDUR.ceil(ExtendedFloat::Top), StdDuration::MAX);
    /// ```
    pub F064SDUR : F064 => StdDuration {
        ceil:  f064sdur_ceil,
        inner: f064sdur_inner,
    }
}

fn f032sdur_ceil(x: F032) -> StdDuration {
    let v = match x {
        ExtendedFloat::Bot => return StdDuration::ZERO,
        ExtendedFloat::Top => return StdDuration::MAX,
        ExtendedFloat::Extend(v) => v,
    };
    if v.is_nan() {
        return StdDuration::MAX;
    }
    if v == f32::INFINITY {
        return StdDuration::MAX;
    }
    if v <= 0.0 {
        return StdDuration::ZERO;
    }
    let max_secs = StdDuration::MAX.as_secs_f32();
    if v >= max_secs {
        return StdDuration::MAX;
    }
    let est = StdDuration::from_secs_f32(v);
    let est_widen = est.as_secs_f32();
    let (z, _) = if est_widen >= v {
        f32_sdur_walks::descend_to_ceil(est, v)
    } else {
        f32_sdur_walks::ascend_to_ceil(est, v)
    };
    z
}

fn f032sdur_inner(d: StdDuration) -> F032 {
    if d == StdDuration::MAX {
        ExtendedFloat::Top
    } else {
        ExtendedFloat::Extend(d.as_secs_f32())
    }
}

crate::conn_l! {
    /// `F032 → StdDuration` — IEEE binary32 seconds ↔ `std::time::Duration`
    /// (left-Galois).
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
    /// use std::time::Duration as StdDuration;
    ///
    /// // 1.0 s in f32 ceils to the bottom of the f32 plateau covering 1.0.
    /// let one = ExtendedFloat::Extend(1.0_f32);
    /// let c = F032SDUR.ceil(one);
    /// assert_eq!(c.as_secs_f32(), 1.0_f32);
    /// ```
    pub F032SDUR : F032 => StdDuration {
        ceil:  f032sdur_ceil,
        inner: f032sdur_inner,
    }
}

// ── Proof-only walk-step probes ─────────────────────────────────────
//
// Mirror the production `f???{tdur,sdur}_ceil` walk-entry but return
// `(z, steps)` from each walk helper instead of dropping `_steps`.
// Used by the Kani harnesses in `crate::kani_proofs::time_walk` to
// prove the iteration bound is ≤ 2 over the full non-fast-path
// finite domain. The shims deliberately omit the production
// fast-path checks (NaN / out-of-range / ±∞ / `<= min_secs`); the
// harness applies the matching `kani::assume`s.

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

#[cfg(test)]
mod float_tdur_tests {
    use super::*;
    #[allow(unused_imports)]
    use crate::conn::{ConnL, ConnR};
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
}

// ── SDUR* Conn tests ────────────────────────────────────────────

#[cfg(test)]
mod sdur_tests {
    use super::*;
    #[allow(unused_imports)]
    use crate::conn::ConnL;
    use crate::prop::arb::{
        arb_std_duration, arb_std_duration_bounded_f32, arb_std_duration_bounded_f64,
        extended_float_f32, extended_float_f64,
    };
    use crate::prop::conn as conn_laws;
    use proptest::prelude::*;

    // ── SDURU064 spot checks (ConnL — no `.floor()` method) ──────

    #[test]
    fn sduru064_zero() {
        assert_eq!(SDURU064.ceil(StdDuration::ZERO), 0_u64);
        assert_eq!(SDURU064.upper(0_u64), StdDuration::ZERO);
    }

    #[test]
    fn sduru064_positive_subsec_rounds_up() {
        let d = StdDuration::from_secs(5) + StdDuration::from_nanos(1);
        assert_eq!(SDURU064.ceil(d), 6_u64);
    }

    #[test]
    fn sduru064_max_saturates_ceil() {
        // MAX has subsec_nanos > 0 and as_secs() == u64::MAX, so ceil
        // saturates rather than overflowing.
        assert_eq!(SDURU064.ceil(StdDuration::MAX), u64::MAX);
    }

    #[test]
    fn sduru064_synthetic_top() {
        // `inner(u64::MAX)` returns `StdDuration::MAX` rather than
        // `from_secs(u64::MAX)` — the synthetic-top promotion that
        // makes Galois L hold across the saturation arm.
        assert_eq!(SDURU064.upper(u64::MAX), StdDuration::MAX);
        // Below the top, `inner` is the natural `from_secs`.
        assert_eq!(SDURU064.upper(42), StdDuration::from_secs(42));
    }

    // ── SDURU128 spot checks (ConnL — no `.floor()` method) ──────

    #[test]
    fn sduru128_one_and_a_half() {
        let d = StdDuration::from_nanos(1_500_000_000);
        assert_eq!(SDURU128.ceil(d), 1_500_000_000_u128);
    }

    #[test]
    fn sduru128_max_no_overflow() {
        let m_nanos = StdDuration::MAX.as_nanos();
        assert_eq!(SDURU128.ceil(StdDuration::MAX), m_nanos);
    }

    #[test]
    fn sduru128_inner_saturates_above_max() {
        assert_eq!(SDURU128.upper(u128::MAX), StdDuration::MAX);
        let above = StdDuration::MAX.as_nanos() + 1;
        assert_eq!(SDURU128.upper(above), StdDuration::MAX);
    }

    // Boundary kernel_l checks at the saturation plateau.
    #[test]
    fn sduru128_kernel_l_at_above_max_boundary() {
        let max_nanos = StdDuration::MAX.as_nanos();
        for b in [0_u128, max_nanos, max_nanos + 1, u128::MAX] {
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
        fine:   arb_std_duration(),
        coarse: any::<u64>(),
        subset: l_only,
    }

    crate::law_battery! {
        mod sduru128_laws,
        conn: SDURU128,
        fine:   arb_std_duration(),
        coarse: any::<u128>(),
        subset: l_only,
    }

    proptest! {
        // Bijection on the representable Finite range — for any rung
        // n ≤ MAX.as_nanos(), `ceil(inner(n)) == n`.
        #[test]
        fn sduru128_round_trip(n in 0_u128..=StdDuration::MAX.as_nanos()) {
            prop_assert!(conn_laws::roundtrip_ceil(&SDURU128, n));
        }
    }

    // ── F064SDUR / F032SDUR spot checks (ConnL — no floor()) ──

    #[test]
    fn f64_sdur_zero() {
        let zero = ExtendedFloat::Extend(0.0_f64);
        assert_eq!(F064SDUR.ceil(zero), StdDuration::ZERO);
        assert_eq!(F064SDUR.upper(StdDuration::ZERO), zero);
    }

    #[test]
    fn f64_sdur_half_second() {
        let half = ExtendedFloat::Extend(0.5_f64);
        let half_d = StdDuration::from_millis(500);
        assert_eq!(F064SDUR.ceil(half), half_d);
        assert_eq!(F064SDUR.upper(half_d), half);
    }

    #[test]
    fn f64_sdur_inner_one_second() {
        assert_eq!(
            F064SDUR.upper(StdDuration::from_secs(1)),
            ExtendedFloat::Extend(1.0_f64)
        );
    }

    #[test]
    fn f64_sdur_negative_input() {
        let neg = ExtendedFloat::Extend(-0.5_f64);
        assert_eq!(F064SDUR.ceil(neg), StdDuration::ZERO);
    }

    #[test]
    fn f64_sdur_nan_saturates_max() {
        let nan = ExtendedFloat::Extend(f64::NAN);
        assert_eq!(F064SDUR.ceil(nan), StdDuration::MAX);
    }

    #[test]
    fn f64_sdur_infinity_saturates() {
        let pos_inf = ExtendedFloat::Extend(f64::INFINITY);
        assert_eq!(F064SDUR.ceil(pos_inf), StdDuration::MAX);

        let neg_inf = ExtendedFloat::Extend(f64::NEG_INFINITY);
        assert_eq!(F064SDUR.ceil(neg_inf), StdDuration::ZERO);
    }

    #[test]
    fn f64_sdur_bot_top_saturates() {
        assert_eq!(F064SDUR.ceil(ExtendedFloat::Bot), StdDuration::ZERO);
        assert_eq!(F064SDUR.ceil(ExtendedFloat::Top), StdDuration::MAX);
    }

    #[test]
    fn f64_sdur_synthetic_top() {
        // `inner(StdDuration::MAX)` returns `Top`, not the natural
        // `Extend(MAX.as_secs_f64())`.
        assert_eq!(F064SDUR.upper(StdDuration::MAX), ExtendedFloat::Top);
    }

    #[test]
    fn f64_sdur_max_float_sentinel_is_total() {
        let sentinel = ExtendedFloat::Extend(StdDuration::MAX.as_secs_f64());

        assert_eq!(F064SDUR.ceil(sentinel), StdDuration::MAX);
        assert!(conn_laws::kernel_l(&F064SDUR, StdDuration::MAX));
    }

    #[test]
    fn f32_sdur_zero() {
        let zero = ExtendedFloat::Extend(0.0_f32);
        assert_eq!(F032SDUR.ceil(zero), StdDuration::ZERO);
    }

    #[test]
    fn f32_sdur_negative_input() {
        let neg = ExtendedFloat::Extend(-0.5_f32);
        assert_eq!(F032SDUR.ceil(neg), StdDuration::ZERO);
    }

    #[test]
    fn f32_sdur_nan_saturates_max() {
        let nan = ExtendedFloat::Extend(f32::NAN);
        assert_eq!(F032SDUR.ceil(nan), StdDuration::MAX);
    }

    #[test]
    fn f32_sdur_infinity_saturates() {
        let pos_inf = ExtendedFloat::Extend(f32::INFINITY);
        assert_eq!(F032SDUR.ceil(pos_inf), StdDuration::MAX);

        let neg_inf = ExtendedFloat::Extend(f32::NEG_INFINITY);
        assert_eq!(F032SDUR.ceil(neg_inf), StdDuration::ZERO);
    }

    #[test]
    fn f32_sdur_synthetic_top() {
        assert_eq!(F032SDUR.upper(StdDuration::MAX), ExtendedFloat::Top);
    }

    #[test]
    fn f32_sdur_max_float_sentinel_is_total() {
        let sentinel = ExtendedFloat::Extend(StdDuration::MAX.as_secs_f32());

        assert_eq!(F032SDUR.ceil(sentinel), StdDuration::MAX);
        assert!(conn_laws::kernel_l(&F032SDUR, StdDuration::MAX));
    }

    // ── F064SDUR / F032SDUR L-side battery (ConnL, hand-rolled) ──

    proptest! {
        #![proptest_config(ProptestConfig { cases: 64, .. ProptestConfig::default() })]
        #[test]
        fn f064sdur_galois_l(a in extended_float_f64(),
                             b in arb_std_duration_bounded_f64()) {
            prop_assert!(conn_laws::galois_l(&F064SDUR, a, b));
        }
        #[test]
        fn f064sdur_closure_l(a in extended_float_f64()) {
            prop_assert!(conn_laws::closure_l(&F064SDUR, a));
        }
        #[test]
        fn f064sdur_kernel_l(b in arb_std_duration_bounded_f64()) {
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
                             b in arb_std_duration_bounded_f32()) {
            prop_assert!(conn_laws::galois_l(&F032SDUR, a, b));
        }
        #[test]
        fn f032sdur_closure_l(a in extended_float_f32()) {
            prop_assert!(conn_laws::closure_l(&F032SDUR, a));
        }
        #[test]
        fn f032sdur_kernel_l(b in arb_std_duration_bounded_f32()) {
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
        // ZERO.
        #[test]
        fn f64_sdur_negative_input_ceil_to_zero(v in -1.0e9_f64..0.0_f64) {
            let a = ExtendedFloat::Extend(v);
            prop_assert_eq!(F064SDUR.ceil(a), StdDuration::ZERO);
        }

        // Plateau invariant for F064SDUR's ceil walk: at any whole-second
        // StdDuration `d`, `v = d.as_secs_f64()` is exact and the f64
        // plateau around `v` brackets `d`. ceil walks down to the
        // smallest plateau member, which widens back to exactly `v` and
        // is ≤ `d`.
        #[test]
        fn f64_sdur_plateau(s in 0_u64..=1_000_000_000_u64) {
            let d = StdDuration::from_secs(s);
            let v = d.as_secs_f64();
            let a = ExtendedFloat::Extend(v);
            let c = F064SDUR.ceil(a);
            prop_assert!(c <= d, "ceil={c:?} d={d:?}");
            prop_assert_eq!(c.as_secs_f64(), v);
        }
    }
}
