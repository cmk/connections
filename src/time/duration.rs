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

fn durnsecs_ceil(d: Duration) -> Extended<i64> {
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

fn durnsecs_inner(b: Extended<i64>) -> Duration {
    match b {
        Extended::NegInf => Duration::MIN,
        Extended::Finite(s) => Duration::seconds(s),
        Extended::PosInf => Duration::MAX,
    }
}

fn durnsecs_floor(d: Duration) -> Extended<i64> {
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

crate::triple! {
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
    pub DURNSECS : Duration => Extended<i64> {
        ceil:  durnsecs_ceil,
        inner: durnsecs_inner,
        floor: durnsecs_floor,
    }
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

    crate::law_battery! {
        mod durnsecs_laws,
        conn: DURNSECS,
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
fn f064durn_ceil(x: F064) -> Extended<Duration> {
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

fn f064durn_inner(d: Extended<Duration>) -> F064 {
    match d {
        Extended::NegInf => ExtendedFloat::Bot,
        Extended::Finite(dur) => ExtendedFloat::Extend(dur.as_seconds_f64()),
        Extended::PosInf => ExtendedFloat::Top,
    }
}

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
/// use connections::time::F064DURN;
/// use connections::float::ExtendedFloat;
/// use connections::extended::Extended;
/// use time::Duration;
///
/// // 0.5 seconds round-trips exactly.
/// let half = ExtendedFloat::Extend(0.5_f64);
/// assert_eq!(F064DURN.ceiling(half), Extended::Finite(Duration::milliseconds(500)));
/// assert_eq!(F064DURN.upper(Extended::Finite(Duration::milliseconds(500))),
///            ExtendedFloat::Extend(0.5));
///
/// // NaN saturates ceil to PosInf.
/// assert_eq!(F064DURN.ceiling(ExtendedFloat::Extend(f64::NAN)), Extended::PosInf);
/// ```
pub const F064DURN: crate::conn::ConnL<F064, Extended<Duration>> =
    crate::conn::Conn::new_l(f064durn_ceil, f064durn_inner);

fn f032durn_ceil(x: F032) -> Extended<Duration> {
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
    // See f064durn_ceil for rationale: `<=` so the round-trip
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

fn f032durn_inner(d: Extended<Duration>) -> F032 {
    match d {
        Extended::NegInf => ExtendedFloat::Bot,
        Extended::Finite(dur) => ExtendedFloat::Extend(dur.as_seconds_f32()),
        Extended::PosInf => ExtendedFloat::Top,
    }
}

/// `F032 → Extended<Duration>` — IEEE binary32 seconds ↔ Duration
/// (left-Galois).
///
/// Mirrors [`F064DURN`]'s shape with `f32` precision. The f32 plateau
/// (range of Durations mapping to the same `f32`) is much wider than
/// f64's: at magnitude ~1 s it is ~120 ns; at magnitude ~10³ s it is
/// ~10⁵ ns. Inner is non-injective on every plateau → not order-
/// reflecting → no true triple. Shipped as `ConnL`. (Plan 32.)
///
/// # Examples
///
/// ```rust
/// use connections::time::F032DURN;
/// use connections::float::ExtendedFloat;
/// use connections::extended::Extended;
/// use time::Duration;
///
/// // 1.0 s in f32 ceils to the bottom of the f32 plateau covering 1.0.
/// let one = ExtendedFloat::Extend(1.0_f32);
/// if let Extended::Finite(c) = F032DURN.ceiling(one) {
///     assert_eq!(c.as_seconds_f32(), 1.0_f32);
/// }
/// ```
pub const F032DURN: crate::conn::ConnL<F032, Extended<Duration>> =
    crate::conn::Conn::new_l(f032durn_ceil, f032durn_inner);

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

fn stdru064_ceil(d: Extended<StdDuration>) -> Extended<u64> {
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

fn stdru064_inner(b: Extended<u64>) -> Extended<StdDuration> {
    match b {
        Extended::NegInf => Extended::NegInf,
        Extended::PosInf => Extended::PosInf,
        Extended::Finite(s) => Extended::Finite(StdDuration::from_secs(s)),
    }
}

fn stdru064_floor(d: Extended<StdDuration>) -> Extended<u64> {
    match d {
        Extended::NegInf => Extended::NegInf,
        Extended::PosInf => Extended::PosInf,
        Extended::Finite(d) => Extended::Finite(d.as_secs()),
    }
}

crate::triple! {
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
    pub STDRU064 : Extended<StdDuration> => Extended<u64> {
        ceil:  stdru064_ceil,
        inner: stdru064_inner,
        floor: stdru064_floor,
    }
}

fn stdru128_ceil(d: Extended<StdDuration>) -> Extended<u128> {
    match d {
        Extended::NegInf => Extended::NegInf,
        Extended::PosInf => Extended::PosInf,
        Extended::Finite(d) => Extended::Finite(d.as_nanos()),
    }
}

fn stdru128_inner(b: Extended<u128>) -> Extended<StdDuration> {
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
/// **One-sided.** Shipped as `ConnL` rather than a `triple!` marker
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
/// use connections::time::STDRU128;
/// use connections::extended::Extended;
/// use std::time::Duration as StdDuration;
///
/// let one_and_a_half = StdDuration::from_nanos(1_500_000_000);
/// assert_eq!(STDRU128.ceiling(Extended::Finite(one_and_a_half)),
///            Extended::Finite(1_500_000_000_u128));
///
/// // `inner` is exact on the representable range and round-trips back.
/// let n = 1_500_000_000_u128;
/// assert_eq!(STDRU128.upper(Extended::Finite(n)),
///            Extended::Finite(StdDuration::from_nanos(n as u64)));
///
/// // Above StdDuration::MAX.as_nanos(), inner saturates to MAX.
/// assert_eq!(STDRU128.upper(Extended::Finite(u128::MAX)),
///            Extended::Finite(StdDuration::MAX));
/// ```
pub const STDRU128: crate::conn::ConnL<Extended<StdDuration>, Extended<u128>> =
    crate::conn::Conn::new_l(stdru128_ceil, stdru128_inner);

fn f064stdr_ceil(x: F064) -> Extended<StdDuration> {
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

fn f064stdr_inner(d: Extended<StdDuration>) -> F064 {
    match d {
        Extended::NegInf => ExtendedFloat::Bot,
        Extended::Finite(dur) => ExtendedFloat::Extend(dur.as_secs_f64()),
        Extended::PosInf => ExtendedFloat::Top,
    }
}

/// `F064 → Extended<StdDuration>` — IEEE binary64 seconds ↔
/// `std::time::Duration` (left-Galois).
///
/// Mirrors [`F064DURN`]'s walk-on-rung shape with an unsigned rung.
/// `inner` is non-injective on the f64 plateau (multiple StdDurations
/// map to the same f64 above ~104 days), so not order-reflecting and
/// no true triple. Shipped as `ConnL`. (Plan 32.)
///
/// # Examples
///
/// ```rust
/// use connections::time::F064STDR;
/// use connections::float::ExtendedFloat;
/// use connections::extended::Extended;
/// use std::time::Duration as StdDuration;
///
/// // 0.5 s round-trips exactly.
/// let half = ExtendedFloat::Extend(0.5_f64);
/// assert_eq!(F064STDR.ceiling(half), Extended::Finite(StdDuration::from_millis(500)));
///
/// // Negative float: ceil saturates up to ZERO (unsigned rung has
/// // no negative representative).
/// let neg = ExtendedFloat::Extend(-0.5_f64);
/// assert_eq!(F064STDR.ceiling(neg), Extended::Finite(StdDuration::ZERO));
/// ```
pub const F064STDR: crate::conn::ConnL<F064, Extended<StdDuration>> =
    crate::conn::Conn::new_l(f064stdr_ceil, f064stdr_inner);

fn f032stdr_ceil(x: F032) -> Extended<StdDuration> {
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

fn f032stdr_inner(d: Extended<StdDuration>) -> F032 {
    match d {
        Extended::NegInf => ExtendedFloat::Bot,
        Extended::Finite(dur) => ExtendedFloat::Extend(dur.as_secs_f32()),
        Extended::PosInf => ExtendedFloat::Top,
    }
}

/// `F032 → Extended<StdDuration>` — IEEE binary32 seconds ↔
/// `std::time::Duration` (left-Galois).
///
/// Mirrors [`F064STDR`] with `f32` precision. The f32 plateau makes
/// `inner` non-injective on every multi-Duration plateau, so no true
/// triple. Shipped as `ConnL`. (Plan 32.)
///
/// # Examples
///
/// ```rust
/// use connections::time::F032STDR;
/// use connections::float::ExtendedFloat;
/// use connections::extended::Extended;
/// use std::time::Duration as StdDuration;
///
/// // 1.0 s in f32 ceils to the bottom of the f32 plateau covering 1.0.
/// let one = ExtendedFloat::Extend(1.0_f32);
/// if let Extended::Finite(c) = F032STDR.ceiling(one) {
///     assert_eq!(c.as_secs_f32(), 1.0_f32);
/// }
/// ```
pub const F032STDR: crate::conn::ConnL<F032, Extended<StdDuration>> =
    crate::conn::Conn::new_l(f032stdr_ceil, f032stdr_inner);

#[cfg(test)]
mod float_durn_tests {
    use super::*;
    #[allow(unused_imports)]
    use crate::conn::{ViewL, ViewR};
    use crate::prop::arb::{
        arb_extended_duration_bounded_f32, arb_extended_duration_bounded_f64, extended_float_f32,
        extended_float_f64,
    };

    // ── F064DURN spot checks ────────────────────────────────────

    #[test]
    fn f64_zero() {
        let zero = ExtendedFloat::Extend(0.0_f64);
        assert_eq!(F064DURN.ceil(zero), Extended::Finite(Duration::ZERO));
        assert_eq!(F064DURN.inner(Extended::Finite(Duration::ZERO)), zero);
    }

    #[test]
    fn f64_half_second() {
        // 0.5 s is exactly representable in f64 and Duration.
        let half = ExtendedFloat::Extend(0.5_f64);
        let half_d = Duration::milliseconds(500);
        assert_eq!(F064DURN.ceil(half), Extended::Finite(half_d));
        assert_eq!(F064DURN.inner(Extended::Finite(half_d)), half);
    }

    #[test]
    fn f64_nan_arms() {
        let nan = ExtendedFloat::Extend(f64::NAN);
        assert_eq!(F064DURN.ceil(nan), Extended::PosInf);
    }

    #[test]
    fn f64_infinity_arms() {
        let pos_inf = ExtendedFloat::Extend(f64::INFINITY);
        assert_eq!(F064DURN.ceil(pos_inf), Extended::PosInf);

        let neg_inf = ExtendedFloat::Extend(f64::NEG_INFINITY);
        assert_eq!(F064DURN.ceil(neg_inf), Extended::Finite(Duration::MIN));
    }

    #[test]
    fn f64_bot_top_arms() {
        assert_eq!(F064DURN.ceil(ExtendedFloat::Bot), Extended::NegInf);
        assert_eq!(F064DURN.ceil(ExtendedFloat::Top), Extended::PosInf);
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

    // (Plan 32: F064DURN demoted to ConnL; floor() removed.)

    // ── F032DURN spot checks (ConnL — no floor()) ──────────────

    #[test]
    fn f32_zero() {
        let zero = ExtendedFloat::Extend(0.0_f32);
        assert_eq!(F032DURN.ceil(zero), Extended::Finite(Duration::ZERO));
        assert_eq!(F032DURN.inner(Extended::Finite(Duration::ZERO)), zero);
    }

    #[test]
    fn f32_one_second_in_plateau() {
        // f32 ULP at 1.0 ≈ 1.19e-7 s. ceil returns the bottom of the
        // plateau covering 1.0; widen back yields 1.0_f32 exactly.
        let one = ExtendedFloat::Extend(1.0_f32);
        if let Extended::Finite(cd) = F032DURN.ceil(one) {
            assert_eq!(cd.as_seconds_f32(), 1.0_f32);
        } else {
            panic!("ceil(1.0) should be Finite");
        }
    }

    #[test]
    fn f32_nan_arms() {
        let nan = ExtendedFloat::Extend(f32::NAN);
        assert_eq!(F032DURN.ceil(nan), Extended::PosInf);
    }

    #[test]
    fn f32_infinity_arms() {
        let pos_inf = ExtendedFloat::Extend(f32::INFINITY);
        assert_eq!(F032DURN.ceil(pos_inf), Extended::PosInf);

        let neg_inf = ExtendedFloat::Extend(f32::NEG_INFINITY);
        assert_eq!(F032DURN.ceil(neg_inf), Extended::Finite(Duration::MIN));
    }

    #[test]
    fn f32_ceil_min_secs_fast_path() {
        let v_min = ExtendedFloat::Extend(Duration::MIN.as_seconds_f32());
        assert_eq!(F032DURN.ceil(v_min), Extended::Finite(Duration::MIN));
    }

    #[test]
    fn f32_bot_top_arms() {
        assert_eq!(F032DURN.ceil(ExtendedFloat::Bot), Extended::NegInf);
        assert_eq!(F032DURN.ceil(ExtendedFloat::Top), Extended::PosInf);
        assert_eq!(F032DURN.inner(Extended::NegInf), ExtendedFloat::Bot);
        assert_eq!(F032DURN.inner(Extended::PosInf), ExtendedFloat::Top);
    }

    // ── Galois L-side battery — F064DURN / F032DURN ────────────
    //
    // F064DURN/F032DURN are ConnL (Plan 32 demoted them — `inner` is
    // non-injective on the f64/f32 plateau, so no true triple). Hand-
    // rolled proptest because law_battery! is marker-only and these
    // are bare ConnL consts. Float-side strategies bound `Extend(_)`
    // to |x| ≤ 1e9 (f64) / 10 (f32) so per-call walk budget stays
    // small.

    use crate::prop::conn as float_durn_conn_laws;
    use ::proptest::prelude::*;

    proptest! {
        #![proptest_config(ProptestConfig { cases: 64, .. ProptestConfig::default() })]
        #[test]
        fn f064durn_galois_l(a in extended_float_f64(),
                             b in arb_extended_duration_bounded_f64()) {
            prop_assert!(float_durn_conn_laws::galois_l(&F064DURN, a, b));
        }
        #[test]
        fn f064durn_closure_l(a in extended_float_f64()) {
            prop_assert!(float_durn_conn_laws::closure_l(&F064DURN, a));
        }
        #[test]
        fn f064durn_kernel_l(b in arb_extended_duration_bounded_f64()) {
            prop_assert!(float_durn_conn_laws::kernel_l(&F064DURN, b));
        }
        #[test]
        fn f032durn_galois_l(a in extended_float_f32(),
                             b in arb_extended_duration_bounded_f32()) {
            prop_assert!(float_durn_conn_laws::galois_l(&F032DURN, a, b));
        }
        #[test]
        fn f032durn_closure_l(a in extended_float_f32()) {
            prop_assert!(float_durn_conn_laws::closure_l(&F032DURN, a));
        }
        #[test]
        fn f032durn_kernel_l(b in arb_extended_duration_bounded_f32()) {
            prop_assert!(float_durn_conn_laws::kernel_l(&F032DURN, b));
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
        arb_extended_std_duration_bounded_f64, arb_extended_u64, arb_extended_u128,
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

    // ── STDRU128 spot checks (ConnL — no `.floor()` method) ──────

    #[test]
    fn stdru128_one_and_a_half() {
        let d = Extended::Finite(StdDuration::from_nanos(1_500_000_000));
        assert_eq!(STDRU128.ceil(d), Extended::Finite(1_500_000_000_u128));
    }

    #[test]
    fn stdru128_max_no_overflow() {
        let m = Extended::Finite(StdDuration::MAX);
        let m_nanos = StdDuration::MAX.as_nanos();
        assert_eq!(STDRU128.ceil(m), Extended::Finite(m_nanos));
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

    // Boundary kernel_l checks: with stdru128 demoted to ConnL, the
    // L-side adjunction holds on the FULL `Extended<u128>` rung
    // (including `Finite(n > max_nanos)` where the prior `triple!`
    // shape silently broke `kernel_r`). Pin those boundaries here
    // so future regressions surface immediately.
    #[test]
    fn stdru128_kernel_l_at_above_max_boundary() {
        let max_nanos = StdDuration::MAX.as_nanos();
        for b in [
            Extended::Finite(0_u128),
            Extended::Finite(max_nanos),
            Extended::Finite(max_nanos + 1),
            Extended::Finite(u128::MAX),
        ] {
            assert!(
                conn_laws::kernel_l(&STDRU128, b),
                "kernel_l violated at b = {:?}",
                b
            );
        }
    }

    // ── STDRU064 / STDRU128 Galois law battery ──────────────────

    crate::law_battery! {
        mod stdru064_laws,
        conn: STDRU064,
        fine:   arb_extended_std_duration(),
        coarse: arb_extended_u64(),
    }

    // STDRU128 is now ConnL — exercise L-side laws over the FULL
    // Extended<u128> rung (no in-range filter). The `coarse` strategy
    // `arb_extended_u128()` includes `Finite(u128::MAX)`, which under
    // the prior `triple!` shape would have surfaced a `kernel_r`
    // violation. With ConnL, only L-side laws apply and they hold on
    // the full domain. Pattern matches TIMENANO/OFDTNANO (bare ConnL
    // const, hand-rolled proptest! since law_battery! is marker-only).
    proptest! {
        #[test]
        fn stdru128_galois_l(d in arb_extended_std_duration(), b in arb_extended_u128()) {
            prop_assert!(conn_laws::galois_l(&STDRU128, d, b));
        }

        #[test]
        fn stdru128_closure_l(d in arb_extended_std_duration()) {
            prop_assert!(conn_laws::closure_l(&STDRU128, d));
        }

        #[test]
        fn stdru128_kernel_l(b in arb_extended_u128()) {
            prop_assert!(conn_laws::kernel_l(&STDRU128, b));
        }

        #[test]
        fn stdru128_monotone_l(a in arb_extended_std_duration(),
                               b in arb_extended_std_duration()) {
            prop_assert!(conn_laws::monotone_l(&STDRU128, a, b));
        }

        #[test]
        fn stdru128_idempotent(d in arb_extended_std_duration()) {
            prop_assert!(conn_laws::idempotent(&STDRU128, d));
        }

        // Bijection on the representable Finite range — for any rung
        // n ≤ MAX.as_nanos(), `ceil(inner(Finite(n))) == Finite(n)`.
        // (No `roundtrip_floor` test: STDRU128 is ConnL, so
        // `.floor()` doesn't exist.)
        #[test]
        fn stdru128_round_trip(n in 0_u128..=StdDuration::MAX.as_nanos()) {
            prop_assert!(conn_laws::roundtrip_ceil(&STDRU128, Extended::Finite(n)));
        }
    }

    // ── F064STDR / F032STDR spot checks (ConnL — no floor()) ──

    #[test]
    fn f64_stdr_zero() {
        let zero = ExtendedFloat::Extend(0.0_f64);
        assert_eq!(F064STDR.ceil(zero), Extended::Finite(StdDuration::ZERO));
        assert_eq!(F064STDR.inner(Extended::Finite(StdDuration::ZERO)), zero);
    }

    #[test]
    fn f64_stdr_half_second() {
        let half = ExtendedFloat::Extend(0.5_f64);
        let half_d = StdDuration::from_millis(500);
        assert_eq!(F064STDR.ceil(half), Extended::Finite(half_d));
        assert_eq!(F064STDR.inner(Extended::Finite(half_d)), half);
    }

    #[test]
    fn f64_stdr_inner_one_second() {
        let one_d = Extended::Finite(StdDuration::from_secs(1));
        assert_eq!(F064STDR.inner(one_d), ExtendedFloat::Extend(1.0_f64));
    }

    #[test]
    fn f64_stdr_negative_input() {
        let neg = ExtendedFloat::Extend(-0.5_f64);
        assert_eq!(F064STDR.ceil(neg), Extended::Finite(StdDuration::ZERO));
    }

    #[test]
    fn f64_stdr_nan_arms() {
        let nan = ExtendedFloat::Extend(f64::NAN);
        assert_eq!(F064STDR.ceil(nan), Extended::PosInf);
    }

    #[test]
    fn f64_stdr_infinity_arms() {
        let pos_inf = ExtendedFloat::Extend(f64::INFINITY);
        assert_eq!(F064STDR.ceil(pos_inf), Extended::PosInf);

        let neg_inf = ExtendedFloat::Extend(f64::NEG_INFINITY);
        assert_eq!(F064STDR.ceil(neg_inf), Extended::Finite(StdDuration::ZERO));
    }

    #[test]
    fn f64_stdr_bot_top_arms() {
        assert_eq!(F064STDR.ceil(ExtendedFloat::Bot), Extended::NegInf);
        assert_eq!(F064STDR.ceil(ExtendedFloat::Top), Extended::PosInf);
        assert_eq!(F064STDR.inner(Extended::NegInf), ExtendedFloat::Bot);
        assert_eq!(F064STDR.inner(Extended::PosInf), ExtendedFloat::Top);
    }

    #[test]
    fn f32_stdr_zero() {
        let zero = ExtendedFloat::Extend(0.0_f32);
        assert_eq!(F032STDR.ceil(zero), Extended::Finite(StdDuration::ZERO));
    }

    #[test]
    fn f32_stdr_negative_input() {
        let neg = ExtendedFloat::Extend(-0.5_f32);
        assert_eq!(F032STDR.ceil(neg), Extended::Finite(StdDuration::ZERO));
    }

    #[test]
    fn f32_stdr_nan_arms() {
        let nan = ExtendedFloat::Extend(f32::NAN);
        assert_eq!(F032STDR.ceil(nan), Extended::PosInf);
    }

    #[test]
    fn f32_stdr_infinity_arms() {
        let pos_inf = ExtendedFloat::Extend(f32::INFINITY);
        assert_eq!(F032STDR.ceil(pos_inf), Extended::PosInf);

        let neg_inf = ExtendedFloat::Extend(f32::NEG_INFINITY);
        assert_eq!(F032STDR.ceil(neg_inf), Extended::Finite(StdDuration::ZERO));
    }

    // ── F064STDR / F032STDR L-side battery (ConnL, hand-rolled) ──

    proptest! {
        #![proptest_config(ProptestConfig { cases: 64, .. ProptestConfig::default() })]
        #[test]
        fn f064stdr_galois_l(a in extended_float_f64(),
                             b in arb_extended_std_duration_bounded_f64()) {
            prop_assert!(conn_laws::galois_l(&F064STDR, a, b));
        }
        #[test]
        fn f064stdr_closure_l(a in extended_float_f64()) {
            prop_assert!(conn_laws::closure_l(&F064STDR, a));
        }
        #[test]
        fn f064stdr_kernel_l(b in arb_extended_std_duration_bounded_f64()) {
            prop_assert!(conn_laws::kernel_l(&F064STDR, b));
        }
        #[test]
        fn f032stdr_galois_l(a in extended_float_f32(),
                             b in arb_extended_std_duration_bounded_f32()) {
            prop_assert!(conn_laws::galois_l(&F032STDR, a, b));
        }
        #[test]
        fn f032stdr_closure_l(a in extended_float_f32()) {
            prop_assert!(conn_laws::closure_l(&F032STDR, a));
        }
        #[test]
        fn f032stdr_kernel_l(b in arb_extended_std_duration_bounded_f32()) {
            prop_assert!(conn_laws::kernel_l(&F032STDR, b));
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
        fn f64_stdr_negative_input_ceil_to_zero(v in -1.0e9_f64..0.0_f64) {
            let a = ExtendedFloat::Extend(v);
            prop_assert_eq!(F064STDR.ceil(a), Extended::Finite(StdDuration::ZERO));
        }

        // Plateau invariant for F064STDR's ceil walk: at any whole-second
        // StdDuration `d`, `v = d.as_secs_f64()` is exact and the f64
        // plateau around `v` brackets `d`. ceil walks down to the
        // smallest plateau member, which widens back to exactly `v` and
        // is ≤ `d`. (Plan 32 demoted F064STDR to ConnL — `floor` removed
        // because the plateau structure is exactly what makes `inner`
        // non-injective.)
        #[test]
        fn f64_stdr_plateau(s in 0_u64..=1_000_000_000_u64) {
            let d = StdDuration::from_secs(s);
            let v = d.as_secs_f64();
            let a = ExtendedFloat::Extend(v);
            if let Extended::Finite(c) = F064STDR.ceil(a) {
                prop_assert!(c <= d, "ceil={c:?} d={d:?}");
                prop_assert_eq!(c.as_secs_f64(), v);
            } else {
                panic!("expected Finite ceil at v={v}");
            }
        }
    }
}
