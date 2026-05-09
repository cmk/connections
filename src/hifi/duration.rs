//! `hifitime::Duration` connections.
//!
//! Hosts:
//!
//! - [`HDURNANO`] — `Extended<Duration> ↔ i128` total nanoseconds.
//!   Bijection on the Finite range `[Duration::MIN.total_nanoseconds(),
//!   Duration::MAX.total_nanoseconds()]`; `i128` values outside that
//!   range saturate the source side to `Extended::NegInf` /
//!   `Extended::PosInf`. Same shape as
//!   `ODTMNANO`: source-side `Extended`,
//!   plain `i128` rung. **One-sided ConnL.**
//!
//! - [`HDURSECS`] — `Extended<Duration> ↔ i64` whole seconds.
//!   `Duration::MAX.to_seconds().abs()` is ≈ 1.03 × 10¹⁴ s, well
//!   inside `i64`'s ±9.22 × 10¹⁸, so no rung-side overflow at the
//!   extremes; the whole-seconds value at MAX/MIN fits a plain `i64`.
//!   Sub-second source inputs round up via `floor = ceil` under
//!   `new_left`. Same shape as
//!   `ODTMSECS`. **One-sided ConnL.**
//!
//! - [`F064HDUR`] / [`F032HDUR`] — IEEE float seconds ↔ Duration.
//!   Walks happen on the Duration rung in 1 ns ULPs; ULP-bounded
//!   correction loops driven by the crate's `def_walk_helpers!`
//!   macro (see `crate::float`) handle the float-precision plateau
//!   where multiple Durations map to the same f-value. Direct port of
//!   `F064TDUR` /
//!   `F032TDUR`. **One-sided ConnL.**
//!
//! ## No two-sided `Extended`
//!
//! Per the project's "single-side `Extended`" rule (see
//! `doc/design.md` and the master integration plan): every Conn
//! here uses `Extended<…>` on **at most one** side. The integer
//! rungs (`i128` / `i64`) are wide enough to absorb the full
//! `Duration` range with a one-step saturation marker, so the
//! source side hosts the synthetic `NegInf` / `PosInf` arms. The
//! float bridges follow the existing `F???TDUR` shape: float on
//! the left (already extended via `ExtendedFloat`), `Extended<HD>`
//! on the right.

use crate::extended::Extended;
use crate::float::{ExtendedFloat, F032, F064, def_walk_helpers};
use hifitime::Duration as HD;

// ── Range bounds, computed once at runtime ─────────────────────
//
// HD::{MIN, MAX} are non-canonical sentinels: MIN's nanoseconds is
// 0 with the most-negative i16 century, while MAX uses
// nanoseconds == NANOSECONDS_PER_CENTURY (one past canonical) at the
// most-positive i16 century. Their `total_nanoseconds()` fits well
// inside i128 (≈ ±10²³ vs ±1.7 × 10³⁸ envelope), so `±1` saturation
// markers are safe.

#[inline]
fn hd_min_nanos() -> i128 {
    HD::MIN.total_nanoseconds()
}

#[inline]
fn hd_max_nanos() -> i128 {
    HD::MAX.total_nanoseconds()
}

#[inline]
fn hd_min_secs() -> i64 {
    // Integer-arithmetic derivation: `total_nanoseconds()` is `i128`
    // and exact, so `/ 1_000_000_000` followed by `as i64` is too
    // (the result is `≈ ±1.03 × 10¹⁴`, well inside `i64`'s
    // `±9.22 × 10¹⁸`). Going through `to_seconds() as i64` would
    // f64-cast a value at `±1.03 × 10²³` magnitude — far past `f64`'s
    // exact-integer range (`2⁵³ ≈ 9 × 10¹⁵`) — losing ones of seconds
    // of precision and producing an off-by-one boundary value. The
    // `roundtrip_ceil` proptest at the boundary catches this; the
    // integer path avoids it entirely. (Spotted in MR !63 review.)
    //
    // `total_nanoseconds()` for `HD::MIN` / `HD::MAX` is an **exact
    // multiple of 10⁹** (each `NANOSECONDS_PER_CENTURY` is 100 × 365.25
    // × 86400 × 10⁹ = 3 155 760 000 × 10⁹ ns, divisible by 10⁹), so
    // truncation-vs-floor doesn't matter at the boundary —
    // `hd_min_max_total_ns_divisible_by_billion` (test below) guards
    // this invariant. (MR !63 round-4 follow-up.)
    (HD::MIN.total_nanoseconds() / 1_000_000_000) as i64
}

#[inline]
fn hd_max_secs() -> i64 {
    // Same integer path as `hd_min_secs` — see its docs. `HD::MAX` is
    // a non-canonical sentinel (`nanoseconds == NANOSECONDS_PER_CENTURY`)
    // which makes the `to_seconds()` route especially fragile here.
    // The boundary is also exactly divisible by 10⁹ (same per-century
    // derivation as `hd_min_secs`).
    (HD::MAX.total_nanoseconds() / 1_000_000_000) as i64
}

// ── HDURNANO ─────────────────────────────────────────────────────

fn hdurnano_ceil(d: Extended<HD>) -> i128 {
    let max_n = hd_max_nanos();
    match d {
        // Asymmetric saturation: NegInf ceils to the rung's absolute
        // minimum so `ceil(NegInf) ≤ b` holds for **all** `b`, matching
        // the Galois RHS `NegInf ≤ inner(b)` which is always true.
        // PosInf ceils to `max_n + 1`, the smallest `b` such that
        // `inner(b) = PosInf`. Mirrors `ODTMNANO`'s shape exactly
        // (see time/offset.rs:123-138 for the derivation).
        Extended::NegInf => i128::MIN,
        Extended::Finite(d) => d.total_nanoseconds(),
        Extended::PosInf => max_n + 1,
    }
}

fn hdurnano_inner(n: i128) -> Extended<HD> {
    let min_n = hd_min_nanos();
    let max_n = hd_max_nanos();
    if n < min_n {
        Extended::NegInf
    } else if n > max_n {
        Extended::PosInf
    } else {
        Extended::Finite(HD::from_total_nanoseconds(n))
    }
}

crate::conn_l! {
    /// `Extended<hifitime::Duration> → i128` — total nanoseconds.
    ///
    /// One-sided left-Galois Conn (`Conn::new_l(ceil, inner)`).
    /// On the Finite portion this is an exact bijection: `ceil` is
    /// `Duration::total_nanoseconds`, `inner` is
    /// `Duration::from_total_nanoseconds` (which always normalizes).
    ///
    /// Saturation (asymmetric — see `ODTMNANO` for the same shape):
    /// - `ceil(NegInf) = i128::MIN`
    /// - `ceil(PosInf) = HD::MAX.total_nanoseconds() + 1`
    /// - `inner(n)` outside `[MIN.total_ns(), MAX.total_ns()]`
    ///   saturates to `Extended::NegInf` / `Extended::PosInf` rather
    ///   than collapsing onto `Finite(MIN)` / `Finite(MAX)` — the
    ///   collapse would break order-reflection on the synthetic
    ///   extremes (which is exactly why this is shipped as `ConnL`
    ///   rather than `conn_k!`, mirroring `ODTMNANO`).
    ///
    /// `i128` is wide enough for the full HD range:
    /// `HD::MAX.total_nanoseconds()` ≈ 1.03 × 10²³, comfortably
    /// inside `i128`'s ±1.7 × 10³⁸ envelope.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::hifi::HDURNANO;
    /// use connections::extended::Extended;
    /// use hifitime::Duration as HDuration;
    ///
    /// // 1.5 s ↔ 1.5 × 10⁹ ns, exactly.
    /// let d = HDuration::from_seconds(1.5);
    /// assert_eq!(HDURNANO.ceil(Extended::Finite(d)), 1_500_000_000_i128);
    /// assert_eq!(HDURNANO.upper(1_500_000_000_i128), Extended::Finite(d));
    ///
    /// // Out-of-range nanoseconds saturate the source side.
    /// assert_eq!(HDURNANO.upper(i128::MAX), Extended::PosInf);
    /// assert_eq!(HDURNANO.upper(i128::MIN), Extended::NegInf);
    /// ```
    pub HDURNANO : Extended<HD> => i128 {
        ceil:  hdurnano_ceil,
        inner: hdurnano_inner,
    }
}

// ── HDURSECS ─────────────────────────────────────────────────────

fn hdursecs_ceil(d: Extended<HD>) -> i64 {
    let max_s = hd_max_secs();
    match d {
        // Asymmetric saturation, see hdurnano_ceil for the derivation.
        Extended::NegInf => i64::MIN,
        Extended::Finite(d) => {
            let total_ns = d.total_nanoseconds();
            // i128-safe arithmetic: split into seconds + sub-second
            // remainder so the i64 result fits under all canonical
            // HD values. div_euclid / rem_euclid give the
            // mathematician's floor-division semantics — for
            // negative total_ns the sub-second residue lives in
            // `[0, 10⁹)`, matching how we then "round up" sub-second
            // tails toward +∞ (i.e., this is ceiling division —
            // `s_floor + 1` is *toward* zero for negatives, *away*
            // from zero for positives). (MR !63 round-5.)
            let one_billion: i128 = 1_000_000_000;
            let s_floor: i64 = total_ns.div_euclid(one_billion) as i64;
            let sub: i128 = total_ns.rem_euclid(one_billion);
            if sub > 0 {
                // The s_floor + 1 saturation can't overflow i64 within
                // the HD range: max canonical s_floor ≈ 1.03e14 ≪ i64::MAX.
                s_floor + 1
            } else {
                s_floor
            }
        }
        Extended::PosInf => max_s + 1,
    }
}

fn hdursecs_inner(s: i64) -> Extended<HD> {
    let min_s = hd_min_secs();
    let max_s = hd_max_secs();
    if s < min_s {
        Extended::NegInf
    } else if s > max_s {
        Extended::PosInf
    } else {
        // i64 → exact i128 nanoseconds, then HD::from_total_nanoseconds
        // (avoids the f64 round-trip that HD::from_seconds would do).
        Extended::Finite(HD::from_total_nanoseconds((s as i128) * 1_000_000_000))
    }
}

crate::conn_l! {
    /// `Extended<hifitime::Duration> → i64` — whole seconds, sub-second
    /// fractions ceiled up to the next whole second.
    ///
    /// One-sided left-Galois Conn (`Conn::new_l(ceil, inner)`).
    /// `inner` saturates `i64` outside `[MIN.to_secs(), MAX.to_secs()]`
    /// onto `Extended::NegInf` / `Extended::PosInf`, making it
    /// non-order-reflecting at the synthetic extremes. The constructor
    /// wires `floor = ceil` as a fn pointer so `floor(a) ≤ ceil(a)`
    /// holds structurally.
    ///
    /// **Behavioral note on rounding:** `ceil(Finite(d))` is
    /// **ceiling division** (rounds toward +∞), uniform across both
    /// signs. On a positive sub-second residue (e.g. `5.000_000_001 s`),
    /// the result is `s_floor + 1 = 6`. On a negative sub-second residue
    /// (e.g. `−5.000_000_001 s`), `div_euclid` + `rem_euclid` produce a
    /// `s_floor = -6` and a positive `sub` of `999_999_999`, so the
    /// result is `s_floor + 1 = -5` — still toward +∞, not away from
    /// zero. Callers who need the truncating direction can compute
    /// `d.total_nanoseconds() / 1_000_000_000` directly.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::hifi::HDURSECS;
    /// use connections::extended::Extended;
    /// use hifitime::Duration as HDuration;
    ///
    /// // Exact second.
    /// let five = HDuration::from_seconds(5.0);
    /// assert_eq!(HDURSECS.ceil(Extended::Finite(five)), 5_i64);
    ///
    /// // Sub-second past 5 s: ceil rounds up.
    /// let mid = HDuration::from_total_nanoseconds(5 * 1_000_000_000 + 1);
    /// assert_eq!(HDURSECS.ceil(Extended::Finite(mid)), 6_i64);
    /// ```
    pub HDURSECS : Extended<HD> => i64 {
        ceil:  hdursecs_ceil,
        inner: hdursecs_inner,
    }
}

// ── Duration ULP shift + float widen helpers ─────────────────────
//
// Used by `def_walk_helpers!` to drive the F???HDUR bridges: walks
// happen on the Duration rung (1 ns increments via `shift_hd`) with
// comparisons in float space (`Duration::to_seconds` for f64; the
// f32 variant casts).

/// Shift `d` by `n` nanoseconds. Saturates at `HD::MIN` / `HD::MAX`
/// so the macro's "if shift didn't move, terminate" guard fires
/// correctly at the boundaries.
pub(crate) fn shift_hd(n: i32, d: HD) -> HD {
    let cur_ns = d.total_nanoseconds();
    let new_ns = cur_ns.saturating_add(n as i128);
    let max_ns = hd_max_nanos();
    let min_ns = hd_min_nanos();
    if new_ns >= max_ns {
        HD::MAX
    } else if new_ns <= min_ns {
        HD::MIN
    } else {
        HD::from_total_nanoseconds(new_ns)
    }
}

#[inline]
fn hd_to_f64(d: HD) -> f64 {
    d.to_seconds()
}

#[inline]
fn hd_to_f32(d: HD) -> f32 {
    d.to_seconds() as f32
}

/// Total nanoseconds as i128 — `HD` natively exposes this.
#[inline]
pub(crate) fn hd_to_ns(d: HD) -> i128 {
    d.total_nanoseconds()
}

/// Saturating reconstruction; clamps at `HD::{MIN,MAX}`.
#[inline]
pub(crate) fn hd_from_ns(n: i128) -> HD {
    let max_ns = hd_max_nanos();
    let min_ns = hd_min_nanos();
    if n >= max_ns {
        HD::MAX
    } else if n <= min_ns {
        HD::MIN
    } else {
        HD::from_total_nanoseconds(n)
    }
}

def_walk_helpers!(
    f64_hdur_walks,
    f64,
    HD,
    shift_hd,
    hd_to_f64,
    hd_to_ns,
    hd_from_ns
);
def_walk_helpers!(
    f32_hdur_walks,
    f32,
    HD,
    shift_hd,
    hd_to_f32,
    hd_to_ns,
    hd_from_ns
);

fn f064hdur_ceil(x: F064) -> Extended<HD> {
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
        return Extended::Finite(HD::MIN);
    }
    // Bounds via integer arithmetic — `HD::MAX.to_seconds()` directly
    // would f64-cast a `±10²³`-magnitude value past the exact-integer
    // range (`2⁵³ ≈ 9 × 10¹⁵`) and could miss out-of-range inputs by
    // boundary rounding error. `hd_{min,max}_secs() as f64` casts an
    // i64 already at `±10¹⁴` (well inside f64-exact-int range) so the
    // cast is precise. Same fix shape as the round-2 migration of
    // `hd_{min,max}_secs` for `HDURSECS`. (MR !63 round-3 review.)
    let max_secs = hd_max_secs() as f64;
    let min_secs = hd_min_secs() as f64;
    if v > max_secs {
        return Extended::PosInf;
    }
    // Same `<=` rationale as F064TDUR (see time/duration.rs): when
    // `v == min_secs` (the round-trip `inner(ceil(NEG_INFINITY))` value),
    // HD::MIN IS the correct ceil. The walk would converge to MIN
    // anyway but takes ~10¹² nanosecond steps at this magnitude (the
    // f64 plateau at |v| ≈ 1e14 is wide). Fast-path it.
    if v <= min_secs {
        return Extended::Finite(HD::MIN);
    }
    let est = HD::from_seconds(v);
    let (z, _) = f64_hdur_walks::solve_to_ceil(est, v);
    Extended::Finite(z)
}

fn f064hdur_inner(d: Extended<HD>) -> F064 {
    match d {
        Extended::NegInf => ExtendedFloat::Bot,
        Extended::Finite(d) => ExtendedFloat::Extend(d.to_seconds()),
        Extended::PosInf => ExtendedFloat::Top,
    }
}

crate::conn_l! {
    /// `F064 → Extended<hifitime::Duration>` — IEEE binary64 seconds
    /// ↔ Duration (left-Galois).
    ///
    /// Walks happen on the Duration rung (1 ns ULPs); the float side
    /// is the comparison frame. `inner(Finite(d))` widens via
    /// `Duration::to_seconds()`, which is non-injective above
    /// |Duration| > 2⁵³ ns ≈ 104 days (multiple Durations map to the
    /// same f64). That non-injectivity → not order-reflecting → no
    /// true triple, so shipped as `ConnL` (matches the rationale for
    /// `F064TDUR`, Plan 32).
    ///
    /// Saturation arms:
    /// - `ceil(Bot)` = `NegInf`.
    /// - `ceil(Top)` = `PosInf`.
    /// - `ceil(Extend(NaN))` = `PosInf`.
    /// - `ceil(Extend(+∞))` = `PosInf`. Symmetric for `−∞` →
    ///   `Finite(HD::MIN)`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::hifi::F064HDUR;
    /// use connections::float::ExtendedFloat;
    /// use connections::extended::Extended;
    /// use hifitime::Duration as HDuration;
    ///
    /// // 0.5 s round-trips exactly.
    /// let half = ExtendedFloat::Extend(0.5_f64);
    /// assert_eq!(
    ///     F064HDUR.ceil(half),
    ///     Extended::Finite(HDuration::from_seconds(0.5)),
    /// );
    ///
    /// // NaN saturates ceil to PosInf.
    /// assert_eq!(F064HDUR.ceil(ExtendedFloat::Extend(f64::NAN)), Extended::PosInf);
    /// ```
    pub F064HDUR : F064 => Extended<HD> {
        ceil:  f064hdur_ceil,
        inner: f064hdur_inner,
    }
}

fn f032hdur_ceil(x: F032) -> Extended<HD> {
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
        return Extended::Finite(HD::MIN);
    }
    // Same integer-derived bounds as `f064hdur_ceil` — see its
    // commentary. The trailing `as f32` cast is lossy on its own (f32
    // ULP at `±10¹⁴` is much wider than the i64 unit), but starting
    // from the integer-correct `hd_{min,max}_secs()` rules out the
    // additive boundary error from the f64 detour. (MR !63 round-3.)
    let max_secs = hd_max_secs() as f32;
    let min_secs = hd_min_secs() as f32;
    if v > max_secs {
        return Extended::PosInf;
    }
    if v <= min_secs {
        return Extended::Finite(HD::MIN);
    }
    let est = HD::from_seconds(v as f64);
    let (z, _) = f32_hdur_walks::solve_to_ceil(est, v);
    Extended::Finite(z)
}

fn f032hdur_inner(d: Extended<HD>) -> F032 {
    match d {
        Extended::NegInf => ExtendedFloat::Bot,
        Extended::Finite(d) => ExtendedFloat::Extend(d.to_seconds() as f32),
        Extended::PosInf => ExtendedFloat::Top,
    }
}

crate::conn_l! {
    /// `F032 → Extended<hifitime::Duration>` — IEEE binary32 seconds
    /// ↔ Duration (left-Galois).
    ///
    /// Mirrors [`F064HDUR`]'s walk-on-rung shape with f32 precision.
    /// The f32 plateau (range of Durations mapping to the same `f32`)
    /// is much wider than f64's — at magnitude ~1 s it is ~120 ns;
    /// at magnitude ~10³ s it is ~10⁵ ns — so `inner` is non-
    /// injective on every plateau and no true triple exists.
    /// Shipped as `ConnL`. (Plan 32 rationale.)
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::hifi::F032HDUR;
    /// use connections::float::ExtendedFloat;
    /// use connections::extended::Extended;
    /// use hifitime::Duration as HDuration;
    ///
    /// // 1.0 s in f32 ceils to a Duration whose `to_seconds() as f32`
    /// // round-trips back to 1.0_f32.
    /// let one = ExtendedFloat::Extend(1.0_f32);
    /// if let Extended::Finite(c) = F032HDUR.ceil(one) {
    ///     assert_eq!(c.to_seconds() as f32, 1.0_f32);
    /// } else {
    ///     panic!("ceil(1.0) should be Finite");
    /// }
    /// ```
    pub F032HDUR : F032 => Extended<HD> {
        ceil:  f032hdur_ceil,
        inner: f032hdur_inner,
    }
}

// ── Proof-only walk + solver step probes ───────────────────────────
//
// `*_walk_steps_for_proof` calls the legacy ULP walk (still emitted
// by the macro and called from this module's
// `*_solve_matches_walk_in_safe_range` proptest cross-checks);
// `*_solve_steps_for_proof` calls `solve_to_ceil`. Each has a
// matching pair of harnesses in `crate::kani_proofs::hifi_walk` —
// see the time/duration.rs banner for the full rationale on
// keeping both. Fast-paths are omitted; matching `kani::assume`s
// live in the harnesses.

#[cfg(kani)]
pub(crate) fn f64_hdur_ceil_walk_steps_for_proof(v: f64) -> (HD, u32) {
    let est = HD::from_seconds(v);
    let est_widen = est.to_seconds();
    if est_widen >= v {
        f64_hdur_walks::descend_to_ceil(est, v)
    } else {
        f64_hdur_walks::ascend_to_ceil(est, v)
    }
}

#[cfg(kani)]
pub(crate) fn f32_hdur_ceil_walk_steps_for_proof(v: f32) -> (HD, u32) {
    let est = HD::from_seconds(v as f64);
    let est_widen = est.to_seconds() as f32;
    if est_widen >= v {
        f32_hdur_walks::descend_to_ceil(est, v)
    } else {
        f32_hdur_walks::ascend_to_ceil(est, v)
    }
}

#[cfg(kani)]
pub(crate) fn f64_hdur_ceil_solve_steps_for_proof(v: f64) -> (HD, u32) {
    let est = HD::from_seconds(v);
    f64_hdur_walks::solve_to_ceil(est, v)
}

#[cfg(kani)]
pub(crate) fn f32_hdur_ceil_solve_steps_for_proof(v: f32) -> (HD, u32) {
    let est = HD::from_seconds(v as f64);
    f32_hdur_walks::solve_to_ceil(est, v)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[allow(unused_imports)]
    use crate::conn::{ConnL, ConnR};
    use crate::prop::arb::{
        arb_extended_hifi_duration, arb_extended_hifi_duration_bounded_f32,
        arb_extended_hifi_duration_bounded_f64, arb_hifi_duration, arb_hifi_total_nanos_in_range,
        arb_hifi_total_secs_in_range, extended_float_f32, extended_float_f64,
    };
    use crate::prop::{conn as conn_laws, lattice as lattice_laws};
    use proptest::prelude::*;

    // Sanity-guards the `hd_min_secs` / `hd_max_secs` derivation: if
    // hifitime ever introduced a non-second-aligned MIN / MAX, the
    // i128-truncation `total_nanoseconds() / 1_000_000_000` would silently
    // disagree with floor-division and the `roundtrip_ceil` boundary
    // would slip by one second. (MR !63 round-4 follow-up.)
    #[test]
    fn hd_min_max_total_ns_divisible_by_billion() {
        assert_eq!(HD::MIN.total_nanoseconds() % 1_000_000_000, 0);
        assert_eq!(HD::MAX.total_nanoseconds() % 1_000_000_000, 0);
    }

    // ── Preorder laws on `hifitime::Duration` ──────────────────

    mod hifi_duration_preorder {
        use super::*;
        #[allow(unused_imports)]
        use crate::conn::{ConnL, ConnR};

        proptest! {
            #[test]
            fn reflexive(x in arb_hifi_duration()) {
                prop_assert!(lattice_laws::lattice_reflexive(&x));
            }

            #[test]
            fn transitive(x in arb_hifi_duration(),
                          y in arb_hifi_duration(),
                          z in arb_hifi_duration()) {
                prop_assert!(lattice_laws::lattice_transitive(&x, &y, &z));
            }

            #[test]
            fn antisymmetric(x in arb_hifi_duration(), y in arb_hifi_duration()) {
                prop_assert!(lattice_laws::lattice_antisymmetric(&x, &y));
            }

            #[test]
            fn bot(x in arb_hifi_duration()) {
                prop_assert!(lattice_laws::lattice_bot(&HD::MIN, &x));
            }

            #[test]
            fn top(x in arb_hifi_duration()) {
                prop_assert!(lattice_laws::lattice_top(&HD::MAX, &x));
            }
        }
    }

    // ── HDURNANO spot checks ────────────────────────────────────

    #[test]
    fn hdurnano_zero() {
        let z = Extended::Finite(HD::ZERO);
        assert_eq!(HDURNANO.ceil(z), 0_i128);
        assert_eq!(HDURNANO.upper(0_i128), z);
    }

    #[test]
    fn hdurnano_one_ns_round_trip() {
        let one = Extended::Finite(HD::EPSILON);
        assert_eq!(HDURNANO.ceil(one), 1_i128);
        assert_eq!(HDURNANO.upper(1_i128), one);
    }

    #[test]
    fn hdurnano_neg_one_ns_round_trip() {
        let neg = Extended::Finite(HD::MIN_NEGATIVE);
        assert_eq!(HDURNANO.ceil(neg), -1_i128);
        assert_eq!(HDURNANO.upper(-1_i128), neg);
    }

    #[test]
    fn hdurnano_min_max_round_trip() {
        let min_n = HD::MIN.total_nanoseconds();
        let max_n = HD::MAX.total_nanoseconds();
        assert_eq!(HDURNANO.ceil(Extended::Finite(HD::MIN)), min_n);
        assert_eq!(HDURNANO.ceil(Extended::Finite(HD::MAX)), max_n);
        assert_eq!(HDURNANO.upper(min_n), Extended::Finite(HD::MIN));
        assert_eq!(HDURNANO.upper(max_n), Extended::Finite(HD::MAX));
    }

    #[test]
    fn hdurnano_saturation_extremes() {
        assert_eq!(HDURNANO.upper(i128::MAX), Extended::PosInf);
        assert_eq!(HDURNANO.upper(i128::MIN), Extended::NegInf);

        let max_n = HD::MAX.total_nanoseconds();
        assert_eq!(HDURNANO.ceil(Extended::PosInf), max_n + 1);
        // Asymmetric: ceil(NegInf) is the rung's absolute min, not
        // `min_n - 1`. See the Conn doc for the Galois-law derivation.
        assert_eq!(HDURNANO.ceil(Extended::NegInf), i128::MIN);
    }

    // ── HDURSECS spot checks ────────────────────────────────────

    #[test]
    fn hdursecs_zero() {
        let z = Extended::Finite(HD::ZERO);
        assert_eq!(HDURSECS.ceil(z), 0_i64);
        assert_eq!(HDURSECS.upper(0_i64), z);
    }

    #[test]
    fn hdursecs_positive_subsec_rounds_up() {
        let d = Extended::Finite(HD::from_total_nanoseconds(5 * 1_000_000_000 + 1));
        assert_eq!(HDURSECS.ceil(d), 6_i64);
    }

    #[test]
    fn hdursecs_negative_subsec_rounds_toward_zero() {
        // -5.000_000_001 s → ceil rounds toward zero (the next-larger
        // whole second) under div_euclid/rem_euclid semantics.
        let d = Extended::Finite(HD::from_total_nanoseconds(-(5 * 1_000_000_000 + 1)));
        assert_eq!(HDURSECS.ceil(d), -5_i64);
    }

    #[test]
    fn hdursecs_synthetic_arms() {
        // Use the same integer-arithmetic derivation as `hd_max_secs`
        // — `HD::MAX.to_seconds() as i64` is the lossy f64-cast path
        // the helper was migrated off of (MR !63 round 1).
        let max_s = (HD::MAX.total_nanoseconds() / 1_000_000_000) as i64;
        assert_eq!(HDURSECS.ceil(Extended::NegInf), i64::MIN);
        assert_eq!(HDURSECS.ceil(Extended::PosInf), max_s + 1);
        assert_eq!(HDURSECS.upper(i64::MIN), Extended::NegInf);
        assert_eq!(HDURSECS.upper(i64::MAX), Extended::PosInf);
    }

    // Boundary spot check: `inner` flips to NegInf/PosInf at exactly
    // `min_s - 1` / `max_s + 1`, which is also exactly where `galois_l`
    // is most likely to fail. (MR !63 round-3 follow-up — these can't
    // live in `arb_hifi_total_secs_in_range` because that strategy
    // feeds `roundtrip_ceil`, which would fail at saturation values.)
    #[test]
    fn hdursecs_inner_saturation_boundary() {
        let min_s = (HD::MIN.total_nanoseconds() / 1_000_000_000) as i64;
        let max_s = (HD::MAX.total_nanoseconds() / 1_000_000_000) as i64;
        // In-range endpoints stay Finite.
        assert!(matches!(HDURSECS.upper(min_s), Extended::Finite(_)));
        assert!(matches!(HDURSECS.upper(max_s), Extended::Finite(_)));
        // One step past saturates symmetrically.
        assert_eq!(HDURSECS.upper(min_s - 1), Extended::NegInf);
        assert_eq!(HDURSECS.upper(max_s + 1), Extended::PosInf);
    }

    // ── Galois law batteries — HDURNANO / HDURSECS (one-sided L) ─
    //
    // ODTMNANO/ODTMSECS template: hand-rolled proptest!s since
    // law_battery! is for marker-struct `conn_k!`-shaped Conns and
    // these are bare `pub const`s.

    proptest! {
        #[test]
        fn hdurnano_galois_l(d in arb_extended_hifi_duration(), b in any::<i128>()) {
            prop_assert!(conn_laws::galois_l(&HDURNANO, d, b));
        }

        #[test]
        fn hdurnano_closure_l(d in arb_extended_hifi_duration()) {
            prop_assert!(conn_laws::closure_l(&HDURNANO, d));
        }

        #[test]
        fn hdurnano_kernel_l(b in any::<i128>()) {
            prop_assert!(conn_laws::kernel_l(&HDURNANO, b));
        }

        #[test]
        fn hdurnano_monotone_l(a in arb_extended_hifi_duration(),
                               b in arb_extended_hifi_duration()) {
            prop_assert!(conn_laws::monotone_l(&HDURNANO, a, b));
        }

        #[test]
        fn hdurnano_idempotent(d in arb_extended_hifi_duration()) {
            prop_assert!(conn_laws::idempotent(&HDURNANO, d));
        }

        #[test]
        fn hdurnano_roundtrip_ceil(b in arb_hifi_total_nanos_in_range()) {
            prop_assert!(conn_laws::roundtrip_ceil(&HDURNANO, b));
        }
    }

    proptest! {
        #[test]
        fn hdursecs_galois_l(d in arb_extended_hifi_duration(), b in any::<i64>()) {
            prop_assert!(conn_laws::galois_l(&HDURSECS, d, b));
        }

        #[test]
        fn hdursecs_closure_l(d in arb_extended_hifi_duration()) {
            prop_assert!(conn_laws::closure_l(&HDURSECS, d));
        }

        #[test]
        fn hdursecs_kernel_l(b in any::<i64>()) {
            prop_assert!(conn_laws::kernel_l(&HDURSECS, b));
        }

        #[test]
        fn hdursecs_monotone_l(a in arb_extended_hifi_duration(),
                               b in arb_extended_hifi_duration()) {
            prop_assert!(conn_laws::monotone_l(&HDURSECS, a, b));
        }

        #[test]
        fn hdursecs_idempotent(d in arb_extended_hifi_duration()) {
            prop_assert!(conn_laws::idempotent(&HDURSECS, d));
        }

        // Round-trip on Finite rung values: for every i64 second in
        // HDURSECS's representable range, `inner` is exact and
        // `ceil` recovers the same integer. Mirror of
        // `hdurnano_roundtrip_ceil`.
        #[test]
        fn hdursecs_roundtrip_ceil(s in arb_hifi_total_secs_in_range()) {
            prop_assert!(conn_laws::roundtrip_ceil(&HDURSECS, s));
        }
    }

    // ── F064HDUR / F032HDUR spot checks (ConnL — no floor()) ──

    #[test]
    fn f64_hdur_zero() {
        let zero = ExtendedFloat::Extend(0.0_f64);
        assert_eq!(F064HDUR.ceil(zero), Extended::Finite(HD::ZERO));
        assert_eq!(F064HDUR.upper(Extended::Finite(HD::ZERO)), zero);
    }

    #[test]
    fn f64_hdur_half_second() {
        let half = ExtendedFloat::Extend(0.5_f64);
        let half_d = HD::from_seconds(0.5);
        assert_eq!(F064HDUR.ceil(half), Extended::Finite(half_d));
        assert_eq!(F064HDUR.upper(Extended::Finite(half_d)), half);
    }

    #[test]
    fn f64_hdur_nan_arms() {
        let nan = ExtendedFloat::Extend(f64::NAN);
        assert_eq!(F064HDUR.ceil(nan), Extended::PosInf);
    }

    #[test]
    fn f64_hdur_infinity_arms() {
        let pos_inf = ExtendedFloat::Extend(f64::INFINITY);
        assert_eq!(F064HDUR.ceil(pos_inf), Extended::PosInf);

        let neg_inf = ExtendedFloat::Extend(f64::NEG_INFINITY);
        assert_eq!(F064HDUR.ceil(neg_inf), Extended::Finite(HD::MIN));
    }

    #[test]
    fn f64_hdur_bot_top_arms() {
        assert_eq!(F064HDUR.ceil(ExtendedFloat::Bot), Extended::NegInf);
        assert_eq!(F064HDUR.ceil(ExtendedFloat::Top), Extended::PosInf);
        assert_eq!(F064HDUR.upper(Extended::NegInf), ExtendedFloat::Bot);
        assert_eq!(F064HDUR.upper(Extended::PosInf), ExtendedFloat::Top);
    }

    // Regression guard mirroring F064TDUR's `f64_ceil_min_secs_fast_path`.
    // Uses the same integer-derived bound as the implementation
    // (`hd_min_secs() as f64`) — `HD::MIN.to_seconds()` would f64-cast
    // a `±10²³`-magnitude value past the exact-integer range and could
    // disagree with the implementation's threshold. (MR !63 round-3.)
    #[test]
    fn f64_hdur_ceil_min_secs_fast_path() {
        let v_min = ExtendedFloat::Extend(hd_min_secs() as f64);
        assert_eq!(F064HDUR.ceil(v_min), Extended::Finite(HD::MIN));
    }

    #[test]
    fn f32_hdur_zero() {
        let zero = ExtendedFloat::Extend(0.0_f32);
        assert_eq!(F032HDUR.ceil(zero), Extended::Finite(HD::ZERO));
    }

    #[test]
    fn f32_hdur_one_second_in_plateau() {
        // f32 ULP at 1.0 ≈ 1.19e-7 s. ceil returns the bottom of
        // the plateau covering 1.0; widen back yields 1.0_f32.
        let one = ExtendedFloat::Extend(1.0_f32);
        if let Extended::Finite(c) = F032HDUR.ceil(one) {
            assert_eq!(c.to_seconds() as f32, 1.0_f32);
        } else {
            panic!("ceil(1.0) should be Finite");
        }
    }

    #[test]
    fn f32_hdur_nan_arms() {
        let nan = ExtendedFloat::Extend(f32::NAN);
        assert_eq!(F032HDUR.ceil(nan), Extended::PosInf);
    }

    #[test]
    fn f32_hdur_infinity_arms() {
        let pos_inf = ExtendedFloat::Extend(f32::INFINITY);
        assert_eq!(F032HDUR.ceil(pos_inf), Extended::PosInf);

        let neg_inf = ExtendedFloat::Extend(f32::NEG_INFINITY);
        assert_eq!(F032HDUR.ceil(neg_inf), Extended::Finite(HD::MIN));
    }

    #[test]
    fn f32_hdur_bot_top_arms() {
        assert_eq!(F032HDUR.ceil(ExtendedFloat::Bot), Extended::NegInf);
        assert_eq!(F032HDUR.ceil(ExtendedFloat::Top), Extended::PosInf);
    }

    // ── F064HDUR / F032HDUR L-side battery (bounded float strats) ──

    proptest! {
        #![proptest_config(ProptestConfig { cases: 64, .. ProptestConfig::default() })]
        #[test]
        fn f064hdur_galois_l(a in extended_float_f64(),
                             b in arb_extended_hifi_duration_bounded_f64()) {
            prop_assert!(conn_laws::galois_l(&F064HDUR, a, b));
        }
        #[test]
        fn f064hdur_closure_l(a in extended_float_f64()) {
            prop_assert!(conn_laws::closure_l(&F064HDUR, a));
        }
        #[test]
        fn f064hdur_kernel_l(b in arb_extended_hifi_duration_bounded_f64()) {
            prop_assert!(conn_laws::kernel_l(&F064HDUR, b));
        }
        #[test]
        fn f064hdur_monotone_l(a1 in extended_float_f64(), a2 in extended_float_f64()) {
            prop_assert!(conn_laws::monotone_l(&F064HDUR, a1, a2));
        }
        #[test]
        fn f064hdur_idempotent(a in extended_float_f64()) {
            prop_assert!(conn_laws::idempotent_l(&F064HDUR, a));
        }
        #[test]
        fn f032hdur_galois_l(a in extended_float_f32(),
                             b in arb_extended_hifi_duration_bounded_f32()) {
            prop_assert!(conn_laws::galois_l(&F032HDUR, a, b));
        }
        #[test]
        fn f032hdur_closure_l(a in extended_float_f32()) {
            prop_assert!(conn_laws::closure_l(&F032HDUR, a));
        }
        #[test]
        fn f032hdur_kernel_l(b in arb_extended_hifi_duration_bounded_f32()) {
            prop_assert!(conn_laws::kernel_l(&F032HDUR, b));
        }
        #[test]
        fn f032hdur_monotone_l(a1 in extended_float_f32(), a2 in extended_float_f32()) {
            prop_assert!(conn_laws::monotone_l(&F032HDUR, a1, a2));
        }
        #[test]
        fn f032hdur_idempotent(a in extended_float_f32()) {
            prop_assert!(conn_laws::idempotent_l(&F032HDUR, a));
        }

        #[test]
        fn f64_hdur_solve_matches_walk_in_safe_range(v in -1.0e6_f64..1.0e6_f64) {
            let est = HD::from_seconds(v);
            let est_widen = est.to_seconds();
            let (walk_z, _) = if est_widen >= v {
                f64_hdur_walks::descend_to_ceil(est, v)
            } else {
                f64_hdur_walks::ascend_to_ceil(est, v)
            };
            let (solve_z, steps) = f64_hdur_walks::solve_to_ceil(est, v);
            prop_assert_eq!(solve_z, walk_z);
            prop_assert!(steps <= 44, "solve_to_ceil took {steps} steps");
        }
    }

    // ── solve_to_ceil termination at MAX magnitude ──────────────

    #[test]
    fn f064_hdur_solve_terminates_at_max_rim() {
        // Mid-magnitude (1e13 s, well past 2⁵³ ns ≈ 104 days where the
        // f64 plateau widens). Pre-solver this would walk ~10⁶ ns.
        let v = ExtendedFloat::Extend(1.0e13_f64);
        let _ = F064HDUR.ceil(v);
    }

    #[test]
    fn f064_hdur_solve_terminates_at_unsigned_min_rim() {
        // Just past the negative rim (still inside hd_min_secs).
        let min_secs = hd_min_secs() as f64;
        let _ = F064HDUR.ceil(ExtendedFloat::Extend(min_secs * 0.9_f64));
    }
}
