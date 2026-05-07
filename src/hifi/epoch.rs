//! `hifitime::Epoch` connections, TAI baseline + UTC.
//!
//! ## Reference epochs
//!
//! Sprint 2 establishes a deliberate **asymmetric reference-epoch
//! choice** that the rest of the hifitime sprints will inherit:
//!
//! - **`ETAI*`** uses **J1900 TAI** as the implicit zero — matches
//!   hifitime's storage-native `to_tai_duration` /
//!   `from_tai_duration`, which count "Duration past J1900 in TAI".
//! - **`EUTC*`** uses **UNIX EPOCH UTC** (1970-01-01 00:00:00) as the
//!   implicit zero — matches the "unix nanoseconds" semantic of
//!   [`OFDTNANO`](crate::time::OFDTNANO) so callers moving values
//!   between `time::OffsetDateTime` and `hifitime::Epoch` get
//!   numerically matching projections.
//!
//! Each Conn's doc states its reference explicitly so users don't
//! have to guess.
//!
//! ## Conn shapes
//!
//! Three Conns per scale, mirroring the per-Duration shape from
//! `crate::hifi::duration`:
//!
//! - **`E{xx}HDUR`** — `Epoch ↔ HDuration`. `iso!` (degenerate
//!   ConnK). No `Extended` either side: both endpoints are bounded
//!   and signed, and the "rebase scale tag" idempotence makes both
//!   adjoint laws trivial under `Epoch`'s instant-based `Eq` /
//!   `Ord`.
//! - **`E{xx}NANO`** — `Extended<Epoch> ↔ i128` total nanoseconds.
//!   `conn_l!`, OFDTNANO shape (asymmetric saturation: `ceil(NegInf)
//!   = i128::MIN`, `ceil(PosInf) = max + 1`).
//! - **`E{xx}F064`** — `F064 → Extended<Epoch>` via 1 ns ULP walks
//!   on the underlying TAI Duration. F064DURN port; the comparison
//!   widens through `to_tai_seconds` (ETAI) or `to_unix_seconds`
//!   (EUTC), but the **walk** is always on TAI Duration so the
//!   shift function is shared (`crate::hifi::duration::shift_hd`).
//!
//! Total: 6 Conns. f32 Epoch bridges are deferred — the f32 plateau
//! is too wide at the multi-decade magnitudes typical of Epoch
//! values.

use crate::extended::Extended;
use crate::float::{ExtendedFloat, F064, def_walk_helpers};
use crate::hifi::duration::shift_hd;
use hifitime::{Duration as HD, Epoch, TimeScale, UNIX_REF_EPOCH};

// ── Range bounds (cached at runtime) ─────────────────────────────

#[inline]
fn hd_min_nanos() -> i128 {
    HD::MIN.total_nanoseconds()
}

#[inline]
fn hd_max_nanos() -> i128 {
    HD::MAX.total_nanoseconds()
}

/// Total nanoseconds of the UNIX epoch in **UTC-since-J1900** units
/// — the reference for `from_unix_duration` / `to_utc_duration`
/// arithmetic. Differs from the TAI-since-J1900 value of UNIX by
/// the accumulated leap-second count (a small handful of seconds).
#[inline]
fn unix_ref_utc_ns() -> i128 {
    UNIX_REF_EPOCH.to_utc_duration().total_nanoseconds()
}

/// `[min, max]` UNIX-anchored nanosecond range — the i128 region
/// where `EUTCNANO.inner` round-trips losslessly through `ceil`.
///
/// Asymmetric: the **lower** bound is `HD::MIN.total_ns()` (not
/// shifted), because `ceil` subtracts `UNIX_REF.utc` from the
/// stored UTC duration and that subtraction would underflow `HD`
/// if the stored value were already `HD::MIN`. The **upper** bound
/// is `HD::MAX.total_ns() − UNIX_REF.utc.total_ns()` (shifted),
/// because the inner addition `n + UNIX_REF.utc` would overflow
/// `HD` for larger `n`.
#[inline]
fn unix_min_nanos() -> i128 {
    hd_min_nanos()
}

#[inline]
fn unix_max_nanos() -> i128 {
    hd_max_nanos() - unix_ref_utc_ns()
}

// Float-bounds helpers for the F064 bridges. The naive
// `HD::MAX.to_seconds()` route f64-casts a value at `±10²³`
// magnitude — far past `f64`'s exact-integer range
// (`2⁵³ ≈ 9 × 10¹⁵`) — and produces an off-by-(seconds) boundary
// value. Doing the integer division **first** lands the result
// at `±10¹⁴`, well inside the exact-integer range, so the trailing
// `as f64` cast is exact. (MR !64 round-2 review.)

#[inline]
fn hd_min_secs_f64() -> f64 {
    (hd_min_nanos() / 1_000_000_000) as f64
}

#[inline]
fn hd_max_secs_f64() -> f64 {
    (hd_max_nanos() / 1_000_000_000) as f64
}

// `unix_min_secs_f64` / `unix_max_secs_f64` derive from
// `unix_{min,max}_nanos` (which serve EUTCNANO's i128 inner threshold)
// rather than from a UNIX-shifted `from_unix_seconds` boundary. The
// asymmetry: `unix_min_nanos == hd_min_nanos` (unshifted, see its
// doc), so `unix_min_secs_f64 == hd_min_secs_f64`. This **is** the
// correct fast-path threshold for `eutcf064_ceil` despite the naming
// mismatch — the inner side's HD-subtraction saturation collapses
// every Finite epoch with TAI ≤ `HD::MIN + UNIX_REF.utc` to the same
// `to_unix_seconds()` value (`hd_min_secs_f64`), so any input v ≤
// that threshold has `Finite(HD::MIN_TAI epoch)` as its Galois-L
// adjoint (the smallest Finite b satisfying v ≤ inner(b)). The walk
// would converge to the same answer; the fast-path just skips the
// 10¹² descend steps. (MR !64 rounds 3-4 review discussion.)

#[inline]
fn unix_min_secs_f64() -> f64 {
    (unix_min_nanos() / 1_000_000_000) as f64
}

#[inline]
fn unix_max_secs_f64() -> f64 {
    (unix_max_nanos() / 1_000_000_000) as f64
}

// ── ETAIHDUR ─────────────────────────────────────────────────────

#[inline]
fn etaihdur_forward(e: Epoch) -> HD {
    e.to_tai_duration()
}

#[inline]
fn etaihdur_back(d: HD) -> Epoch {
    Epoch::from_tai_duration(d)
}

crate::iso! {
    /// `Epoch ↔ hifitime::Duration` — TAI-scale storage projection.
    ///
    /// Reference: **J1900 TAI** (so `back(HD::ZERO)` is the J1900
    /// TAI epoch and `forward(UNIX_REF_EPOCH).total_nanoseconds()`
    /// is the well-known ~70-year offset).
    ///
    /// `iso!` (degenerate `ConnK`) — no `Extended` either side:
    /// both endpoints are bounded and signed, `Epoch`'s ordering is
    /// instant-based via `to_tai_duration().to_parts()`, and
    /// `back ∘ forward` is the "rebase scale tag to TAI"
    /// idempotent operation (equal under `Epoch::Eq`'s scale-aware
    /// normalization).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::hifi::ETAIHDUR;
    /// use connections::conn::{ConnL, ConnR};
    /// use hifitime::{Duration as HDuration, Epoch};
    ///
    /// // J1900 TAI — the storage zero.
    /// let j1900 = Epoch::from_tai_duration(HDuration::ZERO);
    /// assert_eq!(ETAIHDUR.ceil(j1900), HDuration::ZERO);
    /// assert_eq!(ETAIHDUR.upper(HDuration::ZERO), j1900);
    /// ```
    pub ETAIHDUR : Epoch => HD {
        forward: etaihdur_forward,
        back:    etaihdur_back,
    }
}

// ── ETAINANO ─────────────────────────────────────────────────────

fn etainano_ceil(e: Extended<Epoch>) -> i128 {
    let max_n = hd_max_nanos();
    match e {
        Extended::NegInf => i128::MIN,
        Extended::Finite(e) => e.to_tai_duration().total_nanoseconds(),
        Extended::PosInf => max_n + 1,
    }
}

fn etainano_inner(n: i128) -> Extended<Epoch> {
    let min_n = hd_min_nanos();
    let max_n = hd_max_nanos();
    if n < min_n {
        Extended::NegInf
    } else if n > max_n {
        Extended::PosInf
    } else {
        Extended::Finite(Epoch::from_tai_duration(HD::from_total_nanoseconds(n)))
    }
}

crate::conn_l! {
    /// `Extended<hifitime::Epoch> → i128` — total TAI nanoseconds
    /// since **J1900 TAI**.
    ///
    /// One-sided left-Galois Conn (`Conn::new_l(ceil, inner)`).
    /// Same shape as [`HDURNANO`](crate::hifi::HDURNANO) and
    /// [`OFDTNANO`](crate::time::OFDTNANO): source-side `Extended`,
    /// plain `i128` rung, asymmetric saturation
    /// (`ceil(NegInf) = i128::MIN`, `ceil(PosInf) = HD::MAX.total_ns()
    /// + 1`).
    ///
    /// `Epoch`'s effective TAI range is determined by `HD::MIN`
    /// /`HD::MAX` (since `Epoch` stores a TAI `Duration` plus a
    /// scale tag), so the saturation arms reuse the `HD` bounds.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::hifi::ETAINANO;
    /// use connections::extended::Extended;
    /// use hifitime::{Duration as HDuration, Epoch, UNIX_REF_EPOCH};
    ///
    /// // J1900 TAI is zero.
    /// let j1900 = Epoch::from_tai_duration(HDuration::ZERO);
    /// assert_eq!(ETAINANO.ceil(Extended::Finite(j1900)), 0);
    ///
    /// // UNIX_REF_EPOCH is the well-known +70-year TAI offset.
    /// let unix_in_tai_ns = UNIX_REF_EPOCH.to_tai_duration().total_nanoseconds();
    /// assert_eq!(ETAINANO.ceil(Extended::Finite(UNIX_REF_EPOCH)), unix_in_tai_ns);
    /// ```
    pub ETAINANO : Extended<Epoch> => i128 {
        ceil:  etainano_ceil,
        inner: etainano_inner,
    }
}

// ── ETAIF064 ─────────────────────────────────────────────────────
//
// Float-to-Epoch bridge via 1ns ULP walks on the underlying TAI
// Duration. Mirrors F064DURN's shape exactly, just with an Epoch
// rung. The walk shift function is `shift_hd` lifted to Epoch
// (via to_tai_duration / from_tai_duration); the widening is
// `to_tai_seconds`.

#[inline]
fn shift_epoch_tai(n: i32, e: Epoch) -> Epoch {
    Epoch::from_tai_duration(shift_hd(n, e.to_tai_duration()))
}

#[inline]
fn epoch_to_tai_f64(e: Epoch) -> f64 {
    e.to_tai_seconds()
}

def_walk_helpers!(
    f64_etai_walks,
    f64,
    Epoch,
    shift_epoch_tai,
    epoch_to_tai_f64
);

fn etaif064_ceil(x: F064) -> Extended<Epoch> {
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
        return Extended::Finite(Epoch::from_tai_duration(HD::MIN));
    }
    // Bounds via integer arithmetic (`hd_{min,max}_secs_f64` —
    // see helpers); going through `HD::MAX.to_seconds()` directly
    // would f64-cast a `±10²³`-magnitude value past the exact-
    // integer range and could miss out-of-range inputs by the
    // boundary rounding error. (MR !64 round-2 review.)
    let max_secs = hd_max_secs_f64();
    let min_secs = hd_min_secs_f64();
    if v > max_secs {
        return Extended::PosInf;
    }
    // Same `<=` rationale as F064DURN: at v == min_secs, the f64
    // plateau is wide enough that ULP-walking would take ~10¹²
    // steps. Fast-path to MIN.
    if v <= min_secs {
        return Extended::Finite(Epoch::from_tai_duration(HD::MIN));
    }
    let est = Epoch::from_tai_seconds(v);
    let est_widen = est.to_tai_seconds();
    let (z, _) = if est_widen >= v {
        f64_etai_walks::descend_to_ceil(est, v)
    } else {
        f64_etai_walks::ascend_to_ceil(est, v)
    };
    Extended::Finite(z)
}

fn etaif064_inner(e: Extended<Epoch>) -> F064 {
    match e {
        Extended::NegInf => ExtendedFloat::Bot,
        Extended::Finite(e) => ExtendedFloat::Extend(e.to_tai_seconds()),
        Extended::PosInf => ExtendedFloat::Top,
    }
}

crate::conn_l! {
    /// `F064 → Extended<hifitime::Epoch>` — IEEE binary64 seconds
    /// since J1900 TAI ↔ Epoch (left-Galois).
    ///
    /// Walks happen on the underlying TAI Duration in 1 ns ULPs;
    /// the float side is the comparison frame. `inner(Finite(e))`
    /// widens via `Epoch::to_tai_seconds()`, which is non-injective
    /// at multi-decade magnitudes (the f64 plateau widens with
    /// magnitude). Not order-reflecting → no true triple, shipped
    /// as `ConnL` (matches `F064DURN` rationale, Plan 32).
    ///
    /// Saturation arms mirror `F064DURN`: NaN → PosInf, ±∞ → PosInf
    /// / `Finite(Epoch::from_tai_duration(HD::MIN))`, Bot → NegInf,
    /// Top → PosInf.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::hifi::ETAIF064;
    /// use connections::extended::Extended;
    /// use connections::float::ExtendedFloat;
    /// use hifitime::{Duration as HDuration, Epoch};
    ///
    /// // 0.5 TAI seconds past J1900.
    /// let half = ExtendedFloat::Extend(0.5_f64);
    /// let half_e = Epoch::from_tai_duration(HDuration::from_seconds(0.5));
    /// assert_eq!(ETAIF064.ceil(half), Extended::Finite(half_e));
    /// ```
    pub ETAIF064 : F064 => Extended<Epoch> {
        ceil:  etaif064_ceil,
        inner: etaif064_inner,
    }
}

// ── Proof-only walk-step probe (TAI scale) ──────────────────────
//
// Mirrors the production `etaif064_ceil` walk-entry but returns
// `(z, steps)` instead of dropping `_steps`. Used by
// `crate::kani_proofs::hifi_walk` to prove the iteration bound is
// ≤ 2 over the non-fast-path finite domain. The `EUTC` walk is
// deferred — its widen (`Epoch::to_unix_seconds`) consults the
// leap-second table, which makes the loop's per-iteration cost
// intractable for CBMC.

#[cfg(kani)]
pub(crate) fn f64_etai_ceil_walk_steps_for_proof(v: f64) -> (Epoch, u32) {
    let est = Epoch::from_tai_seconds(v);
    let est_widen = est.to_tai_seconds();
    if est_widen >= v {
        f64_etai_walks::descend_to_ceil(est, v)
    } else {
        f64_etai_walks::ascend_to_ceil(est, v)
    }
}

// ── EUTCHDUR ─────────────────────────────────────────────────────

#[inline]
fn eutchdur_forward(e: Epoch) -> HD {
    // UTC-scale Duration since J1900 UTC. Mirrors ETAIHDUR's J1900
    // anchor for consistency in the iso (UNIX-anchoring would put
    // `back(HD::MAX)` outside HD's range and break round-trip — the
    // EUTCNANO / EUTCF064 pair carries the UNIX-anchored semantic).
    e.to_duration_in_time_scale(TimeScale::UTC)
}

#[inline]
fn eutchdur_back(d: HD) -> Epoch {
    Epoch::from_utc_duration(d)
}

crate::iso! {
    /// `Epoch ↔ hifitime::Duration` — UTC-scale projection,
    /// reference **J1900 UTC**.
    ///
    /// Different from [`ETAIHDUR`] in one way: `forward` rebases to
    /// UTC scale via hifitime's `LatestLeapSeconds` table (compile-
    /// time-baked, no runtime data needed), so the resulting
    /// Duration counts UTC seconds (which include leap-second
    /// insertions). The reference epoch is the same J1900 anchor
    /// as ETAIHDUR — UNIX-anchoring would shift the round-trip
    /// boundary outside `HD`'s representable range and break the
    /// iso. The UNIX-anchored UTC numerics live on
    /// [`EUTCNANO`] / [`EUTCF064`] instead.
    ///
    /// `iso!` (degenerate `ConnK`) — `back ∘ forward` is the
    /// "rebase scale tag to UTC" idempotent operation; the
    /// UTC↔TAI mapping IS bijective (each leap second adds one
    /// distinct UTC second; both sides of the leap remain
    /// distinct), so no information is lost.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::hifi::EUTCHDUR;
    /// use connections::conn::{ConnL, ConnR};
    /// use hifitime::{Duration as HDuration, Epoch};
    ///
    /// // J1900 TAI = J1900 UTC (no leap seconds before 1972).
    /// let j1900 = Epoch::from_tai_duration(HDuration::ZERO);
    /// assert_eq!(EUTCHDUR.ceil(j1900), HDuration::ZERO);
    /// ```
    pub EUTCHDUR : Epoch => HD {
        forward: eutchdur_forward,
        back:    eutchdur_back,
    }
}

// ── EUTCNANO ─────────────────────────────────────────────────────

fn eutcnano_ceil(e: Extended<Epoch>) -> i128 {
    let max_n = unix_max_nanos();
    match e {
        Extended::NegInf => i128::MIN,
        Extended::Finite(e) => {
            // UNIX-anchored UTC nanoseconds: subtract UNIX_REF.utc
            // explicitly here (EUTCHDUR is J1900-anchored).
            (e.to_duration_in_time_scale(TimeScale::UTC) - UNIX_REF_EPOCH.to_utc_duration())
                .total_nanoseconds()
        }
        Extended::PosInf => max_n + 1,
    }
}

fn eutcnano_inner(n: i128) -> Extended<Epoch> {
    let min_n = unix_min_nanos();
    let max_n = unix_max_nanos();
    if n < min_n {
        Extended::NegInf
    } else if n > max_n {
        Extended::PosInf
    } else {
        // Add the UNIX UTC offset BEFORE the HD construction so the
        // intermediate HD doesn't saturate at boundary `n` values
        // (which would break round-trip via `ceil`). For `n ∈
        // [unix_min, unix_max]`, `n + unix_ref_utc_ns()` is by
        // construction in `[HD::MIN.total_ns, HD::MAX.total_ns]`,
        // so `from_total_nanoseconds` is exact (no saturation).
        let utc_total_ns = n + unix_ref_utc_ns();
        let utc_dur = HD::from_total_nanoseconds(utc_total_ns);
        Extended::Finite(Epoch::from_utc_duration(utc_dur))
    }
}

crate::conn_l! {
    /// `Extended<hifitime::Epoch> → i128` — UNIX nanoseconds (since
    /// 1970-01-01 00:00:00 UTC). **Same numeric semantic as
    /// [`OFDTNANO`](crate::time::OFDTNANO)** for callers moving
    /// values between `time::OffsetDateTime` and `hifitime::Epoch`.
    ///
    /// One-sided left-Galois Conn (`Conn::new_l(ceil, inner)`),
    /// OFDTNANO shape with the standard asymmetric saturation:
    /// `ceil(NegInf) = i128::MIN`, `ceil(PosInf) = unix_max + 1` —
    /// where `unix_max = HD::MAX.total_ns() − UNIX_REF.utc.total_ns()`,
    /// **distinct** from `ETAINANO`'s `ceil(PosInf) = HD::MAX.total_ns() + 1`.
    /// The two sentinels differ by `UNIX_REF.utc.total_ns()` (~70 years
    /// in nanoseconds); callers using these as PosInf markers must
    /// pick the correct one for the Conn at hand.
    ///
    /// The in-range Finite portion `[unix_min, unix_max]` is
    /// **asymmetric** about the UNIX offset: `unix_min =
    /// HD::MIN.total_ns()` (unshifted — `ceil`'s subtraction
    /// `epoch.to_utc_duration() − UNIX_REF.utc` would underflow `HD`
    /// if the stored value were already at `HD::MIN`); `unix_max =
    /// HD::MAX.total_ns() − UNIX_REF_EPOCH.to_utc_duration().
    /// total_nanoseconds()` (shifted — the inner addition `n +
    /// UNIX_REF.utc` would overflow `HD` beyond it). Sub-second
    /// `Epoch` values round-trip exactly within that range.
    ///
    /// **Non-identity zone.** Epochs whose stored UTC duration falls
    /// in `[HD::MIN, HD::MIN + UNIX_REF.utc.total_ns())` (a ~70-year
    /// window at the negative HD extreme) are NOT preserved by
    /// `inner ∘ ceil`. The `ceil` subtraction saturates against
    /// `HD::MIN`, collapsing the entire window onto `unix_min_nanos`;
    /// `inner` then maps that single value to a single epoch at UTC
    /// `= HD::MIN + UNIX_REF.utc`. Closure (`a ≤ inner(ceil(a))`) and
    /// Galois L still hold — the round-tripped epoch is a *later*
    /// instant than every input in the window — but the round-trip is
    /// non-injective there. The tradeoff is intrinsic to the
    /// asymmetric design and matches the fact that the EUTCF064 walk
    /// at the same magnitude also collapses to `Finite(HD::MIN_TAI
    /// epoch)` via inner-side HD-subtraction saturation.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::hifi::EUTCNANO;
    /// use connections::extended::Extended;
    /// use hifitime::{Epoch, UNIX_REF_EPOCH};
    ///
    /// // UNIX_REF_EPOCH is zero unix nanoseconds.
    /// assert_eq!(EUTCNANO.ceil(Extended::Finite(UNIX_REF_EPOCH)), 0);
    ///
    /// // 1970-01-01 + 1 second = 10⁹ unix nanoseconds.
    /// let one_sec = Epoch::from_unix_seconds(1.0);
    /// assert_eq!(EUTCNANO.ceil(Extended::Finite(one_sec)), 1_000_000_000);
    /// ```
    pub EUTCNANO : Extended<Epoch> => i128 {
        ceil:  eutcnano_ceil,
        inner: eutcnano_inner,
    }
}

// ── EUTCF064 ─────────────────────────────────────────────────────
//
// Float-to-Epoch bridge anchored at UNIX EPOCH UTC. The walk
// advances the underlying TAI Duration by 1ns (so we can reuse
// shift_epoch_tai), but the comparison widens through to_unix_seconds
// — which itself does a UTC conversion (leap-second-aware).

#[inline]
fn epoch_to_unix_f64(e: Epoch) -> f64 {
    e.to_unix_seconds()
}

def_walk_helpers!(
    f64_eutc_walks,
    f64,
    Epoch,
    shift_epoch_tai,
    epoch_to_unix_f64
);

fn eutcf064_ceil(x: F064) -> Extended<Epoch> {
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
        return Extended::Finite(Epoch::from_tai_duration(HD::MIN));
    }
    // UNIX-anchored bounds via integer arithmetic
    // (`unix_{min,max}_secs_f64`); going through
    // `epoch_to_unix_f64(Epoch::from_tai_duration(HD::MAX))` would
    // f64-cast through `to_unix_seconds` at `±10²³` magnitude past
    // f64's exact-integer range and could miss out-of-range inputs.
    // (MR !64 round-2 review.)
    let unix_max_secs = unix_max_secs_f64();
    let unix_min_secs = unix_min_secs_f64();
    if v > unix_max_secs {
        return Extended::PosInf;
    }
    if v <= unix_min_secs {
        return Extended::Finite(Epoch::from_tai_duration(HD::MIN));
    }
    let est = Epoch::from_unix_seconds(v);
    let est_widen = est.to_unix_seconds();
    let (z, _) = if est_widen >= v {
        f64_eutc_walks::descend_to_ceil(est, v)
    } else {
        f64_eutc_walks::ascend_to_ceil(est, v)
    };
    Extended::Finite(z)
}

fn eutcf064_inner(e: Extended<Epoch>) -> F064 {
    match e {
        Extended::NegInf => ExtendedFloat::Bot,
        Extended::Finite(e) => ExtendedFloat::Extend(e.to_unix_seconds()),
        Extended::PosInf => ExtendedFloat::Top,
    }
}

crate::conn_l! {
    /// `F064 → Extended<hifitime::Epoch>` — IEEE binary64 UNIX
    /// seconds (1970-01-01 UTC reference) ↔ Epoch (left-Galois).
    ///
    /// Shape mirrors [`ETAIF064`] exactly with two changes:
    ///
    /// 1. **Reference**: UNIX EPOCH UTC, not J1900 TAI. So the
    ///    `f64` value `0.0` corresponds to `UNIX_REF_EPOCH`.
    /// 2. **Comparison frame**: `to_unix_seconds()` does the UTC
    ///    conversion (leap-second-aware via hifitime's baked-in
    ///    `LatestLeapSeconds`). The walk still advances the
    ///    underlying TAI Duration by 1 ns; the comparison widens
    ///    through unix seconds.
    ///
    /// One-sided `ConnL` for the same reason as `ETAIF064`:
    /// `inner` is non-injective on the f64 plateau at multi-decade
    /// magnitudes.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::hifi::EUTCF064;
    /// use connections::extended::Extended;
    /// use connections::float::ExtendedFloat;
    /// use hifitime::Epoch;
    ///
    /// // 0.0 unix seconds ↔ UNIX EPOCH.
    /// let zero = ExtendedFloat::Extend(0.0_f64);
    /// let unix_epoch = Epoch::from_unix_seconds(0.0);
    /// assert_eq!(EUTCF064.ceil(zero), Extended::Finite(unix_epoch));
    /// ```
    pub EUTCF064 : F064 => Extended<Epoch> {
        ceil:  eutcf064_ceil,
        inner: eutcf064_inner,
    }
}

// ── §3 GNSS scales (GPST, GST, BDT, QZSST) ───────────────────────
//
// Each GNSS scale is an exact integer-second offset to TAI. The
// HDuration projection is therefore an `iso!` (degenerate ConnK);
// the i128 nanosecond projection is `ConnL` with the same
// OFDTNANO-shape asymmetric saturation as ETAI / EUTC; and the f64
// seconds projection is `ConnL` with 1 ns ULP walks on the underlying
// TAI Duration (`shift_epoch_tai`) and a per-scale comparison frame.
//
// References (all exact integer seconds, exposed publicly by hifitime):
// - GPST_REF_EPOCH  = 1980-01-06 UTC ≡ TAI − 19 s (`SECONDS_GPS_TAI_OFFSET_I64 = 2_524_953_619`)
// - QZSST_REF_EPOCH = GPST_REF_EPOCH (QZSS shares GPS's reference)
// - GST_REF_EPOCH   = 1999-08-21      (`SECONDS_GST_TAI_OFFSET_I64 = 3_144_268_819`)
// - BDT_REF_EPOCH   = 2005-12-31      (`SECONDS_BDT_TAI_OFFSET_I64 = 3_345_062_433`)
//
// Saturation bound asymmetry mirrors EUTCNANO exactly: `min_n =
// HD::MIN.total_ns()` (unshifted, otherwise `ceil`'s subtraction
// underflows HD); `max_n = HD::MAX.total_ns() − ref.total_ns()`
// (shifted, otherwise the inner addition overflows HD).

use hifitime::{BDT_REF_EPOCH, GPST_REF_EPOCH, GST_REF_EPOCH, QZSST_REF_EPOCH};

// ── §3 per-scale offset helpers ──────────────────────────────────

#[inline]
fn gpst_ref_tai_ns() -> i128 {
    GPST_REF_EPOCH.to_tai_duration().total_nanoseconds()
}

#[inline]
fn qzsst_ref_tai_ns() -> i128 {
    QZSST_REF_EPOCH.to_tai_duration().total_nanoseconds()
}

#[inline]
fn gst_ref_tai_ns() -> i128 {
    GST_REF_EPOCH.to_tai_duration().total_nanoseconds()
}

#[inline]
fn bdt_ref_tai_ns() -> i128 {
    BDT_REF_EPOCH.to_tai_duration().total_nanoseconds()
}

// Per-scale (min, max) nanosecond bounds. Each min is unshifted (=
// HD::MIN.total_ns()); each max is `HD::MAX.total_ns() − ref_tai_ns()`.

#[inline]
fn gpst_min_nanos() -> i128 {
    hd_min_nanos()
}
#[inline]
fn gpst_max_nanos() -> i128 {
    hd_max_nanos() - gpst_ref_tai_ns()
}
#[inline]
fn qzsst_min_nanos() -> i128 {
    hd_min_nanos()
}
#[inline]
fn qzsst_max_nanos() -> i128 {
    hd_max_nanos() - qzsst_ref_tai_ns()
}
#[inline]
fn gst_min_nanos() -> i128 {
    hd_min_nanos()
}
#[inline]
fn gst_max_nanos() -> i128 {
    hd_max_nanos() - gst_ref_tai_ns()
}
#[inline]
fn bdt_min_nanos() -> i128 {
    hd_min_nanos()
}
#[inline]
fn bdt_max_nanos() -> i128 {
    hd_max_nanos() - bdt_ref_tai_ns()
}

// Per-scale f64 second bounds via integer division (`nanos / 10⁹`,
// landing at ~10¹⁴ — exact in f64). The MR !64 round-2 lesson:
// going through `to_seconds()` directly f64-casts a value past
// `2⁵³`, off-by-seconds at the boundary.

#[inline]
fn gpst_min_secs_f64() -> f64 {
    (gpst_min_nanos() / 1_000_000_000) as f64
}
#[inline]
fn gpst_max_secs_f64() -> f64 {
    (gpst_max_nanos() / 1_000_000_000) as f64
}
#[inline]
fn qzsst_min_secs_f64() -> f64 {
    (qzsst_min_nanos() / 1_000_000_000) as f64
}
#[inline]
fn qzsst_max_secs_f64() -> f64 {
    (qzsst_max_nanos() / 1_000_000_000) as f64
}
#[inline]
fn gst_min_secs_f64() -> f64 {
    (gst_min_nanos() / 1_000_000_000) as f64
}
#[inline]
fn gst_max_secs_f64() -> f64 {
    (gst_max_nanos() / 1_000_000_000) as f64
}
#[inline]
fn bdt_min_secs_f64() -> f64 {
    (bdt_min_nanos() / 1_000_000_000) as f64
}
#[inline]
fn bdt_max_secs_f64() -> f64 {
    (bdt_max_nanos() / 1_000_000_000) as f64
}

// ── §3.1 GPST ────────────────────────────────────────────────────

#[inline]
fn egpshdur_forward(e: Epoch) -> HD {
    e.to_gpst_duration()
}

#[inline]
fn egpshdur_back(d: HD) -> Epoch {
    Epoch::from_gpst_duration(d)
}

crate::iso! {
    /// `Epoch ↔ hifitime::Duration` — GPS Time projection.
    /// Reference: [`hifitime::GPST_REF_EPOCH`] (1980-01-06 UTC,
    /// = TAI 1980-01-06 − 19 s).
    ///
    /// Same `iso!` (degenerate `ConnK`) shape as [`ETAIHDUR`] /
    /// [`EUTCHDUR`]. The GPST offset is an exact integer-second
    /// constant ([`hifitime::SECONDS_GPS_TAI_OFFSET_I64`]), so the
    /// round-trip is integer subtract-then-add — no information loss.
    /// `back ∘ forward` rebases the scale tag to GPST while
    /// preserving the instant under `Epoch::Eq`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::hifi::EGPSHDUR;
    /// use connections::conn::{ConnL, ConnR};
    /// use hifitime::{Duration as HDuration, GPST_REF_EPOCH};
    ///
    /// // GPST reference is the GPST-scale zero.
    /// assert_eq!(EGPSHDUR.ceil(GPST_REF_EPOCH), HDuration::ZERO);
    /// ```
    pub EGPSHDUR : Epoch => HD {
        forward: egpshdur_forward,
        back:    egpshdur_back,
    }
}

fn egpsnano_ceil(e: Extended<Epoch>) -> i128 {
    let max_n = gpst_max_nanos();
    match e {
        Extended::NegInf => i128::MIN,
        Extended::Finite(e) => e.to_gpst_duration().total_nanoseconds(),
        Extended::PosInf => max_n + 1,
    }
}

fn egpsnano_inner(n: i128) -> Extended<Epoch> {
    let min_n = gpst_min_nanos();
    let max_n = gpst_max_nanos();
    if n < min_n {
        Extended::NegInf
    } else if n > max_n {
        Extended::PosInf
    } else {
        // `from_gpst_duration(d)` stores `d` as the GPST-relative
        // duration directly (no anchor shift needed, unlike
        // `eutcnano_inner` whose `from_utc_duration` expects a J1900-
        // anchored UTC value). For `n ∈ [gpst_min, gpst_max]`,
        // `HD::from_total_nanoseconds(n)` is exact (in HD's range),
        // and `to_gpst_duration()` short-circuits on the matching
        // scale tag, so round-trip via `ceil` is exact.
        Extended::Finite(Epoch::from_gpst_duration(HD::from_total_nanoseconds(n)))
    }
}

crate::conn_l! {
    /// `Extended<hifitime::Epoch> → i128` — total GPS Time
    /// nanoseconds since [`hifitime::GPST_REF_EPOCH`].
    ///
    /// One-sided left-Galois Conn (`Conn::new_l(ceil, inner)`),
    /// OFDTNANO shape with asymmetric saturation:
    /// `ceil(NegInf) = i128::MIN`, `ceil(PosInf) = gpst_max + 1`,
    /// where `gpst_max = HD::MAX.total_ns() −
    /// GPST_REF_EPOCH.to_tai_duration().total_nanoseconds()`. The
    /// `inner` round-trip is exact on `[gpst_min, gpst_max]`,
    /// where `gpst_min = HD::MIN.total_ns()` (unshifted, see the
    /// module-level §3 banner for the asymmetry rationale).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::hifi::EGPSNANO;
    /// use connections::extended::Extended;
    /// use hifitime::GPST_REF_EPOCH;
    ///
    /// assert_eq!(EGPSNANO.ceil(Extended::Finite(GPST_REF_EPOCH)), 0);
    /// ```
    pub EGPSNANO : Extended<Epoch> => i128 {
        ceil:  egpsnano_ceil,
        inner: egpsnano_inner,
    }
}

#[inline]
fn epoch_to_gpst_f64(e: Epoch) -> f64 {
    e.to_gpst_seconds()
}

def_walk_helpers!(
    f64_egps_walks,
    f64,
    Epoch,
    shift_epoch_tai,
    epoch_to_gpst_f64
);

fn egpsf064_ceil(x: F064) -> Extended<Epoch> {
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
        return Extended::Finite(Epoch::from_tai_duration(HD::MIN));
    }
    let max_secs = gpst_max_secs_f64();
    let min_secs = gpst_min_secs_f64();
    if v > max_secs {
        return Extended::PosInf;
    }
    // `v ≤ min_secs` short-circuits to the negative HD bound for the
    // same reason as ETAIF064 / EUTCF064: the f64 plateau there is
    // wide enough that walking would take ~10¹² steps and converge
    // to the same answer. (See §1 ETAIF064 doc.)
    if v <= min_secs {
        return Extended::Finite(Epoch::from_tai_duration(HD::MIN));
    }
    let est = Epoch::from_gpst_seconds(v);
    let est_widen = est.to_gpst_seconds();
    let (z, _) = if est_widen >= v {
        f64_egps_walks::descend_to_ceil(est, v)
    } else {
        f64_egps_walks::ascend_to_ceil(est, v)
    };
    Extended::Finite(z)
}

fn egpsf064_inner(e: Extended<Epoch>) -> F064 {
    match e {
        Extended::NegInf => ExtendedFloat::Bot,
        Extended::Finite(e) => ExtendedFloat::Extend(e.to_gpst_seconds()),
        Extended::PosInf => ExtendedFloat::Top,
    }
}

crate::conn_l! {
    /// `F064 → Extended<hifitime::Epoch>` — IEEE binary64 GPST
    /// seconds (since [`hifitime::GPST_REF_EPOCH`]) ↔ Epoch.
    ///
    /// `ConnL`, F064DURN-shape; walks happen on the underlying TAI
    /// Duration in 1 ns ULPs (`shift_epoch_tai`); the comparison
    /// frame is `Epoch::to_gpst_seconds()`. Non-injective at multi-
    /// decade magnitudes (the f64 plateau widens with the absolute
    /// value), so this is `ConnL` not `ConnK` (matches `F064DURN` /
    /// `ETAIF064` rationale).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::hifi::EGPSF064;
    /// use connections::extended::Extended;
    /// use connections::float::ExtendedFloat;
    /// use hifitime::GPST_REF_EPOCH;
    ///
    /// // GPST seconds zero ↔ GPST_REF_EPOCH.
    /// let zero = ExtendedFloat::Extend(0.0_f64);
    /// assert_eq!(EGPSF064.ceil(zero), Extended::Finite(GPST_REF_EPOCH));
    /// ```
    pub EGPSF064 : F064 => Extended<Epoch> {
        ceil:  egpsf064_ceil,
        inner: egpsf064_inner,
    }
}

// ── §3.2 QZSST ───────────────────────────────────────────────────
//
// QZSST shares GPST's reference epoch in hifitime
// (`QZSST_REF_EPOCH == GPST_REF_EPOCH`); we still ship distinct
// const names so the call site documents intent. The Conn bodies
// dispatch through QZSST-tagged hifitime APIs (`to_qzsst_duration`,
// `from_qzsst_duration`, `to_qzsst_seconds`, `from_qzsst_seconds`),
// so the resulting Epochs carry `TimeScale::QZSST` rather than
// `TimeScale::GPST` — observably distinct under `Debug` /
// `Display`, equal-on-instant under `Eq` / `Ord`.

#[inline]
fn eqzshdur_forward(e: Epoch) -> HD {
    e.to_qzsst_duration()
}

#[inline]
fn eqzshdur_back(d: HD) -> Epoch {
    Epoch::from_qzsst_duration(d)
}

crate::iso! {
    /// `Epoch ↔ hifitime::Duration` — QZSS Time projection.
    /// Reference: [`hifitime::QZSST_REF_EPOCH`] (= GPST reference).
    ///
    /// Same shape as [`EGPSHDUR`]. QZSST and GPST share their
    /// reference epoch; the two Conns produce instant-equal results
    /// for any `Epoch` (different scale tag, same TAI duration).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::hifi::EQZSHDUR;
    /// use connections::conn::{ConnL, ConnR};
    /// use hifitime::{Duration as HDuration, QZSST_REF_EPOCH};
    ///
    /// assert_eq!(EQZSHDUR.ceil(QZSST_REF_EPOCH), HDuration::ZERO);
    /// ```
    pub EQZSHDUR : Epoch => HD {
        forward: eqzshdur_forward,
        back:    eqzshdur_back,
    }
}

fn eqzsnano_ceil(e: Extended<Epoch>) -> i128 {
    let max_n = qzsst_max_nanos();
    match e {
        Extended::NegInf => i128::MIN,
        Extended::Finite(e) => e.to_qzsst_duration().total_nanoseconds(),
        Extended::PosInf => max_n + 1,
    }
}

fn eqzsnano_inner(n: i128) -> Extended<Epoch> {
    let min_n = qzsst_min_nanos();
    let max_n = qzsst_max_nanos();
    if n < min_n {
        Extended::NegInf
    } else if n > max_n {
        Extended::PosInf
    } else {
        Extended::Finite(Epoch::from_qzsst_duration(HD::from_total_nanoseconds(n)))
    }
}

crate::conn_l! {
    /// `Extended<hifitime::Epoch> → i128` — total QZSS Time
    /// nanoseconds since [`hifitime::QZSST_REF_EPOCH`] (= GPST ref).
    ///
    /// Mirrors [`EGPSNANO`] exactly; the only observable difference
    /// is that `inner(n)`'s `Finite` arm returns a QZSST-tagged
    /// `Epoch`. Numerically equal to `EGPSNANO` for every input.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::hifi::EQZSNANO;
    /// use connections::extended::Extended;
    /// use hifitime::QZSST_REF_EPOCH;
    ///
    /// assert_eq!(EQZSNANO.ceil(Extended::Finite(QZSST_REF_EPOCH)), 0);
    /// ```
    pub EQZSNANO : Extended<Epoch> => i128 {
        ceil:  eqzsnano_ceil,
        inner: eqzsnano_inner,
    }
}

#[inline]
fn epoch_to_qzsst_f64(e: Epoch) -> f64 {
    e.to_qzsst_seconds()
}

def_walk_helpers!(
    f64_eqzs_walks,
    f64,
    Epoch,
    shift_epoch_tai,
    epoch_to_qzsst_f64
);

fn eqzsf064_ceil(x: F064) -> Extended<Epoch> {
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
        return Extended::Finite(Epoch::from_tai_duration(HD::MIN));
    }
    let max_secs = qzsst_max_secs_f64();
    let min_secs = qzsst_min_secs_f64();
    if v > max_secs {
        return Extended::PosInf;
    }
    if v <= min_secs {
        return Extended::Finite(Epoch::from_tai_duration(HD::MIN));
    }
    let est = Epoch::from_qzsst_seconds(v);
    let est_widen = est.to_qzsst_seconds();
    let (z, _) = if est_widen >= v {
        f64_eqzs_walks::descend_to_ceil(est, v)
    } else {
        f64_eqzs_walks::ascend_to_ceil(est, v)
    };
    Extended::Finite(z)
}

fn eqzsf064_inner(e: Extended<Epoch>) -> F064 {
    match e {
        Extended::NegInf => ExtendedFloat::Bot,
        Extended::Finite(e) => ExtendedFloat::Extend(e.to_qzsst_seconds()),
        Extended::PosInf => ExtendedFloat::Top,
    }
}

crate::conn_l! {
    /// `F064 → Extended<hifitime::Epoch>` — QZSS Time seconds (since
    /// [`hifitime::QZSST_REF_EPOCH`]) ↔ Epoch. Mirrors [`EGPSF064`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::hifi::EQZSF064;
    /// use connections::extended::Extended;
    /// use connections::float::ExtendedFloat;
    /// use hifitime::QZSST_REF_EPOCH;
    ///
    /// let zero = ExtendedFloat::Extend(0.0_f64);
    /// assert_eq!(EQZSF064.ceil(zero), Extended::Finite(QZSST_REF_EPOCH));
    /// ```
    pub EQZSF064 : F064 => Extended<Epoch> {
        ceil:  eqzsf064_ceil,
        inner: eqzsf064_inner,
    }
}

// ── §3.3 GST (Galileo) ───────────────────────────────────────────

#[inline]
fn egsthdur_forward(e: Epoch) -> HD {
    e.to_gst_duration()
}

#[inline]
fn egsthdur_back(d: HD) -> Epoch {
    Epoch::from_gst_duration(d)
}

crate::iso! {
    /// `Epoch ↔ hifitime::Duration` — Galileo System Time projection.
    /// Reference: [`hifitime::GST_REF_EPOCH`] (1999-08-21,
    /// `SECONDS_GST_TAI_OFFSET_I64 = 3_144_268_819`).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::hifi::EGSTHDUR;
    /// use connections::conn::{ConnL, ConnR};
    /// use hifitime::{Duration as HDuration, GST_REF_EPOCH};
    /// assert_eq!(EGSTHDUR.ceil(GST_REF_EPOCH), HDuration::ZERO);
    /// ```
    pub EGSTHDUR : Epoch => HD {
        forward: egsthdur_forward,
        back:    egsthdur_back,
    }
}

fn egstnano_ceil(e: Extended<Epoch>) -> i128 {
    let max_n = gst_max_nanos();
    match e {
        Extended::NegInf => i128::MIN,
        Extended::Finite(e) => e.to_gst_duration().total_nanoseconds(),
        Extended::PosInf => max_n + 1,
    }
}

fn egstnano_inner(n: i128) -> Extended<Epoch> {
    let min_n = gst_min_nanos();
    let max_n = gst_max_nanos();
    if n < min_n {
        Extended::NegInf
    } else if n > max_n {
        Extended::PosInf
    } else {
        Extended::Finite(Epoch::from_gst_duration(HD::from_total_nanoseconds(n)))
    }
}

crate::conn_l! {
    /// `Extended<hifitime::Epoch> → i128` — total GST nanoseconds
    /// since [`hifitime::GST_REF_EPOCH`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::hifi::EGSTNANO;
    /// use connections::extended::Extended;
    /// use hifitime::GST_REF_EPOCH;
    ///
    /// assert_eq!(EGSTNANO.ceil(Extended::Finite(GST_REF_EPOCH)), 0);
    /// ```
    pub EGSTNANO : Extended<Epoch> => i128 {
        ceil:  egstnano_ceil,
        inner: egstnano_inner,
    }
}

#[inline]
fn epoch_to_gst_f64(e: Epoch) -> f64 {
    e.to_gst_seconds()
}

def_walk_helpers!(
    f64_egst_walks,
    f64,
    Epoch,
    shift_epoch_tai,
    epoch_to_gst_f64
);

fn egstf064_ceil(x: F064) -> Extended<Epoch> {
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
        return Extended::Finite(Epoch::from_tai_duration(HD::MIN));
    }
    let max_secs = gst_max_secs_f64();
    let min_secs = gst_min_secs_f64();
    if v > max_secs {
        return Extended::PosInf;
    }
    if v <= min_secs {
        return Extended::Finite(Epoch::from_tai_duration(HD::MIN));
    }
    let est = Epoch::from_gst_seconds(v);
    let est_widen = est.to_gst_seconds();
    let (z, _) = if est_widen >= v {
        f64_egst_walks::descend_to_ceil(est, v)
    } else {
        f64_egst_walks::ascend_to_ceil(est, v)
    };
    Extended::Finite(z)
}

fn egstf064_inner(e: Extended<Epoch>) -> F064 {
    match e {
        Extended::NegInf => ExtendedFloat::Bot,
        Extended::Finite(e) => ExtendedFloat::Extend(e.to_gst_seconds()),
        Extended::PosInf => ExtendedFloat::Top,
    }
}

crate::conn_l! {
    /// `F064 → Extended<hifitime::Epoch>` — GST seconds (since
    /// [`hifitime::GST_REF_EPOCH`]) ↔ Epoch. Same shape as
    /// [`EGPSF064`] with `to_gst_seconds` as the comparison frame.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::hifi::EGSTF064;
    /// use connections::extended::Extended;
    /// use connections::float::ExtendedFloat;
    /// use hifitime::GST_REF_EPOCH;
    ///
    /// let zero = ExtendedFloat::Extend(0.0_f64);
    /// assert_eq!(EGSTF064.ceil(zero), Extended::Finite(GST_REF_EPOCH));
    /// ```
    pub EGSTF064 : F064 => Extended<Epoch> {
        ceil:  egstf064_ceil,
        inner: egstf064_inner,
    }
}

// ── §3.4 BDT (BeiDou) ────────────────────────────────────────────
//
// BDT routes through `to_duration_in_time_scale(TimeScale::BDT)`
// rather than `to_bdt_duration()`. The two are equivalent for
// interior values, but at the rung boundary they diverge:
// `to_bdt_duration` is implemented as `self.to_tai_duration() -
// BDT_REF.to_tai_duration()` (`hifitime/src/epoch/mod.rs:800`),
// which routes through TAI and saturates `HD::MAX + BDT_REF` at the
// HD upper bound. The other GNSS `to_*_duration` methods use
// `to_time_scale(scale).duration` (which short-circuits for the
// matching tag), and so don't have this asymmetry. Going through
// `to_duration_in_time_scale` here gives BDT the same short-circuit
// path and unblocks the iso round-trip at `HD::MAX`.

#[inline]
fn ebdthdur_forward(e: Epoch) -> HD {
    e.to_duration_in_time_scale(TimeScale::BDT)
}

#[inline]
fn ebdthdur_back(d: HD) -> Epoch {
    Epoch::from_bdt_duration(d)
}

crate::iso! {
    /// `Epoch ↔ hifitime::Duration` — BeiDou Time projection.
    /// Reference: [`hifitime::BDT_REF_EPOCH`] (2005-12-31,
    /// `SECONDS_BDT_TAI_OFFSET_I64 = 3_345_062_433`).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::hifi::EBDTHDUR;
    /// use connections::conn::{ConnL, ConnR};
    /// use hifitime::{Duration as HDuration, BDT_REF_EPOCH};
    /// assert_eq!(EBDTHDUR.ceil(BDT_REF_EPOCH), HDuration::ZERO);
    /// ```
    pub EBDTHDUR : Epoch => HD {
        forward: ebdthdur_forward,
        back:    ebdthdur_back,
    }
}

fn ebdtnano_ceil(e: Extended<Epoch>) -> i128 {
    let max_n = bdt_max_nanos();
    match e {
        Extended::NegInf => i128::MIN,
        // Use `to_duration_in_time_scale(BDT)` rather than
        // `to_bdt_duration()` for the same boundary-saturation
        // reason as `ebdthdur_forward` — see the §3.4 banner.
        Extended::Finite(e) => e
            .to_duration_in_time_scale(TimeScale::BDT)
            .total_nanoseconds(),
        Extended::PosInf => max_n + 1,
    }
}

fn ebdtnano_inner(n: i128) -> Extended<Epoch> {
    let min_n = bdt_min_nanos();
    let max_n = bdt_max_nanos();
    if n < min_n {
        Extended::NegInf
    } else if n > max_n {
        Extended::PosInf
    } else {
        Extended::Finite(Epoch::from_bdt_duration(HD::from_total_nanoseconds(n)))
    }
}

crate::conn_l! {
    /// `Extended<hifitime::Epoch> → i128` — total BDT nanoseconds
    /// since [`hifitime::BDT_REF_EPOCH`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::hifi::EBDTNANO;
    /// use connections::extended::Extended;
    /// use hifitime::BDT_REF_EPOCH;
    ///
    /// assert_eq!(EBDTNANO.ceil(Extended::Finite(BDT_REF_EPOCH)), 0);
    /// ```
    pub EBDTNANO : Extended<Epoch> => i128 {
        ceil:  ebdtnano_ceil,
        inner: ebdtnano_inner,
    }
}

#[inline]
fn epoch_to_bdt_f64(e: Epoch) -> f64 {
    // Mirrors the §3.4 banner: route through
    // `to_duration_in_time_scale(BDT)` to share the short-circuit
    // path the other GNSS scales get from `to_*_duration` directly.
    e.to_duration_in_time_scale(TimeScale::BDT).to_seconds()
}

def_walk_helpers!(
    f64_ebdt_walks,
    f64,
    Epoch,
    shift_epoch_tai,
    epoch_to_bdt_f64
);

fn ebdtf064_ceil(x: F064) -> Extended<Epoch> {
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
        return Extended::Finite(Epoch::from_tai_duration(HD::MIN));
    }
    let max_secs = bdt_max_secs_f64();
    let min_secs = bdt_min_secs_f64();
    if v > max_secs {
        return Extended::PosInf;
    }
    if v <= min_secs {
        return Extended::Finite(Epoch::from_tai_duration(HD::MIN));
    }
    let est = Epoch::from_bdt_seconds(v);
    let est_widen = epoch_to_bdt_f64(est);
    let (z, _) = if est_widen >= v {
        f64_ebdt_walks::descend_to_ceil(est, v)
    } else {
        f64_ebdt_walks::ascend_to_ceil(est, v)
    };
    Extended::Finite(z)
}

fn ebdtf064_inner(e: Extended<Epoch>) -> F064 {
    match e {
        Extended::NegInf => ExtendedFloat::Bot,
        Extended::Finite(e) => ExtendedFloat::Extend(epoch_to_bdt_f64(e)),
        Extended::PosInf => ExtendedFloat::Top,
    }
}

crate::conn_l! {
    /// `F064 → Extended<hifitime::Epoch>` — BDT seconds (since
    /// [`hifitime::BDT_REF_EPOCH`]) ↔ Epoch. Same shape as
    /// [`EGPSF064`] with the comparison frame routed through
    /// `epoch_to_bdt_f64` — i.e. `to_duration_in_time_scale(BDT).to_seconds()`,
    /// **not** `to_bdt_seconds()` — to avoid the upper-bound HD
    /// saturation documented in the §3.4 banner.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::hifi::EBDTF064;
    /// use connections::extended::Extended;
    /// use connections::float::ExtendedFloat;
    /// use hifitime::BDT_REF_EPOCH;
    ///
    /// let zero = ExtendedFloat::Extend(0.0_f64);
    /// assert_eq!(EBDTF064.ceil(zero), Extended::Finite(BDT_REF_EPOCH));
    /// ```
    pub EBDTF064 : F064 => Extended<Epoch> {
        ceil:  ebdtf064_ceil,
        inner: ebdtf064_inner,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[allow(unused_imports)]
    use crate::conn::{ConnL, ConnR};
    use crate::prop::arb::{
        arb_extended_hifi_epoch, arb_extended_hifi_epoch_bounded_f64, arb_hifi_bdt_nanos_in_range,
        arb_hifi_epoch, arb_hifi_gpst_nanos_in_range, arb_hifi_gst_nanos_in_range,
        arb_hifi_qzsst_nanos_in_range, arb_hifi_tai_nanos_in_range, arb_hifi_unix_nanos_in_range,
        extended_float_f64,
    };
    use crate::prop::{conn as conn_laws, lattice as lattice_laws};
    use proptest::prelude::*;

    // ── Preorder laws on `Epoch` ────────────────────────────────

    mod hifi_epoch_preorder {
        use super::*;
        #[allow(unused_imports)]
        use crate::conn::{ConnL, ConnR};

        proptest! {
            #[test]
            fn reflexive(x in arb_hifi_epoch()) {
                prop_assert!(lattice_laws::lattice_reflexive(&x));
            }

            #[test]
            fn transitive(x in arb_hifi_epoch(), y in arb_hifi_epoch(), z in arb_hifi_epoch()) {
                prop_assert!(lattice_laws::lattice_transitive(&x, &y, &z));
            }

            #[test]
            fn antisymmetric(x in arb_hifi_epoch(), y in arb_hifi_epoch()) {
                prop_assert!(lattice_laws::lattice_antisymmetric(&x, &y));
            }

            #[test]
            fn bot(x in arb_hifi_epoch()) {
                let bot = Epoch::from_tai_duration(HD::MIN);
                prop_assert!(lattice_laws::lattice_bot(&bot, &x));
            }

            #[test]
            fn top(x in arb_hifi_epoch()) {
                let top = Epoch::from_tai_duration(HD::MAX);
                prop_assert!(lattice_laws::lattice_top(&top, &x));
            }
        }
    }

    // ── ETAIHDUR spot checks ────────────────────────────────────

    #[test]
    fn etaihdur_j1900_zero() {
        let j1900 = Epoch::from_tai_duration(HD::ZERO);
        assert_eq!(ETAIHDUR.ceil(j1900), HD::ZERO);
        assert_eq!(ETAIHDUR.floor(j1900), HD::ZERO);
        assert_eq!(ETAIHDUR.upper(HD::ZERO), j1900);
        assert_eq!(ETAIHDUR.lower(HD::ZERO), j1900);
    }

    #[test]
    fn etaihdur_unix_ref_round_trip() {
        // UNIX_REF_EPOCH's underlying TAI duration is the well-known
        // ~70-year offset; the Conn projects through it bijectively.
        let unix_dur = UNIX_REF_EPOCH.to_tai_duration();
        assert_eq!(ETAIHDUR.ceil(UNIX_REF_EPOCH), unix_dur);
        assert_eq!(ETAIHDUR.upper(unix_dur), Epoch::from_tai_duration(unix_dur),);
    }

    // ── ETAINANO spot checks ────────────────────────────────────

    #[test]
    fn etainano_j1900_zero() {
        let j1900 = Epoch::from_tai_duration(HD::ZERO);
        assert_eq!(ETAINANO.ceil(Extended::Finite(j1900)), 0_i128);
        assert_eq!(ETAINANO.upper(0_i128), Extended::Finite(j1900));
    }

    #[test]
    fn etainano_unix_epoch() {
        let unix_in_tai_ns = UNIX_REF_EPOCH.to_tai_duration().total_nanoseconds();
        assert_eq!(
            ETAINANO.ceil(Extended::Finite(UNIX_REF_EPOCH)),
            unix_in_tai_ns,
        );
        // round-trips through inner — the result is a TAI-scale
        // Epoch with the same instant as UNIX_REF_EPOCH.
        let round_trip = ETAINANO.upper(unix_in_tai_ns);
        assert_eq!(round_trip, Extended::Finite(UNIX_REF_EPOCH));
    }

    #[test]
    fn etainano_saturation_extremes() {
        assert_eq!(ETAINANO.upper(i128::MAX), Extended::PosInf);
        assert_eq!(ETAINANO.upper(i128::MIN), Extended::NegInf);

        let max_n = HD::MAX.total_nanoseconds();
        assert_eq!(ETAINANO.ceil(Extended::PosInf), max_n + 1);
        assert_eq!(ETAINANO.ceil(Extended::NegInf), i128::MIN);
    }

    // ── EUTCHDUR spot checks ────────────────────────────────────

    #[test]
    fn eutchdur_j1900_zero() {
        // J1900 in any scale ↔ HD::ZERO (no leap seconds before 1972,
        // so UTC == TAI here).
        let j1900 = Epoch::from_tai_duration(HD::ZERO);
        assert_eq!(EUTCHDUR.ceil(j1900), HD::ZERO);
        assert_eq!(EUTCHDUR.floor(j1900), HD::ZERO);
        let round_trip = EUTCHDUR.upper(HD::ZERO);
        // round_trip is a UTC-scale Epoch at the same instant as j1900.
        assert_eq!(round_trip, j1900);
    }

    #[test]
    fn eutchdur_unix_ref_round_trip() {
        // `forward(UNIX_REF_EPOCH)` is the UNIX epoch's UTC duration
        // since J1900 (~70 yr minus pre-1972 leap-second adjustments).
        let unix_utc = UNIX_REF_EPOCH.to_utc_duration();
        assert_eq!(EUTCHDUR.ceil(UNIX_REF_EPOCH), unix_utc);
    }

    // ── EUTCNANO spot checks ────────────────────────────────────

    #[test]
    fn eutcnano_unix_epoch_is_zero() {
        assert_eq!(EUTCNANO.ceil(Extended::Finite(UNIX_REF_EPOCH)), 0);
    }

    #[test]
    fn eutcnano_one_second_past_unix() {
        let one_sec = Epoch::from_unix_seconds(1.0);
        assert_eq!(EUTCNANO.ceil(Extended::Finite(one_sec)), 1_000_000_000_i128,);
    }

    #[test]
    fn eutcnano_y2038_round_trip() {
        // 2038-01-19 03:14:08 UTC = 2_147_483_648 unix seconds
        // (the i32-overflow boundary that motivates the i128 rung).
        let y2038_ns: i128 = 2_147_483_648 * 1_000_000_000;
        let y2038 = Epoch::from_unix_seconds(2_147_483_648.0);
        assert_eq!(EUTCNANO.ceil(Extended::Finite(y2038)), y2038_ns);
        assert_eq!(EUTCNANO.upper(y2038_ns), Extended::Finite(y2038));
    }

    #[test]
    fn eutcnano_saturation_extremes() {
        assert_eq!(EUTCNANO.upper(i128::MAX), Extended::PosInf);
        assert_eq!(EUTCNANO.upper(i128::MIN), Extended::NegInf);
    }

    // ── ETAIF064 / EUTCF064 spot checks ──────────────────────────

    #[test]
    fn etaif064_zero_is_j1900() {
        let zero = ExtendedFloat::Extend(0.0_f64);
        let j1900 = Epoch::from_tai_duration(HD::ZERO);
        assert_eq!(ETAIF064.ceil(zero), Extended::Finite(j1900));
        assert_eq!(ETAIF064.upper(Extended::Finite(j1900)), zero);
    }

    #[test]
    fn etaif064_half_second() {
        let half = ExtendedFloat::Extend(0.5_f64);
        let half_e = Epoch::from_tai_duration(HD::from_seconds(0.5));
        assert_eq!(ETAIF064.ceil(half), Extended::Finite(half_e));
    }

    #[test]
    fn etaif064_nan_arms() {
        assert_eq!(
            ETAIF064.ceil(ExtendedFloat::Extend(f64::NAN)),
            Extended::PosInf,
        );
    }

    #[test]
    fn etaif064_inf_arms() {
        assert_eq!(
            ETAIF064.ceil(ExtendedFloat::Extend(f64::INFINITY)),
            Extended::PosInf,
        );
        assert_eq!(
            ETAIF064.ceil(ExtendedFloat::Extend(f64::NEG_INFINITY)),
            Extended::Finite(Epoch::from_tai_duration(HD::MIN)),
        );
    }

    #[test]
    fn etaif064_bot_top_arms() {
        assert_eq!(ETAIF064.ceil(ExtendedFloat::Bot), Extended::NegInf);
        assert_eq!(ETAIF064.ceil(ExtendedFloat::Top), Extended::PosInf);
        assert_eq!(ETAIF064.upper(Extended::NegInf), ExtendedFloat::Bot);
        assert_eq!(ETAIF064.upper(Extended::PosInf), ExtendedFloat::Top);
    }

    #[test]
    fn etaif064_min_secs_fast_path() {
        // F064DURN regression-guard analog: at the integer-derived
        // `min_secs` the f64 plateau is wide enough that the walk
        // would take ~10¹² steps; the `<=` boundary check fast-paths
        // to MIN. Uses `hd_min_secs_f64()` (matches the implementation's
        // threshold) rather than `HD::MIN.to_seconds()` whose `±10²³`-
        // magnitude f64 cast could disagree by ULPs. (MR !63 round-3
        // shape, carried into MR !64.)
        let v_min = ExtendedFloat::Extend(hd_min_secs_f64());
        assert_eq!(
            ETAIF064.ceil(v_min),
            Extended::Finite(Epoch::from_tai_duration(HD::MIN)),
        );
    }

    // Pins the asymmetric-name vs equal-value relationship between
    // `unix_min_secs_f64` and `hd_min_secs_f64`. Documented at length
    // above their definitions; the test makes the equality machine-
    // checked so it can't drift silently. (MR !64 round-5 follow-up.)
    #[test]
    fn unix_min_secs_f64_equals_hd_min_secs_f64() {
        assert_eq!(unix_min_secs_f64(), hd_min_secs_f64());
    }

    // Spot-check for `eutcf064_ceil` at the lower-plateau interior:
    // an input one second below `hd_min_secs_f64` is still inside the
    // ~70-year non-identity zone where `from_unix_seconds` constructs
    // a Finite (non-saturated) TAI duration but the inner side
    // collapses to `hd_min_secs_f64` via UTC subtraction underflow.
    // The walk converges to `Finite(HD::MIN_TAI epoch)`. Guards
    // against regressions of the round-3/4 fast-path discussion.
    // (MR !64 round-5 follow-up.)
    #[test]
    fn eutcf064_below_hd_min_secs_collapses_to_hd_min() {
        let v = ExtendedFloat::Extend(hd_min_secs_f64() - 1.0);
        assert_eq!(
            EUTCF064.ceil(v),
            Extended::Finite(Epoch::from_tai_duration(HD::MIN)),
        );
    }

    #[test]
    fn eutcf064_zero_is_unix_epoch() {
        let zero = ExtendedFloat::Extend(0.0_f64);
        let unix_epoch = Epoch::from_unix_seconds(0.0);
        assert_eq!(EUTCF064.ceil(zero), Extended::Finite(unix_epoch));
        assert_eq!(EUTCF064.upper(Extended::Finite(unix_epoch)), zero);
    }

    #[test]
    fn eutcf064_one_second() {
        let one = ExtendedFloat::Extend(1.0_f64);
        let one_e = Epoch::from_unix_seconds(1.0);
        assert_eq!(EUTCF064.ceil(one), Extended::Finite(one_e));
    }

    #[test]
    fn eutcf064_nan_inf_bot_top() {
        assert_eq!(
            EUTCF064.ceil(ExtendedFloat::Extend(f64::NAN)),
            Extended::PosInf,
        );
        assert_eq!(
            EUTCF064.ceil(ExtendedFloat::Extend(f64::INFINITY)),
            Extended::PosInf,
        );
        assert_eq!(EUTCF064.ceil(ExtendedFloat::Bot), Extended::NegInf);
        assert_eq!(EUTCF064.ceil(ExtendedFloat::Top), Extended::PosInf);
    }

    // ── ETAIHDUR / EUTCHDUR iso law batteries ────────────────────

    crate::law_battery! {
        mod etaihdur_laws,
        conn: ETAIHDUR,
        fine:   arb_hifi_epoch(),
        coarse: crate::prop::arb::arb_hifi_duration(),
        subset: iso_only,
    }

    crate::law_battery! {
        mod eutchdur_laws,
        conn: EUTCHDUR,
        fine:   arb_hifi_epoch(),
        coarse: crate::prop::arb::arb_hifi_duration(),
        subset: iso_only,
    }

    // ── ETAINANO / EUTCNANO ConnL law batteries (hand-rolled) ───

    proptest! {
        #[test]
        fn etainano_galois_l(e in arb_extended_hifi_epoch(), b in any::<i128>()) {
            prop_assert!(conn_laws::galois_l(&ETAINANO, e, b));
        }

        #[test]
        fn etainano_closure_l(e in arb_extended_hifi_epoch()) {
            prop_assert!(conn_laws::closure_l(&ETAINANO, e));
        }

        #[test]
        fn etainano_kernel_l(b in any::<i128>()) {
            prop_assert!(conn_laws::kernel_l(&ETAINANO, b));
        }

        #[test]
        fn etainano_monotone_l(a in arb_extended_hifi_epoch(),
                               b in arb_extended_hifi_epoch()) {
            prop_assert!(conn_laws::monotone_l(&ETAINANO, a, b));
        }

        #[test]
        fn etainano_idempotent(e in arb_extended_hifi_epoch()) {
            prop_assert!(conn_laws::idempotent(&ETAINANO, e));
        }

        #[test]
        fn etainano_roundtrip_ceil(b in arb_hifi_tai_nanos_in_range()) {
            prop_assert!(conn_laws::roundtrip_ceil(&ETAINANO, b));
        }

        #[test]
        fn eutcnano_galois_l(e in arb_extended_hifi_epoch(), b in any::<i128>()) {
            prop_assert!(conn_laws::galois_l(&EUTCNANO, e, b));
        }

        #[test]
        fn eutcnano_closure_l(e in arb_extended_hifi_epoch()) {
            prop_assert!(conn_laws::closure_l(&EUTCNANO, e));
        }

        #[test]
        fn eutcnano_kernel_l(b in any::<i128>()) {
            prop_assert!(conn_laws::kernel_l(&EUTCNANO, b));
        }

        #[test]
        fn eutcnano_monotone_l(a in arb_extended_hifi_epoch(),
                               b in arb_extended_hifi_epoch()) {
            prop_assert!(conn_laws::monotone_l(&EUTCNANO, a, b));
        }

        #[test]
        fn eutcnano_idempotent(e in arb_extended_hifi_epoch()) {
            prop_assert!(conn_laws::idempotent(&EUTCNANO, e));
        }

        #[test]
        fn eutcnano_roundtrip_ceil(b in arb_hifi_unix_nanos_in_range()) {
            prop_assert!(conn_laws::roundtrip_ceil(&EUTCNANO, b));
        }
    }

    // ── ETAIF064 / EUTCF064 ConnL batteries (bounded float strats) ──

    proptest! {
        #![proptest_config(ProptestConfig { cases: 64, .. ProptestConfig::default() })]
        #[test]
        fn etaif064_galois_l(a in extended_float_f64(),
                             b in arb_extended_hifi_epoch_bounded_f64()) {
            prop_assert!(conn_laws::galois_l(&ETAIF064, a, b));
        }
        #[test]
        fn etaif064_closure_l(a in extended_float_f64()) {
            prop_assert!(conn_laws::closure_l(&ETAIF064, a));
        }
        #[test]
        fn etaif064_kernel_l(b in arb_extended_hifi_epoch_bounded_f64()) {
            prop_assert!(conn_laws::kernel_l(&ETAIF064, b));
        }
        #[test]
        fn etaif064_monotone_l(a1 in extended_float_f64(),
                               a2 in extended_float_f64()) {
            prop_assert!(conn_laws::monotone_l(&ETAIF064, a1, a2));
        }
        #[test]
        fn etaif064_idempotent(a in extended_float_f64()) {
            prop_assert!(conn_laws::idempotent_l(&ETAIF064, a));
        }
        #[test]
        fn eutcf064_galois_l(a in extended_float_f64(),
                             b in arb_extended_hifi_epoch_bounded_f64()) {
            prop_assert!(conn_laws::galois_l(&EUTCF064, a, b));
        }
        #[test]
        fn eutcf064_closure_l(a in extended_float_f64()) {
            prop_assert!(conn_laws::closure_l(&EUTCF064, a));
        }
        #[test]
        fn eutcf064_kernel_l(b in arb_extended_hifi_epoch_bounded_f64()) {
            prop_assert!(conn_laws::kernel_l(&EUTCF064, b));
        }
        #[test]
        fn eutcf064_monotone_l(a1 in extended_float_f64(),
                               a2 in extended_float_f64()) {
            prop_assert!(conn_laws::monotone_l(&EUTCF064, a1, a2));
        }
        #[test]
        fn eutcf064_idempotent(a in extended_float_f64()) {
            prop_assert!(conn_laws::idempotent_l(&EUTCF064, a));
        }
    }

    // ── §3 GNSS spot checks ──────────────────────────────────────

    #[test]
    fn egpshdur_ref_zero() {
        assert_eq!(EGPSHDUR.ceil(GPST_REF_EPOCH), HD::ZERO);
        assert_eq!(EGPSHDUR.upper(HD::ZERO), GPST_REF_EPOCH);
    }

    #[test]
    fn egpsnano_ref_zero() {
        assert_eq!(EGPSNANO.ceil(Extended::Finite(GPST_REF_EPOCH)), 0_i128);
        assert_eq!(EGPSNANO.upper(0_i128), Extended::Finite(GPST_REF_EPOCH));
    }

    #[test]
    fn egpsnano_saturation_extremes() {
        assert_eq!(EGPSNANO.upper(i128::MAX), Extended::PosInf);
        assert_eq!(EGPSNANO.upper(i128::MIN), Extended::NegInf);
        assert_eq!(EGPSNANO.ceil(Extended::NegInf), i128::MIN);
        let max_n =
            HD::MAX.total_nanoseconds() - GPST_REF_EPOCH.to_tai_duration().total_nanoseconds();
        assert_eq!(EGPSNANO.ceil(Extended::PosInf), max_n + 1);
    }

    #[test]
    fn egpsf064_zero_is_ref() {
        let zero = ExtendedFloat::Extend(0.0_f64);
        assert_eq!(EGPSF064.ceil(zero), Extended::Finite(GPST_REF_EPOCH));
    }

    #[test]
    fn egpsf064_nan_inf_bot_top() {
        assert_eq!(
            EGPSF064.ceil(ExtendedFloat::Extend(f64::NAN)),
            Extended::PosInf,
        );
        assert_eq!(
            EGPSF064.ceil(ExtendedFloat::Extend(f64::INFINITY)),
            Extended::PosInf,
        );
        assert_eq!(EGPSF064.ceil(ExtendedFloat::Bot), Extended::NegInf);
        assert_eq!(EGPSF064.ceil(ExtendedFloat::Top), Extended::PosInf);
    }

    #[test]
    fn eqzshdur_ref_zero() {
        assert_eq!(EQZSHDUR.ceil(QZSST_REF_EPOCH), HD::ZERO);
    }

    #[test]
    fn eqzsnano_ref_zero() {
        assert_eq!(EQZSNANO.ceil(Extended::Finite(QZSST_REF_EPOCH)), 0_i128);
    }

    #[test]
    fn eqzsnano_saturation_extremes() {
        assert_eq!(EQZSNANO.upper(i128::MAX), Extended::PosInf);
        assert_eq!(EQZSNANO.upper(i128::MIN), Extended::NegInf);
        assert_eq!(EQZSNANO.ceil(Extended::NegInf), i128::MIN);
        let max_n =
            HD::MAX.total_nanoseconds() - QZSST_REF_EPOCH.to_tai_duration().total_nanoseconds();
        assert_eq!(EQZSNANO.ceil(Extended::PosInf), max_n + 1);
    }

    #[test]
    fn eqzsf064_zero_is_ref() {
        let zero = ExtendedFloat::Extend(0.0_f64);
        // QZSST_REF_EPOCH and GPST_REF_EPOCH are instant-equal but
        // the inner-side answer is constructed via from_qzsst_seconds,
        // which produces a QZSST-tagged Epoch. Compare on instant via
        // Epoch's Eq (which is scale-aware via to_parts).
        assert_eq!(EQZSF064.ceil(zero), Extended::Finite(QZSST_REF_EPOCH));
    }

    #[test]
    fn egsthdur_ref_zero() {
        assert_eq!(EGSTHDUR.ceil(GST_REF_EPOCH), HD::ZERO);
    }

    #[test]
    fn egstnano_ref_zero() {
        assert_eq!(EGSTNANO.ceil(Extended::Finite(GST_REF_EPOCH)), 0_i128);
    }

    #[test]
    fn egstnano_saturation_extremes() {
        assert_eq!(EGSTNANO.upper(i128::MAX), Extended::PosInf);
        assert_eq!(EGSTNANO.upper(i128::MIN), Extended::NegInf);
        assert_eq!(EGSTNANO.ceil(Extended::NegInf), i128::MIN);
        let max_n =
            HD::MAX.total_nanoseconds() - GST_REF_EPOCH.to_tai_duration().total_nanoseconds();
        assert_eq!(EGSTNANO.ceil(Extended::PosInf), max_n + 1);
    }

    #[test]
    fn egstf064_zero_is_ref() {
        let zero = ExtendedFloat::Extend(0.0_f64);
        assert_eq!(EGSTF064.ceil(zero), Extended::Finite(GST_REF_EPOCH));
    }

    #[test]
    fn ebdthdur_ref_zero() {
        assert_eq!(EBDTHDUR.ceil(BDT_REF_EPOCH), HD::ZERO);
    }

    #[test]
    fn ebdtnano_ref_zero() {
        assert_eq!(EBDTNANO.ceil(Extended::Finite(BDT_REF_EPOCH)), 0_i128);
    }

    #[test]
    fn ebdtnano_saturation_extremes() {
        assert_eq!(EBDTNANO.upper(i128::MAX), Extended::PosInf);
        assert_eq!(EBDTNANO.upper(i128::MIN), Extended::NegInf);
        assert_eq!(EBDTNANO.ceil(Extended::NegInf), i128::MIN);
        let max_n =
            HD::MAX.total_nanoseconds() - BDT_REF_EPOCH.to_tai_duration().total_nanoseconds();
        assert_eq!(EBDTNANO.ceil(Extended::PosInf), max_n + 1);
    }

    #[test]
    fn ebdtf064_zero_is_ref() {
        let zero = ExtendedFloat::Extend(0.0_f64);
        assert_eq!(EBDTF064.ceil(zero), Extended::Finite(BDT_REF_EPOCH));
    }

    #[test]
    fn egps_known_offset_at_interior_epoch() {
        // Pick an interior TAI epoch well past GPST inception
        // (1980-01-06 UTC) and confirm `EGPSHDUR` projects it
        // through the ±19-leap-second-equivalent integer offset.
        // `SECONDS_GPS_TAI_OFFSET` is the J1900-TAI seconds at GPST
        // inception; for any TAI Epoch `e`,
        // `EGPSHDUR.ceil(e).to_seconds() == e.to_tai_seconds() − offset`.
        let e = Epoch::from_tai_seconds(3_000_000_000.0); // ~rough 1995 TAI
        let gpst_secs = EGPSHDUR.ceil(e).to_seconds();
        let expected = e.to_tai_seconds() - hifitime::SECONDS_GPS_TAI_OFFSET;
        assert!((gpst_secs - expected).abs() < 1e-6);
    }

    // ── §3 GNSS HDUR iso law batteries ───────────────────────────

    crate::law_battery! {
        mod egpshdur_laws,
        conn: EGPSHDUR,
        fine:   arb_hifi_epoch(),
        coarse: crate::prop::arb::arb_hifi_duration(),
        subset: iso_only,
    }

    crate::law_battery! {
        mod eqzshdur_laws,
        conn: EQZSHDUR,
        fine:   arb_hifi_epoch(),
        coarse: crate::prop::arb::arb_hifi_duration(),
        subset: iso_only,
    }

    crate::law_battery! {
        mod egsthdur_laws,
        conn: EGSTHDUR,
        fine:   arb_hifi_epoch(),
        coarse: crate::prop::arb::arb_hifi_duration(),
        subset: iso_only,
    }

    crate::law_battery! {
        mod ebdthdur_laws,
        conn: EBDTHDUR,
        fine:   arb_hifi_epoch(),
        coarse: crate::prop::arb::arb_hifi_duration(),
        subset: iso_only,
    }

    // ── §3 GNSS NANO ConnL batteries (hand-rolled) ───────────────

    proptest! {
        #[test]
        fn egpsnano_galois_l(e in arb_extended_hifi_epoch(), b in any::<i128>()) {
            prop_assert!(conn_laws::galois_l(&EGPSNANO, e, b));
        }
        #[test]
        fn egpsnano_closure_l(e in arb_extended_hifi_epoch()) {
            prop_assert!(conn_laws::closure_l(&EGPSNANO, e));
        }
        #[test]
        fn egpsnano_kernel_l(b in any::<i128>()) {
            prop_assert!(conn_laws::kernel_l(&EGPSNANO, b));
        }
        #[test]
        fn egpsnano_monotone_l(a in arb_extended_hifi_epoch(),
                               b in arb_extended_hifi_epoch()) {
            prop_assert!(conn_laws::monotone_l(&EGPSNANO, a, b));
        }
        #[test]
        fn egpsnano_idempotent(e in arb_extended_hifi_epoch()) {
            prop_assert!(conn_laws::idempotent(&EGPSNANO, e));
        }
        #[test]
        fn egpsnano_roundtrip_ceil(b in arb_hifi_gpst_nanos_in_range()) {
            prop_assert!(conn_laws::roundtrip_ceil(&EGPSNANO, b));
        }

        #[test]
        fn eqzsnano_galois_l(e in arb_extended_hifi_epoch(), b in any::<i128>()) {
            prop_assert!(conn_laws::galois_l(&EQZSNANO, e, b));
        }
        #[test]
        fn eqzsnano_closure_l(e in arb_extended_hifi_epoch()) {
            prop_assert!(conn_laws::closure_l(&EQZSNANO, e));
        }
        #[test]
        fn eqzsnano_kernel_l(b in any::<i128>()) {
            prop_assert!(conn_laws::kernel_l(&EQZSNANO, b));
        }
        #[test]
        fn eqzsnano_monotone_l(a in arb_extended_hifi_epoch(),
                               b in arb_extended_hifi_epoch()) {
            prop_assert!(conn_laws::monotone_l(&EQZSNANO, a, b));
        }
        #[test]
        fn eqzsnano_idempotent(e in arb_extended_hifi_epoch()) {
            prop_assert!(conn_laws::idempotent(&EQZSNANO, e));
        }
        #[test]
        fn eqzsnano_roundtrip_ceil(b in arb_hifi_qzsst_nanos_in_range()) {
            prop_assert!(conn_laws::roundtrip_ceil(&EQZSNANO, b));
        }

        #[test]
        fn egstnano_galois_l(e in arb_extended_hifi_epoch(), b in any::<i128>()) {
            prop_assert!(conn_laws::galois_l(&EGSTNANO, e, b));
        }
        #[test]
        fn egstnano_closure_l(e in arb_extended_hifi_epoch()) {
            prop_assert!(conn_laws::closure_l(&EGSTNANO, e));
        }
        #[test]
        fn egstnano_kernel_l(b in any::<i128>()) {
            prop_assert!(conn_laws::kernel_l(&EGSTNANO, b));
        }
        #[test]
        fn egstnano_monotone_l(a in arb_extended_hifi_epoch(),
                               b in arb_extended_hifi_epoch()) {
            prop_assert!(conn_laws::monotone_l(&EGSTNANO, a, b));
        }
        #[test]
        fn egstnano_idempotent(e in arb_extended_hifi_epoch()) {
            prop_assert!(conn_laws::idempotent(&EGSTNANO, e));
        }
        #[test]
        fn egstnano_roundtrip_ceil(b in arb_hifi_gst_nanos_in_range()) {
            prop_assert!(conn_laws::roundtrip_ceil(&EGSTNANO, b));
        }

        #[test]
        fn ebdtnano_galois_l(e in arb_extended_hifi_epoch(), b in any::<i128>()) {
            prop_assert!(conn_laws::galois_l(&EBDTNANO, e, b));
        }
        #[test]
        fn ebdtnano_closure_l(e in arb_extended_hifi_epoch()) {
            prop_assert!(conn_laws::closure_l(&EBDTNANO, e));
        }
        #[test]
        fn ebdtnano_kernel_l(b in any::<i128>()) {
            prop_assert!(conn_laws::kernel_l(&EBDTNANO, b));
        }
        #[test]
        fn ebdtnano_monotone_l(a in arb_extended_hifi_epoch(),
                               b in arb_extended_hifi_epoch()) {
            prop_assert!(conn_laws::monotone_l(&EBDTNANO, a, b));
        }
        #[test]
        fn ebdtnano_idempotent(e in arb_extended_hifi_epoch()) {
            prop_assert!(conn_laws::idempotent(&EBDTNANO, e));
        }
        #[test]
        fn ebdtnano_roundtrip_ceil(b in arb_hifi_bdt_nanos_in_range()) {
            prop_assert!(conn_laws::roundtrip_ceil(&EBDTNANO, b));
        }

        // GPST and QZSST share their reference epoch in hifitime; the
        // two NANO Conns must agree numerically on every input
        // regardless of the input Epoch's scale tag.
        #[test]
        fn egpsnano_eq_eqzsnano(e in arb_extended_hifi_epoch()) {
            prop_assert_eq!(EGPSNANO.ceil(e), EQZSNANO.ceil(e));
        }
        #[test]
        fn egpshdur_eq_eqzshdur(e in arb_hifi_epoch()) {
            prop_assert_eq!(EGPSHDUR.ceil(e), EQZSHDUR.ceil(e));
        }
    }

    // ── §3 GNSS F064 ConnL batteries (bounded float strats) ──────

    proptest! {
        #![proptest_config(ProptestConfig { cases: 64, .. ProptestConfig::default() })]

        #[test]
        fn egpsf064_galois_l(a in extended_float_f64(),
                             b in arb_extended_hifi_epoch_bounded_f64()) {
            prop_assert!(conn_laws::galois_l(&EGPSF064, a, b));
        }
        #[test]
        fn egpsf064_closure_l(a in extended_float_f64()) {
            prop_assert!(conn_laws::closure_l(&EGPSF064, a));
        }
        #[test]
        fn egpsf064_kernel_l(b in arb_extended_hifi_epoch_bounded_f64()) {
            prop_assert!(conn_laws::kernel_l(&EGPSF064, b));
        }
        #[test]
        fn egpsf064_monotone_l(a1 in extended_float_f64(),
                               a2 in extended_float_f64()) {
            prop_assert!(conn_laws::monotone_l(&EGPSF064, a1, a2));
        }
        #[test]
        fn egpsf064_idempotent(a in extended_float_f64()) {
            prop_assert!(conn_laws::idempotent_l(&EGPSF064, a));
        }

        #[test]
        fn eqzsf064_galois_l(a in extended_float_f64(),
                             b in arb_extended_hifi_epoch_bounded_f64()) {
            prop_assert!(conn_laws::galois_l(&EQZSF064, a, b));
        }
        #[test]
        fn eqzsf064_closure_l(a in extended_float_f64()) {
            prop_assert!(conn_laws::closure_l(&EQZSF064, a));
        }
        #[test]
        fn eqzsf064_kernel_l(b in arb_extended_hifi_epoch_bounded_f64()) {
            prop_assert!(conn_laws::kernel_l(&EQZSF064, b));
        }
        #[test]
        fn eqzsf064_monotone_l(a1 in extended_float_f64(),
                               a2 in extended_float_f64()) {
            prop_assert!(conn_laws::monotone_l(&EQZSF064, a1, a2));
        }
        #[test]
        fn eqzsf064_idempotent(a in extended_float_f64()) {
            prop_assert!(conn_laws::idempotent_l(&EQZSF064, a));
        }

        #[test]
        fn egstf064_galois_l(a in extended_float_f64(),
                             b in arb_extended_hifi_epoch_bounded_f64()) {
            prop_assert!(conn_laws::galois_l(&EGSTF064, a, b));
        }
        #[test]
        fn egstf064_closure_l(a in extended_float_f64()) {
            prop_assert!(conn_laws::closure_l(&EGSTF064, a));
        }
        #[test]
        fn egstf064_kernel_l(b in arb_extended_hifi_epoch_bounded_f64()) {
            prop_assert!(conn_laws::kernel_l(&EGSTF064, b));
        }
        #[test]
        fn egstf064_monotone_l(a1 in extended_float_f64(),
                               a2 in extended_float_f64()) {
            prop_assert!(conn_laws::monotone_l(&EGSTF064, a1, a2));
        }
        #[test]
        fn egstf064_idempotent(a in extended_float_f64()) {
            prop_assert!(conn_laws::idempotent_l(&EGSTF064, a));
        }

        #[test]
        fn ebdtf064_galois_l(a in extended_float_f64(),
                             b in arb_extended_hifi_epoch_bounded_f64()) {
            prop_assert!(conn_laws::galois_l(&EBDTF064, a, b));
        }
        #[test]
        fn ebdtf064_closure_l(a in extended_float_f64()) {
            prop_assert!(conn_laws::closure_l(&EBDTF064, a));
        }
        #[test]
        fn ebdtf064_kernel_l(b in arb_extended_hifi_epoch_bounded_f64()) {
            prop_assert!(conn_laws::kernel_l(&EBDTF064, b));
        }
        #[test]
        fn ebdtf064_monotone_l(a1 in extended_float_f64(),
                               a2 in extended_float_f64()) {
            prop_assert!(conn_laws::monotone_l(&EBDTF064, a1, a2));
        }
        #[test]
        fn ebdtf064_idempotent(a in extended_float_f64()) {
            prop_assert!(conn_laws::idempotent_l(&EBDTF064, a));
        }
    }
}
