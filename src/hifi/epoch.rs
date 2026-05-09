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
//! - **`EUTC*`** uses **J1900 UTC** as the implicit zero,
//!   leap-second-aware. Only [`EUTCHDUR`] populates this family
//!   (UNIX-anchoring would push the iso's round-trip boundary
//!   outside `HD::MAX` — see the `EUTCHDUR` doc for the
//!   derivation).
//! - **`EUNX*`** uses **UNIX EPOCH UTC** (1970-01-01 00:00:00) as
//!   the implicit zero — the integer-rung / float-rung bridges
//!   ([`EUNXNANO`], [`F064EUNX`]) that match
//!   `ODTMNANO`'s convention so callers
//!   moving values between `time::OffsetDateTime` and
//!   `hifitime::Epoch` get numerically matching projections.
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
//!   `conn_l!`, ODTMNANO shape (asymmetric saturation: `ceil(NegInf)
//!   = i128::MIN`, `ceil(PosInf) = max + 1`).
//! - **`F064E{xx}`** — `F064 → Extended<Epoch>` via 1 ns ULP walks
//!   on the underlying TAI Duration. F064TDUR port; the comparison
//!   widens through `to_tai_seconds` (ETAI) or `to_unix_seconds`
//!   (EUNX), but the **walk** is always on TAI Duration so the
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
/// where `EUNXNANO.inner` round-trips losslessly through `ceil`.
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
// `unix_{min,max}_nanos` (which serve EUNXNANO's i128 inner threshold)
// rather than from a UNIX-shifted `from_unix_seconds` boundary. The
// asymmetry: `unix_min_nanos == hd_min_nanos` (unshifted, see its
// doc), so `unix_min_secs_f64 == hd_min_secs_f64`. This **is** the
// correct fast-path threshold for `f064eunx_ceil` despite the naming
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
    /// `ODTMNANO`: source-side `Extended`,
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

// ── F064ETAI ─────────────────────────────────────────────────────
//
// Float-to-Epoch bridge via 1ns ULP walks on the underlying TAI
// Duration. Mirrors F064TDUR's shape exactly, just with an Epoch
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

/// Total TAI-frame nanoseconds as i128 — `Epoch` is internally a TAI
/// `Duration`, so this is exact. Same value used as the
/// `solve_to_ceil` search axis across **every** scale; the scale
/// only changes the widening step (`to_*_seconds`), not the
/// underlying ns identity.
#[inline]
fn epoch_to_ns(e: Epoch) -> i128 {
    e.to_tai_duration().total_nanoseconds()
}

/// Saturating reconstruction; clamps at the underlying `HD::{MIN,MAX}`
/// representable as TAI-anchored Epochs.
#[inline]
fn epoch_from_ns(n: i128) -> Epoch {
    Epoch::from_tai_duration(crate::hifi::duration::hd_from_ns(n))
}

def_walk_helpers!(
    f64_etai_walks,
    f64,
    Epoch,
    shift_epoch_tai,
    epoch_to_tai_f64,
    epoch_to_ns,
    epoch_from_ns
);

fn f064etai_ceil(x: F064) -> Extended<Epoch> {
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
    // Same `<=` rationale as F064TDUR: at v == min_secs, the f64
    // plateau is wide enough that ULP-walking would take ~10¹²
    // steps. Fast-path to MIN.
    if v <= min_secs {
        return Extended::Finite(Epoch::from_tai_duration(HD::MIN));
    }
    let est = Epoch::from_tai_seconds(v);
    let (z, _) = f64_etai_walks::solve_to_ceil(est, v);
    Extended::Finite(z)
}

fn f064etai_inner(e: Extended<Epoch>) -> F064 {
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
    /// as `ConnL` (matches `F064TDUR` rationale, Plan 32).
    ///
    /// Saturation arms mirror `F064TDUR`: NaN → PosInf, ±∞ → PosInf
    /// / `Finite(Epoch::from_tai_duration(HD::MIN))`, Bot → NegInf,
    /// Top → PosInf.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::hifi::F064ETAI;
    /// use connections::extended::Extended;
    /// use connections::float::ExtendedFloat;
    /// use hifitime::{Duration as HDuration, Epoch};
    ///
    /// // 0.5 TAI seconds past J1900.
    /// let half = ExtendedFloat::Extend(0.5_f64);
    /// let half_e = Epoch::from_tai_duration(HDuration::from_seconds(0.5));
    /// assert_eq!(F064ETAI.ceil(half), Extended::Finite(half_e));
    /// ```
    pub F064ETAI : F064 => Extended<Epoch> {
        ceil:  f064etai_ceil,
        inner: f064etai_inner,
    }
}

// ── Proof-only walk-step probe (TAI scale) ──────────────────────
//
// Mirrors the production `f064etai_ceil` walk-entry but returns
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

#[cfg(kani)]
pub(crate) fn f64_etai_ceil_solve_steps_for_proof(v: f64) -> (Epoch, u32) {
    let est = Epoch::from_tai_seconds(v);
    f64_etai_walks::solve_to_ceil(est, v)
}

// ── EUTCHDUR ─────────────────────────────────────────────────────

#[inline]
fn eutchdur_forward(e: Epoch) -> HD {
    // UTC-scale Duration since J1900 UTC. Mirrors ETAIHDUR's J1900
    // anchor for consistency in the iso (UNIX-anchoring would put
    // `back(HD::MAX)` outside HD's range and break round-trip — the
    // EUNXNANO / F064EUNX pair carries the UNIX-anchored semantic).
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
    /// [`EUNXNANO`] / [`F064EUNX`] instead.
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

// ── EUNXNANO ─────────────────────────────────────────────────────

fn eunxnano_ceil(e: Extended<Epoch>) -> i128 {
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

fn eunxnano_inner(n: i128) -> Extended<Epoch> {
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
    /// `ODTMNANO`** for callers moving
    /// values between `time::OffsetDateTime` and `hifitime::Epoch`.
    ///
    /// One-sided left-Galois Conn (`Conn::new_l(ceil, inner)`),
    /// ODTMNANO shape with the standard asymmetric saturation:
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
    /// asymmetric design and matches the fact that the F064EUNX walk
    /// at the same magnitude also collapses to `Finite(HD::MIN_TAI
    /// epoch)` via inner-side HD-subtraction saturation.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::hifi::EUNXNANO;
    /// use connections::extended::Extended;
    /// use hifitime::{Epoch, UNIX_REF_EPOCH};
    ///
    /// // UNIX_REF_EPOCH is zero unix nanoseconds.
    /// assert_eq!(EUNXNANO.ceil(Extended::Finite(UNIX_REF_EPOCH)), 0);
    ///
    /// // 1970-01-01 + 1 second = 10⁹ unix nanoseconds.
    /// let one_sec = Epoch::from_unix_seconds(1.0);
    /// assert_eq!(EUNXNANO.ceil(Extended::Finite(one_sec)), 1_000_000_000);
    /// ```
    pub EUNXNANO : Extended<Epoch> => i128 {
        ceil:  eunxnano_ceil,
        inner: eunxnano_inner,
    }
}

// ── F064EUNX ─────────────────────────────────────────────────────
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
    epoch_to_unix_f64,
    epoch_to_ns,
    epoch_from_ns
);

fn f064eunx_ceil(x: F064) -> Extended<Epoch> {
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
    let (z, _) = f64_eutc_walks::solve_to_ceil(est, v);
    Extended::Finite(z)
}

fn f064eunx_inner(e: Extended<Epoch>) -> F064 {
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
    /// Shape mirrors [`F064ETAI`] exactly with two changes:
    ///
    /// 1. **Reference**: UNIX EPOCH UTC, not J1900 TAI. So the
    ///    `f64` value `0.0` corresponds to `UNIX_REF_EPOCH`.
    /// 2. **Comparison frame**: `to_unix_seconds()` does the UTC
    ///    conversion (leap-second-aware via hifitime's baked-in
    ///    `LatestLeapSeconds`). The walk still advances the
    ///    underlying TAI Duration by 1 ns; the comparison widens
    ///    through unix seconds.
    ///
    /// One-sided `ConnL` for the same reason as `F064ETAI`:
    /// `inner` is non-injective on the f64 plateau at multi-decade
    /// magnitudes.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::hifi::F064EUNX;
    /// use connections::extended::Extended;
    /// use connections::float::ExtendedFloat;
    /// use hifitime::Epoch;
    ///
    /// // 0.0 unix seconds ↔ UNIX EPOCH.
    /// let zero = ExtendedFloat::Extend(0.0_f64);
    /// let unix_epoch = Epoch::from_unix_seconds(0.0);
    /// assert_eq!(F064EUNX.ceil(zero), Extended::Finite(unix_epoch));
    /// ```
    pub F064EUNX : F064 => Extended<Epoch> {
        ceil:  f064eunx_ceil,
        inner: f064eunx_inner,
    }
}

// ── §3 GNSS scales (GPST, GST, BDT, QZSST) ───────────────────────
//
// Each GNSS scale is an exact integer-second offset to TAI. The
// HDuration projection is therefore an `iso!` (degenerate ConnK);
// the i128 nanosecond projection is `ConnL` with the same
// ODTMNANO-shape asymmetric saturation as ETAI / EUTC; and the f64
// seconds projection is `ConnL` with 1 ns ULP walks on the underlying
// TAI Duration (`shift_epoch_tai`) and a per-scale comparison frame.
//
// References (all exact integer seconds, exposed publicly by hifitime):
// - GPST_REF_EPOCH  = 1980-01-06 UTC ≡ TAI − 19 s (`SECONDS_GPS_TAI_OFFSET_I64 = 2_524_953_619`)
// - QZSST_REF_EPOCH = GPST_REF_EPOCH (QZSS shares GPS's reference)
// - GST_REF_EPOCH   = 1999-08-21      (`SECONDS_GST_TAI_OFFSET_I64 = 3_144_268_819`)
// - BDT_REF_EPOCH   = 2005-12-31      (`SECONDS_BDT_TAI_OFFSET_I64 = 3_345_062_433`)
//
// Saturation bound asymmetry mirrors EUNXNANO exactly: `min_n =
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
        // `eunxnano_inner` whose `from_utc_duration` expects a J1900-
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
    /// ODTMNANO shape with asymmetric saturation:
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
    epoch_to_gpst_f64,
    epoch_to_ns,
    epoch_from_ns
);

fn f064egps_ceil(x: F064) -> Extended<Epoch> {
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
    // same reason as F064ETAI / F064EUNX: the f64 plateau there is
    // wide enough that walking would take ~10¹² steps and converge
    // to the same answer. (See §1 F064ETAI doc.)
    if v <= min_secs {
        return Extended::Finite(Epoch::from_tai_duration(HD::MIN));
    }
    let est = Epoch::from_gpst_seconds(v);
    let (z, _) = f64_egps_walks::solve_to_ceil(est, v);
    Extended::Finite(z)
}

fn f064egps_inner(e: Extended<Epoch>) -> F064 {
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
    /// `ConnL`, F064TDUR-shape; walks happen on the underlying TAI
    /// Duration in 1 ns ULPs (`shift_epoch_tai`); the comparison
    /// frame is `Epoch::to_gpst_seconds()`. Non-injective at multi-
    /// decade magnitudes (the f64 plateau widens with the absolute
    /// value), so this is `ConnL` not `ConnK` (matches `F064TDUR` /
    /// `F064ETAI` rationale).
    ///
    /// **NEG_INFINITY arm tag.** `ceil(Extend(f64::NEG_INFINITY))`
    /// returns `Finite(Epoch::from_tai_duration(HD::MIN))` — a
    /// **TAI**-tagged Epoch, not a GPST-tagged one. Inherited from
    /// the §1 `F064ETAI` design. The ConnL idempotent law still
    /// holds (`Epoch::Eq` is instant-based; the saturated subtraction
    /// in `to_gpst_seconds` makes successive `ceil ∘ inner` round-
    /// trips collapse to the same instant), but readers should not
    /// assume the result carries the GPST scale tag throughout.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::hifi::F064EGPS;
    /// use connections::extended::Extended;
    /// use connections::float::ExtendedFloat;
    /// use hifitime::GPST_REF_EPOCH;
    ///
    /// // GPST seconds zero ↔ GPST_REF_EPOCH.
    /// let zero = ExtendedFloat::Extend(0.0_f64);
    /// assert_eq!(F064EGPS.ceil(zero), Extended::Finite(GPST_REF_EPOCH));
    /// ```
    pub F064EGPS : F064 => Extended<Epoch> {
        ceil:  f064egps_ceil,
        inner: f064egps_inner,
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
    epoch_to_qzsst_f64,
    epoch_to_ns,
    epoch_from_ns
);

fn f064eqzs_ceil(x: F064) -> Extended<Epoch> {
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
    let (z, _) = f64_eqzs_walks::solve_to_ceil(est, v);
    Extended::Finite(z)
}

fn f064eqzs_inner(e: Extended<Epoch>) -> F064 {
    match e {
        Extended::NegInf => ExtendedFloat::Bot,
        Extended::Finite(e) => ExtendedFloat::Extend(e.to_qzsst_seconds()),
        Extended::PosInf => ExtendedFloat::Top,
    }
}

crate::conn_l! {
    /// `F064 → Extended<hifitime::Epoch>` — QZSS Time seconds (since
    /// [`hifitime::QZSST_REF_EPOCH`]) ↔ Epoch. Mirrors [`F064EGPS`],
    /// including the [NEG_INFINITY arm tag](F064EGPS) caveat
    /// (the `f64::NEG_INFINITY` arm yields a **TAI**-tagged Epoch,
    /// not a QZSST-tagged one — laws still hold under instant-based
    /// `Epoch::Eq`).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::hifi::F064EQZS;
    /// use connections::extended::Extended;
    /// use connections::float::ExtendedFloat;
    /// use hifitime::QZSST_REF_EPOCH;
    ///
    /// let zero = ExtendedFloat::Extend(0.0_f64);
    /// assert_eq!(F064EQZS.ceil(zero), Extended::Finite(QZSST_REF_EPOCH));
    /// ```
    pub F064EQZS : F064 => Extended<Epoch> {
        ceil:  f064eqzs_ceil,
        inner: f064eqzs_inner,
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
    epoch_to_gst_f64,
    epoch_to_ns,
    epoch_from_ns
);

fn f064egst_ceil(x: F064) -> Extended<Epoch> {
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
    let (z, _) = f64_egst_walks::solve_to_ceil(est, v);
    Extended::Finite(z)
}

fn f064egst_inner(e: Extended<Epoch>) -> F064 {
    match e {
        Extended::NegInf => ExtendedFloat::Bot,
        Extended::Finite(e) => ExtendedFloat::Extend(e.to_gst_seconds()),
        Extended::PosInf => ExtendedFloat::Top,
    }
}

crate::conn_l! {
    /// `F064 → Extended<hifitime::Epoch>` — GST seconds (since
    /// [`hifitime::GST_REF_EPOCH`]) ↔ Epoch. Same shape as
    /// [`F064EGPS`] with `to_gst_seconds` as the comparison frame.
    /// Same NEG_INFINITY tag caveat as [`F064EGPS`] (the arm yields
    /// a **TAI**-tagged Epoch, not a GST-tagged one — laws still
    /// hold under instant-based `Epoch::Eq`).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::hifi::F064EGST;
    /// use connections::extended::Extended;
    /// use connections::float::ExtendedFloat;
    /// use hifitime::GST_REF_EPOCH;
    ///
    /// let zero = ExtendedFloat::Extend(0.0_f64);
    /// assert_eq!(F064EGST.ceil(zero), Extended::Finite(GST_REF_EPOCH));
    /// ```
    pub F064EGST : F064 => Extended<Epoch> {
        ceil:  f064egst_ceil,
        inner: f064egst_inner,
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
    epoch_to_bdt_f64,
    epoch_to_ns,
    epoch_from_ns
);

fn f064ebdt_ceil(x: F064) -> Extended<Epoch> {
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
    let (z, _) = f64_ebdt_walks::solve_to_ceil(est, v);
    Extended::Finite(z)
}

fn f064ebdt_inner(e: Extended<Epoch>) -> F064 {
    match e {
        Extended::NegInf => ExtendedFloat::Bot,
        Extended::Finite(e) => ExtendedFloat::Extend(epoch_to_bdt_f64(e)),
        Extended::PosInf => ExtendedFloat::Top,
    }
}

crate::conn_l! {
    /// `F064 → Extended<hifitime::Epoch>` — BDT seconds (since
    /// [`hifitime::BDT_REF_EPOCH`]) ↔ Epoch. Same shape as
    /// [`F064EGPS`] with the comparison frame routed through
    /// `epoch_to_bdt_f64` — i.e. `to_duration_in_time_scale(BDT).to_seconds()`,
    /// **not** `to_bdt_seconds()` — to avoid the upper-bound HD
    /// saturation documented in the §3.4 banner. Same NEG_INFINITY
    /// tag caveat as [`F064EGPS`] (the arm yields a **TAI**-tagged
    /// Epoch — laws hold under instant-based `Epoch::Eq`).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::hifi::F064EBDT;
    /// use connections::extended::Extended;
    /// use connections::float::ExtendedFloat;
    /// use hifitime::BDT_REF_EPOCH;
    ///
    /// let zero = ExtendedFloat::Extend(0.0_f64);
    /// assert_eq!(F064EBDT.ceil(zero), Extended::Finite(BDT_REF_EPOCH));
    /// ```
    pub F064EBDT : F064 => Extended<Epoch> {
        ceil:  f064ebdt_ceil,
        inner: f064ebdt_inner,
    }
}

// ── §4 Relativistic scales (TT, ET, TDB) ─────────────────────────
//
// Three F064 Conns: F064ETDT (Terrestrial Time), F064ETDE (Ephemeris
// Time, NAIF SPICE), F064ETDB (Barycentric Dynamical Time, ESA
// algorithm). HDUR / NANO projections are **deferred** for the entire
// relativistic family:
//
// - **TT.** TT = TAI + 32.184 s exact (`hifitime::TT_OFFSET_MS = 32_184`,
//   interpreted in milliseconds at `epoch/mod.rs:70` and `:305`).
//   The forward direction is **additive**, so at TAI HD::MAX the
//   `to_tt_duration` arithmetic saturates at HD::MAX (verified at
//   `duration/ops.rs:155-211`), losing 32.184 s. The iso `back ∘
//   forward` then differs from the original by 32.184 s under
//   `Epoch::Eq`, breaking the law. ConnL demotion doesn't recover
//   either: no HD value `b` satisfies `inner(b) = a` for `a` at TAI
//   HD::MAX. Plan 45 ships F064 only — the walk's fast-paths
//   intercept boundary inputs before saturation hits.
//
// - **ET / TDB.** Lossy iterative algorithms (NAIF Newton-Raphson at
//   `epoch/mod.rs:306-331`, ESA polynomial sin/cos at `:332-346`).
//   Round-trip diverges by ≤1 ns under `Epoch::Eq` — confirmed by
//   hifitime's own continuity tests at `tests/epoch.rs:2366,2420`,
//   which use a 1 ns tolerance. Integer-nanosecond projections would
//   imply false precision; F064 is the natural frame.
//
// Reference epochs:
// - **TT** anchored at **J1900 TT** (= TAI J1900 minus 32.184 s,
//   stored as the instant with `to_tt_duration() == HD::ZERO`).
//   `to_tt_seconds(epoch)` returns elapsed TT seconds since J1900 TT.
// - **ET / TDB** anchored at **J2000 (TAI 2000-01-01 12:00:00)**
//   (`hifitime::J2000_REF_EPOCH`). `to_et_seconds(epoch)` returns
//   elapsed ET seconds since J2000 ET; same for TDB. Both ET and
//   TDB short-circuit at `to_time_scale(_)`'s subtractive arm, so
//   they don't suffer the +offset saturation TT does.

use hifitime::J2000_REF_EPOCH;

// ── §4 per-scale offset / float-bound helpers ───────────────────

/// Total nanoseconds of J2000 in TAI-since-J1900 units (≈ 3.16 × 10¹⁸).
/// ET and TDB are anchored at this instant via hifitime's
/// `prime_epoch_offset` machinery; their F064 walks use it as the
/// implicit subtractive offset (mirrors `gpst_ref_tai_ns` for the
/// GNSS scales).
#[inline]
fn j2000_tai_ns() -> i128 {
    J2000_REF_EPOCH.to_tai_duration().total_nanoseconds()
}

// TT bounds — J1900 anchored, +32.184 s safety margin to dodge the
// upper-end saturation. The fast-path `v > tt_max_secs_f64()` →
// PosInf intercepts inputs that would otherwise drive the walk into
// the saturated region.
const TT_OFFSET_NS: i128 = 32_184_000_000;

#[inline]
fn tt_min_nanos() -> i128 {
    hd_min_nanos()
}
#[inline]
fn tt_max_nanos() -> i128 {
    hd_max_nanos() - TT_OFFSET_NS
}
#[inline]
fn tt_min_secs_f64() -> f64 {
    (tt_min_nanos() / 1_000_000_000) as f64
}
#[inline]
fn tt_max_secs_f64() -> f64 {
    (tt_max_nanos() / 1_000_000_000) as f64
}

// ET / TDB share the J2000 reference. Same asymmetric bounds as the
// GNSS scales: `min` is unshifted (= `hd_min_nanos() / 1e9`) because
// the inner side's underflow at HD::MIN is the same as the bare HD
// boundary; `max` is shifted by `j2000_tai_ns()` because the inner
// addition `n + j2000_tai_ns()` would overflow HD beyond it.
#[inline]
fn et_min_secs_f64() -> f64 {
    (hd_min_nanos() / 1_000_000_000) as f64
}
#[inline]
fn et_max_secs_f64() -> f64 {
    ((hd_max_nanos() - j2000_tai_ns()) / 1_000_000_000) as f64
}
#[inline]
fn tdb_min_secs_f64() -> f64 {
    et_min_secs_f64()
}
#[inline]
fn tdb_max_secs_f64() -> f64 {
    et_max_secs_f64()
}

// ── §4.1 TT (Terrestrial Time) ───────────────────────────────────

#[inline]
fn epoch_to_tt_f64(e: Epoch) -> f64 {
    e.to_tt_seconds()
}

def_walk_helpers!(
    f64_etdt_walks,
    f64,
    Epoch,
    shift_epoch_tai,
    epoch_to_tt_f64,
    epoch_to_ns,
    epoch_from_ns
);

fn f064etdt_ceil(x: F064) -> Extended<Epoch> {
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
    let max_secs = tt_max_secs_f64();
    let min_secs = tt_min_secs_f64();
    if v > max_secs {
        return Extended::PosInf;
    }
    if v <= min_secs {
        return Extended::Finite(Epoch::from_tai_duration(HD::MIN));
    }
    let est = Epoch::from_tt_seconds(v);
    let (z, _) = f64_etdt_walks::solve_to_ceil(est, v);
    Extended::Finite(z)
}

fn f064etdt_inner(e: Extended<Epoch>) -> F064 {
    match e {
        Extended::NegInf => ExtendedFloat::Bot,
        Extended::Finite(e) => ExtendedFloat::Extend(e.to_tt_seconds()),
        Extended::PosInf => ExtendedFloat::Top,
    }
}

crate::conn_l! {
    /// `F064 → Extended<hifitime::Epoch>` — Terrestrial Time seconds
    /// (since **J1900 TT**, i.e. TAI 1900-01-01 minus 32.184 s) ↔ Epoch.
    ///
    /// TT = TAI + 32.184 s exact (`hifitime::TT_OFFSET_MS`). This is
    /// the **only** Terrestrial-Time Conn shipping in the crate;
    /// HDUR / NANO projections of TT have an unavoidable boundary
    /// failure at TAI HD::MAX where the +32.184 s forward saturates
    /// in `Duration::add` (`hifitime/src/duration/ops.rs:155-211`).
    /// The F064 walk-with-fast-paths intercepts inputs above
    /// `tt_max_secs_f64()` before the walk hits the saturated region,
    /// so this Conn is well-defined over the full f64 input domain.
    ///
    /// Same NEG_INFINITY tag caveat as [`F064EGPS`] (the saturated arm
    /// yields a **TAI**-tagged Epoch — laws hold under instant-based
    /// `Epoch::Eq`).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::hifi::F064ETDT;
    /// use connections::extended::Extended;
    /// use connections::float::ExtendedFloat;
    /// use hifitime::{Duration as HDuration, Epoch};
    ///
    /// // 0.0 TT seconds since J1900 TT = the instant whose TT-stored
    /// // duration is HD::ZERO.
    /// let zero = ExtendedFloat::Extend(0.0_f64);
    /// let j1900_tt = Epoch::from_tt_duration(HDuration::ZERO);
    /// assert_eq!(F064ETDT.ceil(zero), Extended::Finite(j1900_tt));
    /// ```
    pub F064ETDT : F064 => Extended<Epoch> {
        ceil:  f064etdt_ceil,
        inner: f064etdt_inner,
    }
}

// Proof-only walk + solver step probes — see `crate::kani_proofs::hifi_walk`.
#[cfg(kani)]
pub(crate) fn f64_etdt_ceil_walk_steps_for_proof(v: f64) -> (Epoch, u32) {
    let est = Epoch::from_tt_seconds(v);
    let est_widen = est.to_tt_seconds();
    if est_widen >= v {
        f64_etdt_walks::descend_to_ceil(est, v)
    } else {
        f64_etdt_walks::ascend_to_ceil(est, v)
    }
}

#[cfg(kani)]
pub(crate) fn f64_etdt_ceil_solve_steps_for_proof(v: f64) -> (Epoch, u32) {
    let est = Epoch::from_tt_seconds(v);
    f64_etdt_walks::solve_to_ceil(est, v)
}

// ── §4.2 ET (NAIF SPICE Ephemeris Time) ──────────────────────────

#[inline]
fn epoch_to_et_f64(e: Epoch) -> f64 {
    e.to_et_seconds()
}

def_walk_helpers!(
    f64_etde_walks,
    f64,
    Epoch,
    shift_epoch_tai,
    epoch_to_et_f64,
    epoch_to_ns,
    epoch_from_ns
);

fn f064etde_ceil(x: F064) -> Extended<Epoch> {
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
    let max_secs = et_max_secs_f64();
    let min_secs = et_min_secs_f64();
    if v > max_secs {
        return Extended::PosInf;
    }
    if v <= min_secs {
        return Extended::Finite(Epoch::from_tai_duration(HD::MIN));
    }
    let est = Epoch::from_et_seconds(v);
    let (z, _) = f64_etde_walks::solve_to_ceil(est, v);
    Extended::Finite(z)
}

fn f064etde_inner(e: Extended<Epoch>) -> F064 {
    match e {
        Extended::NegInf => ExtendedFloat::Bot,
        Extended::Finite(e) => ExtendedFloat::Extend(e.to_et_seconds()),
        Extended::PosInf => ExtendedFloat::Top,
    }
}

crate::conn_l! {
    /// `F064 → Extended<hifitime::Epoch>` — NAIF SPICE Ephemeris Time
    /// seconds (since **J2000 ET**) ↔ Epoch.
    ///
    /// **Lossy:** ET is computed via Newton-Raphson iteration over the
    /// NAIF coefficients (`hifitime/src/epoch/mod.rs:306-331`). The
    /// hifitime tolerance is 1 ns, and round-trip through this Conn
    /// is precise to **≤ 1 ns** under `Epoch::Eq` per
    /// `hifitime/tests/epoch.rs:2420`. For sub-ns precision the
    /// scale itself is undefined; F064 is the natural frame.
    ///
    /// Same NEG_INFINITY tag caveat as [`F064EGPS`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::hifi::F064ETDE;
    /// use connections::extended::Extended;
    /// use connections::float::ExtendedFloat;
    /// use hifitime::Epoch;
    ///
    /// // 0.0 ET seconds since J2000 ET = J2000 instant.
    /// let zero = ExtendedFloat::Extend(0.0_f64);
    /// let j2000_et = Epoch::from_et_seconds(0.0);
    /// // Round-trip is precise to ≤ 1 ns under instant Eq.
    /// match F064ETDE.ceil(zero) {
    ///     Extended::Finite(got) => {
    ///         assert!((got - j2000_et).abs() <= 1.0 * hifitime::Unit::Nanosecond);
    ///     }
    ///     _ => panic!("expected Finite"),
    /// }
    /// ```
    pub F064ETDE : F064 => Extended<Epoch> {
        ceil:  f064etde_ceil,
        inner: f064etde_inner,
    }
}

// ── §4.3 TDB (Barycentric Dynamical Time, ESA algorithm) ─────────

#[inline]
fn epoch_to_tdb_f64(e: Epoch) -> f64 {
    e.to_tdb_seconds()
}

def_walk_helpers!(
    f64_etdb_walks,
    f64,
    Epoch,
    shift_epoch_tai,
    epoch_to_tdb_f64,
    epoch_to_ns,
    epoch_from_ns
);

fn f064etdb_ceil(x: F064) -> Extended<Epoch> {
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
    let max_secs = tdb_max_secs_f64();
    let min_secs = tdb_min_secs_f64();
    if v > max_secs {
        return Extended::PosInf;
    }
    if v <= min_secs {
        return Extended::Finite(Epoch::from_tai_duration(HD::MIN));
    }
    let est = Epoch::from_tdb_seconds(v);
    let (z, _) = f64_etdb_walks::solve_to_ceil(est, v);
    Extended::Finite(z)
}

fn f064etdb_inner(e: Extended<Epoch>) -> F064 {
    match e {
        Extended::NegInf => ExtendedFloat::Bot,
        Extended::Finite(e) => ExtendedFloat::Extend(e.to_tdb_seconds()),
        Extended::PosInf => ExtendedFloat::Top,
    }
}

crate::conn_l! {
    /// `F064 → Extended<hifitime::Epoch>` — Barycentric Dynamical Time
    /// seconds (since **J2000 TDB**) ↔ Epoch.
    ///
    /// **Lossy:** TDB is computed via the ESA closed-form polynomial
    /// with periodic sin/cos correction (`hifitime/src/epoch/mod.rs:332-346`).
    /// The hifitime tolerance is 1 ns; round-trip through this Conn
    /// is precise to **≤ 1 ns** under `Epoch::Eq` per
    /// `hifitime/tests/epoch.rs:2366`. TDB is described as "more
    /// precise than SPICE ET" in hifitime
    /// (`initializers.rs:246-248`); the per-century divergence between
    /// ET and TDB is ≤ 30 µs, well above this Conn's f64 ULP at most
    /// real magnitudes.
    ///
    /// Same NEG_INFINITY tag caveat as [`F064EGPS`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::hifi::F064ETDB;
    /// use connections::extended::Extended;
    /// use connections::float::ExtendedFloat;
    /// use hifitime::Epoch;
    ///
    /// // 0.0 TDB seconds since J2000 TDB = J2000 instant.
    /// let zero = ExtendedFloat::Extend(0.0_f64);
    /// let j2000_tdb = Epoch::from_tdb_seconds(0.0);
    /// match F064ETDB.ceil(zero) {
    ///     Extended::Finite(got) => {
    ///         assert!((got - j2000_tdb).abs() <= 1.0 * hifitime::Unit::Nanosecond);
    ///     }
    ///     _ => panic!("expected Finite"),
    /// }
    /// ```
    pub F064ETDB : F064 => Extended<Epoch> {
        ceil:  f064etdb_ceil,
        inner: f064etdb_inner,
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

    // ── EUNXNANO spot checks ────────────────────────────────────

    #[test]
    fn eunxnano_unix_epoch_is_zero() {
        assert_eq!(EUNXNANO.ceil(Extended::Finite(UNIX_REF_EPOCH)), 0);
    }

    #[test]
    fn eunxnano_one_second_past_unix() {
        let one_sec = Epoch::from_unix_seconds(1.0);
        assert_eq!(EUNXNANO.ceil(Extended::Finite(one_sec)), 1_000_000_000_i128,);
    }

    #[test]
    fn eunxnano_y2038_round_trip() {
        // 2038-01-19 03:14:08 UTC = 2_147_483_648 unix seconds
        // (the i32-overflow boundary that motivates the i128 rung).
        let y2038_ns: i128 = 2_147_483_648 * 1_000_000_000;
        let y2038 = Epoch::from_unix_seconds(2_147_483_648.0);
        assert_eq!(EUNXNANO.ceil(Extended::Finite(y2038)), y2038_ns);
        assert_eq!(EUNXNANO.upper(y2038_ns), Extended::Finite(y2038));
    }

    #[test]
    fn eunxnano_saturation_extremes() {
        assert_eq!(EUNXNANO.upper(i128::MAX), Extended::PosInf);
        assert_eq!(EUNXNANO.upper(i128::MIN), Extended::NegInf);
    }

    // ── F064ETAI / F064EUNX spot checks ──────────────────────────

    #[test]
    fn f064etai_zero_is_j1900() {
        let zero = ExtendedFloat::Extend(0.0_f64);
        let j1900 = Epoch::from_tai_duration(HD::ZERO);
        assert_eq!(F064ETAI.ceil(zero), Extended::Finite(j1900));
        assert_eq!(F064ETAI.upper(Extended::Finite(j1900)), zero);
    }

    #[test]
    fn f064etai_half_second() {
        let half = ExtendedFloat::Extend(0.5_f64);
        let half_e = Epoch::from_tai_duration(HD::from_seconds(0.5));
        assert_eq!(F064ETAI.ceil(half), Extended::Finite(half_e));
    }

    #[test]
    fn f064etai_nan_arms() {
        assert_eq!(
            F064ETAI.ceil(ExtendedFloat::Extend(f64::NAN)),
            Extended::PosInf,
        );
    }

    #[test]
    fn f064etai_inf_arms() {
        assert_eq!(
            F064ETAI.ceil(ExtendedFloat::Extend(f64::INFINITY)),
            Extended::PosInf,
        );
        assert_eq!(
            F064ETAI.ceil(ExtendedFloat::Extend(f64::NEG_INFINITY)),
            Extended::Finite(Epoch::from_tai_duration(HD::MIN)),
        );
    }

    #[test]
    fn f064etai_bot_top_arms() {
        assert_eq!(F064ETAI.ceil(ExtendedFloat::Bot), Extended::NegInf);
        assert_eq!(F064ETAI.ceil(ExtendedFloat::Top), Extended::PosInf);
        assert_eq!(F064ETAI.upper(Extended::NegInf), ExtendedFloat::Bot);
        assert_eq!(F064ETAI.upper(Extended::PosInf), ExtendedFloat::Top);
    }

    #[test]
    fn f064etai_min_secs_fast_path() {
        // F064TDUR regression-guard analog: at the integer-derived
        // `min_secs` the f64 plateau is wide enough that the walk
        // would take ~10¹² steps; the `<=` boundary check fast-paths
        // to MIN. Uses `hd_min_secs_f64()` (matches the implementation's
        // threshold) rather than `HD::MIN.to_seconds()` whose `±10²³`-
        // magnitude f64 cast could disagree by ULPs. (MR !63 round-3
        // shape, carried into MR !64.)
        let v_min = ExtendedFloat::Extend(hd_min_secs_f64());
        assert_eq!(
            F064ETAI.ceil(v_min),
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

    // Spot-check for `f064eunx_ceil` at the lower-plateau interior:
    // an input one second below `hd_min_secs_f64` is still inside the
    // ~70-year non-identity zone where `from_unix_seconds` constructs
    // a Finite (non-saturated) TAI duration but the inner side
    // collapses to `hd_min_secs_f64` via UTC subtraction underflow.
    // The walk converges to `Finite(HD::MIN_TAI epoch)`. Guards
    // against regressions of the round-3/4 fast-path discussion.
    // (MR !64 round-5 follow-up.)
    #[test]
    fn f064eunx_below_hd_min_secs_collapses_to_hd_min() {
        let v = ExtendedFloat::Extend(hd_min_secs_f64() - 1.0);
        assert_eq!(
            F064EUNX.ceil(v),
            Extended::Finite(Epoch::from_tai_duration(HD::MIN)),
        );
    }

    #[test]
    fn f064eunx_zero_is_unix_epoch() {
        let zero = ExtendedFloat::Extend(0.0_f64);
        let unix_epoch = Epoch::from_unix_seconds(0.0);
        assert_eq!(F064EUNX.ceil(zero), Extended::Finite(unix_epoch));
        assert_eq!(F064EUNX.upper(Extended::Finite(unix_epoch)), zero);
    }

    #[test]
    fn f064eunx_one_second() {
        let one = ExtendedFloat::Extend(1.0_f64);
        let one_e = Epoch::from_unix_seconds(1.0);
        assert_eq!(F064EUNX.ceil(one), Extended::Finite(one_e));
    }

    #[test]
    fn f064eunx_nan_inf_bot_top() {
        assert_eq!(
            F064EUNX.ceil(ExtendedFloat::Extend(f64::NAN)),
            Extended::PosInf,
        );
        assert_eq!(
            F064EUNX.ceil(ExtendedFloat::Extend(f64::INFINITY)),
            Extended::PosInf,
        );
        assert_eq!(F064EUNX.ceil(ExtendedFloat::Bot), Extended::NegInf);
        assert_eq!(F064EUNX.ceil(ExtendedFloat::Top), Extended::PosInf);
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

    // ── ETAINANO / EUNXNANO ConnL law batteries (hand-rolled) ───

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
        fn eunxnano_galois_l(e in arb_extended_hifi_epoch(), b in any::<i128>()) {
            prop_assert!(conn_laws::galois_l(&EUNXNANO, e, b));
        }

        #[test]
        fn eunxnano_closure_l(e in arb_extended_hifi_epoch()) {
            prop_assert!(conn_laws::closure_l(&EUNXNANO, e));
        }

        #[test]
        fn eunxnano_kernel_l(b in any::<i128>()) {
            prop_assert!(conn_laws::kernel_l(&EUNXNANO, b));
        }

        #[test]
        fn eunxnano_monotone_l(a in arb_extended_hifi_epoch(),
                               b in arb_extended_hifi_epoch()) {
            prop_assert!(conn_laws::monotone_l(&EUNXNANO, a, b));
        }

        #[test]
        fn eunxnano_idempotent(e in arb_extended_hifi_epoch()) {
            prop_assert!(conn_laws::idempotent(&EUNXNANO, e));
        }

        #[test]
        fn eunxnano_roundtrip_ceil(b in arb_hifi_unix_nanos_in_range()) {
            prop_assert!(conn_laws::roundtrip_ceil(&EUNXNANO, b));
        }
    }

    // ── F064ETAI / F064EUNX ConnL batteries (bounded float strats) ──

    proptest! {
        #![proptest_config(ProptestConfig { cases: 64, .. ProptestConfig::default() })]
        #[test]
        fn f064etai_galois_l(a in extended_float_f64(),
                             b in arb_extended_hifi_epoch_bounded_f64()) {
            prop_assert!(conn_laws::galois_l(&F064ETAI, a, b));
        }
        #[test]
        fn f064etai_closure_l(a in extended_float_f64()) {
            prop_assert!(conn_laws::closure_l(&F064ETAI, a));
        }
        #[test]
        fn f064etai_kernel_l(b in arb_extended_hifi_epoch_bounded_f64()) {
            prop_assert!(conn_laws::kernel_l(&F064ETAI, b));
        }
        #[test]
        fn f064etai_monotone_l(a1 in extended_float_f64(),
                               a2 in extended_float_f64()) {
            prop_assert!(conn_laws::monotone_l(&F064ETAI, a1, a2));
        }
        #[test]
        fn f064etai_idempotent(a in extended_float_f64()) {
            prop_assert!(conn_laws::idempotent_l(&F064ETAI, a));
        }
        #[test]
        fn f064eunx_galois_l(a in extended_float_f64(),
                             b in arb_extended_hifi_epoch_bounded_f64()) {
            prop_assert!(conn_laws::galois_l(&F064EUNX, a, b));
        }
        #[test]
        fn f064eunx_closure_l(a in extended_float_f64()) {
            prop_assert!(conn_laws::closure_l(&F064EUNX, a));
        }
        #[test]
        fn f064eunx_kernel_l(b in arb_extended_hifi_epoch_bounded_f64()) {
            prop_assert!(conn_laws::kernel_l(&F064EUNX, b));
        }
        #[test]
        fn f064eunx_monotone_l(a1 in extended_float_f64(),
                               a2 in extended_float_f64()) {
            prop_assert!(conn_laws::monotone_l(&F064EUNX, a1, a2));
        }
        #[test]
        fn f064eunx_idempotent(a in extended_float_f64()) {
            prop_assert!(conn_laws::idempotent_l(&F064EUNX, a));
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
    fn f064egps_zero_is_ref() {
        let zero = ExtendedFloat::Extend(0.0_f64);
        assert_eq!(F064EGPS.ceil(zero), Extended::Finite(GPST_REF_EPOCH));
    }

    #[test]
    fn f064egps_nan_inf_bot_top() {
        assert_eq!(
            F064EGPS.ceil(ExtendedFloat::Extend(f64::NAN)),
            Extended::PosInf,
        );
        assert_eq!(
            F064EGPS.ceil(ExtendedFloat::Extend(f64::INFINITY)),
            Extended::PosInf,
        );
        assert_eq!(F064EGPS.ceil(ExtendedFloat::Bot), Extended::NegInf);
        assert_eq!(F064EGPS.ceil(ExtendedFloat::Top), Extended::PosInf);
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
    fn f064eqzs_zero_is_ref() {
        let zero = ExtendedFloat::Extend(0.0_f64);
        // QZSST_REF_EPOCH and GPST_REF_EPOCH are instant-equal but
        // the inner-side answer is constructed via from_qzsst_seconds,
        // which produces a QZSST-tagged Epoch. Compare on instant via
        // Epoch's Eq (which is scale-aware via to_parts).
        assert_eq!(F064EQZS.ceil(zero), Extended::Finite(QZSST_REF_EPOCH));
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
    fn f064egst_zero_is_ref() {
        let zero = ExtendedFloat::Extend(0.0_f64);
        assert_eq!(F064EGST.ceil(zero), Extended::Finite(GST_REF_EPOCH));
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
    fn f064ebdt_zero_is_ref() {
        let zero = ExtendedFloat::Extend(0.0_f64);
        assert_eq!(F064EBDT.ceil(zero), Extended::Finite(BDT_REF_EPOCH));
    }

    #[test]
    fn egps_known_offset_at_interior_epoch() {
        // Pick an interior TAI epoch well past GPST inception
        // (1980-01-06 UTC) and confirm `EGPSHDUR` projects it
        // through the +19-leap-second-equivalent integer offset.
        // The expected value uses the **literal** offset
        // `2_524_953_619` (J1900-TAI seconds at GPST inception, per
        // <https://gssc.esa.int/navipedia/index.php/Time_References_in_GNSS#GPS_Time_.28GPST.29>)
        // rather than `hifitime::SECONDS_GPS_TAI_OFFSET`, so the
        // assertion remains independent of the constant the Conn
        // itself transitively depends on. (MR !66 round-1.)
        let e = Epoch::from_tai_seconds(3_000_000_000.0); // ~rough 1995 TAI
        let gpst_secs = EGPSHDUR.ceil(e).to_seconds();
        let expected = e.to_tai_seconds() - 2_524_953_619.0;
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
        fn f064egps_galois_l(a in extended_float_f64(),
                             b in arb_extended_hifi_epoch_bounded_f64()) {
            prop_assert!(conn_laws::galois_l(&F064EGPS, a, b));
        }
        #[test]
        fn f064egps_closure_l(a in extended_float_f64()) {
            prop_assert!(conn_laws::closure_l(&F064EGPS, a));
        }
        #[test]
        fn f064egps_kernel_l(b in arb_extended_hifi_epoch_bounded_f64()) {
            prop_assert!(conn_laws::kernel_l(&F064EGPS, b));
        }
        #[test]
        fn f064egps_monotone_l(a1 in extended_float_f64(),
                               a2 in extended_float_f64()) {
            prop_assert!(conn_laws::monotone_l(&F064EGPS, a1, a2));
        }
        #[test]
        fn f064egps_idempotent(a in extended_float_f64()) {
            prop_assert!(conn_laws::idempotent_l(&F064EGPS, a));
        }

        #[test]
        fn f064eqzs_galois_l(a in extended_float_f64(),
                             b in arb_extended_hifi_epoch_bounded_f64()) {
            prop_assert!(conn_laws::galois_l(&F064EQZS, a, b));
        }
        #[test]
        fn f064eqzs_closure_l(a in extended_float_f64()) {
            prop_assert!(conn_laws::closure_l(&F064EQZS, a));
        }
        #[test]
        fn f064eqzs_kernel_l(b in arb_extended_hifi_epoch_bounded_f64()) {
            prop_assert!(conn_laws::kernel_l(&F064EQZS, b));
        }
        #[test]
        fn f064eqzs_monotone_l(a1 in extended_float_f64(),
                               a2 in extended_float_f64()) {
            prop_assert!(conn_laws::monotone_l(&F064EQZS, a1, a2));
        }
        #[test]
        fn f064eqzs_idempotent(a in extended_float_f64()) {
            prop_assert!(conn_laws::idempotent_l(&F064EQZS, a));
        }

        #[test]
        fn f064egst_galois_l(a in extended_float_f64(),
                             b in arb_extended_hifi_epoch_bounded_f64()) {
            prop_assert!(conn_laws::galois_l(&F064EGST, a, b));
        }
        #[test]
        fn f064egst_closure_l(a in extended_float_f64()) {
            prop_assert!(conn_laws::closure_l(&F064EGST, a));
        }
        #[test]
        fn f064egst_kernel_l(b in arb_extended_hifi_epoch_bounded_f64()) {
            prop_assert!(conn_laws::kernel_l(&F064EGST, b));
        }
        #[test]
        fn f064egst_monotone_l(a1 in extended_float_f64(),
                               a2 in extended_float_f64()) {
            prop_assert!(conn_laws::monotone_l(&F064EGST, a1, a2));
        }
        #[test]
        fn f064egst_idempotent(a in extended_float_f64()) {
            prop_assert!(conn_laws::idempotent_l(&F064EGST, a));
        }

        #[test]
        fn f064ebdt_galois_l(a in extended_float_f64(),
                             b in arb_extended_hifi_epoch_bounded_f64()) {
            prop_assert!(conn_laws::galois_l(&F064EBDT, a, b));
        }
        #[test]
        fn f064ebdt_closure_l(a in extended_float_f64()) {
            prop_assert!(conn_laws::closure_l(&F064EBDT, a));
        }
        #[test]
        fn f064ebdt_kernel_l(b in arb_extended_hifi_epoch_bounded_f64()) {
            prop_assert!(conn_laws::kernel_l(&F064EBDT, b));
        }
        #[test]
        fn f064ebdt_monotone_l(a1 in extended_float_f64(),
                               a2 in extended_float_f64()) {
            prop_assert!(conn_laws::monotone_l(&F064EBDT, a1, a2));
        }
        #[test]
        fn f064ebdt_idempotent(a in extended_float_f64()) {
            prop_assert!(conn_laws::idempotent_l(&F064EBDT, a));
        }
    }

    // ── §4 Relativistic spot checks ──────────────────────────────

    #[test]
    fn f064etdt_zero_is_j1900_tt() {
        // 0.0 TT seconds since J1900 TT = the instant whose
        // TT-stored Duration is HD::ZERO.
        let zero = ExtendedFloat::Extend(0.0_f64);
        let j1900_tt = Epoch::from_tt_duration(HD::ZERO);
        assert_eq!(F064ETDT.ceil(zero), Extended::Finite(j1900_tt));
    }

    #[test]
    fn f064etdt_nan_inf_bot_top() {
        assert_eq!(
            F064ETDT.ceil(ExtendedFloat::Extend(f64::NAN)),
            Extended::PosInf,
        );
        assert_eq!(
            F064ETDT.ceil(ExtendedFloat::Extend(f64::INFINITY)),
            Extended::PosInf,
        );
        assert_eq!(F064ETDT.ceil(ExtendedFloat::Bot), Extended::NegInf);
        assert_eq!(F064ETDT.ceil(ExtendedFloat::Top), Extended::PosInf);
    }

    #[test]
    fn f064etde_zero_is_near_j2000() {
        // 0.0 ET seconds since J2000 ET = J2000 instant (within 1 ns
        // due to the Newton-Raphson lossy round-trip).
        let zero = ExtendedFloat::Extend(0.0_f64);
        let j2000_et = Epoch::from_et_seconds(0.0);
        let result = F064ETDE.ceil(zero);
        match result {
            Extended::Finite(got) => {
                assert!(
                    (got - j2000_et).abs() < 1.0 * hifitime::Unit::Nanosecond,
                    "F064ETDE.ceil(0.0) = {:?}, expected near {:?}",
                    got,
                    j2000_et,
                );
            }
            other => panic!("expected Finite, got {:?}", other),
        }
    }

    #[test]
    fn f064etde_nan_inf_bot_top() {
        assert_eq!(
            F064ETDE.ceil(ExtendedFloat::Extend(f64::NAN)),
            Extended::PosInf,
        );
        assert_eq!(F064ETDE.ceil(ExtendedFloat::Bot), Extended::NegInf);
        assert_eq!(F064ETDE.ceil(ExtendedFloat::Top), Extended::PosInf);
    }

    #[test]
    fn f064etdb_zero_is_near_j2000() {
        // 0.0 TDB seconds since J2000 TDB = J2000 instant (within 1 ns
        // due to the ESA polynomial lossy round-trip).
        let zero = ExtendedFloat::Extend(0.0_f64);
        let j2000_tdb = Epoch::from_tdb_seconds(0.0);
        let result = F064ETDB.ceil(zero);
        match result {
            Extended::Finite(got) => {
                assert!(
                    (got - j2000_tdb).abs() < 1.0 * hifitime::Unit::Nanosecond,
                    "F064ETDB.ceil(0.0) = {:?}, expected near {:?}",
                    got,
                    j2000_tdb,
                );
            }
            other => panic!("expected Finite, got {:?}", other),
        }
    }

    #[test]
    fn f064etdb_nan_inf_bot_top() {
        assert_eq!(
            F064ETDB.ceil(ExtendedFloat::Extend(f64::NAN)),
            Extended::PosInf,
        );
        assert_eq!(F064ETDB.ceil(ExtendedFloat::Bot), Extended::NegInf);
        assert_eq!(F064ETDB.ceil(ExtendedFloat::Top), Extended::PosInf);
    }

    #[test]
    fn etdt_known_offset_at_interior_epoch() {
        // TT projection adds exactly 32.184 s to TAI on the interior.
        // Pick a TAI epoch well inside HD bounds and confirm the
        // offset is literal arithmetic, comparing through TT-seconds.
        let e = Epoch::from_tai_seconds(3_000_000_000.0);
        let tt_secs = e.to_tt_seconds();
        let tai_secs = e.to_tai_seconds();
        // TT_OFFSET_MS = 32_184 ms = 32.184 s exact.
        assert!((tt_secs - tai_secs - 32.184).abs() < 1e-6);
    }

    // ── §4 Relativistic F064 ConnL batteries (bounded float strats) ──

    proptest! {
        #![proptest_config(ProptestConfig { cases: 64, .. ProptestConfig::default() })]

        #[test]
        fn f064etdt_galois_l(a in extended_float_f64(),
                             b in arb_extended_hifi_epoch_bounded_f64()) {
            prop_assert!(conn_laws::galois_l(&F064ETDT, a, b));
        }
        #[test]
        fn f064etdt_closure_l(a in extended_float_f64()) {
            prop_assert!(conn_laws::closure_l(&F064ETDT, a));
        }
        #[test]
        fn f064etdt_kernel_l(b in arb_extended_hifi_epoch_bounded_f64()) {
            prop_assert!(conn_laws::kernel_l(&F064ETDT, b));
        }
        #[test]
        fn f064etdt_monotone_l(a1 in extended_float_f64(),
                               a2 in extended_float_f64()) {
            prop_assert!(conn_laws::monotone_l(&F064ETDT, a1, a2));
        }
        #[test]
        fn f064etdt_idempotent(a in extended_float_f64()) {
            prop_assert!(conn_laws::idempotent_l(&F064ETDT, a));
        }

        #[test]
        fn f064etde_galois_l(a in extended_float_f64(),
                             b in arb_extended_hifi_epoch_bounded_f64()) {
            prop_assert!(conn_laws::galois_l(&F064ETDE, a, b));
        }
        #[test]
        fn f064etde_closure_l(a in extended_float_f64()) {
            prop_assert!(conn_laws::closure_l(&F064ETDE, a));
        }
        #[test]
        fn f064etde_kernel_l(b in arb_extended_hifi_epoch_bounded_f64()) {
            prop_assert!(conn_laws::kernel_l(&F064ETDE, b));
        }
        #[test]
        fn f064etde_monotone_l(a1 in extended_float_f64(),
                               a2 in extended_float_f64()) {
            prop_assert!(conn_laws::monotone_l(&F064ETDE, a1, a2));
        }
        #[test]
        fn f064etde_idempotent(a in extended_float_f64()) {
            prop_assert!(conn_laws::idempotent_l(&F064ETDE, a));
        }

        #[test]
        fn f064etdb_galois_l(a in extended_float_f64(),
                             b in arb_extended_hifi_epoch_bounded_f64()) {
            prop_assert!(conn_laws::galois_l(&F064ETDB, a, b));
        }
        #[test]
        fn f064etdb_closure_l(a in extended_float_f64()) {
            prop_assert!(conn_laws::closure_l(&F064ETDB, a));
        }
        #[test]
        fn f064etdb_kernel_l(b in arb_extended_hifi_epoch_bounded_f64()) {
            prop_assert!(conn_laws::kernel_l(&F064ETDB, b));
        }
        #[test]
        fn f064etdb_monotone_l(a1 in extended_float_f64(),
                               a2 in extended_float_f64()) {
            prop_assert!(conn_laws::monotone_l(&F064ETDB, a1, a2));
        }
        #[test]
        fn f064etdb_idempotent(a in extended_float_f64()) {
            prop_assert!(conn_laws::idempotent_l(&F064ETDB, a));
        }
    }

    // ── §4 Relativistic ≤1 ns round-trip checks (J2000 only) ─────
    //
    // ET / TDB are lossy at the ≤1 ns level under hifitime's instant-
    // based `Eq` per `tests/epoch.rs:2366,2420` — but **only at J2000
    // itself**, where the f64 representation of the duration is ~0 and
    // the f64 ULP is at its smallest. Over the bounded f64 envelope
    // (`±10⁹ s` magnitude per `arb_hifi_duration_bounded_f64`), the
    // f64 ULP grows to ~10²·10⁻⁷ ≈ hundreds of ns, dominating any
    // hifitime-internal iteration error. So the broader proptest
    // tolerance test that the master plan called for is not
    // meaningful — galois_l already proves correctness as a one-sided
    // Conn. Spot-test the J2000 boundary instead, where the
    // 1 ns tolerance is the genuine measurement of the iteration.

    #[test]
    fn f064etde_at_j2000_within_1ns() {
        let j2000_et = Epoch::from_et_seconds(0.0);
        let ef = F064ETDE.upper(Extended::Finite(j2000_et));
        let recovered = F064ETDE.ceil(ef);
        match recovered {
            Extended::Finite(got) => {
                let drift = (got - j2000_et).abs();
                assert!(
                    drift <= 1.0 * hifitime::Unit::Nanosecond,
                    "ET round-trip at J2000 diverged: Δ {:?}",
                    drift,
                );
            }
            other => panic!("expected Finite, got {:?}", other),
        }
    }

    #[test]
    fn f064etdb_at_j2000_within_1ns() {
        let j2000_tdb = Epoch::from_tdb_seconds(0.0);
        let ef = F064ETDB.upper(Extended::Finite(j2000_tdb));
        let recovered = F064ETDB.ceil(ef);
        match recovered {
            Extended::Finite(got) => {
                let drift = (got - j2000_tdb).abs();
                assert!(
                    drift <= 1.0 * hifitime::Unit::Nanosecond,
                    "TDB round-trip at J2000 diverged: Δ {:?}",
                    drift,
                );
            }
            other => panic!("expected Finite, got {:?}", other),
        }
    }

    // ── ETAI: solve_to_ceil termination + walk-equivalence ───────
    //
    // ETAI is the representative epoch scale: pure constant-offset
    // arithmetic relative to TAI, no leap-second table or
    // sin/Newton-Raphson iteration. The other 8 scales share the
    // same `shift_epoch_tai` / `epoch_to_ns` / `epoch_from_ns`
    // plumbing so any solver bug would surface here too.

    #[test]
    fn f064_etai_solve_terminates_at_walk_pathological_magnitude() {
        // 1e13 TAI seconds is well past the 2⁵³-ns regime where the
        // f64 plateau widens past 1 ULP — pre-solver this would walk
        // ~10⁶ ns. With the solver it returns within ≤ 44 iterations.
        let v = ExtendedFloat::Extend(1.0e13_f64);
        let _ = F064ETAI.ceil(v);
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(64))]

        #[test]
        fn f64_etai_solve_matches_walk_in_safe_range(v in -1.0e6_f64..1.0e6_f64) {
            let est = Epoch::from_tai_seconds(v);
            let est_widen = est.to_tai_seconds();
            let (walk_z, _) = if est_widen >= v {
                f64_etai_walks::descend_to_ceil(est, v)
            } else {
                f64_etai_walks::ascend_to_ceil(est, v)
            };
            let (solve_z, steps) = f64_etai_walks::solve_to_ceil(est, v);
            prop_assert_eq!(solve_z, walk_z);
            prop_assert!(steps <= 52, "solve_to_ceil took {steps} steps");
        }
    }
}
