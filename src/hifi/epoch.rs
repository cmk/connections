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
    let max_secs = HD::MAX.to_seconds();
    let min_secs = HD::MIN.to_seconds();
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
    /// OFDTNANO shape with the standard asymmetric saturation
    /// (`ceil(NegInf) = i128::MIN`, `ceil(PosInf) = unix_max + 1`).
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
    // UTC-anchored bounds: HD::MAX/MIN translated to unix-seconds
    // space via UNIX_REF_EPOCH.
    let unix_max_secs = epoch_to_unix_f64(Epoch::from_tai_duration(HD::MAX));
    let unix_min_secs = epoch_to_unix_f64(Epoch::from_tai_duration(HD::MIN));
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

#[cfg(test)]
mod tests {
    use super::*;
    #[allow(unused_imports)]
    use crate::conn::{ConnL, ConnR};
    use crate::prop::arb::{
        arb_extended_hifi_epoch, arb_extended_hifi_epoch_bounded_f64, arb_hifi_epoch,
        arb_hifi_tai_nanos_in_range, arb_hifi_unix_nanos_in_range, extended_float_f64,
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
        // F064DURN regression-guard analog: at v == HD::MIN.to_seconds()
        // the f64 plateau is wide enough that the walk would take
        // ~10¹² steps. The `<=` boundary check fast-paths to MIN.
        let v_min = ExtendedFloat::Extend(HD::MIN.to_seconds());
        assert_eq!(
            ETAIF064.ceil(v_min),
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
}
