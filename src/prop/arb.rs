//! Shared proptest strategies.
//!
//! Centralizes the `arb_f32` / `arb_f64` generators that `conn/*`,
//! `lattice`, and test modules used to reinvent separately.
//!
//! All float strategies use **1:2 uniform-to-boundary** bias —
//! Galois-connection bugs cluster at the co/domain extremes, so the
//! boundary slot is sampled twice as often as the uniform slot. The
//! bounded variants pin `|x|` to a smaller range to keep
//! plateau-walk costs tractable for connections feeding into a
//! Duration / decimal rung.
//!
//! Variants:
//!
//! - [`arb_f32`] / [`arb_f64`] — full float domain. Boundary slot
//!   covers NaN, ±∞, ±0, MIN_POSITIVE, MAX, MIN, EPSILON, the
//!   smallest positive subnormal, and the integer-precision boundary
//!   `2^N ± 1` (N=24 for f32, N=53 for f64). Use for connections
//!   whose source and target are both float-shaped.
//! - [`arb_f32_bounded`] / [`arb_f64_bounded`] — restricted uniform
//!   range plus a slimmer boundary set. Use for connections feeding
//!   bounded-resolution rungs (`F032TDUR`, `F064TDUR`, FD06, FD09,
//!   FD12, …). Unbounded `any::<f64>()` shrinks bit-by-bit through
//!   the mantissa on saturation failures and dominates runtime
//!   without finding structural bugs; bounded ranges plus explicit
//!   boundaries give wider adjoint-law coverage. See
//!   `doc/plans/plan-2026-04-23-05.md` for the original discussion.
//!
//! Extended-wrapped variants (`extended_float_f??`, `arb_extended_*`)
//! use **1:1:2** weighting (or 1:1:3 for floats, 1:1:1 for finite-
//! variant enums) to give NegInf/PosInf saturation arms enough
//! sampling rate to hit reliably even at low case counts.
//!
//! Tier-specific strategies live here too: `fixed_*` for the
//! decimal fixed-point ladder, and `extended_*` for `Extended`-
//! wrapped variants. Naming is `<tier>_<role>` to disambiguate the
//! same algebraic role across families.

use proptest::prelude::*;

/// Arbitrary `f64` with boundary-heavy weighting.
///
/// 1:2 uniform-to-boundary — boundary `prop_oneof!` picks uniformly
/// among 13 named extrema covering every Galois-bug-prone region of
/// the f64 domain:
///
/// - `NaN`, `±∞`, `±0`, `MIN_POSITIVE`, `MAX`, `MIN` — saturation /
///   sign / NaN-arm coverage (8 values).
/// - `EPSILON` — smallest representable change at 1.0; useful for
///   monotonicity probes.
/// - `f64::from_bits(1)` — smallest positive subnormal; tests
///   denormalised-input handling.
/// - `2^53 - 1`, `2^53`, `2^53 + 1` — the integer-precision
///   boundary; above 2^53 consecutive integers are not exactly
///   representable, and conn implementations that round-trip through
///   integer rungs must handle this region without losing identity.
pub fn arb_f64() -> impl Strategy<Value = f64> {
    prop_oneof![
        1 => any::<f64>(),
        2 => prop_oneof![
            Just(f64::NAN),
            Just(f64::INFINITY),
            Just(f64::NEG_INFINITY),
            Just(0.0_f64),
            Just(-0.0_f64),
            Just(f64::MIN_POSITIVE),
            Just(f64::MAX),
            Just(f64::MIN),
            Just(f64::EPSILON),
            Just(f64::from_bits(1)),
            Just(2.0_f64.powi(53) - 1.0),
            Just(2.0_f64.powi(53)),
            Just(2.0_f64.powi(53) + 1.0),
        ],
    ]
}

/// Arbitrary `f32` with boundary-heavy weighting.
///
/// 1:2 uniform-to-boundary — same shape as [`arb_f64`] but with
/// f32-scale precision boundaries at `2^24 ± 1`.
pub fn arb_f32() -> impl Strategy<Value = f32> {
    prop_oneof![
        1 => any::<f32>(),
        2 => prop_oneof![
            Just(f32::NAN),
            Just(f32::INFINITY),
            Just(f32::NEG_INFINITY),
            Just(0.0_f32),
            Just(-0.0_f32),
            Just(f32::MIN_POSITIVE),
            Just(f32::MAX),
            Just(f32::MIN),
            Just(f32::EPSILON),
            Just(f32::from_bits(1)),
            Just(2.0_f32.powi(24) - 1.0),
            Just(2.0_f32.powi(24)),
            Just(2.0_f32.powi(24) + 1.0),
        ],
    ]
}

/// Arbitrary `f64` bounded to `|x| ≤ 1e9` plus the full boundary set.
///
/// Use this instead of [`arb_f64`] for connections whose target is a
/// bounded integer rung (FD06, FD09, FD12, …). The uniform slot is
/// a finite range rather than `any::<f64>()`, which prevents the
/// mantissa-bit shrink pathology on saturation failures.
///
/// 1:2 uniform-to-boundary weighting ensures Galois-bug-prone extrema
/// are sampled at >5% each. The boundary slot includes `EPSILON` and
/// the smallest positive subnormal alongside the standard
/// saturation/sign/NaN values. Precision-boundary integers (`2^53 ±
/// 1`) are intentionally omitted: they lie at \|v\| ≈ 9e15, far
/// outside the bound, and would re-introduce the very wide-plateau
/// walk this strategy exists to prevent.
pub fn arb_f64_bounded() -> impl Strategy<Value = f64> {
    prop_oneof![
        1 => -1.0e9_f64..1.0e9_f64,
        2 => prop_oneof![
            Just(f64::NAN),
            Just(f64::INFINITY),
            Just(f64::NEG_INFINITY),
            Just(0.0_f64),
            Just(-0.0_f64),
            Just(f64::MIN_POSITIVE),
            Just(f64::MAX),
            Just(f64::MIN),
            Just(f64::EPSILON),
            Just(f64::from_bits(1)),
        ],
    ]
}

/// Arbitrary `f16` with edge-case-heavy boundary set.
///
/// 8:2 boundary-to-uniform weighting (boundary-heavy by design — the
/// 16-bit type's interesting failure modes are concentrated at NaN,
/// ±0, ±∞, MIN/MAX, and the subnormal boundary). The uniform slot is
/// a bounded `f32` range covering the full finite `f16` domain
/// (`±f16::MAX = ±65504`) mapped through `as f16` (RTNE) — bounded
/// so proptest's float-range strategy does binary-search shrinking
/// rather than per-bit toggling on the 16-bit pattern.
///
/// Gated on the `f16` cargo feature (nightly required).
#[cfg(feature = "f16")]
pub fn arb_f16() -> impl Strategy<Value = f16> {
    prop_oneof![
        1 => Just(f16::NAN),
        1 => Just(f16::INFINITY),
        1 => Just(f16::NEG_INFINITY),
        1 => Just(0.0_f16),
        1 => Just(-0.0_f16),
        1 => Just(f16::MIN_POSITIVE),
        // Smallest positive subnormal (bit pattern 0x0001).
        1 => Just(f16::from_bits(1)),
        1 => Just(f16::MAX),
        1 => Just(f16::MIN),
        2 => (-65504.0_f32..=65504.0_f32).prop_map(|x| x as f16),
    ]
}

// ── ExtendedFloat<f??> / Extended<Rung> strategies ───────────────
//
// `any::<f64>()` shrinks bit-by-bit through the mantissa and
// dominates runtime without finding structural bugs; bounded ranges
// plus explicit boundaries give wide enough adjoint-law coverage.

use crate::float::ExtendedFloat;

use crate::extended::Extended;

/// `ExtendedFloat<f64>` over `Bot`, `Top`, and bounded `Finite`
/// values.
///
/// 1:1:3 weighting (Bot:Top:Finite) — Bot and Top are each a single
/// concrete value and the saturation-arm bugs they probe live at
/// fixed code paths; bumping their share to 20% each (vs the prior
/// 10%) ensures both arms hit reliably even at low case counts.
pub fn extended_float_f64() -> impl Strategy<Value = ExtendedFloat<f64>> {
    prop_oneof![
        1 => Just(ExtendedFloat::Bot),
        1 => Just(ExtendedFloat::Top),
        3 => arb_f64_bounded().prop_map(ExtendedFloat::Extend),
    ]
}

/// Arbitrary `f32` bounded to `|x| ≤ 10` plus the full boundary set.
///
/// Mirrors [`arb_f64_bounded`] for the f32 width but with a tighter
/// uniform range. `F032TDUR`'s ceil/floor walk a 1-nanosecond Duration
/// rung and stop at the f32-precision plateau boundary; at magnitudes
/// above ~10 s the f32 plateau exceeds ~10⁴ ns and proptest budgets
/// blow out. The boundary slot still pins MAX/MIN/INF/MIN_POSITIVE so
/// saturation paths are exercised even though the uniform body is
/// narrow.
///
/// 1:2 uniform-to-boundary weighting ensures Galois-bug-prone extrema
/// are sampled at >5% each. The boundary slot includes `EPSILON` and
/// the smallest positive subnormal. Precision-boundary integers
/// (`2^24 ± 1`) are intentionally omitted: 2^24 ≈ 16.8M, far outside
/// the |v| ≤ 10 bound this strategy exists to enforce.
pub fn arb_f32_bounded() -> impl Strategy<Value = f32> {
    prop_oneof![
        1 => -10.0_f32..10.0_f32,
        2 => prop_oneof![
            Just(f32::NAN),
            Just(f32::INFINITY),
            Just(f32::NEG_INFINITY),
            Just(0.0_f32),
            Just(-0.0_f32),
            Just(f32::MIN_POSITIVE),
            Just(f32::MAX),
            Just(f32::MIN),
            Just(f32::EPSILON),
            Just(f32::from_bits(1)),
        ],
    ]
}

/// `ExtendedFloat<f32>` over `Bot`, `Top`, and bounded `Finite`
/// values. Mirrors [`extended_float_f64`]'s 1:1:3 weighting.
pub fn extended_float_f32() -> impl Strategy<Value = ExtendedFloat<f32>> {
    prop_oneof![
        1 => Just(ExtendedFloat::Bot),
        1 => Just(ExtendedFloat::Top),
        3 => arb_f32_bounded().prop_map(ExtendedFloat::Extend),
    ]
}

/// `Extended<Duration>` over `NegInf`, `PosInf`, and `Finite` values
/// from [`arb_duration`] — 1:1:2 weighting. Used by
/// `Extended<Duration>` generators that don't drive a
/// magnitude-sensitive walk. NegInf/PosInf each get 25% so the
/// saturation arms are sampled even at low case counts.
pub fn arb_extended_duration() -> impl Strategy<Value = Extended<Duration>> {
    prop_oneof![
        1 => Just(Extended::NegInf),
        1 => Just(Extended::PosInf),
        2 => arb_duration().prop_map(Extended::Finite),
    ]
}

/// `Duration` strategy bounded to `|secs| ≤ 1e9` — for `F064TDUR`
/// proptests.
///
/// Above ~10⁹ s the f64 plateau alone is ~120 ns wide (manageable),
/// but interaction with arbitrary rung-side `Extended<Duration>`
/// extremes (e.g. `Duration::MAX`) blows out the per-case walk budget
/// — `Duration::MAX.as_seconds_f64()` lies at magnitude ~9.2e18 where
/// the f64 plateau is ~2049 s ≈ 2e12 ns of walk per call.
///
/// Boundary slot kept rich (Duration::ZERO, ±1ns, ±1s, the bounded
/// extremes); the uniform slot is a Duration::new(s, n) with
/// `s ∈ -10⁹..=10⁹`, `n ∈ -999_999_999..=999_999_999`.
pub fn arb_duration_bounded_f64() -> impl Strategy<Value = Duration> {
    prop_oneof![
        1 => Just(Duration::ZERO),
        1 => Just(Duration::seconds(1_000_000_000)),
        1 => Just(Duration::seconds(-1_000_000_000)),
        1 => Just(Duration::seconds(-1) - Duration::nanoseconds(1)),
        1 => Just(Duration::seconds(0) + Duration::nanoseconds(1)),
        1 => Just(Duration::seconds(1) - Duration::nanoseconds(1)),
        1 => Just(Duration::nanoseconds(1)),
        1 => Just(Duration::nanoseconds(-1)),
        12 => (-1_000_000_000_i64..=1_000_000_000_i64, -999_999_999_i32..=999_999_999_i32)
            .prop_map(|(s, n)| Duration::new(s, n)),
    ]
}

/// `Duration` strategy bounded to `|secs| ≤ 10` — for `F032TDUR`
/// proptests.
///
/// f32's coarser precision means walks beyond magnitude ~10 s become
/// infeasible: at magnitude 10 s f32 ULP ≈ 10⁻⁶ s ≈ 1000 ns of walk
/// per call; at magnitude 10⁶ s it is ~10⁵ ns; at 10⁹ s it is ~10¹¹ ns
/// and the rung-side `inner(b)` then `ceil/floor` round-trip in the
/// kernel laws hangs proptest. Bound the rung-side magnitude to where
/// f32 maintains microsecond precision so walks stay under ~10⁴ steps.
pub fn arb_duration_bounded_f32() -> impl Strategy<Value = Duration> {
    prop_oneof![
        1 => Just(Duration::ZERO),
        1 => Just(Duration::seconds(10)),
        1 => Just(Duration::seconds(-10)),
        1 => Just(Duration::seconds(-1) - Duration::nanoseconds(1)),
        1 => Just(Duration::seconds(0) + Duration::nanoseconds(1)),
        1 => Just(Duration::seconds(1) - Duration::nanoseconds(1)),
        1 => Just(Duration::nanoseconds(1)),
        1 => Just(Duration::nanoseconds(-1)),
        12 => (-10_i64..=10_i64, -999_999_999_i32..=999_999_999_i32)
            .prop_map(|(s, n)| Duration::new(s, n)),
    ]
}

/// `Extended<Duration>` over `NegInf`, `PosInf`, and bounded `Finite`
/// values from [`arb_duration_bounded_f64`] — 1:1:2 weighting. Used
/// by the `F064TDUR` galois battery.
pub fn arb_extended_duration_bounded_f64() -> impl Strategy<Value = Extended<Duration>> {
    prop_oneof![
        1 => Just(Extended::NegInf),
        1 => Just(Extended::PosInf),
        2 => arb_duration_bounded_f64().prop_map(Extended::Finite),
    ]
}

/// `Extended<Duration>` over `NegInf`, `PosInf`, and bounded `Finite`
/// values from [`arb_duration_bounded_f32`] — 1:1:2 weighting. Used
/// by the `F032TDUR` galois battery.
pub fn arb_extended_duration_bounded_f32() -> impl Strategy<Value = Extended<Duration>> {
    prop_oneof![
        1 => Just(Extended::NegInf),
        1 => Just(Extended::PosInf),
        2 => arb_duration_bounded_f32().prop_map(Extended::Finite),
    ]
}

// ── std::time::Duration strategies ───────────────────────────────
//
// Mirrors the time-crate `arb_duration*` family but over the
// **unsigned** `[ZERO, MAX]` range. Used by the STDR* Conn batteries.

/// Arbitrary `std::time::Duration` over the full unsigned range with
/// bias toward `ZERO`, `MAX`, sub-second values, and exact-second
/// values. Mirrors [`arb_duration`]'s shape sans the negative arms.
pub fn arb_std_duration() -> impl Strategy<Value = std::time::Duration> {
    prop_oneof![
        // Named extremes
        1 => Just(std::time::Duration::ZERO),
        1 => Just(std::time::Duration::MAX),
        // Sub-second / exact-second edges
        1 => Just(std::time::Duration::from_nanos(1)),
        1 => Just(std::time::Duration::from_secs(1)),
        1 => Just(std::time::Duration::new(1, 999_999_999)),
        // u64-second extreme without subsec (largest exact-second value)
        1 => Just(std::time::Duration::from_secs(u64::MAX)),
        // ±1ns from MAX to catch off-by-one saturation bugs
        1 => Just(std::time::Duration::MAX - std::time::Duration::from_nanos(1)),
        // Full-range uniform sample.
        9 => (any::<u64>(), 0_u32..=999_999_999_u32)
            .prop_map(|(s, n)| std::time::Duration::new(s, n)),
    ]
}

/// `Extended<std::time::Duration>` over `NegInf`, `PosInf`, and `Finite`
/// values from [`arb_std_duration`] — 1:1:2 weighting. Used by Conn
/// batteries that don't drive a magnitude-sensitive walk.
pub fn arb_extended_std_duration() -> impl Strategy<Value = Extended<std::time::Duration>> {
    prop_oneof![
        1 => Just(Extended::NegInf),
        1 => Just(Extended::PosInf),
        2 => arb_std_duration().prop_map(Extended::Finite),
    ]
}

/// `std::time::Duration` strategy bounded to `secs ≤ 1e9` — for
/// `F064SDUR` proptests. Same plateau-walk reasoning as
/// [`arb_duration_bounded_f64`].
pub fn arb_std_duration_bounded_f64() -> impl Strategy<Value = std::time::Duration> {
    prop_oneof![
        1 => Just(std::time::Duration::ZERO),
        1 => Just(std::time::Duration::from_secs(1_000_000_000)),
        1 => Just(std::time::Duration::from_nanos(1)),
        1 => Just(std::time::Duration::from_secs(1) - std::time::Duration::from_nanos(1)),
        1 => Just(std::time::Duration::from_secs(1)),
        12 => (0_u64..=1_000_000_000_u64, 0_u32..=999_999_999_u32)
            .prop_map(|(s, n)| std::time::Duration::new(s, n)),
    ]
}

/// `std::time::Duration` strategy bounded to `secs ≤ 10` — for
/// `F032SDUR` proptests. Same plateau-walk reasoning as
/// [`arb_duration_bounded_f32`].
pub fn arb_std_duration_bounded_f32() -> impl Strategy<Value = std::time::Duration> {
    prop_oneof![
        1 => Just(std::time::Duration::ZERO),
        1 => Just(std::time::Duration::from_secs(10)),
        1 => Just(std::time::Duration::from_nanos(1)),
        1 => Just(std::time::Duration::from_secs(1) - std::time::Duration::from_nanos(1)),
        1 => Just(std::time::Duration::from_secs(1)),
        12 => (0_u64..=10_u64, 0_u32..=999_999_999_u32)
            .prop_map(|(s, n)| std::time::Duration::new(s, n)),
    ]
}

/// `Extended<std::time::Duration>` over `NegInf`, `PosInf`, and bounded
/// `Finite` values from [`arb_std_duration_bounded_f64`] — 1:1:2 weighting.
/// Used by the `F064SDUR` galois battery.
pub fn arb_extended_std_duration_bounded_f64()
-> impl Strategy<Value = Extended<std::time::Duration>> {
    prop_oneof![
        1 => Just(Extended::NegInf),
        1 => Just(Extended::PosInf),
        2 => arb_std_duration_bounded_f64().prop_map(Extended::Finite),
    ]
}

/// `Extended<std::time::Duration>` over `NegInf`, `PosInf`, and bounded
/// `Finite` values from [`arb_std_duration_bounded_f32`] — 1:1:2 weighting.
/// Used by the `F032SDUR` galois battery.
pub fn arb_extended_std_duration_bounded_f32()
-> impl Strategy<Value = Extended<std::time::Duration>> {
    prop_oneof![
        1 => Just(Extended::NegInf),
        1 => Just(Extended::PosInf),
        2 => arb_std_duration_bounded_f32().prop_map(Extended::Finite),
    ]
}

/// `Extended<u64>` over `NegInf`, `PosInf`, and `Finite` values —
/// 1:1:8 weighting with explicit bias toward `Finite::{0, MAX}`.
///
/// Currently used only by the `SDURU064` Galois battery; exported for
/// downstream crates that need the same generic shape (matches
/// [`arb_extended_i64`]).
pub fn arb_extended_u64() -> impl Strategy<Value = Extended<u64>> {
    prop_oneof![
        1 => Just(Extended::NegInf),
        1 => Just(Extended::PosInf),
        1 => Just(Extended::Finite(0_u64)),
        1 => Just(Extended::Finite(u64::MAX)),
        8 => any::<u64>().prop_map(Extended::Finite),
    ]
}

/// `Extended<u128>` over `NegInf`, `PosInf`, and `Finite` values —
/// 1:1:8 weighting with explicit bias toward `Finite::{0, MAX,
/// std::time::Duration::MAX.as_nanos()}`. The third boundary is the
/// largest rung value `SDURU128.upper` round-trips bijectively.
///
/// Not currently driven by any Conn battery in this crate (the
/// `SDURU128` battery uses [`arb_extended_sdur_nanos_in_range`] to stay
/// within the bijective image); exported for downstream crates that
/// want the full unbounded generator.
pub fn arb_extended_u128() -> impl Strategy<Value = Extended<u128>> {
    let max_dur_nanos = std::time::Duration::MAX.as_nanos();
    prop_oneof![
        1 => Just(Extended::NegInf),
        1 => Just(Extended::PosInf),
        1 => Just(Extended::Finite(0_u128)),
        1 => Just(Extended::Finite(u128::MAX)),
        1 => Just(Extended::Finite(max_dur_nanos)),
        8 => any::<u128>().prop_map(Extended::Finite),
    ]
}

/// `Extended<u128>` bounded to `Finite(b)` with `b ≤
/// StdDuration::MAX.as_nanos()`. Used by the `SDURU128` Galois battery
/// — outside this range the rung exceeds StdDuration's bijective image
/// and `inner` saturates, so the law check is restricted to the
/// representable region (mirrors `arb_unix_nanos_in_range` for
/// `ODTMNANO`). NegInf/PosInf are still sampled.
pub fn arb_extended_sdur_nanos_in_range() -> impl Strategy<Value = Extended<u128>> {
    let max_dur_nanos = std::time::Duration::MAX.as_nanos();
    prop_oneof![
        1 => Just(Extended::NegInf),
        1 => Just(Extended::PosInf),
        1 => Just(Extended::Finite(0_u128)),
        1 => Just(Extended::Finite(max_dur_nanos)),
        1 => Just(Extended::Finite(1_500_000_000_u128)),
        8 => (0_u128..=max_dur_nanos).prop_map(Extended::Finite),
    ]
}

/// `ExtendedFloat<f16>` over `Bot`, `Top`, and `Finite` from
/// [`arb_f16`] — 1:1:3 weighting matching the f64/f32 extended-float
/// strategies.
///
/// Gated on the `f16` cargo feature (nightly required).
#[cfg(feature = "f16")]
pub fn extended_float_f16() -> impl Strategy<Value = ExtendedFloat<f16>> {
    prop_oneof![
        1 => Just(ExtendedFloat::Bot),
        1 => Just(ExtendedFloat::Top),
        3 => arb_f16().prop_map(ExtendedFloat::Extend),
    ]
}

// ── time-crate strategies ────────────────────────────────────────
//
// `arb_date` covers the full default-features Date range
// (year ±9999) by sampling julian-day integers in
// `[Date::MIN.to_julian_day(), Date::MAX.to_julian_day()]`. The
// other strategies bias toward boundary values (MIN/MAX/ZERO/MIDNIGHT)
// because the Galois rounding edge cases live there.

use time::{Date, Duration, Month, OffsetDateTime, PrimitiveDateTime, Time, UtcOffset, Weekday};

/// Arbitrary `time::Date` over the full default Date range
/// (year ±9999) with explicit bias toward `Date::{MIN, MAX, EPOCH}`,
/// the Unix epoch start (`1970-01-01`), the Y2038 cutover
/// (`2038-01-19`), and the year-10K boundary (`9999-12-31`).
pub fn arb_date() -> impl Strategy<Value = Date> {
    let min_jd = Date::MIN.to_julian_day();
    let max_jd = Date::MAX.to_julian_day();
    prop_oneof![
        1 => Just(Date::MIN),
        1 => Just(Date::MAX),
        1 => Just(Date::from_julian_day(0).expect("jd 0 is in range")),
        1 => Just(Date::from_calendar_date(1970, Month::January, 1).expect("epoch")),
        1 => Just(Date::from_calendar_date(2038, Month::January, 19).expect("Y2038")),
        1 => Just(Date::from_calendar_date(9999, Month::December, 31).expect("Y10K-1")),
        10 => (min_jd..=max_jd).prop_map(|jd| Date::from_julian_day(jd).expect("jd in [MIN..=MAX]")),
    ]
}

/// Arbitrary `time::Time` over the full nanosecond range
/// `[0, 86_400 × 10⁹)` with bias toward `MIDNIGHT`, end-of-day,
/// and noon (the canonical doc-example anchor).
pub fn arb_time() -> impl Strategy<Value = Time> {
    const NS_PER_DAY: i64 = 86_400 * 1_000_000_000;
    prop_oneof![
        1 => Just(Time::MIDNIGHT),
        1 => Just(Time::MIDNIGHT + Duration::nanoseconds(NS_PER_DAY - 1)),
        1 => Just(Time::MIDNIGHT + Duration::seconds(1)),
        1 => Just(Time::MIDNIGHT + Duration::nanoseconds(1)),
        1 => Just(Time::from_hms(12, 0, 0).expect("noon")),
        8 => (0..NS_PER_DAY).prop_map(|ns| Time::MIDNIGHT + Duration::nanoseconds(ns)),
    ]
}

/// Arbitrary `time::Duration` over the **full i64-second range**.
/// Earlier versions of this strategy clipped the uniform slot to
/// `±10⁹ s` (≈ ±31.7 years) — only 0.01% of the reachable
/// nanosecond domain — leaving the saturation arms at
/// `Duration::MIN/MAX` exercised only by explicit boundary `Just`s.
/// The widened range exposes float-Duration bridges and DURNFD09's
/// out-of-range path to proportional proptest coverage.
pub fn arb_duration() -> impl Strategy<Value = Duration> {
    prop_oneof![
        // Named extremes
        1 => Just(Duration::ZERO),
        1 => Just(Duration::MIN),
        1 => Just(Duration::MAX),
        // Signed-rounding edges around ±1s
        1 => Just(Duration::seconds(-1) - Duration::nanoseconds(1)),
        1 => Just(Duration::seconds(0) + Duration::nanoseconds(1)),
        1 => Just(Duration::seconds(1) - Duration::nanoseconds(1)),
        // i64-second extremes (no subsec — exact second multiples)
        1 => Just(Duration::seconds(i64::MAX)),
        1 => Just(Duration::seconds(i64::MIN)),
        // ±1ns and ±(MAX-1ns) to catch off-by-one saturation bugs
        1 => Just(Duration::nanoseconds(1)),
        1 => Just(Duration::nanoseconds(-1)),
        1 => Just(Duration::MAX - Duration::nanoseconds(1)),
        1 => Just(Duration::MIN + Duration::nanoseconds(1)),
        // Full-range uniform sample. `Duration::new` normalises any
        // sign mismatch between (s, n).
        12 => (any::<i64>(), -999_999_999_i32..=999_999_999_i32)
            .prop_map(|(s, n)| Duration::new(s, n)),
    ]
}

/// Arbitrary `time::PrimitiveDateTime` from the cartesian product of
/// [`arb_date`] and [`arb_time`].
pub fn arb_primitive_dt() -> impl Strategy<Value = PrimitiveDateTime> {
    (arb_date(), arb_time()).prop_map(|(d, t)| PrimitiveDateTime::new(d, t))
}

/// `Extended<Date>` over `NegInf`, `PosInf`, and `Finite` values from
/// [`arb_date`] — 1:1:2 weighting.
pub fn arb_extended_date() -> impl Strategy<Value = Extended<Date>> {
    prop_oneof![
        1 => Just(Extended::NegInf),
        1 => Just(Extended::PosInf),
        2 => arb_date().prop_map(Extended::Finite),
    ]
}

/// `i32` strategy bounded to `[Date::MIN.to_julian_day(),
/// Date::MAX.to_julian_day()]` — the round-trippable range for the
/// `Date ↔ julian day` connection.
pub fn arb_jd_in_range() -> impl Strategy<Value = i32> {
    let min_jd = Date::MIN.to_julian_day();
    let max_jd = Date::MAX.to_julian_day();
    prop_oneof![
        1 => Just(min_jd),
        1 => Just(max_jd),
        1 => Just(0_i32),
        8 => min_jd..=max_jd,
    ]
}

/// `Extended<Time>` over `NegInf`, `PosInf`, and `Finite` values
/// from [`arb_time`] — 1:1:2 weighting.
pub fn arb_extended_time() -> impl Strategy<Value = Extended<Time>> {
    prop_oneof![
        1 => Just(Extended::NegInf),
        1 => Just(Extended::PosInf),
        2 => arb_time().prop_map(Extended::Finite),
    ]
}

/// `i64` strategy bounded to `[0, 86_400 × 10⁹)` — the
/// round-trippable nanoseconds-since-midnight range for the
/// `Time ↔ ns` connection.
pub fn arb_ns_in_range() -> impl Strategy<Value = i64> {
    const NS_MAX: i64 = 86_400 * 1_000_000_000 - 1;
    prop_oneof![
        1 => Just(0_i64),
        1 => Just(NS_MAX),
        1 => Just(1_i64),
        1 => Just(43_200_000_000_000_i64),
        8 => 0..=NS_MAX,
    ]
}

/// `i64` strategy bounded to `[0, 86_400)` — the round-trippable
/// whole-seconds-since-midnight range for the `Time ↔ secs`
/// connection.
pub fn arb_secs_in_range() -> impl Strategy<Value = i64> {
    const SECS_MAX: i64 = 86_400 - 1;
    prop_oneof![
        1 => Just(0_i64),
        1 => Just(SECS_MAX),
        1 => Just(43_200_i64),
        8 => 0..=SECS_MAX,
    ]
}

/// `Extended<i64>` over `NegInf`, `PosInf`, and `Finite` values —
/// 1:1:8 weighting with explicit bias toward `Finite::{MIN, MAX}`.
pub fn arb_extended_i64() -> impl Strategy<Value = Extended<i64>> {
    prop_oneof![
        1 => Just(Extended::NegInf),
        1 => Just(Extended::PosInf),
        1 => Just(Extended::Finite(i64::MIN)),
        1 => Just(Extended::Finite(i64::MAX)),
        8 => any::<i64>().prop_map(Extended::Finite),
    ]
}

// ── time-crate v2: OffsetDateTime / UtcOffset / Weekday / Month ──

/// Arbitrary `time::UtcOffset` over the full `±25:59:59` range.
/// Boundary slots include UTC, the bracket extremes, common
/// real-world offsets (whole hours `+01:00`, half-hour `+05:30`
/// India, quarter-hour `+05:45` Nepal, `+12:45` Chatham), and the
/// negative side (`-08:00`, `-04:00`).
pub fn arb_utc_offset() -> impl Strategy<Value = UtcOffset> {
    prop_oneof![
        1 => Just(UtcOffset::UTC),
        1 => Just(UtcOffset::from_whole_seconds( 93599).expect("+25:59:59")),
        1 => Just(UtcOffset::from_whole_seconds(-93599).expect("-25:59:59")),
        1 => Just(UtcOffset::from_hms( 1,  0, 0).expect("+01:00")),
        1 => Just(UtcOffset::from_hms( 5, 30, 0).expect("+05:30 India")),
        1 => Just(UtcOffset::from_hms( 5, 45, 0).expect("+05:45 Nepal")),
        1 => Just(UtcOffset::from_hms( 9,  0, 0).expect("+09:00 Japan")),
        1 => Just(UtcOffset::from_hms(12, 45, 0).expect("+12:45 Chatham")),
        1 => Just(UtcOffset::from_hms(-8,  0, 0).expect("-08:00 Pacific")),
        1 => Just(UtcOffset::from_hms(-4,  0, 0).expect("-04:00 Eastern")),
        10 => (-93599_i32..=93599_i32)
            .prop_map(|s| UtcOffset::from_whole_seconds(s).expect("in range")),
    ]
}

/// `Extended<UtcOffset>` over `NegInf`, `PosInf`, and `Finite`
/// values from [`arb_utc_offset`] — 1:1:2 weighting.
pub fn arb_extended_utc_offset() -> impl Strategy<Value = Extended<UtcOffset>> {
    prop_oneof![
        1 => Just(Extended::NegInf),
        1 => Just(Extended::PosInf),
        2 => arb_utc_offset().prop_map(Extended::Finite),
    ]
}

/// Arbitrary `time::OffsetDateTime`. Cartesian product of
/// `(arb_date, arb_time, arb_utc_offset)` plus the canonical
/// landmarks: `UNIX_EPOCH`, the type-level extremes, ±1 ns from
/// epoch, and the Y2038 cutover.
pub fn arb_offset_dt() -> impl Strategy<Value = OffsetDateTime> {
    let y2038 =
        OffsetDateTime::from_unix_timestamp(2_147_483_648).expect("Y2038 in OffsetDateTime range");
    let landmarks = prop_oneof![
        1 => Just(OffsetDateTime::UNIX_EPOCH),
        1 => Just(OffsetDateTime::from_unix_timestamp_nanos(1).expect("epoch + 1ns")),
        1 => Just(OffsetDateTime::from_unix_timestamp_nanos(-1).expect("epoch - 1ns")),
        1 => Just(y2038),
    ];
    let extremes = prop_oneof![
        1 => Just(OffsetDateTime::new_in_offset(Date::MIN, Time::MIDNIGHT, UtcOffset::UTC)),
        1 => Just(OffsetDateTime::new_in_offset(
            Date::MAX,
            Time::from_hms_nano(23, 59, 59, 999_999_999).expect("end-of-day"),
            UtcOffset::UTC,
        )),
    ];
    let body = (arb_date(), arb_time(), arb_utc_offset())
        .prop_map(|(d, t, o)| OffsetDateTime::new_in_offset(d, t, o));
    prop_oneof![
        2 => landmarks,
        1 => extremes,
        9 => body,
    ]
}

/// `Extended<OffsetDateTime>` over `NegInf`, `PosInf`, and `Finite`
/// values from [`arb_offset_dt`] — 1:1:2 weighting.
pub fn arb_extended_offset_dt() -> impl Strategy<Value = Extended<OffsetDateTime>> {
    prop_oneof![
        1 => Just(Extended::NegInf),
        1 => Just(Extended::PosInf),
        2 => arb_offset_dt().prop_map(Extended::Finite),
    ]
}

/// Arbitrary `time::Weekday` — uniform over the seven variants.
pub fn arb_weekday() -> impl Strategy<Value = Weekday> {
    prop_oneof![
        Just(Weekday::Monday),
        Just(Weekday::Tuesday),
        Just(Weekday::Wednesday),
        Just(Weekday::Thursday),
        Just(Weekday::Friday),
        Just(Weekday::Saturday),
        Just(Weekday::Sunday),
    ]
}

/// `Extended<Weekday>` over `NegInf`, `PosInf`, and `Finite` values
/// from [`arb_weekday`] — 1:1:1 weighting.
///
/// Equal-leg ratio (vs the 1:1:2 used elsewhere) because `Weekday`
/// has only 7 finite variants; with 1:1:2 each variant samples at
/// 2/9 ÷ 7 ≈ 3.2%. At 1:1:1 each variant samples at 1/3 ÷ 7 ≈ 4.8%
/// while NegInf and PosInf each get 33% — keeps every variant within
/// striking distance of >5% even at low case counts.
pub fn arb_extended_weekday() -> impl Strategy<Value = Extended<Weekday>> {
    prop_oneof![
        1 => Just(Extended::NegInf),
        1 => Just(Extended::PosInf),
        1 => arb_weekday().prop_map(Extended::Finite),
    ]
}

/// Arbitrary `time::Month` — uniform over the twelve variants.
pub fn arb_month() -> impl Strategy<Value = Month> {
    prop_oneof![
        Just(Month::January),
        Just(Month::February),
        Just(Month::March),
        Just(Month::April),
        Just(Month::May),
        Just(Month::June),
        Just(Month::July),
        Just(Month::August),
        Just(Month::September),
        Just(Month::October),
        Just(Month::November),
        Just(Month::December),
    ]
}

/// `Extended<Month>` over `NegInf`, `PosInf`, and `Finite` values
/// from [`arb_month`] — 1:1:1 weighting (matches
/// [`arb_extended_weekday`]'s reasoning for equal-leg ratio on
/// finite-variant enums).
pub fn arb_extended_month() -> impl Strategy<Value = Extended<Month>> {
    prop_oneof![
        1 => Just(Extended::NegInf),
        1 => Just(Extended::PosInf),
        1 => arb_month().prop_map(Extended::Finite),
    ]
}

/// `i128` strategy bounded to `[OffsetDateTime::MIN.unix_timestamp_nanos(),
/// OffsetDateTime::MAX.unix_timestamp_nanos()]` — the round-trippable
/// unix-nanosecond range for the `OffsetDateTime ↔ i128` connection.
pub fn arb_unix_nanos_in_range() -> impl Strategy<Value = i128> {
    let min_ns = OffsetDateTime::new_in_offset(Date::MIN, Time::MIDNIGHT, UtcOffset::UTC)
        .unix_timestamp_nanos();
    let max_ns = OffsetDateTime::new_in_offset(
        Date::MAX,
        Time::from_hms_nano(23, 59, 59, 999_999_999).expect("end-of-day"),
        UtcOffset::UTC,
    )
    .unix_timestamp_nanos();
    prop_oneof![
        1 => Just(min_ns),
        1 => Just(max_ns),
        1 => Just(0_i128),
        1 => Just( 1_000_000_000_i128),
        1 => Just(-1_000_000_000_i128),
        1 => Just( 2_147_483_648_000_000_000_i128), // Y2038 in nanos
        10 => min_ns..=max_ns,
    ]
}

/// `i64` strategy bounded to OffsetDateTime's whole-second range.
pub fn arb_unix_secs_in_range() -> impl Strategy<Value = i64> {
    let min_s =
        OffsetDateTime::new_in_offset(Date::MIN, Time::MIDNIGHT, UtcOffset::UTC).unix_timestamp();
    let max_s = OffsetDateTime::new_in_offset(
        Date::MAX,
        Time::from_hms_nano(23, 59, 59, 999_999_999).expect("end-of-day"),
        UtcOffset::UTC,
    )
    .unix_timestamp();
    prop_oneof![
        1 => Just(min_s),
        1 => Just(max_s),
        1 => Just(0_i64),
        1 => Just(1_i64),
        1 => Just(-1_i64),
        1 => Just(2_147_483_648_i64), // Y2038
        10 => min_s..=max_s,
    ]
}

/// `i32` strategy bounded to UtcOffset's `whole_seconds` range
/// (`±93599`).
pub fn arb_offset_secs_in_range() -> impl Strategy<Value = i32> {
    prop_oneof![
        1 => Just(-93599_i32),
        1 => Just( 93599_i32),
        1 => Just(0_i32),
        1 => Just( 19800_i32), // +05:30 India
        1 => Just( 20700_i32), // +05:45 Nepal
        1 => Just(-28800_i32), // -08:00 Pacific
        10 => -93599_i32..=93599_i32,
    ]
}

/// `u8` strategy bounded to `1..=7` — round-trippable ISO weekday
/// numbering for `WDAYU008`.
pub fn arb_iso_weekday_byte() -> impl Strategy<Value = u8> {
    1_u8..=7
}

/// `u8` strategy bounded to `1..=12` — round-trippable month
/// numbering for `MNTHU008`.
pub fn arb_month_byte() -> impl Strategy<Value = u8> {
    1_u8..=12
}

// ── char / net / ordering strategies (Plan 24 families) ────────

/// Arbitrary valid `char` with bias toward the surrogate-gap
/// boundary (`'\u{D7FF}'`, `'\u{E000}'`) and the Unicode max
/// (`'\u{10FFFF}'`). Uniform slot uses [`proptest::char::any`].
pub fn arb_char() -> impl Strategy<Value = char> {
    prop_oneof![
        1 => Just('\u{0}'),
        1 => Just('\u{D7FF}'),
        1 => Just('\u{E000}'),
        1 => Just('\u{10FFFF}'),
        1 => Just('A'),
        1 => Just('\n'),
        10 => proptest::char::any(),
    ]
}

/// `Extended<char>` over `NegInf`, `PosInf`, and `Finite` values from
/// [`arb_char`] — 1:1:2 weighting.
pub fn arb_extended_char() -> impl Strategy<Value = Extended<char>> {
    prop_oneof![
        1 => Just(Extended::NegInf),
        1 => Just(Extended::PosInf),
        2 => arb_char().prop_map(Extended::Finite),
    ]
}

/// `Extended<u32>` over `NegInf`, `PosInf`, and `Finite` values —
/// 1:1:8 weighting with explicit bias toward the char-relevant
/// boundaries (`0xD7FF`, `0xD800`, `0xDFFF`, `0xE000`, `0x10FFFF`,
/// `0x110000`) plus `{0, MAX}`.
pub fn arb_extended_u32() -> impl Strategy<Value = Extended<u32>> {
    prop_oneof![
        1 => Just(Extended::NegInf),
        1 => Just(Extended::PosInf),
        1 => Just(Extended::Finite(0_u32)),
        1 => Just(Extended::Finite(u32::MAX)),
        1 => Just(Extended::Finite(0xD7FF)),
        1 => Just(Extended::Finite(0xD800)),
        1 => Just(Extended::Finite(0xDFFF)),
        1 => Just(Extended::Finite(0xE000)),
        1 => Just(Extended::Finite(0x10FFFF)),
        1 => Just(Extended::Finite(0x110000)),
        8 => any::<u32>().prop_map(Extended::Finite),
    ]
}

/// Arbitrary `Ipv4Addr` — uniform over the full 32-bit range with
/// explicit bias toward landmarks (UNSPECIFIED, BROADCAST, LOCALHOST).
pub fn arb_ipv4() -> impl Strategy<Value = std::net::Ipv4Addr> {
    prop_oneof![
        1 => Just(std::net::Ipv4Addr::UNSPECIFIED),
        1 => Just(std::net::Ipv4Addr::BROADCAST),
        1 => Just(std::net::Ipv4Addr::new(127, 0, 0, 1)),
        1 => Just(std::net::Ipv4Addr::new(192, 168, 1, 1)),
        8 => any::<u32>().prop_map(std::net::Ipv4Addr::from_bits),
    ]
}

/// `Extended<Ipv4Addr>` — 1:1:2 weighting for the synthetic ends and
/// the `Finite` slot from [`arb_ipv4`].
pub fn arb_extended_ipv4() -> impl Strategy<Value = Extended<std::net::Ipv4Addr>> {
    prop_oneof![
        1 => Just(Extended::NegInf),
        1 => Just(Extended::PosInf),
        2 => arb_ipv4().prop_map(Extended::Finite),
    ]
}

/// Arbitrary `Ipv6Addr` — uniform over the full 128-bit range with
/// explicit bias toward landmarks (UNSPECIFIED, LOCALHOST, the
/// v4-mapped block extremes plus the points just outside it).
pub fn arb_ipv6() -> impl Strategy<Value = std::net::Ipv6Addr> {
    let v4mapped_lo: u128 = 0x0000_0000_0000_0000_0000_FFFF_0000_0000;
    let v4mapped_hi: u128 = 0x0000_0000_0000_0000_0000_FFFF_FFFF_FFFF;
    prop_oneof![
        1 => Just(std::net::Ipv6Addr::UNSPECIFIED),
        1 => Just(std::net::Ipv6Addr::LOCALHOST),
        // `v4mapped_lo - 1` is the largest v6 below the v4-mapped block —
        // the first point where `IPV6IPV4`'s ceil and floor diverge in
        // opposite directions, so the proptest battery needs reliable
        // coverage of it.
        1 => Just(std::net::Ipv6Addr::from_bits(v4mapped_lo - 1)),
        1 => Just(std::net::Ipv6Addr::from_bits(v4mapped_lo)),
        1 => Just(std::net::Ipv6Addr::from_bits(v4mapped_hi)),
        1 => Just(std::net::Ipv6Addr::from_bits(v4mapped_hi + 1)),
        1 => Just(std::net::Ipv6Addr::from_bits(u128::MAX)),
        8 => any::<u128>().prop_map(std::net::Ipv6Addr::from_bits),
    ]
}

/// `Extended<Ipv6Addr>` — 1:1:2 weighting for the synthetic ends and
/// the `Finite` slot from [`arb_ipv6`].
pub fn arb_extended_ipv6() -> impl Strategy<Value = Extended<std::net::Ipv6Addr>> {
    prop_oneof![
        1 => Just(Extended::NegInf),
        1 => Just(Extended::PosInf),
        2 => arb_ipv6().prop_map(Extended::Finite),
    ]
}

/// Arbitrary `IpAddr` — sums [`arb_ipv4`] and [`arb_ipv6`] with the
/// V4/V6 ratio weighted toward V6 (more boundary cases live there).
pub fn arb_ip_addr() -> impl Strategy<Value = std::net::IpAddr> {
    prop_oneof![
        1 => arb_ipv4().prop_map(std::net::IpAddr::V4),
        2 => arb_ipv6().prop_map(std::net::IpAddr::V6),
    ]
}

/// Arbitrary `SocketAddrV4` — cartesian product of [`arb_ipv4`] and
/// the full `u16` port range, with bias toward landmark ports
/// (`0`, `65535`, `80`, `443`).
pub fn arb_socket_addr_v4() -> impl Strategy<Value = std::net::SocketAddrV4> {
    let port = prop_oneof![
        1 => Just(0_u16),
        1 => Just(u16::MAX),
        1 => Just(80_u16),
        1 => Just(443_u16),
        6 => any::<u16>(),
    ];
    (arb_ipv4(), port).prop_map(|(ip, p)| std::net::SocketAddrV4::new(ip, p))
}

/// `Extended<SocketAddrV4>` — 1:1:2 weighting for synthetic ends and
/// `Finite` slot from [`arb_socket_addr_v4`].
pub fn arb_extended_socket_addr_v4() -> impl Strategy<Value = Extended<std::net::SocketAddrV4>> {
    prop_oneof![
        1 => Just(Extended::NegInf),
        1 => Just(Extended::PosInf),
        2 => arb_socket_addr_v4().prop_map(Extended::Finite),
    ]
}

/// Arbitrary `SocketAddrV6` — cartesian product of [`arb_ipv6`],
/// `u16` port, `u32` flowinfo, and `u32` scope_id with all-zero
/// flowinfo/scope_id biased.
pub fn arb_socket_addr_v6() -> impl Strategy<Value = std::net::SocketAddrV6> {
    let port = prop_oneof![
        1 => Just(0_u16),
        1 => Just(u16::MAX),
        1 => Just(80_u16),
        6 => any::<u16>(),
    ];
    let flowinfo = prop_oneof![
        2 => Just(0_u32),
        1 => Just(u32::MAX),
        4 => any::<u32>(),
    ];
    let scope_id = prop_oneof![
        2 => Just(0_u32),
        1 => Just(u32::MAX),
        4 => any::<u32>(),
    ];
    (arb_ipv6(), port, flowinfo, scope_id)
        .prop_map(|(ip, p, fi, si)| std::net::SocketAddrV6::new(ip, p, fi, si))
}

/// `Extended<SocketAddrV6>` — 1:1:2 weighting for synthetic ends and
/// `Finite` slot from [`arb_socket_addr_v6`].
pub fn arb_extended_socket_addr_v6() -> impl Strategy<Value = Extended<std::net::SocketAddrV6>> {
    prop_oneof![
        1 => Just(Extended::NegInf),
        1 => Just(Extended::PosInf),
        2 => arb_socket_addr_v6().prop_map(Extended::Finite),
    ]
}

/// Arbitrary `SocketAddr` — sums [`arb_socket_addr_v4`] and
/// [`arb_socket_addr_v6`] with the V4/V6 ratio weighted toward V6.
pub fn arb_socket_addr() -> impl Strategy<Value = std::net::SocketAddr> {
    prop_oneof![
        1 => arb_socket_addr_v4().prop_map(std::net::SocketAddr::V4),
        2 => arb_socket_addr_v6().prop_map(std::net::SocketAddr::V6),
    ]
}

/// Arbitrary `core::cmp::Ordering` — uniform over the three variants.
pub fn arb_ordering() -> impl Strategy<Value = core::cmp::Ordering> {
    prop_oneof![
        Just(core::cmp::Ordering::Less),
        Just(core::cmp::Ordering::Equal),
        Just(core::cmp::Ordering::Greater),
    ]
}

// ── hifitime::Duration strategies ───────────────────────────────
//
// Gated on `feature = "hifi"`. Mirror the `arb_duration*` family but
// over hifitime's `Duration` (i16 centuries × NANOSECONDS_PER_CENTURY +
// u64 sub-century nanoseconds, total range ≈ ±1.03 × 10²³ ns).
//
// All entries go through `Duration::from_total_nanoseconds`, which
// always normalizes (`nanoseconds < NANOSECONDS_PER_CENTURY` post-
// canonicalization). hifitime's `PartialOrd` is field-wise and only
// agrees with semantic order on canonical Durations; never use
// `from_parts` here.

#[cfg(feature = "hifi")]
mod hifi_dur {
    use super::*;
    use crate::extended::Extended;
    use hifitime::Duration as HD;

    /// Arbitrary `hifitime::Duration` over the full canonical range.
    pub fn arb_hifi_duration() -> impl Strategy<Value = HD> {
        prop_oneof![
            // Named extremes
            1 => Just(HD::ZERO),
            1 => Just(HD::MIN),
            1 => Just(HD::MAX),
            1 => Just(HD::EPSILON),
            1 => Just(HD::MIN_NEGATIVE),
            // Signed-rounding edges around ±1 s
            1 => Just(HD::from_total_nanoseconds(1_000_000_000 - 1)),
            1 => Just(HD::from_total_nanoseconds(1_000_000_000 + 1)),
            1 => Just(HD::from_total_nanoseconds(-(1_000_000_000 - 1))),
            1 => Just(HD::from_total_nanoseconds(-(1_000_000_000 + 1))),
            // ±1 s exact
            1 => Just(HD::from_seconds(1.0)),
            1 => Just(HD::from_seconds(-1.0)),
            // ±(MAX-1ns), ±(MIN+1ns)
            1 => Just(HD::from_total_nanoseconds(HD::MAX.total_nanoseconds() - 1)),
            1 => Just(HD::from_total_nanoseconds(HD::MIN.total_nanoseconds() + 1)),
            // Two slots split per the saturation analysis (MR !63
            // round-2 review): `Duration::from_total_nanoseconds`
            // (hifitime 4.3, `src/duration/mod.rs:172`) saturates to
            // `Duration::MIN` / `Duration::MAX` when the implied
            // `centuries` value falls outside `i16`. The HD range is
            // `~1.6 × 10¹⁵×` smaller than `i128`, so a single
            // `any::<i128>()` slot collapses essentially all draws to
            // the saturation arms (zero interior coverage).
            //
            // The bounded slot at weight 11 fills the interior
            // uniformly across the canonical HD range. The
            // unbounded slot at weight 1 keeps the saturation arms
            // exercised at a non-negligible rate.
            11 => (HD::MIN.total_nanoseconds()..=HD::MAX.total_nanoseconds())
                .prop_map(HD::from_total_nanoseconds),
            1 => any::<i128>().prop_map(HD::from_total_nanoseconds),
        ]
    }

    /// `Extended<HD>` — 1:1:2 weighting for synthetic ends and
    /// `Finite` slot from [`arb_hifi_duration`].
    pub fn arb_extended_hifi_duration() -> impl Strategy<Value = Extended<HD>> {
        prop_oneof![
            1 => Just(Extended::NegInf),
            1 => Just(Extended::PosInf),
            2 => arb_hifi_duration().prop_map(Extended::Finite),
        ]
    }

    /// Bounded-magnitude `HD` for the `F064HDUR` law battery.
    /// Pins |total_ns| ≤ 10⁹ × 10⁹ ns = 10¹⁸ ns ≈ 31 yr — well under
    /// the f64 mantissa-precision wall at 2⁵³ ns ≈ 104 days, *but*
    /// well over the per-Conn-call ULP-walk budget. The 31-yr bound
    /// matches `arb_duration_bounded_f64`'s rationale (see arb.rs
    /// header).
    pub fn arb_hifi_duration_bounded_f64() -> impl Strategy<Value = HD> {
        const SECS_BOUND: i128 = 1_000_000_000; // ±31.7 yr
        const NANOS_BOUND: i128 = SECS_BOUND * 1_000_000_000;
        prop_oneof![
            1 => Just(HD::ZERO),
            1 => Just(HD::EPSILON),
            1 => Just(HD::MIN_NEGATIVE),
            1 => Just(HD::from_seconds(1.0)),
            1 => Just(HD::from_seconds(-1.0)),
            8 => (-NANOS_BOUND..=NANOS_BOUND).prop_map(HD::from_total_nanoseconds),
        ]
    }

    /// Bounded-magnitude `HD` for the `F032HDUR` law battery.
    /// Pins |total_ns| ≤ 10 × 10⁹ ns = 10 s — same shape as
    /// `arb_duration_bounded_f32` (the f32 plateau is much wider;
    /// keeping the bound tight keeps walk budgets sane).
    pub fn arb_hifi_duration_bounded_f32() -> impl Strategy<Value = HD> {
        const NANOS_BOUND: i128 = 10 * 1_000_000_000; // ±10 s
        prop_oneof![
            1 => Just(HD::ZERO),
            1 => Just(HD::EPSILON),
            1 => Just(HD::MIN_NEGATIVE),
            1 => Just(HD::from_seconds(1.0)),
            1 => Just(HD::from_seconds(-1.0)),
            8 => (-NANOS_BOUND..=NANOS_BOUND).prop_map(HD::from_total_nanoseconds),
        ]
    }

    /// `Extended<HD>` — bounded-f64 variant for float-bridge laws.
    pub fn arb_extended_hifi_duration_bounded_f64() -> impl Strategy<Value = Extended<HD>> {
        prop_oneof![
            1 => Just(Extended::NegInf),
            1 => Just(Extended::PosInf),
            2 => arb_hifi_duration_bounded_f64().prop_map(Extended::Finite),
        ]
    }

    /// `Extended<HD>` — bounded-f32 variant for float-bridge laws.
    pub fn arb_extended_hifi_duration_bounded_f32() -> impl Strategy<Value = Extended<HD>> {
        prop_oneof![
            1 => Just(Extended::NegInf),
            1 => Just(Extended::PosInf),
            2 => arb_hifi_duration_bounded_f32().prop_map(Extended::Finite),
        ]
    }

    /// `i128` strategy bounded to `[HD::MIN.total_ns(), HD::MAX.total_ns()]`
    /// — the round-trippable range for `HDURNANO`. Mirrors
    /// [`super::arb_unix_nanos_in_range`].
    pub fn arb_hifi_total_nanos_in_range() -> impl Strategy<Value = i128> {
        let min_n = HD::MIN.total_nanoseconds();
        let max_n = HD::MAX.total_nanoseconds();
        prop_oneof![
            1 => Just(min_n),
            1 => Just(max_n),
            1 => Just(0_i128),
            1 => Just(1_i128),
            1 => Just(-1_i128),
            8 => min_n..=max_n,
        ]
    }

    /// `i64` strategy bounded to the round-trippable range for
    /// `HDURSECS`. The bounds are derived **via integer arithmetic**
    /// (`total_nanoseconds() / 1_000_000_000`) rather than
    /// `to_seconds() as i64` — the latter f64-casts a value at
    /// `±10²³` magnitude, which is far past `f64`'s exact-integer
    /// range (`2⁵³ ≈ 9 × 10¹⁵`) and could produce an off-by-one
    /// boundary value, silently narrowing the strategy. (MR !63
    /// review.)
    pub fn arb_hifi_total_secs_in_range() -> impl Strategy<Value = i64> {
        let min_s = (HD::MIN.total_nanoseconds() / 1_000_000_000) as i64;
        let max_s = (HD::MAX.total_nanoseconds() / 1_000_000_000) as i64;
        prop_oneof![
            1 => Just(min_s),
            1 => Just(max_s),
            1 => Just(0_i64),
            1 => Just(1_i64),
            1 => Just(-1_i64),
            8 => min_s..=max_s,
        ]
    }
}

#[cfg(feature = "hifi")]
pub use hifi_dur::{
    arb_extended_hifi_duration, arb_extended_hifi_duration_bounded_f32,
    arb_extended_hifi_duration_bounded_f64, arb_hifi_duration, arb_hifi_duration_bounded_f32,
    arb_hifi_duration_bounded_f64, arb_hifi_total_nanos_in_range, arb_hifi_total_secs_in_range,
};

// ── hifitime::Epoch strategies ──────────────────────────────────
//
// Sprint-2 set: TAI-scale Epochs only. Cross-scale arbs (UTC,
// GPST, …) deferred until Sprint-3+ scale-specific Conns surface
// the need; the Conn laws don't care about the scale tag (Epoch's
// Ord/Eq are instant-based) so single-scale arbs cover every law.

#[cfg(feature = "hifi")]
mod hifi_epoch {
    use super::*;
    use crate::extended::Extended;
    use hifitime::{
        BDT_REF_EPOCH, Duration as HD, Epoch, GPST_REF_EPOCH, GST_REF_EPOCH, J1900_REF_EPOCH,
        J2000_REF_EPOCH, QZSST_REF_EPOCH, UNIX_REF_EPOCH,
    };

    /// Arbitrary `hifitime::Epoch` over the full canonical TAI range,
    /// biased toward the well-known reference epochs.
    pub fn arb_hifi_epoch() -> impl Strategy<Value = Epoch> {
        prop_oneof![
            // Named reference epochs hifitime ships
            1 => Just(J1900_REF_EPOCH),
            1 => Just(J2000_REF_EPOCH),
            1 => Just(UNIX_REF_EPOCH),
            1 => Just(GPST_REF_EPOCH),
            1 => Just(GST_REF_EPOCH),
            1 => Just(BDT_REF_EPOCH),
            1 => Just(QZSST_REF_EPOCH),
            // HD extremes wrapped as TAI Epochs
            1 => Just(Epoch::from_tai_duration(HD::MIN)),
            1 => Just(Epoch::from_tai_duration(HD::MAX)),
            1 => Just(Epoch::from_tai_duration(HD::ZERO)),
            1 => Just(Epoch::from_tai_duration(HD::EPSILON)),
            1 => Just(Epoch::from_tai_duration(HD::MIN_NEGATIVE)),
            // Full-range uniform sample via the canonical Duration arb.
            12 => super::arb_hifi_duration().prop_map(Epoch::from_tai_duration),
        ]
    }

    /// `Extended<Epoch>` — 1:1:2 weighting for synthetic ends and
    /// `Finite` slot from [`arb_hifi_epoch`].
    pub fn arb_extended_hifi_epoch() -> impl Strategy<Value = Extended<Epoch>> {
        prop_oneof![
            1 => Just(Extended::NegInf),
            1 => Just(Extended::PosInf),
            2 => arb_hifi_epoch().prop_map(Extended::Finite),
        ]
    }

    /// Bounded-magnitude `Epoch` for the f64 epoch-bridge law
    /// batteries — pins the underlying TAI Duration to the same
    /// `±10⁹ s` envelope as `arb_hifi_duration_bounded_f64`.
    pub fn arb_hifi_epoch_bounded_f64() -> impl Strategy<Value = Epoch> {
        super::arb_hifi_duration_bounded_f64().prop_map(Epoch::from_tai_duration)
    }

    /// `Extended<Epoch>` — bounded-f64 variant for float-bridge laws.
    pub fn arb_extended_hifi_epoch_bounded_f64() -> impl Strategy<Value = Extended<Epoch>> {
        prop_oneof![
            1 => Just(Extended::NegInf),
            1 => Just(Extended::PosInf),
            2 => arb_hifi_epoch_bounded_f64().prop_map(Extended::Finite),
        ]
    }

    /// `i128` strategy bounded to `[HD::MIN.total_ns(), HD::MAX.total_ns()]`
    /// — the round-trippable range for `ETAINANO`. Same range as
    /// `arb_hifi_total_nanos_in_range` (Epoch-via-TAI uses the same
    /// reference as raw HD), but kept as a separate fn for clarity
    /// at the call-site.
    pub fn arb_hifi_tai_nanos_in_range() -> impl Strategy<Value = i128> {
        super::arb_hifi_total_nanos_in_range()
    }

    /// `i128` strategy bounded to the UNIX-anchored round-trippable
    /// range for `EUNXNANO`. **Asymmetric** about the UNIX offset:
    /// lower bound is `HD::MIN.total_ns()` (not shifted, because
    /// `ceil`'s `epoch.to_utc_duration() − UNIX_REF.utc` subtraction
    /// would underflow HD if the stored UTC duration were already
    /// `HD::MIN`); upper bound is `HD::MAX.total_ns() −
    /// UNIX_REF.utc.total_ns()` (shifted, because the inner
    /// `n + UNIX_REF.utc` addition would overflow HD beyond it).
    pub fn arb_hifi_unix_nanos_in_range() -> impl Strategy<Value = i128> {
        let unix_off = UNIX_REF_EPOCH.to_utc_duration().total_nanoseconds();
        let min_n = HD::MIN.total_nanoseconds();
        let max_n = HD::MAX.total_nanoseconds() - unix_off;
        prop_oneof![
            1 => Just(min_n),
            1 => Just(min_n + 1),                            // lower-saturation boundary partner of `max_n - 1` (MR !64 round-5)
            1 => Just(max_n - 1),                            // probes the upper saturation boundary (MR !64 round-4)
            1 => Just(max_n),
            1 => Just(0_i128),
            1 => Just(1_000_000_000_i128),                   // 1 s past UNIX
            1 => Just(2_147_483_648_000_000_000_i128),       // Y2038 cutover
            1 => Just(-1_i128),
            8 => min_n..=max_n,
        ]
    }

    /// Shared body of the four `arb_hifi_{gpst,gst,bdt,qzsst}_nanos_in_range`
    /// strategies (and any future GNSS scale that adopts the same
    /// asymmetric bounds). Lower bound is `HD::MIN.total_ns()`
    /// (unshifted — `ceil`'s subtraction would underflow `HD` if the
    /// stored TAI duration were already at `HD::MIN`); upper bound is
    /// `HD::MAX.total_ns() − offset_ns` (shifted — the inner addition
    /// `n + offset_ns` would overflow `HD` beyond it). MR !66 round-2
    /// extracted this from four copy-paste bodies per Plan T1.
    fn arb_hifi_scale_nanos_in_range(offset_ns: i128) -> impl Strategy<Value = i128> {
        let min_n = HD::MIN.total_nanoseconds();
        let max_n = HD::MAX.total_nanoseconds() - offset_ns;
        prop_oneof![
            1 => Just(min_n),
            1 => Just(min_n + 1),
            1 => Just(max_n - 1),
            1 => Just(max_n),
            1 => Just(0_i128),
            1 => Just(1_i128),
            1 => Just(-1_i128),
            8 => min_n..=max_n,
        ]
    }

    /// `i128` strategy bounded to the GPST-anchored round-trippable
    /// range for `EGPSNANO`. Same asymmetric pattern as
    /// [`arb_hifi_unix_nanos_in_range`]; bodies factored through
    /// [`arb_hifi_scale_nanos_in_range`].
    pub fn arb_hifi_gpst_nanos_in_range() -> impl Strategy<Value = i128> {
        arb_hifi_scale_nanos_in_range(GPST_REF_EPOCH.to_tai_duration().total_nanoseconds())
    }

    /// `i128` strategy bounded to the GST-anchored round-trippable
    /// range for `EGSTNANO`. See [`arb_hifi_gpst_nanos_in_range`].
    pub fn arb_hifi_gst_nanos_in_range() -> impl Strategy<Value = i128> {
        arb_hifi_scale_nanos_in_range(GST_REF_EPOCH.to_tai_duration().total_nanoseconds())
    }

    /// `i128` strategy bounded to the BDT-anchored round-trippable
    /// range for `EBDTNANO`. See [`arb_hifi_gpst_nanos_in_range`].
    pub fn arb_hifi_bdt_nanos_in_range() -> impl Strategy<Value = i128> {
        arb_hifi_scale_nanos_in_range(BDT_REF_EPOCH.to_tai_duration().total_nanoseconds())
    }

    /// `i128` strategy bounded to the QZSST-anchored round-trippable
    /// range for `EQZSNANO`. QZSST shares GPST's reference epoch
    /// (`QZSST_REF_EPOCH == GPST_REF_EPOCH` in hifitime), but kept as
    /// a distinct public name so the call site documents intent.
    pub fn arb_hifi_qzsst_nanos_in_range() -> impl Strategy<Value = i128> {
        arb_hifi_scale_nanos_in_range(QZSST_REF_EPOCH.to_tai_duration().total_nanoseconds())
    }
}

#[cfg(feature = "hifi")]
pub use hifi_epoch::{
    arb_extended_hifi_epoch, arb_extended_hifi_epoch_bounded_f64, arb_hifi_bdt_nanos_in_range,
    arb_hifi_epoch, arb_hifi_epoch_bounded_f64, arb_hifi_gpst_nanos_in_range,
    arb_hifi_gst_nanos_in_range, arb_hifi_qzsst_nanos_in_range, arb_hifi_tai_nanos_in_range,
    arb_hifi_unix_nanos_in_range,
};

// ── hifitime calendar enum strategies ───────────────────────────

#[cfg(feature = "hifi")]
mod hifi_calendar {
    use super::*;
    use crate::extended::Extended;
    use hifitime::{MonthName, Weekday};

    /// Arbitrary `hifitime::MonthName` — uniform over all 12 variants.
    pub fn arb_hifi_month() -> impl Strategy<Value = MonthName> {
        prop_oneof![
            Just(MonthName::January),
            Just(MonthName::February),
            Just(MonthName::March),
            Just(MonthName::April),
            Just(MonthName::May),
            Just(MonthName::June),
            Just(MonthName::July),
            Just(MonthName::August),
            Just(MonthName::September),
            Just(MonthName::October),
            Just(MonthName::November),
            Just(MonthName::December),
        ]
    }

    /// `Extended<MonthName>` — 1:1:4 NegInf:PosInf:Finite weighting.
    pub fn arb_extended_hifi_month() -> impl Strategy<Value = Extended<MonthName>> {
        prop_oneof![
            1 => Just(Extended::NegInf),
            1 => Just(Extended::PosInf),
            4 => arb_hifi_month().prop_map(Extended::Finite),
        ]
    }

    /// Arbitrary `hifitime::Weekday` — uniform over all 7 variants
    /// (ISO 8601 ordering, 0=Mon…6=Sun).
    pub fn arb_hifi_weekday() -> impl Strategy<Value = Weekday> {
        prop_oneof![
            Just(Weekday::Monday),
            Just(Weekday::Tuesday),
            Just(Weekday::Wednesday),
            Just(Weekday::Thursday),
            Just(Weekday::Friday),
            Just(Weekday::Saturday),
            Just(Weekday::Sunday),
        ]
    }

    /// `Extended<Weekday>` — 1:1:4 NegInf:PosInf:Finite weighting.
    pub fn arb_extended_hifi_weekday() -> impl Strategy<Value = Extended<Weekday>> {
        prop_oneof![
            1 => Just(Extended::NegInf),
            1 => Just(Extended::PosInf),
            4 => arb_hifi_weekday().prop_map(Extended::Finite),
        ]
    }
}

#[cfg(feature = "hifi")]
pub use hifi_calendar::{
    arb_extended_hifi_month, arb_extended_hifi_weekday, arb_hifi_month, arb_hifi_weekday,
};
