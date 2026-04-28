//! Shared proptest strategies.
//!
//! Centralizes the `arb_f32` / `arb_f64` generators that `conn/*`,
//! `lattice`, and test modules used to reinvent separately. Two
//! variants are provided:
//!
//! - [`arb_f32`] / [`arb_f64`] — 4:1 uniform-to-boundary bias over
//!   the full float domain. Boundary slot includes NaN, ±∞, ±0,
//!   MIN_POSITIVE, MAX, MIN with equal weight. Use for connections
//!   whose source and target are both float-shaped (`f64 ↔ f32`,
//!   identity on floats, preorder tests).
//! - [`arb_f64_bounded`] — 6:1 uniform-to-boundary bias restricted
//!   to `|x| ≤ 1e9` plus the same explicit boundary set. Use for
//!   connections that feed into a bounded integer rung (FD06,
//!   FD12, …); unbounded `any::<f64>()` shrinks bit-by-bit through
//!   the mantissa on saturation failures, exploring the
//!   `i64::MAX × PREC` corner of the input space for minutes while
//!   teaching nothing about the adjoint law. See
//!   `doc/plans/plan-2026-04-23-05.md` for the discussion.
//!
//! Tier-specific strategies live here too: `fixed_*` for the
//! decimal fixed-point ladder, and `extended_*` for `Extended`-
//! wrapped variants. Naming is `<tier>_<role>` to disambiguate the
//! same algebraic role across families.

use proptest::prelude::*;

/// Arbitrary `f64` with elevated-frequency boundary cases.
///
/// 4:1 weight — four arbitrary bit patterns for every one boundary
/// value. The boundary `prop_oneof!` picks uniformly among
/// `{NaN, ±∞, ±0, MIN_POSITIVE, MAX, MIN}`.
pub fn arb_f64() -> impl Strategy<Value = f64> {
    prop_oneof![
        4 => any::<f64>(),
        1 => prop_oneof![
            Just(f64::NAN),
            Just(f64::INFINITY),
            Just(f64::NEG_INFINITY),
            Just(0.0_f64),
            Just(-0.0_f64),
            Just(f64::MIN_POSITIVE),
            Just(f64::MAX),
            Just(f64::MIN),
        ],
    ]
}

/// Arbitrary `f32` with elevated-frequency boundary cases.
///
/// Same shape as [`arb_f64`]: 4:1 arbitrary-to-boundary ratio.
pub fn arb_f32() -> impl Strategy<Value = f32> {
    prop_oneof![
        4 => any::<f32>(),
        1 => prop_oneof![
            Just(f32::NAN),
            Just(f32::INFINITY),
            Just(f32::NEG_INFINITY),
            Just(0.0_f32),
            Just(-0.0_f32),
            Just(f32::MIN_POSITIVE),
            Just(f32::MAX),
            Just(f32::MIN),
        ],
    ]
}

/// Arbitrary `f64` bounded to `|x| ≤ 1e9` plus the full boundary set.
///
/// Use this instead of [`arb_f64`] for connections whose target is a
/// bounded integer rung (FD06, FD09, FD12, …). The uniform slot is
/// a finite range rather than `any::<f64>()`, which prevents the
/// mantissa-bit shrink pathology on saturation failures. 6:1 ratio
/// keeps the boundary coverage comparable to [`arb_f64`]'s 4:1
/// despite the narrower uniform distribution.
pub fn arb_f64_bounded() -> impl Strategy<Value = f64> {
    prop_oneof![
        6 => -1.0e9_f64..1.0e9_f64,
        1 => prop_oneof![
            Just(f64::NAN),
            Just(f64::INFINITY),
            Just(f64::NEG_INFINITY),
            Just(0.0_f64),
            Just(-0.0_f64),
            Just(f64::MIN_POSITIVE),
            Just(f64::MAX),
            Just(f64::MIN),
        ],
    ]
}

// `arb_f32_bounded` is intentionally omitted: no current connection
// saturates f32 into a bounded integer rung. Add it (mirroring
// `arb_f64_bounded` above) when an F32F?? or similar conn appears.

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
/// values (8:1:1 weighting toward finite).
pub fn extended_float_f64() -> impl Strategy<Value = ExtendedFloat<f64>> {
    prop_oneof![
        1 => Just(ExtendedFloat::Bot),
        1 => Just(ExtendedFloat::Top),
        8 => arb_f64_bounded().prop_map(ExtendedFloat::Extend),
    ]
}

/// Arbitrary `f32` bounded to `|x| ≤ 10` plus the full boundary set.
///
/// Mirrors [`arb_f64_bounded`] for the f32 width but with a tighter
/// uniform range. `F032DURN`'s ceil/floor walk a 1-nanosecond Duration
/// rung and stop at the f32-precision plateau boundary; at magnitudes
/// above ~10 s the f32 plateau exceeds ~10⁴ ns and proptest budgets
/// blow out. The boundary slot still pins MAX/MIN/INF/MIN_POSITIVE so
/// saturation paths are exercised even though the uniform body is
/// narrow.
pub fn arb_f32_bounded() -> impl Strategy<Value = f32> {
    prop_oneof![
        6 => -10.0_f32..10.0_f32,
        1 => prop_oneof![
            Just(f32::NAN),
            Just(f32::INFINITY),
            Just(f32::NEG_INFINITY),
            Just(0.0_f32),
            Just(-0.0_f32),
            Just(f32::MIN_POSITIVE),
            Just(f32::MAX),
            Just(f32::MIN),
        ],
    ]
}

/// `ExtendedFloat<f32>` over `Bot`, `Top`, and bounded `Finite`
/// values (8:1:1 weighting toward finite). Uses [`arb_f32_bounded`].
pub fn extended_float_f32() -> impl Strategy<Value = ExtendedFloat<f32>> {
    prop_oneof![
        1 => Just(ExtendedFloat::Bot),
        1 => Just(ExtendedFloat::Top),
        8 => arb_f32_bounded().prop_map(ExtendedFloat::Extend),
    ]
}

/// `Extended<Duration>` over `NegInf`, `PosInf`, and `Finite` values
/// from [`arb_duration`] (1:1:8 weighting). Used by `Extended<Duration>`
/// generators that don't drive a magnitude-sensitive walk.
pub fn arb_extended_duration() -> impl Strategy<Value = Extended<Duration>> {
    prop_oneof![
        1 => Just(Extended::NegInf),
        1 => Just(Extended::PosInf),
        8 => arb_duration().prop_map(Extended::Finite),
    ]
}

/// `Duration` strategy bounded to `|secs| ≤ 1e9` — for `F064DURN`
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

/// `Duration` strategy bounded to `|secs| ≤ 10` — for `F032DURN`
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
/// values from [`arb_duration_bounded_f64`] (1:1:8 weighting). Used by
/// the `F064DURN` galois battery.
pub fn arb_extended_duration_bounded_f64() -> impl Strategy<Value = Extended<Duration>> {
    prop_oneof![
        1 => Just(Extended::NegInf),
        1 => Just(Extended::PosInf),
        8 => arb_duration_bounded_f64().prop_map(Extended::Finite),
    ]
}

/// `Extended<Duration>` over `NegInf`, `PosInf`, and bounded `Finite`
/// values from [`arb_duration_bounded_f32`] (1:1:8 weighting). Used by
/// the `F032DURN` galois battery.
pub fn arb_extended_duration_bounded_f32() -> impl Strategy<Value = Extended<Duration>> {
    prop_oneof![
        1 => Just(Extended::NegInf),
        1 => Just(Extended::PosInf),
        8 => arb_duration_bounded_f32().prop_map(Extended::Finite),
    ]
}

/// `ExtendedFloat<f16>` over `Bot`, `Top`, and `Finite` from
/// [`arb_f16`] (1:1:8 weighting toward finite, matching the existing
/// extended-float strategies).
///
/// Gated on the `f16` cargo feature (nightly required).
#[cfg(feature = "f16")]
pub fn extended_float_f16() -> impl Strategy<Value = ExtendedFloat<f16>> {
    prop_oneof![
        1 => Just(ExtendedFloat::Bot),
        1 => Just(ExtendedFloat::Top),
        8 => arb_f16().prop_map(ExtendedFloat::Extend),
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
/// [`arb_date`] (1:1:8 weighting).
pub fn arb_extended_date() -> impl Strategy<Value = Extended<Date>> {
    prop_oneof![
        1 => Just(Extended::NegInf),
        1 => Just(Extended::PosInf),
        8 => arb_date().prop_map(Extended::Finite),
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
/// from [`arb_time`] (1:1:8 weighting).
pub fn arb_extended_time() -> impl Strategy<Value = Extended<Time>> {
    prop_oneof![
        1 => Just(Extended::NegInf),
        1 => Just(Extended::PosInf),
        8 => arb_time().prop_map(Extended::Finite),
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
/// values from [`arb_utc_offset`] (1:1:8 weighting).
pub fn arb_extended_utc_offset() -> impl Strategy<Value = Extended<UtcOffset>> {
    prop_oneof![
        1 => Just(Extended::NegInf),
        1 => Just(Extended::PosInf),
        8 => arb_utc_offset().prop_map(Extended::Finite),
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
/// values from [`arb_offset_dt`] (1:1:8 weighting).
pub fn arb_extended_offset_dt() -> impl Strategy<Value = Extended<OffsetDateTime>> {
    prop_oneof![
        1 => Just(Extended::NegInf),
        1 => Just(Extended::PosInf),
        8 => arb_offset_dt().prop_map(Extended::Finite),
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
/// from [`arb_weekday`] (1:1:8 weighting).
pub fn arb_extended_weekday() -> impl Strategy<Value = Extended<Weekday>> {
    prop_oneof![
        1 => Just(Extended::NegInf),
        1 => Just(Extended::PosInf),
        8 => arb_weekday().prop_map(Extended::Finite),
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
/// from [`arb_month`] (1:1:8 weighting).
pub fn arb_extended_month() -> impl Strategy<Value = Extended<Month>> {
    prop_oneof![
        1 => Just(Extended::NegInf),
        1 => Just(Extended::PosInf),
        8 => arb_month().prop_map(Extended::Finite),
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
