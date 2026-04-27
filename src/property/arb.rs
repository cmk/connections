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
//! decimal fixed-point ladder, `rate_*` for sample-rate rationals,
//! `pico_*` for cross-tier FD12↔Sample conns, and `extended_*` for
//! `Extended`-wrapped variants of those. Naming is `<tier>_<role>`
//! to disambiguate the same algebraic role across the four
//! families.

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

/// Arbitrary [`half::f16`] with edge-case-heavy boundary set.
///
/// 8:2 boundary-to-uniform weighting (boundary-heavy by design — the
/// 16-bit type's interesting failure modes are concentrated at NaN,
/// ±0, ±∞, MIN/MAX, and the subnormal boundary). The uniform slot is
/// a bounded `f32` range covering the full finite `f16` domain
/// (`±f16::MAX = ±65504`) mapped through `from_f32` (RTNE) — bounded
/// so proptest's float-range strategy does binary-search shrinking
/// rather than per-bit toggling on the 16-bit pattern.
pub fn arb_f16() -> impl Strategy<Value = half::f16> {
    prop_oneof![
        1 => Just(half::f16::NAN),
        1 => Just(half::f16::INFINITY),
        1 => Just(half::f16::NEG_INFINITY),
        1 => Just(half::f16::ZERO),
        1 => Just(half::f16::NEG_ZERO),
        1 => Just(half::f16::MIN_POSITIVE),
        1 => Just(half::f16::MIN_POSITIVE_SUBNORMAL),
        1 => Just(half::f16::MAX),
        1 => Just(half::f16::MIN),
        2 => (-65504.0_f32..=65504.0_f32).prop_map(half::f16::from_f32),
    ]
}

/// Arbitrary [`half::bf16`] with edge-case-heavy boundary set.
///
/// Same 8:2 shape as [`arb_f16`]. The uniform slot uses a smaller
/// bounded f32 range (`±1e6`) than bf16's true ±3.4e38 dynamic range
/// — the boundary slot still includes `bf16::MAX` / `bf16::MIN` so
/// extreme magnitudes are covered. Tight uniform range keeps shrink
/// time bounded.
///
/// **Note on the gap:** values in `(1e6, bf16::MAX)` (≈ `(10⁶, 3.4×10³⁸)`)
/// are not reachable from the uniform slot. The boundary slot covers
/// the extreme endpoints (`MAX`, `MIN`), so saturation paths are
/// exercised — but a Conn that mishandled values in the *middle* of
/// the high-magnitude range would not be caught by this strategy
/// alone. Acceptable because the f32→bf16 / f64→bf16 narrowing logic
/// is bit-pattern-uniform across magnitudes; structural bugs surface
/// at the boundary or in the uniform slot. If a future Conn
/// introduces magnitude-dependent behavior, widen this range.
pub fn arb_bf16() -> impl Strategy<Value = half::bf16> {
    prop_oneof![
        1 => Just(half::bf16::NAN),
        1 => Just(half::bf16::INFINITY),
        1 => Just(half::bf16::NEG_INFINITY),
        1 => Just(half::bf16::ZERO),
        1 => Just(half::bf16::NEG_ZERO),
        1 => Just(half::bf16::MIN_POSITIVE),
        1 => Just(half::bf16::MIN_POSITIVE_SUBNORMAL),
        1 => Just(half::bf16::MAX),
        1 => Just(half::bf16::MIN),
        // Bounded to ±1e6 (not bf16's full ±3.4e38 range) for shrink
        // performance. MAX/MIN endpoints are covered by the boundary
        // slot above; see fn-level rustdoc for the full rationale.
        2 => (-1.0e6_f32..=1.0e6_f32).prop_map(half::bf16::from_f32),
    ]
}

// ── Fixed-point ladder (FD12..FD00) strategies ───────────────────
//
// For each (Fine, Coarse) pair with ratio PREC, the `inner` call
// computes `coarse * PREC` which must fit i64. Strategies clamp the
// coarse-side input to `|x| < i64::MAX / PREC` to avoid overflow
// inside the connection itself. The fine-side input is bounded by
// i64 range naturally.

/// Coarse-side i64 strategy for Fine→Coarse with `inner` ratio
/// `PREC`. Clamped to `|x| ≤ i64::MAX / prec` so `c · prec` fits i64.
pub fn fixed_coarse(prec: i64) -> impl Strategy<Value = i64> {
    let limit = i64::MAX / prec;
    prop_oneof![
        1 => Just(0_i64),
        1 => Just(1_i64),
        1 => Just(-1_i64),
        1 => Just(limit),
        1 => Just(-limit),
        5 => -limit..=limit,
    ]
}

/// Fine-side i64 strategy for Fine→Coarse with `inner` ratio `PREC`.
/// Full i64 range with explicit boundary bias around `±prec` and
/// `i64::{MIN, MAX}`. Use for properties that don't round-trip
/// through `inner` (adjoint, monotone, kernel).
pub fn fixed_fine(prec: i64) -> impl Strategy<Value = i64> {
    prop_oneof![
        1 => Just(0_i64),
        1 => Just(prec),
        1 => Just(-prec),
        1 => Just(prec - 1),
        1 => Just(-(prec - 1)),
        1 => Just(prec + 1),
        1 => Just(-(prec + 1)),
        1 => Just(i64::MAX),
        1 => Just(i64::MIN + 1), // i64::MIN causes overflow under negation in some checks
        5 => any::<i64>(),
    ]
}

/// Fine-side strategy restricted to values whose `inner(ceil(_))`
/// round-trip does not overflow.
///
/// `inner(c) = c * PREC`, so the safe Fine range is
/// `|fine| ≤ (i64::MAX / PREC) * PREC` — every Fine value that
/// `ceil` can map without pushing the resulting Coarse past
/// `i64::MAX / PREC`. Use for properties that round-trip through
/// `inner` (closure, idempotent).
pub fn fixed_safe_fine(prec: i64) -> impl Strategy<Value = i64> {
    let limit = (i64::MAX / prec) * prec;
    prop_oneof![
        1 => Just(0_i64),
        1 => Just(prec),
        1 => Just(-prec),
        1 => Just(prec - 1),
        1 => Just(-(prec - 1)),
        1 => Just(prec + 1),
        1 => Just(-(prec + 1)),
        1 => Just(limit),
        1 => Just(-limit),
        5 => -limit..=limit,
    ]
}

// ── ExtendedFloat<f??> / Extended<Rung> strategies ───────────────
//
// `any::<f64>()` shrinks bit-by-bit through the mantissa and
// dominates runtime without finding structural bugs; bounded ranges
// plus explicit boundaries give wide enough adjoint-law coverage.

use crate::conn::fixed::decimal::{FD06, FD09, FD12, HasResolution};
use crate::conn::float::ExtendedFloat;
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

/// `ExtendedFloat<half::f16>` over `Bot`, `Top`, and `Finite` from
/// [`arb_f16`] (1:1:8 weighting toward finite, matching the existing
/// extended-float strategies).
pub fn extended_float_f16() -> impl Strategy<Value = ExtendedFloat<half::f16>> {
    prop_oneof![
        1 => Just(ExtendedFloat::Bot),
        1 => Just(ExtendedFloat::Top),
        8 => arb_f16().prop_map(ExtendedFloat::Extend),
    ]
}

/// `ExtendedFloat<half::bf16>` over `Bot`, `Top`, and `Finite` from
/// [`arb_bf16`] (1:1:8 weighting).
pub fn extended_float_bf16() -> impl Strategy<Value = ExtendedFloat<half::bf16>> {
    prop_oneof![
        1 => Just(ExtendedFloat::Bot),
        1 => Just(ExtendedFloat::Top),
        8 => arb_bf16().prop_map(ExtendedFloat::Extend),
    ]
}

/// `Extended<FD06>` over `NegInf`, `PosInf`, and finite FD06
/// values bounded by `i64::MAX / FD06::PREC` (plus i64-edge
/// `Just`s).
pub fn extended_fd06() -> impl Strategy<Value = Extended<FD06>> {
    let limit = i64::MAX / FD06::PREC;
    prop_oneof![
        1 => Just(Extended::NegInf),
        1 => Just(Extended::PosInf),
        1 => Just(Extended::Finite(FD06(i64::MAX))),
        1 => Just(Extended::Finite(FD06(i64::MIN))),
        8 => (-limit..=limit).prop_map(|x| Extended::Finite(FD06(x))),
    ]
}

/// `Extended<FD09>` over `NegInf`, `PosInf`, and finite FD09 (1ns)
/// values across the full `i64` backing range. FD09's `inner` does
/// not multiply through PREC (it's Duration's natural resolution),
/// so the full i64 range is safe.
pub fn extended_fd09() -> impl Strategy<Value = Extended<FD09>> {
    prop_oneof![
        1 => Just(Extended::NegInf),
        1 => Just(Extended::PosInf),
        1 => Just(Extended::Finite(FD09(0))),
        1 => Just(Extended::Finite(FD09(i64::MAX))),
        1 => Just(Extended::Finite(FD09(i64::MIN))),
        1 => Just(Extended::Finite(FD09(1_000_000_000))),  // 1 second
        1 => Just(Extended::Finite(FD09(-1_000_000_000))), // -1 second
        8 => any::<i64>().prop_map(|x| Extended::Finite(FD09(x))),
    ]
}

/// `Extended<FD12>` over `NegInf`, `PosInf`, and finite FD12 values
/// bounded by `i64::MAX / FD12::PREC` (plus i64-edge `Just`s).
pub fn extended_fd12() -> impl Strategy<Value = Extended<FD12>> {
    let limit = i64::MAX / FD12::PREC;
    prop_oneof![
        1 => Just(Extended::NegInf),
        1 => Just(Extended::PosInf),
        1 => Just(Extended::Finite(FD12(i64::MAX))),
        1 => Just(Extended::Finite(FD12(i64::MIN))),
        8 => (-limit..=limit).prop_map(|x| Extended::Finite(FD12(x))),
    ]
}

// ── Sample-rate (Sxxx) strategies ────────────────────────────────
//
// For Conn<S_a, S_b> with rational ratio `num/den`, the `inner`
// computation does `c · num / den` and casts to i64; the safe
// Coarse range is `|c| ≤ i64::MAX / num`.

/// Coarse-side i64 strategy for rate↔rate Conn with rational ratio
/// `num/den`. Clamped to `|x| ≤ i64::MAX / num`.
pub fn rate_coarse(num: i128) -> impl Strategy<Value = i64> {
    let limit = (i64::MAX as i128 / num.max(1)) as i64;
    let limit = limit.max(1);
    prop_oneof![
        1 => Just(0_i64),
        1 => Just(1_i64),
        1 => Just(-1_i64),
        1 => Just(limit),
        1 => Just(-limit),
        5 => -limit..=limit,
    ]
}

/// Fine-side i64 strategy for rate↔rate Conn with rational ratio
/// `num/den`. ceil/floor compute `x · den ± (den-1)` as i128, never
/// overflowing for `den ≤ 1e7` and `x ∈ i64`; the i64 cast of the
/// result fits because dividing by `num ≥ den` shrinks magnitude.
/// Bias to boundaries around `±(i64::MAX − den − 1)`.
///
/// **Precondition:** `num ≥ den`. The strategy's range depends only
/// on `den`, but the safety argument relies on `num ≥ den` to ensure
/// the final i64 cast doesn't overflow. Asserted at the top of the
/// function so a caller mismatch fails loudly during property-test
/// setup rather than as a silent overflow inside a generated case.
pub fn rate_fine(den: i128, num: i128) -> impl Strategy<Value = i64> {
    assert!(
        num >= den,
        "rate_fine precondition violated: num ({num}) < den ({den}); \
         the strategy's range relies on num ≥ den to keep the i64 \
         cast in range",
    );
    let near_max = i64::MAX - den as i64 - 1;
    prop_oneof![
        1 => Just(0_i64),
        1 => Just(1_i64),
        1 => Just(-1_i64),
        1 => Just(near_max),
        1 => Just(-near_max),
        5 => -near_max..=near_max,
    ]
}

/// Fine-side strategy for rate↔rate Conn with `inner(ceil(_))`
/// round-trip safety: `|x| ≤ i64::MAX − num`. Use for closure and
/// idempotent properties.
pub fn rate_safe_fine(num: i128) -> impl Strategy<Value = i64> {
    let guard: i64 = i64::try_from(num).expect("num fits i64");
    let limit = i64::MAX - guard;
    prop_oneof![
        1 => Just(0_i64),
        1 => Just(1_i64),
        1 => Just(-1_i64),
        1 => Just(limit),
        1 => Just(-limit),
        5 => -limit..=limit,
    ]
}

// ── FD12↔Sample-rate strategies ──────────────────────────────────
//
// For `Conn<FD12, S_xxx>` (cross-tier between decimal SI time and
// sample-indexed time at a specific rate), FD12-side is full i64,
// Sample-side is bounded by the rate ratio.

/// FD12-side i64 strategy for FD12↔Sample Conn. Full range with
/// boundary bias.
pub fn pico_fine() -> impl Strategy<Value = i64> {
    prop_oneof![
        1 => Just(0_i64),
        1 => Just(1_i64),
        1 => Just(-1_i64),
        1 => Just(i64::MAX),
        1 => Just(i64::MIN + 1),
        5 => any::<i64>(),
    ]
}

/// Sample-side i64 strategy for FD12↔Sample Conn with rational
/// ratio `num/den`. Clamped to `|bits · num / den| < i64::MAX`,
/// i.e. `|bits| < i64::MAX · den / num`.
///
/// `i64::MAX · den` stays in i128 trivially for the rate ratios
/// shipped today (`den ≤ 113_000`); the `saturating_mul` is a
/// belt-and-suspenders for a future `den` past `i128::MAX / i64::MAX`
/// (≈ `1.84e19`), which would silently clamp rather than overflow.
/// No call site approaches that bound.
pub fn pico_coarse(num: i128, den: i128) -> impl Strategy<Value = i64> {
    let limit = ((i64::MAX as i128).saturating_mul(den) / num.max(1)) as i64;
    let limit = limit.max(1);
    prop_oneof![
        1 => Just(0_i64),
        1 => Just(1_i64),
        1 => Just(-1_i64),
        1 => Just(limit),
        1 => Just(-limit),
        5 => -limit..=limit,
    ]
}

/// FD12-side strategy for FD12↔Sample with round-trip safety:
/// `|p| ≤ i64::MAX − num`.
pub fn pico_safe(num: i128) -> impl Strategy<Value = i64> {
    let guard: i64 = i64::try_from(num).expect("num fits i64");
    let limit = i64::MAX - guard;
    prop_oneof![
        1 => Just(0_i64),
        1 => Just(1_i64),
        1 => Just(-1_i64),
        1 => Just(limit),
        1 => Just(-limit),
        5 => -limit..=limit,
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
