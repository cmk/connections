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
//!   connections that feed into a bounded integer rung (Micro,
//!   Pico, …); unbounded `any::<f64>()` shrinks bit-by-bit through
//!   the mantissa on saturation failures, exploring the
//!   `i64::MAX × PREC` corner of the input space for minutes while
//!   teaching nothing about the adjoint law. See
//!   `doc/plans/plan-2026-04-23-05.md` for the discussion.
//!
//! Tier-specific strategies live here too: `fixed_*` for the
//! decimal fixed-point ladder, `rate_*` for sample-rate rationals,
//! `pico_*` for cross-tier Pico↔Sample conns, and `extended_*` for
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
/// bounded integer rung (Micro, Nano, Pico, …). The uniform slot is
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

// ── Fixed-point ladder (Pico..Uni) strategies ────────────────────
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

use crate::conn::float::ExtendedFloat;
use crate::conn::fixed::{HasResolution, Micro, Pico};
use crate::extended::Extended;

/// `ExtendedFloat<f64>` over `Bot`, `Top`, and bounded `Finite`
/// values (8:1:1 weighting toward finite).
pub fn extended_float_f64() -> impl Strategy<Value = ExtendedFloat<f64>> {
    prop_oneof![
        1 => Just(ExtendedFloat::Bot),
        1 => Just(ExtendedFloat::Top),
        8 => arb_f64_bounded().prop_map(ExtendedFloat::Finite),
    ]
}

/// `Extended<Micro>` over `NegInf`, `PosInf`, and finite Micro
/// values bounded by `i64::MAX / Micro::PREC` (plus i64-edge
/// `Just`s).
pub fn extended_micro() -> impl Strategy<Value = Extended<Micro>> {
    let limit = i64::MAX / Micro::PREC;
    prop_oneof![
        1 => Just(Extended::NegInf),
        1 => Just(Extended::PosInf),
        1 => Just(Extended::Finite(Micro(i64::MAX))),
        1 => Just(Extended::Finite(Micro(i64::MIN))),
        8 => (-limit..=limit).prop_map(|x| Extended::Finite(Micro(x))),
    ]
}

/// `Extended<Pico>` over `NegInf`, `PosInf`, and finite Pico values
/// bounded by `i64::MAX / Pico::PREC` (plus i64-edge `Just`s).
pub fn extended_pico() -> impl Strategy<Value = Extended<Pico>> {
    let limit = i64::MAX / Pico::PREC;
    prop_oneof![
        1 => Just(Extended::NegInf),
        1 => Just(Extended::PosInf),
        1 => Just(Extended::Finite(Pico(i64::MAX))),
        1 => Just(Extended::Finite(Pico(i64::MIN))),
        8 => (-limit..=limit).prop_map(|x| Extended::Finite(Pico(x))),
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

// ── Pico↔Sample-rate strategies ──────────────────────────────────
//
// For `Conn<Pico, S_xxx>` (cross-tier between decimal SI time and
// sample-indexed time at a specific rate), Pico-side is full i64,
// Sample-side is bounded by the rate ratio.

/// Pico-side i64 strategy for Pico↔Sample Conn. Full range with
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

/// Sample-side i64 strategy for Pico↔Sample Conn with rational
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

/// Pico-side strategy for Pico↔Sample with round-trip safety:
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
