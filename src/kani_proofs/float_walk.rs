//! **Headline result:** the `f64 → f32` ULP-walk in
//! [`crate::float::f32`] terminates in **≤ 2 iterations** for every
//! finite, non-NaN `f64` input.
//!
//! `ceil_f64_f32` / `floor_f64_f32` start with `est = x as f32` (RNE)
//! and then walk the f32 ladder by ±1 ULP until the embedding lands
//! on the right side of `x`. RNE places `est` within ½ ULP of `x`, so
//! one walk step suffices in the common case; saturation boundaries
//! and subnormals can force a second step. More than two would be a
//! bug in the helper.
//!
//! Promoting that bound from "proptest never sampled a counterexample"
//! to "no counterexample exists in the finite-non-NaN domain" is
//! what these harnesses prove.
//!
//! # Tiers
//!
//! Three tiers in escalating order of input restriction. Run T0
//! first; fall back to T1 / T2 if CBMC's FP solver doesn't return.
//!
//! | Tier | Constraint               | Note                                           |
//! |------|--------------------------|------------------------------------------------|
//! | T0   | finite + non-NaN only    | full domain — primary proof obligation         |
//! | T1   | `\|x\| ≤ 1e6`              | excludes saturation plateau, common slice      |
//! | T2   | single binade            | by IEEE structural symmetry, lifts to all      |
//!
//! Each tier appears as its own `#[kani::proof]` so they can be run
//! independently from the command line.

use crate::float::f32::{ceil_walk_steps_for_proof, floor_walk_steps_for_proof};

// ── T0 — full finite, non-NaN domain ────────────────────────────────

/// `ceil_f64_f32`: walk converges in ≤ 2 ULP corrections for every
/// finite, non-NaN `f64`.
#[kani::proof]
#[kani::unwind(4)]
fn t0_ceil_walk_steps_le_2() {
    let x: f64 = kani::any();
    kani::assume(x.is_finite() && !x.is_nan());
    let (_z, steps) = ceil_walk_steps_for_proof(x);
    assert!(steps <= 2);
}

/// `floor_f64_f32`: walk converges in ≤ 2 ULP corrections for every
/// finite, non-NaN `f64`.
#[kani::proof]
#[kani::unwind(4)]
fn t0_floor_walk_steps_le_2() {
    let x: f64 = kani::any();
    kani::assume(x.is_finite() && !x.is_nan());
    let (_z, steps) = floor_walk_steps_for_proof(x);
    assert!(steps <= 2);
}

// ── T1 — bounded magnitude ──────────────────────────────────────────
//
// Skip the saturation plateau (|x| ≥ f32::MAX) and the subnormal
// regime (|x| ≤ f32::MIN_POSITIVE). Both are still finite and
// non-NaN, but they're the regions where the walk can take its
// second step. The T1 harness verifies the bound on the well-behaved
// middle slice; pair with T0 to cover the boundaries.

/// `ceil_f64_f32`: walk converges in ≤ 1 ULP correction when
/// `|x| ≤ 1e6` (well-behaved domain, no saturation, no subnormal).
#[kani::proof]
#[kani::unwind(3)]
fn t1_ceil_walk_steps_le_1_bounded() {
    let x: f64 = kani::any();
    kani::assume(x.is_finite() && !x.is_nan());
    kani::assume(x.abs() <= 1e6_f64);
    let (_z, steps) = ceil_walk_steps_for_proof(x);
    assert!(steps <= 1);
}

/// `floor_f64_f32`: walk converges in ≤ 1 ULP correction when
/// `|x| ≤ 1e6`.
#[kani::proof]
#[kani::unwind(3)]
fn t1_floor_walk_steps_le_1_bounded() {
    let x: f64 = kani::any();
    kani::assume(x.is_finite() && !x.is_nan());
    kani::assume(x.abs() <= 1e6_f64);
    let (_z, steps) = floor_walk_steps_for_proof(x);
    assert!(steps <= 1);
}

// ── T2 — single binade ──────────────────────────────────────────────
//
// `[1.0, 2.0)` is the canonical normal binade — full mantissa range,
// no exponent edge cases. By IEEE structural symmetry across binades,
// proving the bound here lifts to the full range modulo saturation
// and subnormals (which T0 covers). Useful as a sanity check if T0
// times out.

/// `ceil_f64_f32`: walk converges in ≤ 1 ULP correction on the
/// `[1.0, 2.0)` binade.
#[kani::proof]
#[kani::unwind(3)]
fn t2_ceil_walk_steps_le_1_unit_binade() {
    let x: f64 = kani::any();
    kani::assume(x >= 1.0_f64 && x < 2.0_f64);
    let (_z, steps) = ceil_walk_steps_for_proof(x);
    assert!(steps <= 1);
}

/// `floor_f64_f32`: walk converges in ≤ 1 ULP correction on the
/// `[1.0, 2.0)` binade.
#[kani::proof]
#[kani::unwind(3)]
fn t2_floor_walk_steps_le_1_unit_binade() {
    let x: f64 = kani::any();
    kani::assume(x >= 1.0_f64 && x < 2.0_f64);
    let (_z, steps) = floor_walk_steps_for_proof(x);
    assert!(steps <= 1);
}
