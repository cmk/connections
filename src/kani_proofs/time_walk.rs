//! Walk-step upper-bound theorems for the float→Duration bridges in
//! `crate::time::duration` — Plan 43's headline result for the time
//! domain.
//!
//! Each harness proves the ULP walk inside the production
//! `f???{tdur,sdur}_ceil` closure converges in ≤ 1 iteration on a
//! magnitude-bounded input slice. T0 (full finite non-NaN domain) was
//! attempted but the time-crate symex cost (per-iteration calls to
//! `Duration::new_ranged_unchecked` / `partial_cmp` plus
//! `Duration::saturating_seconds_f64`) pushed CBMC past 25 minutes of
//! solver time per harness; T1 keeps the proof tractable while still
//! covering the practical operating range.
//!
//! See `kani_proofs::float_walk` for the matching `F064F032` walk;
//! this file mirrors its T1/T2 tiered shape.
//!
//! Production-side exposers live in `crate::time::duration` behind
//! `#[cfg(kani)]`. They omit production fast-paths; this file applies
//! the matching `kani::assume`s on the input.

// ── T1 — bounded magnitude ───────────────────────────────────────────
//
// `|v| ≤ 1e6` excludes the f64 / f32 plateau (well below the
// rung-saturation boundary at ±9.22e18 for `time::Duration` and
// ±1.84e19 for `std::time::Duration`). On this slice the walk's
// initial estimate is within 1 rung-step of the truth, so a single
// correction step suffices.

#[kani::proof]
#[kani::unwind(3)]
fn t1_f64_tdur_walk_steps_le_1() {
    let v: f64 = kani::any();
    kani::assume(v.is_finite() && !v.is_nan());
    kani::assume(v.abs() <= 1e6_f64);
    let (_, steps) = crate::time::duration::f64_tdur_ceil_walk_steps_for_proof(v);
    assert!(steps <= 1);
}

#[kani::proof]
#[kani::unwind(3)]
fn t1_f32_tdur_walk_steps_le_1() {
    let v: f32 = kani::any();
    kani::assume(v.is_finite() && !v.is_nan());
    kani::assume(v.abs() <= 1e6_f32);
    let (_, steps) = crate::time::duration::f32_tdur_ceil_walk_steps_for_proof(v);
    assert!(steps <= 1);
}

#[kani::proof]
#[kani::unwind(3)]
fn t1_f64_sdur_walk_steps_le_1() {
    let v: f64 = kani::any();
    kani::assume(v.is_finite() && !v.is_nan());
    // Unsigned rung — production fast-paths `v <= 0.0` to ZERO before
    // the walk runs.
    kani::assume(v > 0.0 && v <= 1e6_f64);
    let (_, steps) = crate::time::duration::f64_sdur_ceil_walk_steps_for_proof(v);
    assert!(steps <= 1);
}

#[kani::proof]
#[kani::unwind(3)]
fn t1_f32_sdur_walk_steps_le_1() {
    let v: f32 = kani::any();
    kani::assume(v.is_finite() && !v.is_nan());
    kani::assume(v > 0.0 && v <= 1e6_f32);
    let (_, steps) = crate::time::duration::f32_sdur_ceil_walk_steps_for_proof(v);
    assert!(steps <= 1);
}

// ── T2 — single binade ───────────────────────────────────────────────
//
// `[1.0, 2.0)` is the canonical normal binade — full mantissa range,
// no exponent edge cases. By IEEE structural symmetry across binades,
// proving the bound here lifts to most of the well-behaved domain
// (saturation and subnormals excluded; T0/T1 cover those when
// tractable).

#[kani::proof]
#[kani::unwind(3)]
fn t2_f64_tdur_walk_steps_unit_binade() {
    let v: f64 = kani::any();
    kani::assume(v >= 1.0_f64 && v < 2.0_f64);
    let (_, steps) = crate::time::duration::f64_tdur_ceil_walk_steps_for_proof(v);
    assert!(steps <= 1);
}

#[kani::proof]
#[kani::unwind(3)]
fn t2_f32_tdur_walk_steps_unit_binade() {
    let v: f32 = kani::any();
    kani::assume(v >= 1.0_f32 && v < 2.0_f32);
    let (_, steps) = crate::time::duration::f32_tdur_ceil_walk_steps_for_proof(v);
    assert!(steps <= 1);
}

#[kani::proof]
#[kani::unwind(3)]
fn t2_f64_sdur_walk_steps_unit_binade() {
    let v: f64 = kani::any();
    kani::assume(v >= 1.0_f64 && v < 2.0_f64);
    let (_, steps) = crate::time::duration::f64_sdur_ceil_walk_steps_for_proof(v);
    assert!(steps <= 1);
}

#[kani::proof]
#[kani::unwind(3)]
fn t2_f32_sdur_walk_steps_unit_binade() {
    let v: f32 = kani::any();
    kani::assume(v >= 1.0_f32 && v < 2.0_f32);
    let (_, steps) = crate::time::duration::f32_sdur_ceil_walk_steps_for_proof(v);
    assert!(steps <= 1);
}
