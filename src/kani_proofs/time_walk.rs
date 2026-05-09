//! Solver-step upper-bound theorems for the float→Duration bridges
//! in `crate::time::duration`.
//!
//! The production path is now `solve_to_ceil` — a binary search in
//! `i128`-nanosecond space over a fixed `±2⁴²`-ns bracket around the
//! starting estimate. The search halves the gap each iteration, so
//! the per-call iteration count is bounded by
//! `⌈log₂(2 × 2⁴²)⌉ = 43` regardless of input magnitude. These
//! harnesses pin that bound formally.
//!
//! Earlier (Plan 43) the same exposers proved `steps ≤ 1` for the
//! ULP-walk implementation; the walk became unbounded at extreme
//! magnitudes (`f64::MAX` plateau ≈ 2 × 10¹² ns) which is why the
//! solver replaced it. The walks are still emitted by the macro —
//! see `crate::float::def_walk_helpers!` — and remain useful for the
//! float-narrowing Conns whose plateau is ≤ 1 dst-ULP, but the
//! float→Duration production callers no longer reach them.
//!
//! Production-side exposers live in `crate::time::duration` behind
//! `#[cfg(kani)]`. They omit production fast-paths; this file applies
//! matching `kani::assume`s on the input.

const SOLVE_STEP_BOUND: u32 = 44;

// ── T1 — bounded magnitude ───────────────────────────────────────────

#[kani::proof]
#[kani::unwind(45)]
fn t1_f64_tdur_solve_steps_le_bound() {
    let v: f64 = kani::any();
    kani::assume(v.is_finite() && !v.is_nan());
    kani::assume(v.abs() <= 1e6_f64);
    let (_, steps) = crate::time::duration::f64_tdur_ceil_walk_steps_for_proof(v);
    assert!(steps <= SOLVE_STEP_BOUND);
}

#[kani::proof]
#[kani::unwind(45)]
fn t1_f32_tdur_solve_steps_le_bound() {
    let v: f32 = kani::any();
    kani::assume(v.is_finite() && !v.is_nan());
    kani::assume(v.abs() <= 1e6_f32);
    let (_, steps) = crate::time::duration::f32_tdur_ceil_walk_steps_for_proof(v);
    assert!(steps <= SOLVE_STEP_BOUND);
}

#[kani::proof]
#[kani::unwind(45)]
fn t1_f64_sdur_solve_steps_le_bound() {
    let v: f64 = kani::any();
    kani::assume(v.is_finite() && !v.is_nan());
    // Unsigned rung — production fast-paths `v <= 0.0` to ZERO before
    // the solver runs.
    kani::assume(v > 0.0 && v <= 1e6_f64);
    let (_, steps) = crate::time::duration::f64_sdur_ceil_walk_steps_for_proof(v);
    assert!(steps <= SOLVE_STEP_BOUND);
}

#[kani::proof]
#[kani::unwind(45)]
fn t1_f32_sdur_solve_steps_le_bound() {
    let v: f32 = kani::any();
    kani::assume(v.is_finite() && !v.is_nan());
    kani::assume(v > 0.0 && v <= 1e6_f32);
    let (_, steps) = crate::time::duration::f32_sdur_ceil_walk_steps_for_proof(v);
    assert!(steps <= SOLVE_STEP_BOUND);
}

// ── T2 — single binade ───────────────────────────────────────────────

#[kani::proof]
#[kani::unwind(45)]
fn t2_f64_tdur_solve_steps_unit_binade() {
    let v: f64 = kani::any();
    kani::assume(v >= 1.0_f64 && v < 2.0_f64);
    let (_, steps) = crate::time::duration::f64_tdur_ceil_walk_steps_for_proof(v);
    assert!(steps <= SOLVE_STEP_BOUND);
}

#[kani::proof]
#[kani::unwind(45)]
fn t2_f32_tdur_solve_steps_unit_binade() {
    let v: f32 = kani::any();
    kani::assume(v >= 1.0_f32 && v < 2.0_f32);
    let (_, steps) = crate::time::duration::f32_tdur_ceil_walk_steps_for_proof(v);
    assert!(steps <= SOLVE_STEP_BOUND);
}

#[kani::proof]
#[kani::unwind(45)]
fn t2_f64_sdur_solve_steps_unit_binade() {
    let v: f64 = kani::any();
    kani::assume(v >= 1.0_f64 && v < 2.0_f64);
    let (_, steps) = crate::time::duration::f64_sdur_ceil_walk_steps_for_proof(v);
    assert!(steps <= SOLVE_STEP_BOUND);
}

#[kani::proof]
#[kani::unwind(45)]
fn t2_f32_sdur_solve_steps_unit_binade() {
    let v: f32 = kani::any();
    kani::assume(v >= 1.0_f32 && v < 2.0_f32);
    let (_, steps) = crate::time::duration::f32_sdur_ceil_walk_steps_for_proof(v);
    assert!(steps <= SOLVE_STEP_BOUND);
}
