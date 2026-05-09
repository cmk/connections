//! Step-count upper bounds for the float→Duration bridges in
//! `crate::time::duration`.
//!
//! Two parallel families of harnesses, both proving exhaustive
//! step bounds over symbolic-input slices.
//!
//! ## Walk harnesses (`*_walk_*`)
//!
//! Pin `walk_steps ≤ 1` for the legacy ULP walk on bounded-magnitude
//! and unit-binade slices. The walk fns are no longer called from
//! production for these Conns, but they're still emitted by
//! `def_walk_helpers!` and called from the
//! `*_solve_matches_walk_in_safe_range` proptest cross-checks in
//! `crate::time::duration::tests`. Breaking `ascend_to_ceil` /
//! `descend_to_ceil` would silently break those cross-checks; the
//! walk harnesses keep them honest. (Same harnesses as the
//! pre-Plan-2026-05-08-05 contract.)
//!
//! ## Solver harnesses (`*_solve_*`)
//!
//! Pin `solve_steps ≤ SOLVE_STEP_BOUND` (= 44) for `solve_to_ceil`
//! over the same input slices. The bound is structural to the binary
//! search (loop body halves the bracket each iteration); the
//! harnesses are the SMT-blessed seal on top. CBMC may take longer
//! on these than on the walk harnesses — see the plan's §Review for
//! contingency notes if a harness becomes intractable.
//!
//! Production-side exposers live in `crate::time::duration` behind
//! `#[cfg(kani)]`. They omit production fast-paths; this file
//! applies the matching `kani::assume`s.

use super::SOLVE_STEP_BOUND;

// ── T1 — bounded magnitude — walk path ──────────────────────────────

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

// ── T2 — single binade — walk path ──────────────────────────────────

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

// ── T1 — bounded magnitude — solver path ────────────────────────────

#[kani::proof]
#[kani::unwind(53)]
fn t1_f64_tdur_solve_steps_le_bound() {
    let v: f64 = kani::any();
    kani::assume(v.is_finite() && !v.is_nan());
    kani::assume(v.abs() <= 1e6_f64);
    let (_, steps) = crate::time::duration::f64_tdur_ceil_solve_steps_for_proof(v);
    assert!(steps <= SOLVE_STEP_BOUND);
}

#[kani::proof]
#[kani::unwind(53)]
fn t1_f32_tdur_solve_steps_le_bound() {
    let v: f32 = kani::any();
    kani::assume(v.is_finite() && !v.is_nan());
    kani::assume(v.abs() <= 1e6_f32);
    let (_, steps) = crate::time::duration::f32_tdur_ceil_solve_steps_for_proof(v);
    assert!(steps <= SOLVE_STEP_BOUND);
}

#[kani::proof]
#[kani::unwind(53)]
fn t1_f64_sdur_solve_steps_le_bound() {
    let v: f64 = kani::any();
    kani::assume(v.is_finite() && !v.is_nan());
    kani::assume(v > 0.0 && v <= 1e6_f64);
    let (_, steps) = crate::time::duration::f64_sdur_ceil_solve_steps_for_proof(v);
    assert!(steps <= SOLVE_STEP_BOUND);
}

#[kani::proof]
#[kani::unwind(53)]
fn t1_f32_sdur_solve_steps_le_bound() {
    let v: f32 = kani::any();
    kani::assume(v.is_finite() && !v.is_nan());
    kani::assume(v > 0.0 && v <= 1e6_f32);
    let (_, steps) = crate::time::duration::f32_sdur_ceil_solve_steps_for_proof(v);
    assert!(steps <= SOLVE_STEP_BOUND);
}

// ── T2 — single binade — solver path ────────────────────────────────

#[kani::proof]
#[kani::unwind(53)]
fn t2_f64_tdur_solve_steps_unit_binade() {
    let v: f64 = kani::any();
    kani::assume(v >= 1.0_f64 && v < 2.0_f64);
    let (_, steps) = crate::time::duration::f64_tdur_ceil_solve_steps_for_proof(v);
    assert!(steps <= SOLVE_STEP_BOUND);
}

#[kani::proof]
#[kani::unwind(53)]
fn t2_f32_tdur_solve_steps_unit_binade() {
    let v: f32 = kani::any();
    kani::assume(v >= 1.0_f32 && v < 2.0_f32);
    let (_, steps) = crate::time::duration::f32_tdur_ceil_solve_steps_for_proof(v);
    assert!(steps <= SOLVE_STEP_BOUND);
}

#[kani::proof]
#[kani::unwind(53)]
fn t2_f64_sdur_solve_steps_unit_binade() {
    let v: f64 = kani::any();
    kani::assume(v >= 1.0_f64 && v < 2.0_f64);
    let (_, steps) = crate::time::duration::f64_sdur_ceil_solve_steps_for_proof(v);
    assert!(steps <= SOLVE_STEP_BOUND);
}

#[kani::proof]
#[kani::unwind(53)]
fn t2_f32_sdur_solve_steps_unit_binade() {
    let v: f32 = kani::any();
    kani::assume(v >= 1.0_f32 && v < 2.0_f32);
    let (_, steps) = crate::time::duration::f32_sdur_ceil_solve_steps_for_proof(v);
    assert!(steps <= SOLVE_STEP_BOUND);
}
