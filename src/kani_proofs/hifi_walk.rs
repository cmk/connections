//! Step-count upper bounds for the float→hifitime bridges in
//! `crate::hifi::{duration,epoch}`.
//!
//! Two parallel families of harnesses; see
//! `crate::kani_proofs::time_walk` for the full layout rationale.
//!
//! ## Walk harnesses (`*_walk_*`)
//!
//! Pin `walk_steps ≤ 1` for the legacy ULP walk on bounded slices.
//! No longer reached from production but still called by
//! `*_solve_matches_walk_in_safe_range` proptest cross-checks.
//!
//! ## Solver harnesses (`*_solve_*`)
//!
//! Pin `solve_steps ≤ SOLVE_STEP_BOUND` (= 52) for `solve_to_ceil`
//! over the same slices.
//!
//! `f64_eutc_walks` is **deferred**: its widen consults `hifitime`'s
//! leap-second table. `f64_etde_walks` / `f64_etdb_walks` are also
//! deferred (`f64::sin` inside the NAIF / ESA correction
//! algorithms). ETDT and ETAI are pure constant-offset arithmetic
//! and ship harnesses normally.

use super::SOLVE_STEP_BOUND;

// ── T1 — bounded magnitude — walk path ──────────────────────────────

#[kani::proof]
#[kani::unwind(3)]
fn t1_f64_hdur_walk_steps_le_1() {
    let v: f64 = kani::any();
    kani::assume(v.is_finite() && !v.is_nan());
    kani::assume(v.abs() <= 1e6_f64);
    let (_, steps) = crate::hifi::duration::f64_hdur_ceil_walk_steps_for_proof(v);
    assert!(steps <= 1);
}

#[kani::proof]
#[kani::unwind(3)]
fn t1_f32_hdur_walk_steps_le_1() {
    let v: f32 = kani::any();
    kani::assume(v.is_finite() && !v.is_nan());
    kani::assume(v.abs() <= 1e6_f32);
    let (_, steps) = crate::hifi::duration::f32_hdur_ceil_walk_steps_for_proof(v);
    assert!(steps <= 1);
}

#[kani::proof]
#[kani::unwind(3)]
fn t1_f64_etai_walk_steps_le_1() {
    let v: f64 = kani::any();
    kani::assume(v.is_finite() && !v.is_nan());
    kani::assume(v.abs() <= 1e6_f64);
    let (_, steps) = crate::hifi::epoch::f64_etai_ceil_walk_steps_for_proof(v);
    assert!(steps <= 1);
}

#[kani::proof]
#[kani::unwind(3)]
fn t1_f64_etdt_walk_steps_le_1() {
    let v: f64 = kani::any();
    kani::assume(v.is_finite() && !v.is_nan());
    kani::assume(v.abs() <= 1e6_f64);
    let (_, steps) = crate::hifi::epoch::f64_etdt_ceil_walk_steps_for_proof(v);
    assert!(steps <= 1);
}

// ── T2 — single binade — walk path ──────────────────────────────────

#[kani::proof]
#[kani::unwind(3)]
fn t2_f64_hdur_walk_steps_unit_binade() {
    let v: f64 = kani::any();
    kani::assume(v >= 1.0_f64 && v < 2.0_f64);
    let (_, steps) = crate::hifi::duration::f64_hdur_ceil_walk_steps_for_proof(v);
    assert!(steps <= 1);
}

#[kani::proof]
#[kani::unwind(3)]
fn t2_f32_hdur_walk_steps_unit_binade() {
    let v: f32 = kani::any();
    kani::assume(v >= 1.0_f32 && v < 2.0_f32);
    let (_, steps) = crate::hifi::duration::f32_hdur_ceil_walk_steps_for_proof(v);
    assert!(steps <= 1);
}

#[kani::proof]
#[kani::unwind(3)]
fn t2_f64_etai_walk_steps_unit_binade() {
    let v: f64 = kani::any();
    kani::assume(v >= 1.0_f64 && v < 2.0_f64);
    let (_, steps) = crate::hifi::epoch::f64_etai_ceil_walk_steps_for_proof(v);
    assert!(steps <= 1);
}

#[kani::proof]
#[kani::unwind(3)]
fn t2_f64_etdt_walk_steps_unit_binade() {
    let v: f64 = kani::any();
    kani::assume(v >= 1.0_f64 && v < 2.0_f64);
    let (_, steps) = crate::hifi::epoch::f64_etdt_ceil_walk_steps_for_proof(v);
    assert!(steps <= 1);
}

// ── T1 — bounded magnitude — solver path ────────────────────────────

#[kani::proof]
#[kani::unwind(53)]
fn t1_f64_hdur_solve_steps_le_bound() {
    let v: f64 = kani::any();
    kani::assume(v.is_finite() && !v.is_nan());
    kani::assume(v.abs() <= 1e6_f64);
    let (_, steps) = crate::hifi::duration::f64_hdur_ceil_solve_steps_for_proof(v);
    assert!(steps <= SOLVE_STEP_BOUND);
}

#[kani::proof]
#[kani::unwind(53)]
fn t1_f32_hdur_solve_steps_le_bound() {
    let v: f32 = kani::any();
    kani::assume(v.is_finite() && !v.is_nan());
    kani::assume(v.abs() <= 1e6_f32);
    let (_, steps) = crate::hifi::duration::f32_hdur_ceil_solve_steps_for_proof(v);
    assert!(steps <= SOLVE_STEP_BOUND);
}

#[kani::proof]
#[kani::unwind(53)]
fn t1_f64_etai_solve_steps_le_bound() {
    let v: f64 = kani::any();
    kani::assume(v.is_finite() && !v.is_nan());
    kani::assume(v.abs() <= 1e6_f64);
    let (_, steps) = crate::hifi::epoch::f64_etai_ceil_solve_steps_for_proof(v);
    assert!(steps <= SOLVE_STEP_BOUND);
}

#[kani::proof]
#[kani::unwind(53)]
fn t1_f64_etdt_solve_steps_le_bound() {
    let v: f64 = kani::any();
    kani::assume(v.is_finite() && !v.is_nan());
    kani::assume(v.abs() <= 1e6_f64);
    let (_, steps) = crate::hifi::epoch::f64_etdt_ceil_solve_steps_for_proof(v);
    assert!(steps <= SOLVE_STEP_BOUND);
}

// ── T2 — single binade — solver path ────────────────────────────────

#[kani::proof]
#[kani::unwind(53)]
fn t2_f64_hdur_solve_steps_unit_binade() {
    let v: f64 = kani::any();
    kani::assume(v >= 1.0_f64 && v < 2.0_f64);
    let (_, steps) = crate::hifi::duration::f64_hdur_ceil_solve_steps_for_proof(v);
    assert!(steps <= SOLVE_STEP_BOUND);
}

#[kani::proof]
#[kani::unwind(53)]
fn t2_f32_hdur_solve_steps_unit_binade() {
    let v: f32 = kani::any();
    kani::assume(v >= 1.0_f32 && v < 2.0_f32);
    let (_, steps) = crate::hifi::duration::f32_hdur_ceil_solve_steps_for_proof(v);
    assert!(steps <= SOLVE_STEP_BOUND);
}

#[kani::proof]
#[kani::unwind(53)]
fn t2_f64_etai_solve_steps_unit_binade() {
    let v: f64 = kani::any();
    kani::assume(v >= 1.0_f64 && v < 2.0_f64);
    let (_, steps) = crate::hifi::epoch::f64_etai_ceil_solve_steps_for_proof(v);
    assert!(steps <= SOLVE_STEP_BOUND);
}

#[kani::proof]
#[kani::unwind(53)]
fn t2_f64_etdt_solve_steps_unit_binade() {
    let v: f64 = kani::any();
    kani::assume(v >= 1.0_f64 && v < 2.0_f64);
    let (_, steps) = crate::hifi::epoch::f64_etdt_ceil_solve_steps_for_proof(v);
    assert!(steps <= SOLVE_STEP_BOUND);
}
