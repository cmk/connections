//! Solver-step upper-bound theorems for the float→hifitime bridges
//! in `crate::hifi::{duration,epoch}`.
//!
//! Production now uses `solve_to_ceil` — a binary search in
//! `i128`-nanosecond space over a fixed `±2⁴²`-ns bracket — so the
//! per-call iteration count is bounded by
//! `⌈log₂(2 × 2⁴²)⌉ = 43` regardless of input magnitude. These
//! harnesses pin that bound formally on a magnitude-bounded slice;
//! the bound is structural to the solver body and holds equally on
//! the wider domain, but Kani gives us the SMT-blessed seal here.
//!
//! Plan 43 originally proved `steps ≤ 1` for the ULP-walk
//! implementation; the walk became unbounded at extreme magnitudes
//! (`f64::MAX` plateau ≈ 2 × 10¹² ns) which is why the solver
//! replaced it. The walks are still emitted by `def_walk_helpers!`
//! and used by float-narrowing Conns whose plateau is ≤ 1 dst-ULP,
//! but float→hifitime production callers no longer reach them.
//!
//! `f64_eutc_walks` is **deferred**: its widen consults `hifitime`'s
//! leap-second table, whose `partition_point` search makes the
//! per-iteration cost intractable for CBMC. `f64_etde_walks` /
//! `f64_etdb_walks` are also **deferred** for the same reason
//! (`f64::sin` inside the NAIF / ESA correction algorithms). Property
//! tests carry the load. ETDT is pure constant-offset arithmetic and
//! ships normally; ETAI similarly.

const SOLVE_STEP_BOUND: u32 = 44;

// ── T1 — bounded magnitude ──────────────────────────────────────────

#[kani::proof]
#[kani::unwind(45)]
fn t1_f64_hdur_solve_steps_le_bound() {
    let v: f64 = kani::any();
    kani::assume(v.is_finite() && !v.is_nan());
    kani::assume(v.abs() <= 1e6_f64);
    let (_, steps) = crate::hifi::duration::f64_hdur_ceil_walk_steps_for_proof(v);
    assert!(steps <= SOLVE_STEP_BOUND);
}

#[kani::proof]
#[kani::unwind(45)]
fn t1_f32_hdur_solve_steps_le_bound() {
    let v: f32 = kani::any();
    kani::assume(v.is_finite() && !v.is_nan());
    kani::assume(v.abs() <= 1e6_f32);
    let (_, steps) = crate::hifi::duration::f32_hdur_ceil_walk_steps_for_proof(v);
    assert!(steps <= SOLVE_STEP_BOUND);
}

#[kani::proof]
#[kani::unwind(45)]
fn t1_f64_etai_solve_steps_le_bound() {
    let v: f64 = kani::any();
    kani::assume(v.is_finite() && !v.is_nan());
    kani::assume(v.abs() <= 1e6_f64);
    let (_, steps) = crate::hifi::epoch::f64_etai_ceil_walk_steps_for_proof(v);
    assert!(steps <= SOLVE_STEP_BOUND);
}

#[kani::proof]
#[kani::unwind(45)]
fn t1_f64_etdt_solve_steps_le_bound() {
    let v: f64 = kani::any();
    kani::assume(v.is_finite() && !v.is_nan());
    kani::assume(v.abs() <= 1e6_f64);
    let (_, steps) = crate::hifi::epoch::f64_etdt_ceil_walk_steps_for_proof(v);
    assert!(steps <= SOLVE_STEP_BOUND);
}

// ── T2 — single binade ──────────────────────────────────────────────

#[kani::proof]
#[kani::unwind(45)]
fn t2_f64_hdur_solve_steps_unit_binade() {
    let v: f64 = kani::any();
    kani::assume(v >= 1.0_f64 && v < 2.0_f64);
    let (_, steps) = crate::hifi::duration::f64_hdur_ceil_walk_steps_for_proof(v);
    assert!(steps <= SOLVE_STEP_BOUND);
}

#[kani::proof]
#[kani::unwind(45)]
fn t2_f32_hdur_solve_steps_unit_binade() {
    let v: f32 = kani::any();
    kani::assume(v >= 1.0_f32 && v < 2.0_f32);
    let (_, steps) = crate::hifi::duration::f32_hdur_ceil_walk_steps_for_proof(v);
    assert!(steps <= SOLVE_STEP_BOUND);
}

#[kani::proof]
#[kani::unwind(45)]
fn t2_f64_etai_solve_steps_unit_binade() {
    let v: f64 = kani::any();
    kani::assume(v >= 1.0_f64 && v < 2.0_f64);
    let (_, steps) = crate::hifi::epoch::f64_etai_ceil_walk_steps_for_proof(v);
    assert!(steps <= SOLVE_STEP_BOUND);
}

#[kani::proof]
#[kani::unwind(45)]
fn t2_f64_etdt_solve_steps_unit_binade() {
    let v: f64 = kani::any();
    kani::assume(v >= 1.0_f64 && v < 2.0_f64);
    let (_, steps) = crate::hifi::epoch::f64_etdt_ceil_walk_steps_for_proof(v);
    assert!(steps <= SOLVE_STEP_BOUND);
}
