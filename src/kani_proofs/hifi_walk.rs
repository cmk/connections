//! Walk-step upper-bound theorems for the float→hifitime bridges in
//! `crate::hifi::{duration,epoch}` — Plan 43's headline result for
//! the hifi domain.
//!
//! Each harness proves the ULP walk inside the production
//! `f???hdur_ceil` / `etaif064_ceil` closures converges in ≤ 1
//! iteration on a magnitude-bounded slice. The structure mirrors
//! `crate::kani_proofs::time_walk`: T0 (full finite non-NaN) was
//! attempted but stalls in CBMC's SAT loop past the practical
//! solver budget once `Duration::saturating_seconds_f64` and the
//! per-iteration `total_nanoseconds` calls are unrolled. T1 caps
//! magnitude so the walk's initial estimate is within 1 rung-step
//! and a single correction suffices.
//!
//! `f64_eutc_walks` is **deferred**: its widen consults `hifitime`'s
//! leap-second table, whose `partition_point` search makes the
//! per-iteration cost intractable for CBMC.

// ── T1 — bounded magnitude ──────────────────────────────────────────

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

// ── T2 — single binade ──────────────────────────────────────────────

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
