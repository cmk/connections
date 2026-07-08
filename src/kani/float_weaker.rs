//! Weaker SMT-tractable properties for `F064F032`. Full Galois laws
//! over the IEEE bit space are intractable for CBMC's FP theory; these
//! harnesses cover the lower-cost, individually-useful slices.
//!
//! Every harness restricts inputs to **finite, non-NaN** values, since
//! NaN handling is a separate question (handled by the `*_nan` unit
//! tests in `src/float/f064.rs`).

use crate::conn::{ConnL, ConnR};
use crate::float::N5;
use crate::float::f064::F064F032;
use crate::prop::conn as conn_laws;

// Helper — symbolic finite-non-NaN N5<f64>.
fn arb_finite_ef64() -> N5<f64> {
    let v: f64 = kani::any();
    kani::assume(v.is_finite() && !v.is_nan());
    N5::new(v)
}

// Helper — symbolic finite-non-NaN N5<f32>.
fn arb_finite_ef32() -> N5<f32> {
    let v: f32 = kani::any();
    kani::assume(v.is_finite() && !v.is_nan());
    N5::new(v)
}

// Helper — symbolic N5::new(f64) within f32's representable range.
// Inputs whose magnitude exceeds `f32::MAX as f64` saturate to ±∞ in
// f32, so the round-trip embedding is no longer finite. The
// finite-in-finite-out claim only applies on this in-range slice.
fn arb_in_f32_range_ef64() -> N5<f64> {
    let v: f64 = kani::any();
    kani::assume(v.is_finite() && !v.is_nan());
    kani::assume(v.abs() <= f32::MAX as f64);
    N5::new(v)
}

/// `inner(ceil(x))` is finite when `x` is finite **and within f32's
/// representable range**. Inputs above `f32::MAX` saturate the ceil
/// to `f32::INFINITY`; that's correct numerical behavior, not a bug.
#[kani::proof]
#[kani::unwind(4)]
fn finite_in_finite_out_ceil_in_range() {
    let x = arb_in_f32_range_ef64();
    let y = F064F032.upper(F064F032.ceil(x));
    assert!(y.into_inner().is_finite());
}

/// Same property, floor side.
#[kani::proof]
#[kani::unwind(4)]
fn finite_in_finite_out_floor_in_range() {
    let x = arb_in_f32_range_ef64();
    let y = F064F032.lower(F064F032.floor(x));
    assert!(y.into_inner().is_finite());
}

/// Closure law (left): `x ≤ inner(ceil(x))` for finite, non-NaN `x`.
#[kani::proof]
#[kani::unwind(4)]
fn closure_l_finite() {
    let x = arb_finite_ef64();
    assert!(conn_laws::closure_l(&F064F032.view_l(), x));
}

/// Closure law (right): `inner(floor(x)) ≤ x` for finite, non-NaN `x`.
#[kani::proof]
#[kani::unwind(4)]
fn closure_r_finite() {
    let x = arb_finite_ef64();
    assert!(conn_laws::closure_r(&F064F032.view_r(), x));
}

/// Idempotence at the lifted level: `(inner ∘ ceil)² == (inner ∘
/// ceil)` over finite, non-NaN inputs. Walking-bound = 1 for the
/// **composed** Conn (note: distinct from the headline ULP-walk
/// bound in `float_walk.rs`, which counts ±1-ULP steps inside the
/// inner f32 walker).
#[kani::proof]
#[kani::unwind(4)]
fn idempotent_l_finite() {
    let x = arb_finite_ef64();
    assert!(conn_laws::idempotent_l(&F064F032.view_l(), x));
}

/// Sandwich: `floor(x) ≤ ceil(x)` for finite, non-NaN `x`.
#[kani::proof]
#[kani::unwind(4)]
fn floor_le_ceil_finite() {
    let x = arb_finite_ef64();
    assert!(conn_laws::floor_le_ceil(&F064F032, x));
}

/// `inner(b) ≤ inner(b')` ⟹ `b ≤ b'` (order-reflection of the
/// embedding) on finite, non-NaN target endpoints. The defining
/// property of an adjoint triple — see `prop::conn::order_reflecting`.
#[kani::proof]
#[kani::unwind(4)]
fn order_reflecting_finite() {
    let b1 = arb_finite_ef32();
    let b2 = arb_finite_ef32();
    assert!(conn_laws::order_reflecting(&F064F032, b1, b2));
}

/// Round-trip on rounds: `ceil(inner(b)) == b` for finite-non-NaN `b`.
/// Holds because `inner` is the lossless `f32 → f64` widening, so
/// every `b ∈ image(ceil)` is a "round" value.
#[kani::proof]
#[kani::unwind(4)]
fn roundtrip_ceil_finite() {
    let b = arb_finite_ef32();
    assert!(conn_laws::roundtrip_ceil(&F064F032.view_l(), b));
}
