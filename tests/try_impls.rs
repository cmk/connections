//! `?`-operator (`Try` / `FromResidual`) behaviour for [`Interval`],
//! [`Extended`], and [`ExtendedFloat`].
//!
//! Gated on the nightly `try_trait` feature — the whole file compiles to
//! nothing on stable / without the feature, so it never enters the
//! stable CI gate (same posture as the `f16`-gated code). Run with:
//!
//! ```text
//! cargo +nightly test --features try_trait --test try_impls
//! ```
//!
//! `?` and the explicit `Try` / `FromResidual` calls are themselves
//! unstable, so this test crate needs its own `try_trait_v2` gate (the
//! library's crate-level gate does not reach a separate integration
//! test binary).
#![cfg(feature = "try_trait")]
#![cfg_attr(feature = "try_trait", feature(try_trait_v2))]

use std::ops::{ControlFlow, FromResidual, Try};

use connections::extended::Extended;
use connections::float::ExtendedFloat;
use connections::interval::Interval;
use proptest::prelude::*;

// ── Extended<T> ─────────────────────────────────────────────────────

/// `?` extracts each `Finite` payload; the first bound hit short-circuits
/// the whole fn, carrying *which* bound out unchanged.
fn ext_sum(a: Extended<i32>, b: Extended<i32>) -> Extended<i32> {
    let x = a?;
    let y = b?;
    Extended::Finite(x + y)
}

#[test]
fn extended_question_extracts_and_propagates() {
    assert_eq!(
        ext_sum(Extended::Finite(2), Extended::Finite(5)),
        Extended::Finite(7)
    );
    // A bound short-circuits, preserving its identity.
    assert_eq!(
        ext_sum(Extended::NegInf, Extended::Finite(5)),
        Extended::NegInf
    );
    assert_eq!(
        ext_sum(Extended::Finite(2), Extended::PosInf),
        Extended::PosInf
    );
    // Left operand is evaluated first, so its bound wins.
    assert_eq!(
        ext_sum(Extended::PosInf, Extended::NegInf),
        Extended::PosInf
    );
}

/// `?` can change the payload type: the residual `Extended<Infallible>`
/// feeds `FromResidual for Extended<i64>` just as well as `<i32>`.
fn ext_widen(x: Extended<i32>) -> Extended<i64> {
    Extended::Finite(i64::from(x?))
}

#[test]
fn extended_question_changes_payload_type() {
    assert_eq!(ext_widen(Extended::Finite(7)), Extended::Finite(7_i64));
    assert_eq!(ext_widen(Extended::NegInf), Extended::NegInf);
    assert_eq!(ext_widen(Extended::PosInf), Extended::PosInf);
}

fn arb_ext_i32() -> impl Strategy<Value = Extended<i32>> {
    prop_oneof![
        1 => Just(Extended::NegInf),
        1 => Just(Extended::PosInf),
        3 => any::<i32>().prop_map(Extended::Finite),
    ]
}

proptest! {
    /// `branch` agrees with `finite`, and a broken bound round-trips back
    /// through `from_residual` to the identical value.
    #[test]
    fn extended_branch_agrees_with_finite(x in arb_ext_i32()) {
        match Try::branch(x) {
            ControlFlow::Continue(v) => prop_assert_eq!(x.finite(), Some(v)),
            ControlFlow::Break(r) => {
                prop_assert_eq!(x.finite(), None);
                let back: Extended<i32> = FromResidual::from_residual(r);
                prop_assert_eq!(back, x);
            }
        }
    }

    /// `from_output` ∘ `branch` is the identity on the payload.
    #[test]
    fn extended_from_output_roundtrips(v in any::<i32>()) {
        let wrapped = <Extended<i32> as Try>::from_output(v);
        prop_assert_eq!(wrapped, Extended::Finite(v));
        match Try::branch(wrapped) {
            ControlFlow::Continue(u) => prop_assert_eq!(u, v),
            ControlFlow::Break(_) => prop_assert!(false, "Finite must Continue"),
        }
    }
}

// ── ExtendedFloat<T> ────────────────────────────────────────────────

fn ef_sum(a: ExtendedFloat<f64>, b: ExtendedFloat<f64>) -> ExtendedFloat<f64> {
    let x = a?;
    let y = b?;
    ExtendedFloat::Extend(x + y)
}

#[test]
fn extended_float_question_extracts_and_propagates() {
    assert_eq!(
        ef_sum(ExtendedFloat::Extend(1.5), ExtendedFloat::Extend(2.0)),
        ExtendedFloat::Extend(3.5)
    );
    assert_eq!(
        ef_sum(ExtendedFloat::Bot, ExtendedFloat::Extend(2.0)),
        ExtendedFloat::Bot
    );
    assert_eq!(
        ef_sum(ExtendedFloat::Extend(1.5), ExtendedFloat::Top),
        ExtendedFloat::Top
    );
}

#[test]
fn extended_float_nan_is_a_payload_not_a_shortcircuit() {
    // NaN lives in the `Extend` slot, so `?` extracts it as an ordinary
    // payload — only the synthetic `Bot` / `Top` endpoints break. The
    // sum stays NaN, and `Extend(NaN) == Extend(NaN)` by the reflexive
    // `PartialEq`.
    let out = ef_sum(ExtendedFloat::Extend(f64::NAN), ExtendedFloat::Extend(1.0));
    assert_eq!(out, ExtendedFloat::Extend(f64::NAN));
}

fn arb_ef_f64() -> impl Strategy<Value = ExtendedFloat<f64>> {
    prop_oneof![
        1 => Just(ExtendedFloat::Bot),
        1 => Just(ExtendedFloat::Top),
        3 => any::<f64>().prop_map(ExtendedFloat::Extend),
    ]
}

proptest! {
    /// `Extend` continues; `Bot` / `Top` break and round-trip back to the
    /// identical endpoint through `from_residual`.
    #[test]
    fn extended_float_branch_partitions_by_variant(x in arb_ef_f64()) {
        match Try::branch(x) {
            ControlFlow::Continue(_) => prop_assert!(matches!(x, ExtendedFloat::Extend(_))),
            ControlFlow::Break(r) => {
                prop_assert!(matches!(x, ExtendedFloat::Bot | ExtendedFloat::Top));
                let back: ExtendedFloat<f64> = FromResidual::from_residual(r);
                prop_assert_eq!(back, x);
            }
        }
    }
}

// ── Interval<A> ─────────────────────────────────────────────────────

/// `?` yields a `Closed` interval's endpoints as `(lo, hi)`; `Empty`
/// short-circuits. The residual is payload-agnostic, so this widens
/// `Interval<i32>` into an `Interval<i64>`-returning fn.
fn iv_widen(iv: Interval<i32>) -> Interval<i64> {
    let (lo, hi) = iv?;
    Interval::new(i64::from(lo), i64::from(hi))
}

#[test]
fn interval_question_extracts_and_propagates() {
    assert_eq!(iv_widen(Interval::new(2, 5)), Interval::new(2_i64, 5));
    assert_eq!(iv_widen(Interval::Empty), Interval::<i64>::Empty);
}

fn arb_iv_i32() -> impl Strategy<Value = Interval<i32>> {
    prop_oneof![
        1 => Just(Interval::Empty),
        3 => (any::<i32>(), any::<i32>()).prop_map(|(a, b)| Interval::new(a, b)),
    ]
}

proptest! {
    /// `Closed` continues (recovering its endpoints); `Empty` breaks and
    /// round-trips back to `Empty`. `from_output` rebuilds the `Closed`.
    #[test]
    fn interval_branch_partitions_by_variant(iv in arb_iv_i32()) {
        match Try::branch(iv) {
            ControlFlow::Continue((lo, hi)) => {
                prop_assert_eq!(iv, Interval::Closed { lo, hi });
                prop_assert_eq!(<Interval<i32> as Try>::from_output((lo, hi)), iv);
            }
            ControlFlow::Break(r) => {
                prop_assert_eq!(iv, Interval::Empty);
                let back: Interval<i32> = FromResidual::from_residual(r);
                prop_assert_eq!(back, Interval::Empty);
            }
        }
    }
}
