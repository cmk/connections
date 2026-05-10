//! Shared strategies for the `fixed_*_float_q_galois` integration
//! tests.
//!
//! `connections::prop::arb` is gated on `feature = "testing"`, which
//! the CI test job doesn't pass to integration tests. Inlining here
//! keeps the per-test files compact and the strategies are bit-for-
//! bit copies of `arb_f32_bounded` / `arb_f64_bounded` +
//! `extended_float_f{32,64}` from `src/prop/arb.rs`.

#![allow(dead_code)] // Each integration test imports a subset.

use connections::float::ExtendedFloat;
use proptest::prelude::*;

pub fn extended_float_f32() -> impl Strategy<Value = ExtendedFloat<f32>> {
    prop_oneof![
        1 => Just(ExtendedFloat::Bot),
        1 => Just(ExtendedFloat::Top),
        3 => prop_oneof![
            1 => -10.0_f32..10.0_f32,
            2 => prop_oneof![
                Just(f32::NAN),
                Just(f32::INFINITY),
                Just(f32::NEG_INFINITY),
                Just(0.0_f32),
                Just(-0.0_f32),
                Just(f32::MIN_POSITIVE),
                Just(f32::MAX),
                Just(f32::MIN),
                Just(f32::EPSILON),
                Just(f32::from_bits(1)),
            ],
        ].prop_map(ExtendedFloat::Extend),
    ]
}

pub fn extended_float_f64() -> impl Strategy<Value = ExtendedFloat<f64>> {
    prop_oneof![
        1 => Just(ExtendedFloat::Bot),
        1 => Just(ExtendedFloat::Top),
        3 => prop_oneof![
            1 => -1.0e9_f64..1.0e9_f64,
            2 => prop_oneof![
                Just(f64::NAN),
                Just(f64::INFINITY),
                Just(f64::NEG_INFINITY),
                Just(0.0_f64),
                Just(-0.0_f64),
                Just(f64::MIN_POSITIVE),
                Just(f64::MAX),
                Just(f64::MIN),
                Just(f64::EPSILON),
                Just(f64::from_bits(1)),
            ],
        ].prop_map(ExtendedFloat::Extend),
    ]
}
