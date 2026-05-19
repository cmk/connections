//! Shared strategies for the `tests/fixed/*_float_q.rs` submodules.
//!
//! These are bit-for-bit copies of `arb_f32_bounded` /
//! `arb_f64_bounded` + `extended_float_f{32,64}` from
//! `src/prop/arb.rs`. Inlining here (rather than depending on
//! `connections::prop::arb`) lets this test binary build without
//! the `proptest` cargo feature having to be on the manifest of
//! the integration-test target — `proptest` is a dev-dep of this
//! crate, so the strategies and `Strategy` trait are already in
//! scope regardless of the feature.

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
                // Saturation plateaus mirroring `arb_f32_bounded`.
                Just(2.0_f32.powi(31)),
                Just(-2.0_f32.powi(31)),
                Just(f32::from_bits(2.0_f32.powi(31).to_bits() + 1)),
                Just(2.0_f32.powi(32)),
                Just(f32::from_bits(2.0_f32.powi(32).to_bits() + 1)),
                Just(2.0_f32.powi(63)),
                Just(f32::from_bits(2.0_f32.powi(63).to_bits() + 1)),
                Just(2.0_f32.powi(64)),
                Just(f32::from_bits(2.0_f32.powi(64).to_bits() + 1)),
                Just(2.0_f32.powi(127)),
                Just(-2.0_f32.powi(127)),
                Just(f32::from_bits(2.0_f32.powi(127).to_bits() + 1)),
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
                // Saturation plateaus mirroring `arb_f64_bounded`.
                Just(2.0_f64.powi(63)),
                Just(-2.0_f64.powi(63)),
                Just(f64::from_bits(2.0_f64.powi(63).to_bits() + 1)),
                Just(2.0_f64.powi(64)),
                Just(f64::from_bits(2.0_f64.powi(64).to_bits() + 1)),
                Just(2.0_f64.powi(127)),
                Just(-2.0_f64.powi(127)),
                Just(f64::from_bits(2.0_f64.powi(127).to_bits() + 1)),
                Just(2.0_f64.powi(128)),
                Just(f64::from_bits(2.0_f64.powi(128).to_bits() + 1)),
            ],
        ].prop_map(ExtendedFloat::Extend),
    ]
}
