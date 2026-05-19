//! Shared f16 proptest strategy for the
//! `tests/fixed/*_float_q_f16.rs` submodules.
//!
//! Split out of `helpers.rs` because referencing `f16` requires
//! `#![feature(f16)]` at the test crate root (`tests/fixed.rs`,
//! gated by `#[cfg(feature = "f16")]`).

#![allow(dead_code)] // Each integration test imports a subset.

use connections::float::ExtendedFloat;
use proptest::prelude::*;

pub fn extended_float_f16() -> impl Strategy<Value = ExtendedFloat<f16>> {
    prop_oneof![
        1 => Just(ExtendedFloat::Bot),
        1 => Just(ExtendedFloat::Top),
        3 => prop_oneof![
            1 => (-10.0_f32..10.0_f32).prop_map(|v| v as f16),
            2 => prop_oneof![
                Just(f16::NAN),
                Just(f16::INFINITY),
                Just(f16::NEG_INFINITY),
                Just(0.0_f16),
                Just(-0.0_f16),
                Just(f16::MIN_POSITIVE),
                Just(f16::MAX),
                Just(f16::MIN),
                Just(f16::EPSILON),
                Just(f16::from_bits(1)),
                // f16's exact-integer boundary (mantissa 11 →
                // 2^11 = 2048 is the largest f16 with unit ULP).
                Just(2.0_f16.powi(11)),
                Just(-2.0_f16.powi(11)),
                // High-magnitude finite f16; below f16::MAX (65504)
                // and within u16 / i16 reach exactly.
                Just(2.0_f16.powi(15)),
                Just(-2.0_f16.powi(15)),
                // i8/u8 saturation boundaries — small enough to fit
                // in f16 exactly.
                Just(127.0_f16),
                Just(128.0_f16),
                Just(-128.0_f16),
                Just(255.0_f16),
                Just(256.0_f16),
            ],
        ].prop_map(ExtendedFloat::Extend),
    ]
}
