//! Galois-law proptest battery for `fixed::i032`'s f32/f64 → Q-format Conns.
//!
//! See `tests/fixed_i8_float_q_galois.rs` for the rationale. f32
//! source is L-only (32 > 24); f64 source is full triple (32 ≤ 53).

use super::helpers::{extended_float_f32, extended_float_f64};
use connections::extended::Extended;
use connections::fixed::i032::*;
use fixed::FixedI32;
use fixed::types::extra::{U0, U4, U8, U16, U24, U32};
use proptest::prelude::*;

macro_rules! props_for_float_q_l {
    ($mod_name:ident, $conn:ident, $float_ext:ident, $Frac:ty) => {
        connections::law_battery! {
            mod $mod_name,
            conn: $conn,
            fine: $float_ext(),
            coarse: prop_oneof![
                1 => Just(Extended::NegInf),
                1 => Just(Extended::PosInf),
                1 => Just(Extended::Finite(FixedI32::<$Frac>::from_bits(0))),
                1 => Just(Extended::Finite(FixedI32::<$Frac>::from_bits(i32::MIN))),
                1 => Just(Extended::Finite(FixedI32::<$Frac>::from_bits(i32::MAX))),
                8 => any::<i32>()
                    .prop_map(|b| Extended::Finite(FixedI32::<$Frac>::from_bits(b))),
            ],
            subset: l_only,
            cases: 1024,
        }
    };
}
macro_rules! props_for_float_q_k {
    ($mod_name:ident, $conn:ident, $float_ext:ident, $Frac:ty) => {
        connections::law_battery! {
            mod $mod_name,
            conn: $conn,
            fine: $float_ext(),
            coarse: prop_oneof![
                1 => Just(Extended::NegInf),
                1 => Just(Extended::PosInf),
                1 => Just(Extended::Finite(FixedI32::<$Frac>::from_bits(0))),
                1 => Just(Extended::Finite(FixedI32::<$Frac>::from_bits(i32::MIN))),
                1 => Just(Extended::Finite(FixedI32::<$Frac>::from_bits(i32::MAX))),
                8 => any::<i32>()
                    .prop_map(|b| Extended::Finite(FixedI32::<$Frac>::from_bits(b))),
            ],
            cases: 1024,
        }
    };
}

props_for_float_q_l!(laws_f032q000, F032Q000, extended_float_f32, U0);
props_for_float_q_l!(laws_f032q004, F032Q004, extended_float_f32, U4);
props_for_float_q_l!(laws_f032q008, F032Q008, extended_float_f32, U8);
props_for_float_q_l!(laws_f032q016, F032Q016, extended_float_f32, U16);
props_for_float_q_l!(laws_f032q024, F032Q024, extended_float_f32, U24);
props_for_float_q_l!(laws_f032q032, F032Q032, extended_float_f32, U32);

props_for_float_q_k!(laws_f064q000, F064Q000, extended_float_f64, U0);
props_for_float_q_k!(laws_f064q004, F064Q004, extended_float_f64, U4);
props_for_float_q_k!(laws_f064q008, F064Q008, extended_float_f64, U8);
props_for_float_q_k!(laws_f064q016, F064Q016, extended_float_f64, U16);
props_for_float_q_k!(laws_f064q024, F064Q024, extended_float_f64, U24);
props_for_float_q_k!(laws_f064q032, F064Q032, extended_float_f64, U32);
