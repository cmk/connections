//! Galois-law proptest battery for `fixed::u032`'s f32/f64 → Q-format Conns.

use super::helpers::{extended_float_f32, extended_float_f64};
use connections::extended::Extended;
use connections::fixed::u032::*;
use fixed::FixedU32;
use fixed::types::extra::{
    U0 as F0, U4 as F4, U8 as F8, U16 as F16, U24 as F24, U31 as F31, U32 as F32,
};
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
                1 => Just(Extended::Finite(FixedU32::<$Frac>::from_bits(0))),
                1 => Just(Extended::Finite(FixedU32::<$Frac>::from_bits(u32::MAX))),
                8 => any::<u32>()
                    .prop_map(|b| Extended::Finite(FixedU32::<$Frac>::from_bits(b))),
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
                1 => Just(Extended::Finite(FixedU32::<$Frac>::from_bits(0))),
                1 => Just(Extended::Finite(FixedU32::<$Frac>::from_bits(u32::MAX))),
                8 => any::<u32>()
                    .prop_map(|b| Extended::Finite(FixedU32::<$Frac>::from_bits(b))),
            ],
            cases: 1024,
        }
    };
}

props_for_float_q_l!(laws_f032q000, F032Q000, extended_float_f32, F0);
props_for_float_q_l!(laws_f032q004, F032Q004, extended_float_f32, F4);
props_for_float_q_l!(laws_f032q008, F032Q008, extended_float_f32, F8);
props_for_float_q_l!(laws_f032q016, F032Q016, extended_float_f32, F16);
props_for_float_q_l!(laws_f032q024, F032Q024, extended_float_f32, F24);
props_for_float_q_l!(laws_f032q031, F032Q031, extended_float_f32, F31);
props_for_float_q_l!(laws_f032q032, F032Q032, extended_float_f32, F32);

props_for_float_q_k!(laws_f064q000, F064Q000, extended_float_f64, F0);
props_for_float_q_k!(laws_f064q004, F064Q004, extended_float_f64, F4);
props_for_float_q_k!(laws_f064q008, F064Q008, extended_float_f64, F8);
props_for_float_q_k!(laws_f064q016, F064Q016, extended_float_f64, F16);
props_for_float_q_k!(laws_f064q024, F064Q024, extended_float_f64, F24);
props_for_float_q_k!(laws_f064q031, F064Q031, extended_float_f64, F31);
props_for_float_q_k!(laws_f064q032, F064Q032, extended_float_f64, F32);
