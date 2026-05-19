//! Galois-law proptest battery for `fixed::u008`'s f32/f64 → Q-format Conns.
//! See `tests/fixed_i8_float_q_galois.rs` for the rationale.

use super::helpers::{extended_float_f32, extended_float_f64};
use connections::extended::Extended;
use connections::fixed::u008::*;
use fixed::FixedU8;
use fixed::types::extra::{
    U0 as F0, U1 as F1, U2 as F2, U3 as F3, U4 as F4, U6 as F6, U7 as F7, U8 as F8,
};
use proptest::prelude::*;

macro_rules! props_for_float_q {
    ($mod_name:ident, $conn:ident, $float_ext:ident, $Frac:ty) => {
        connections::law_battery! {
            mod $mod_name,
            conn: $conn,
            fine: $float_ext(),
            coarse: prop_oneof![
                1 => Just(Extended::NegInf),
                1 => Just(Extended::PosInf),
                1 => Just(Extended::Finite(FixedU8::<$Frac>::from_bits(0))),
                1 => Just(Extended::Finite(FixedU8::<$Frac>::from_bits(u8::MAX))),
                8 => any::<u8>()
                    .prop_map(|b| Extended::Finite(FixedU8::<$Frac>::from_bits(b))),
            ],
            cases: 1024,
        }
    };
}

props_for_float_q!(laws_f032q000, F032Q000, extended_float_f32, F0);
props_for_float_q!(laws_f032q001, F032Q001, extended_float_f32, F1);
props_for_float_q!(laws_f032q002, F032Q002, extended_float_f32, F2);
props_for_float_q!(laws_f032q003, F032Q003, extended_float_f32, F3);
props_for_float_q!(laws_f032q004, F032Q004, extended_float_f32, F4);
props_for_float_q!(laws_f032q006, F032Q006, extended_float_f32, F6);
props_for_float_q!(laws_f032q007, F032Q007, extended_float_f32, F7);
props_for_float_q!(laws_f032q008, F032Q008, extended_float_f32, F8);

props_for_float_q!(laws_f064q000, F064Q000, extended_float_f64, F0);
props_for_float_q!(laws_f064q001, F064Q001, extended_float_f64, F1);
props_for_float_q!(laws_f064q002, F064Q002, extended_float_f64, F2);
props_for_float_q!(laws_f064q003, F064Q003, extended_float_f64, F3);
props_for_float_q!(laws_f064q004, F064Q004, extended_float_f64, F4);
props_for_float_q!(laws_f064q006, F064Q006, extended_float_f64, F6);
props_for_float_q!(laws_f064q007, F064Q007, extended_float_f64, F7);
props_for_float_q!(laws_f064q008, F064Q008, extended_float_f64, F8);
