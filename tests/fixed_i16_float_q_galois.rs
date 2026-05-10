//! Galois-law proptest battery for `fixed::i016`'s f32/f64 → Q-format Conns.
//! See `tests/fixed_i8_float_q_galois.rs` for the rationale.

mod common;

use common::{extended_float_f32, extended_float_f64};
use connections::extended::Extended;
use connections::fixed::i016::*;
use fixed::FixedI16;
use fixed::types::extra::{U0, U2, U4, U8, U12, U16};
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
                1 => Just(Extended::Finite(FixedI16::<$Frac>::from_bits(0))),
                1 => Just(Extended::Finite(FixedI16::<$Frac>::from_bits(i16::MIN))),
                1 => Just(Extended::Finite(FixedI16::<$Frac>::from_bits(i16::MAX))),
                8 => any::<i16>()
                    .prop_map(|b| Extended::Finite(FixedI16::<$Frac>::from_bits(b))),
            ],
            cases: 1024,
        }
    };
}

props_for_float_q!(laws_f032q000, F032Q000, extended_float_f32, U0);
props_for_float_q!(laws_f032q002, F032Q002, extended_float_f32, U2);
props_for_float_q!(laws_f032q004, F032Q004, extended_float_f32, U4);
props_for_float_q!(laws_f032q008, F032Q008, extended_float_f32, U8);
props_for_float_q!(laws_f032q012, F032Q012, extended_float_f32, U12);
props_for_float_q!(laws_f032q016, F032Q016, extended_float_f32, U16);

props_for_float_q!(laws_f064q000, F064Q000, extended_float_f64, U0);
props_for_float_q!(laws_f064q002, F064Q002, extended_float_f64, U2);
props_for_float_q!(laws_f064q004, F064Q004, extended_float_f64, U4);
props_for_float_q!(laws_f064q008, F064Q008, extended_float_f64, U8);
props_for_float_q!(laws_f064q012, F064Q012, extended_float_f64, U12);
props_for_float_q!(laws_f064q016, F064Q016, extended_float_f64, U16);
