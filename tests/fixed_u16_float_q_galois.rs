//! Galois-law proptest battery for `fixed::u016`'s f32/f64 → Q-format Conns.
//! See `tests/fixed_i8_float_q_galois.rs` for the rationale.

mod common;

use common::{extended_float_f32, extended_float_f64};
use connections::extended::Extended;
use connections::fixed::u016::*;
use fixed::FixedU16;
use fixed::types::extra::{
    U0 as F0, U2 as F2, U4 as F4, U8 as F8, U12 as F12, U14 as F14, U15 as F15, U16 as F16,
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
                1 => Just(Extended::Finite(FixedU16::<$Frac>::from_bits(0))),
                1 => Just(Extended::Finite(FixedU16::<$Frac>::from_bits(u16::MAX))),
                8 => any::<u16>()
                    .prop_map(|b| Extended::Finite(FixedU16::<$Frac>::from_bits(b))),
            ],
            cases: 1024,
        }
    };
}

props_for_float_q!(laws_f032q000, F032Q000, extended_float_f32, F0);
props_for_float_q!(laws_f032q002, F032Q002, extended_float_f32, F2);
props_for_float_q!(laws_f032q004, F032Q004, extended_float_f32, F4);
props_for_float_q!(laws_f032q008, F032Q008, extended_float_f32, F8);
props_for_float_q!(laws_f032q012, F032Q012, extended_float_f32, F12);
props_for_float_q!(laws_f032q014, F032Q014, extended_float_f32, F14);
props_for_float_q!(laws_f032q015, F032Q015, extended_float_f32, F15);
props_for_float_q!(laws_f032q016, F032Q016, extended_float_f32, F16);

props_for_float_q!(laws_f064q000, F064Q000, extended_float_f64, F0);
props_for_float_q!(laws_f064q002, F064Q002, extended_float_f64, F2);
props_for_float_q!(laws_f064q004, F064Q004, extended_float_f64, F4);
props_for_float_q!(laws_f064q008, F064Q008, extended_float_f64, F8);
props_for_float_q!(laws_f064q012, F064Q012, extended_float_f64, F12);
props_for_float_q!(laws_f064q014, F064Q014, extended_float_f64, F14);
props_for_float_q!(laws_f064q015, F064Q015, extended_float_f64, F15);
props_for_float_q!(laws_f064q016, F064Q016, extended_float_f64, F16);
