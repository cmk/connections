//! Galois-law proptest battery for `fixed::i008`'s f32/f64 → Q-format Conns.
//!
//! Hosted as an integration test (separate crate) so the main lib
//! test binary doesn't carry these — combined with the existing
//! Q→Q ladder, the lib-test rustc invocation OOMs on CI's container
//! memory budget. Each `tests/fixed_<host>_float_q_galois.rs` is a
//! standalone rustc invocation, peak memory per compile stays
//! within budget.
//!
//! Host bit-width 8 ≤ both f32 and f64 mantissas, so every Conn is
//! a full adjoint triple.

use super::helpers::{extended_float_f32, extended_float_f64};
use connections::extended::Extended;
use connections::fixed::i008::*;
use fixed::FixedI8;
use fixed::types::extra::{U0, U1, U2, U3, U4, U6, U8};
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
                1 => Just(Extended::Finite(FixedI8::<$Frac>::from_bits(0))),
                1 => Just(Extended::Finite(FixedI8::<$Frac>::from_bits(i8::MIN))),
                1 => Just(Extended::Finite(FixedI8::<$Frac>::from_bits(i8::MAX))),
                8 => any::<i8>()
                    .prop_map(|b| Extended::Finite(FixedI8::<$Frac>::from_bits(b))),
            ],
            cases: 1024,
        }
    };
}

props_for_float_q!(laws_f032q000, F032Q000, extended_float_f32, U0);
props_for_float_q!(laws_f032q001, F032Q001, extended_float_f32, U1);
props_for_float_q!(laws_f032q002, F032Q002, extended_float_f32, U2);
props_for_float_q!(laws_f032q003, F032Q003, extended_float_f32, U3);
props_for_float_q!(laws_f032q004, F032Q004, extended_float_f32, U4);
props_for_float_q!(laws_f032q006, F032Q006, extended_float_f32, U6);
props_for_float_q!(laws_f032q008, F032Q008, extended_float_f32, U8);

props_for_float_q!(laws_f064q000, F064Q000, extended_float_f64, U0);
props_for_float_q!(laws_f064q001, F064Q001, extended_float_f64, U1);
props_for_float_q!(laws_f064q002, F064Q002, extended_float_f64, U2);
props_for_float_q!(laws_f064q003, F064Q003, extended_float_f64, U3);
props_for_float_q!(laws_f064q004, F064Q004, extended_float_f64, U4);
props_for_float_q!(laws_f064q006, F064Q006, extended_float_f64, U6);
props_for_float_q!(laws_f064q008, F064Q008, extended_float_f64, U8);
