//! Galois-law proptest battery for `fixed::i128`'s f32/f64 → Q-format Conns.
//! Both sources are L-only (host bits 128 > both mantissa thresholds).

use super::helpers::{extended_float_f32, extended_float_f64};
use connections::extended::Extended;
use connections::fixed::i128::*;
use fixed::FixedI128;
use fixed::types::extra::{U0, U16, U32, U64, U96, U128};
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
                1 => Just(Extended::Finite(FixedI128::<$Frac>::from_bits(0))),
                1 => Just(Extended::Finite(FixedI128::<$Frac>::from_bits(i128::MIN))),
                1 => Just(Extended::Finite(FixedI128::<$Frac>::from_bits(i128::MAX))),
                8 => any::<i128>()
                    .prop_map(|b| Extended::Finite(FixedI128::<$Frac>::from_bits(b))),
            ],
            subset: l_only,
            cases: 1024,
        }
    };
}

props_for_float_q_l!(laws_f032q000, F032Q000, extended_float_f32, U0);
props_for_float_q_l!(laws_f032q016, F032Q016, extended_float_f32, U16);
props_for_float_q_l!(laws_f032q032, F032Q032, extended_float_f32, U32);
props_for_float_q_l!(laws_f032q064, F032Q064, extended_float_f32, U64);
props_for_float_q_l!(laws_f032q096, F032Q096, extended_float_f32, U96);
props_for_float_q_l!(laws_f032q128, F032Q128, extended_float_f32, U128);

props_for_float_q_l!(laws_f064q000, F064Q000, extended_float_f64, U0);
props_for_float_q_l!(laws_f064q016, F064Q016, extended_float_f64, U16);
props_for_float_q_l!(laws_f064q032, F064Q032, extended_float_f64, U32);
props_for_float_q_l!(laws_f064q064, F064Q064, extended_float_f64, U64);
props_for_float_q_l!(laws_f064q096, F064Q096, extended_float_f64, U96);
props_for_float_q_l!(laws_f064q128, F064Q128, extended_float_f64, U128);
