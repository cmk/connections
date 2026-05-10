//! Galois-law proptest battery for `fixed::i064`'s f32/f64 → Q-format Conns.
//! Both sources are L-only (host bits 64 > both mantissa thresholds).

mod common;

use common::{extended_float_f32, extended_float_f64};
use connections::extended::Extended;
use connections::fixed::i064::*;
use fixed::FixedI64;
use fixed::types::extra::{U0, U8, U16, U32, U48, U64};
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
                1 => Just(Extended::Finite(FixedI64::<$Frac>::from_bits(0))),
                1 => Just(Extended::Finite(FixedI64::<$Frac>::from_bits(i64::MIN))),
                1 => Just(Extended::Finite(FixedI64::<$Frac>::from_bits(i64::MAX))),
                8 => any::<i64>()
                    .prop_map(|b| Extended::Finite(FixedI64::<$Frac>::from_bits(b))),
            ],
            subset: l_only,
        }
    };
}

props_for_float_q_l!(laws_f032q000, F032Q000, extended_float_f32, U0);
props_for_float_q_l!(laws_f032q008, F032Q008, extended_float_f32, U8);
props_for_float_q_l!(laws_f032q016, F032Q016, extended_float_f32, U16);
props_for_float_q_l!(laws_f032q032, F032Q032, extended_float_f32, U32);
props_for_float_q_l!(laws_f032q048, F032Q048, extended_float_f32, U48);
props_for_float_q_l!(laws_f032q064, F032Q064, extended_float_f32, U64);

props_for_float_q_l!(laws_f064q000, F064Q000, extended_float_f64, U0);
props_for_float_q_l!(laws_f064q008, F064Q008, extended_float_f64, U8);
props_for_float_q_l!(laws_f064q016, F064Q016, extended_float_f64, U16);
props_for_float_q_l!(laws_f064q032, F064Q032, extended_float_f64, U32);
props_for_float_q_l!(laws_f064q048, F064Q048, extended_float_f64, U48);
props_for_float_q_l!(laws_f064q064, F064Q064, extended_float_f64, U64);
