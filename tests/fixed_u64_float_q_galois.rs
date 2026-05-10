//! Galois-law proptest battery for `fixed::u064`'s f32/f64 → Q-format Conns.

mod common;

use common::{extended_float_f32, extended_float_f64};
use connections::extended::Extended;
use connections::fixed::u064::*;
use fixed::FixedU64;
use fixed::types::extra::{
    U0 as F0, U8 as F8, U16 as F16, U32 as F32, U48 as F48, U63 as F63, U64 as F64,
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
                1 => Just(Extended::Finite(FixedU64::<$Frac>::from_bits(0))),
                1 => Just(Extended::Finite(FixedU64::<$Frac>::from_bits(u64::MAX))),
                8 => any::<u64>()
                    .prop_map(|b| Extended::Finite(FixedU64::<$Frac>::from_bits(b))),
            ],
            subset: l_only,
            cases: 1024,
        }
    };
}

props_for_float_q_l!(laws_f032q000, F032Q000, extended_float_f32, F0);
props_for_float_q_l!(laws_f032q008, F032Q008, extended_float_f32, F8);
props_for_float_q_l!(laws_f032q016, F032Q016, extended_float_f32, F16);
props_for_float_q_l!(laws_f032q032, F032Q032, extended_float_f32, F32);
props_for_float_q_l!(laws_f032q048, F032Q048, extended_float_f32, F48);
props_for_float_q_l!(laws_f032q063, F032Q063, extended_float_f32, F63);
props_for_float_q_l!(laws_f032q064, F032Q064, extended_float_f32, F64);

props_for_float_q_l!(laws_f064q000, F064Q000, extended_float_f64, F0);
props_for_float_q_l!(laws_f064q008, F064Q008, extended_float_f64, F8);
props_for_float_q_l!(laws_f064q016, F064Q016, extended_float_f64, F16);
props_for_float_q_l!(laws_f064q032, F064Q032, extended_float_f64, F32);
props_for_float_q_l!(laws_f064q048, F064Q048, extended_float_f64, F48);
props_for_float_q_l!(laws_f064q063, F064Q063, extended_float_f64, F63);
props_for_float_q_l!(laws_f064q064, F064Q064, extended_float_f64, F64);
