//! Galois-law proptest battery for `fixed::u128`'s f32/f64 → Q-format Conns.

mod common;

use common::{extended_float_f32, extended_float_f64};
use connections::extended::Extended;
use connections::fixed::u128::*;
use fixed::FixedU128;
use fixed::types::extra::{
    U0 as F0, U16 as F16, U32 as F32, U64 as F64, U96 as F96, U127 as F127, U128 as F128,
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
                1 => Just(Extended::Finite(FixedU128::<$Frac>::from_bits(0))),
                1 => Just(Extended::Finite(FixedU128::<$Frac>::from_bits(u128::MAX))),
                8 => any::<u128>()
                    .prop_map(|b| Extended::Finite(FixedU128::<$Frac>::from_bits(b))),
            ],
            subset: l_only,
            cases: 1024,
        }
    };
}

props_for_float_q_l!(laws_f032q000, F032Q000, extended_float_f32, F0);
props_for_float_q_l!(laws_f032q016, F032Q016, extended_float_f32, F16);
props_for_float_q_l!(laws_f032q032, F032Q032, extended_float_f32, F32);
props_for_float_q_l!(laws_f032q064, F032Q064, extended_float_f32, F64);
props_for_float_q_l!(laws_f032q096, F032Q096, extended_float_f32, F96);
props_for_float_q_l!(laws_f032q127, F032Q127, extended_float_f32, F127);
props_for_float_q_l!(laws_f032q128, F032Q128, extended_float_f32, F128);

props_for_float_q_l!(laws_f064q000, F064Q000, extended_float_f64, F0);
props_for_float_q_l!(laws_f064q016, F064Q016, extended_float_f64, F16);
props_for_float_q_l!(laws_f064q032, F064Q032, extended_float_f64, F32);
props_for_float_q_l!(laws_f064q064, F064Q064, extended_float_f64, F64);
props_for_float_q_l!(laws_f064q096, F064Q096, extended_float_f64, F96);
props_for_float_q_l!(laws_f064q127, F064Q127, extended_float_f64, F127);
props_for_float_q_l!(laws_f064q128, F064Q128, extended_float_f64, F128);
