//! Galois-law proptest battery for `fixed::i032`'s f16 → Q-format Conns.
//!
//! Gated on `feature = "f16"` (nightly). Host bit-width 32 > f16
//! mantissa 11 → L-only.

use super::helpers_f16::extended_float_f16;
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

props_for_float_q_l!(laws_f016q000, F016Q000, extended_float_f16, U0);
props_for_float_q_l!(laws_f016q004, F016Q004, extended_float_f16, U4);
props_for_float_q_l!(laws_f016q008, F016Q008, extended_float_f16, U8);
props_for_float_q_l!(laws_f016q016, F016Q016, extended_float_f16, U16);
props_for_float_q_l!(laws_f016q024, F016Q024, extended_float_f16, U24);
props_for_float_q_l!(laws_f016q032, F016Q032, extended_float_f16, U32);
