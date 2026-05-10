//! Galois-law proptest battery for `fixed::u032`'s f16 → Q-format Conns.
//!
//! Gated on `feature = "f16"` (nightly). Host bit-width 32 > f16
//! mantissa 11 → L-only.

#![cfg(feature = "f16")]
#![feature(f16)]

#[path = "common/f16.rs"]
mod common_f16;

use common_f16::extended_float_f16;
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

props_for_float_q_l!(laws_f016q000, F016Q000, extended_float_f16, F0);
props_for_float_q_l!(laws_f016q004, F016Q004, extended_float_f16, F4);
props_for_float_q_l!(laws_f016q008, F016Q008, extended_float_f16, F8);
props_for_float_q_l!(laws_f016q016, F016Q016, extended_float_f16, F16);
props_for_float_q_l!(laws_f016q024, F016Q024, extended_float_f16, F24);
props_for_float_q_l!(laws_f016q031, F016Q031, extended_float_f16, F31);
props_for_float_q_l!(laws_f016q032, F016Q032, extended_float_f16, F32);
