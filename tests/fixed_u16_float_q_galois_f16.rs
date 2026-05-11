#![cfg(feature = "fixed")]

//! Galois-law proptest battery for `fixed::u016`'s f16 → Q-format Conns.
//!
//! Gated on `feature = "f16"` (nightly). Host bit-width 16 > f16
//! mantissa 11 → L-only.

#![cfg(feature = "f16")]
#![feature(f16)]

#[path = "common/f16.rs"]
mod common_f16;

use common_f16::extended_float_f16;
use connections::extended::Extended;
use connections::fixed::u016::*;
use fixed::FixedU16;
use fixed::types::extra::{
    U0 as F0, U2 as F2, U4 as F4, U8 as F8, U12 as F12, U14 as F14, U15 as F15, U16 as F16,
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
                1 => Just(Extended::Finite(FixedU16::<$Frac>::from_bits(0))),
                1 => Just(Extended::Finite(FixedU16::<$Frac>::from_bits(u16::MAX))),
                8 => any::<u16>()
                    .prop_map(|b| Extended::Finite(FixedU16::<$Frac>::from_bits(b))),
            ],
            subset: l_only,
            cases: 1024,
        }
    };
}

props_for_float_q_l!(laws_f016q000, F016Q000, extended_float_f16, F0);
props_for_float_q_l!(laws_f016q002, F016Q002, extended_float_f16, F2);
props_for_float_q_l!(laws_f016q004, F016Q004, extended_float_f16, F4);
props_for_float_q_l!(laws_f016q008, F016Q008, extended_float_f16, F8);
props_for_float_q_l!(laws_f016q012, F016Q012, extended_float_f16, F12);
props_for_float_q_l!(laws_f016q014, F016Q014, extended_float_f16, F14);
props_for_float_q_l!(laws_f016q015, F016Q015, extended_float_f16, F15);
props_for_float_q_l!(laws_f016q016, F016Q016, extended_float_f16, F16);
