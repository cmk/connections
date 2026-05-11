#![cfg(feature = "fixed")]

//! Galois-law proptest battery for `fixed::u008`'s f16 → Q-format Conns.
//!
//! Gated on `feature = "f16"` (nightly). Sister to
//! `tests/fixed_u8_float_q_galois.rs`. Host bit-width 8 ≤ f16
//! mantissa 11 → full adjoint triple.

#![cfg(feature = "f16")]
#![feature(f16)]

#[path = "common/f16.rs"]
mod common_f16;

use common_f16::extended_float_f16;
use connections::extended::Extended;
use connections::fixed::u008::*;
use fixed::FixedU8;
use fixed::types::extra::{
    U0 as F0, U1 as F1, U2 as F2, U3 as F3, U4 as F4, U6 as F6, U7 as F7, U8 as F8,
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
                1 => Just(Extended::Finite(FixedU8::<$Frac>::from_bits(0))),
                1 => Just(Extended::Finite(FixedU8::<$Frac>::from_bits(u8::MAX))),
                8 => any::<u8>()
                    .prop_map(|b| Extended::Finite(FixedU8::<$Frac>::from_bits(b))),
            ],
            cases: 1024,
        }
    };
}

props_for_float_q!(laws_f016q000, F016Q000, extended_float_f16, F0);
props_for_float_q!(laws_f016q001, F016Q001, extended_float_f16, F1);
props_for_float_q!(laws_f016q002, F016Q002, extended_float_f16, F2);
props_for_float_q!(laws_f016q003, F016Q003, extended_float_f16, F3);
props_for_float_q!(laws_f016q004, F016Q004, extended_float_f16, F4);
props_for_float_q!(laws_f016q006, F016Q006, extended_float_f16, F6);
props_for_float_q!(laws_f016q007, F016Q007, extended_float_f16, F7);
props_for_float_q!(laws_f016q008, F016Q008, extended_float_f16, F8);
