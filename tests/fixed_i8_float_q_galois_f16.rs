#![cfg(feature = "fixed")]

//! Galois-law proptest battery for `fixed::i008`'s f16 → Q-format Conns.
//!
//! Gated on `feature = "f16"` (nightly). Sister to
//! `tests/fixed_i8_float_q_galois.rs` — same shape, f16 source.
//! Host bit-width 8 ≤ f16 mantissa 11, so every Conn is a full
//! adjoint triple.

#![cfg(feature = "f16")]
#![feature(f16)]

#[path = "common/f16.rs"]
mod common_f16;

use common_f16::extended_float_f16;
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

props_for_float_q!(laws_f016q000, F016Q000, extended_float_f16, U0);
props_for_float_q!(laws_f016q001, F016Q001, extended_float_f16, U1);
props_for_float_q!(laws_f016q002, F016Q002, extended_float_f16, U2);
props_for_float_q!(laws_f016q003, F016Q003, extended_float_f16, U3);
props_for_float_q!(laws_f016q004, F016Q004, extended_float_f16, U4);
props_for_float_q!(laws_f016q006, F016Q006, extended_float_f16, U6);
props_for_float_q!(laws_f016q008, F016Q008, extended_float_f16, U8);
