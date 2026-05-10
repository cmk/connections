//! Galois-law proptest battery for `fixed::i128`'s f16 → Q-format Conns.
//!
//! Gated on `feature = "f16"` (nightly). Host bit-width 128 > f16
//! mantissa 11 → L-only.

#![cfg(feature = "f16")]
#![feature(f16)]

#[path = "common/f16.rs"]
mod common_f16;

use common_f16::extended_float_f16;
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

props_for_float_q_l!(laws_f016q000, F016Q000, extended_float_f16, U0);
props_for_float_q_l!(laws_f016q016, F016Q016, extended_float_f16, U16);
props_for_float_q_l!(laws_f016q032, F016Q032, extended_float_f16, U32);
props_for_float_q_l!(laws_f016q064, F016Q064, extended_float_f16, U64);
props_for_float_q_l!(laws_f016q096, F016Q096, extended_float_f16, U96);
props_for_float_q_l!(laws_f016q128, F016Q128, extended_float_f16, U128);
