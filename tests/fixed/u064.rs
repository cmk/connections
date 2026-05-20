//! Galois-law proptest battery for `fixed::u064`. Integration
//! test — see `tests/fixed/u008.rs` for rationale.

use connections::fixed::u064::*;
use fixed::FixedU64;
use fixed::types::extra::{U0, U8, U16, U32, U48, U63, U64};
use proptest::prelude::*;

macro_rules! props_for_pair {
    ($mod_name:ident, $conn:ident, $FineFrac:ty, $CoarseFrac:ty) => {
        connections::law_battery! {
            mod $mod_name,
            conn: $conn,
            fine:   prop_oneof![
                1 => Just(FixedU64::<$FineFrac>::from_bits(0)),
                1 => Just(FixedU64::<$FineFrac>::from_bits(1)),
                1 => Just(FixedU64::<$FineFrac>::from_bits(u64::MAX)),
                8 => any::<u64>().prop_map(FixedU64::<$FineFrac>::from_bits),
            ],
            coarse: prop_oneof![
                1 => Just(FixedU64::<$CoarseFrac>::from_bits(0)),
                1 => Just(FixedU64::<$CoarseFrac>::from_bits(1)),
                1 => Just(FixedU64::<$CoarseFrac>::from_bits(u64::MAX)),
                8 => any::<u64>().prop_map(FixedU64::<$CoarseFrac>::from_bits),
            ],
            subset: l_only,
        }
    };
}

props_for_pair!(q008q000, Q008Q000, U8, U0);
props_for_pair!(q016q000, Q016Q000, U16, U0);
props_for_pair!(q032q000, Q032Q000, U32, U0);
props_for_pair!(q048q000, Q048Q000, U48, U0);
props_for_pair!(q063q000, Q063Q000, U63, U0);
props_for_pair!(q064q000, Q064Q000, U64, U0);
props_for_pair!(q016q008, Q016Q008, U16, U8);
props_for_pair!(q032q008, Q032Q008, U32, U8);
props_for_pair!(q048q008, Q048Q008, U48, U8);
props_for_pair!(q063q008, Q063Q008, U63, U8);
props_for_pair!(q064q008, Q064Q008, U64, U8);
props_for_pair!(q032q016, Q032Q016, U32, U16);
props_for_pair!(q048q016, Q048Q016, U48, U16);
props_for_pair!(q063q016, Q063Q016, U63, U16);
props_for_pair!(q064q016, Q064Q016, U64, U16);
props_for_pair!(q048q032, Q048Q032, U48, U32);
props_for_pair!(q063q032, Q063Q032, U63, U32);
props_for_pair!(q064q032, Q064Q032, U64, U32);
props_for_pair!(q063q048, Q063Q048, U63, U48);
props_for_pair!(q064q048, Q064Q048, U64, U48);
props_for_pair!(q064q063, Q064Q063, U64, U63);
