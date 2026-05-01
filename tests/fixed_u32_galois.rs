//! Galois-law proptest battery for `conn::fixed::u32`. Integration
//! test — see `tests/conn_fixed_u08_galois.rs` for rationale.

use connections::fixed::u32::*;
use fixed::FixedU32;
use fixed::types::extra::{U0, U4, U8, U16, U24, U31, U32};
use proptest::prelude::*;

macro_rules! props_for_pair {
    ($mod_name:ident, $conn:ident, $FineFrac:ty, $CoarseFrac:ty) => {
        connections::law_battery! {
            mod $mod_name,
            conn: $conn,
            fine:   any::<u32>().prop_map(FixedU32::<$FineFrac>::from_bits),
            coarse: any::<u32>().prop_map(FixedU32::<$CoarseFrac>::from_bits),
            subset: l_only,
        }
    };
}

props_for_pair!(q004q000, Q004Q000, U4, U0);
props_for_pair!(q008q000, Q008Q000, U8, U0);
props_for_pair!(q016q000, Q016Q000, U16, U0);
props_for_pair!(q024q000, Q024Q000, U24, U0);
props_for_pair!(q031q000, Q031Q000, U31, U0);
props_for_pair!(q032q000, Q032Q000, U32, U0);
props_for_pair!(q008q004, Q008Q004, U8, U4);
props_for_pair!(q016q004, Q016Q004, U16, U4);
props_for_pair!(q024q004, Q024Q004, U24, U4);
props_for_pair!(q031q004, Q031Q004, U31, U4);
props_for_pair!(q032q004, Q032Q004, U32, U4);
props_for_pair!(q016q008, Q016Q008, U16, U8);
props_for_pair!(q024q008, Q024Q008, U24, U8);
props_for_pair!(q031q008, Q031Q008, U31, U8);
props_for_pair!(q032q008, Q032Q008, U32, U8);
props_for_pair!(q024q016, Q024Q016, U24, U16);
props_for_pair!(q031q016, Q031Q016, U31, U16);
props_for_pair!(q032q016, Q032Q016, U32, U16);
props_for_pair!(q031q024, Q031Q024, U31, U24);
props_for_pair!(q032q024, Q032Q024, U32, U24);
props_for_pair!(q032q031, Q032Q031, U32, U31);
