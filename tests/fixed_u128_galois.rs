//! Galois-law proptest battery for `conn::fixed::u128`. Integration
//! test — see `tests/conn_fixed_u08_galois.rs` for rationale.
//!
//! u128 generators are expensive; case count capped to 64 (same
//! precedent as `conn::fixed::i128`).

use connections::fixed::u128::*;
use fixed::FixedU128;
use fixed::types::extra::{U0, U16, U32, U64, U96, U127, U128};
use proptest::prelude::*;

macro_rules! props_for_pair {
    ($mod_name:ident, $conn:ident, $FineFrac:ty, $CoarseFrac:ty) => {
        connections::law_battery! {
            mod $mod_name,
            conn: $conn,
            fine:   any::<u128>().prop_map(FixedU128::<$FineFrac>::from_bits),
            coarse: any::<u128>().prop_map(FixedU128::<$CoarseFrac>::from_bits),
            subset: l_only,
            cases: 64,
        }
    };
}

props_for_pair!(q016q000, Q016Q000, U16, U0);
props_for_pair!(q032q000, Q032Q000, U32, U0);
props_for_pair!(q064q000, Q064Q000, U64, U0);
props_for_pair!(q096q000, Q096Q000, U96, U0);
props_for_pair!(q127q000, Q127Q000, U127, U0);
props_for_pair!(q128q000, Q128Q000, U128, U0);
props_for_pair!(q032q016, Q032Q016, U32, U16);
props_for_pair!(q064q016, Q064Q016, U64, U16);
props_for_pair!(q096q016, Q096Q016, U96, U16);
props_for_pair!(q127q016, Q127Q016, U127, U16);
props_for_pair!(q128q016, Q128Q016, U128, U16);
props_for_pair!(q064q032, Q064Q032, U64, U32);
props_for_pair!(q096q032, Q096Q032, U96, U32);
props_for_pair!(q127q032, Q127Q032, U127, U32);
props_for_pair!(q128q032, Q128Q032, U128, U32);
props_for_pair!(q096q064, Q096Q064, U96, U64);
props_for_pair!(q127q064, Q127Q064, U127, U64);
props_for_pair!(q128q064, Q128Q064, U128, U64);
props_for_pair!(q127q096, Q127Q096, U127, U96);
props_for_pair!(q128q096, Q128Q096, U128, U96);
props_for_pair!(q128q127, Q128Q127, U128, U127);
