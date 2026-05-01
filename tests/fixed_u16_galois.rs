//! Galois-law proptest battery for `conn::fixed::u16`.
//!
//! See `tests/conn_fixed_u08_galois.rs` for the rationale: this is
//! an integration test rather than a `#[cfg(test)] mod` inside
//! `src/conn/fixed/u16.rs` to keep the lib-test rustc invocation
//! under CI's container memory budget.

use connections::fixed::u16::*;
use fixed::FixedU16;
use fixed::types::extra::{U0, U2, U4, U8, U12, U14, U15, U16};
use proptest::prelude::*;

macro_rules! props_for_pair {
    ($mod_name:ident, $conn:ident, $FineFrac:ty, $CoarseFrac:ty) => {
        connections::law_battery! {
            mod $mod_name,
            conn: $conn,
            fine:   any::<u16>().prop_map(FixedU16::<$FineFrac>::from_bits),
            coarse: any::<u16>().prop_map(FixedU16::<$CoarseFrac>::from_bits),
            subset: l_only,
        }
    };
}

props_for_pair!(q002q000, Q002Q000, U2, U0);
props_for_pair!(q004q000, Q004Q000, U4, U0);
props_for_pair!(q008q000, Q008Q000, U8, U0);
props_for_pair!(q012q000, Q012Q000, U12, U0);
props_for_pair!(q014q000, Q014Q000, U14, U0);
props_for_pair!(q015q000, Q015Q000, U15, U0);
props_for_pair!(q016q000, Q016Q000, U16, U0);
props_for_pair!(q004q002, Q004Q002, U4, U2);
props_for_pair!(q008q002, Q008Q002, U8, U2);
props_for_pair!(q012q002, Q012Q002, U12, U2);
props_for_pair!(q014q002, Q014Q002, U14, U2);
props_for_pair!(q015q002, Q015Q002, U15, U2);
props_for_pair!(q016q002, Q016Q002, U16, U2);
props_for_pair!(q008q004, Q008Q004, U8, U4);
props_for_pair!(q012q004, Q012Q004, U12, U4);
props_for_pair!(q014q004, Q014Q004, U14, U4);
props_for_pair!(q015q004, Q015Q004, U15, U4);
props_for_pair!(q016q004, Q016Q004, U16, U4);
props_for_pair!(q012q008, Q012Q008, U12, U8);
props_for_pair!(q014q008, Q014Q008, U14, U8);
props_for_pair!(q015q008, Q015Q008, U15, U8);
props_for_pair!(q016q008, Q016Q008, U16, U8);
props_for_pair!(q014q012, Q014Q012, U14, U12);
props_for_pair!(q015q012, Q015Q012, U15, U12);
props_for_pair!(q016q012, Q016Q012, U16, U12);
props_for_pair!(q015q014, Q015Q014, U15, U14);
props_for_pair!(q016q014, Q016Q014, U16, U14);
props_for_pair!(q016q015, Q016Q015, U16, U15);
