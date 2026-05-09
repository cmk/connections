//! SMT-verified Galois-connection laws via [Kani].
//!
//! This subtree mirrors the macro families in [`crate::fixed`] one
//! file per family. Each `#[kani::proof]` harness is the SMT
//! analogue of one of the proptest cases under `tests/*_galois.rs` —
//! same predicate (from [`crate::prop::conn`]), but the input is a
//! `kani::any::<_>()` symbolic value rather than a sampled
//! `proptest::any!()`. CBMC then bit-blasts the predicate over the
//! full input domain and either returns a proof or surfaces a
//! counterexample.
//!
//! ## Running
//!
//! Install once:
//!
//! ```text
//! cargo install --locked kani-verifier
//! cargo kani setup
//! ```
//!
//! Then from the crate root:
//!
//! ```text
//! cargo kani                    # all harnesses
//! cargo kani --harness <name>   # one harness
//! ```
//!
//! ## Layout
//!
//! | Module                 | Macro family                                          |
//! |------------------------|-------------------------------------------------------|
//! | [`int_narrow`]         | [`crate::int_int_narrow!`]                            |
//! | [`uint_sat`]           | [`crate::uint_int_sat!`] (single-sided R)             |
//! | [`uint_widen`]         | [`crate::uint_uint!`] + [`crate::int_uint!`]          |
//! | [`uint_narrow`]        | [`crate::uint_uint_narrow!`] + [`crate::int_uint_narrow!`] |
//! | [`ext_int`]            | [`crate::ext_int!`] (`Extended<_>` source widening)   |
//! | [`nz_ext`]             | [`crate::nz_int_ext!`] (signed) + [`crate::nz_uint_ext!`] (unsigned) |
//! | [`fix_fix_signed`]     | `fix_fix_iN!` (Q-format ladder, signed)               |
//! | [`fix_fix_unsigned`]   | `fix_fix_uN!` (Q-format ladder, unsigned)             |
//! | [`iso_family`]         | [`crate::iso!`] (lossless cross-crate iso)            |
//! | [`float_walk`]         | F064F032 ULP-walk iteration upper bound               |
//! | [`float_weaker`]       | F064F032 finite-domain weaker properties              |
//! | [`time_walk`]          | float→Duration walk-step ≤ 2 (Plan 43)                |
//! | [`time_pure`]          | TIMENANO / TIMESECS / TDURSECS / SDURU064 / SDURU128 (Plan 43) |
//! | [`hifi_walk`]          | float→hifi-Duration / TAI-Epoch walk-step ≤ 2 (Plan 43) |
//! | [`hifi_pure`]          | HDURNANO / HDURSECS / ETAINANO / ETAIHDUR (Plan 43)   |
//! | [`fixed_be_one`]       | fixed::u8::U008BE01 / fixed::i8::I008BE01 / fixed::u8::BOOLBE01 (Plan 47) |
//! | [`fixed_be_two`]       | fixed::u16::U016BE02 / fixed::i16::I016BE02 (Plan 47) |
//! | [`fixed_be_four`]      | fixed::u32::U032BE04 / fixed::i32::I032BE04 (Plan 47) |
//! | [`hifi_calendar`]      | MONTU008 / MONTN008 / WKDYU008 (Plan 46)              |
//!
//! [Kani]: https://model-checking.github.io/kani/

#![allow(dead_code, unused_imports)]

mod ext_int;
mod fix_fix_signed;
mod fix_fix_unsigned;
mod fixed_be_four;
mod fixed_be_one;
mod fixed_be_two;
mod float_walk;
mod float_weaker;
#[cfg(feature = "hifi")]
mod hifi_calendar;
#[cfg(feature = "hifi")]
mod hifi_pure;
#[cfg(feature = "hifi")]
mod hifi_walk;
mod int_narrow;
mod iso_family;
mod nz_ext;
#[cfg(feature = "time")]
mod time_pure;
#[cfg(feature = "time")]
mod time_walk;
mod uint_narrow;
mod uint_sat;
mod uint_widen;
