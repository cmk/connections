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
//! | [`time_walk`]          | float→Duration solver-step ≤ 44 (binary-search bracket bound) |
//! | [`time_pure`]          | TIMENANO / TIMESECS / TDURSECS / SDURU064 / SDURU128 (Plan 43) |
//! | [`hifi_walk`]          | float→hifi-Duration / TAI-Epoch solver-step ≤ 44 (binary-search bracket bound) |
//! | [`hifi_pure`]          | HDURNANO / HDURSECS / ETAINANO / ETAIHDUR (Plan 43)   |
//! | [`byte_one`]           | U008OBYT / I008OBYT / BOOLOBYT (Plan 47, `byte` feature) |
//! | [`byte_two`]           | U016OBYT / I016OBYT (Plan 47, `byte` feature) |
//! | [`byte_four`]          | U032OBYT / I032OBYT (Plan 47, `byte` feature) |
//! | [`fixed_le_one`]       | fixed::u008::U008LE01 / fixed::i008::I008LE01 / fixed::u008::BOOLLE01 |
//! | [`fixed_le_two`]       | fixed::u016::U016LE02 / fixed::i016::I016LE02 |
//! | [`fixed_le_four`]      | fixed::u032::U032LE04 / fixed::i032::I032LE04 |
//! | [`hifi_calendar`]      | MONTU008 / MONTN008 / WKDYU008 (Plan 46)              |
//!
//! [Kani]: https://model-checking.github.io/kani/

#![allow(dead_code, unused_imports)]

/// Upper bound on `solve_to_ceil` iterations for the duration / epoch
/// instantiations. The bracket is fixed at `±2⁴²` ns around the
/// starting estimate; binary search exhausts in
/// `⌈log₂(2 × 2⁴²)⌉ = 43` iterations, with `+1` slack for the
/// terminating `lo == hi` check. Shared between
/// [`time_walk`] and [`hifi_walk`] so the two harness suites can't
/// drift apart on the bound.
pub(crate) const SOLVE_STEP_BOUND: u32 = 44;

#[cfg(feature = "byte")]
mod byte_four;
#[cfg(feature = "byte")]
mod byte_one;
#[cfg(feature = "byte")]
mod byte_two;
mod ext_int;
mod fix_fix_signed;
mod fix_fix_unsigned;
mod fixed_le_four;
mod fixed_le_one;
mod fixed_le_two;
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
