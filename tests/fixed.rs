#![cfg(feature = "fixed")]
#![cfg_attr(feature = "f16", feature(f16))]

//! Galois-law proptest batteries for `connections::fixed::*`.
//!
//! Single integration test binary aggregating Q-format ladders,
//! float→Q bridges, NonZero / cross-crate iso families. Mirrors
//! `src/fixed/`'s per-host-type layout. The previous flat layout
//! ran each `fixed_<host>_<…>_galois.rs` as its own integration
//! binary; aggregation cuts ten linker runs, and per-`mod` rustc
//! translation-unit isolation keeps peak memory under the
//! CI container budget.
//!
//! `#[path]` attributes are required because the integration-test
//! crate root resolves `mod foo;` against the parent directory
//! (`tests/`), not a stem-named subdirectory.

#[path = "fixed/helpers.rs"]
mod helpers;

#[cfg(feature = "f16")]
#[path = "fixed/helpers_f16.rs"]
mod helpers_f16;

#[path = "fixed/nz_iso.rs"]
mod nz_iso;

#[path = "fixed/i008_float_q.rs"]
mod i008_float_q;
#[path = "fixed/i016_float_q.rs"]
mod i016_float_q;
#[path = "fixed/i032_float_q.rs"]
mod i032_float_q;
#[path = "fixed/i064_float_q.rs"]
mod i064_float_q;
#[path = "fixed/i128_float_q.rs"]
mod i128_float_q;
#[path = "fixed/u008.rs"]
mod u008;
#[path = "fixed/u008_float_q.rs"]
mod u008_float_q;
#[path = "fixed/u016.rs"]
mod u016;
#[path = "fixed/u016_float_q.rs"]
mod u016_float_q;
#[path = "fixed/u032.rs"]
mod u032;
#[path = "fixed/u032_float_q.rs"]
mod u032_float_q;
#[path = "fixed/u064.rs"]
mod u064;
#[path = "fixed/u064_float_q.rs"]
mod u064_float_q;
#[path = "fixed/u128.rs"]
mod u128;
#[path = "fixed/u128_float_q.rs"]
mod u128_float_q;

#[cfg(feature = "f16")]
#[path = "fixed/i008_float_q_f16.rs"]
mod i008_float_q_f16;
#[cfg(feature = "f16")]
#[path = "fixed/i016_float_q_f16.rs"]
mod i016_float_q_f16;
#[cfg(feature = "f16")]
#[path = "fixed/i032_float_q_f16.rs"]
mod i032_float_q_f16;
#[cfg(feature = "f16")]
#[path = "fixed/i064_float_q_f16.rs"]
mod i064_float_q_f16;
#[cfg(feature = "f16")]
#[path = "fixed/i128_float_q_f16.rs"]
mod i128_float_q_f16;
#[cfg(feature = "f16")]
#[path = "fixed/u008_float_q_f16.rs"]
mod u008_float_q_f16;
#[cfg(feature = "f16")]
#[path = "fixed/u016_float_q_f16.rs"]
mod u016_float_q_f16;
#[cfg(feature = "f16")]
#[path = "fixed/u032_float_q_f16.rs"]
mod u032_float_q_f16;
#[cfg(feature = "f16")]
#[path = "fixed/u064_float_q_f16.rs"]
mod u064_float_q_f16;
#[cfg(feature = "f16")]
#[path = "fixed/u128_float_q_f16.rs"]
mod u128_float_q_f16;
