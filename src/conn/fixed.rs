//! Connections over fractional number representations.
//!
//! - [`decimal`] — `i64`-backed SI-prefix ladder (`FD00`..`FD12`,
//!   base-10 scaling). Hand-rolled, independent of the upstream
//!   `fixed` crate.
//! - [`i08`] / [`i16`] / [`i32`] / [`i64`] / [`i128`] — `fixed`-crate
//!   `FixedI<width><Frac>` ladders (base-2 scaling). The submodule
//!   name encodes the inner primitive width; `Frac` levels are
//!   encoded in the Conn-constant names (`I<frac>I<frac>`, three-digit
//!   zero-padded). The `i128` module uses `checked_mul`+saturate
//!   instead of widening (no native `i256` in stable Rust).
//! - [`u08`] / [`u16`] / [`u32`] / [`u64`] / [`u128`] — same shape
//!   over `FixedU<width><Frac>`. Frac level set extends each signed
//!   counterpart with the canonical Q1.N format for the width
//!   (`U7` in u08 for MIDI velocity, `U14`/`U15` in u16, etc.).

pub mod decimal;
pub mod i08;
pub mod i128;
pub mod i16;
pub mod i32;
pub mod i64;
pub mod u08;
pub mod u128;
pub mod u16;
pub mod u32;
pub mod u64;

// The `fixed`-crate signed AND unsigned types (`FixedI{8,16,32,64,128}<F>`,
// `FixedU{8,16,32,64,128}<F>`) already derive `PartialEq` / `Eq` /
// `PartialOrd` / `Ord` upstream — totally ordered by their underlying
// integer bits — so they flow through any `T: Eq + PartialOrd` law
// predicate without per-crate impls.
