//! Connections over fractional number representations.
//!
//! - [`decimal`] — `i64`-backed SI-prefix ladder (Uni..Pico, base-10
//!   scaling). Hand-rolled, independent of the upstream `fixed` crate.
//!
//! Future sub-modules will host `fixed`-crate-native binary ladders
//! (`FixedI*<Frac>`, base-2 scaling). Reserving the `fixed` parent
//! name now keeps the `fixed::decimal` path stable when those land.

pub mod decimal;
