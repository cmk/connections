//! Galois-law proptest batteries for `connections::core::*`.
//!
//! Single integration test binary aggregating the per-host-type
//! batteries. Mirrors `src/core/`'s `iNNN.rs` / `uNNN.rs` layout.
//! Hosted as one binary rather than ten so `cargo test` invokes
//! ten fewer linker runs; per-module rustc memory stays bounded
//! because each `mod <name>;` translates to its own
//! object-file-level translation unit.
//!
//! `#[path]` attributes are required because the integration-test
//! crate root resolves `mod foo;` against the parent directory
//! (`tests/`), not a stem-named subdirectory.

#[path = "core/i008.rs"]
mod i008;
#[path = "core/i016.rs"]
mod i016;
#[path = "core/i032.rs"]
mod i032;
#[path = "core/i064.rs"]
mod i064;
#[path = "core/i128.rs"]
mod i128;
#[path = "core/surface.rs"]
mod surface;
#[path = "core/u008.rs"]
mod u008;
#[path = "core/u016.rs"]
mod u016;
#[path = "core/u032.rs"]
mod u032;
#[path = "core/u064.rs"]
mod u064;
#[path = "core/u128.rs"]
mod u128;
