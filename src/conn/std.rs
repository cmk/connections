//! Connections rooted in primitive types from [`std`].
//!
//! Per the [§Module organization](crate) rule, each per-type
//! submodule hosts the Conn consts where that type wins as the
//! placement target — typically the right-hand side of the Conn,
//! or the more-general endpoint when one side is from a non-`std`
//! crate. (Conns spanning a `std` type and an external crate's type
//! live in the external crate's submodule under the
//! "specific > general" precedence.)
//!
//! - [`mod@i64`] — i64-rooted Conns; nests
//!   [`i64::decimal`], the custom decimal-SI ladder (`FD00`..`FD12`)
//!   built on i64.
//!
//! Additional per-type submodules (`i8`, `i16`, `i32`, `i128`, `u8`,
//! `u16`, `u32`, `u64`, `u128`, `f32`, `f64`) land alongside as the
//! integer-widening / cross-sign / float-narrowing Conn families
//! migrate out of the legacy `conn::int`, `conn::uint`, and
//! `conn::float` modules.

pub mod i64;
