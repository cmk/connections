//! Rust port of [Haskell `connections`](https://github.com/cmk/connections).
//!
//! A Galois connection (adjoint triple `ceil ⊣ inner ⊣ floor`) between
//! two preordered sets, stored as three `fn` pointers. See
//! [`doc/design.md`](https://github.com/cmk/connections/blob/main/doc/design.md)
//! for the high-level design.
//!
//! ## Naming convention
//!
//! Public `Conn` constants follow Haskell's `fXYfZW` 6-character
//! shape: two tier codes separated by `f` / `s`, smaller-bit tier on
//! the left.
//!
//! Tier codes name a *type*, not a module. All `F??F??` Conn
//! constants (pairs of decimal-rung tiers, or float × decimal-rung)
//! live in [`conn::fixed`]; all `S???S???` rate-pair constants and
//! `F??S???` cross-tier constants live in [`conn::sample`].
//!
//! | code   | type                               | resolution           |
//! |--------|------------------------------------|----------------------|
//! | `F00`  | [`conn::fixed::Uni`]               | 1 s                  |
//! | `F01`  | [`conn::fixed::Deci`]              | 100 ms               |
//! | `F02`  | [`conn::fixed::Centi`]             | 10 ms                |
//! | `F03`  | [`conn::fixed::Milli`]             | 1 ms                 |
//! | `F06`  | [`conn::fixed::Micro`]             | 1 µs                 |
//! | `F09`  | [`conn::fixed::Nano`]              | 1 ns                 |
//! | `F12`  | [`conn::fixed::Pico`]              | 1 ps                 |
//! | `F64`  | [`ExtendedFloat<f64>`](conn::float::ExtendedFloat) | IEEE double          |
//! | `S44`  | [`conn::sample::S44`]              | 1 sample @ 44.1 kHz  |
//! | `S48`  | [`conn::sample::S48`]              | 1 sample @ 48 kHz    |
//! | `S88`  | [`conn::sample::S88`]              | 1 sample @ 88.2 kHz  |
//! | `S96`  | [`conn::sample::S96`]              | 1 sample @ 96 kHz    |
//! | `S176` | [`conn::sample::S176`]             | 1 sample @ 176.4 kHz |
//! | `S192` | [`conn::sample::S192`]             | 1 sample @ 192 kHz   |
//!
//! Examples:
//!
//! - [`conn::fixed::F12F06`] — `Pico → Micro` (exact decimal-ladder embed).
//! - [`conn::fixed::F64F06`] — `ExtendedFloat<f64> → Extended<Micro>` (lawful
//!   over the full IEEE domain, with saturation on the Rung side).
//! - [`conn::sample::F12S48`] — `Pico → S48` (cross-tier to sample rate).
//! - [`conn::sample::S88S44`] — `S88 → S44` (rate-pair).
//!
//! An `F32` code is not (yet) exported: an `inner` that narrows
//! `i64 → f32` collapses large runs of Rung values onto the same
//! f32, forcing an O(plateau) correction per ceil/floor call. f32
//! callers widen losslessly at the boundary:
//! `F64F06.ceil(ExtendedFloat::Finite(arg_f32 as f64))`.
//!
//! ## Composition
//!
//! [`Conn<A, B>`](conn::Conn) stores three bare `fn` pointers so the
//! type is `Copy`, const-constructible, and heap-free — which
//! prevents a generic `.then()` method (a composed fn would need to
//! capture both inputs, which bare `fn` cannot). For the
//! compile-time-known case, the [`compose_conn!`] declarative macro
//! takes two `const Conn`s and expands to a fresh `const Conn`:
//!
//! ```
//! use connections::compose_conn;
//! use connections::conn::Conn;
//! use connections::conn::fixed::{F06F00, F12F06, Pico, Uni};
//!
//! compose_conn! {
//!     pub const F12F00_VIA_MICRO: Conn<Pico, Uni> = F12F06, F06F00;
//! }
//! ```
//!
//! The intermediate type (`Micro` here) is inferred and never named.
//! Runtime composition is deferred until a closure-capturing
//! `DynConn` variant lands.

#![forbid(unsafe_code)]

pub mod conn;
pub mod extended;
pub mod lattice;

// Test-only: shared proptest strategies for the `conn::*` and
// `lattice` `#[cfg(test)]` blocks. Gated on `cfg(test)` so the
// `proptest` dev-dep doesn't leak into the public build.
#[cfg(test)]
pub(crate) mod property;
