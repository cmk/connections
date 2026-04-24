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
//! live in [`fixed`]; all `S???S???` rate-pair constants and
//! `F??S???` cross-tier constants live in [`sample`].
//!
//! | code   | type                          | resolution           |
//! |--------|-------------------------------|----------------------|
//! | `F00`  | [`fixed::Uni`]                | 1 s                  |
//! | `F01`  | [`fixed::Deci`]               | 100 ms               |
//! | `F02`  | [`fixed::Centi`]              | 10 ms                |
//! | `F03`  | [`fixed::Milli`]              | 1 ms                 |
//! | `F06`  | [`fixed::Micro`]              | 1 µs                 |
//! | `F09`  | [`fixed::Nano`]               | 1 ns                 |
//! | `F12`  | [`fixed::Pico`]               | 1 ps                 |
//! | `F64`  | [`float_ext::FloatExt<f64>`]  | IEEE double          |
//! | `S44`  | [`sample::S44`]               | 1 sample @ 44.1 kHz  |
//! | `S48`  | [`sample::S48`]               | 1 sample @ 48 kHz    |
//! | `S88`  | [`sample::S88`]               | 1 sample @ 88.2 kHz  |
//! | `S96`  | [`sample::S96`]               | 1 sample @ 96 kHz    |
//! | `S176` | [`sample::S176`]              | 1 sample @ 176.4 kHz |
//! | `S192` | [`sample::S192`]              | 1 sample @ 192 kHz   |
//!
//! Examples:
//!
//! - [`fixed::F12F06`] — `Pico → Micro` (exact decimal-ladder embed).
//! - [`fixed::F64F06`] — `FloatExt<f64> → Extended<Micro>` (lawful
//!   over the full IEEE domain, with saturation on the Rung side).
//! - [`sample::F12S48`] — `Pico → S48` (cross-tier to sample rate).
//! - [`sample::S88S44`] — `S88 → S44` (rate-pair).
//!
//! An `F32` code is not (yet) exported: an `inner` that narrows
//! `i64 → f32` collapses large runs of Rung values onto the same
//! f32, forcing an O(plateau) correction per ceil/floor call. f32
//! callers widen losslessly at the boundary:
//! `F64F06.ceil(FloatExt::Finite(arg_f32 as f64))`.

#![forbid(unsafe_code)]

pub mod conn;
pub mod extended;
pub mod fixed;
pub mod float;
pub mod float_ext;
pub mod order;
pub mod sample;
