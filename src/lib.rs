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
//! Tier codes name a *type*, not a module. All `FD<dd>FD<dd>` Conn
//! constants (pairs of decimal-rung tiers) and all `F064FD<dd>` cross-
//! tier float-into-decimal constants live in [`conn::fixed::decimal`];
//! all `S???S???` rate-pair constants and `FD12S???` cross-tier
//! constants live in [`conn::sample`].
//!
//! | code     | type                                                | resolution           |
//! |----------|-----------------------------------------------------|----------------------|
//! | `FD00`   | [`conn::fixed::decimal::FD00`]                      | 1 s                  |
//! | `FD01`   | [`conn::fixed::decimal::FD01`]                      | 100 ms               |
//! | `FD02`   | [`conn::fixed::decimal::FD02`]                      | 10 ms                |
//! | `FD03`   | [`conn::fixed::decimal::FD03`]                      | 1 ms                 |
//! | `FD06`   | [`conn::fixed::decimal::FD06`]                      | 1 µs                 |
//! | `FD09`   | [`conn::fixed::decimal::FD09`]                      | 1 ns                 |
//! | `FD12`   | [`conn::fixed::decimal::FD12`]                      | 1 ps                 |
//! | `F064`   | [`ExtendedFloat<f64>`](conn::float::ExtendedFloat)  | IEEE double          |
//! | `S044`   | [`conn::sample::S044`]                              | 1 sample @ 44.1 kHz  |
//! | `S048`   | [`conn::sample::S048`]                              | 1 sample @ 48 kHz    |
//! | `S088`   | [`conn::sample::S088`]                              | 1 sample @ 88.2 kHz  |
//! | `S096`   | [`conn::sample::S096`]                              | 1 sample @ 96 kHz    |
//! | `S176`   | [`conn::sample::S176`]                              | 1 sample @ 176.4 kHz |
//! | `S192`   | [`conn::sample::S192`]                              | 1 sample @ 192 kHz   |
//! | `U08`  | `u8`                               | unsigned 8-bit       |
//! | `U16`  | `u16`                              | unsigned 16-bit      |
//! | `U32`  | `u32`                              | unsigned 32-bit      |
//! | `U64`  | `u64`                              | unsigned 64-bit      |
//! | `I08`  | `i8`                               | signed 8-bit         |
//! | `I16`  | `i16`                              | signed 16-bit        |
//! | `I32`  | `i32`                              | signed 32-bit        |
//! | `I64`  | `i64`                              | signed 64-bit        |
//!
//! Integer codes name a Rust primitive directly (no newtype wrapper).
//! All `U??U??` and `I??U??` constants live in [`conn::uint`]; all
//! `I??I??` and `U??I??` constants live in [`conn::int`]. The signed-
//! widening (`I??I??`) and unsigned-into-signed (`U??I??`) families
//! wrap the source in [`Extended`](extended::Extended) — i.e.
//! `U08I16` is `Conn<Extended<u8>, i16>` — to give target values
//! beyond the source range a place to land. The other two integer
//! families (`U??U??`, `I??U??`) are single-sided and use plain
//! primitives on both sides.
//!
//! Examples:
//!
//! - [`conn::fixed::decimal::FD12FD06`] — `FD12 → FD06` (exact decimal-ladder embed).
//! - [`conn::fixed::decimal::F064FD06`] — `ExtendedFloat<f64> → Extended<FD06>`
//!   (lawful over the full IEEE domain, with saturation on the Rung side).
//! - [`conn::sample::FD12S048`] — `FD12 → S048` (cross-tier to sample rate).
//! - [`conn::sample::S088S044`] — `S088 → S044` (rate-pair).
//! - [`conn::uint::U08U16`] — `u8 → u16` saturating widen.
//! - [`conn::int::I08I16`] — `Extended<i8> → i16` (signed widening, range-extended source).
//! - [`conn::int::U08I16`] — `Extended<u8> → i16` (unsigned source into signed target).
//!
//! An `F032` code is not (yet) exported: an `inner` that narrows
//! `i64 → f32` collapses large runs of Rung values onto the same
//! f32, forcing an O(plateau) correction per ceil/floor call. f32
//! callers widen losslessly at the boundary:
//! `F064FD06.ceil(ExtendedFloat::Finite(arg_f32 as f64))`.
//!
//! ## Composition
//!
//! [`Conn<A, B>`](conn::Conn) stores three bare `fn` pointers so the
//! type is `Copy`, const-constructible, and heap-free — which
//! prevents a generic `.then()` method (a composed fn would need to
//! capture both inputs, which bare `fn` cannot). For the
//! compile-time-known case, the [`compose!`] macro expands a chain of
//! two or more `Conn` consts into a fresh `Conn<Src, Dst>`:
//!
//! ```rust,no_run
//! use connections::compose;
//! use connections::conn::Conn;
//! use connections::conn::fixed::decimal::{FD00, FD03FD00, FD06FD03, FD09FD06, FD12, FD12FD09};
//!
//! const FD12FD00_BIS: Conn<FD12, FD00> =
//!     compose!(FD12FD09, FD09FD06, FD06FD03, FD03FD00);
//! ```
//!
//! Source/destination types come from the binding annotation;
//! intermediates are inferred. Runtime composition is deferred until
//! a closure-capturing `DynConn` variant lands — see `doc/design.md`.

#![forbid(unsafe_code)]

pub mod conn;
pub mod extended;
pub mod lattice;

// Property predicates (`property::laws`) and proptest strategies
// (`property::arb`) for downstream crates that want to drive their
// own tests against this crate's algebras. `laws` is always public
// — its predicates are pure `bool`-returning fns over this crate's
// types. `arb` is gated on the `testing` feature, which flips
// `proptest` from a dev-dep to an optional regular dep.
pub mod property;
