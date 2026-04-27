#![doc = include_str!("../README.md")]
//!
//! ---
//!
//! ## Internal docs (additional context for code readers)
//!
//! Rust port of [Haskell `connections`](https://github.com/cmk/connections).
//!
//! A Galois connection (adjoint triple `ceil ⊣ inner ⊣ floor`) between
//! two preordered sets, stored as three `fn` pointers. See
//! [`doc/design.md`](https://github.com/cmk/connections/blob/main/doc/design.md)
//! for the high-level design.
//!
//! ## Naming convention
//!
//! Every public `Conn` constant has an 8-character `XnnnYmmm` shape:
//! 4 chars per side (smaller-resolution / coarser tier on the right).
//! One family takes a 2-letter prefix (decimal-fixed `FD<dd>`); every
//! other family takes a 1-letter prefix and 3 zero-padded digits.
//!
//! | code     | type                                                | meaning                |
//! |----------|-----------------------------------------------------|------------------------|
//! | `FD00`   | [`conn::std::i64::decimal::FD00`]                      | 10⁰ s   (1 s)          |
//! | `FD01`   | [`conn::std::i64::decimal::FD01`]                      | 10⁻¹ s  (100 ms)       |
//! | `FD02`   | [`conn::std::i64::decimal::FD02`]                      | 10⁻² s  (10 ms)        |
//! | `FD03`   | [`conn::std::i64::decimal::FD03`]                      | 10⁻³ s  (1 ms)         |
//! | `FD06`   | [`conn::std::i64::decimal::FD06`]                      | 10⁻⁶ s  (1 µs)         |
//! | `FD09`   | [`conn::std::i64::decimal::FD09`]                      | 10⁻⁹ s  (1 ns)         |
//! | `FD12`   | [`conn::std::i64::decimal::FD12`]                      | 10⁻¹² s (1 ps)         |
//! | `F016`   | [`F016`](conn::float::F016)                         | IEEE binary16 (sw via `half`) |
//! | `B016`   | [`B016`](conn::float::B016)                         | Google bfloat16 (sw via `half`) |
//! | `F032`   | [`F032`](conn::float::F032)                         | IEEE binary32          |
//! | `F064`   | [`F064`](conn::float::F064)                         | IEEE binary64          |
//! | `F128`   | (deferred — `f128` unstable)                        | IEEE binary128         |
//! | `I008`   | `i8`                                                | signed 8-bit           |
//! | `I016`   | `i16`                                               | signed 16-bit          |
//! | `I032`   | `i32`                                               | signed 32-bit          |
//! | `I064`   | `i64`                                               | signed 64-bit          |
//! | `I128`   | `i128`                                              | signed 128-bit         |
//! | `U008`   | `u8`                                                | unsigned 8-bit         |
//! | `U016`   | `u16`                                               | unsigned 16-bit        |
//! | `U032`   | `u32`                                               | unsigned 32-bit        |
//! | `U064`   | `u64`                                               | unsigned 64-bit        |
//! | `U128`   | `u128`                                              | unsigned 128-bit       |
//!
//! For binary fixed-point, the family letter encodes the **sign** of
//! the underlying primitive — `I###` for `FixedI<width><U<frac>>` (signed)
//! and `U###` for `FixedU<width><U<frac>>` (unsigned). The 3-digit
//! field is the frac level. Backing width lives in the module path:
//! `conn::fixed::i8::I008I004` is the i8-backed 8-frac → 4-frac Conn,
//! while `conn::fixed::i64::I008I004` is the i64-backed analogue. Both
//! share the constant name `I008I004`; resolution is by qualified
//! import:
//!
//! ```ignore
//! use connections::conn::fixed::i8 as fi8;
//! use connections::conn::fixed::i64 as fi64;
//! let _ = fi8::I008I000;     // i8-backed  Q0.8 → Q8.0
//! let _ = fi64::I008I000;    // i64-backed Q56.8 → Q64.0
//! ```
//!
//! Integer-conn families (`conn::int`, `conn::uint`) name primitives
//! directly: `I008I016` is `Conn<Extended<i8>, i16>`. The signed-
//! widening (`I###I###`) and unsigned-into-signed (`U###I###`) families
//! in `conn::int` wrap the source in [`Extended`](extended::Extended)
//! to give target values beyond the source range a place to land. The
//! `conn::uint` families (`U###U###`, `I###U###`) are single-sided and
//! use plain primitives on both sides.
//!
//! Examples:
//!
//! - [`conn::std::i64::decimal::FD12FD06`] — `FD12 → FD06` (exact decimal-ladder embed).
//! - [`conn::std::i64::decimal::F064FD06`] — `ExtendedFloat<f64> → Extended<FD06>`
//!   (lawful over the full IEEE domain, with saturation on the Rung side).
//! - [`conn::float::f64::F064F032`] — `F064 → F032` (lossy IEEE narrowing).
//! - [`conn::float::f64::F064F016`] — `F064 → F016` (direct f64 → IEEE binary16).
//! - [`conn::float::f64::F064B016`] — `F064 → B016` (direct f64 → bfloat16).
//! - [`conn::float::f32::F032F016`] — `F032 → F016` (f32 → IEEE binary16).
//! - [`conn::float::f32::F032B016`] — `F032 → B016` (f32 → bfloat16).
//! - [`conn::uint::U008U016`] — `u8 → u16` saturating widen.
//! - [`conn::int::I008I016`] — `Extended<i8> → i16` (signed widening, range-extended source).
//! - [`conn::int::U008I016`] — `Extended<u8> → i16` (unsigned source into signed target).
//! - [`conn::fixed::u8::U008U007`] — `FixedU8<U8> → FixedU8<U7>` (Q0.8 ↔ Q1.7,
//!   the 7-bit MIDI velocity format).
//! - [`conn::fixed::u16::U016U015`] — `FixedU16<U16> → FixedU16<U15>` (Q0.16 ↔ Q1.15,
//!   canonical signed-PCM-equivalent unsigned audio amplitude).
//! - [`conn::fixed::u32::U032U031`] — `FixedU32<U32> → FixedU32<U31>` (Q0.32 ↔ Q1.31,
//!   the canonical 32-bit normalised-amplitude format).
//!
//! An `F032`-into-decimal cross-tier (e.g. `F032FD06`) is not yet
//! exported: an `inner` that narrows `i64 → f32` collapses large
//! runs of Rung values onto the same f32, forcing an O(plateau)
//! correction per ceil/floor call. f32 callers widen losslessly at
//! the boundary:
//! `F064FD06.ceil(ExtendedFloat::Extend(arg_f32 as f64))`. `F128` is
//! blocked on `f128` stabilisation in stable Rust.
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
//! use connections::conn::std::i64::decimal::{FD00, FD03FD00, FD06FD03, FD09FD06, FD12, FD12FD09};
//!
//! const FD12FD00_BIS: Conn<FD12, FD00> =
//!     compose!(FD12FD09, FD09FD06, FD06FD03, FD03FD00);
//! ```
//!
//! Source/destination types come from the binding annotation;
//! intermediates are inferred. Runtime composition is deferred until
//! a closure-capturing `DynConn` variant lands — see `doc/design.md`.
//!
//! ## Cast operations
//!
//! Operations on a [`Conn`](conn::Conn) — accessors, lifters, and the
//! curried [`maximize`] / [`minimize`] helpers — live in
//! [`conn::cast`] and are re-exported at the crate root for ergonomic
//! access (`connections::ceiling(&c, x)` rather than
//! `connections::conn::cast::ceiling(&c, x)`).
//!
//! The Haskell `Data.Connection.Cast` module distinguishes
//! L-side names (`ceiling`/`upper`/`maximize`) from R-side names
//! (`floor`/`lower`/`minimize`) via a phantom `Side` data kind. This
//! port collapses both sides onto the unified [`Conn`](conn::Conn) (it
//! always carries the full triple `ceil ⊣ inner ⊣ floor`), so both
//! naming conventions are simultaneously available on every value.
//! See [`conn::cast`] for the rationale.
//!
//! | Haskell | Rust (free fn at crate root) |
//! |---------|-------------------------------|
//! | `ceiling`/`upper` | [`ceiling`] / [`upper`] |
//! | `floor`/`lower` | [`floor`] / [`lower`] |
//! | `ceiling1`/`upper1` | [`ceiling1`] / [`upper1`] |
//! | `floor1`/`lower1` | [`floor1`] / [`lower1`] |
//! | `ceiling2`/`upper2` | [`ceiling2`] / [`upper2`] |
//! | `floor2`/`lower2` | [`floor2`] / [`lower2`] |
//! | `maximize` | [`maximize`] |
//! | `minimize` | [`minimize`] |

#![forbid(unsafe_code)]

pub mod conn;
pub mod extended;
pub mod lattice;

// Re-exports of [`conn::cast`] free functions at the crate root for
// ergonomic access (`connections::ceiling(&c, x)` rather than the
// module path).
//
// Note on glob-imports: `floor` / `ceiling` are the bare function
// names from category theory, not the `f32::floor` / `f64::ceil`
// methods. If you `use connections::*` alongside another crate's
// glob (e.g. `use libm::*`, `use num_traits::*`), the names may
// collide. Resolution is by type — these take `&Conn<A, B>` as their
// first argument, so a wrong `floor` will produce a type error
// rather than silent misbehavior — but prefer named imports
// (`use connections::{ceiling, floor};`) over globs to make the
// origin explicit.
pub use conn::cast::{
    ceiling, ceiling1, ceiling2, floor, floor1, floor2, lower, lower1, lower2, maximize, minimize,
    upper, upper1, upper2,
};

// Property predicates (`property::laws`) and proptest strategies
// (`property::arb`) for downstream crates that want to drive their
// own tests against this crate's algebras. `laws` is always public
// — its predicates are pure `bool`-returning fns over this crate's
// types. `arb` is gated on the `testing` feature, which flips
// `proptest` from a dev-dep to an optional regular dep.
pub mod property;
