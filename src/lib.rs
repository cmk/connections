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
//! Most families take a 1-letter prefix and 3 zero-padded digits;
//! the time-crate Conns use the all-letter `ABCDXYZW` shape (e.g.
//! `DURNSECS`).
//!
//! | code     | type                                                | meaning                |
//! |----------|-----------------------------------------------------|------------------------|
//! | `F016`   | `float::f16::F016` (gated)                          | IEEE binary16 (`f16` feature, nightly) |
//! | `F032`   | [`F032`](float::F032)                               | IEEE binary32          |
//! | `F064`   | [`F064`](float::F064)                               | IEEE binary64          |
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
//! For binary fixed-point, every Conn whose endpoints are Q-format
//! wrappers from the [`fixed`] crate uses the **`Q`** prefix on those
//! sides. Sign and host bit-width are implicit from the module path
//! (`fixed::i8` → signed 8-bit, `fixed::u8` → unsigned 8-bit, etc.);
//! the 3-digit field is the frac level. Backing width therefore lives
//! in the module path: `fixed::i8::Q008Q004` is the i8-backed 8-frac
//! → 4-frac Conn, while `fixed::i64::Q008Q004` is the i64-backed
//! analogue. Both share the constant name `Q008Q004`; resolution is
//! by qualified import:
//!
//! ```ignore
//! use connections::fixed::i8 as fi8;
//! use connections::fixed::i64 as fi64;
//! let _ = fi8::Q008Q000;     // i8-backed  Q0.8 → Q8.0
//! let _ = fi64::Q008Q000;    // i64-backed Q56.8 → Q64.0
//! ```
//!
//! [`fixed`]: https://docs.rs/fixed
//!
//! Std-int-conn families live alongside the Q-format ladder under
//! `fixed::{i8,…,u128}` — one submodule per destination primitive,
//! named after the **right side** of the cast. So `I008I016` (signed
//! widening `Extended<i8> → i16`) lives in `fixed::i16`; `I016I008`
//! (signed narrowing `i16 → i8`) lives in `fixed::i8`; `U008I008`
//! (cross-sign non-widening `u8 → i8`) also lives in `fixed::i8`.
//! The signed-widening (`I###I###`) and unsigned-into-signed-widening
//! (`U###I###`) families wrap the source in
//! [`Extended`](extended::Extended) (full adjoint triple). The other
//! six families ship as single-sided over plain primitives —
//! left-Galois ([`Conn::new_left`](conn::Conn::new_left)) for the
//! U→U / I→U widening + the I→I / U→U / I→U narrowing cases,
//! right-Galois ([`Conn::new_right`](conn::Conn::new_right)) for U→I
//! non-widening (where the saturation plateau lives on the target
//! side).
//!
//! Examples:
//!
//! - [`float::f32::F064F032`] — `F064 → F032` (lossy IEEE narrowing).
//! - `float::f16::F064F016` — `F064 → F016` (direct f64 → IEEE binary16, `f16` feature).
//! - `float::f16::F032F016` — `F032 → F016` (f32 → IEEE binary16, `f16` feature).
//! - [`fixed::u16::U008U016`] — `u8 → u16` saturating widen (§ Word.hs `w08w16`).
//! - [`fixed::i16::I008I016`] — `Extended<i8> → i16` (signed widening, range-extended source).
//! - [`fixed::i16::U008I016`] — `Extended<u8> → i16` (unsigned source into signed target).
//! - [`fixed::i8::I016I008`] — `i16 → i8` signed-narrowing saturating cast.
//! - [`fixed::u8::U064U008`] — `u64 → u8` unsigned-narrowing saturating cast.
//! - [`fixed::i8::U008I008`] — `u8 → i8` non-widening cross-sign (right-Galois single-sided).
//! - [`fixed::u8::I016U008`] — `i16 → u8` cross-sign narrowing (negative-clip + saturate).
//! - [`fixed::u8::Q008Q007`] — `FixedU8<U8> → FixedU8<U7>` (Q0.8 ↔ Q1.7,
//!   the 7-bit MIDI velocity format).
//! - [`fixed::u16::Q016Q015`] — `FixedU16<U16> → FixedU16<U15>` (Q0.16 ↔ Q1.15,
//!   canonical signed-PCM-equivalent unsigned audio amplitude).
//! - [`fixed::u32::Q032Q031`] — `FixedU32<U32> → FixedU32<U31>` (Q0.32 ↔ Q1.31,
//!   the canonical 32-bit normalised-amplitude format).
//! - [`fixed::i8::I008N008`] — `i8 → NonZeroI8` (asymmetric adjoint
//!   at zero: `floor(0) = -1`, `ceil(0) = +1`).
//! - [`fixed::i8::Q000I008`] — `FixedI8<U0> ↔ i8` cross-crate iso
//!   (Q8.0 lossless bridge to the std primitive).
//!
//! `F128` is blocked on `f128` stabilisation in stable Rust.
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
//!
//! // Three-step compose: id ∘ id ∘ id = id (any Conn type works).
//! const ID_I32: Conn<i32, i32> = Conn::identity();
//! const COMPOSED: Conn<i32, i32> = compose!(ID_I32, ID_I32, ID_I32);
//! ```
//!
//! Source/destination types come from the binding annotation;
//! intermediates are inferred. Runtime composition is deferred until
//! a closure-capturing `DynConn` variant lands — see `doc/design.md`.
//!
//! ## Cast operations
//!
//! Operations on a [`Conn`](conn::Conn) — accessors and lifters —
//! are free functions in [`conn`] and re-exported at the crate root
//! for ergonomic access (`connections::ceiling(&c, x)` rather than
//! `connections::conn::ceiling(&c, x)`).
//!
//! The Haskell `Data.Connection.Cast` module distinguishes L-side
//! names (`ceiling`/`upper`) from R-side names (`floor`/`lower`) via
//! a phantom `Side` data kind. This port collapses both sides onto
//! the unified [`Conn`](conn::Conn) (it always carries the full triple
//! `ceil ⊣ inner ⊣ floor`), so both naming conventions are
//! simultaneously available on every value. See [`conn`] for the
//! rationale.
//!
//! | Haskell | Rust (free fn at crate root) |
//! |---------|-------------------------------|
//! | `ceiling`/`upper` | [`ceiling`] / [`upper`] |
//! | `floor`/`lower` | [`floor`] / [`lower`] |
//! | `ceiling1`/`upper1` | [`ceiling1`] / [`upper1`] |
//! | `floor1`/`lower1` | [`floor1`] / [`lower1`] |
//! | `ceiling2`/`upper2` | [`ceiling2`] / [`upper2`] |
//! | `floor2`/`lower2` | [`floor2`] / [`lower2`] |

// `f16` is currently a nightly-only primitive (tracking #116909). Opting
// into the `f16` cargo feature enables the gated `F016` / `F032F016` /
// `F064F016` Conns and arb strategies, but requires building on nightly
// because `#![feature(f16)]` is a nightly-only attribute. Default stable
// builds skip the f16 path entirely.
#![cfg_attr(feature = "f16", feature(f16))]
#![forbid(unsafe_code)]

pub mod addr;
pub mod conn;
pub mod extended;
pub mod fixed;
pub mod float;
pub mod lattice;
pub mod time;

// Re-exports of [`conn`] free functions at the crate root for
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
pub use conn::{
    ceiling, ceiling1, ceiling2, floor, floor1, floor2, interval, lower, lower1, lower2, median,
    midpoint, round, round1, round2, truncate, truncate1, truncate2, upper, upper1, upper2,
};

// Property predicates (`prop::conn`, `prop::lattice`) and proptest
// strategies (`prop::arb`) for downstream crates that want to drive
// their own tests against this crate's algebras. The predicate
// modules are always public — they're pure `bool`-returning fns
// over this crate's types. `arb` is gated on the `testing` feature,
// which flips `proptest` from a dev-dep to an optional regular dep.
pub mod prop;
