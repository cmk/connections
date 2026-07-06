#![doc = include_str!("../README.md")]

//! ## Naming
//!
//! Every public `Conn` constant has an 8-character `XnnnYmmm` shape:
//! 4 chars per side (smaller-resolution / coarser tier on the right).
//! Most families take a 1-letter prefix and 3 zero-padded digits;
//! the time-crate Conns use the all-letter `ABCDXYZW` shape (e.g.
//! `TDURSECS`).
//!
//! | code     | type                         | meaning              |
//! |----------|------------------------------|----------------------|
//! | `F016`   | `float::F016` (gated)        | IEEE binary16        |
//! | `F032`   | [`F032`](float::F032)        | IEEE binary32        |
//! | `F064`   | [`F064`](float::F064)        | IEEE binary64        |
//! | `F128`   | (deferred — `f128` unstable) | IEEE binary128       |
//! | `I008`   | `i8`                         | signed 8-bit         |
//! | `I016`   | `i16`                        | signed 16-bit        |
//! | `I032`   | `i32`                        | signed 32-bit        |
//! | `I064`   | `i64`                        | signed 64-bit        |
//! | `I128`   | `i128`                       | signed 128-bit       |
//! | `U008`   | `u8`                         | unsigned 8-bit       |
//! | `U016`   | `u16`                        | unsigned 16-bit      |
//! | `U032`   | `u32`                        | unsigned 32-bit      |
//! | `U064`   | `u64`                        | unsigned 64-bit      |
//! | `U128`   | `u128`                       | unsigned 128-bit     |
//! | `SIZE`   | [`usize`](crate::core::size) | pointer-width unsigned (all-letter side) |
//!
//! For binary fixed-point, every Conn whose endpoints are Q-format
//! wrappers from the [`fixed`] crate uses the **`Q`** prefix on those
//! sides. Sign and host bit-width are implicit from the module path
//! (`fixed::i008` → signed 8-bit, `fixed::u008` → unsigned 8-bit, etc.);
//! the 3-digit field is the frac level. Backing width therefore lives
//! in the module path: `fixed::i008::Q008Q004` is the i8-backed 8-frac
//! → 4-frac Conn, while `fixed::i064::Q008Q004` is the i64-backed
//! analogue. Both share the constant name `Q008Q004`; resolution is
//! by qualified import:
//!
//! ```ignore
//! use connections::fixed::i008 as fi008;
//! use connections::fixed::i064 as fi064;
//! let _ = fi008::Q008Q000;     // i8-backed  Q0.8 → Q8.0
//! let _ = fi064::Q008Q000;    // i64-backed Q56.8 → Q64.0
//! ```
//!
//! Each `fixed::iN` / `fixed::uN` submodule also exports a per-host
//! `pub type` alias family — for example
//! `fixed::i008::I004 = FixedI8<U4>` (signed Q4.4) and
//! `fixed::u016::U008 = FixedU16<U8>` (unsigned Q8.8) — for direct use
//! of the wrapper type without a Conn. The `I`/`U` prefix marks host
//! signedness and the three digits are the frac level — a deliberately
//! distinct namespace from the Conn-name `Q###` prefix used in
//! `Q008Q004`-style identifiers. The `fixed` module docs (gated on the
//! `fixed` feature) carry the full layering rationale.
//!
//! [`fixed`]: https://docs.rs/fixed
//!
//! Std-int Conn families live under `core::{i008,…,u128}` (the
//! pure-`core`/`std` half of the crate's top-level split — see
//! [`mod@core`]). Peer numeric Conns are source-oriented:
//! `I008I016` (signed widening `Extended<i8> → i16`) lives in
//! `core::i008`; `I016I008` (signed narrowing `i16 → i8`) lives in
//! `core::i016`; `U008I008` (cross-sign non-widening `u8 → i8`) lives
//! in `core::u008`.
//! The signed-widening (`I###I###`) and unsigned-into-signed-widening
//! (`U###I###`) families wrap the source in
//! [`Extended`](extended::Extended) and ship as adjoint-triple markers
//! (unit structs implementing both [`ConnL`](conn::ConnL) and
//! [`ConnR`](conn::ConnR)). The other six families ship as
//! single-sided `Conn` consts — left-Galois
//! ([`Conn::new_l`](conn::Conn::new_l)) for the U→U / I→U widening +
//! the I→I / U→U / I→U narrowing cases, right-Galois
//! ([`Conn::new_r`](conn::Conn::new_r)) for U→I non-widening (where
//! the saturation plateau lives on the target side).
//!
//! Examples:
//!
//! - [`core::f064::F064F032`] — `F064 → F032` (lossy IEEE narrowing).
//! - `core::f064::F064F016` — `F064 → F016` (direct f64 → IEEE binary16, `f16` feature).
//! - `core::f032::F032F016` — `F032 → F016` (f32 → IEEE binary16, `f16` feature).
//! - [`core::u008::U008U016`] — `u8 → u16` saturating widen.
//! - [`core::i008::I008I016`] — `Extended<i8> → i16` (signed widening, range-extended source).
//! - [`core::u008::U008I016`] — `Extended<u8> → i16` (unsigned source into signed target).
//! - [`core::i016::I016I008`] — `i16 → i8` signed-narrowing saturating cast.
//! - [`core::u064::U064U008`] — `u64 → u8` unsigned-narrowing saturating cast.
//! - [`core::u008::U008I008`] — `u8 → i8` non-widening cross-sign (right-Galois single-sided).
//! - [`core::i016::I016U008`] — `i16 → u8` cross-sign narrowing (negative-clip + saturate).
//! - `fixed::u008::Q008Q007` — `FixedU8<U8> → FixedU8<U7>` (Q0.8 ↔ Q1.7,
//!   the 7-bit MIDI velocity format).
//! - `fixed::u016::Q016Q015` — `FixedU16<U16> → FixedU16<U15>` (Q0.16 ↔ Q1.15,
//!   canonical signed-PCM-equivalent unsigned audio amplitude).
//! - `fixed::u032::Q032Q031` — `FixedU32<U32> → FixedU32<U31>` (Q0.32 ↔ Q1.31,
//!   the canonical 32-bit normalised-amplitude format).
//! - [`core::i008::I008N008`] — `i8 → NonZeroI8` (asymmetric adjoint
//!   at zero: `floor(0) = -1`, `ceil(0) = +1`).
//! - `fixed::i008::Q000I008` — `FixedI8<U0> ↔ i8` cross-crate iso
//! - `fixed::i016::Q015I016` — signed normalized `FixedI16<U15> ↔ i16` bit iso
//!   (Q8.0 lossless bridge to the std primitive).
//!
//! `F128` is blocked on `f128` stabilisation in stable Rust.
//!
//! ---
//!
//! # Usage
//!
//! ## ConnK
//!
//! The two-sided helpers ([`ConnK`](conn::ConnK)-bound free fns,
//! re-exported via [`prelude`]) carry the following π-bracket
//! worked-example thread in their per-fn doctests:
//!
//! ```rust
//! use connections::float::ExtendedFloat::Extend;
//! use connections::core::f064::F064F032;
//!
//! let pi64 = Extend(std::f64::consts::PI);
//! // f32's nearest representation of π widened losslessly to f64.
//! let pi32 = Extend(std::f32::consts::PI as f64);
//!
//! // Lossless ≠ precise: the value is still the f32 approximation.
//! assert_ne!(pi64, pi32);
//! // upper just widens; for F064F032 that's the f32 → f64 cast.
//! assert_eq!(F064F032.swap_l().swap_r().upper(Extend(std::f32::consts::PI)), pi32);
//! ```
//!
//! - [`interval`](crate::conn::interval) — bracket of `x` as an
//!   [`Interval<A>`](crate::interval::Interval) (closed cell `[lo, hi] ⊆ A`
//!   sharing `x`'s B-projection; `Interval::Empty` for NaN-bearing
//!   inputs)
//! - [`truncate`](crate::prelude::truncate),
//!   [`truncate1`](crate::prelude::truncate1),
//!   [`truncate2`](crate::prelude::truncate2) — round-toward-zero through the triple
//! - [`round`](crate::prelude::round) — round-to-nearest f32 of true π
//!   (ties broken toward zero)
//! - [`round1`](crate::prelude::round1) — Newton step on `sin` near π
//! - [`round2`](crate::prelude::round2) — catastrophic-cancellation recovery
//! - [`median`](crate::prelude::median) — Birkhoff median (i32 ordered lattice
//!   + N5 lattice with NaN, both at the function's doctest)
//!
//! Principal-filter / principal-ideal predicates live as inherent
//! methods on the one-sided views: [`Conn::filter_l`](crate::conn::Conn::filter_l)
//! on `Conn<_, _, L>` (upward-closed: `ceil(a) ≤ b`),
//! [`Conn::filter_r`](crate::conn::Conn::filter_r) on `Conn<_, _, R>`
//! (downward-closed: `b ≤ floor(a)`).
//!
//! ## Composition
//!
//! [`Conn<A, B, K>`](conn::Conn) stores two bare `fn` pointers (`f`
//! and `g`) plus a phantom kind tag, so the type is `Copy`, const-
//! constructible, and heap-free — which prevents a generic `.then()`
//! method (a composed fn would need to capture both inputs, which bare
//! `fn` cannot). For the compile-time-known case the
//! [`compose_l!`](crate::compose_l) / [`compose_r!`](crate::compose_r)
//! macros expand a chain of two or more same-kind `Conn` consts into
//! a fresh `Conn<Src, Dst>` / `Conn<Src, Dst, R>`:
//!
//! ```rust,no_run
//! use connections::compose_l;
//! use connections::conn::Conn;
//!
//! // Three-step compose at the L-side: id ∘ id ∘ id = id.
//! const ID_I32: Conn<i32, i32> = Conn::identity();
//! const COMPOSED: Conn<i32, i32> = compose_l!(ID_I32, ID_I32, ID_I32);
//! ```
//!
//! For triple markers, [`compose_k!`](crate::compose_k) is the
//! declaration-form combiner: it generates a fresh marker unit-struct
//! whose [`ConnL`](conn::ConnL) / [`ConnR`](conn::ConnR) impls compose
//! the parents' views via `compose_l!` / `compose_r!`. The bare
//! [`compose!`](crate::compose) is a forwarder to `compose_l!`,
//! mirroring the `K = L` default of [`Conn`](crate::conn::Conn). Runtime composition is
//! deferred until a closure-capturing `DynConn` variant lands; see the
//! repository's `doc/design.md` (not shipped in the published crate).
//!
//! ## Codegen macros
//!
//! Every `Conn` const in this crate is generated by one of a small
//! number of macro families. The declaration-form macros
//! ([`conn_k!`](crate::conn_k) and its `forward = back` shorthand
//! [`iso!`](crate::iso), plus the one-sided [`conn_l!`](crate::conn_l)
//! / [`conn_r!`](crate::conn_r)) along with
//! [`compose_k!`](crate::compose_k) / [`compose_l!`](crate::compose_l)
//! / [`compose_r!`](crate::compose_r) / [`compose!`](crate::compose)
//! are unconditionally exported. The seven internal saturating-cast /
//! NonZero macro families (`uint_uint!`, `int_uint!`, `ext_int!`,
//! `*_narrow!`, `uint_int_sat!`, `nz_*_ext!`) ship under the
//! `connections::macros` module, gated on the `macros` cargo
//! feature, for downstream crates that want to extend this crate's
//! algebra to their own bounded-integer / Q-format / NonZero types.

// `f16` is currently a nightly-only primitive (tracking #116909). Opting
// into the `f16` cargo feature enables the gated `F016` / `F032F016` /
// `F064F016` Conns and arb strategies, but requires building on nightly
// because `#![feature(f16)]` is a nightly-only attribute. Default stable
// builds skip the f16 path entirely.
#![cfg_attr(feature = "f16", feature(f16))]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![forbid(unsafe_code)]

pub mod addr;
pub mod conn;
pub mod core;
pub mod extended;
#[cfg_attr(docsrs, doc(cfg(feature = "fixed")))]
#[cfg(feature = "fixed")]
pub mod fixed;
pub mod float;
#[cfg(feature = "hifi")]
pub mod hifi;
pub mod interval;
pub mod lattice;
#[cfg_attr(docsrs, doc(cfg(feature = "time")))]
#[cfg(feature = "time")]
pub mod time;
#[cfg_attr(docsrs, doc(cfg(feature = "uhlc")))]
#[cfg(feature = "uhlc")]
pub mod uhlc;

/// Idiomatic batch import of the trait family, two-sided helpers, and
/// the [`Interval`](crate::interval::Interval) bracket type.
///
/// Two-sided ops (`round`, `truncate`, `median`, `interval` and the
/// `1` / `2` lifters) are bare-named functions; routing them through
/// the prelude keeps them inside an opt-in namespace and out of the
/// crate-root glob's collision surface (`std::iter::Iterator::round`
/// once it lands, `num_traits::ToPrimitive`, etc.). One-sided ops
/// (`ceil` / `upper` / `floor` / `lower` and their `1` / `2` lifters)
/// are kind-gated inherent methods on `Conn<_, _, L>` / `Conn<_, _, R>`;
/// the capability traits re-exported here carry the polarity swaps.
///
/// # Examples
///
/// ```rust
/// use connections::prelude::*;
/// use connections::core::f064::F064F032;
/// use connections::float::ExtendedFloat::Extend;
///
/// // The two-sided helpers and capability traits arrive via the prelude.
/// let pi32 = F064F032.swap_l().swap_r().ceil(Extend(std::f64::consts::PI));
/// assert_eq!(pi32, Extend(std::f32::consts::PI));
/// ```
pub mod prelude {
    pub use crate::conn::{ConnK, ConnL, ConnR};
    pub use crate::conn::{
        interval, median, round, round1, round2, truncate, truncate1, truncate2,
    };
    pub use crate::interval::Interval;
}

// Property predicates (`prop::conn`, `prop::lattice`) and proptest
// strategies (`prop::arb`) for downstream crates that want to drive
// their own tests against this crate's algebras. The predicate
// modules are always public — they're pure `bool`-returning fns
// over this crate's types. `arb` is gated on the `testing` feature,
// which flips `proptest` from a dev-dep to an optional regular dep.
pub mod prop;

// SMT-verified Galois-connection laws via Kani. Compiled only when
// `cargo kani` sets `--cfg kani`; invisible to `cargo build`,
// `cargo test`, and downstream consumers. Each submodule mirrors
// one macro family in `src/fixed.rs` and proves the same laws that
// `tests/*_galois.rs` exercise via proptest, but for *all* inputs
// within the bit-width rather than a sampled subset.
#[cfg(all(kani, feature = "fixed"))]
mod kani;

/// Codegen macros for downstream crates building their own
/// bounded-integer / Q-format / NonZero / iso lattices on top of
/// this crate. Gated on the `macros` cargo feature.
///
/// The macros listed here are accessible at the crate root
/// (e.g. `connections::uint_uint!`) once the feature is enabled —
/// `pub use` aliases under `connections::macros::*` provide an
/// alternative curated namespace.
///
/// | macro                 | purpose                                                                       |
/// |-----------------------|-------------------------------------------------------------------------------|
/// | [`iso!`]              | degenerate-Galois bijection (lossless iso) from a `(forward, back)` pair.     |
/// | [`conn_k!`]           | full adjoint triple marker from `(ceil, inner, floor)`.                       |
/// | [`conn_l!`]           | one-sided L-Galois `Conn<A, B>` const from `(ceil, inner)`.                   |
/// | [`conn_r!`]           | one-sided R-Galois `Conn<A, B, R>` const from `(inner, floor)`.               |
/// | [`compose_k!`]        | declaration-form composition of two triple markers.                           |
/// | [`compose_l!`]        | compose a chain of L-Conn paths into a fresh `Conn<Src, Dst>`.                |
/// | [`compose_r!`]        | compose a chain of R-Conn paths into a fresh `Conn<Src, Dst, R>`.             |
/// | [`compose!`]          | forwarder to [`compose_l!`] (mirrors the `K = L` default of [`Conn`](crate::conn::Conn)).        |
/// | [`lift_l!`]           | lift a unary fn over `A` through an L-pair to its `B`-endo form.              |
/// | [`lift_r!`]           | lift a unary fn over `A` through an R-pair to its `B`-endo form.              |
/// | [`lift_k!`]           | lift a unary fn over `A` through a triple marker (both kinds at once).        |
/// | [`uint_uint!`]        | `Conn<u_N, u_M>` widening (left-Galois).                                      |
/// | [`int_uint!`]         | `Conn<i_N, u_M>` widening / same-width cross-sign (left-Galois).              |
/// | [`ext_int!`]          | `Conn<Extended<$A>, $B>` widening with Extended source (full triple).         |
/// | [`int_int_narrow!`]   | `Conn<i_N, i_M>` narrowing (left-Galois).                                     |
/// | [`uint_uint_narrow!`] | `Conn<u_N, u_M>` narrowing (left-Galois).                                     |
/// | [`uint_int_sat!`]     | `Conn<u_N, i_M>` non-widening cross-sign (right-Galois).                      |
/// | [`int_uint_narrow!`]  | `Conn<i_N, u_M>` narrowing (left-Galois).                                     |
/// | [`nz_int_ext!`]       | `Conn<i_N, NonZero<i_N>>` asymmetric-at-zero adjoint (full triple).           |
/// | [`nz_uint_ext!`]      | `Conn<u_N, NonZero<u_N>>` saturating-to-NonZero(1) (left-Galois).             |
/// | [`nz_uint_widen!`]    | `Conn<NonZero<u_N>, NonZero<u_M>>` widening saturating-at-max (left-Galois).  |
/// | [`nz_int_narrow!`]    | `Conn<NonZero<i_N>, NonZero<i_M>>` narrowing saturating-at-MIN/MAX (left-Galois). |
/// | [`nz_uint_narrow!`]   | `Conn<NonZero<u_N>, NonZero<u_M>>` narrowing saturating-at-max (left-Galois). |
/// | [`law_battery!`]      | declaration-form proptest suite for a Conn — galois / round-trip / floor_le_ceil. |
///
/// [`iso!`]: crate::iso
/// [`conn_k!`]: crate::conn_k
/// [`conn_l!`]: crate::conn_l
/// [`conn_r!`]: crate::conn_r
/// [`compose_k!`]: crate::compose_k
/// [`compose!`]: crate::compose
/// [`compose_l!`]: crate::compose_l
/// [`compose_r!`]: crate::compose_r
/// [`lift_l!`]: crate::lift_l
/// [`lift_r!`]: crate::lift_r
/// [`lift_k!`]: crate::lift_k
/// [`uint_uint!`]: crate::uint_uint
/// [`int_uint!`]: crate::int_uint
/// [`ext_int!`]: crate::ext_int
/// [`int_int_narrow!`]: crate::int_int_narrow
/// [`uint_uint_narrow!`]: crate::uint_uint_narrow
/// [`uint_int_sat!`]: crate::uint_int_sat
/// [`int_uint_narrow!`]: crate::int_uint_narrow
/// [`nz_int_ext!`]: crate::nz_int_ext
/// [`nz_uint_ext!`]: crate::nz_uint_ext
/// [`nz_uint_widen!`]: crate::nz_uint_widen
/// [`nz_int_narrow!`]: crate::nz_int_narrow
/// [`nz_uint_narrow!`]: crate::nz_uint_narrow
/// [`law_battery!`]: crate::law_battery
#[cfg(feature = "macros")]
pub mod macros {
    pub use crate::{
        compose, compose_k, compose_l, compose_r, conn_k, conn_l, conn_r, ext_int, int_int_narrow,
        int_uint, int_uint_narrow, iso, law_battery, lift_k, lift_l, lift_r, nz_int_ext,
        nz_int_narrow, nz_uint_ext, nz_uint_narrow, nz_uint_widen, uint_int_sat, uint_uint,
        uint_uint_narrow,
    };
}
