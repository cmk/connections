//! Sortable byte-encoding connections.
//!
//! Each public `Conn` here is a degenerate Galois connection
//! (`floor = ceil = forward`, shipped via [`iso!`](crate::iso))
//! between a numeric host primitive and a fixed-width `[u8; N]`
//! whose **lexicographic order matches the host's numeric order**.
//! Round-trips are bit-exact in both directions.
//!
//! # Why "ordered"
//!
//! Plain big-endian `to_be_bytes` is monotone only on **unsigned**
//! integer hosts: signed-int and float hosts have a sign bit that
//! sorts the wrong way. Each Conn here pre-encodes the bit pattern
//! so byte-lex order matches numeric order:
//!
//! - **Unsigned ints**: identity bit projection then `to_be_bytes`.
//! - **Signed ints**: flip the sign bit (`x ^ MSB`) then `to_be_bytes`.
//!   `iN::MIN` → `[0; N]`, `0` → `[0x80, 0, …]`, `iN::MAX` → `[0xFF; N]`.
//! - **IEEE floats**: pre-encode via the totalOrder bit-trick
//!   (positive: flip MSB; negative: invert all bits) then
//!   `to_be_bytes`. Matches IEEE 754 totalOrder semantics, so even
//!   NaN sorts coherently.
//!
//! Same algebra the crate already uses internally for ULP walks
//! ([`signed32`](crate::float)). This module just lifts it to a
//! first-class `Conn`.
//!
//! # When to use this
//!
//! - Keying values into a sorted byte-store (RocksDB, sled,
//!   FoundationDB) where the comparator is byte-lex.
//! - Building a totalOrder over `f32` / `f64` for sort stability
//!   (NaNs included).
//! - Round-tripping a primitive through any byte-oriented
//!   serializer without losing bit-pattern fidelity.
//!
//! Submodules group Conns by host byte-width — this matches the
//! Kani-tractability tiering (1–4 byte hosts have SMT proofs;
//! 8/16-byte hosts are proptest-only).
//!
//! # Naming
//!
//! Right-side type code is `BE{NN}`: big-endian byte arrays, with `NN`
//! recording the byte width (`BE01`, `BE02`, `BE04`, `BE08`, `BE16`).
//! Left-side is the standard host code (`U008`, `I032`,
//! `F064`, `BOOL`, …). 8 chars total per the §Conn-name format
//! convention in `CLAUDE.md`.

pub mod eight;
pub mod four;
pub mod one;
pub mod sixteen;
pub mod two;

pub use eight::{I064BE08, U064BE08};
pub use four::{I032BE04, U032BE04};
pub use one::{BOOLBE01, I008BE01, U008BE01};
pub use sixteen::{I128BE16, U128BE16};
pub use two::{I016BE02, U016BE02};

// Float BE Conns (`F016BE02`, `F032BE04`, `F064BE08`) are deferred from
// this sprint — see `doc/plans/plan-2026-05-07-03.md` §Review for the
// design rationale. The byte encoding (totalOrder pre-encoding + BE
// bytes) preserves IEEE 754 totalOrder, but the host endpoint's
// `PartialOrd` returns `None` for any NaN comparison, which would make
// the emitted `iso!` claim a Galois law it does not satisfy at
// NaN-decoding byte arrays.
