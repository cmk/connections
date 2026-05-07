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
//! Right-side type code is `OBYT` (4L+0D ABCD shape — "Ordered
//! BYTes"). Left-side is the standard host code (`U008`, `I032`,
//! `F064`, `BOOL`, …). 8 chars total per the §Conn-name format
//! convention in `CLAUDE.md`.

pub mod eight;
pub mod four;
pub mod one;
pub mod sixteen;
pub mod two;

pub use eight::{F064OBYT, I064OBYT, U064OBYT};
pub use four::{F032OBYT, I032OBYT, U032OBYT};
pub use one::{BOOLOBYT, I008OBYT, U008OBYT};
pub use sixteen::{I128OBYT, U128OBYT};
pub use two::{I016OBYT, U016OBYT};

#[cfg(feature = "f16")]
pub use two::F016OBYT;
