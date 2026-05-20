//! # uhlc Conns
//!
//! Galois connections bridging the [`uhlc`](https://docs.rs/uhlc) crate's
//! HLC types to integer / byte endpoints. Gated on `feature = "uhlc"`.
//!
//! | Conn         | Endpoints           | Law        |
//! |--------------|---------------------|------------|
//! | `NDURU064`   | `NTP64` ↔ `u64`     | iso (full) |
//! | `HLIDLX16`   | `ID` ↔ `LX<16>`     | R-only     |
//!
//! `HLIDLX16` bridges to the opaque-bytes [`LX<16>`](crate::core::LX)
//! rather than `NonZero<u128>`: `ID`'s derived `Ord` is byte-lex
//! (LSB-first under LE storage), which is *not* the integer order on
//! the underlying `u128`. `LX<16>`'s lex-from-byte-0 `Ord` matches
//! `ID`'s. The connection is right-Galois (not iso): `LX<16>` has the
//! all-zero value that `ID` doesn't, and saturating that puncture to
//! the lex-min valid `ID` breaks the L-law but preserves the R-law.
//! See the [`id`] submodule for the derivation.

pub mod id;
pub mod ntp64;

pub use id::HLIDLX16;
pub use ntp64::NDURU064;
