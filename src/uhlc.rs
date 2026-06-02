//! # uhlc Conns
//!
//! Galois connections bridging the [`uhlc`](https://docs.rs/uhlc) crate's
//! HLC types to integer / byte endpoints. Gated on `feature = "uhlc"`.
//!
//! | Conn         | Endpoints           | Law        |
//! |--------------|---------------------|------------|
//! | `NDURU064`   | `NTP64` ↔ `u64`     | iso (full) |
//! | `HLIDLX16`   | `Option<ID>` ↔ `LX<16>` | iso (full) |
//!
//! `HLIDLX16` bridges to the opaque-bytes [`LX<16>`](crate::core::LX)
//! rather than `NonZero<u128>`: `ID`'s derived `Ord` is byte-lex
//! (LSB-first under LE storage), which is *not* the integer order on
//! the underlying `u128`. `LX<16>`'s lex-from-byte-0 `Ord` matches
//! `ID`'s. `None` represents the all-zero byte-string puncture that no
//! `ID` can inhabit, making the connection a full iso.

pub mod id;
pub mod ntp64;

pub use id::HLIDLX16;
pub use ntp64::NDURU064;
