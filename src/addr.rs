//! Network-address connections.
//!
//! Submodules group the connections by source domain so the file
//! layout mirrors `time/`:
//!
//! - [`ip`] — IPv4 / IPv6 ↔ integer connections ([`U032IPV4`],
//!   [`U128IPV6`]).
//!
//! Every public `Conn` constant is re-exported from this module's
//! root, so callers continue to write `connections::addr::U032IPV4`
//! (the family-flat path) without having to know which sub-module
//! hosts the implementation.
//!
//! # Naming convention
//!
//! Constants in this module use the **8-character** name shape: each
//! half is one of `A123` / `AB12` / `ABC1` / `ABCD`. `IPV4` and
//! `IPV6` are 4L+0D domain-mnemonic prefixes for `std::net::Ipv4Addr`
//! and `std::net::Ipv6Addr` respectively.
//!
//! IP-address types sit on the **right** of these Conns: an
//! `Ipv4Addr` is use-wise more specific than the bare `u32` it
//! shares its bit-width with, so the natural composition flows
//! `<some numeric chain> → u32 → Ipv4Addr` (left-to-right).

pub mod ip;
pub mod socket;

pub use ip::{IPV6IPV4, IPVXIPV4, IPVXIPV6, U032IPV4, U128IPV6};
pub use socket::{SOVXSOV4, SOVXSOV6};
