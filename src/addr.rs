//! Network-address connections.
//!
//! Submodules group the connections by source domain so the file
//! layout mirrors `time/`:
//!
//! - [`ip`] — `std::net::{Ipv4Addr, Ipv6Addr, IpAddr}` connections:
//!   [`U032IPV4`] and [`U128IPV6`] (total bijections), [`IPV6IPV4`]
//!   (the v4-mapped bridge as a full triple), and [`IPVXIPV4`] /
//!   [`IPVXIPV6`] (one-sided sum projections extracting the V4 / V6
//!   variant from `IpAddr`).
//! - [`socket`] — `std::net::{SocketAddr, SocketAddrV4, SocketAddrV6}`
//!   connections: [`SOVXSOV4`] and [`SOVXSOV6`], the one-sided sum
//!   projections extracting V4 / V6 from `SocketAddr`.
//!
//! Every public `Conn` constant is re-exported from this module's
//! root, so callers continue to write `connections::addr::U032IPV4`
//! (the family-flat path) without having to know which sub-module
//! hosts the implementation.
//!
//! # Naming convention
//!
//! Constants in this module use the **8-character** name shape: each
//! half is one of `A123` / `AB12` / `ABC1` / `ABCD`. The 4L+0D
//! domain-mnemonic prefixes used here:
//!
//! | code | meaning                                                |
//! |------|--------------------------------------------------------|
//! | `IPV4` | `std::net::Ipv4Addr`                                 |
//! | `IPV6` | `std::net::Ipv6Addr`                                 |
//! | `IPVX` | `std::net::IpAddr` (sum of `Ipv4Addr` and `Ipv6Addr`) |
//! | `SOV4` | `std::net::SocketAddrV4`                             |
//! | `SOV6` | `std::net::SocketAddrV6`                             |
//! | `SOVX` | `std::net::SocketAddr` (sum of `SocketAddrV4` / `V6`) |
//!
//! Domain-specific types sit on the **right** of these Conns: an
//! `Ipv4Addr` is use-wise more specific than the bare `u32` it
//! shares its bit-width with, and the variant types `Ipv4Addr` /
//! `Ipv6Addr` are more specific than the sum `IpAddr` they belong
//! to. The natural composition flows `<some numeric chain> → u32 →
//! Ipv4Addr` (left-to-right) and `IpAddr → Extended<Ipv4Addr>`
//! (sum-to-variant projection).
//!
//! # One-sided vs full-triple shapes
//!
//! - **Full triples** ([`U032IPV4`], [`U128IPV6`], [`IPV6IPV4`])
//!   satisfy both Galois laws plus `floor_le_ceil`. The total
//!   bijections trivially; `IPV6IPV4` because `inner` is
//!   order-reflecting (the v4-mapped block is a strict subset of
//!   `Ipv6Addr`, giving the same "subsec room" pattern that lets
//!   `DURNSECS` survive at `Duration::MIN`).
//! - **One-sided** ([`IPVXIPV4`] / [`SOVXSOV4`] via [`Conn::new_left`];
//!   [`IPVXIPV6`] / [`SOVXSOV6`] via [`Conn::new_right`]) — the sum
//!   types' MIN/MAX coincide with `inner`'s synthetic-end values, so
//!   the full triple isn't lawful (`floor_le_ceil` would fail at the
//!   source extremes). Shipped one-sided so `floor = ceil`
//!   structurally; only the constructor's side of Galois is asserted.
//!
//! [`Conn::new_left`]: crate::conn::Conn::new_left
//! [`Conn::new_right`]: crate::conn::Conn::new_right

pub mod ip;
pub mod socket;

pub use ip::{IPV6IPV4, IPVXIPV4, IPVXIPV6, U032IPV4, U128IPV6};
pub use socket::{SOVXSOV4, SOVXSOV6};
