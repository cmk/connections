//! Galois connections among the [`time`](https://docs.rs/time) crate's
//! calendar / clock / duration types.
//!
//! Submodules group the connections by source domain so the file
//! layout mirrors `conn::fixed`:
//!
//! - [`date`] — calendar `Date` connections ([`DATEJDAY`]).
//! - [`clock`] — clock-time connections ([`TIMENANO`], [`TIMESECS`]).
//! - [`duration`] — signed time-span connections ([`DURNSECS`]).
//! - [`datetime`] — naive `PrimitiveDateTime` connections ([`PDTMDATE`]).
//! - [`offset`] — timezone-aware `OffsetDateTime` connections
//!   ([`OFDTNANO`], [`OFDTSECS`]). A planned `UtcOffset` conn is
//!   deferred — see the module docs for the rationale.
//!
//! Every public `Conn` constant is re-exported from this module's
//! root, so callers continue to write
//! `connections::conn::time::DURNSECS` (the family-flat path) without
//! having to know which sub-module hosts the implementation.
//!
//! # Naming convention
//!
//! Constants in this module use an **8-character** name in place of the
//! 6-character `XYYZZZ` shape used by the integer / fixed / sample
//! ladders. Each half is four characters drawn from one of:
//!
//! | half pattern | shape                                       | example |
//! |--------------|---------------------------------------------|---------|
//! | `A123`       | 1 letter + 3 digits                         | `F009`  |
//! | `AB12`       | 2 letters + 2 digits                        | `DR01`  |
//! | `ABC1`       | 3 letters + 1 digit                         | `DUR0`  |
//! | `ABCD`       | 4 letters                                   | `DATE`  |
//!
//! The two halves of a constant name need not share the same pattern.
//! All constants in this module use the all-letter `ABCDXWYZ` shape
//! because the source/target types are domain-typed (`Date`, `Time`,
//! `Duration`, `PrimitiveDateTime`) rather than tier-coded.
//!
//! # Constants
//!
//! | name | type | role |
//! |------|------|------|
//! | [`DATEJDAY`] | `Conn<Extended<Date>, i32>` | proleptic-Gregorian Julian day (exact bijection on Date range; saturating outside). |
//! | [`TIMENANO`] | `Conn<Extended<Time>, i64>` | nanoseconds since midnight (exact bijection on `[0, 86_400 × 10⁹)`). |
//! | [`TIMESECS`] | `Conn<Extended<Time>, i64>` | whole seconds since midnight; sub-second `ceil` and `floor` differ. |
//! | [`DURNSECS`] | `Conn<Duration, Extended<i64>>` | signed whole seconds; rung extended for `±i64::MAX ± 1` overflow. |
//! | [`F064DURN`] | `Conn<F064, Extended<Duration>>` | f64 seconds ↔ Duration; saturating ceil/floor walk on the 1ns Duration rung. |
//! | [`F032DURN`] | `Conn<F032, Extended<Duration>>` | f32 seconds ↔ Duration; same walk shape with f32 precision. |
//! | [`PDTMDATE`] | `Conn<PrimitiveDateTime, Extended<Date>>` | drops sub-day time; `ceil` rolls to the next day if past midnight. |
//! | [`OFDTNANO`] | `Conn<Extended<OffsetDateTime>, i128>` | unix nanoseconds since epoch (lossless across full OffsetDateTime range). |
//! | [`OFDTSECS`] | `Conn<Extended<OffsetDateTime>, i64>` | unix whole seconds since epoch; sub-second rounding. |
//!
//! Each constant ships with a runnable `# Examples` doctest and a
//! `proptest!` block driving the laws in [`crate::property::laws`].
//!
//! # Verification
//!
//! Every `Conn` constant is exercised in its sub-module's
//! `#[cfg(test)] mod tests` by the full Galois law battery from
//! [`crate::property::laws`]. The four time-crate types used here
//! (`Date`, `Time`, `Duration`, `PrimitiveDateTime`) all derive
//! `Eq + PartialOrd` upstream — total order, no NaN sentinel — so
//! the law machinery accepts them directly without any per-crate
//! trait impls.
//!
//! # Example
//!
//! Bracketing a sub-second `Duration` via [`DURNSECS`]. This block
//! is the canonical introductory example and is mirrored verbatim
//! into the README so that `cargo test --doc` enforces both stay
//! compiling.
//!
//! ```rust
//! use connections::conn::time::DURNSECS;
//! use connections::extended::Extended;
//! use time::Duration;
//!
//! let half = Duration::seconds(5) + Duration::nanoseconds(1);
//! assert_eq!(DURNSECS.ceil(half),  Extended::Finite(6));
//! assert_eq!(DURNSECS.floor(half), Extended::Finite(5));
//! assert_eq!(DURNSECS.inner(Extended::Finite(42)), Duration::seconds(42));
//! ```

pub mod clock;
pub mod date;
pub mod datetime;
pub mod duration;
pub mod offset;

pub use clock::{TIMENANO, TIMESECS};
pub use date::DATEJDAY;
pub use datetime::PDTMDATE;
pub use duration::{DURNSECS, F032DURN, F064DURN};
pub use offset::{OFDTNANO, OFDTSECS};
