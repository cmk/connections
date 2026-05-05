//! Galois connections among time-domain types, spanning both the
//! [`time`](https://docs.rs/time) crate and
//! [`std::time`](https://doc.rust-lang.org/std/time/).
//!
//! Submodules group the connections by source domain so the file
//! layout mirrors `conn::fixed`:
//!
//! - [`date`] — calendar `Date` connections ([`DATEJDAY`]).
//! - [`clock`] — clock-time connections ([`TIMENANO`], [`TIMESECS`]).
//! - [`duration`] — time-span connections, signed (`time::Duration`:
//!   [`DURNSECS`], [`F032DURN`], [`F064DURN`]) and unsigned
//!   (`std::time::Duration`: [`STDRU064`], [`STDRU128`], [`F032STDR`],
//!   [`F064STDR`]).
//! - [`datetime`] — naive `PrimitiveDateTime` connections ([`PDTMDATE`]).
//! - [`offset`] — timezone-aware `OffsetDateTime` connections
//!   ([`OFDTNANO`], [`OFDTSECS`]). A planned `UtcOffset` conn is
//!   deferred — see the module docs for the rationale.
//!
//! Every public `Conn` constant is re-exported from this module's
//! root, so callers continue to write
//! `connections::time::DURNSECS` (the family-flat path) without
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
//! Most constants in this module use the all-letter `ABCDXWYZ` shape
//! because the source/target types are domain-typed (`Date`, `Time`,
//! `Duration`, `PrimitiveDateTime`, `StdDuration`); the `STDR`/`F???`
//! cross-bridges (`STDRU064`, `STDRU128`, `F064STDR`, `F032STDR`) mix
//! the all-letter `STDR` half with the std-primitive `1L+3D` half.
//!
//! Domain-mnemonic prefixes used by this module:
//!
//! | code   | source / target type           |
//! |--------|--------------------------------|
//! | `DATE` | `Extended<time::Date>`         |
//! | `JDAY` | `i32` julian day               |
//! | `TIME` | `Extended<time::Time>`         |
//! | `NANO` | `i64` nanos since midnight     |
//! | `SECS` | `i64` whole seconds            |
//! | `DURN` | `time::Duration` / `Extended<time::Duration>` |
//! | `STDR` | `Extended<std::time::Duration>` |
//! | `PDTM` | `time::PrimitiveDateTime`      |
//! | `OFDT` | `Extended<time::OffsetDateTime>` |
//!
//! # Constants
//!
//! | name | type | role |
//! |------|------|------|
//! | [`DATEJDAY`] | `Conn<Extended<Date>, i32>` | proleptic-Gregorian Julian day (exact bijection on Date range; saturating outside). |
//! | [`TIMENANO`] | `Conn<Extended<Time>, i64>` | nanoseconds since midnight (exact bijection on `[0, 86_400 × 10⁹)`). |
//! | [`TIMESECS`] | `Conn<Extended<Time>, i64>` | whole seconds since midnight; sub-second inputs round up (`floor = ceil` under `new_left`). |
//! | [`DURNSECS`] | `Conn<Duration, Extended<i64>>` | signed whole seconds; rung extended for `±i64::MAX ± 1` overflow. |
//! | [`F064DURN`] | `Conn<F064, Extended<Duration>>` | f64 seconds ↔ Duration; saturating ceil/floor walk on the 1ns Duration rung. |
//! | [`F032DURN`] | `Conn<F032, Extended<Duration>>` | f32 seconds ↔ Duration; same walk shape with f32 precision. |
//! | [`STDRU064`] | `Conn<Extended<StdDuration>, Extended<u64>>` | unsigned whole seconds; rung PosInf at `MAX` overflow, both sides wrapped to keep `ceil(Finite(ZERO)) = Finite(0)`. |
//! | [`STDRU128`] | `Conn<Extended<StdDuration>, Extended<u128>>` | unsigned exact nanoseconds; bijection on the representable Finite range, `inner` saturates above `MAX.as_nanos()`. |
//! | [`F064STDR`] | `Conn<F064, Extended<StdDuration>>` | f64 seconds ↔ StdDuration; negative inputs project ceil → `Finite(ZERO)`, floor → `NegInf`. |
//! | [`F032STDR`] | `Conn<F032, Extended<StdDuration>>` | f32 seconds ↔ StdDuration; same walk shape with f32 precision. |
//! | [`PDTMDATE`] | `Conn<PrimitiveDateTime, Extended<Date>>` | sub-day inputs round up to the next day (`floor = ceil` under `new_left`). |
//! | [`OFDTNANO`] | `Conn<Extended<OffsetDateTime>, i128>` | unix nanoseconds since epoch (lossless across full OffsetDateTime range). |
//! | [`OFDTSECS`] | `Conn<Extended<OffsetDateTime>, i64>` | unix whole seconds since epoch; sub-second inputs round up (`floor = ceil` under `new_left`). |
//!
//! Each constant ships with a runnable `# Examples` doctest and a
//! `proptest!` block driving the laws in [`crate::prop::conn`].
//!
//! # Verification
//!
//! Every `Conn` constant is exercised in its sub-module's
//! `#[cfg(test)] mod tests` by the appropriate law battery from
//! [`crate::prop::conn`] — the left-sided battery for `new_left`
//! Conns (TIMENANO, TIMESECS, DATEJDAY, OFDTNANO, OFDTSECS, PDTMDATE)
//! and the full battery for full-triple Conns (the Duration / SystemTime
//! family). The four time-crate types used here (`Date`, `Time`,
//! `Duration`, `PrimitiveDateTime`) all derive `Eq + PartialOrd`
//! upstream — total order, no NaN sentinel — so the law machinery
//! accepts them directly without any per-crate trait impls.
//!
//! # Example
//!
//! Bracketing a sub-second `Duration` via [`DURNSECS`]. This block
//! is the canonical introductory example and is mirrored verbatim
//! into the README so that `cargo test --doc` enforces both stay
//! compiling.
//!
//! ```rust
//! use connections::conn::{ConnL, ConnR};  // brings .ceil/.inner/.floor in via default methods
//! use connections::time::DURNSECS;
//! use connections::extended::Extended;
//! use time::Duration;
//!
//! let half = Duration::seconds(5) + Duration::nanoseconds(1);
//! assert_eq!(DURNSECS.ceil(half),  Extended::Finite(6));
//! assert_eq!(DURNSECS.floor(half), Extended::Finite(5));
//! assert_eq!(DURNSECS.upper(Extended::Finite(42)), Duration::seconds(42));
//! ```
//!
//! And the unsigned counterpoint via [`STDRU064`]:
//!
//! ```rust
//! use connections::conn::{ConnL, ConnR};
//! use connections::time::STDRU064;
//! use connections::extended::Extended;
//! use std::time::Duration as StdDuration;
//!
//! let half = StdDuration::from_secs(5) + StdDuration::from_nanos(1);
//! assert_eq!(STDRU064.ceil(Extended::Finite(half)),  Extended::Finite(6));
//! assert_eq!(STDRU064.floor(Extended::Finite(half)), Extended::Finite(5));
//! ```

pub mod clock;
pub mod date;
pub mod datetime;
pub mod duration;
pub mod offset;

pub use clock::{TIMENANO, TIMESECS};
pub use date::DATEJDAY;
pub use datetime::PDTMDATE;
pub use duration::{DURNSECS, F032DURN, F032STDR, F064DURN, F064STDR, STDRU064, STDRU128};
pub use offset::{OFDTNANO, OFDTSECS};
