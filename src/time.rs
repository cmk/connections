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
//!   [`TDURSECS`], [`F032TDUR`], [`F064TDUR`]) and unsigned
//!   (`std::time::Duration`: [`SDURU064`], [`SDURU128`], [`F032SDUR`],
//!   [`F064SDUR`]).
//! - [`datetime`] — naive `PrimitiveDateTime` connections ([`PDTMDATE`]).
//! - [`offset`] — timezone-aware `OffsetDateTime` connections
//!   ([`ODTMNANO`], [`ODTMSECS`]). A planned `UtcOffset` conn is
//!   deferred — see the module docs for the rationale.
//!
//! Every public `Conn` constant is re-exported from this module's
//! root, so callers continue to write
//! `connections::time::TDURSECS` (the family-flat path) without
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
//! `Duration`, `PrimitiveDateTime`, `StdDuration`); the `SDUR`/`F???`
//! cross-bridges (`SDURU064`, `SDURU128`, `F064SDUR`, `F032SDUR`) mix
//! the all-letter `SDUR` half with the std-primitive `1L+3D` half.
//!
//! Domain-mnemonic prefixes used by this module follow two
//! sub-conventions:
//!
//! - **Suffix-family (`*DUR` / `*DTM`)** — 1-letter variant + 3-letter
//!   family suffix. The `Duration` family prefixes the host crate
//!   (`T`/`S`/`H` for `time` / `std` / `hifitime`) onto the shared
//!   `DUR` suffix; the `DateTime` family prefixes the variant
//!   (`P`/`O` for `Primitive` / `Offset`) onto `DTM`.
//! - **Singleton 4-letter type tag** — `DATE`, `TIME` (no parallel
//!   variants in scope).
//!
//! | code   | source / target type           |
//! |--------|--------------------------------|
//! | `DATE` | `Extended<time::Date>`         |
//! | `JDAY` | `i32` julian day               |
//! | `TIME` | `Extended<time::Time>`         |
//! | `NANO` | `i64` nanos since midnight     |
//! | `SECS` | `i64` whole seconds            |
//! | `TDUR` | `time::Duration` / `Extended<time::Duration>` |
//! | `SDUR` | `Extended<std::time::Duration>` |
//! | `PDTM` | `time::PrimitiveDateTime`      |
//! | `ODTM` | `Extended<time::OffsetDateTime>` |
//!
//! See the `hifi` module (gated on the `hifi` feature) for the
//! parallel `HDUR` (hifitime Duration) and `E***` (Epoch scale
//! projection) families.
//!
//! # Constants
//!
//! | name | type | role |
//! |------|------|------|
//! | [`DATEJDAY`] | `Conn<Extended<Date>, i32>` | proleptic-Gregorian Julian day (exact bijection on Date range; saturating outside). |
//! | [`TIMENANO`] | `Conn<Extended<Time>, i64>` | nanoseconds since midnight (exact bijection on `[0, 86_400 × 10⁹)`). |
//! | [`TIMESECS`] | `Conn<Extended<Time>, i64>` | whole seconds since midnight; sub-second inputs round up (`floor = ceil` under `new_left`). |
//! | [`TDURSECS`] | `Conn<Duration, Extended<i64>>` | signed whole seconds; rung extended for `±i64::MAX ± 1` overflow. |
//! | [`F064TDUR`] | `Conn<F064, Extended<Duration>>` | f64 seconds ↔ Duration; saturating ceil/floor walk on the 1ns Duration rung. |
//! | [`F032TDUR`] | `Conn<F032, Extended<Duration>>` | f32 seconds ↔ Duration; same walk shape with f32 precision. |
//! | [`SDURU064`] | `Conn<Extended<StdDuration>, Extended<u64>>` | unsigned whole seconds, left-Galois; rung PosInf at `MAX` overflow, both sides wrapped to keep `ceil(Finite(ZERO)) = Finite(0)`. |
//! | [`SDURU128`] | `Conn<Extended<StdDuration>, Extended<u128>>` | unsigned exact nanoseconds; bijection on the representable Finite range, `inner` saturates above `MAX.as_nanos()`. |
//! | [`F064SDUR`] | `Conn<F064, Extended<StdDuration>>` | f64 seconds ↔ StdDuration; negative inputs project ceil → `Finite(ZERO)`, floor → `NegInf`. |
//! | [`F032SDUR`] | `Conn<F032, Extended<StdDuration>>` | f32 seconds ↔ StdDuration; same walk shape with f32 precision. |
//! | [`PDTMDATE`] | `Conn<PrimitiveDateTime, Extended<Date>>` | sub-day inputs round up to the next day (`floor = ceil` under `new_left`). |
//! | [`ODTMNANO`] | `Conn<Extended<OffsetDateTime>, i128>` | unix nanoseconds since epoch (lossless across full OffsetDateTime range). |
//! | [`ODTMSECS`] | `Conn<Extended<OffsetDateTime>, i64>` | unix whole seconds since epoch; sub-second inputs round up (`floor = ceil` under `new_left`). |
//!
//! Each constant ships with a runnable `# Examples` doctest and a
//! `proptest!` block driving the laws in [`crate::prop::conn`].
//!
//! # Verification
//!
//! Every `Conn` constant is exercised in its sub-module's
//! `#[cfg(test)] mod tests` by the appropriate law battery from
//! [`crate::prop::conn`] — the left-sided battery for `new_left`
//! Conns (TIMENANO, TIMESECS, DATEJDAY, ODTMNANO, ODTMSECS, PDTMDATE)
//! and the full battery for full-triple Conns (the Duration / SystemTime
//! family). The four time-crate types used here (`Date`, `Time`,
//! `Duration`, `PrimitiveDateTime`) all derive `Eq + PartialOrd`
//! upstream — total order, no NaN sentinel — so the law machinery
//! accepts them directly without any per-crate trait impls.
//!
//! # Example
//!
//! Bracketing a sub-second `Duration` via [`TDURSECS`]. This block
//! is the canonical introductory example and is mirrored verbatim
//! into the README so that `cargo test --doc` enforces both stay
//! compiling.
//!
//! ```rust
//! use connections::conn::{ConnL, ConnR};
//! use connections::time::TDURSECS;
//! use connections::extended::Extended;
//! use time::Duration;
//!
//! let dur = Duration::seconds(5) + Duration::nanoseconds(1);
//! assert_eq!(TDURSECS.ceil(dur),  Extended::Finite(6));   // round up
//! assert_eq!(TDURSECS.floor(dur), Extended::Finite(5));   // round down
//! assert_eq!(TDURSECS.upper(Extended::Finite(42)), Duration::seconds(42));
//! ```
//!
//! And the unsigned counterpoint via [`SDURU064`]:
//!
//! ```rust
//! use connections::time::SDURU064;
//! use connections::extended::Extended;
//! use std::time::Duration as StdDuration;
//!
//! let dur = StdDuration::from_secs(5) + StdDuration::from_nanos(1);
//! assert_eq!(SDURU064.ceil(Extended::Finite(dur)),  Extended::Finite(6));
//! ```

pub mod clock;
pub mod date;
pub mod datetime;
pub mod duration;
pub mod offset;

pub use clock::{TIMENANO, TIMESECS};
pub use date::DATEJDAY;
pub use datetime::PDTMDATE;
pub use duration::{F032SDUR, F032TDUR, F064SDUR, F064TDUR, SDURU064, SDURU128, TDURSECS};
pub use offset::{ODTMNANO, ODTMSECS};
