//! Galois connections among
//! [`hifitime`](https://docs.rs/hifitime) types.
//!
//! Where [`crate::time`] covers civil-calendar arithmetic via the
//! `time` crate (microsecond-ish, leap-second-naive), this module
//! covers nanosecond-precision absolute time across multiple
//! relativistic / civil time scales (TAI, UTC, GPST, …) via
//! `hifitime`. The two families coexist; downstream code picks
//! whichever resolution / scale system fits the application.
//!
//! Submodules group the connections by source domain so the file
//! layout mirrors [`crate::time`]:
//!
//! - [`duration`] — `hifitime::Duration` connections
//!   ([`HDURNANO`], [`HDURSECS`], [`F064HDUR`], [`F032HDUR`]).
//!
//! Sprints 2-6 add `Epoch` projections (TAI / UTC / GNSS /
//! relativistic), the calendar enums (`MonthName`, `Weekday`),
//! and cross-crate bridges to `time` / `std::time` / `SystemTime`.
//!
//! # Naming convention
//!
//! Constants use the same **8-character** name shape as [`crate::time`]
//! — two 4-character halves drawn independently from `A123` / `AB12` /
//! `ABC1` / `ABCD`. Domain-mnemonic prefixes used by this module:
//!
//! | code   | source / target type                                       |
//! |--------|------------------------------------------------------------|
//! | `HDUR` | `hifitime::Duration` / `Extended<hifitime::Duration>`      |
//! | `NANO` | `i128` total nanoseconds (vs `time/`'s i64 — hifitime is wider) |
//! | `SECS` | `i64` whole seconds                                        |
//! | `F064` | [`F064`](crate::float::F064)                               |
//! | `F032` | [`F032`](crate::float::F032)                               |
//!
//! Sprint 2-onward will add `ETAI` / `EUTC` / `EGPS` / `EGST` /
//! `EBDT` / `EQZS` / `ETDT` / `ETDE` / `ETDB` for `hifitime::Epoch`
//! projections (1-letter `E` + 3-letter time-scale code; `ETD*` is
//! the dynamical-time family marker for TT/ET/TDB).
//!
//! # Constants
//!
//! | name          | type                                                | role |
//! |---------------|-----------------------------------------------------|------|
//! | [`HDURNANO`]  | `Conn<Extended<Duration>, i128>`                    | total nanoseconds (lossless on the in-range Finite portion) |
//! | [`HDURSECS`]  | `Conn<Extended<Duration>, i64>`                     | whole seconds; sub-second inputs round up (`floor = ceil` under `new_left`) |
//! | [`F064HDUR`]  | `Conn<F064, Extended<Duration>>`                    | f64 seconds ↔ Duration; saturating ULP walk on the 1ns Duration rung |
//! | [`F032HDUR`]  | `Conn<F032, Extended<Duration>>`                    | f32 seconds ↔ Duration; same walk shape with f32 precision |
//!
//! Each constant ships with a runnable `# Examples` doctest and
//! `proptest!` blocks driving the laws in [`crate::prop::conn`].

pub mod duration;

pub use duration::{F032HDUR, F064HDUR, HDURNANO, HDURSECS};
