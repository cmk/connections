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
//! - [`epoch`] — `hifitime::Epoch` projections in two scale-families
//!   (Sprint 2): TAI ([`ETAIHDUR`], [`ETAINANO`], [`ETAIF064`]) and
//!   UTC ([`EUTCHDUR`], [`EUTCNANO`], [`EUTCF064`]).
//!
//! Sprints 3-6 add the GNSS scales (GPST/GST/BDT/QZSST), the
//! relativistic scales (TT/ET/TDB), the calendar enums
//! (`MonthName`, `Weekday`), and cross-crate bridges to `time` /
//! `std::time` / `SystemTime`.
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
//! | `ETAI` | `hifitime::Epoch` projected in **TAI** scale (J1900 reference) |
//! | `EUTC` | `hifitime::Epoch` projected in **UTC** scale (UNIX reference) |
//! | `NANO` | `i128` total nanoseconds (vs `time/`'s i64 — hifitime is wider) |
//! | `SECS` | `i64` whole seconds                                        |
//! | `F064` | [`F064`](crate::float::F064)                               |
//! | `F032` | [`F032`](crate::float::F032)                               |
//!
//! Sprints 3-onward will add `EGPS` / `EGST` / `EBDT` / `EQZS` /
//! `ETDT` / `ETDE` / `ETDB` for the remaining `hifitime::Epoch`
//! scale projections (1-letter `E` + 3-letter time-scale code;
//! `ETD*` is the dynamical-time family marker for TT/ET/TDB).
//!
//! ## Reference epochs (per scale family)
//!
//! Each `E{xx}*` family has an implicit reference epoch baked into
//! the projection. Document this in any new Conn that joins:
//!
//! - **`ETAI*`** → **J1900 TAI** (hifitime's storage-native zero).
//! - **`EUTC*`** has a **mixed reference**: [`EUTCHDUR`] uses
//!   **J1900 UTC** (UNIX-anchoring would push the iso's round-trip
//!   boundary outside `HD`'s range — see the `EUTCHDUR` doc for the
//!   derivation), while [`EUTCNANO`] and [`EUTCF064`] use
//!   **UNIX EPOCH UTC** (1970-01-01 00:00:00 UTC) so numerical
//!   values match [`OFDTNANO`](crate::time::OFDTNANO)'s convention
//!   for callers bridging `time::OffsetDateTime` ↔
//!   `hifitime::Epoch`.
//!
//! # Constants
//!
//! | name          | type                                                | role |
//! |---------------|-----------------------------------------------------|------|
//! | [`HDURNANO`]  | `Conn<Extended<Duration>, i128>`                    | total nanoseconds (lossless on the in-range Finite portion) |
//! | [`HDURSECS`]  | `Conn<Extended<Duration>, i64>`                     | whole seconds; sub-second inputs round up (`floor = ceil` under `new_left`) |
//! | [`F064HDUR`]  | `Conn<F064, Extended<Duration>>`                    | f64 seconds ↔ Duration; saturating ULP walk on the 1ns Duration rung |
//! | [`F032HDUR`]  | `Conn<F032, Extended<Duration>>`                    | f32 seconds ↔ Duration; same walk shape with f32 precision |
//! | [`ETAIHDUR`]  | `Conn<Epoch, Duration>`                             | Epoch ↔ TAI Duration since J1900 (degenerate iso) |
//! | [`ETAINANO`]  | `Conn<Extended<Epoch>, i128>`                       | TAI nanoseconds since J1900 |
//! | [`ETAIF064`]  | `Conn<F064, Extended<Epoch>>`                       | f64 TAI seconds since J1900 ↔ Epoch (ULP walks on TAI Duration) |
//! | [`EUTCHDUR`]  | `Conn<Epoch, Duration>`                             | Epoch ↔ UTC Duration since **J1900 UTC** (leap-second-aware iso; UNIX-anchored variants live in [`EUTCNANO`] / [`EUTCF064`] below) |
//! | [`EUTCNANO`]  | `Conn<Extended<Epoch>, i128>`                       | UNIX nanoseconds (matches [`OFDTNANO`](crate::time::OFDTNANO)) |
//! | [`EUTCF064`]  | `Conn<F064, Extended<Epoch>>`                       | f64 UNIX seconds ↔ Epoch (ULP walks on TAI Duration) |
//!
//! Each constant ships with a runnable `# Examples` doctest and
//! `proptest!` blocks driving the laws in [`crate::prop::conn`].

pub mod duration;
pub mod epoch;

pub use duration::{F032HDUR, F064HDUR, HDURNANO, HDURSECS};
pub use epoch::{ETAIF064, ETAIHDUR, ETAINANO, EUTCF064, EUTCHDUR, EUTCNANO};
