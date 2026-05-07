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
//! - [`epoch`] — `hifitime::Epoch` projections across six scale-
//!   families: TAI ([`ETAIHDUR`], [`ETAINANO`], [`ETAIF064`]),
//!   UTC ([`EUTCHDUR`], [`EUTCNANO`], [`EUTCF064`]),
//!   GPST ([`EGPSHDUR`], [`EGPSNANO`], [`EGPSF064`]),
//!   QZSST ([`EQZSHDUR`], [`EQZSNANO`], [`EQZSF064`]),
//!   GST ([`EGSTHDUR`], [`EGSTNANO`], [`EGSTF064`]),
//!   BDT ([`EBDTHDUR`], [`EBDTNANO`], [`EBDTF064`]).
//!
//! Sprints 4-6 add the relativistic scales (TT/ET/TDB), the calendar
//! enums (`MonthName`, `Weekday`), and cross-crate bridges to
//! `time` / `std::time` / `SystemTime`.
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
//! | `EGPS` | `hifitime::Epoch` projected in **GPST** scale (1980-01-06 UTC reference) |
//! | `EQZS` | `hifitime::Epoch` projected in **QZSST** scale (= GPST reference) |
//! | `EGST` | `hifitime::Epoch` projected in **GST** scale (Galileo, 1999-08-21 reference) |
//! | `EBDT` | `hifitime::Epoch` projected in **BDT** scale (BeiDou, 2005-12-31 reference) |
//! | `NANO` | `i128` total nanoseconds (vs `time/`'s i64 — hifitime is wider) |
//! | `SECS` | `i64` whole seconds                                        |
//! | `F064` | [`F064`](crate::float::F064)                               |
//! | `F032` | [`F032`](crate::float::F032)                               |
//!
//! Sprints 4-onward will add `ETDT` / `ETDE` / `ETDB` for the
//! remaining `hifitime::Epoch` scale projections (1-letter `E` +
//! 3-letter time-scale code; `ETD*` is the dynamical-time family
//! marker for TT/ET/TDB).
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
//! - **`E{GPS,QZS}*`** → [`hifitime::GPST_REF_EPOCH`] (1980-01-06 UTC,
//!   = TAI 1980-01-06 − 19 s). GPST and QZSST share this reference;
//!   the two Conn families differ only in scale-tag dispatch
//!   (`to_gpst_*` vs `to_qzsst_*`). **`EGST*`** → 1999-08-21
//!   ([`hifitime::GST_REF_EPOCH`]). **`EBDT*`** → 2005-12-31
//!   ([`hifitime::BDT_REF_EPOCH`]). All four GNSS scales are exact
//!   integer-second offsets to TAI; the HDUR / NANO projections lose
//!   no information, only the F064 projection is lossy at multi-
//!   decade magnitudes.
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
//! | [`EGPSHDUR`]  | `Conn<Epoch, Duration>`                             | Epoch ↔ GPST Duration since 1980-01-06 UTC (degenerate iso) |
//! | [`EGPSNANO`]  | `Conn<Extended<Epoch>, i128>`                       | GPST nanoseconds since 1980-01-06 UTC |
//! | [`EGPSF064`]  | `Conn<F064, Extended<Epoch>>`                       | f64 GPST seconds since 1980-01-06 UTC ↔ Epoch (ULP walks on TAI Duration) |
//! | [`EQZSHDUR`]  | `Conn<Epoch, Duration>`                             | Epoch ↔ QZSST Duration (= GPST reference, distinct scale tag) |
//! | [`EQZSNANO`]  | `Conn<Extended<Epoch>, i128>`                       | QZSST nanoseconds (= GPST numerics, QZSST tag) |
//! | [`EQZSF064`]  | `Conn<F064, Extended<Epoch>>`                       | f64 QZSST seconds ↔ Epoch (ULP walks on TAI Duration) |
//! | [`EGSTHDUR`]  | `Conn<Epoch, Duration>`                             | Epoch ↔ GST (Galileo) Duration since 1999-08-21 (degenerate iso) |
//! | [`EGSTNANO`]  | `Conn<Extended<Epoch>, i128>`                       | GST nanoseconds since 1999-08-21 |
//! | [`EGSTF064`]  | `Conn<F064, Extended<Epoch>>`                       | f64 GST seconds since 1999-08-21 ↔ Epoch (ULP walks on TAI Duration) |
//! | [`EBDTHDUR`]  | `Conn<Epoch, Duration>`                             | Epoch ↔ BDT (BeiDou) Duration since 2005-12-31 (degenerate iso) |
//! | [`EBDTNANO`]  | `Conn<Extended<Epoch>, i128>`                       | BDT nanoseconds since 2005-12-31 |
//! | [`EBDTF064`]  | `Conn<F064, Extended<Epoch>>`                       | f64 BDT seconds since 2005-12-31 ↔ Epoch (ULP walks on TAI Duration) |
//! | [`ETDTF064`]  | `Conn<F064, Extended<Epoch>>`                       | f64 TT seconds since J1900 TT ↔ Epoch (relativistic, +32.184 s offset) |
//! | [`ETDEF064`]  | `Conn<F064, Extended<Epoch>>`                       | f64 NAIF SPICE ET seconds since J2000 ET ↔ Epoch (≤1 ns lossy) |
//! | [`ETDBF064`]  | `Conn<F064, Extended<Epoch>>`                       | f64 ESA TDB seconds since J2000 TDB ↔ Epoch (≤1 ns lossy) |
//! | [`MONTU008`]  | `Conn<Extended<MonthName>, u8>`                     | month enum ↔ canonical 1=Jan…12=Dec u8; saturate u8 ∉ [1,12] |
//! | [`MONTNZ08`]  | `Conn<Extended<MonthName>, NonZeroU8>`              | natural NonZero rep; saturate NonZeroU8 > 12 |
//! | [`WKDYU008`]  | `Conn<Extended<Weekday>, u8>`                       | weekday enum ↔ 0=Mon…6=Sun (ISO); saturate u8 ∉ [0,6] |
//!
//! Each constant ships with a runnable `# Examples` doctest and
//! `proptest!` blocks driving the laws in [`crate::prop::conn`].
//!
//! ## Relativistic scales (TT / ET / TDB) — F064 only
//!
//! Sprint 4 ships **F064-only** Conns for the relativistic scales.
//! HDUR / NANO projections of TT / ET / TDB are **deferred**:
//!
//! - **TT.** Forward `to_tt_duration` adds +32.184 s (`hifitime::TT_OFFSET_MS`),
//!   which `Duration::add` saturates at `HD::MAX` per
//!   `hifitime/src/duration/ops.rs:155-211`. The iso `back ∘ forward`
//!   then loses 32.184 s under `Epoch::Eq`. Neither `iso!` nor
//!   `conn_l!` recovers the boundary; F064's walk fast-paths
//!   intercept.
//! - **ET / TDB.** Lossy iterative algorithms (≤1 ns under hifitime's
//!   `Epoch::Eq` per `hifitime/tests/epoch.rs:2366,2420`). Integer-ns
//!   projections would imply false precision; F064 absorbs the
//!   imprecision via the ULP walk.
//!
//! See [`crate::hifi::epoch`]'s §4 banner for the full derivation.
//!
//! ## Calendar enums (Sprint 5)
//!
//! [`MONTU008`] / [`MONTNZ08`] / [`WKDYU008`] **diverge** from
//! hifitime's `MonthName::from(u8)` and `Weekday::from(u8)` impls,
//! which silently default-on-error or wrap-via-rem_euclid for
//! out-of-domain integers. The Conn variants saturate to
//! `Extended::NegInf` / `Extended::PosInf` instead — the
//! "saturate-don't-pretend" convention from the OFDTNANO family.
//! See [`crate::hifi::calendar`]'s module docs for the rationale.

pub mod calendar;
pub mod duration;
pub mod epoch;

pub use calendar::{MONTNZ08, MONTU008, WKDYU008};
pub use duration::{F032HDUR, F064HDUR, HDURNANO, HDURSECS};
pub use epoch::{
    EBDTF064, EBDTHDUR, EBDTNANO, EGPSF064, EGPSHDUR, EGPSNANO, EGSTF064, EGSTHDUR, EGSTNANO,
    EQZSF064, EQZSHDUR, EQZSNANO, ETAIF064, ETAIHDUR, ETAINANO, ETDBF064, ETDEF064, ETDTF064,
    EUTCF064, EUTCHDUR, EUTCNANO,
};
