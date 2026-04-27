//! Galois connections among the [`time`](https://docs.rs/time) crate's
//! calendar / clock / duration types.
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
//! # Constants (added incrementally — see [`crate::doc/plans`])
//!
//! Pending — see the sprint plan. Each constant ships with a runnable
//! `# Examples` doctest and a `proptest!` block driving the laws in
//! [`crate::property::laws`].
//!
//! # Verification
//!
//! Every `Conn` constant is exercised in `#[cfg(test)] mod tests` by
//! the full Galois law battery from [`crate::property::laws`]. The
//! [`Ple`](crate::lattice::Ple) impls below delegate to the time
//! crate's existing total `Ord` — no NaN handling is needed.
//!
//! ```rust
//! use time::{Date, Month};
//! let d = Date::from_calendar_date(2000, Month::January, 1).unwrap();
//! assert_eq!(d.year(), 2000);
//! ```
