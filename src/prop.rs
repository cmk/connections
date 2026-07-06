//! Property predicates and proptest strategies for testing
//! consumers of this crate's algebras.
//!
//! - [`conn`] — Galois-connection law predicates (adjoint laws,
//!   cast lifter laws, two-sided helper laws).
//! - [`lattice`] — Heyting / Coheyting / Bi-Heyting / Boolean /
//!   bare partial-order law predicates.
//! - `arb` — proptest strategies (`arb_f64`, `arb_f32`,
//!   `arb_f64_bounded`, `arb_f16`, the `extended_float_*` and
//!   time-crate generators). Gated on the `proptest` feature, which
//!   flips `proptest` from this crate's dev-dep to an optional
//!   regular dep so downstream callers can pull it in.
//!
//! Each predicate is a pure `bool`-returning fn over this crate's
//! types; downstream wraps them in their own `proptest!` blocks.
//! In-crate tests use the predicate modules through
//! `cfg(any(test, feature = "proptest"))`.
//!
//! ## Downstream usage
//!
//! ```rust,no_run
//! use connections::conn::view_l;
//! use connections::core::f064::F064F032;
//! use connections::float::ExtendedFloat;
//! use connections::prop::conn;
//!
//! // Spot check: F064F032 satisfies the Galois adjoint law over a
//! // representative pair. F064F032 is now a triple-marker unit
//! // struct; `view_l(&F064F032)` is its L-view.
//! let a = ExtendedFloat::Extend(1.5_f64);
//! let b = ExtendedFloat::Extend(1.5_f32);
//! assert!(conn::galois_l(&view_l(&F064F032), a, b));
//! ```
//!
//! With the `proptest` feature enabled, downstream proptest blocks
//! can drive the predicates over arbitrary inputs:
//!
//! ```text
//! use connections::conn::view_l;
//! use connections::prop::{arb, conn};
//! use connections::core::f064::F064F032;
//! use connections::float::ExtendedFloat;
//! use proptest::prelude::*;
//!
//! proptest! {
//!     #[test]
//!     fn f064_f032_satisfies_galois(
//!         a in arb::arb_f64(),
//!         b in arb::arb_f32(),
//!     ) {
//!         prop_assert!(conn::galois_l(
//!             &view_l(&F064F032),
//!             ExtendedFloat::Extend(a),
//!             ExtendedFloat::Extend(b),
//!         ));
//!     }
//! }
//! ```

pub mod conn;
pub mod interval;
pub mod lattice;

#[cfg(any(test, feature = "proptest"))]
#[cfg_attr(docsrs, doc(cfg(feature = "proptest")))]
pub mod arb;
