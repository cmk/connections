//! Property predicates and proptest strategies for testing
//! consumers of this crate's algebras.
//!
//! - [`conn`] — Galois-connection law predicates (adjoint laws,
//!   cast lifter laws, two-sided helper laws).
//! - [`lattice`] — Heyting / Coheyting / Bi-Heyting / Boolean /
//!   bare partial-order law predicates.
//! - [`arb`] — proptest strategies (`arb_f64`, `arb_f32`,
//!   `arb_f64_bounded`, `arb_f16`, the `extended_float_*` and
//!   time-crate generators). Gated on the `testing` feature, which
//!   flips `proptest` from this crate's dev-dep to an optional
//!   regular dep so downstream callers can pull it in.
//!
//! Each predicate is a pure `bool`-returning fn over this crate's
//! types; downstream wraps them in their own `proptest!` blocks.
//! In-crate tests use the predicate modules through
//! `cfg(any(test, feature = "testing"))`.
//!
//! ## Downstream usage
//!
//! ```rust,no_run
//! use connections::float::f32::F064F032;
//! use connections::float::ExtendedFloat;
//! use connections::prop::conn;
//!
//! // Spot check: F064F032 satisfies the Galois adjoint law over a
//! // representative pair. F064F032 is now a triple-marker unit
//! // struct; reach for its L-view via the ViewL impl.
//! use connections::conn::ViewL;
//! let a = ExtendedFloat::Extend(1.5_f64);
//! let b = ExtendedFloat::Extend(1.5_f32);
//! assert!(conn::galois_l(&F064F032::L, a, b));
//! ```
//!
//! With the `testing` feature enabled, downstream proptest blocks
//! can drive the predicates over arbitrary inputs:
//!
//! ```ignore
//! use connections::conn::ViewL;  // brings F064F032::L into scope
//! use connections::prop::{arb, conn};
//! use connections::float::f32::F064F032;
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
//!             &F064F032::L,
//!             ExtendedFloat::Extend(a),
//!             ExtendedFloat::Extend(b),
//!         ));
//!     }
//! }
//! ```

pub mod conn;
pub mod lattice;

#[cfg(any(test, feature = "testing"))]
#[cfg_attr(docsrs, doc(cfg(feature = "testing")))]
pub mod arb;
