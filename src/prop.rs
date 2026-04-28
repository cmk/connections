//! Property predicates and proptest strategies for testing
//! consumers of this crate's algebras.
//!
//! - [`laws`] — pure `bool`-returning predicate functions, one per
//!   algebraic law. Always public, no proptest dependency. Downstream
//!   crates wrap them in their own `proptest!` blocks via
//!   `prop_assert!(connections::prop::laws::heyting_adjunction(&x, &y, &z))`.
//! - [`arb`] — proptest strategies (`arb_f64`, `arb_f32`,
//!   `arb_f64_bounded`, `arb_f16`, the `extended_float_*` and
//!   time-crate generators). Gated on the
//!   `testing` feature, which flips `proptest` from this crate's
//!   dev-dep to an optional regular dep so downstream callers can
//!   pull it in.
//!
//! In-crate tests use both modules through `cfg(any(test,
//! feature = "testing"))`.
//!
//! ## Downstream usage
//!
//! ```rust,no_run
//! use connections::float::f32::F064F032;
//! use connections::float::ExtendedFloat;
//! use connections::prop::laws;
//!
//! // Spot check: F064F032 satisfies the Galois adjoint law over a
//! // representative pair.
//! let a = ExtendedFloat::Extend(1.5_f64);
//! let b = ExtendedFloat::Extend(1.5_f32);
//! assert!(laws::conn_galois_l(&F064F032, a, b));
//! ```
//!
//! With the `testing` feature enabled, downstream proptest blocks
//! can drive the predicates over arbitrary inputs:
//!
//! ```ignore
//! use connections::prop::{arb, laws};
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
//!         prop_assert!(laws::conn_galois_l(
//!             &F064F032,
//!             ExtendedFloat::Extend(a),
//!             ExtendedFloat::Extend(b),
//!         ));
//!     }
//! }
//! ```

pub mod laws;

#[cfg(any(test, feature = "testing"))]
#[cfg_attr(docsrs, doc(cfg(feature = "testing")))]
pub mod arb;
