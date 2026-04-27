//! Property predicates and proptest strategies for testing
//! consumers of this crate's algebras.
//!
//! - [`laws`] — pure `bool`-returning predicate functions, one per
//!   algebraic law. Always public, no proptest dependency. Downstream
//!   crates wrap them in their own `proptest!` blocks via
//!   `prop_assert!(connections::property::laws::heyting_adjunction(&x, &y, &z))`.
//! - [`arb`] — proptest strategies (`arb_f64`, `arb_f32`,
//!   `arb_f64_bounded`, plus tier-specific generators for the
//!   fixed/rate/extended Conn families). Gated on the `testing`
//!   feature, which flips `proptest` from this crate's dev-dep to an
//!   optional regular dep so downstream callers can pull it in.
//!
//! In-crate tests use both modules through `cfg(any(test,
//! feature = "testing"))`.
//!
//! ## Downstream usage
//!
//! ```rust,no_run
//! use connections::compose;
//! use connections::conn::Conn;
//! use connections::conn::std::i64::decimal::{FD00, FD03FD00, FD06FD03, FD09FD06, FD12, FD12FD09};
//! use connections::property::laws;
//!
//! const COMPOSED: Conn<FD12, FD00> = compose!(FD12FD09, FD09FD06, FD06FD03, FD03FD00);
//!
//! // Spot check: a composed Conn satisfies the Galois adjoint law.
//! assert!(laws::conn_galois_l(&COMPOSED, FD12(1_500_000_000_000), FD00(2)));
//! assert!(laws::conn_floor_le_ceil(&COMPOSED, FD12(42)));
//! ```
//!
//! With the `testing` feature enabled, downstream proptest blocks
//! can drive the predicates over arbitrary inputs:
//!
//! ```ignore
//! use connections::property::{arb, laws};
//! use connections::conn::std::i64::decimal::FD12FD00;
//! use proptest::prelude::*;
//!
//! proptest! {
//!     #[test]
//!     fn my_fd12_fd00_satisfies_galois(
//!         p in arb::fixed_fine(1_000_000_000_000),
//!         u in arb::fixed_coarse(1_000_000_000_000),
//!     ) {
//!         use connections::conn::std::i64::decimal::{FD00, FD12};
//!         prop_assert!(laws::conn_galois_l(&FD12FD00, FD12(p), FD00(u)));
//!     }
//! }
//! ```

pub mod laws;

#[cfg(any(test, feature = "testing"))]
#[cfg_attr(docsrs, doc(cfg(feature = "testing")))]
pub mod arb;
