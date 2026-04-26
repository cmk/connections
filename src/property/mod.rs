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
//! use connections::conn::fixed::{F03F00, F06F03, F09F06, F12F09, Pico, Uni};
//! use connections::property::laws;
//!
//! const COMPOSED: Conn<Pico, Uni> = compose!(F12F09, F09F06, F06F03, F03F00);
//!
//! // Spot check: a composed Conn satisfies the Galois adjoint law.
//! assert!(laws::conn_galois_l(&COMPOSED, Pico(1_500_000_000_000), Uni(2)));
//! assert!(laws::conn_floor_le_ceil(&COMPOSED, Pico(42)));
//! ```
//!
//! With the `testing` feature enabled, downstream proptest blocks
//! can drive the predicates over arbitrary inputs:
//!
//! ```ignore
//! use connections::property::{arb, laws};
//! use connections::conn::fixed::F12F00;
//! use proptest::prelude::*;
//!
//! proptest! {
//!     #[test]
//!     fn my_pico_uni_satisfies_galois(
//!         p in arb::fixed_fine(1_000_000_000_000),
//!         u in arb::fixed_coarse(1_000_000_000_000),
//!     ) {
//!         use connections::conn::fixed::{Pico, Uni};
//!         prop_assert!(laws::conn_galois_l(&F12F00, Pico(p), Uni(u)));
//!     }
//! }
//! ```

pub mod laws;

#[cfg(any(test, feature = "testing"))]
pub mod arb;
