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

pub mod laws;

#[cfg(any(test, feature = "testing"))]
pub mod arb;
