//! Plan 03 verification — the trait-method API on
//! [`ConnL`](connections::conn::ConnL) /
//! [`ConnR`](connections::conn::ConnR) /
//! [`ConnK`](connections::conn::ConnK) agrees with the free-fn and
//! inherent-view projection forms on markers, and value receivers keep
//! resolving accessors to the inherent `const fn` base that the compose
//! macros ride on.
//!
//! These equivalences are structural (the methods forward to the free
//! fns / inherent view), so the properties are regression guards: they
//! fail loudly if a future change makes `M.round(x)` diverge from
//! `round(&M, x)`.

use connections::conn::{
    Conn, ConnK, ConnL, ConnR, L, R, interval, median, round, round1, truncate, view_l, view_r,
};
use connections::core::f064::F064F032;
use connections::float::N5;
use proptest::prelude::*;

/// `N5<f64>` strategy biased toward N5 boundaries, with a finite
/// interior band. NaN is included because `N5` makes it reflexive.
fn ext_f64() -> impl Strategy<Value = N5<f64>> {
    prop_oneof![
        1 => Just(N5::new(f64::NAN)),
        1 => Just(N5::new(f64::NEG_INFINITY)),
        1 => Just(N5::new(f64::INFINITY)),
        8 => (-1.0e6_f64..1.0e6).prop_map(N5::new),
    ]
}

/// `N5<f32>` counterpart of [`ext_f64`].
fn ext_f32() -> impl Strategy<Value = N5<f32>> {
    prop_oneof![
        1 => Just(N5::new(f32::NAN)),
        1 => Just(N5::new(f32::NEG_INFINITY)),
        1 => Just(N5::new(f32::INFINITY)),
        8 => (-1.0e6_f32..1.0e6).prop_map(N5::new),
    ]
}

proptest! {
    /// L-side accessors: `M.ceil(a)` (trait default) equals both the
    /// inherent-view form `M.view_l().ceil(a)` and the free-fn form
    /// `view_l(&M).ceil(a)`; same for `upper` / `ceil1` / `upper1`.
    #[test]
    fn marker_direct_eq_view_l(a in ext_f64(), b in ext_f32()) {
        prop_assert_eq!(F064F032.ceil(a), F064F032.view_l().ceil(a));
        prop_assert_eq!(F064F032.ceil(a), view_l(&F064F032).ceil(a));
        prop_assert_eq!(F064F032.upper(b), F064F032.view_l().upper(b));
        prop_assert_eq!(F064F032.upper1(|x| x, a), view_l(&F064F032).upper1(|x| x, a));
        prop_assert_eq!(F064F032.ceil1(|x| x, b), view_l(&F064F032).ceil1(|x| x, b));
    }

    /// R-side accessors: dual of [`marker_direct_eq_view_l`] over
    /// `floor` / `lower` / `floor1` / `lower1`.
    #[test]
    fn marker_direct_eq_view_r(a in ext_f64(), b in ext_f32()) {
        prop_assert_eq!(F064F032.floor(a), F064F032.view_r().floor(a));
        prop_assert_eq!(F064F032.floor(a), view_r(&F064F032).floor(a));
        prop_assert_eq!(F064F032.lower(b), F064F032.view_r().lower(b));
        prop_assert_eq!(F064F032.lower1(|x| x, a), view_r(&F064F032).lower1(|x| x, a));
        prop_assert_eq!(F064F032.floor1(|x| x, b), view_r(&F064F032).floor1(|x| x, b));
    }

    /// Two-sided helpers: the `ConnK` method equals the retained free
    /// fn for `round` / `truncate` / `interval` / `round1`.
    #[test]
    fn marker_two_sided_eq_free_fn(a in ext_f64(), b in ext_f32()) {
        prop_assert_eq!(F064F032.round(a), round(&F064F032, a));
        prop_assert_eq!(F064F032.truncate(a), truncate(&F064F032, a));
        prop_assert_eq!(F064F032.interval(a), interval(&F064F032, a));
        prop_assert_eq!(F064F032.round1(|x| x, b), round1(&F064F032, |x| x, b));
    }
}

// ── median: method == free fn on a diagonal `A = (B, B)` triple ────────

fn max_i32(p: (i32, i32)) -> i32 {
    p.0.max(p.1)
}
fn dup_i32(x: i32) -> (i32, i32) {
    (x, x)
}
fn min_i32(p: (i32, i32)) -> i32 {
    p.0.min(p.1)
}
connections::conn_k! {
    /// A totally-ordered i32 median triple (join = max, meet = min).
    OrdI32Med : (i32, i32) => i32 {
        ceil:  max_i32,
        inner: dup_i32,
        floor: min_i32,
    }
}

#[test]
fn median_method_eq_free_fn() {
    for (x, y, z) in [(1, 2, 3), (3, 1, 2), (5, 5, 1), (-2, 0, 7), (7, 7, 7)] {
        assert_eq!(
            OrdI32Med.median(x, y, z),
            median(&OrdI32Med, x, y, z),
            "median method must match the free fn for ({x}, {y}, {z})",
        );
    }
    // Sanity: the diagonal triple reduces to the numeric median.
    assert_eq!(OrdI32Med.median(1, 2, 3), 2);
}

// ── value_accessor_unchanged: values keep the inherent `const fn` base ──

fn id_i32(x: i32) -> i32 {
    x
}

/// A one-sided `Conn` value. Its `swap_l` must stay usable in `const`
/// position: if the value receiver bound the (non-`const`) trait
/// default instead of the inherent `const fn`, this item would fail to
/// compile. This is the base the `compose_*!` / `lift_*!` macros ride
/// on.
const VALUE_L: Conn<i32, i32, L> = Conn::new_l(id_i32, id_i32);
const VALUE_SWAPPED: Conn<i32, i32, R> = VALUE_L.swap_l();

#[test]
fn value_accessor_unchanged() {
    // `VALUE_SWAPPED` only exists if `VALUE_L.swap_l()` const-evaluated,
    // i.e. resolved to the inherent `const fn swap_l` (inherent wins
    // method resolution over the new trait default).
    assert_eq!(VALUE_SWAPPED.floor(5), 5);
    // The value is `ConnL` (blanket impl) but not `ConnR`, so it is not
    // `ConnK` — the two-sided helpers stay triple-only. The `.ceil`
    // call resolves to the inherent accessor on the value.
    assert_eq!(VALUE_L.ceil(5), 5);
}
