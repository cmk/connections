//! Compile-fail test driver via `trybuild`.
//!
//! Each fixture in `tests/compile_fail/` exercises the type-system
//! discipline introduced in Plan 29A: kind-tagged Conns and the
//! `ImpliesL` / `ImpliesR` bounds on free fns and property
//! predicates. The `.stderr` snapshots pin the rustc error message
//! so a regression that lets the wrong kind through trips this
//! test.
//!
//! Snapshots may need updating across rustc upgrades when the
//! compiler's diagnostic wording shifts. Re-bless via:
//! `TRYBUILD=overwrite cargo test --test compile_fail`.

#[test]
fn kind_discipline() {
    let t = trybuild::TestCases::new();
    t.compile_fail("tests/compile_fail/floor_on_l_conn.rs");
    t.compile_fail("tests/compile_fail/ceiling_on_r_conn.rs");
    t.compile_fail("tests/compile_fail/galois_l_on_r_conn.rs");
    t.compile_fail("tests/compile_fail/galois_r_on_l_conn.rs");
    // The E0277 snapshot for `round` enumerates every type implementing
    // `ConnL`, so its wording depends on which feature-gated marker
    // families are compiled in. Pinned against CI's feature set; other
    // combinations skip it rather than chase an unstable list.
    #[cfg(all(
        feature = "fixed",
        feature = "time",
        feature = "hifi",
        feature = "uhlc"
    ))]
    t.compile_fail("tests/compile_fail/round_on_l_conn.rs");
    t.compile_fail("tests/compile_fail/compose_l_with_r.rs");
}
