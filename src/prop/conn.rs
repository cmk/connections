//! Galois-connection law predicates, kind-bound and ConnK-bound.
//!
//! Each predicate takes either `&Conn<A, B, L>` (L-laws),
//! `&Conn<A, B, R>` (R-laws), or `&T: ConnL<A=A,B=B> + ConnR<A=A,B=B>` (laws spanning
//! both views). Inputs are passed by value (Conn is `Copy`).
//! Returns `bool`.

use crate::conn::{
    Conn, ConnL, ConnR, L, R, ceil, ceil1, ceil2, floor, floor1, floor2, lower, upper,
};

// (back-compat re-exports removed under the prefix-strip rename —
// `floor_le_ceil`, `ulp_bound`, `idempotent` are the canonical names.)

// ── L-side predicates ─────────────────────────────────────────────────

/// Galois law (left): `ceil(a) ≤ b ⟺ a ≤ inner(b)`.
pub fn galois_l<A: Copy + Eq + PartialOrd, B: Copy + Eq + PartialOrd>(
    c: &Conn<A, B, L>,
    a: A,
    b: B,
) -> bool {
    (ceil(c, a) <= b) == (a <= upper(c, b))
}

/// Closure law (left): `a ≤ inner(ceil(a))` — unit of `inner ⊣ ceil`.
pub fn closure_l<A: Copy + PartialOrd, B: Copy>(c: &Conn<A, B, L>, a: A) -> bool {
    a <= upper(c, ceil(c, a))
}

/// Kernel law (left): `ceil(inner(b)) ≤ b` — counit of `inner ⊣ ceil`.
pub fn kernel_l<A: Copy, B: Copy + PartialOrd>(c: &Conn<A, B, L>, b: B) -> bool {
    ceil(c, upper(c, b)) <= b
}

/// Monotonicity (left): `a1 ≤ a2 ⟹ ceil(a1) ≤ ceil(a2)`.
pub fn monotone_l<A: Copy + PartialOrd, B: Copy + PartialOrd>(
    c: &Conn<A, B, L>,
    a1: A,
    a2: A,
) -> bool {
    if a1 <= a2 {
        ceil(c, a1) <= ceil(c, a2)
    } else {
        true
    }
}

/// Idempotence (left): `(inner ∘ ceil)² == (inner ∘ ceil)`.
pub fn idempotent_l<A: Copy + Eq, B: Copy>(c: &Conn<A, B, L>, a: A) -> bool {
    let once = upper(c, ceil(c, a));
    let twice = upper(c, ceil(c, once));
    once == twice
}

/// Backwards-compat alias for [`idempotent_l`].
pub fn idempotent<A: Copy + Eq, B: Copy>(c: &Conn<A, B, L>, a: A) -> bool {
    idempotent_l(c, a)
}

/// `ceil1` kernel law: `ceil1(c, id, b) ≤ b`.
pub fn ceil1_id_kernel<A: Copy, B: Copy + PartialOrd>(c: &Conn<A, B, L>, b: B) -> bool {
    ceil1(c, |x| x, b) <= b
}

/// `ceil2` collapse-on-projection.
pub fn ceil2_id_diag<A: Copy, B: Copy + Eq>(c: &Conn<A, B, L>, b: B) -> bool {
    ceil2(c, |p, _q| p, b, b) == ceil1(c, |x| x, b)
}

/// Round-trip via ceil: `ceil(upper(b)) == b` (exact-embedding L-Conns).
pub fn roundtrip_ceil<A: Copy, B: Copy + Eq>(c: &Conn<A, B, L>, b: B) -> bool {
    ceil(c, upper(c, b)) == b
}

/// Iso forward round-trip (L): `inner(ceil(a)) == a`. Holds for
/// any L-Conn that is also an iso (no information lost on the
/// `A → B` side); only needs `A: Eq`, so usable on types that
/// don't impl `Ord`.
pub fn iso_roundtrip_l<A: Copy + Eq, B: Copy>(c: &Conn<A, B, L>, a: A) -> bool {
    upper(c, ceil(c, a)) == a
}

// ── R-side predicates ─────────────────────────────────────────────────

/// Galois law (right): `inner(b) ≤ a ⟺ b ≤ floor(a)`.
pub fn galois_r<A: Copy + Eq + PartialOrd, B: Copy + Eq + PartialOrd>(
    c: &Conn<A, B, R>,
    a: A,
    b: B,
) -> bool {
    (lower(c, b) <= a) == (b <= floor(c, a))
}

/// Closure law (right): `inner(floor(a)) ≤ a`.
pub fn closure_r<A: Copy + PartialOrd, B: Copy>(c: &Conn<A, B, R>, a: A) -> bool {
    lower(c, floor(c, a)) <= a
}

/// Kernel law (right): `b ≤ floor(inner(b))`.
pub fn kernel_r<A: Copy, B: Copy + PartialOrd>(c: &Conn<A, B, R>, b: B) -> bool {
    b <= floor(c, lower(c, b))
}

/// Monotonicity (right): `b1 ≤ b2 ⟹ inner(b1) ≤ inner(b2)`.
pub fn monotone_r<A: Copy + PartialOrd, B: Copy + PartialOrd>(
    c: &Conn<A, B, R>,
    b1: B,
    b2: B,
) -> bool {
    if b1 <= b2 {
        lower(c, b1) <= lower(c, b2)
    } else {
        true
    }
}

/// Idempotence (right): the kernel operator is idempotent on its image.
pub fn idempotent_r<A: Copy, B: Copy + Eq>(c: &Conn<A, B, R>, b: B) -> bool {
    let once = floor(c, lower(c, b));
    let twice = floor(c, lower(c, once));
    once == twice
}

/// `floor1` kernel law: `b ≤ floor1(c, id, b)`.
pub fn floor1_id_kernel<A: Copy, B: Copy + PartialOrd>(c: &Conn<A, B, R>, b: B) -> bool {
    b <= floor1(c, |x| x, b)
}

/// `floor2` collapse-on-projection.
pub fn floor2_id_diag<A: Copy, B: Copy + Eq>(c: &Conn<A, B, R>, b: B) -> bool {
    floor2(c, |p, _q| p, b, b) == floor1(c, |x| x, b)
}

/// Round-trip via floor: `floor(inner(b)) == b` (exact-embedding R-Conns).
pub fn roundtrip_floor<A: Copy, B: Copy + Eq>(c: &Conn<A, B, R>, b: B) -> bool {
    floor(c, lower(c, b)) == b
}

// ── ConnK-bound predicates ──────────────────────────────────────────

/// `floor(a) ≤ ceil(a)` — the rounding-sandwich.
///
/// **Necessary and sufficient for a true adjoint triple.** Equivalent
/// to: `inner` is order-reflecting (`inner(x) ≤ inner(y) ⟹ x ≤ y`).
///
/// Sufficiency: from the closure laws `inner(floor(a)) ≤ a ≤ inner(ceil(a))`,
/// transitivity gives `inner(floor(a)) ≤ inner(ceil(a))`, and
/// order-reflection of `inner` lifts this to `floor(a) ≤ ceil(a)`.
///
/// Necessity: assume `floor(a) ≤ ceil(a)` for every `a`. Take
/// `x, y ∈ B` with `inner(x) ≤ inner(y)`. Then
/// `x ≤ floor(inner(x)) ≤ ceil(inner(x)) ≤ y` — first step is
/// `inner ⊣ floor` kernel, second is the assumption at `a = inner(x)`,
/// third is L-Galois `ceil(a) ≤ b ⟺ a ≤ inner(b)` with the given
/// hypothesis. So `x ≤ y`.
///
/// Required for every marker shipping both `ConnL` and `ConnR`. The
/// `law_battery!` `full` subset enforces both this and its cause —
/// see [`order_reflecting`] for the load-bearing predicate. This
/// predicate is the user-facing fast signal (single quantifier over
/// `A`); `order_reflecting` quantifies over `B²` and thus catches
/// boundary violations with twice the proptest surface area.
pub fn floor_le_ceil<T, A: Copy, B: Copy + PartialOrd>(t: &T, a: A) -> bool
where
    T: ConnL<A = A, B = B> + ConnR<A = A, B = B>,
{
    floor(t, a) <= ceil(t, a)
}

/// `inner(b1) ≤ inner(b2) ⟹ b1 ≤ b2` — `inner` is order-reflecting.
///
/// **The defining property of an adjoint triple.** Given the per-side
/// L/R Galois laws, this is equivalent to [`floor_le_ceil`] (see that
/// predicate's doc for both directions of the proof). Order-reflection
/// is the *cause*; the rounding sandwich is the *corollary*.
///
/// Quantifying over `(b1, b2) ∈ B²` gives a proptest twice the surface
/// area of [`floor_le_ceil`] (which only sees `a ∈ A`), so this catches
/// boundary violations the rounding-sandwich check would miss when the
/// source-side strategy under-samples extremes — the failure mode that
/// hid the Haskell `f09sys` bug for years.
///
/// `inner` is taken from the L view (`t.conn_l().upper`); for a true
/// triple the L-view's `upper` and the R-view's `lower` are the same
/// function pointer by construction, so the choice of view is
/// arbitrary.
pub fn order_reflecting<T, A, B>(t: &T, b1: B, b2: B) -> bool
where
    T: ConnL<A = A, B = B> + ConnR<A = A, B = B>,
    A: Copy + PartialOrd,
    B: Copy + PartialOrd,
{
    let l = t.conn_l();
    let a1 = upper(&l, b1);
    let a2 = upper(&l, b2);
    if a1 <= a2 { b1 <= b2 } else { true }
}

/// ULP-bound: `ceil(a) - floor(a) ≤ 1` under a caller-provided
/// rung-extractor.
pub fn ulp_bound<T, A, B, F>(t: &T, a: A, rung: F) -> bool
where
    T: ConnL<A = A, B = B> + ConnR<A = A, B = B>,
    A: Copy,
    B: Copy,
    F: Fn(B) -> i64,
{
    let c_val = rung(ceil(t, a));
    let f_val = rung(floor(t, a));
    c_val
        .checked_sub(f_val)
        .is_some_and(|d| (0..=1).contains(&d))
}

/// `interval(t, x).contains(&x)` whenever the bracket is
/// non-empty; vacuously true when the bracket is `Empty`
/// (malformed triple, or antichain endpoints in a partial order).
///
/// As of the `interval` sandwich-postcondition refactor this is
/// **true by construction**: `interval` returns `Closed` only
/// when `lo ≤ x ≤ hi`. Kept as a regression check on `interval`'s
/// body — a bug there would now be caught here directly.
pub fn bracket_contains_x<T, A, B>(t: &T, x: A) -> bool
where
    T: ConnL<A = A, B = B> + ConnR<A = A, B = B>,
    A: Copy + PartialOrd,
    B: Copy,
{
    let i = crate::conn::interval(t, x);
    matches!(i, crate::interval::Interval::Empty) || i.contains(&x)
}

/// Bracket endpoints are themselves grid-aligned: re-bracketing
/// either endpoint produces the singleton interval at that endpoint.
/// This is the *correct* idempotence-flavored property — `lo` and
/// `hi` sit on the boundary between B-cells, so each one is its own
/// bracket.
pub fn bracket_endpoints_self_bracket<T, A, B>(t: &T, x: A) -> bool
where
    T: ConnL<A = A, B = B> + ConnR<A = A, B = B>,
    A: Copy + PartialOrd,
    B: Copy,
{
    match crate::conn::interval(t, x) {
        crate::interval::Interval::Empty => true,
        crate::interval::Interval::Closed { lo, hi } => {
            crate::conn::interval(t, lo) == crate::interval::Interval::Closed { lo, hi: lo }
                && crate::conn::interval(t, hi) == crate::interval::Interval::Closed { lo: hi, hi }
        }
    }
}

/// Bracket endpoints share `x`'s B-cell:
/// `floor(lo) == floor(x) && ceil(hi) == ceil(x)`.
pub fn bracket_endpoints_share_b_cell<T, A, B>(t: &T, x: A) -> bool
where
    T: ConnL<A = A, B = B> + ConnR<A = A, B = B>,
    A: Copy + PartialOrd,
    B: Copy + Eq,
{
    match crate::conn::interval(t, x) {
        crate::interval::Interval::Empty => true,
        crate::interval::Interval::Closed { lo, hi } => {
            floor(t, lo) == floor(t, x) && ceil(t, hi) == ceil(t, x)
        }
    }
}

/// `round(t, x)` is always one of `ceil(t, x)` / `floor(t, x)`.
pub fn round_picks_endpoint<T, A, B>(t: &T, x: A) -> bool
where
    T: ConnL<A = A, B = B> + ConnR<A = A, B = B>,
    A: Copy + PartialOrd + core::ops::Sub<Output = A> + From<u8>,
    B: Copy + Eq,
{
    let r = crate::conn::round(t, x);
    r == ceil(t, x) || r == floor(t, x)
}

/// `truncate(t, x)` is always one of `ceil(t, x)` / `floor(t, x)`.
pub fn truncate_picks_endpoint<T, A, B>(t: &T, x: A) -> bool
where
    T: ConnL<A = A, B = B> + ConnR<A = A, B = B>,
    A: Copy + PartialOrd + From<u8>,
    B: Copy + Eq,
{
    let v = crate::conn::truncate(t, x);
    v == ceil(t, x) || v == floor(t, x)
}

/// Toward-zero contract: `x ≥ 0 ⟹ truncate = floor`, otherwise `= ceil`.
pub fn truncate_toward_zero<T, A, B>(t: &T, x: A) -> bool
where
    T: ConnL<A = A, B = B> + ConnR<A = A, B = B>,
    A: Copy + PartialOrd + From<u8>,
    B: Copy + Eq,
{
    let zero = A::from(0);
    let v = crate::conn::truncate(t, x);
    if x >= zero {
        v == floor(t, x)
    } else {
        v == ceil(t, x)
    }
}

/// `round1(t, id, x) == x` for an identity triple.
pub fn round1_id_unit<T, A, B>(t: &T, x: B) -> bool
where
    T: ConnL<A = A, B = B> + ConnR<A = A, B = B>,
    A: Copy + PartialOrd + core::ops::Sub<Output = A> + From<u8>,
    B: Copy + Eq,
{
    crate::conn::round1(t, |a| a, x) == x
}

/// `truncate1(t, id, x) == x` for an identity triple.
pub fn truncate1_id_unit<T, A, B>(t: &T, x: B) -> bool
where
    T: ConnL<A = A, B = B> + ConnR<A = A, B = B>,
    A: Copy + PartialOrd + From<u8>,
    B: Copy + Eq,
{
    crate::conn::truncate1(t, |a| a, x) == x
}

// ── Birkhoff median axioms (triple-bound) ─────────────────────────────

/// Median axiom 1 (idempotence): `median(t, x, x, y) == x`.
pub fn median_idempotent<T, A>(t: &T, x: A, y: A) -> bool
where
    T: ConnL<A = (A, A), B = A> + ConnR<A = (A, A), B = A>,
    A: Copy + Eq,
{
    crate::conn::median(t, x, x, y) == x
}

/// Median axiom 2 (rotation).
pub fn median_rotate<T, A>(t: &T, x: A, y: A, z: A) -> bool
where
    T: ConnL<A = (A, A), B = A> + ConnR<A = (A, A), B = A>,
    A: Copy + Eq,
{
    crate::conn::median(t, x, y, z) == crate::conn::median(t, z, x, y)
}

/// Median axiom 3 (last-two swap).
pub fn median_swap_yz<T, A>(t: &T, x: A, y: A, z: A) -> bool
where
    T: ConnL<A = (A, A), B = A> + ConnR<A = (A, A), B = A>,
    A: Copy + Eq,
{
    crate::conn::median(t, x, y, z) == crate::conn::median(t, x, z, y)
}

/// Median axiom 4 (associativity).
pub fn median_associative<T, A>(t: &T, w: A, x: A, y: A, z: A) -> bool
where
    T: ConnL<A = (A, A), B = A> + ConnR<A = (A, A), B = A>,
    A: Copy + Eq,
{
    let lhs = crate::conn::median(t, crate::conn::median(t, x, w, y), w, z);
    let rhs = crate::conn::median(t, x, w, crate::conn::median(t, y, w, z));
    lhs == rhs
}

// ── law_battery! macro ──────────────────────────────────────────────
//
// Generates the standard property-test battery for a `Conn` marker
// inside a fresh `mod $mod_name` block. Subsumes the per-host-type
// `props_for_pair!` macros that lived in `src/fixed/i*.rs` and the
// hand-rolled blocks in `time/duration.rs`, `addr/ip.rs`, `char.rs`,
// `float/f064.rs`, etc. (Plan 31 T2.)

/// Generate a property-test battery for an adjoint connection.
///
/// `conn:` accepts a value expression — either a triple-marker
/// instance (`TripleIdI32`, `Q008Q000`, …) or a `Conn<_,_,K>` const
/// (`TIMENANO`, `U032I032`, …). The trait dispatch (`.conn_l()` /
/// `.conn_r()`) extracts the appropriate one-sided `Conn` from
/// either shape.
///
/// Each invocation emits `mod $mod_name { ... }` containing the
/// requested subset of the standard property checks:
///
/// | Subset (`subset:` flag) | Tests emitted | Trait bounds on `A` / `B` |
/// |-------------------------|---------------|---------------------------|
/// | `full` (default)        | `galois_l`, `galois_r`, `closure_l`, `closure_r`, `kernel_l`, `kernel_r`, `monotone_l`, `monotone_r`, `idempotent`, `floor_le_ceil`, `order_reflecting`, `bracket_contains_x`, `bracket_endpoints_self_bracket`, `bracket_endpoints_share_b_cell` | `A`, `B`: `Copy + Eq + PartialOrd` |
/// | `numeric_only`          | `full` ∪ `round_picks_endpoint`, `truncate_picks_endpoint`, `truncate_toward_zero`                                    | adds `A: Sub<Output = A> + From<u8>` |
/// | `l_only`                | `galois_l`, `closure_l`, `kernel_l`, `monotone_l`, `idempotent` | same |
/// | `r_only`                | `galois_r`, `closure_r`, `kernel_r`, `monotone_r` | same |
/// | `iso_only`              | `idempotent`, `iso_roundtrip_l`, `roundtrip_ceil`                                                                     | `A`: `Copy + Eq`; `B`: `Copy + Eq` (no `Ord` required) |
///
/// `cases: N` optionally overrides the proptest case count
/// (default: 256, the proptest default; set to 64 for expensive
/// generators like full-range `i128`).
///
/// ```ignore
/// connections::law_battery! {
///     mod q008q000,
///     conn: Q008Q000,
///     fine:   any::<i8>().prop_map(FixedI8::<U8>::from_bits),
///     coarse: any::<i8>().prop_map(FixedI8::<U0>::from_bits),
/// }
///
/// connections::law_battery! {
///     mod q000i032_iso,
///     conn: Q000I032,
///     fine:   any::<i32>().prop_map(FixedI32::<U0>::from_bits),
///     coarse: any::<i32>(),
///     subset: iso_only,
/// }
/// ```
#[macro_export]
macro_rules! law_battery {
    // ── Public top-level arms (forward to internal @batch arms) ──

    // full (default), no cases override
    (mod $m:ident, conn: $c:expr, fine: $f:expr, coarse: $cs:expr $(,)?) => {
        $crate::law_battery!(@batch full, $m, $c, $f, $cs,
            ::proptest::test_runner::Config::default());
    };
    (mod $m:ident, conn: $c:expr, fine: $f:expr, coarse: $cs:expr, cases: $n:expr $(,)?) => {
        $crate::law_battery!(@batch full, $m, $c, $f, $cs,
            ::proptest::test_runner::Config { cases: $n,
                .. ::proptest::test_runner::Config::default() });
    };

    // numeric_only — superset of `full`; adds round/truncate
    // contract properties that need `A: Sub<Output = A> + From<u8>`.
    (mod $m:ident, conn: $c:expr, fine: $f:expr, coarse: $cs:expr,
     subset: numeric_only $(,)?) => {
        $crate::law_battery!(@batch numeric_only, $m, $c, $f, $cs,
            ::proptest::test_runner::Config::default());
    };
    (mod $m:ident, conn: $c:expr, fine: $f:expr, coarse: $cs:expr,
     subset: numeric_only, cases: $n:expr $(,)?) => {
        $crate::law_battery!(@batch numeric_only, $m, $c, $f, $cs,
            ::proptest::test_runner::Config { cases: $n,
                .. ::proptest::test_runner::Config::default() });
    };

    // l_only
    (mod $m:ident, conn: $c:expr, fine: $f:expr, coarse: $cs:expr, subset: l_only $(,)?) => {
        $crate::law_battery!(@batch l_only, $m, $c, $f, $cs,
            ::proptest::test_runner::Config::default());
    };
    (mod $m:ident, conn: $c:expr, fine: $f:expr, coarse: $cs:expr, subset: l_only,
     cases: $n:expr $(,)?) => {
        $crate::law_battery!(@batch l_only, $m, $c, $f, $cs,
            ::proptest::test_runner::Config { cases: $n,
                .. ::proptest::test_runner::Config::default() });
    };

    // r_only
    (mod $m:ident, conn: $c:expr, fine: $f:expr, coarse: $cs:expr, subset: r_only $(,)?) => {
        $crate::law_battery!(@batch r_only, $m, $c, $f, $cs,
            ::proptest::test_runner::Config::default());
    };
    (mod $m:ident, conn: $c:expr, fine: $f:expr, coarse: $cs:expr, subset: r_only,
     cases: $n:expr $(,)?) => {
        $crate::law_battery!(@batch r_only, $m, $c, $f, $cs,
            ::proptest::test_runner::Config { cases: $n,
                .. ::proptest::test_runner::Config::default() });
    };

    // iso_only
    (mod $m:ident, conn: $c:expr, fine: $f:expr, coarse: $cs:expr, subset: iso_only $(,)?) => {
        $crate::law_battery!(@batch iso_only, $m, $c, $f, $cs,
            ::proptest::test_runner::Config::default());
    };
    (mod $m:ident, conn: $c:expr, fine: $f:expr, coarse: $cs:expr, subset: iso_only,
     cases: $n:expr $(,)?) => {
        $crate::law_battery!(@batch iso_only, $m, $c, $f, $cs,
            ::proptest::test_runner::Config { cases: $n,
                .. ::proptest::test_runner::Config::default() });
    };

    // ── Internal @batch arms ──
    //
    // `full` and `numeric_only` share their 14-test core via the
    // hidden `@props_full` arm; `numeric_only` then layers on the
    // arithmetic-bound contract tests via `@props_numeric_extras`.
    // Editing the `full` test set means editing `@props_full` —
    // both batteries pick up the change.

    (@batch full, $m:ident, $c:expr, $f:expr, $cs:expr, $cfg:expr) => {
        mod $m {
            #[allow(unused_imports)]
            use super::*;
            #[allow(unused_imports)]
            use ::proptest::prelude::*;
            #[allow(unused_imports)]
            use $crate::conn::{ConnL as _, ConnR as _};
            $crate::law_battery!(@props_full, $c, $f, $cs, $cfg);
        }
    };

    (@batch numeric_only, $m:ident, $c:expr, $f:expr, $cs:expr, $cfg:expr) => {
        mod $m {
            #[allow(unused_imports)]
            use super::*;
            #[allow(unused_imports)]
            use ::proptest::prelude::*;
            #[allow(unused_imports)]
            use $crate::conn::{ConnL as _, ConnR as _};
            $crate::law_battery!(@props_full, $c, $f, $cs, $cfg);
            $crate::law_battery!(@props_numeric_extras, $c, $f, $cs, $cfg);
        }
    };

    // The shared body for `full` and `numeric_only` — 14 tests.
    (@props_full, $c:expr, $f:expr, $cs:expr, $cfg:expr) => {
        ::proptest::proptest! {
            #![proptest_config($cfg)]
            #[test]
            fn galois_l(a in $f, b in $cs) {
                ::proptest::prop_assert!(
                    $crate::prop::conn::galois_l(&($c).conn_l(), a, b));
            }
            #[test]
            fn galois_r(a in $f, b in $cs) {
                ::proptest::prop_assert!(
                    $crate::prop::conn::galois_r(&($c).conn_r(), a, b));
            }
            #[test]
            fn closure_l(a in $f) {
                ::proptest::prop_assert!(
                    $crate::prop::conn::closure_l(&($c).conn_l(), a));
            }
            #[test]
            fn closure_r(a in $f) {
                ::proptest::prop_assert!(
                    $crate::prop::conn::closure_r(&($c).conn_r(), a));
            }
            #[test]
            fn kernel_l(b in $cs) {
                ::proptest::prop_assert!(
                    $crate::prop::conn::kernel_l(&($c).conn_l(), b));
            }
            #[test]
            fn kernel_r(b in $cs) {
                ::proptest::prop_assert!(
                    $crate::prop::conn::kernel_r(&($c).conn_r(), b));
            }
            #[test]
            fn monotone_l(a1 in $f, a2 in $f) {
                ::proptest::prop_assert!(
                    $crate::prop::conn::monotone_l(&($c).conn_l(), a1, a2));
            }
            #[test]
            fn monotone_r(b1 in $cs, b2 in $cs) {
                ::proptest::prop_assert!(
                    $crate::prop::conn::monotone_r(&($c).conn_r(), b1, b2));
            }
            #[test]
            fn idempotent(a in $f) {
                ::proptest::prop_assert!(
                    $crate::prop::conn::idempotent(&($c).conn_l(), a));
            }
            #[test]
            fn floor_le_ceil(a in $f) {
                ::proptest::prop_assert!(
                    $crate::prop::conn::floor_le_ceil(&($c), a));
            }
            #[test]
            fn order_reflecting(b1 in $cs, b2 in $cs) {
                ::proptest::prop_assert!(
                    $crate::prop::conn::order_reflecting(&($c), b1, b2));
            }
            #[test]
            fn bracket_contains_x(a in $f) {
                ::proptest::prop_assert!(
                    $crate::prop::conn::bracket_contains_x(&($c), a));
            }
            #[test]
            fn bracket_endpoints_self_bracket(a in $f) {
                ::proptest::prop_assert!(
                    $crate::prop::conn::bracket_endpoints_self_bracket(&($c), a));
            }
            #[test]
            fn bracket_endpoints_share_b_cell(a in $f) {
                ::proptest::prop_assert!(
                    $crate::prop::conn::bracket_endpoints_share_b_cell(&($c), a));
            }
        }
    };

    // The numeric-only extras: round/truncate contract properties
    // requiring `A: Sub<Output = A> + From<u8>`. Layered on top of
    // `@props_full` by `@batch numeric_only`.
    (@props_numeric_extras, $c:expr, $f:expr, $cs:expr, $cfg:expr) => {
        ::proptest::proptest! {
            #![proptest_config($cfg)]
            #[test]
            fn round_picks_endpoint(a in $f) {
                ::proptest::prop_assert!(
                    $crate::prop::conn::round_picks_endpoint(&($c), a));
            }
            #[test]
            fn truncate_picks_endpoint(a in $f) {
                ::proptest::prop_assert!(
                    $crate::prop::conn::truncate_picks_endpoint(&($c), a));
            }
            #[test]
            fn truncate_toward_zero(a in $f) {
                ::proptest::prop_assert!(
                    $crate::prop::conn::truncate_toward_zero(&($c), a));
            }
        }
    };

    (@batch l_only, $m:ident, $c:expr, $f:expr, $cs:expr, $cfg:expr) => {
        mod $m {
            #[allow(unused_imports)]
            use super::*;
            #[allow(unused_imports)]
            use ::proptest::prelude::*;
            #[allow(unused_imports)]
            use $crate::conn::ConnL as _;
            ::proptest::proptest! {
                #![proptest_config($cfg)]
                #[test]
                fn galois_l(a in $f, b in $cs) {
                    ::proptest::prop_assert!(
                        $crate::prop::conn::galois_l(&($c).conn_l(), a, b));
                }
                #[test]
                fn closure_l(a in $f) {
                    ::proptest::prop_assert!(
                        $crate::prop::conn::closure_l(&($c).conn_l(), a));
                }
                #[test]
                fn kernel_l(b in $cs) {
                    ::proptest::prop_assert!(
                        $crate::prop::conn::kernel_l(&($c).conn_l(), b));
                }
                #[test]
                fn monotone_l(a1 in $f, a2 in $f) {
                    ::proptest::prop_assert!(
                        $crate::prop::conn::monotone_l(&($c).conn_l(), a1, a2));
                }
                #[test]
                fn idempotent(a in $f) {
                    ::proptest::prop_assert!(
                        $crate::prop::conn::idempotent(&($c).conn_l(), a));
                }
            }
        }
    };

    (@batch r_only, $m:ident, $c:expr, $f:expr, $cs:expr, $cfg:expr) => {
        mod $m {
            #[allow(unused_imports)]
            use super::*;
            #[allow(unused_imports)]
            use ::proptest::prelude::*;
            #[allow(unused_imports)]
            use $crate::conn::ConnR as _;
            ::proptest::proptest! {
                #![proptest_config($cfg)]
                #[test]
                fn galois_r(a in $f, b in $cs) {
                    ::proptest::prop_assert!(
                        $crate::prop::conn::galois_r(&($c).conn_r(), a, b));
                }
                #[test]
                fn closure_r(a in $f) {
                    ::proptest::prop_assert!(
                        $crate::prop::conn::closure_r(&($c).conn_r(), a));
                }
                #[test]
                fn kernel_r(b in $cs) {
                    ::proptest::prop_assert!(
                        $crate::prop::conn::kernel_r(&($c).conn_r(), b));
                }
                #[test]
                fn monotone_r(b1 in $cs, b2 in $cs) {
                    ::proptest::prop_assert!(
                        $crate::prop::conn::monotone_r(&($c).conn_r(), b1, b2));
                }
            }
        }
    };

    (@batch iso_only, $m:ident, $c:expr, $f:expr, $cs:expr, $cfg:expr) => {
        mod $m {
            #[allow(unused_imports)]
            use super::*;
            #[allow(unused_imports)]
            use ::proptest::prelude::*;
            #[allow(unused_imports)]
            use $crate::conn::ConnL as _;
            ::proptest::proptest! {
                #![proptest_config($cfg)]
                #[test]
                fn idempotent(a in $f) {
                    ::proptest::prop_assert!(
                        $crate::prop::conn::idempotent(&($c).conn_l(), a));
                }
                #[test]
                fn iso_roundtrip_l(a in $f) {
                    ::proptest::prop_assert!(
                        $crate::prop::conn::iso_roundtrip_l(&($c).conn_l(), a));
                }
                #[test]
                fn roundtrip_ceil(b in $cs) {
                    ::proptest::prop_assert!(
                        $crate::prop::conn::roundtrip_ceil(&($c).conn_l(), b));
                }
            }
        }
    };
}
