//! Galois-connection law predicates.
//!
//! Each function takes a `&Conn<A, B>` plus inputs by value (Conn
//! types in this crate are all `Copy`) and returns `bool`, so
//! downstream crates can drive them in their own `proptest!` blocks
//! without depending on this crate's strategy module:
//!
//! ```ignore
//! use connections::prop::conn::conn_galois_l;
//! use proptest::prelude::*;
//!
//! proptest! {
//!     #[test]
//!     fn my_conn_satisfies_galois(a: i32, b: i32) {
//!         prop_assert!(conn_galois_l(&MY_CONN, a, b));
//!     }
//! }
//! ```
//!
//! The bound `Eq + PartialOrd` is the lawful framework: `Eq`
//! certifies reflexive `PartialEq`, and `PartialOrd` derives a
//! genuine partial order from it. Rust's `PartialOrd` alone is too
//! weak (NaN ≠ NaN under raw-float `PartialEq` breaks reflexivity);
//! the `Eq` bound is what enforces the float fix at the wrapper
//! boundary. Float Conns route through `ExtendedFloat<T>`, whose
//! patched `PartialEq` makes `NaN == NaN` and is therefore `Eq`.
//!
//! Naming convention: every predicate is `conn_<lawname>` —
//! adjoint laws (`conn_galois_l`/`r`, `conn_closure_l`/`r`,
//! `conn_kernel_l`/`r`, `conn_monotone_l`/`r`, `conn_idempotent`,
//! `conn_floor_le_ceil`, `conn_roundtrip_*`, `conn_ulp_bound`) plus
//! the cast-lifter laws on `Conn`'s free-fn operations (`upper1`,
//! `ceiling1`, `floor1`, `lower1`, the `*2` variants, `interval`,
//! `midpoint`, `round`, `truncate`, `median`).

use crate::conn::Conn;

// ── Adjoint laws ─────────────────────────────────────────────────

/// Galois law (left): `ceil(a) ≤ b ⟺ a ≤ inner(b)`.
pub fn conn_galois_l<A: Copy + Eq + PartialOrd, B: Copy + Eq + PartialOrd>(
    c: &Conn<A, B>,
    a: A,
    b: B,
) -> bool {
    (c.ceil(a) <= b) == (a <= c.inner(b))
}

/// Galois law (right): `inner(b) ≤ a ⟺ b ≤ floor(a)`.
pub fn conn_galois_r<A: Copy + Eq + PartialOrd, B: Copy + Eq + PartialOrd>(
    c: &Conn<A, B>,
    a: A,
    b: B,
) -> bool {
    (c.inner(b) <= a) == (b <= c.floor(a))
}

/// Closure law (left): `a ≤ inner(ceil(a))` — the unit of the
/// `inner ⊣ ceil` adjunction.
pub fn conn_closure_l<A: Copy + PartialOrd, B: Copy>(c: &Conn<A, B>, a: A) -> bool {
    a <= c.inner(c.ceil(a))
}

/// Closure law (right): `inner(floor(a)) ≤ a` — the dual of [`conn_closure_l`].
pub fn conn_closure_r<A: Copy + PartialOrd, B: Copy>(c: &Conn<A, B>, a: A) -> bool {
    c.inner(c.floor(a)) <= a
}

/// Kernel law (left): `ceil(inner(b)) ≤ b` — the counit of the
/// `inner ⊣ ceil` adjunction.
pub fn conn_kernel_l<A: Copy, B: Copy + PartialOrd>(c: &Conn<A, B>, b: B) -> bool {
    c.ceil(c.inner(b)) <= b
}

/// Kernel law (right): `b ≤ floor(inner(b))` — the dual of [`conn_kernel_l`].
pub fn conn_kernel_r<A: Copy, B: Copy + PartialOrd>(c: &Conn<A, B>, b: B) -> bool {
    b <= c.floor(c.inner(b))
}

/// Monotonicity (left): `a1 ≤ a2 ⟹ ceil(a1) ≤ ceil(a2) ∧ floor(a1) ≤ floor(a2)`.
pub fn conn_monotone_l<A: Copy + PartialOrd, B: Copy + PartialOrd>(
    c: &Conn<A, B>,
    a1: A,
    a2: A,
) -> bool {
    if a1 <= a2 {
        c.ceil(a1) <= c.ceil(a2) && c.floor(a1) <= c.floor(a2)
    } else {
        true
    }
}

/// Monotonicity (right): `b1 ≤ b2 ⟹ inner(b1) ≤ inner(b2)`.
pub fn conn_monotone_r<A: Copy + PartialOrd, B: Copy + PartialOrd>(
    c: &Conn<A, B>,
    b1: B,
    b2: B,
) -> bool {
    if b1 <= b2 {
        c.inner(b1) <= c.inner(b2)
    } else {
        true
    }
}

/// Idempotence: `(inner ∘ ceil) ∘ (inner ∘ ceil) = inner ∘ ceil` —
/// the closure operator is idempotent on its image. With `Eq +
/// PartialOrd` (i.e. `PartialEq` is reflexive), comparison is
/// directly via `==`; there is no need for the preorder-
/// equivalence pattern (`x ≤ y && y ≤ x`).
pub fn conn_idempotent<A: Copy + Eq, B: Copy>(c: &Conn<A, B>, a: A) -> bool {
    let once = c.inner(c.ceil(a));
    let twice = c.inner(c.ceil(once));
    once == twice
}

/// `floor(a) ≤ ceil(a)` — the floor never exceeds the ceiling.
pub fn conn_floor_le_ceil<A: Copy, B: Copy + PartialOrd>(c: &Conn<A, B>, a: A) -> bool {
    c.floor(a) <= c.ceil(a)
}

/// Round-trip via ceil: `ceil(inner(b)) = b` for exact-embedding
/// connections (where `inner(b)` lands on a value that ceils back
/// to `b`). Strictly stronger than [`conn_kernel_l`].
pub fn conn_roundtrip_ceil<A: Copy, B: Copy + Eq>(c: &Conn<A, B>, b: B) -> bool {
    c.ceil(c.inner(b)) == b
}

/// Round-trip via floor: `floor(inner(b)) = b` for exact-embedding
/// connections. Strictly stronger than [`conn_kernel_r`].
pub fn conn_roundtrip_floor<A: Copy, B: Copy + Eq>(c: &Conn<A, B>, b: B) -> bool {
    c.floor(c.inner(b)) == b
}

/// ULP-bound: `ceil(a) - floor(a) ≤ 1` under a caller-provided
/// rung-extractor. Specific to integer-tier connections (the rung
/// types have an `i64` payload); downstream supplies the extractor
/// closure (e.g. `|b| b.0`).
///
/// Uses `checked_sub` rather than `>=` + raw subtraction so the
/// `floor ≤ ceil` ordering is checked explicitly: if a buggy
/// implementation returns `floor > ceil`, the predicate returns
/// `false` rather than masking the violation via i64 wraparound.
pub fn conn_ulp_bound<A, B, F>(c: &Conn<A, B>, a: A, rung: F) -> bool
where
    A: Copy,
    B: Copy,
    F: Fn(B) -> i64,
{
    let c_val = rung(c.ceil(a));
    let f_val = rung(c.floor(a));
    c_val
        .checked_sub(f_val)
        .is_some_and(|d| (0..=1).contains(&d))
}

// ── Cast lifter laws (for the `upper`/`lower`/`ceiling`/`floor` ──
//    free fns folded into `crate::conn` from the former
//    `crate::conn::cast` submodule) ────────────────────────────────
//
// These predicates exercise the lifter free functions (`upper1`,
// `ceiling1`, etc.). The underlying algebraic laws (closure /
// kernel / monotonicity) are already covered by the adjoint-law
// predicates above; these add a thin layer that catches
// mis-delegation in the lifters themselves (e.g. an `upper1` that
// accidentally calls `floor` instead of `ceil` would still typecheck
// but would fail the unit law on a non-degenerate triple).

/// `upper1` unit law: `a ≤ upper1(c, id, a)`. Equivalent to
/// [`conn_closure_l`] routed through the lifter.
pub fn conn_upper1_id_unit<A: Copy + PartialOrd, B: Copy>(c: &Conn<A, B>, a: A) -> bool {
    a <= crate::conn::upper1(c, |x| x, a)
}

/// `lower1` counit law: `lower1(c, id, a) ≤ a`. Equivalent to
/// [`conn_closure_r`] routed through the lifter.
pub fn conn_lower1_id_counit<A: Copy + PartialOrd, B: Copy>(c: &Conn<A, B>, a: A) -> bool {
    crate::conn::lower1(c, |x| x, a) <= a
}

/// `ceiling1` kernel law: `ceiling1(c, id, b) ≤ b`. Equivalent to
/// [`conn_kernel_l`] routed through the lifter.
pub fn conn_ceiling1_id_kernel<A: Copy, B: Copy + PartialOrd>(c: &Conn<A, B>, b: B) -> bool {
    crate::conn::ceiling1(c, |x| x, b) <= b
}

/// `floor1` kernel law: `b ≤ floor1(c, id, b)`. Equivalent to
/// [`conn_kernel_r`] routed through the lifter.
pub fn conn_floor1_id_kernel<A: Copy, B: Copy + PartialOrd>(c: &Conn<A, B>, b: B) -> bool {
    b <= crate::conn::floor1(c, |x| x, b)
}

/// `upper2` collapse-on-projection: when called with the
/// first-projection `|p, _| p` on equal args `(a, a)`, `upper2`
/// equals `upper1` with `id`. This is a narrow consistency check on
/// the lifter, **not** a general diagonal law; for arbitrary `f`,
/// the broader `upper2(c, f, a, a) == upper1(c, |b| f(b, b), a)`
/// would require `f` to be supplied as a parameter.
pub fn conn_upper2_id_diag<A: Copy + Eq, B: Copy>(c: &Conn<A, B>, a: A) -> bool {
    let l = crate::conn::upper2(c, |p, _q| p, a, a);
    let r = crate::conn::upper1(c, |x| x, a);
    l == r
}

/// `lower2` collapse-on-projection: dual of [`conn_upper2_id_diag`]
/// — narrow check that `lower2(c, |p, _| p, a, a) == lower1(c, id, a)`.
pub fn conn_lower2_id_diag<A: Copy + Eq, B: Copy>(c: &Conn<A, B>, a: A) -> bool {
    let l = crate::conn::lower2(c, |p, _q| p, a, a);
    let r = crate::conn::lower1(c, |x| x, a);
    l == r
}

/// `ceiling2` collapse-on-projection: with `|p, _| p` on `(b, b)`,
/// equals `ceiling1` with `id`. Narrow check, see
/// [`conn_upper2_id_diag`] for why.
pub fn conn_ceiling2_id_diag<A: Copy, B: Copy + Eq>(c: &Conn<A, B>, b: B) -> bool {
    let l = crate::conn::ceiling2(c, |p, _q| p, b, b);
    let r = crate::conn::ceiling1(c, |x| x, b);
    l == r
}

/// `floor2` collapse-on-projection: dual of [`conn_ceiling2_id_diag`].
pub fn conn_floor2_id_diag<A: Copy, B: Copy + Eq>(c: &Conn<A, B>, b: B) -> bool {
    let l = crate::conn::floor2(c, |p, _q| p, b, b);
    let r = crate::conn::floor1(c, |x| x, b);
    l == r
}

// ── Two-sided helper laws (for `crate::conn::{interval, midpoint,
//    round, truncate, median}` and friends) ─────────────────────

/// `interval` evaluated at the conn's midpoint resolves to
/// `Some(Equal)` (or `None` if the source values are NaN-bearing).
/// Mirrors Haskell `Cast.hs` doctest:
/// `interval c (midpoint c x) == Just EQ`.
pub fn conn_interval_at_midpoint_eq_or_none<A, B>(c: &Conn<A, B>, x: A) -> bool
where
    A: Copy
        + PartialOrd
        + core::ops::Add<Output = A>
        + core::ops::Sub<Output = A>
        + core::ops::Div<Output = A>
        + From<u8>,
{
    use core::cmp::Ordering;
    let mid = crate::conn::midpoint(c, x);
    let result = crate::conn::interval(c, mid);
    matches!(result, None | Some(Ordering::Equal))
}

/// `midpoint(c, x)` lies between `c.inner(c.floor(x))` and
/// `c.inner(c.ceil(x))` whenever those two are themselves comparable.
/// On saturating Conns the bracket can flip; the predicate returns
/// `true` vacuously when `lo > hi` (consistent with the
/// `conn_floor_le_ceil` precedent for injective-`inner` checks).
pub fn conn_midpoint_between<A, B>(c: &Conn<A, B>, x: A) -> bool
where
    A: Copy
        + PartialOrd
        + core::ops::Add<Output = A>
        + core::ops::Sub<Output = A>
        + core::ops::Div<Output = A>
        + From<u8>,
{
    let lo = c.inner(c.floor(x));
    let hi = c.inner(c.ceil(x));
    let mid = crate::conn::midpoint(c, x);
    if lo <= hi {
        lo <= mid && mid <= hi
    } else {
        true
    }
}

/// `round(c, x)` is always one of `c.ceil(x)` / `c.floor(x)` (since
/// every dispatch arm of [`crate::conn::round`] returns one or
/// the other directly).
pub fn conn_round_picks_endpoint<A, B>(c: &Conn<A, B>, x: A) -> bool
where
    A: Copy + PartialOrd + core::ops::Sub<Output = A> + From<u8>,
    B: Copy + Eq,
{
    let r = crate::conn::round(c, x);
    r == c.ceil(x) || r == c.floor(x)
}

/// `truncate(c, x)` is always one of `c.ceil(x)` / `c.floor(x)`.
pub fn conn_truncate_picks_endpoint<A, B>(c: &Conn<A, B>, x: A) -> bool
where
    A: Copy + PartialOrd + From<u8>,
    B: Copy + Eq,
{
    let t = crate::conn::truncate(c, x);
    t == c.ceil(x) || t == c.floor(x)
}

/// Toward-zero contract: `x ≥ 0 ⟹ truncate = floor`,
/// otherwise (including the NaN-bearing case where `x ≥ 0` is false)
/// `truncate = ceil`.
pub fn conn_truncate_toward_zero<A, B>(c: &Conn<A, B>, x: A) -> bool
where
    A: Copy + PartialOrd + From<u8>,
    B: Copy + Eq,
{
    let zero = A::from(0);
    let t = crate::conn::truncate(c, x);
    if x >= zero {
        t == c.floor(x)
    } else {
        t == c.ceil(x)
    }
}

/// `round1(c, id, x) == x` for an identity Conn (Haskell axiom
/// `round1 identity = id`). Documented to be a delegation check on
/// identity Conns; on non-identity triples the equality holds only
/// when `x` already lies on a representable rung.
///
/// # Warning
///
/// Only reliable as a law predicate for **identity Conns**. The
/// signature accepts any `Conn<A, B>`, but driving this predicate
/// over a non-identity triple (e.g. `I016I008`) produces spurious
/// failures whenever `x` does not already lie on a representable
/// rung — those are not law violations. For non-identity Conns,
/// use [`conn_round_picks_endpoint`] instead.
pub fn conn_round1_id_unit<A, B>(c: &Conn<A, B>, x: B) -> bool
where
    A: Copy + PartialOrd + core::ops::Sub<Output = A> + From<u8>,
    B: Copy + Eq,
{
    crate::conn::round1(c, |a| a, x) == x
}

/// `truncate1(c, id, x) == x` for an identity Conn (Haskell axiom
/// `truncate1 identity = id`). Same caveats as
/// [`conn_round1_id_unit`].
///
/// # Warning
///
/// Only reliable as a law predicate for **identity Conns**. For
/// non-identity Conns, use [`conn_truncate_picks_endpoint`] —
/// driving this predicate elsewhere produces spurious failures
/// that are not law violations.
pub fn conn_truncate1_id_unit<A, B>(c: &Conn<A, B>, x: B) -> bool
where
    A: Copy + PartialOrd + From<u8>,
    B: Copy + Eq,
{
    crate::conn::truncate1(c, |a| a, x) == x
}

/// Birkhoff median axiom 1: `median(c, x, x, y) == x`.
pub fn conn_median_idempotent<A>(c: &Conn<(A, A), A>, x: A, y: A) -> bool
where
    A: Copy + Eq,
{
    crate::conn::median(c, x, x, y) == x
}

/// Birkhoff median axiom 2 (rotation):
/// `median(c, x, y, z) == median(c, z, x, y)`.
pub fn conn_median_rotate<A>(c: &Conn<(A, A), A>, x: A, y: A, z: A) -> bool
where
    A: Copy + Eq,
{
    crate::conn::median(c, x, y, z) == crate::conn::median(c, z, x, y)
}

/// Birkhoff median axiom 3 (last-two swap):
/// `median(c, x, y, z) == median(c, x, z, y)`.
pub fn conn_median_swap_yz<A>(c: &Conn<(A, A), A>, x: A, y: A, z: A) -> bool
where
    A: Copy + Eq,
{
    crate::conn::median(c, x, y, z) == crate::conn::median(c, x, z, y)
}
