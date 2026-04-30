//! Galois-connection law predicates, kind-bound and Triple-bound.
//!
//! Each predicate takes either `&Conn<A, B, L>` (L-laws),
//! `&Conn<A, B, R>` (R-laws), or `&T: Triple<A, B>` (laws spanning
//! both views). Inputs are passed by value (Conn is `Copy`).
//! Returns `bool`.

use crate::conn::{Conn, L, R, Triple, ViewL, ViewR};

// (back-compat re-exports removed under the prefix-strip rename —
// `floor_le_ceil`, `ulp_bound`, `idempotent` are the canonical names.)

// ── L-side predicates ─────────────────────────────────────────────────

/// Galois law (left): `ceil(a) ≤ b ⟺ a ≤ inner(b)`.
pub fn galois_l<A: Copy + Eq + PartialOrd, B: Copy + Eq + PartialOrd>(
    c: &Conn<A, B, L>,
    a: A,
    b: B,
) -> bool {
    (c.ceiling(a) <= b) == (a <= c.upper(b))
}

/// Closure law (left): `a ≤ inner(ceil(a))` — unit of `inner ⊣ ceil`.
pub fn closure_l<A: Copy + PartialOrd, B: Copy>(c: &Conn<A, B, L>, a: A) -> bool {
    a <= c.upper(c.ceiling(a))
}

/// Kernel law (left): `ceil(inner(b)) ≤ b` — counit of `inner ⊣ ceil`.
pub fn kernel_l<A: Copy, B: Copy + PartialOrd>(c: &Conn<A, B, L>, b: B) -> bool {
    c.ceiling(c.upper(b)) <= b
}

/// Monotonicity (left): `a1 ≤ a2 ⟹ ceil(a1) ≤ ceil(a2)`.
pub fn monotone_l<A: Copy + PartialOrd, B: Copy + PartialOrd>(
    c: &Conn<A, B, L>,
    a1: A,
    a2: A,
) -> bool {
    if a1 <= a2 {
        c.ceiling(a1) <= c.ceiling(a2)
    } else {
        true
    }
}

/// Idempotence (left): `(inner ∘ ceil)² == (inner ∘ ceil)`.
pub fn idempotent_l<A: Copy + Eq, B: Copy>(c: &Conn<A, B, L>, a: A) -> bool {
    let once = c.upper(c.ceiling(a));
    let twice = c.upper(c.ceiling(once));
    once == twice
}

/// Backwards-compat alias for [`idempotent_l`].
pub fn idempotent<A: Copy + Eq, B: Copy>(c: &Conn<A, B, L>, a: A) -> bool {
    idempotent_l(c, a)
}

/// `upper1` unit law: `a ≤ upper1(c, id, a)`.
pub fn upper1_id_unit<A: Copy + PartialOrd, B: Copy>(c: &Conn<A, B, L>, a: A) -> bool {
    a <= c.upper1(|x| x, a)
}

/// `upper2` collapse-on-projection: `upper2(c, |p, _| p, a, a) == upper1(c, id, a)`.
pub fn upper2_id_diag<A: Copy + Eq, B: Copy>(c: &Conn<A, B, L>, a: A) -> bool {
    c.upper2(|p, _q| p, a, a) == c.upper1(|x| x, a)
}

/// `ceiling1` kernel law: `ceiling1(c, id, b) ≤ b`.
pub fn ceiling1_id_kernel<A: Copy, B: Copy + PartialOrd>(c: &Conn<A, B, L>, b: B) -> bool {
    c.ceiling1(|x| x, b) <= b
}

/// `ceiling2` collapse-on-projection.
pub fn ceiling2_id_diag<A: Copy, B: Copy + Eq>(c: &Conn<A, B, L>, b: B) -> bool {
    c.ceiling2(|p, _q| p, b, b) == c.ceiling1(|x| x, b)
}

/// Round-trip via ceil: `ceil(inner(b)) == b` (exact-embedding L-Conns).
pub fn roundtrip_ceil<A: Copy, B: Copy + Eq>(c: &Conn<A, B, L>, b: B) -> bool {
    c.ceiling(c.upper(b)) == b
}

// ── R-side predicates ─────────────────────────────────────────────────

/// Galois law (right): `inner(b) ≤ a ⟺ b ≤ floor(a)`.
pub fn galois_r<A: Copy + Eq + PartialOrd, B: Copy + Eq + PartialOrd>(
    c: &Conn<A, B, R>,
    a: A,
    b: B,
) -> bool {
    (c.lower(b) <= a) == (b <= c.floor(a))
}

/// Closure law (right): `inner(floor(a)) ≤ a`.
pub fn closure_r<A: Copy + PartialOrd, B: Copy>(c: &Conn<A, B, R>, a: A) -> bool {
    c.lower(c.floor(a)) <= a
}

/// Kernel law (right): `b ≤ floor(inner(b))`.
pub fn kernel_r<A: Copy, B: Copy + PartialOrd>(c: &Conn<A, B, R>, b: B) -> bool {
    b <= c.floor(c.lower(b))
}

/// Monotonicity (right): `b1 ≤ b2 ⟹ inner(b1) ≤ inner(b2)`.
pub fn monotone_r<A: Copy + PartialOrd, B: Copy + PartialOrd>(
    c: &Conn<A, B, R>,
    b1: B,
    b2: B,
) -> bool {
    if b1 <= b2 {
        c.lower(b1) <= c.lower(b2)
    } else {
        true
    }
}

/// Idempotence (right): the kernel operator is idempotent on its image.
pub fn idempotent_r<A: Copy, B: Copy + Eq>(c: &Conn<A, B, R>, b: B) -> bool {
    let once = c.floor(c.lower(b));
    let twice = c.floor(c.lower(once));
    once == twice
}

/// `lower1` counit law: `lower1(c, id, a) ≤ a`.
pub fn lower1_id_counit<A: Copy + PartialOrd, B: Copy>(c: &Conn<A, B, R>, a: A) -> bool {
    c.lower1(|x| x, a) <= a
}

/// `lower2` collapse-on-projection.
pub fn lower2_id_diag<A: Copy + Eq, B: Copy>(c: &Conn<A, B, R>, a: A) -> bool {
    c.lower2(|p, _q| p, a, a) == c.lower1(|x| x, a)
}

/// `floor1` kernel law: `b ≤ floor1(c, id, b)`.
pub fn floor1_id_kernel<A: Copy, B: Copy + PartialOrd>(c: &Conn<A, B, R>, b: B) -> bool {
    b <= c.floor1(|x| x, b)
}

/// `floor2` collapse-on-projection.
pub fn floor2_id_diag<A: Copy, B: Copy + Eq>(c: &Conn<A, B, R>, b: B) -> bool {
    c.floor2(|p, _q| p, b, b) == c.floor1(|x| x, b)
}

/// Round-trip via floor: `floor(inner(b)) == b` (exact-embedding R-Conns).
pub fn roundtrip_floor<A: Copy, B: Copy + Eq>(c: &Conn<A, B, R>, b: B) -> bool {
    c.floor(c.lower(b)) == b
}

// ── Triple-bound predicates ──────────────────────────────────────────

/// `floor(a) ≤ ceil(a)` — the rounding-sandwich. Required for every
/// shipped triple.
pub fn floor_le_ceil<T, A: Copy, B: Copy + PartialOrd>(_t: &T, a: A) -> bool
where
    T: Triple<A, B>,
{
    <T as ViewR<A, B>>::R.floor(a) <= <T as ViewL<A, B>>::L.ceiling(a)
}

/// ULP-bound: `ceil(a) - floor(a) ≤ 1` under a caller-provided
/// rung-extractor.
pub fn ulp_bound<T, A, B, F>(_t: &T, a: A, rung: F) -> bool
where
    T: Triple<A, B>,
    A: Copy,
    B: Copy,
    F: Fn(B) -> i64,
{
    let c_val = rung(<T as ViewL<A, B>>::L.ceiling(a));
    let f_val = rung(<T as ViewR<A, B>>::R.floor(a));
    c_val
        .checked_sub(f_val)
        .is_some_and(|d| (0..=1).contains(&d))
}

/// `interval` evaluated at the conn's midpoint resolves to
/// `Some(Equal)` (or `None` if the source values are NaN-bearing).
pub fn interval_at_midpoint_eq_or_none<T, A, B>(t: &T, x: A) -> bool
where
    T: Triple<A, B>,
    A: Copy
        + PartialOrd
        + core::ops::Add<Output = A>
        + core::ops::Sub<Output = A>
        + core::ops::Div<Output = A>
        + From<u8>,
    B: Copy,
{
    use core::cmp::Ordering;
    let mid = crate::conn::midpoint(t, x);
    matches!(crate::conn::interval(t, mid), None | Some(Ordering::Equal))
}

/// `midpoint(t, x)` lies between `T::R.lower(T::R.floor(x))` and
/// `T::L.upper(T::L.ceiling(x))` whenever those two are comparable.
pub fn midpoint_between<T, A, B>(t: &T, x: A) -> bool
where
    T: Triple<A, B>,
    A: Copy
        + PartialOrd
        + core::ops::Add<Output = A>
        + core::ops::Sub<Output = A>
        + core::ops::Div<Output = A>
        + From<u8>,
    B: Copy,
{
    let lo = <T as ViewR<A, B>>::R.lower(<T as ViewR<A, B>>::R.floor(x));
    let hi = <T as ViewL<A, B>>::L.upper(<T as ViewL<A, B>>::L.ceiling(x));
    let mid = crate::conn::midpoint(t, x);
    if lo <= hi {
        lo <= mid && mid <= hi
    } else {
        true
    }
}

/// `round(t, x)` is always one of `T::L.ceiling(x)` / `T::R.floor(x)`.
pub fn round_picks_endpoint<T, A, B>(t: &T, x: A) -> bool
where
    T: Triple<A, B>,
    A: Copy + PartialOrd + core::ops::Sub<Output = A> + From<u8>,
    B: Copy + Eq,
{
    let r = crate::conn::round(t, x);
    r == <T as ViewL<A, B>>::L.ceiling(x) || r == <T as ViewR<A, B>>::R.floor(x)
}

/// `truncate(t, x)` is always one of `T::L.ceiling(x)` / `T::R.floor(x)`.
pub fn truncate_picks_endpoint<T, A, B>(t: &T, x: A) -> bool
where
    T: Triple<A, B>,
    A: Copy + PartialOrd + From<u8>,
    B: Copy + Eq,
{
    let v = crate::conn::truncate(t, x);
    v == <T as ViewL<A, B>>::L.ceiling(x) || v == <T as ViewR<A, B>>::R.floor(x)
}

/// Toward-zero contract: `x ≥ 0 ⟹ truncate = floor`, otherwise `= ceil`.
pub fn truncate_toward_zero<T, A, B>(t: &T, x: A) -> bool
where
    T: Triple<A, B>,
    A: Copy + PartialOrd + From<u8>,
    B: Copy + Eq,
{
    let zero = A::from(0);
    let v = crate::conn::truncate(t, x);
    if x >= zero {
        v == <T as ViewR<A, B>>::R.floor(x)
    } else {
        v == <T as ViewL<A, B>>::L.ceiling(x)
    }
}

/// `round1(t, id, x) == x` for an identity triple.
pub fn round1_id_unit<T, A, B>(t: &T, x: B) -> bool
where
    T: Triple<A, B>,
    A: Copy + PartialOrd + core::ops::Sub<Output = A> + From<u8>,
    B: Copy + Eq,
{
    crate::conn::round1(t, |a| a, x) == x
}

/// `truncate1(t, id, x) == x` for an identity triple.
pub fn truncate1_id_unit<T, A, B>(t: &T, x: B) -> bool
where
    T: Triple<A, B>,
    A: Copy + PartialOrd + From<u8>,
    B: Copy + Eq,
{
    crate::conn::truncate1(t, |a| a, x) == x
}

// ── Birkhoff median axioms (triple-bound) ─────────────────────────────

/// Median axiom 1 (idempotence): `median(t, x, x, y) == x`.
pub fn median_idempotent<T, A>(t: &T, x: A, y: A) -> bool
where
    T: Triple<(A, A), A>,
    A: Copy + Eq,
{
    crate::conn::median(t, x, x, y) == x
}

/// Median axiom 2 (rotation).
pub fn median_rotate<T, A>(t: &T, x: A, y: A, z: A) -> bool
where
    T: Triple<(A, A), A>,
    A: Copy + Eq,
{
    crate::conn::median(t, x, y, z) == crate::conn::median(t, z, x, y)
}

/// Median axiom 3 (last-two swap).
pub fn median_swap_yz<T, A>(t: &T, x: A, y: A, z: A) -> bool
where
    T: Triple<(A, A), A>,
    A: Copy + Eq,
{
    crate::conn::median(t, x, y, z) == crate::conn::median(t, x, z, y)
}

/// Median axiom 4 (associativity).
pub fn median_associative<T, A>(t: &T, w: A, x: A, y: A, z: A) -> bool
where
    T: Triple<(A, A), A>,
    A: Copy + Eq,
{
    let lhs = crate::conn::median(t, crate::conn::median(t, x, w, y), w, z);
    let rhs = crate::conn::median(t, x, w, crate::conn::median(t, y, w, z));
    lhs == rhs
}
