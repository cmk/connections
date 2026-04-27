//! Algebraic-law predicates over this crate's lattice traits.
//!
//! Each function takes its inputs by reference and returns `bool`,
//! so downstream crates can drive them in their own `proptest!`
//! blocks without depending on this crate's strategy module:
//!
//! ```ignore
//! use connections::property::laws::heyting_adjunction;
//! use proptest::prelude::*;
//!
//! proptest! {
//!     #[test]
//!     fn my_type_is_heyting(x: MyType, y: MyType, z: MyType) {
//!         prop_assert!(heyting_adjunction(&x, &y, &z));
//!     }
//! }
//! ```
//!
//! Naming convention: `<algebra>_<lawname>` — `heyting_*`,
//! `coheyting_*`, `biheyting_*`, `symmetric_*`, `boolean_*` for the
//! lattice families; `conn_*` and `lattice_*` for Galois-connection
//! laws and bare-preorder laws.

use crate::conn::Conn;
use crate::lattice::{Coheyting, Heyting};

// ── Heyting (h0–h17) ─────────────────────────────────────────────

/// h0: adjunction — `x.meet(y) ⊑ z ⟺ x ⊑ y.imp(z)`
pub fn heyting_adjunction<T: Heyting + Eq>(x: &T, y: &T, z: &T) -> bool {
    (x.meet(y) <= *z) == (*x <= y.imp(z))
}

/// h1: imp monotone in 2nd arg under join
pub fn heyting_imp_mono_join_2nd<T: Heyting>(x: &T, y: &T, z: &T) -> bool {
    x.imp(y) <= x.imp(&y.join(z))
}

/// h2: imp antitone in 1st arg under join
pub fn heyting_imp_anti_join_1st<T: Heyting>(x: &T, y: &T, z: &T) -> bool {
    x.join(z).imp(y) <= x.imp(y)
}

/// h3: imp monotone in 2nd arg under ple
pub fn heyting_imp_mono_ple_2nd<T: Heyting>(x: &T, y: &T, z: &T) -> bool {
    if *x <= *y {
        z.imp(x) <= z.imp(y)
    } else {
        true // vacuously true
    }
}

/// h4: currying — `(x.meet(y)).imp(z) == x.imp(y.imp(z))`
pub fn heyting_currying<T: Heyting + Eq>(x: &T, y: &T, z: &T) -> bool {
    x.meet(y).imp(z) == x.imp(&y.imp(z))
}

/// h5: imp distributes over meet
pub fn heyting_imp_dist_meet<T: Heyting + Eq>(x: &T, y: &T, z: &T) -> bool {
    x.imp(&y.meet(z)) == x.imp(y).meet(&x.imp(z))
}

/// h6: weakening — `y ⊑ x.imp(x.meet(y))`
pub fn heyting_weakening<T: Heyting>(x: &T, y: &T) -> bool {
    *y <= x.imp(&x.meet(y))
}

/// h7: modus ponens — `x.meet(x.imp(y)) == x.meet(y)`
pub fn heyting_modus_ponens<T: Heyting + Eq>(x: &T, y: &T) -> bool {
    x.meet(&x.imp(y)) == x.meet(y)
}

/// h8: neg boundary values — `bot.neg() == top && top.neg() == bot`.
/// Takes a dummy argument so it can be driven from a `proptest!` block.
pub fn heyting_neg_boundary<T: Heyting + Eq>(_: &T) -> bool {
    T::bot().neg() == T::top() && T::top().neg() == T::bot()
}

/// c8: coneg boundary values — `bot.coneg() == top && top.coneg() == bot`.
/// Takes a dummy argument so it can be driven from a `proptest!` block.
pub fn coheyting_coneg_boundary<T: Coheyting + Eq>(_: &T) -> bool {
    T::bot().coneg() == T::top() && T::top().coneg() == T::bot()
}

/// h9: neg-join ≤ imp
pub fn heyting_neg_join_le_imp<T: Heyting>(x: &T, y: &T) -> bool {
    x.neg().join(y) <= x.imp(y)
}

/// h10: imp = top iff ⊑
pub fn heyting_imp_top_iff_ple<T: Heyting + Eq>(x: &T, y: &T) -> bool {
    (*x <= *y) == (x.imp(y) == T::top())
}

/// h11: neg antitone under join
pub fn heyting_neg_anti_join<T: Heyting>(x: &T, y: &T) -> bool {
    x.join(y).neg() <= x.neg()
}

/// h12: neg-imp de Morgan — `(x.imp(y)).neg() == x.neg().neg().meet(y.neg())`
pub fn heyting_neg_imp_de_morgan<T: Heyting + Eq>(x: &T, y: &T) -> bool {
    x.imp(y).neg() == x.neg().neg().meet(&y.neg())
}

/// h13: neg-join de Morgan — `x.join(y).neg() == x.neg().meet(y.neg())`
pub fn heyting_neg_join_de_morgan<T: Heyting + Eq>(x: &T, y: &T) -> bool {
    x.join(y).neg() == x.neg().meet(&y.neg())
}

/// h14: non-contradiction — `x.meet(x.neg()) == bot`
pub fn heyting_non_contradiction<T: Heyting + Eq>(x: &T) -> bool {
    x.meet(&x.neg()) == T::bot()
}

/// h15: triple neg — `x.neg().neg().neg() == x.neg()`
pub fn heyting_triple_neg<T: Heyting + Eq>(x: &T) -> bool {
    x.neg().neg().neg() == x.neg()
}

/// h16: double neg mid — `x.neg().neg().mid() == top`
pub fn heyting_double_neg_mid<T: Heyting + Eq>(x: &T) -> bool {
    x.neg().neg().mid() == T::top()
}

/// h17: double neg monad — `x ⊑ x.neg().neg()`
pub fn heyting_double_neg_monad<T: Heyting>(x: &T) -> bool {
    *x <= x.neg().neg()
}

// ── Coheyting (c0–c20) ───────────────────────────────────────────

/// c0: adjunction — `x.coimp(y) ⊑ z ⟺ x ⊑ y.join(z)`
pub fn coheyting_adjunction<T: Coheyting + Eq>(x: &T, y: &T, z: &T) -> bool {
    (x.coimp(y) <= *z) == (*x <= y.join(z))
}

/// c1: coimp monotone (meet in 1st arg)
pub fn coheyting_coimp_mono_meet_1st<T: Coheyting>(x: &T, y: &T, z: &T) -> bool {
    x.meet(z).coimp(y) <= x.coimp(y)
}

/// c2: coimp antitone (meet in 2nd arg)
pub fn coheyting_coimp_anti_meet_2nd<T: Coheyting>(x: &T, y: &T, z: &T) -> bool {
    x.coimp(y) <= x.coimp(&y.meet(z))
}

/// c3: coimp monotone (ple in 1st arg)
pub fn coheyting_coimp_mono_ple_1st<T: Coheyting>(x: &T, y: &T, z: &T) -> bool {
    if *y <= *x {
        y.coimp(z) <= x.coimp(z)
    } else {
        true
    }
}

/// c4: co-currying — `z.coimp(x.join(y)) == z.coimp(x).coimp(y)`
pub fn coheyting_co_currying<T: Coheyting + Eq>(x: &T, y: &T, z: &T) -> bool {
    z.coimp(&x.join(y)) == z.coimp(x).coimp(y)
}

/// c5: coimp distributes over join
pub fn coheyting_coimp_dist_join<T: Coheyting + Eq>(x: &T, y: &T, z: &T) -> bool {
    y.join(z).coimp(x) == y.coimp(x).join(&z.coimp(x))
}

/// c6: coimp ⊑ self
pub fn coheyting_coimp_le_self<T: Coheyting>(x: &T, y: &T) -> bool {
    x.coimp(y) <= *x
}

/// c7: join absorption
pub fn coheyting_join_absorption<T: Coheyting + Eq>(x: &T, y: &T) -> bool {
    x.join(&y.coimp(x)) == x.join(y)
}

/// c9: meet-coneg ≥ coimp
pub fn coheyting_meet_coneg_ge_coimp<T: Coheyting>(x: &T, y: &T) -> bool {
    x.coimp(y) <= x.meet(&y.coneg())
}

/// c10: coimp = bot iff ⊑
pub fn coheyting_coimp_bot_iff_ple<T: Coheyting + Eq>(x: &T, y: &T) -> bool {
    (*y <= *x) == (y.coimp(x) == T::bot())
}

/// c11: coneg antitone under meet
pub fn coheyting_coneg_anti_meet<T: Coheyting>(x: &T, y: &T) -> bool {
    x.coneg() <= x.meet(y).coneg()
}

/// c12: coneg-coimp de Morgan
pub fn coheyting_coneg_coimp_de_morgan<T: Coheyting + Eq>(x: &T, y: &T) -> bool {
    y.coimp(x).coneg() == x.coneg().coneg().join(&y.coneg())
}

/// c13: coneg-meet de Morgan
pub fn coheyting_coneg_meet_de_morgan<T: Coheyting + Eq>(x: &T, y: &T) -> bool {
    x.meet(y).coneg() == x.coneg().join(&y.coneg())
}

/// c14: excluded middle — `x.join(x.coneg()) == top`
pub fn coheyting_excluded_middle<T: Coheyting + Eq>(x: &T) -> bool {
    x.join(&x.coneg()) == T::top()
}

/// c15: triple coneg
pub fn coheyting_triple_coneg<T: Coheyting + Eq>(x: &T) -> bool {
    x.coneg().coneg().coneg() == x.coneg()
}

/// c16: double coneg comid — `x.comid().coneg().coneg() == bot`
pub fn coheyting_double_coneg_comid<T: Coheyting + Eq>(x: &T) -> bool {
    x.comid().coneg().coneg() == T::bot()
}

/// c17: double coneg comonad — `x.coneg().coneg() ⊑ x`
pub fn coheyting_double_coneg_comonad<T: Coheyting>(x: &T) -> bool {
    x.coneg().coneg() <= *x
}

/// c18: comid decomposition — `x == x.comid().join(x.coneg().coneg())`
pub fn coheyting_comid_decomp<T: Coheyting + Eq>(x: &T) -> bool {
    *x == x.comid().join(&x.coneg().coneg())
}

/// c19: Leibniz rule
pub fn coheyting_leibniz<T: Coheyting + Eq>(x: &T, y: &T) -> bool {
    x.meet(y).comid() == x.comid().meet(y).join(&x.meet(&y.comid()))
}

/// c20: comid additivity
pub fn coheyting_comid_additive<T: Coheyting + Eq>(x: &T, y: &T) -> bool {
    x.join(y).comid().join(&x.meet(y).comid()) == x.comid().join(&y.comid())
}

// ── Bi-Heyting (s1) ──────────────────────────────────────────────

/// s1: neg ⊑ coneg (Biheyting — requires both Heyting + Coheyting)
pub fn biheyting_neg_le_coneg<T: Heyting + Coheyting>(x: &T) -> bool {
    x.neg() <= x.coneg()
}

// ── Symmetric (symmetric1–symmetric13) ───────────────────────────

use crate::lattice::{Symmetric, convl, convr};

/// symmetric1: `not(not(x)) == x` (involution)
pub fn symmetric_involution<T: Symmetric + Eq>(x: &T) -> bool {
    x.not().not() == *x
}

/// symmetric2: `neg(neg(x)) == convr(convl(x))`
pub fn symmetric_double_neg_eq_convrl<T: Symmetric + Eq>(x: &T) -> bool {
    x.neg().neg() == convr(&convl(x))
}

/// symmetric3: `coneg(coneg(x)) == convl(convr(x))`
pub fn symmetric_double_coneg_eq_convlr<T: Symmetric + Eq>(x: &T) -> bool {
    x.coneg().coneg() == convl(&convr(x))
}

/// symmetric4: `coneg(x) == convl(not(x))` and `neg(x) == not(convl(x))`
pub fn symmetric_coneg_neg_convl<T: Symmetric + Eq>(x: &T) -> bool {
    x.coneg() == convl(&x.not()) && x.neg() == convl(x).not()
}

/// symmetric5: `coneg(x) == not(convr(x))` and `neg(x) == convr(not(x))`
pub fn symmetric_coneg_neg_convr<T: Symmetric + Eq>(x: &T) -> bool {
    x.coneg() == convr(x).not() && x.neg() == convr(&x.not())
}

/// symmetric6: `neg(x).join(neg(neg(x))) == top` (Heyting only)
pub fn symmetric_neg_excluded_middle<T: Heyting + Eq>(x: &T) -> bool {
    x.neg().join(&x.neg().neg()) == T::top()
}

/// symmetric7: de Morgan — `not(x.meet(y)) == not(x).join(not(y))`
pub fn symmetric_not_de_morgan_meet<T: Symmetric + Eq>(x: &T, y: &T) -> bool {
    x.meet(y).not() == x.not().join(&y.not())
}

/// symmetric8: `not(not(x.join(y))) == not(not(x)).join(not(not(y)))`
pub fn symmetric_double_not_join<T: Symmetric + Eq>(x: &T, y: &T) -> bool {
    x.join(y).not().not() == x.not().not().join(&y.not().not())
}

/// symmetric9: de Morgan — `not(x.join(y)) == not(x).meet(not(y))`
pub fn symmetric_not_de_morgan_join<T: Symmetric + Eq>(x: &T, y: &T) -> bool {
    x.join(y).not() == x.not().meet(&y.not())
}

/// symmetric10: `convl(x.join(y)) == convl(x).join(convl(y))`
pub fn symmetric_convl_join<T: Symmetric + Eq>(x: &T, y: &T) -> bool {
    convl(&x.join(y)) == convl(x).join(&convl(y))
}

/// symmetric11: `convr(x.meet(y)) == convr(x).meet(convr(y))`
pub fn symmetric_convr_meet<T: Symmetric + Eq>(x: &T, y: &T) -> bool {
    convr(&x.meet(y)) == convr(x).meet(&convr(y))
}

/// symmetric12: `convl(x.meet(y)) == coneg(coneg(convl(x).meet(convl(y))))`
pub fn symmetric_convl_meet<T: Symmetric + Eq>(x: &T, y: &T) -> bool {
    convl(&x.meet(y)) == convl(x).meet(&convl(y)).coneg().coneg()
}

/// symmetric13: `convr(x.join(y)) == neg(neg(convr(x).join(convr(y))))`
pub fn symmetric_convr_join<T: Symmetric + Eq>(x: &T, y: &T) -> bool {
    convr(&x.join(y)) == convr(x).join(&convr(y)).neg().neg()
}

// ── Boolean (boolean0–boolean6) ──────────────────────────────────

/// boolean0: `neg(x) == coneg(x)` (Biheyting — true iff Boolean)
pub fn boolean_neg_eq_coneg<T: Heyting + Coheyting + Eq>(x: &T) -> bool {
    x.neg() == x.coneg()
}

/// boolean1: `neg(neg(x)) == x` (Heyting — true iff Boolean)
pub fn boolean_double_neg_id<T: Heyting + Eq>(x: &T) -> bool {
    x.neg().neg() == *x
}

/// boolean2: `x.join(x.neg()) == top` (excluded middle)
pub fn boolean_excluded_middle<T: Heyting + Eq>(x: &T) -> bool {
    x.join(&x.neg()) == T::top()
}

/// boolean3: `x.meet(x.coneg()) == bot` (non-contradiction for coneg)
pub fn boolean_non_contradiction<T: Coheyting + Eq>(x: &T) -> bool {
    x.meet(&x.coneg()) == T::bot()
}

/// boolean4: contrapositive — `(x <= y) implies (y.neg() <= x.neg())`
pub fn boolean_contrapositive<T: Heyting>(x: &T, y: &T) -> bool {
    if *x <= *y { y.neg() <= x.neg() } else { true }
}

/// boolean5: `x.coimp(y) == neg(neg(y).imp(neg(x)))` (Biheyting)
pub fn boolean_coimp_from_imp<T: Heyting + Coheyting + Eq>(x: &T, y: &T) -> bool {
    x.coimp(y) == y.neg().imp(&x.neg()).neg()
}

/// boolean6: `x.imp(y) == coneg(coneg(y).coimp(coneg(x)))` (Biheyting)
pub fn boolean_imp_from_coimp<T: Heyting + Coheyting + Eq>(x: &T, y: &T) -> bool {
    x.imp(y) == y.coneg().coimp(&x.coneg()).coneg()
}

// ── Galois-connection laws ───────────────────────────────────────
//
// Predicates take `&Conn<A, B>` plus inputs by value (Conn types in
// this crate are all `Copy`). The bound `Eq + PartialOrd` is the
// lawful framework: `Eq` certifies reflexive `PartialEq`, and
// `PartialOrd` derives a genuine partial order from it. Rust's
// `PartialOrd` alone is too weak (NaN ≠ NaN under raw-float
// `PartialEq` breaks reflexivity); the `Eq` bound is what enforces
// the float fix at the wrapper boundary. Float Conns route through
// `ExtendedFloat<T>`, whose patched `PartialEq` makes `NaN == NaN`
// and is therefore `Eq`.

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

// ── Cast lifter laws (for `conn::cast::*`) ───────────────────────
//
// These predicates exercise the lifter free functions (`upper1`,
// `ceiling1`, etc.) in `conn::cast`. The underlying algebraic laws
// (closure / kernel / monotonicity) are already covered by the
// `conn_*` predicates above; these add a thin layer that catches
// mis-delegation in the lifters themselves (e.g. an `upper1` that
// accidentally calls `floor` instead of `ceil` would still typecheck
// but would fail the unit law on a non-degenerate triple).

/// `upper1` unit law: `a ≤ upper1(c, id, a)`. Equivalent to
/// [`conn_closure_l`] routed through the lifter.
pub fn cast_upper1_id_unit<A: Copy + PartialOrd, B: Copy>(c: &Conn<A, B>, a: A) -> bool {
    a <= crate::conn::cast::upper1(c, |x| x, a)
}

/// `lower1` counit law: `lower1(c, id, a) ≤ a`. Equivalent to
/// [`conn_closure_r`] routed through the lifter.
pub fn cast_lower1_id_counit<A: Copy + PartialOrd, B: Copy>(c: &Conn<A, B>, a: A) -> bool {
    crate::conn::cast::lower1(c, |x| x, a) <= a
}

/// `ceiling1` kernel law: `ceiling1(c, id, b) ≤ b`. Equivalent to
/// [`conn_kernel_l`] routed through the lifter.
pub fn cast_ceiling1_id_kernel<A: Copy, B: Copy + PartialOrd>(c: &Conn<A, B>, b: B) -> bool {
    crate::conn::cast::ceiling1(c, |x| x, b) <= b
}

/// `floor1` kernel law: `b ≤ floor1(c, id, b)`. Equivalent to
/// [`conn_kernel_r`] routed through the lifter.
pub fn cast_floor1_id_kernel<A: Copy, B: Copy + PartialOrd>(c: &Conn<A, B>, b: B) -> bool {
    b <= crate::conn::cast::floor1(c, |x| x, b)
}

/// `upper2` collapse-on-projection: when called with the
/// first-projection `|p, _| p` on equal args `(a, a)`, `upper2`
/// equals `upper1` with `id`. This is a narrow consistency check on
/// the lifter, **not** a general diagonal law; for arbitrary `f`,
/// the broader `upper2(c, f, a, a) == upper1(c, |b| f(b, b), a)`
/// would require `f` to be supplied as a parameter.
pub fn cast_upper2_id_diag<A: Copy + Eq, B: Copy>(c: &Conn<A, B>, a: A) -> bool {
    let l = crate::conn::cast::upper2(c, |p, _q| p, a, a);
    let r = crate::conn::cast::upper1(c, |x| x, a);
    l == r
}

/// `lower2` collapse-on-projection: dual of [`cast_upper2_id_diag`]
/// — narrow check that `lower2(c, |p, _| p, a, a) == lower1(c, id, a)`.
pub fn cast_lower2_id_diag<A: Copy + Eq, B: Copy>(c: &Conn<A, B>, a: A) -> bool {
    let l = crate::conn::cast::lower2(c, |p, _q| p, a, a);
    let r = crate::conn::cast::lower1(c, |x| x, a);
    l == r
}

/// `ceiling2` collapse-on-projection: with `|p, _| p` on `(b, b)`,
/// equals `ceiling1` with `id`. Narrow check, see
/// [`cast_upper2_id_diag`] for why.
pub fn cast_ceiling2_id_diag<A: Copy, B: Copy + Eq>(c: &Conn<A, B>, b: B) -> bool {
    let l = crate::conn::cast::ceiling2(c, |p, _q| p, b, b);
    let r = crate::conn::cast::ceiling1(c, |x| x, b);
    l == r
}

/// `floor2` collapse-on-projection: dual of [`cast_ceiling2_id_diag`].
pub fn cast_floor2_id_diag<A: Copy, B: Copy + Eq>(c: &Conn<A, B>, b: B) -> bool {
    let l = crate::conn::cast::floor2(c, |p, _q| p, b, b);
    let r = crate::conn::cast::floor1(c, |x| x, b);
    l == r
}

/// `maximize` is the curried form of `ceiling` over a `Conn<(A, B), C>`:
/// `maximize(c, a, b) == ceiling(c, (a, b))`.
pub fn cast_maximize_eq_ceiling<A: Copy, B: Copy, C: Copy + Eq>(
    c: &Conn<(A, B), C>,
    a: A,
    b: B,
) -> bool {
    let l = crate::conn::cast::maximize(c, a, b);
    let r = crate::conn::cast::ceiling(c, (a, b));
    l == r
}

/// `minimize` is the curried form of `floor` over a `Conn<(A, B), C>`:
/// `minimize(c, a, b) == floor(c, (a, b))`.
pub fn cast_minimize_eq_floor<A: Copy, B: Copy, C: Copy + Eq>(
    c: &Conn<(A, B), C>,
    a: A,
    b: B,
) -> bool {
    let l = crate::conn::cast::minimize(c, a, b);
    let r = crate::conn::cast::floor(c, (a, b));
    l == r
}

// ── Two-sided helper laws (for `conn::cast::{interval, midpoint,
//    round, truncate, median}` and friends) ─────────────────────

/// `interval` evaluated at the conn's midpoint resolves to
/// `Some(Equal)` (or `None` if the source values are NaN-bearing).
/// Mirrors Haskell `Cast.hs` doctest:
/// `interval c (midpoint c x) == Just EQ`.
pub fn cast_interval_at_midpoint_eq_or_none<A, B>(c: &Conn<A, B>, x: A) -> bool
where
    A: Copy
        + PartialOrd
        + core::ops::Add<Output = A>
        + core::ops::Sub<Output = A>
        + core::ops::Div<Output = A>
        + From<u8>,
{
    use core::cmp::Ordering;
    let mid = crate::conn::cast::midpoint(c, x);
    let result = crate::conn::cast::interval(c, mid);
    matches!(result, None | Some(Ordering::Equal))
}

/// `midpoint(c, x)` lies between `c.inner(c.floor(x))` and
/// `c.inner(c.ceil(x))` whenever those two are themselves comparable.
/// On saturating Conns the bracket can flip; the predicate returns
/// `true` vacuously when `lo > hi` (consistent with the
/// `conn_floor_le_ceil` precedent for injective-`inner` checks).
pub fn cast_midpoint_between<A, B>(c: &Conn<A, B>, x: A) -> bool
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
    let mid = crate::conn::cast::midpoint(c, x);
    if lo <= hi {
        lo <= mid && mid <= hi
    } else {
        true
    }
}

/// `round(c, x)` is always one of `c.ceil(x)` / `c.floor(x)` (since
/// every dispatch arm of [`crate::conn::cast::round`] returns one or
/// the other directly).
pub fn cast_round_picks_endpoint<A, B>(c: &Conn<A, B>, x: A) -> bool
where
    A: Copy + PartialOrd + core::ops::Sub<Output = A> + From<u8>,
    B: Copy + Eq,
{
    let r = crate::conn::cast::round(c, x);
    r == c.ceil(x) || r == c.floor(x)
}

/// `truncate(c, x)` is always one of `c.ceil(x)` / `c.floor(x)`.
pub fn cast_truncate_picks_endpoint<A, B>(c: &Conn<A, B>, x: A) -> bool
where
    A: Copy + PartialOrd + From<u8>,
    B: Copy + Eq,
{
    let t = crate::conn::cast::truncate(c, x);
    t == c.ceil(x) || t == c.floor(x)
}

/// Toward-zero contract: `x ≥ 0 ⟹ truncate = floor`,
/// otherwise (including the NaN-bearing case where `x ≥ 0` is false)
/// `truncate = ceil`.
pub fn cast_truncate_toward_zero<A, B>(c: &Conn<A, B>, x: A) -> bool
where
    A: Copy + PartialOrd + From<u8>,
    B: Copy + Eq,
{
    let zero = A::from(0);
    let t = crate::conn::cast::truncate(c, x);
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
/// over a non-identity triple (e.g. `FD12FD09`) produces spurious
/// failures whenever `x` does not already lie on a representable
/// rung — those are not law violations. For non-identity Conns,
/// use [`cast_round_picks_endpoint`] instead.
pub fn cast_round1_id_unit<A, B>(c: &Conn<A, B>, x: B) -> bool
where
    A: Copy + PartialOrd + core::ops::Sub<Output = A> + From<u8>,
    B: Copy + Eq,
{
    crate::conn::cast::round1(c, |a| a, x) == x
}

/// `truncate1(c, id, x) == x` for an identity Conn (Haskell axiom
/// `truncate1 identity = id`). Same caveats as
/// [`cast_round1_id_unit`].
///
/// # Warning
///
/// Only reliable as a law predicate for **identity Conns**. For
/// non-identity Conns, use [`cast_truncate_picks_endpoint`] —
/// driving this predicate elsewhere produces spurious failures
/// that are not law violations.
pub fn cast_truncate1_id_unit<A, B>(c: &Conn<A, B>, x: B) -> bool
where
    A: Copy + PartialOrd + From<u8>,
    B: Copy + Eq,
{
    crate::conn::cast::truncate1(c, |a| a, x) == x
}

/// Birkhoff median axiom 1: `median(c, x, x, y) == x`.
pub fn cast_median_idempotent<A>(c: &Conn<(A, A), A>, x: A, y: A) -> bool
where
    A: Copy + Eq,
{
    crate::conn::cast::median(c, x, x, y) == x
}

/// Birkhoff median axiom 2 (rotation):
/// `median(c, x, y, z) == median(c, z, x, y)`.
pub fn cast_median_rotate<A>(c: &Conn<(A, A), A>, x: A, y: A, z: A) -> bool
where
    A: Copy + Eq,
{
    crate::conn::cast::median(c, x, y, z) == crate::conn::cast::median(c, z, x, y)
}

/// Birkhoff median axiom 3 (last-two swap):
/// `median(c, x, y, z) == median(c, x, z, y)`.
pub fn cast_median_swap_yz<A>(c: &Conn<(A, A), A>, x: A, y: A, z: A) -> bool
where
    A: Copy + Eq,
{
    crate::conn::cast::median(c, x, y, z) == crate::conn::cast::median(c, x, z, y)
}

// ── Bare partial-order laws (for any `T: Eq + PartialOrd`) ──────
//
// These predicates are diagnostic: a violation indicates the type
// fails the `Eq + PartialOrd` contract. Standard library types
// (`i64`, `String`) trivially satisfy them; the `ExtendedFloat<T>`
// wrapper does too because its `PartialEq` is patched to be
// reflexive at NaN. Raw `f64`/`f32` cannot impl `Eq` (NaN ≠ NaN),
// so they are excluded from these predicates by the type system.

/// Reflexivity: `x ≤ x`. Trivial under `Eq + PartialOrd` because
/// `Eq` certifies `x == x`, and `PartialOrd::le` returns `true` on
/// equal values.
#[allow(clippy::eq_op)] // `x <= x` is the law we're checking, not redundant.
pub fn lattice_reflexive<T: PartialOrd>(x: &T) -> bool {
    x <= x
}

/// Transitivity: `x ≤ y ∧ y ≤ z ⟹ x ≤ z`.
pub fn lattice_transitive<T: PartialOrd>(x: &T, y: &T, z: &T) -> bool {
    if x <= y && y <= z { x <= z } else { true }
}

/// Antisymmetry: `x ≤ y ∧ y ≤ x ⟹ x = y`. With `Eq + PartialOrd`
/// this is the standard partial-order axiom.
pub fn lattice_antisymmetric<T: Eq + PartialOrd>(x: &T, y: &T) -> bool {
    if x <= y && y <= x { x == y } else { true }
}

/// Bottom: `bot ≤ x` for every `x`.
pub fn lattice_bot<T: PartialOrd>(bot: &T, x: &T) -> bool {
    bot <= x
}

/// Top: `x ≤ top` for every `x`.
pub fn lattice_top<T: PartialOrd>(top: &T, x: &T) -> bool {
    x <= top
}
