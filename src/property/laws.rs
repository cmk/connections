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
//! laws and bare-preorder laws (added in subsequent commits of the
//! property tidy-up sprint).

#![allow(dead_code)]

use crate::conn::Conn;
use crate::lattice::{Coheyting, Heyting, Ple};

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
    if *x <= *y {
        y.neg() <= x.neg()
    } else {
        true
    }
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
// this crate are all `Copy`). `Ple`-bound for uniformity across
// integer rungs and float ExtendedFloat. Downstream wraps in
// `prop_assert!` in their own proptest blocks.

/// Galois law (left): `ceil(a) ≤ b ⟺ a ≤ inner(b)`.
pub fn conn_galois_l<A: Copy + Ple, B: Copy + Ple>(c: &Conn<A, B>, a: A, b: B) -> bool {
    c.ceil(a).ple(&b) == a.ple(&c.inner(b))
}

/// Galois law (right): `inner(b) ≤ a ⟺ b ≤ floor(a)`.
pub fn conn_galois_r<A: Copy + Ple, B: Copy + Ple>(c: &Conn<A, B>, a: A, b: B) -> bool {
    c.inner(b).ple(&a) == b.ple(&c.floor(a))
}

/// Closure law (left): `a ≤ inner(ceil(a))` — the unit of the
/// `inner ⊣ ceil` adjunction.
pub fn conn_closure_l<A: Copy + Ple, B: Copy>(c: &Conn<A, B>, a: A) -> bool {
    a.ple(&c.inner(c.ceil(a)))
}

/// Closure law (right): `inner(floor(a)) ≤ a` — the dual of [`conn_closure_l`].
pub fn conn_closure_r<A: Copy + Ple, B: Copy>(c: &Conn<A, B>, a: A) -> bool {
    c.inner(c.floor(a)).ple(&a)
}

/// Kernel law (left): `ceil(inner(b)) ≤ b` — the counit of the
/// `inner ⊣ ceil` adjunction.
pub fn conn_kernel_l<A: Copy, B: Copy + Ple>(c: &Conn<A, B>, b: B) -> bool {
    c.ceil(c.inner(b)).ple(&b)
}

/// Kernel law (right): `b ≤ floor(inner(b))` — the dual of [`conn_kernel_l`].
pub fn conn_kernel_r<A: Copy, B: Copy + Ple>(c: &Conn<A, B>, b: B) -> bool {
    b.ple(&c.floor(c.inner(b)))
}

/// Monotonicity (left): `a1 ≤ a2 ⟹ ceil(a1) ≤ ceil(a2) ∧ floor(a1) ≤ floor(a2)`.
pub fn conn_monotone_l<A: Copy + Ple, B: Copy + Ple>(
    c: &Conn<A, B>,
    a1: A,
    a2: A,
) -> bool {
    if a1.ple(&a2) {
        c.ceil(a1).ple(&c.ceil(a2)) && c.floor(a1).ple(&c.floor(a2))
    } else {
        true
    }
}

/// Monotonicity (right): `b1 ≤ b2 ⟹ inner(b1) ≤ inner(b2)`.
pub fn conn_monotone_r<A: Copy + Ple, B: Copy + Ple>(
    c: &Conn<A, B>,
    b1: B,
    b2: B,
) -> bool {
    if b1.ple(&b2) {
        c.inner(b1).ple(&c.inner(b2))
    } else {
        true
    }
}

/// Idempotence: `(inner ∘ ceil) ∘ (inner ∘ ceil) = inner ∘ ceil` —
/// the closure operator is idempotent on its image.
pub fn conn_idempotent<A: Copy + Eq, B: Copy>(c: &Conn<A, B>, a: A) -> bool {
    let once = c.inner(c.ceil(a));
    let twice = c.inner(c.ceil(once));
    once == twice
}

/// `floor(a) ≤ ceil(a)` — the floor never exceeds the ceiling.
pub fn conn_floor_le_ceil<A: Copy, B: Copy + Ple>(c: &Conn<A, B>, a: A) -> bool {
    c.floor(a).ple(&c.ceil(a))
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
pub fn conn_ulp_bound<A, B, F>(c: &Conn<A, B>, a: A, rung: F) -> bool
where
    A: Copy,
    B: Copy,
    F: Fn(B) -> i64,
{
    let c_val = rung(c.ceil(a));
    let f_val = rung(c.floor(a));
    c_val >= f_val && c_val - f_val <= 1
}

// ── Bare-preorder laws (for types impl'ing `Ple`) ────────────────

/// Reflexivity: `x ≤ x` — every element is comparable to itself.
pub fn lattice_reflexive<T: Ple>(x: &T) -> bool {
    x.ple(x)
}

/// Transitivity: `x ≤ y ∧ y ≤ z ⟹ x ≤ z`.
pub fn lattice_transitive<T: Ple>(x: &T, y: &T, z: &T) -> bool {
    if x.ple(y) && y.ple(z) {
        x.ple(z)
    } else {
        true
    }
}

/// Antisymmetry under preorder equivalence: if `x ≤ y` and `y ≤ x`
/// then `x` and `y` are interchangeable in every `ple` comparison
/// against the supplied probes (typically `top` and `bot` of the
/// type's lattice). For float `Ple` (the N5 lattice), where
/// `NaN.ple(NaN)` is true but NaN ≠ any finite, this expresses the
/// preorder equivalence class without demanding `Eq`.
pub fn lattice_antisymmetric<T: Ple>(x: &T, y: &T, top: &T, bot: &T) -> bool {
    if x.ple(y) && y.ple(x) {
        x.ple(top) == y.ple(top)
            && x.ple(bot) == y.ple(bot)
            && top.ple(x) == top.ple(y)
            && bot.ple(x) == bot.ple(y)
    } else {
        true
    }
}

/// Bottom: `bot ≤ x` for every `x`.
pub fn lattice_bot<T: Ple>(bot: &T, x: &T) -> bool {
    bot.ple(x)
}

/// Top: `x ≤ top` for every `x`.
pub fn lattice_top<T: Ple>(top: &T, x: &T) -> bool {
    x.ple(top)
}
