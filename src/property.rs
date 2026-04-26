#![allow(dead_code)]
//! Shared proptest strategies.
//!
//! Centralizes the `arb_f32` / `arb_f64` generators that `conn/*`,
//! `lattice`, and test modules used to reinvent separately. Two
//! variants are provided:
//!
//! - [`arb_f32`] / [`arb_f64`] — 4:1 uniform-to-boundary bias over
//!   the full float domain. Boundary slot includes NaN, ±∞, ±0,
//!   MIN_POSITIVE, MAX, MIN with equal weight. Use for connections
//!   whose source and target are both float-shaped (`f64 ↔ f32`,
//!   identity on floats, preorder tests).
//! - [`arb_f32_bounded`] / [`arb_f64_bounded`] — 6:1 uniform-to-
//!   boundary bias restricted to `|x| ≤ 1e9` plus the same explicit
//!   boundary set. Use for connections that feed into a bounded
//!   integer rung (Micro, Pico, …); unbounded `any::<f{32,64}>()`
//!   shrinks bit-by-bit through the mantissa on saturation
//!   failures, exploring the `i64::MAX × PREC` corner of the input
//!   space for minutes while teaching nothing about the adjoint
//!   law. See `doc/plans/plan-2026-04-23-05.md` for the discussion.
//!
//! Tier-specific strategies (`arb_extended_micro`,
//! `arb_extended_float_f64`, `bounded_coarse`, …) stay colocated
//! with their tier since they depend on tier types.

use proptest::prelude::*;

/// Arbitrary `f64` with elevated-frequency boundary cases.
///
/// 4:1 weight — four arbitrary bit patterns for every one boundary
/// value. The boundary `prop_oneof!` picks uniformly among
/// `{NaN, ±∞, ±0, MIN_POSITIVE, MAX, MIN}`.
pub fn arb_f64() -> impl Strategy<Value = f64> {
    prop_oneof![
        4 => any::<f64>(),
        1 => prop_oneof![
            Just(f64::NAN),
            Just(f64::INFINITY),
            Just(f64::NEG_INFINITY),
            Just(0.0_f64),
            Just(-0.0_f64),
            Just(f64::MIN_POSITIVE),
            Just(f64::MAX),
            Just(f64::MIN),
        ],
    ]
}

/// Arbitrary `f32` with elevated-frequency boundary cases.
///
/// Same shape as [`arb_f64`]: 4:1 arbitrary-to-boundary ratio.
pub fn arb_f32() -> impl Strategy<Value = f32> {
    prop_oneof![
        4 => any::<f32>(),
        1 => prop_oneof![
            Just(f32::NAN),
            Just(f32::INFINITY),
            Just(f32::NEG_INFINITY),
            Just(0.0_f32),
            Just(-0.0_f32),
            Just(f32::MIN_POSITIVE),
            Just(f32::MAX),
            Just(f32::MIN),
        ],
    ]
}

/// Arbitrary `f64` bounded to `|x| ≤ 1e9` plus the full boundary set.
///
/// Use this instead of [`arb_f64`] for connections whose target is a
/// bounded integer rung (Micro, Nano, Pico, …). The uniform slot is
/// a finite range rather than `any::<f64>()`, which prevents the
/// mantissa-bit shrink pathology on saturation failures. 6:1 ratio
/// keeps the boundary coverage comparable to [`arb_f64`]'s 4:1
/// despite the narrower uniform distribution.
pub fn arb_f64_bounded() -> impl Strategy<Value = f64> {
    prop_oneof![
        6 => -1.0e9_f64..1.0e9_f64,
        1 => prop_oneof![
            Just(f64::NAN),
            Just(f64::INFINITY),
            Just(f64::NEG_INFINITY),
            Just(0.0_f64),
            Just(-0.0_f64),
            Just(f64::MIN_POSITIVE),
            Just(f64::MAX),
            Just(f64::MIN),
        ],
    ]
}

// `arb_f32_bounded` is intentionally omitted: no current connection
// saturates f32 into a bounded integer rung. Add it (mirroring
// `arb_f64_bounded` above) when an F32F?? or similar conn appears.

// ── Lattice property test functions ──────────────────────────────
//
// Generic test predicates ported from `Data.Lattice.Property`. Each
// takes trait-bounded values by reference and returns `bool`.
// Downstream crates instantiate them in `proptest!` blocks with
// their own strategies.
//
// Naming: `heyting_*` for Heyting laws, `coheyting_*` for co-Heyting,
// `biheyting_*` for laws requiring both.
//
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

/// h8: neg boundary values — `bot.neg() == top && top.neg() == bot`
pub fn heyting_neg_boundary<T: Heyting + Eq>() -> bool {
    T::bot().neg() == T::top() && T::top().neg() == T::bot()
}

/// c8: coneg boundary values — `bot.coneg() == top && top.coneg() == bot`
pub fn coheyting_coneg_boundary<T: Coheyting + Eq>() -> bool {
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
    x.coneg() == convl(&x.not()) && x.neg() == x.not().coneg()
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
