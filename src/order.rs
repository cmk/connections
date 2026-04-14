/// N5 lattice partial order for IEEE 754 floats.
///
/// Extends the standard float ordering so that:
/// - NaN is reflexive: `ple(NaN, NaN)` is true
/// - NaN is below +∞: `ple(NaN, +∞)` is true
/// - NaN is above -∞: `ple(-∞, NaN)` is true
/// - NaN is incomparable with all finite values and with each ±∞ in the other direction
///
/// This recovers the N5 lattice shape used in the Haskell `connections` library.
/// Partial less-or-equal under the N5 lattice ordering.
pub trait Ple {
    fn ple(&self, other: &Self) -> bool;
}

impl Ple for f32 {
    fn ple(&self, other: &Self) -> bool {
        n5_le_f32(*self, *other)
    }
}

impl Ple for f64 {
    fn ple(&self, other: &Self) -> bool {
        n5_le_f64(*self, *other)
    }
}

/// N5 ordering for f32.
fn n5_le_f32(x: f32, y: f32) -> bool {
    if x.is_nan() && y.is_nan() {
        true
    } else if x.is_nan() {
        y == f32::INFINITY
    } else if y.is_nan() {
        x == f32::NEG_INFINITY
    } else {
        x <= y
    }
}

/// N5 ordering for f64.
fn n5_le_f64(x: f64, y: f64) -> bool {
    if x.is_nan() && y.is_nan() {
        true
    } else if x.is_nan() {
        y == f64::INFINITY
    } else if y.is_nan() {
        x == f64::NEG_INFINITY
    } else {
        x <= y
    }
}

// Blanket impls for totally ordered types — ple is just <=.
impl Ple for i8 { fn ple(&self, other: &Self) -> bool { self <= other } }
impl Ple for i16 { fn ple(&self, other: &Self) -> bool { self <= other } }
impl Ple for i32 { fn ple(&self, other: &Self) -> bool { self <= other } }
impl Ple for i64 { fn ple(&self, other: &Self) -> bool { self <= other } }
impl Ple for u8 { fn ple(&self, other: &Self) -> bool { self <= other } }
impl Ple for u16 { fn ple(&self, other: &Self) -> bool { self <= other } }
impl Ple for u32 { fn ple(&self, other: &Self) -> bool { self <= other } }
impl Ple for u64 { fn ple(&self, other: &Self) -> bool { self <= other } }

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    // ── Strategies ─────────────────────────────────────────────────

    fn arb_f32() -> impl Strategy<Value = f32> {
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

    fn arb_f64() -> impl Strategy<Value = f64> {
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

    // ── Spot checks ────────────────────────────────────────────────

    #[test]
    fn nan_reflexive_f32() {
        assert!(f32::NAN.ple(&f32::NAN));
    }

    #[test]
    fn nan_reflexive_f64() {
        assert!(f64::NAN.ple(&f64::NAN));
    }

    #[test]
    fn nan_below_pos_inf_f64() {
        assert!(f64::NAN.ple(&f64::INFINITY));
    }

    #[test]
    fn neg_inf_below_nan_f64() {
        assert!(f64::NEG_INFINITY.ple(&f64::NAN));
    }

    #[test]
    fn nan_incomparable_with_finite_f64() {
        assert!(!f64::NAN.ple(&1.0));
        assert!(!1.0_f64.ple(&f64::NAN));
    }

    #[test]
    fn nan_not_below_neg_inf() {
        assert!(!f64::NAN.ple(&f64::NEG_INFINITY));
    }

    #[test]
    fn pos_inf_not_below_nan() {
        assert!(!f64::INFINITY.ple(&f64::NAN));
    }

    #[test]
    fn normal_ordering_preserved() {
        assert!(1.0_f64.ple(&2.0));
        assert!(!2.0_f64.ple(&1.0));
        assert!(f64::NEG_INFINITY.ple(&f64::INFINITY));
    }

    // ── Preorder property tests (f64) ──────────────────────────────

    proptest! {
        #[test]
        fn prop_reflexive_f64(x in arb_f64()) {
            prop_assert!(x.ple(&x), "reflexivity failed for {x}");
        }

        #[test]
        fn prop_reflexive_f32(x in arb_f32()) {
            prop_assert!(x.ple(&x), "reflexivity failed for {x}");
        }

        #[test]
        fn prop_transitive_f64(x in arb_f64(), y in arb_f64(), z in arb_f64()) {
            // x ≤ y ∧ y ≤ z ⟹ x ≤ z
            if x.ple(&y) && y.ple(&z) {
                prop_assert!(x.ple(&z),
                    "transitivity failed: {x} ≤ {y} ≤ {z} but not {x} ≤ {z}");
            }
        }

        #[test]
        fn prop_transitive_f32(x in arb_f32(), y in arb_f32(), z in arb_f32()) {
            if x.ple(&y) && y.ple(&z) {
                prop_assert!(x.ple(&z),
                    "transitivity failed: {x} ≤ {y} ≤ {z} but not {x} ≤ {z}");
            }
        }

        #[test]
        fn prop_antisymmetric_f64(x in arb_f64(), y in arb_f64()) {
            // x ≤ y ∧ y ≤ x ⟹ x ~~ y (equivalent under the preorder)
            // For floats, "equivalent" means both ple directions hold — which is
            // the premise, so this is trivially true. The stronger check: if
            // x ≤ y ∧ y ≤ x, then for any z, x ≤ z ⟺ y ≤ z.
            if x.ple(&y) && y.ple(&x) {
                // x and y are equivalent — they should be interchangeable
                // Test with a few witnesses.
                prop_assert_eq!(x.ple(&f64::INFINITY), y.ple(&f64::INFINITY));
                prop_assert_eq!(x.ple(&f64::NEG_INFINITY), y.ple(&f64::NEG_INFINITY));
                prop_assert_eq!(f64::INFINITY.ple(&x), f64::INFINITY.ple(&y));
                prop_assert_eq!(f64::NEG_INFINITY.ple(&x), f64::NEG_INFINITY.ple(&y));
            }
        }

        #[test]
        fn prop_bot_f64(x in arb_f64()) {
            // -∞ is bottom among comparable elements
            // Under N5, -∞ ≤ everything (including NaN)
            prop_assert!(f64::NEG_INFINITY.ple(&x),
                "-∞ should be ≤ {x}");
        }

        #[test]
        fn prop_top_f64(x in arb_f64()) {
            // +∞ is top among comparable elements
            // Under N5, everything ≤ +∞ (including NaN)
            prop_assert!(x.ple(&f64::INFINITY),
                "{x} should be ≤ +∞");
        }

        #[test]
        fn prop_bot_f32(x in arb_f32()) {
            prop_assert!(f32::NEG_INFINITY.ple(&x));
        }

        #[test]
        fn prop_top_f32(x in arb_f32()) {
            prop_assert!(x.ple(&f32::INFINITY));
        }
    }
}
