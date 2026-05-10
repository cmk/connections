//! Conns sourced from [`super::F032`] (`ExtendedFloat<f32>`).
//!
//! Houses:
//!
//! - `F032F016` (`ExtendedFloat<f32> -> ExtendedFloat<f16>`) — float
//!   narrowing, behind the `f16` cargo feature.
//! - `F032U008` / `F032U016` / `F032I008` / `F032I016` — Float to
//!   `Extended<intN>` adjoint triples (target fits losslessly in the
//!   f32 mantissa, so a true Galois triple exists).
//! - `F032U032` / `F032U064` / `F032I032` / `F032I064` — Float to
//!   `Extended<intN>` left-only Conns (target precision exceeds the
//!   f32 mantissa, so `inner` is not order-reflecting and only the
//!   L-Galois adjunction holds).

#[cfg(feature = "f16")]
use super::f016::{F016, ceil_f32_f16, floor_f32_f16};
#[cfg(feature = "f16")]
use super::{ExtendedFloat, F032};
use super::{float_ext_int, float_ext_int_l};

#[cfg(feature = "f16")]
fn f032f016_ceil(x: F032) -> F016 {
    match x {
        ExtendedFloat::Bot => ExtendedFloat::Bot,
        ExtendedFloat::Top => ExtendedFloat::Top,
        ExtendedFloat::Extend(v) => ExtendedFloat::Extend(ceil_f32_f16(v)),
    }
}

#[cfg(feature = "f16")]
fn f032f016_inner(y: F016) -> F032 {
    match y {
        ExtendedFloat::Bot => ExtendedFloat::Bot,
        ExtendedFloat::Top => ExtendedFloat::Top,
        ExtendedFloat::Extend(v) => ExtendedFloat::Extend(v as f32),
    }
}

#[cfg(feature = "f16")]
fn f032f016_floor(x: F032) -> F016 {
    match x {
        ExtendedFloat::Bot => ExtendedFloat::Bot,
        ExtendedFloat::Top => ExtendedFloat::Top,
        ExtendedFloat::Extend(v) => ExtendedFloat::Extend(floor_f32_f16(v)),
    }
}

#[cfg(feature = "f16")]
crate::conn_k! {
    /// Connection between [`super::F032`] (`ExtendedFloat<f32>`) and
    /// [`super::f016::F016`] (`ExtendedFloat<f16>`) under the N5 lattice.
    ///
    /// ```
    /// # #![feature(f16)]
    /// use connections::float::f032::F032F016;
    /// use connections::float::{ExtendedFloat::Extend, F032};
    ///
    /// let pi = Extend(std::f32::consts::PI);
    /// let pi_up = F032F016.ceil(pi);
    /// let pi_down = F032F016.floor(pi);
    /// assert!(F032F016.upper(pi_down) <= pi);
    /// assert!(pi <= F032F016.upper(pi_up));
    ///
    /// let huge: F032 = Extend(f32::MAX);
    /// assert_eq!(F032F016.ceil(huge), Extend(f16::INFINITY));
    /// ```
    pub F032F016 : F032 => F016 {
        ceil:  f032f016_ceil,
        inner: f032f016_inner,
        floor: f032f016_floor,
    }
}

// ── §2: Float → Extended<intN> narrowing ─────────────────────────────
//
// Saturation policy and adjoint shape are documented on the
// `float_ext_int!` / `float_ext_int_l!` macros in `crate::float`.
// Threshold: `i8`/`u8`/`i16`/`u16` fit in the f32 mantissa (24 bits
// incl. implicit) so they ship as full triples; `i32`/`u32`/`i64`/`u64`
// do not, so they ship as L-only.

float_ext_int!  (
    /// `ExtendedFloat<f32> ↔ Extended<u8>` — full Galois triple
    /// (`u8::MAX = 255` fits in the f32 mantissa).
    pub F032U008, f32, u8
);
float_ext_int!  (
    /// `ExtendedFloat<f32> ↔ Extended<u16>` — full Galois triple.
    pub F032U016, f32, u16
);
float_ext_int_l!(
    /// `ExtendedFloat<f32> → Extended<u32>` — L-only (`u32::MAX`
    /// exceeds the f32 mantissa, so distinct large `u32` values can
    /// alias to the same `f32`).
    pub F032U032, f32, u32
);
float_ext_int_l!(
    /// `ExtendedFloat<f32> → Extended<u64>` — L-only.
    pub F032U064, f32, u64
);
float_ext_int!  (
    /// `ExtendedFloat<f32> ↔ Extended<i8>` — full Galois triple.
    pub F032I008, f32, i8
);
float_ext_int!  (
    /// `ExtendedFloat<f32> ↔ Extended<i16>` — full Galois triple.
    pub F032I016, f32, i16
);
float_ext_int_l!(
    /// `ExtendedFloat<f32> → Extended<i32>` — L-only (`i32::MAX`
    /// exceeds the f32 mantissa).
    pub F032I032, f32, i32
);
float_ext_int_l!(
    /// `ExtendedFloat<f32> → Extended<i64>` — L-only.
    pub F032I064, f32, i64
);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::conn::{ConnL, ConnR};
    use crate::extended::Extended;
    use crate::float::ExtendedFloat;
    use crate::prop::arb::{
        arb_extended_i8, arb_extended_i16, arb_extended_i32, arb_extended_i64, arb_extended_u8,
        arb_extended_u16, arb_extended_u32, arb_extended_u64, extended_float_f32,
    };

    // ── Spot checks ─────────────────────────────────────────────────

    #[test]
    fn nan_ceil_pos_inf() {
        assert_eq!(
            F032U008.ceil(ExtendedFloat::Extend(f32::NAN)),
            Extended::PosInf
        );
        assert_eq!(
            F032I008.ceil(ExtendedFloat::Extend(f32::NAN)),
            Extended::PosInf
        );
        assert_eq!(
            F032U064.ceil(ExtendedFloat::Extend(f32::NAN)),
            Extended::PosInf
        );
    }

    #[test]
    fn nan_floor_neg_inf() {
        assert_eq!(
            F032U008.floor(ExtendedFloat::Extend(f32::NAN)),
            Extended::NegInf
        );
        assert_eq!(
            F032I016.floor(ExtendedFloat::Extend(f32::NAN)),
            Extended::NegInf
        );
    }

    #[test]
    fn pos_inf_saturates_via_high_branch() {
        // `Extend(+∞)` matches the `v > hi` branch (since `hi` is
        // finite), so `ceil → PosInf` and `floor → Finite(MAX)`.
        // A separate `v == INFINITY` arm would map `floor → PosInf`
        // and break the Galois law at boundary `(Top, PosInf)`
        // because `inner(PosInf) = Top > Extend(+∞)`.
        assert_eq!(
            F032U008.ceil(ExtendedFloat::Extend(f32::INFINITY)),
            Extended::PosInf
        );
        assert_eq!(
            F032I008.floor(ExtendedFloat::Extend(f32::INFINITY)),
            Extended::Finite(i8::MAX)
        );
    }

    #[test]
    fn neg_inf_saturates_via_low_branch() {
        // Symmetric to `pos_inf_saturates_via_high_branch`:
        // `Extend(-∞)` falls through `v < lo`, so
        // `ceil → Finite(MIN)` (which is 0 for unsigned, MIN for
        // signed) and `floor → NegInf`.
        assert_eq!(
            F032U008.ceil(ExtendedFloat::Extend(f32::NEG_INFINITY)),
            Extended::Finite(0)
        );
        assert_eq!(
            F032I008.ceil(ExtendedFloat::Extend(f32::NEG_INFINITY)),
            Extended::Finite(i8::MIN)
        );
        assert_eq!(
            F032U008.floor(ExtendedFloat::Extend(f32::NEG_INFINITY)),
            Extended::NegInf
        );
        assert_eq!(
            F032I008.floor(ExtendedFloat::Extend(f32::NEG_INFINITY)),
            Extended::NegInf
        );
    }

    #[test]
    fn bot_top_pass_through() {
        assert_eq!(F032U008.ceil(ExtendedFloat::Bot), Extended::NegInf);
        assert_eq!(F032U008.floor(ExtendedFloat::Bot), Extended::NegInf);
        assert_eq!(F032U008.ceil(ExtendedFloat::Top), Extended::PosInf);
        assert_eq!(F032U008.floor(ExtendedFloat::Top), Extended::PosInf);
        // L-only Conns expose ceil and upper but no `floor`.
        assert_eq!(F032I064.ceil(ExtendedFloat::Bot), Extended::NegInf);
        assert_eq!(F032I064.ceil(ExtendedFloat::Top), Extended::PosInf);
    }

    #[test]
    fn saturate_high_unsigned() {
        assert_eq!(
            F032U008.ceil(ExtendedFloat::Extend(300.0_f32)),
            Extended::PosInf
        );
        assert_eq!(
            F032U008.floor(ExtendedFloat::Extend(300.0_f32)),
            Extended::Finite(u8::MAX)
        );
    }

    #[test]
    fn saturate_low_signed() {
        assert_eq!(
            F032I008.ceil(ExtendedFloat::Extend(-200.0_f32)),
            Extended::Finite(i8::MIN)
        );
        assert_eq!(
            F032I008.floor(ExtendedFloat::Extend(-200.0_f32)),
            Extended::NegInf
        );
    }

    #[test]
    fn saturate_low_unsigned() {
        // For `Extend(-1.0)` we have v < 0 = u8::MIN as f32, so
        // `ceil → Finite(MIN) = Finite(0)` and `floor → NegInf`.
        assert_eq!(
            F032U008.ceil(ExtendedFloat::Extend(-1.0_f32)),
            Extended::Finite(0)
        );
        assert_eq!(
            F032U008.floor(ExtendedFloat::Extend(-1.0_f32)),
            Extended::NegInf
        );
    }

    #[test]
    fn exact_integer_round_trip() {
        // For finite v exactly representable as int, ceil = floor = Finite(v).
        assert_eq!(
            F032U008.ceil(ExtendedFloat::Extend(42.0_f32)),
            Extended::Finite(42)
        );
        assert_eq!(
            F032U008.floor(ExtendedFloat::Extend(42.0_f32)),
            Extended::Finite(42)
        );
        assert_eq!(
            F032I016.ceil(ExtendedFloat::Extend(-1234.0_f32)),
            Extended::Finite(-1234)
        );
    }

    #[test]
    fn fraction_brackets_integer() {
        // 2.5 lies between 2 and 3.
        assert_eq!(
            F032I008.ceil(ExtendedFloat::Extend(2.5_f32)),
            Extended::Finite(3)
        );
        assert_eq!(
            F032I008.floor(ExtendedFloat::Extend(2.5_f32)),
            Extended::Finite(2)
        );
    }

    #[test]
    fn inner_round_trip_finite() {
        assert_eq!(
            F032U008.upper(Extended::Finite(42_u8)),
            ExtendedFloat::Extend(42.0_f32),
        );
        // Sentinels round-trip to ExtendedFloat sentinels (NOT
        // `Extend(±INFINITY)`) so the Galois law holds at the
        // `(Top, PosInf)` and `(Bot, NegInf)` boundaries.
        assert_eq!(F032U008.upper(Extended::NegInf), ExtendedFloat::Bot);
        assert_eq!(F032U008.upper(Extended::PosInf), ExtendedFloat::Top);
    }

    // ── Property tests via `law_battery!` ───────────────────────────

    crate::law_battery! {
        mod laws_u008,
        conn: F032U008,
        fine:   extended_float_f32(),
        coarse: arb_extended_u8(),
    }
    crate::law_battery! {
        mod laws_u016,
        conn: F032U016,
        fine:   extended_float_f32(),
        coarse: arb_extended_u16(),
    }
    crate::law_battery! {
        mod laws_u032,
        conn: F032U032,
        fine:   extended_float_f32(),
        coarse: arb_extended_u32(),
        subset: l_only,
    }
    crate::law_battery! {
        mod laws_u064,
        conn: F032U064,
        fine:   extended_float_f32(),
        coarse: arb_extended_u64(),
        subset: l_only,
    }
    crate::law_battery! {
        mod laws_i008,
        conn: F032I008,
        fine:   extended_float_f32(),
        coarse: arb_extended_i8(),
    }
    crate::law_battery! {
        mod laws_i016,
        conn: F032I016,
        fine:   extended_float_f32(),
        coarse: arb_extended_i16(),
    }
    crate::law_battery! {
        mod laws_i032,
        conn: F032I032,
        fine:   extended_float_f32(),
        coarse: arb_extended_i32(),
        subset: l_only,
    }
    crate::law_battery! {
        mod laws_i064,
        conn: F032I064,
        fine:   extended_float_f32(),
        coarse: arb_extended_i64(),
        subset: l_only,
    }
}
