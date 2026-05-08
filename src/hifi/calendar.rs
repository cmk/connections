//! `hifitime::MonthName` and `hifitime::Weekday` connections.
//!
//! Three `Conn`s wrapping hifitime's two `repr(u8)` calendar enums:
//!
//! - [`MONTU008`] — `Extended<MonthName> → u8` (1=Jan…12=Dec).
//! - [`MONTN008`] — `Extended<MonthName> → NonZeroU8`, the natural
//!   representation when the caller already knows months are ≥ 1.
//! - [`WKDYU008`] — `Extended<Weekday> → u8` (0=Mon…6=Sun, ISO 8601
//!   ordering).
//!
//! ## Saturate, don't wrap
//!
//! Hifitime's `From<u8>` impls do **not** preserve a clean bijection:
//!
//! - [`MonthName::from`](hifitime::MonthName)`(u: u8)` returns
//!   `MonthName::January` (the `#[default]`) for any value not in
//!   `[1, 12]`. So `MonthName::from(0) == MonthName::from(1) == January`
//!   — collision.
//! - [`Weekday::from`](hifitime::Weekday)`(u: u8)` uses `rem_euclid(7)`.
//!   So `Weekday::from(7) == Weekday::from(0) == Monday` — wrap.
//!
//! Both behaviors break the [`crate::iso!`] adjoint laws. These Conns
//! ship as [`crate::conn_l!`] (one-sided left-Galois) following the
//! **ODTMNANO shape** (single-side `Extended`, asymmetric saturation
//! on the integer rung): `Extended` lives only on the enum side; the
//! `u8` / `NonZeroU8` rung uses saturation arms (`ceil(NegInf) = 0`
//! or smallest-valid; `ceil(PosInf) = max_valid + 1`). Callers
//! wanting hifitime's wrapping/defaulting semantics use
//! `MonthName::from(u8)` / `Weekday::from(u8)` directly.
//!
//! ## Naming
//!
//! Per CLAUDE.md §Conn-name format: `MONT` and `WKDY` are 4-letter
//! `ABCD`-shape source codes; `U008` is the canonical `Extended<…>
//! → u8` target code (`A123` shape, `U` = unsigned int + 8-bit
//! width). `N008` is the matching canonical form for the
//! `NonZeroU8` target (`A123` shape, `N` = `NonZero<*>` + 8-bit
//! width), parallel to [`crate::fixed::i8::I008N008`].

use crate::extended::Extended;
use core::num::NonZeroU8;
use hifitime::{MonthName, Weekday};

// ── MONTU008 ─────────────────────────────────────────────────────

fn montu008_ceil(m: Extended<MonthName>) -> u8 {
    match m {
        // u8=0 sits below the canonical [1, 12] month range, so it's
        // the natural "below" sentinel — distinct from `Finite(January)`
        // which maps to 1.
        Extended::NegInf => 0,
        // MonthName variants Jan..Dec map to discriminants 0..11 (the
        // `#[default]` sits at January, position 0). Canonical month
        // numbering is 1-indexed, so add 1.
        Extended::Finite(month) => month as u8 + 1,
        // u8=13 is `max_valid + 1` — the ODTMNANO-shape PosInf sentinel.
        Extended::PosInf => 13,
    }
}

fn montu008_inner(u: u8) -> Extended<MonthName> {
    match u {
        0 => Extended::NegInf,
        n @ 1..=12 => Extended::Finite(MonthName::from(n)),
        // u8 ∈ [13, 255] sits above the canonical range. Saturate to
        // PosInf rather than wrapping/defaulting via `MonthName::from`.
        _ => Extended::PosInf,
    }
}

crate::conn_l! {
    /// `Extended<MonthName> → u8` — month enum ↔ canonical 1-indexed
    /// integer (1=Jan…12=Dec).
    ///
    /// One-sided left-Galois Conn (`Conn::new_l(ceil, inner)`),
    /// ODTMNANO shape: `Extended` only on the source; the `u8` rung
    /// uses saturation arms (`ceil(NegInf) = 0`, `ceil(PosInf) = 13`).
    /// `inner: u8 → Extended<MonthName>` saturates `u8` values
    /// outside `[1, 12]` onto `Extended::NegInf` (u8=0) or
    /// `Extended::PosInf` (u8 ≥ 13).
    ///
    /// **Diverges from `MonthName::from(u8)`'s default-on-error
    /// semantics:** `MONTU008.upper(0)` returns `NegInf`, not
    /// `Finite(January)`. `MONTU008.upper(13)` returns `PosInf`, not
    /// `Finite(January)`. Callers wanting hifitime's defaulting
    /// behavior call `MonthName::from(u8)` directly.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::hifi::MONTU008;
    /// use connections::extended::Extended;
    /// use hifitime::MonthName;
    ///
    /// assert_eq!(MONTU008.ceil(Extended::Finite(MonthName::January)), 1);
    /// assert_eq!(MONTU008.ceil(Extended::Finite(MonthName::December)), 12);
    /// assert_eq!(MONTU008.upper(6), Extended::Finite(MonthName::June));
    ///
    /// // Out-of-range u8 values saturate.
    /// assert_eq!(MONTU008.upper(0), Extended::NegInf);
    /// assert_eq!(MONTU008.upper(13), Extended::PosInf);
    /// assert_eq!(MONTU008.ceil(Extended::NegInf), 0);
    /// assert_eq!(MONTU008.ceil(Extended::PosInf), 13);
    /// ```
    pub MONTU008 : Extended<MonthName> => u8 {
        ceil:  montu008_ceil,
        inner: montu008_inner,
    }
}

// ── MONTN008 ─────────────────────────────────────────────────────

fn montn008_ceil(m: Extended<MonthName>) -> NonZeroU8 {
    // NonZeroU8 has no value below 1 — there's no "below valid"
    // sentinel available. Collapse `Extended::NegInf` to the smallest
    // valid (`NonZeroU8::new(1)`, January's slot). The Galois law
    // tolerates this collapse: `NegInf < Finite(January)` on the
    // source maps to `1 ≤ 1` (equality) on the target, which is
    // monotone-with-equality.
    let n = match m {
        Extended::NegInf => 1,
        Extended::Finite(month) => month as u8 + 1,
        Extended::PosInf => 13,
    };
    match NonZeroU8::new(n) {
        Some(nz) => nz,
        None => unreachable!("ceil produces values in [1, 13], never zero"),
    }
}

fn montn008_inner(nz: NonZeroU8) -> Extended<MonthName> {
    let n = nz.get();
    match n {
        1..=12 => Extended::Finite(MonthName::from(n)),
        // NonZeroU8 > 12 saturates to PosInf. The type already rules
        // out the zero case, so no NegInf arm fires from `Finite`
        // input (the NegInf collapse on `ceil(NegInf) = 1` is one-way:
        // `inner(1) = Finite(January)`, not NegInf).
        _ => Extended::PosInf,
    }
}

crate::conn_l! {
    /// `Extended<MonthName> → NonZeroU8` — month enum ↔ canonical
    /// 1-indexed `NonZeroU8` (1=Jan…12=Dec).
    ///
    /// Same shape as [`MONTU008`] but with the type-level guarantee
    /// that the integer side is non-zero. The natural representation
    /// when the caller already knows months are ≥ 1.
    ///
    /// One-sided left-Galois Conn. Because `NonZeroU8` has no value
    /// below 1, `ceil(NegInf)` collapses onto `NonZeroU8(1)` (the same
    /// slot as January) — monotone-with-equality is sufficient for
    /// Galois-L. `ceil(PosInf) = NonZeroU8(13)`. `inner` saturates
    /// `NonZeroU8` values > 12 onto `Extended::PosInf`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::hifi::MONTN008;
    /// use connections::extended::Extended;
    /// use core::num::NonZeroU8;
    /// use hifitime::MonthName;
    ///
    /// let one = NonZeroU8::new(1).unwrap();
    /// assert_eq!(MONTN008.ceil(Extended::Finite(MonthName::January)), one);
    ///
    /// let twelve = NonZeroU8::new(12).unwrap();
    /// assert_eq!(MONTN008.ceil(Extended::Finite(MonthName::December)), twelve);
    ///
    /// // NonZeroU8 > 12 saturates.
    /// let thirteen = NonZeroU8::new(13).unwrap();
    /// assert_eq!(MONTN008.upper(thirteen), Extended::PosInf);
    /// ```
    pub MONTN008 : Extended<MonthName> => NonZeroU8 {
        ceil:  montn008_ceil,
        inner: montn008_inner,
    }
}

// ── WKDYU008 ─────────────────────────────────────────────────────

fn wkdyu008_ceil(w: Extended<Weekday>) -> u8 {
    match w {
        // Weekday::Monday = 0, so `u8 = 0` is the smallest valid slot
        // — no sub-Monday sentinel available. Collapse `NegInf` onto
        // `0` (Monday's slot); same monotone-with-equality argument
        // as MONTN008.
        Extended::NegInf => 0,
        // Weekday::Monday = 0…Sunday = 6 by explicit discriminant
        // (`hifitime/src/weekday.rs:28-37`). No offset needed — the
        // cast is direct.
        Extended::Finite(day) => day as u8,
        // u8=7 is `max_valid + 1` — the ODTMNANO-shape PosInf sentinel.
        Extended::PosInf => 7,
    }
}

fn wkdyu008_inner(u: u8) -> Extended<Weekday> {
    match u {
        0..=6 => Extended::Finite(Weekday::from(u)),
        // u8 ≥ 7 saturates to PosInf (NOT to a wrapped weekday).
        // Hifitime's `Weekday::from(7)` returns Monday via rem_euclid,
        // which would break Galois-L monotonicity. We diverge here
        // intentionally — see the type doc.
        _ => Extended::PosInf,
    }
}

crate::conn_l! {
    /// `Extended<Weekday> → u8` — weekday enum ↔ canonical 0-indexed
    /// integer (0=Mon…6=Sun, ISO 8601 ordering).
    ///
    /// One-sided left-Galois Conn (`Conn::new_l(ceil, inner)`),
    /// ODTMNANO shape: `Extended` only on the source. `ceil(NegInf)`
    /// collapses to `0` (Monday's slot — no sub-Monday u8 available);
    /// `ceil(PosInf) = 7`. `inner: u8 → Extended<Weekday>` saturates
    /// `u8` values ≥ 7 onto `Extended::PosInf` rather than wrapping
    /// via `rem_euclid(7)`.
    ///
    /// **Diverges from `Weekday::from(u8)`'s wrapping semantics:**
    /// `WKDYU008.upper(7)` returns `PosInf`, not `Finite(Monday)`.
    /// The wrap is mathematically meaningful for circular date math
    /// but breaks Galois-L's monotonicity, so this Conn intentionally
    /// rejects out-of-range integers. Callers wanting wrapping use
    /// `Weekday::from(u8)` directly.
    ///
    /// Hifitime uses **0=Monday, 6=Sunday** (ISO 8601). For C89-style
    /// 0=Sunday ordering, see `Weekday::to_c89_weekday()`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use connections::hifi::WKDYU008;
    /// use connections::extended::Extended;
    /// use hifitime::Weekday;
    ///
    /// assert_eq!(WKDYU008.ceil(Extended::Finite(Weekday::Monday)), 0);
    /// assert_eq!(WKDYU008.ceil(Extended::Finite(Weekday::Sunday)), 6);
    /// assert_eq!(WKDYU008.upper(3), Extended::Finite(Weekday::Thursday));
    ///
    /// // u8 ≥ 7 saturates (NOT a wrap to Monday).
    /// assert_eq!(WKDYU008.upper(7), Extended::PosInf);
    /// assert_eq!(WKDYU008.upper(255), Extended::PosInf);
    /// assert_eq!(WKDYU008.ceil(Extended::PosInf), 7);
    /// ```
    pub WKDYU008 : Extended<Weekday> => u8 {
        ceil:  wkdyu008_ceil,
        inner: wkdyu008_inner,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[allow(unused_imports)]
    use crate::conn::{ConnL, ConnR};
    use crate::prop::arb::{arb_extended_hifi_month, arb_extended_hifi_weekday};
    use crate::prop::conn as conn_laws;
    use proptest::prelude::*;

    // Local helper strategies — bias toward boundary u8 / NonZeroU8
    // values relevant to the calendar saturation arms.
    //
    // `arb_u8_calendar` is the **union** of MONTU008 boundaries
    // (0, 1, 12, 13) and WKDYU008 boundaries (0, 6, 7) plus a
    // generic `any::<u8>()` slot. Naming reflects the shared intent
    // across both calendar Conns. A new Conn family with a different
    // canonical integer range should NOT reuse this — define its own
    // boundary-biased helper rather than inheriting MONT/WKDY-specific
    // values. (MR !69 round-1.)
    fn arb_u8_calendar() -> impl Strategy<Value = u8> {
        prop_oneof![
            1 => Just(0_u8),
            1 => Just(1_u8),
            1 => Just(6_u8),
            1 => Just(7_u8),
            1 => Just(12_u8),
            1 => Just(13_u8),
            1 => Just(254_u8),
            1 => Just(u8::MAX),
            8 => any::<u8>(),
        ]
    }

    fn arb_nz_u8_calendar() -> impl Strategy<Value = NonZeroU8> {
        prop_oneof![
            1 => Just(NonZeroU8::new(1).unwrap()),
            1 => Just(NonZeroU8::new(12).unwrap()),
            1 => Just(NonZeroU8::new(13).unwrap()),
            1 => Just(NonZeroU8::new(254).unwrap()),
            1 => Just(NonZeroU8::new(u8::MAX).unwrap()),
            8 => (1u8..=u8::MAX).prop_map(|n| NonZeroU8::new(n).unwrap()),
        ]
    }

    // ── Spot checks ─────────────────────────────────────────────

    #[test]
    fn montu008_january_is_one() {
        assert_eq!(MONTU008.ceil(Extended::Finite(MonthName::January)), 1);
        assert_eq!(MONTU008.upper(1), Extended::Finite(MonthName::January));
    }

    #[test]
    fn montu008_december_is_twelve() {
        assert_eq!(MONTU008.ceil(Extended::Finite(MonthName::December)), 12);
        assert_eq!(MONTU008.upper(12), Extended::Finite(MonthName::December));
    }

    #[test]
    fn montu008_zero_saturates_neg_inf() {
        // u8=0 < smallest valid month — saturates to NegInf, NOT
        // defaulting to January via MonthName::from(0).
        assert_eq!(MONTU008.upper(0), Extended::NegInf);
    }

    #[test]
    fn montu008_thirteen_saturates_pos_inf() {
        // u8=13 > largest valid month — saturates to PosInf, NOT
        // defaulting to January via MonthName::from(13).
        assert_eq!(MONTU008.upper(13), Extended::PosInf);
    }

    #[test]
    fn montu008_extended_extremes() {
        assert_eq!(MONTU008.ceil(Extended::NegInf), 0);
        assert_eq!(MONTU008.ceil(Extended::PosInf), 13);
    }

    #[test]
    fn montu008_round_trip_all_months() {
        let months = [
            MonthName::January,
            MonthName::February,
            MonthName::March,
            MonthName::April,
            MonthName::May,
            MonthName::June,
            MonthName::July,
            MonthName::August,
            MonthName::September,
            MonthName::October,
            MonthName::November,
            MonthName::December,
        ];
        for (i, &m) in months.iter().enumerate() {
            let canon = (i + 1) as u8;
            assert_eq!(MONTU008.ceil(Extended::Finite(m)), canon);
            assert_eq!(MONTU008.upper(canon), Extended::Finite(m));
        }
    }

    #[test]
    fn montn008_january_is_nonzero_one() {
        let one = NonZeroU8::new(1).unwrap();
        assert_eq!(MONTN008.ceil(Extended::Finite(MonthName::January)), one);
    }

    #[test]
    fn montn008_december_is_nonzero_twelve() {
        let twelve = NonZeroU8::new(12).unwrap();
        assert_eq!(MONTN008.ceil(Extended::Finite(MonthName::December)), twelve);
    }

    #[test]
    fn montn008_thirteen_saturates_pos_inf() {
        let thirteen = NonZeroU8::new(13).unwrap();
        assert_eq!(MONTN008.upper(thirteen), Extended::PosInf);
    }

    #[test]
    fn montn008_neg_inf_collapses_to_one() {
        // NonZeroU8 has no sub-1 sentinel; NegInf collapses to 1.
        let one = NonZeroU8::new(1).unwrap();
        assert_eq!(MONTN008.ceil(Extended::NegInf), one);
    }

    #[test]
    fn montn008_one_recovers_january_not_neg_inf() {
        // Inverse of the NegInf-collapse: `upper(NonZeroU8(1))` must
        // recover `Finite(January)`, NOT `NegInf`. The collapse on
        // `ceil` is one-way; a refactor that inverted the inner arm
        // (`inner(1) → NegInf`) would silently break the round-trip
        // round-trip while still satisfying monotonicity. (MR !69
        // round-1.)
        let one = NonZeroU8::new(1).unwrap();
        assert_eq!(MONTN008.upper(one), Extended::Finite(MonthName::January),);
    }

    #[test]
    fn wkdyu008_monday_is_zero() {
        assert_eq!(WKDYU008.ceil(Extended::Finite(Weekday::Monday)), 0);
        assert_eq!(WKDYU008.upper(0), Extended::Finite(Weekday::Monday));
    }

    #[test]
    fn wkdyu008_sunday_is_six() {
        assert_eq!(WKDYU008.ceil(Extended::Finite(Weekday::Sunday)), 6);
        assert_eq!(WKDYU008.upper(6), Extended::Finite(Weekday::Sunday));
    }

    #[test]
    fn wkdyu008_seven_saturates_pos_inf() {
        // u8=7 — hifitime wraps to Monday via rem_euclid; we saturate
        // to PosInf to preserve Galois-L monotonicity.
        assert_eq!(WKDYU008.upper(7), Extended::PosInf);
    }

    #[test]
    fn wkdyu008_neg_inf_collapses_to_zero() {
        // u8 has no sub-0 sentinel; NegInf collapses to 0 (Monday's slot).
        assert_eq!(WKDYU008.ceil(Extended::NegInf), 0);
    }

    #[test]
    fn wkdyu008_round_trip_all_weekdays() {
        let weekdays = [
            Weekday::Monday,
            Weekday::Tuesday,
            Weekday::Wednesday,
            Weekday::Thursday,
            Weekday::Friday,
            Weekday::Saturday,
            Weekday::Sunday,
        ];
        for (i, &w) in weekdays.iter().enumerate() {
            let canon = i as u8;
            assert_eq!(WKDYU008.ceil(Extended::Finite(w)), canon);
            assert_eq!(WKDYU008.upper(canon), Extended::Finite(w));
        }
    }

    // ── ConnL law batteries ─────────────────────────────────────

    proptest! {
        #[test]
        fn montu008_galois_l(a in arb_extended_hifi_month(), b in arb_u8_calendar()) {
            prop_assert!(conn_laws::galois_l(&MONTU008, a, b));
        }
        #[test]
        fn montu008_closure_l(a in arb_extended_hifi_month()) {
            prop_assert!(conn_laws::closure_l(&MONTU008, a));
        }
        #[test]
        fn montu008_kernel_l(b in arb_u8_calendar()) {
            prop_assert!(conn_laws::kernel_l(&MONTU008, b));
        }
        #[test]
        fn montu008_monotone_l(a1 in arb_extended_hifi_month(),
                               a2 in arb_extended_hifi_month()) {
            prop_assert!(conn_laws::monotone_l(&MONTU008, a1, a2));
        }
        #[test]
        fn montu008_idempotent(a in arb_extended_hifi_month()) {
            prop_assert!(conn_laws::idempotent(&MONTU008, a));
        }

        #[test]
        fn montn008_galois_l(a in arb_extended_hifi_month(), b in arb_nz_u8_calendar()) {
            prop_assert!(conn_laws::galois_l(&MONTN008, a, b));
        }
        #[test]
        fn montn008_closure_l(a in arb_extended_hifi_month()) {
            prop_assert!(conn_laws::closure_l(&MONTN008, a));
        }
        #[test]
        fn montn008_kernel_l(b in arb_nz_u8_calendar()) {
            prop_assert!(conn_laws::kernel_l(&MONTN008, b));
        }
        #[test]
        fn montn008_monotone_l(a1 in arb_extended_hifi_month(),
                               a2 in arb_extended_hifi_month()) {
            prop_assert!(conn_laws::monotone_l(&MONTN008, a1, a2));
        }
        #[test]
        fn montn008_idempotent(a in arb_extended_hifi_month()) {
            prop_assert!(conn_laws::idempotent(&MONTN008, a));
        }

        #[test]
        fn wkdyu008_galois_l(a in arb_extended_hifi_weekday(), b in arb_u8_calendar()) {
            prop_assert!(conn_laws::galois_l(&WKDYU008, a, b));
        }
        #[test]
        fn wkdyu008_closure_l(a in arb_extended_hifi_weekday()) {
            prop_assert!(conn_laws::closure_l(&WKDYU008, a));
        }
        #[test]
        fn wkdyu008_kernel_l(b in arb_u8_calendar()) {
            prop_assert!(conn_laws::kernel_l(&WKDYU008, b));
        }
        #[test]
        fn wkdyu008_monotone_l(a1 in arb_extended_hifi_weekday(),
                               a2 in arb_extended_hifi_weekday()) {
            prop_assert!(conn_laws::monotone_l(&WKDYU008, a1, a2));
        }
        #[test]
        fn wkdyu008_idempotent(a in arb_extended_hifi_weekday()) {
            prop_assert!(conn_laws::idempotent(&WKDYU008, a));
        }
    }
}
