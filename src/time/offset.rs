//! Timezone-aware `OffsetDateTime` connections.
//!
//! Hosts:
//!
//! - [`OFDTNANO`] — `OffsetDateTime ↔ i128` unix nanoseconds
//!   (lossless across the full default OffsetDateTime range; i64
//!   seconds is too narrow).
//! - [`OFDTSECS`] — `OffsetDateTime ↔ i64` unix whole seconds with
//!   sub-second rounding (analog of [`TIMESECS`](super::TIMESECS)
//!   for the clock domain).
//!
//! `OffsetDateTime` equality and ordering in `time` 0.3 are
//! **instant**-based (the `Ord` impl re-bases the right-hand side
//! to the left-hand side's offset before comparing, which collapses
//! same-instant-different-offset values into a single equivalence
//! class). The conns therefore treat any two OffsetDateTime values
//! representing the same instant as identical, regardless of their
//! offset variant.
//!
//! A planned `UTCOSECS` connection (`UtcOffset ↔ i32` total seconds)
//! is **deferred**: `UtcOffset`'s `Ord` impl in `time` 0.3 orders by
//! a packed `as_u32()` byte representation (a hash-key implementation
//! detail), not by `whole_seconds`. The Galois machinery requires the
//! source-side `PartialOrd` to align with the rung's natural order,
//! which `UtcOffset` doesn't provide. Future sprint should introduce
//! a `UtcOffsetSecs(UtcOffset)` newtype with `PartialOrd` by
//! `whole_seconds`, then wire `UTCOSECS` over the wrapper.
//!
//! # Example
//!
//! ```rust
//! use connections::time::OFDTNANO;
//! use connections::extended::Extended;
//! use time::OffsetDateTime;
//!
//! assert_eq!(OFDTNANO.inner(0), Extended::Finite(OffsetDateTime::UNIX_EPOCH));
//! assert_eq!(
//!     OFDTNANO.ceil(Extended::Finite(OffsetDateTime::UNIX_EPOCH)),
//!     0,
//! );
//! ```

use crate::conn::Conn;
use crate::extended::Extended;
use time::{Date, OffsetDateTime, Time, UtcOffset};

// ── Range bounds, computed once at runtime ─────────────────────
//
// `OffsetDateTime`'s instant range is **wider** than its
// (Date::MIN, Date::MAX) UTC bounds. An OffsetDateTime is a
// (PrimitiveDateTime, UtcOffset) pair where the local PDT is in
// `[Date::MIN, Date::MAX]` × Time, but the instant = local_pdt −
// offset. The most-negative offset (-25:59:59) on Date::MAX local
// extends the instant past Date::MAX UTC; symmetric for the
// +25:59:59 offset on Date::MIN. So the actual instant range is
// approximately `[Date::MIN+25:59:59 UTC, Date::MAX-25:59:59 UTC]`.
//
// `time::OffsetDateTime`'s `Ord` re-bases the right-hand side to
// the LHS's offset before comparing — this is instant-based and
// exposes the wider range to law tests.

#[inline]
fn end_of_day_time() -> Time {
    Time::from_hms_nano(23, 59, 59, 999_999_999).expect("23:59:59.999_999_999 is a valid Time")
}

/// Minimum-instant OffsetDateTime: Date::MIN at midnight, with the
/// most-positive offset (`+25:59:59`) — local-pdt is the smallest,
/// offset is the largest, so `local − offset` is the smallest instant.
#[cfg(test)]
#[inline]
fn ofdt_min_instant() -> OffsetDateTime {
    OffsetDateTime::new_in_offset(
        Date::MIN,
        Time::MIDNIGHT,
        UtcOffset::from_whole_seconds(93_599).expect("+25:59:59 is a valid offset"),
    )
}

/// Maximum-instant OffsetDateTime: Date::MAX at end-of-day, with
/// the most-negative offset (`-25:59:59`).
#[cfg(test)]
#[inline]
fn ofdt_max_instant() -> OffsetDateTime {
    OffsetDateTime::new_in_offset(
        Date::MAX,
        end_of_day_time(),
        UtcOffset::from_whole_seconds(-93_599).expect("-25:59:59 is a valid offset"),
    )
}

/// Smallest unix-nanosecond rung value that
/// `OffsetDateTime::from_unix_timestamp_nanos` accepts (Date::MIN
/// midnight UTC). The instant range of `OffsetDateTime` is wider —
/// see `ofdt_min_instant` — but the rung saturates here because
/// the inverse direction (rung → OFDT) only constructs UTC OFDTs.
#[inline]
fn utc_min_ns() -> i128 {
    OffsetDateTime::new_in_offset(Date::MIN, Time::MIDNIGHT, UtcOffset::UTC).unix_timestamp_nanos()
}

#[inline]
fn utc_max_ns() -> i128 {
    OffsetDateTime::new_in_offset(Date::MAX, end_of_day_time(), UtcOffset::UTC)
        .unix_timestamp_nanos()
}

#[inline]
fn utc_min_s() -> i64 {
    OffsetDateTime::new_in_offset(Date::MIN, Time::MIDNIGHT, UtcOffset::UTC).unix_timestamp()
}

#[inline]
fn utc_max_s() -> i64 {
    OffsetDateTime::new_in_offset(Date::MAX, end_of_day_time(), UtcOffset::UTC).unix_timestamp()
}

// ── OFDTNANO ─────────────────────────────────────────────────────

/// `Extended<OffsetDateTime> → i128` — unix nanoseconds since
/// `OffsetDateTime::UNIX_EPOCH`.
///
/// One-sided left-Galois Conn (`Conn::new_left(ceil, inner)`):
/// `inner: i128 → Extended<OffsetDateTime>` saturates out-of-range
/// `i128` values onto `Extended::NegInf` / `Extended::PosInf`, which
/// makes `inner` non-order-reflecting at the synthetic extremes. The
/// constructor wires `floor = ceil` as a fn pointer so `floor(a) ≤
/// ceil(a)` holds structurally over the full source domain.
///
/// Lossless across the full default-features OffsetDateTime range
/// (year ±9999 ≈ ±3.16 × 10²⁰ ns, comfortably inside `i128`'s
/// ±1.7 × 10³⁸ envelope). On the `Finite` portion this is an exact
/// bijection on the instant.
///
/// Two OffsetDateTimes representing the same instant in different
/// offsets compare equal under `time` 0.3's `PartialEq` and so map
/// to the same `i128`. `inner` returns the UTC representative.
///
/// # Examples
///
/// ```rust
/// use connections::time::OFDTNANO;
/// use connections::extended::Extended;
/// use time::OffsetDateTime;
///
/// assert_eq!(OFDTNANO.ceil(Extended::Finite(OffsetDateTime::UNIX_EPOCH)), 0);
/// assert_eq!(OFDTNANO.inner(1_000_000_000), Extended::Finite(
///     OffsetDateTime::UNIX_EPOCH + time::Duration::seconds(1),
/// ));
///
/// // Out-of-range nanoseconds saturate.
/// assert_eq!(OFDTNANO.inner(i128::MAX), Extended::PosInf);
/// ```
pub const OFDTNANO: Conn<Extended<OffsetDateTime>, i128> = {
    fn ceil(o: Extended<OffsetDateTime>) -> i128 {
        let min_ns = utc_min_ns();
        let max_ns = utc_max_ns();
        match o {
            Extended::NegInf => i128::MIN,
            Extended::Finite(odt) => {
                let n = odt.unix_timestamp_nanos();
                // OFDT's instant range exceeds the UTC range its rung
                // covers; saturate the rung to ±(UTC_bounds ± 1) when
                // the instant escapes via a non-UTC offset.
                if n < min_ns {
                    min_ns
                } else if n > max_ns {
                    max_ns + 1
                } else {
                    n
                }
            }
            Extended::PosInf => max_ns + 1,
        }
    }

    fn inner(n: i128) -> Extended<OffsetDateTime> {
        let min_ns = utc_min_ns();
        let max_ns = utc_max_ns();
        if n < min_ns {
            Extended::NegInf
        } else if n > max_ns {
            Extended::PosInf
        } else {
            match OffsetDateTime::from_unix_timestamp_nanos(n) {
                Ok(odt) => Extended::Finite(odt),
                Err(_) => unreachable!("n in [utc_min_ns, utc_max_ns]"),
            }
        }
    }

    Conn::new_left(ceil, inner)
};

// ── OFDTSECS ─────────────────────────────────────────────────────

/// `Extended<OffsetDateTime> → i64` — unix whole seconds since
/// `OffsetDateTime::UNIX_EPOCH`, rounding sub-second fractions up to
/// the next whole second.
///
/// One-sided left-Galois Conn (`Conn::new_left(ceil, inner)`). Two
/// reasons it can't ship as a full triple:
///
/// - `inner` saturates out-of-range `i64` values to
///   `Extended::NegInf` / `Extended::PosInf`, making it non-order-
///   reflecting at the synthetic source extremes.
/// - On Finite sub-second inputs, the natural `ceil` (round up) and
///   `floor` (truncate) differ; the constructor wires `floor = ceil`
///   as a fn pointer so the law holds structurally.
///
/// **Behavioral note on rounding:** `ceil(Finite(odt))` =
/// `odt.unix_timestamp() + 1` when `odt.nanosecond() != 0`, otherwise
/// `odt.unix_timestamp()`. Because `floor = ceil` under `new_left`,
/// callers reading `OFDTSECS.floor(odt)` get the **rounded-up**
/// answer, not the truncated one (`unix_timestamp()` is itself
/// `floor`-shaped in the `time` crate). Callers needing the
/// truncating direction can compute `odt.unix_timestamp()` directly.
///
/// `i64` is wide enough for the full OffsetDateTime range (`±3.16 ×
/// 10¹¹` s, comfortably inside `i64`'s `±9.22 × 10¹⁸`), so the only
/// saturation happens on the outer `Extended` source arms.
///
/// # Examples
///
/// ```rust
/// use connections::time::OFDTSECS;
/// use connections::extended::Extended;
/// use time::{Duration, OffsetDateTime};
///
/// // Exact second.
/// assert_eq!(OFDTSECS.ceil(Extended::Finite(OffsetDateTime::UNIX_EPOCH)), 0);
///
/// // Sub-second past epoch: ceil rounds up.
/// let mid = OffsetDateTime::UNIX_EPOCH + Duration::nanoseconds(1);
/// assert_eq!(OFDTSECS.ceil(Extended::Finite(mid)), 1);
/// ```
pub const OFDTSECS: Conn<Extended<OffsetDateTime>, i64> = {
    fn ceil(o: Extended<OffsetDateTime>) -> i64 {
        let min_s = utc_min_s();
        let max_s = utc_max_s();
        match o {
            Extended::NegInf => i64::MIN,
            Extended::Finite(odt) => {
                let s = odt.unix_timestamp();
                if s < min_s {
                    // Instant below UTC range — smallest rung Finite
                    // value is min_s.
                    min_s
                } else if s >= max_s {
                    // Instant at or beyond UTC max: ceil bumps past
                    // max_s into the saturation marker.
                    if s > max_s || odt.nanosecond() != 0 {
                        max_s + 1
                    } else {
                        max_s
                    }
                } else if odt.nanosecond() != 0 {
                    // Sub-second past s — ceil rounds up by one.
                    s + 1
                } else {
                    s
                }
            }
            Extended::PosInf => max_s + 1,
        }
    }

    fn inner(s: i64) -> Extended<OffsetDateTime> {
        let min_s = utc_min_s();
        let max_s = utc_max_s();
        if s < min_s {
            Extended::NegInf
        } else if s > max_s {
            Extended::PosInf
        } else {
            match OffsetDateTime::from_unix_timestamp(s) {
                Ok(odt) => Extended::Finite(odt),
                Err(_) => unreachable!("s in [utc_min_s, utc_max_s]"),
            }
        }
    }

    Conn::new_left(ceil, inner)
};

#[cfg(test)]
mod ofdt_tests {
    use super::*;
    use crate::prop::arb::{
        arb_extended_offset_dt, arb_offset_dt, arb_unix_nanos_in_range, arb_unix_secs_in_range,
    };
    use crate::prop::{conn as conn_laws, lattice as lattice_laws};
    use proptest::prelude::*;
    use time::Duration;

    // ── Preorder laws on `OffsetDateTime` ───────────────────────

    mod offset_dt_preorder {
        use super::*;

        proptest! {
            #[test]
            fn reflexive(x in arb_offset_dt()) {
                prop_assert!(lattice_laws::lattice_reflexive(&x));
            }

            #[test]
            fn transitive(x in arb_offset_dt(), y in arb_offset_dt(), z in arb_offset_dt()) {
                prop_assert!(lattice_laws::lattice_transitive(&x, &y, &z));
            }

            #[test]
            fn antisymmetric(x in arb_offset_dt(), y in arb_offset_dt()) {
                prop_assert!(lattice_laws::lattice_antisymmetric(&x, &y));
            }

            #[test]
            fn bot(x in arb_offset_dt()) {
                prop_assert!(lattice_laws::lattice_bot(&ofdt_min_instant(), &x));
            }

            #[test]
            fn top(x in arb_offset_dt()) {
                prop_assert!(lattice_laws::lattice_top(&ofdt_max_instant(), &x));
            }
        }
    }

    // ── OFDTNANO spot checks ────────────────────────────────────

    #[test]
    fn epoch_is_zero() {
        assert_eq!(
            OFDTNANO.ceil(Extended::Finite(OffsetDateTime::UNIX_EPOCH)),
            0
        );
        assert_eq!(
            OFDTNANO.inner(0),
            Extended::Finite(OffsetDateTime::UNIX_EPOCH)
        );
    }

    #[test]
    fn one_ns_past_epoch() {
        let mid = OffsetDateTime::UNIX_EPOCH + Duration::nanoseconds(1);
        assert_eq!(OFDTNANO.ceil(Extended::Finite(mid)), 1);
        assert_eq!(OFDTNANO.inner(1), Extended::Finite(mid));
    }

    #[test]
    fn one_ns_before_epoch() {
        let mid = OffsetDateTime::UNIX_EPOCH - Duration::nanoseconds(1);
        assert_eq!(OFDTNANO.ceil(Extended::Finite(mid)), -1);
        assert_eq!(OFDTNANO.inner(-1), Extended::Finite(mid));
    }

    #[test]
    fn y2038() {
        let y2038_ns: i128 = 2_147_483_648_000_000_000;
        let y2038 = OffsetDateTime::from_unix_timestamp_nanos(y2038_ns).unwrap();
        assert_eq!(OFDTNANO.ceil(Extended::Finite(y2038)), y2038_ns);
        assert_eq!(OFDTNANO.inner(y2038_ns), Extended::Finite(y2038));
    }

    #[test]
    fn utc_extremes_round_trip() {
        // UTC extremes are the round-trippable boundary — wider
        // OffsetDateTime instants (e.g. Date::MAX with negative
        // offset) saturate the rung.
        let min_utc = OffsetDateTime::new_in_offset(Date::MIN, Time::MIDNIGHT, UtcOffset::UTC);
        let max_utc = OffsetDateTime::new_in_offset(
            Date::MAX,
            Time::from_hms_nano(23, 59, 59, 999_999_999).unwrap(),
            UtcOffset::UTC,
        );
        let min_ns = utc_min_ns();
        let max_ns = utc_max_ns();

        assert_eq!(OFDTNANO.ceil(Extended::Finite(min_utc)), min_ns);
        assert_eq!(OFDTNANO.ceil(Extended::Finite(max_utc)), max_ns);
        assert_eq!(OFDTNANO.inner(min_ns), Extended::Finite(min_utc));
        assert_eq!(OFDTNANO.inner(max_ns), Extended::Finite(max_utc));
    }

    #[test]
    fn instant_extreme_saturates() {
        // ofdt_max_instant() has instant past utc_max_ns; ceil bumps
        // it to max_ns + 1 (the PosInf marker on the rung).
        let max_inst = ofdt_max_instant();
        assert_eq!(OFDTNANO.ceil(Extended::Finite(max_inst)), utc_max_ns() + 1);

        let min_inst = ofdt_min_instant();
        assert_eq!(OFDTNANO.ceil(Extended::Finite(min_inst)), utc_min_ns());
    }

    #[test]
    fn ofdtnano_saturation_extremes() {
        assert_eq!(OFDTNANO.inner(i128::MAX), Extended::PosInf);
        assert_eq!(OFDTNANO.inner(i128::MIN), Extended::NegInf);

        let max_ns = utc_max_ns();
        assert_eq!(OFDTNANO.ceil(Extended::PosInf), max_ns + 1);
        assert_eq!(OFDTNANO.ceil(Extended::NegInf), i128::MIN);
        // `new_left` wires `floor = ceil` structurally.
        assert_eq!(OFDTNANO.floor(Extended::PosInf), max_ns + 1);
        assert_eq!(OFDTNANO.floor(Extended::NegInf), i128::MIN);
    }

    // ── OFDTSECS spot checks ────────────────────────────────────

    #[test]
    fn ofdtsecs_epoch() {
        assert_eq!(
            OFDTSECS.ceil(Extended::Finite(OffsetDateTime::UNIX_EPOCH)),
            0
        );
        assert_eq!(
            OFDTSECS.inner(0),
            Extended::Finite(OffsetDateTime::UNIX_EPOCH)
        );
    }

    #[test]
    fn ofdtsecs_subsec_rounds_up() {
        let mid = OffsetDateTime::UNIX_EPOCH + Duration::nanoseconds(1);
        assert_eq!(OFDTSECS.ceil(Extended::Finite(mid)), 1);
    }

    #[test]
    fn ofdtsecs_negative_subsec() {
        // 1969-12-31 23:59:59.5 UTC: instant = -0.5 s. ceil rounds
        // up to 0.
        let half_before = OffsetDateTime::UNIX_EPOCH - Duration::milliseconds(500);
        assert_eq!(OFDTSECS.ceil(Extended::Finite(half_before)), 0);
    }

    #[test]
    fn ofdtsecs_saturation_extremes() {
        let max_s = utc_max_s();
        assert_eq!(OFDTSECS.ceil(Extended::PosInf), max_s + 1);
        assert_eq!(OFDTSECS.ceil(Extended::NegInf), i64::MIN);
        // `new_left` wires `floor = ceil` structurally.
        assert_eq!(OFDTSECS.floor(Extended::PosInf), max_s + 1);
        assert_eq!(OFDTSECS.floor(Extended::NegInf), i64::MIN);
    }

    // ── Galois law battery — OFDTNANO (one-sided L) ────────────

    proptest! {
        #[test]
        fn ofdtnano_galois_l(o in arb_extended_offset_dt(), b in any::<i128>()) {
            prop_assert!(conn_laws::conn_galois_l(&OFDTNANO, o, b));
        }

        #[test]
        fn ofdtnano_floor_le_ceil(o in arb_extended_offset_dt()) {
            prop_assert!(conn_laws::conn_floor_le_ceil(&OFDTNANO, o));
        }

        #[test]
        fn ofdtnano_closure_l(o in arb_extended_offset_dt()) {
            prop_assert!(conn_laws::conn_closure_l(&OFDTNANO, o));
        }

        #[test]
        fn ofdtnano_kernel_l(b in any::<i128>()) {
            prop_assert!(conn_laws::conn_kernel_l(&OFDTNANO, b));
        }

        #[test]
        fn ofdtnano_monotone_l(a in arb_extended_offset_dt(), b in arb_extended_offset_dt()) {
            prop_assert!(conn_laws::conn_monotone_l(&OFDTNANO, a, b));
        }

        #[test]
        fn ofdtnano_idempotent(o in arb_extended_offset_dt()) {
            prop_assert!(conn_laws::conn_idempotent(&OFDTNANO, o));
        }

        #[test]
        fn ofdtnano_roundtrip_ceil(b in arb_unix_nanos_in_range()) {
            prop_assert!(conn_laws::conn_roundtrip_ceil(&OFDTNANO, b));
        }
    }

    // ── Galois law battery — OFDTSECS (one-sided L) ────────────

    proptest! {
        #[test]
        fn ofdtsecs_galois_l(o in arb_extended_offset_dt(), b in any::<i64>()) {
            prop_assert!(conn_laws::conn_galois_l(&OFDTSECS, o, b));
        }

        #[test]
        fn ofdtsecs_floor_le_ceil(o in arb_extended_offset_dt()) {
            prop_assert!(conn_laws::conn_floor_le_ceil(&OFDTSECS, o));
        }

        #[test]
        fn ofdtsecs_closure_l(o in arb_extended_offset_dt()) {
            prop_assert!(conn_laws::conn_closure_l(&OFDTSECS, o));
        }

        #[test]
        fn ofdtsecs_kernel_l(b in any::<i64>()) {
            prop_assert!(conn_laws::conn_kernel_l(&OFDTSECS, b));
        }

        #[test]
        fn ofdtsecs_monotone_l(a in arb_extended_offset_dt(), b in arb_extended_offset_dt()) {
            prop_assert!(conn_laws::conn_monotone_l(&OFDTSECS, a, b));
        }

        #[test]
        fn ofdtsecs_idempotent(o in arb_extended_offset_dt()) {
            prop_assert!(conn_laws::conn_idempotent(&OFDTSECS, o));
        }

        #[test]
        fn ofdtsecs_roundtrip_ceil(b in arb_unix_secs_in_range()) {
            prop_assert!(conn_laws::conn_roundtrip_ceil(&OFDTSECS, b));
        }
    }
}
