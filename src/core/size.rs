//! `usize` → `u32` / `u64` pointer-width cast Conns.
//!
//! `usize` is pointer-width (16/32/64-bit by target), so these casts
//! cannot reuse the fixed-width `as`-based std-int macros in
//! [`crate::core`]: an `as`-narrowing *truncates* out-of-range values
//! (`70000_u32 as u16 == 4464`) where the Galois law needs *saturation*.
//! Both Conns therefore clamp with [`TryFrom`], which makes them lawful
//! on every target width rather than only the 64-bit host.
//!
//! - [`SIZEU032`] — `usize → u32`, saturating narrow (a lossless widen
//!   when `usize < u32`, i.e. a 16-bit target).
//! - [`SIZEU064`] — `usize → u64`, saturating embed (the identity iso on
//!   a 64-bit target; a lossless widen on 16/32-bit).
//!
//! Both are one-sided left-Galois ([`Conn::new_l`]): `ceil ⊣ inner`.

use crate::conn::Conn;

/// `usize → u32` saturating narrow (left-Galois).
///
/// `ceil` clamps source values above `u32::MAX` down to `u32::MAX`;
/// `inner` widens losslessly with a FINE_MAX fixup (`inner(u32::MAX) =
/// usize::MAX`). The fixup is what keeps left-Galois true on a 64-bit
/// target, where every `usize > u32::MAX` collapses onto `u32::MAX` under
/// `ceil`: taking `b = u32::MAX` makes the law's LHS `ceil(a) ≤ b`
/// vacuously true, so `a ≤ inner(b)` must hold for *every* `a`, forcing
/// `inner(u32::MAX) = usize::MAX`. Mirrors the fixed-width
/// `uint_uint_narrow!` macro.
///
/// On a 16-bit target `usize` is *narrower* than `u32`, so `ceil` is a
/// lossless widen and `inner` saturates instead — the same two functions
/// stay lawful because both clamp with `TryFrom`.
pub const SIZEU032: Conn<usize, u32> = {
    fn ceil(x: usize) -> u32 {
        u32::try_from(x).unwrap_or(u32::MAX)
    }
    fn inner(y: u32) -> usize {
        if y == u32::MAX {
            usize::MAX
        } else {
            // y < u32::MAX: fits in usize on 32/64-bit; on a 16-bit
            // target it saturates to usize::MAX.
            usize::try_from(y).unwrap_or(usize::MAX)
        }
    }
    Conn::new_l(ceil, inner)
};

/// `usize → u64` saturating embed (left-Galois).
///
/// `ceil` embeds losslessly on every real target (`usize ≤ 64` bits); the
/// `unwrap_or` saturation arm is dead on real hardware and only fires on a
/// hypothetical `> 64`-bit `usize`. `inner` saturates `u64` values above
/// `usize::MAX` down to `usize::MAX`.
///
/// Unlike [`SIZEU032`] there is **no** FINE_MAX fixup: this is a widening
/// (like the fixed-width `uint_uint!` macro), so the saturation cap already
/// lands `inner(u64::MAX) = usize::MAX` on 16/32-bit targets, and on a
/// 64-bit target `usize == u64` makes the whole Conn the identity iso.
pub const SIZEU064: Conn<usize, u64> = {
    fn ceil(x: usize) -> u64 {
        u64::try_from(x).unwrap_or(u64::MAX)
    }
    fn inner(y: u64) -> usize {
        usize::try_from(y).unwrap_or(usize::MAX)
    }
    Conn::new_l(ceil, inner)
};

// ────────────────────────────────────────────────────────────────────
// Tests
// ────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::prop::conn as conn_laws;
    use proptest::prelude::*;

    // ── SIZEU032 saturation / fixup spot checks ───────────────────────

    #[test]
    fn sizeu032_saturates_and_fixes_up() {
        // Width-agnostic: the FINE_MAX fixup pins inner(u32::MAX) to
        // usize::MAX on every target, and small values round-trip.
        assert_eq!(SIZEU032.upper(u32::MAX), usize::MAX);
        assert_eq!(SIZEU032.upper(0), 0);
        assert_eq!(SIZEU032.ceil(1_000), 1_000);
        assert_eq!(SIZEU032.upper(1_000), 1_000);

        // Narrowing saturation only exists where usize is wider than u32
        // (a 64-bit target): source values above u32::MAX clamp down under
        // ceil. On 16/32-bit no usize exceeds u32::MAX, so there is nothing
        // to saturate and `ceil(usize::MAX)` is the lossless `usize::MAX`.
        #[cfg(target_pointer_width = "64")]
        {
            assert_eq!(SIZEU032.ceil(usize::MAX), u32::MAX);
            assert_eq!(SIZEU032.ceil(u32::MAX as usize + 1), u32::MAX);
        }
    }

    // ── SIZEU064 embed spot checks ────────────────────────────────────

    #[test]
    fn sizeu064_embeds_and_saturates() {
        assert_eq!(SIZEU064.upper(u64::MAX), usize::MAX);
        // Lossless embed on the low range: ceil == `as`, and it round-trips.
        for v in [0usize, 1, 1_000, usize::MAX - 1] {
            assert_eq!(SIZEU064.ceil(v), v as u64);
            assert_eq!(SIZEU064.upper(v as u64), v);
        }
    }

    // ── Boundary-biased Galois-law properties ─────────────────────────

    fn arb_usize() -> impl Strategy<Value = usize> {
        prop_oneof![
            Just(0usize),
            Just(usize::MAX),
            Just(u32::MAX as usize),
            any::<usize>()
        ]
    }
    fn arb_u32() -> impl Strategy<Value = u32> {
        prop_oneof![Just(0u32), Just(u32::MAX), any::<u32>()]
    }
    fn arb_u64() -> impl Strategy<Value = u64> {
        prop_oneof![
            Just(0u64),
            Just(u64::MAX),
            Just(usize::MAX as u64),
            any::<u64>()
        ]
    }

    proptest! {
        #[test]
        fn sizeu032_galois_l(a in arb_usize(), b in arb_u32()) {
            prop_assert!(conn_laws::galois_l(&SIZEU032, a, b));
        }
        #[test]
        fn sizeu032_kernel_l(b in arb_u32()) {
            prop_assert!(conn_laws::kernel_l(&SIZEU032, b));
        }
        #[test]
        fn sizeu064_galois_l(a in arb_usize(), b in arb_u64()) {
            prop_assert!(conn_laws::galois_l(&SIZEU064, a, b));
        }
        #[test]
        fn sizeu064_kernel_l(b in arb_u64()) {
            prop_assert!(conn_laws::kernel_l(&SIZEU064, b));
        }
    }
}
