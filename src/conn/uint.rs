//! Unsigned-integer connections: `u_N → u_M` widening and `i_N → u_M`
//! saturating cross-sign casts.
//!
//! Two families, both single-sided ([`Conn::new_left`]):
//!
//! - **`U??U??`** — `Conn<u_N, u_M>` for `N < M`. `ceil` is the
//!   `as`-upcast (lossless); `inner` saturates at `u_N::MAX`.
//! - **`I??U??`** — `Conn<i_N, u_M>` for `N ≤ M`. `ceil` clips negative
//!   inputs to `0`, then upcasts; `inner` saturates at `i_N::MAX`. The
//!   `bits(i_N) ≤ bits(u_M)` constraint guarantees the positive half of
//!   `i_N` fits in `u_M` losslessly.
//!
//! Mirrors `Data.Connection.Word` from the upstream Haskell `connections`
//! library — see the type-code legend in [`crate`].

use crate::conn::Conn;

// ── U??U??: unsigned widen + saturating-narrow inner ────────────────

macro_rules! uint_uint {
    ($NAME:ident, $A:ty, $B:ty) => {
        #[doc = concat!("`", stringify!($A), " → ", stringify!($B), "` saturating cast.")]
        pub const $NAME: Conn<$A, $B> = {
            fn ceil(x: $A) -> $B {
                x as $B
            }
            fn inner(x: $B) -> $A {
                let cap = <$A>::MAX as $B;
                let clipped = if x > cap { cap } else { x };
                clipped as $A
            }
            Conn::new_left(ceil, inner)
        };
    };
}

uint_uint!(U08U16, u8, u16);
uint_uint!(U08U32, u8, u32);
uint_uint!(U08U64, u8, u64);
uint_uint!(U16U32, u16, u32);
uint_uint!(U16U64, u16, u64);
uint_uint!(U32U64, u32, u64);

// ── I??U??: signed → unsigned saturating cast (saturate at 0) ───────

macro_rules! int_uint {
    ($NAME:ident, $A:ty, $B:ty) => {
        #[doc = concat!(
                    "`",
                    stringify!($A),
                    " → ",
                    stringify!($B),
                    "` saturating cast: negatives clip to 0; `inner` saturates at source max."
                )]
        pub const $NAME: Conn<$A, $B> = {
            fn ceil(x: $A) -> $B {
                if x < 0 { 0 } else { x as $B }
            }
            fn inner(x: $B) -> $A {
                let cap = <$A>::MAX as $B;
                let clipped = if x > cap { cap } else { x };
                clipped as $A
            }
            Conn::new_left(ceil, inner)
        };
    };
}

int_uint!(I08U08, i8, u8);
int_uint!(I08U16, i8, u16);
int_uint!(I16U16, i16, u16);
int_uint!(I08U32, i8, u32);
int_uint!(I16U32, i16, u32);
int_uint!(I32U32, i32, u32);
int_uint!(I08U64, i8, u64);
int_uint!(I16U64, i16, u64);
int_uint!(I32U64, i32, u64);
int_uint!(I64U64, i64, u64);

#[cfg(test)]
mod tests {
    use super::*;

    // ── Spot checks ────────────────────────────────────────────────

    #[test]
    fn uint_widening_ceil_at_boundaries() {
        assert_eq!(U08U16.ceil(0u8), 0u16);
        assert_eq!(U08U16.ceil(u8::MAX), u8::MAX as u16);
        assert_eq!(U08U32.ceil(u8::MAX), u8::MAX as u32);
        assert_eq!(U08U64.ceil(u8::MAX), u8::MAX as u64);
        assert_eq!(U16U32.ceil(u16::MAX), u16::MAX as u32);
        assert_eq!(U16U64.ceil(u16::MAX), u16::MAX as u64);
        assert_eq!(U32U64.ceil(u32::MAX), u32::MAX as u64);
    }

    #[test]
    fn uint_widening_inner_saturates_at_source_max() {
        assert_eq!(U08U16.inner(u16::MAX), u8::MAX);
        assert_eq!(U08U32.inner(u32::MAX), u8::MAX);
        assert_eq!(U08U64.inner(u64::MAX), u8::MAX);
        assert_eq!(U16U32.inner(u32::MAX), u16::MAX);
        assert_eq!(U16U64.inner(u64::MAX), u16::MAX);
        assert_eq!(U32U64.inner(u64::MAX), u32::MAX);
        // Below cap is identity-cast back.
        assert_eq!(U08U16.inner(50), 50);
        assert_eq!(U16U64.inner(60_000), 60_000);
    }

    #[test]
    fn int_uint_ceil_clips_negatives_to_zero() {
        assert_eq!(I08U08.ceil(-5), 0);
        assert_eq!(I08U16.ceil(-128), 0);
        assert_eq!(I16U32.ceil(-32_768), 0);
        assert_eq!(I32U64.ceil(-1), 0);
        assert_eq!(I64U64.ceil(i64::MIN), 0);
    }

    #[test]
    fn int_uint_ceil_passes_non_negative() {
        assert_eq!(I08U08.ceil(0), 0);
        assert_eq!(I08U08.ceil(127), 127);
        assert_eq!(I08U16.ceil(127), 127);
        assert_eq!(I16U32.ceil(32_767), 32_767);
        assert_eq!(I32U64.ceil(i32::MAX), i32::MAX as u64);
        assert_eq!(I64U64.ceil(i64::MAX), i64::MAX as u64);
    }

    #[test]
    fn int_uint_inner_saturates_at_source_max() {
        assert_eq!(I08U08.inner(u8::MAX), i8::MAX);
        assert_eq!(I08U16.inner(u16::MAX), i8::MAX);
        assert_eq!(I16U16.inner(u16::MAX), i16::MAX);
        assert_eq!(I08U32.inner(u32::MAX), i8::MAX);
        assert_eq!(I32U32.inner(u32::MAX), i32::MAX);
        assert_eq!(I08U64.inner(u64::MAX), i8::MAX);
        assert_eq!(I64U64.inner(u64::MAX), i64::MAX);
        // Below cap is identity-cast back.
        assert_eq!(I16U32.inner(20_000), 20_000);
    }

    #[test]
    fn int_uint_galois_at_mid_positive() {
        // Exercises the active branch (`a >= 0`, ceil widens, inner is
        // below cap so identity-casts back) — proptest covers this too,
        // but proptest's `any::<iN>()` weights heavily toward boundary
        // values; this fixes a representative middle point.
        for (a, b) in [(50i8, 100u16), (50i8, 49u16), (100i8, 100u16)] {
            assert_eq!(
                I08U16.ceil(a) <= b,
                a as i32 <= I08U16.inner(b) as i32,
                "I08U16 galois_upper @ ({a}, {b})"
            );
        }
    }

    // ── Property tests ─────────────────────────────────────────────
    //
    // Single-sided Galois connection (`Conn::new_left`) laws:
    //
    //   galois_upper:   ceil(a) ≤ b  ⟺  a ≤ inner(b)
    //   ceil_monotone:  a1 ≤ a2  ⟹  ceil(a1) ≤ ceil(a2)
    //   inner_monotone: b1 ≤ b2  ⟹  inner(b1) ≤ inner(b2)
    //   kernel:         ceil(inner(b)) ≤ b

    macro_rules! single_sided_props {
        ($mod_name:ident, $CONN:expr, $arb_src:expr, $arb_tgt:expr) => {
            mod $mod_name {
                use super::*;
                use proptest::prelude::*;

                proptest! {
                    #[test]
                    fn galois_upper(a in $arb_src, b in $arb_tgt) {
                        prop_assert_eq!($CONN.ceil(a) <= b, a <= $CONN.inner(b));
                    }

                    #[test]
                    fn ceil_monotone(a1 in $arb_src, a2 in $arb_src) {
                        let (lo, hi) = if a1 <= a2 { (a1, a2) } else { (a2, a1) };
                        prop_assert!($CONN.ceil(lo) <= $CONN.ceil(hi));
                    }

                    #[test]
                    fn inner_monotone(b1 in $arb_tgt, b2 in $arb_tgt) {
                        let (lo, hi) = if b1 <= b2 { (b1, b2) } else { (b2, b1) };
                        prop_assert!($CONN.inner(lo) <= $CONN.inner(hi));
                    }

                    #[test]
                    fn kernel(b in $arb_tgt) {
                        prop_assert!($CONN.ceil($CONN.inner(b)) <= b);
                    }
                }
            }
        };
    }

    single_sided_props!(u08u16, U08U16, any::<u8>(), any::<u16>());
    single_sided_props!(u08u32, U08U32, any::<u8>(), any::<u32>());
    single_sided_props!(u08u64, U08U64, any::<u8>(), any::<u64>());
    single_sided_props!(u16u32, U16U32, any::<u16>(), any::<u32>());
    single_sided_props!(u16u64, U16U64, any::<u16>(), any::<u64>());
    single_sided_props!(u32u64, U32U64, any::<u32>(), any::<u64>());

    single_sided_props!(i08u08, I08U08, any::<i8>(), any::<u8>());
    single_sided_props!(i08u16, I08U16, any::<i8>(), any::<u16>());
    single_sided_props!(i16u16, I16U16, any::<i16>(), any::<u16>());
    single_sided_props!(i08u32, I08U32, any::<i8>(), any::<u32>());
    single_sided_props!(i16u32, I16U32, any::<i16>(), any::<u32>());
    single_sided_props!(i32u32, I32U32, any::<i32>(), any::<u32>());
    single_sided_props!(i08u64, I08U64, any::<i8>(), any::<u64>());
    single_sided_props!(i16u64, I16U64, any::<i16>(), any::<u64>());
    single_sided_props!(i32u64, I32U64, any::<i32>(), any::<u64>());
    single_sided_props!(i64u64, I64U64, any::<i64>(), any::<u64>());
}
