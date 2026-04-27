//! Signed-integer connections: Galois adjoint triples from a
//! range-extended source (`Extended<i_N>` or `Extended<u_N>`) into a
//! signed target `i_M`.
//!
//! Two families, both **full adjoint triples** ([`Conn::new`]):
//!
//! - **`I??I??`** — `Conn<Extended<i_N>, i_M>` with `bits(i_N) <
//!   bits(i_M)`. Signed widening with `Extended` on the source so that
//!   target values below `i_N::MIN` (or above `i_N::MAX`) have a place
//!   to land in the source.
//! - **`U??I??`** — `Conn<Extended<u_N>, i_M>` with `bits(u_N) <
//!   bits(i_M)` (strict — source must fit in target's positive half).
//!
//! Both families share an identical body (mirrors the `conn` helper in
//! Haskell `Data.Connection.Int`). The asymmetry between `ceil` and
//! `floor` lives at the infinity inputs:
//!
//! | input | `ceil` | `floor` |
//! |---|---|---|
//! | `NegInf`     | `i_M::MIN`        | `<source MIN as i_M> − 1` (one below source range) |
//! | `Finite(a)`  | `a as i_M`        | `a as i_M`                                          |
//! | `PosInf`     | `<source MAX as i_M> + 1` (one above source range) | `i_M::MAX` |
//!
//! `inner` partitions the target into three regions: `x ≤ below ↦ NegInf`,
//! `x ≥ above ↦ PosInf`, otherwise `Finite(x as source)` (always lossless
//! by the bit-width constraint).
//!
//! Mirrors `Data.Connection.Int` from the upstream Haskell `connections`
//! library — see the type-code legend in [`crate`].

use crate::conn::Conn;
use crate::extended::Extended;

// One macro covers both Int→Int and Uint→Int. The body is identical;
// only the source type's `MIN`/`MAX` differ. The result is always a
// `Conn<Extended<$A>, $B>` full triple.
//
// Constraints (verified at the call site, not at compile time):
//   - `(<$A>::MIN as $B) - 1` and `(<$A>::MAX as $B) + 1` must fit in $B
//     — guaranteed by `bits($A) < bits($B)` (signed source) or
//     `bits($A) ≤ bits($B) - 1` (unsigned source, equivalent).
//   - `<$B>::MIN < BELOW` and `<$B>::MAX > ABOVE` (i.e. target has room
//     beyond the source range so saturation values are distinct).
macro_rules! ext_int {
    ($NAME:ident, $A:ty, $B:ty) => {
        #[doc = concat!(
                    "`Extended<",
                    stringify!($A),
                    "> → ",
                    stringify!($B),
                    "` adjoint triple."
                )]
        pub const $NAME: Conn<Extended<$A>, $B> = {
            // `BELOW` is one below the source's MIN; `ABOVE` is one
            // above the source's MAX. Both are themselves in the
            // infinity regions: `inner(BELOW) == NegInf` and
            // `inner(ABOVE) == PosInf` (the `<=` / `>=` are inclusive).
            // `Finite(_)` only covers the open interval (BELOW, ABOVE).
            const BELOW: $B = (<$A>::MIN as $B) - 1;
            const ABOVE: $B = (<$A>::MAX as $B) + 1;
            fn ceil(x: Extended<$A>) -> $B {
                match x {
                    Extended::NegInf => <$B>::MIN,
                    Extended::Finite(a) => a as $B,
                    Extended::PosInf => ABOVE,
                }
            }
            fn inner(x: $B) -> Extended<$A> {
                if x <= BELOW {
                    Extended::NegInf
                } else if x >= ABOVE {
                    Extended::PosInf
                } else {
                    Extended::Finite(x as $A)
                }
            }
            fn floor(x: Extended<$A>) -> $B {
                match x {
                    Extended::NegInf => BELOW,
                    Extended::Finite(a) => a as $B,
                    Extended::PosInf => <$B>::MAX,
                }
            }
            Conn::new(ceil, inner, floor)
        };
    };
}

// I??I?? — signed widening (Extended source).
ext_int!(I008I016, i8, i16);
ext_int!(I008I032, i8, i32);
ext_int!(I008I064, i8, i64);
ext_int!(I016I032, i16, i32);
ext_int!(I016I064, i16, i64);
ext_int!(I032I064, i32, i64);

// U??I?? — unsigned source (Extended) into signed target. The strict
// `bits(u_N) < bits(i_M)` constraint guarantees the source range fits
// in the target's positive half.
ext_int!(U008I016, u8, i16);
ext_int!(U008I032, u8, i32);
ext_int!(U008I064, u8, i64);
ext_int!(U016I032, u16, i32);
ext_int!(U016I064, u16, i64);
ext_int!(U032I064, u32, i64);

#[cfg(test)]
mod tests {
    use super::*;

    // ── Spot checks: I??I?? (signed Extended source) ──────────────

    #[test]
    fn int_widening_ceil_at_boundaries() {
        // NegInf saturates to target MIN.
        assert_eq!(I008I016.ceil(Extended::NegInf), i16::MIN);
        // PosInf goes to "one above source max".
        assert_eq!(I008I016.ceil(Extended::PosInf), 128);
        // Finite passes through with sign.
        assert_eq!(I008I016.ceil(Extended::Finite(0)), 0);
        assert_eq!(I008I016.ceil(Extended::Finite(i8::MIN)), -128);
        assert_eq!(I008I016.ceil(Extended::Finite(i8::MAX)), 127);
        // Wider source.
        assert_eq!(I032I064.ceil(Extended::PosInf), (i32::MAX as i64) + 1);
    }

    #[test]
    fn int_widening_floor_at_boundaries() {
        // NegInf goes to "one below source min".
        assert_eq!(I008I016.floor(Extended::NegInf), -129);
        // PosInf saturates to target MAX.
        assert_eq!(I008I016.floor(Extended::PosInf), i16::MAX);
        assert_eq!(I032I064.floor(Extended::NegInf), (i32::MIN as i64) - 1);
        assert_eq!(I032I064.floor(Extended::PosInf), i64::MAX);
    }

    #[test]
    fn int_widening_inner_partitions_target_range() {
        // x ≤ below → NegInf
        assert_eq!(I008I016.inner(-129), Extended::NegInf);
        assert_eq!(I008I016.inner(i16::MIN), Extended::NegInf);
        // x ≥ above → PosInf
        assert_eq!(I008I016.inner(128), Extended::PosInf);
        assert_eq!(I008I016.inner(i16::MAX), Extended::PosInf);
        // -128 ≤ x ≤ 127 → Finite
        assert_eq!(I008I016.inner(-128), Extended::Finite(i8::MIN));
        assert_eq!(I008I016.inner(0), Extended::Finite(0));
        assert_eq!(I008I016.inner(127), Extended::Finite(i8::MAX));
    }

    // ── Spot checks: U??I?? (unsigned Extended source) ────────────

    #[test]
    fn uint_int_ceil_at_boundaries() {
        assert_eq!(U008I016.ceil(Extended::NegInf), i16::MIN);
        assert_eq!(U008I016.ceil(Extended::PosInf), 256);
        assert_eq!(U008I016.ceil(Extended::Finite(0)), 0);
        assert_eq!(U008I016.ceil(Extended::Finite(255)), 255);
        assert_eq!(U016I032.ceil(Extended::PosInf), 65_536);
        assert_eq!(U032I064.ceil(Extended::PosInf), 4_294_967_296);
    }

    #[test]
    fn uint_int_floor_at_boundaries() {
        assert_eq!(U008I016.floor(Extended::NegInf), -1);
        assert_eq!(U008I016.floor(Extended::PosInf), i16::MAX);
        assert_eq!(U008I016.floor(Extended::Finite(255)), 255);
        assert_eq!(U016I032.floor(Extended::NegInf), -1);
        assert_eq!(U032I064.floor(Extended::NegInf), -1);
    }

    #[test]
    fn uint_int_inner_partitions_target_range() {
        assert_eq!(U008I016.inner(-1), Extended::NegInf);
        assert_eq!(U008I016.inner(i16::MIN), Extended::NegInf);
        assert_eq!(U008I016.inner(256), Extended::PosInf);
        assert_eq!(U008I016.inner(i16::MAX), Extended::PosInf);
        assert_eq!(U008I016.inner(0), Extended::Finite(0));
        assert_eq!(U008I016.inner(50), Extended::Finite(50));
        assert_eq!(U008I016.inner(255), Extended::Finite(255));
    }

    // ── Property tests ─────────────────────────────────────────────
    //
    // Full adjoint triple `ceil ⊣ inner ⊣ floor` over a range-extended
    // source. Tests:
    //
    //   galois_upper:    ceil(a) ≤ b   ⟺   a ≤ inner(b)
    //   galois_lower:    inner(b) ≤ a  ⟺   b ≤ floor(a)
    //   ceil_monotone, floor_monotone, inner_monotone
    //   kernel_upper:    ceil(inner(b)) ≤ b
    //   kernel_lower:    b ≤ floor(inner(b))
    //
    // Note: the usual `floor ≤ ceil` invariant does NOT hold here. At
    // `a = NegInf`, `ceil(NegInf) = target::MIN` (far) but
    // `floor(NegInf) = below` (near, just under source range). The two
    // adjoints sit on opposite sides of the inner-induced collapse class.
    // Both `kernel` laws above replace it; together with the four
    // adjointness/monotonicity laws they fully characterise the triple.

    macro_rules! ext_int_props {
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
                    fn galois_lower(a in $arb_src, b in $arb_tgt) {
                        prop_assert_eq!($CONN.inner(b) <= a, b <= $CONN.floor(a));
                    }

                    #[test]
                    fn ceil_monotone(a1 in $arb_src, a2 in $arb_src) {
                        let (lo, hi) = if a1 <= a2 { (a1, a2) } else { (a2, a1) };
                        prop_assert!($CONN.ceil(lo) <= $CONN.ceil(hi));
                    }

                    #[test]
                    fn floor_monotone(a1 in $arb_src, a2 in $arb_src) {
                        let (lo, hi) = if a1 <= a2 { (a1, a2) } else { (a2, a1) };
                        prop_assert!($CONN.floor(lo) <= $CONN.floor(hi));
                    }

                    #[test]
                    fn inner_monotone(b1 in $arb_tgt, b2 in $arb_tgt) {
                        let (lo, hi) = if b1 <= b2 { (b1, b2) } else { (b2, b1) };
                        prop_assert!($CONN.inner(lo) <= $CONN.inner(hi));
                    }

                    #[test]
                    fn kernel_upper(b in $arb_tgt) {
                        prop_assert!($CONN.ceil($CONN.inner(b)) <= b);
                    }

                    #[test]
                    fn kernel_lower(b in $arb_tgt) {
                        prop_assert!(b <= $CONN.floor($CONN.inner(b)));
                    }
                }
            }
        };
    }

    // Strategies for `Extended<T>` — bias toward boundary values.
    // Each generator: 4 boundary singletons (NegInf, PosInf, Finite::MIN,
    // Finite::MAX) plus uniform Finite values, frequency 1:1:1:1:8.
    macro_rules! arb_ext {
        ($name:ident, $T:ty) => {
            fn $name() -> impl proptest::strategy::Strategy<Value = Extended<$T>> {
                use proptest::prelude::*;
                prop_oneof![
                    1 => Just(Extended::NegInf),
                    1 => Just(Extended::PosInf),
                    1 => Just(Extended::Finite(<$T>::MIN)),
                    1 => Just(Extended::Finite(<$T>::MAX)),
                    8 => any::<$T>().prop_map(Extended::Finite),
                ]
            }
        };
    }

    arb_ext!(arb_ext_i8, i8);
    arb_ext!(arb_ext_i16, i16);
    arb_ext!(arb_ext_i32, i32);
    arb_ext!(arb_ext_u8, u8);
    arb_ext!(arb_ext_u16, u16);
    arb_ext!(arb_ext_u32, u32);

    // I??I?? — signed widening
    ext_int_props!(i008i016, I008I016, arb_ext_i8(), any::<i16>());
    ext_int_props!(i008i032, I008I032, arb_ext_i8(), any::<i32>());
    ext_int_props!(i008i064, I008I064, arb_ext_i8(), any::<i64>());
    ext_int_props!(i016i032, I016I032, arb_ext_i16(), any::<i32>());
    ext_int_props!(i016i064, I016I064, arb_ext_i16(), any::<i64>());
    ext_int_props!(i032i064, I032I064, arb_ext_i32(), any::<i64>());

    // U??I?? — unsigned source widening
    ext_int_props!(u008i016, U008I016, arb_ext_u8(), any::<i16>());
    ext_int_props!(u008i032, U008I032, arb_ext_u8(), any::<i32>());
    ext_int_props!(u008i064, U008I064, arb_ext_u8(), any::<i64>());
    ext_int_props!(u016i032, U016I032, arb_ext_u16(), any::<i32>());
    ext_int_props!(u016i064, U016I064, arb_ext_u16(), any::<i64>());
    ext_int_props!(u032i064, U032I064, arb_ext_u32(), any::<i64>());
}
