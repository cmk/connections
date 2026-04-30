//! Galois-law proptest battery for `conn::std::u8`.
//!
//! Hosted as an integration test (separate crate) so the lib-test
//! binary stays small — same precedent as
//! `tests/conn_fixed_u<width>_galois.rs`.

#[allow(unused_imports)]
use connections::conn::{ViewL, ViewR};
use connections::fixed::u8::*;
use proptest::prelude::*;

// Left-Galois single-sided battery: `galois_upper`, monotonicity,
// kernel, idempotent. **`galois_lower` is intentionally omitted**
// — for `Conn::new_left` (where `floor = ceil`), the right-Galois
// bi-implication `inner(b) ≤ a ⟺ b ≤ floor(a)` fails by design at
// saturation plateaus. That asymmetry is the defining property of
// "single-sided"; only one Galois direction holds. See the review
// thread on MR !27 for the worked counter-example at
// `(a = i32::MIN, b = i8::MIN)`.
macro_rules! single_sided_props {
    ($mod_name:ident, $CONN:path, $arb_src:expr, $arb_tgt:expr) => {
        mod $mod_name {
            use super::*;

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
                #[test]
                fn idempotent(a in $arb_src) {
                    let once = $CONN.inner($CONN.ceil(a));
                    let twice = $CONN.inner($CONN.ceil(once));
                    prop_assert_eq!(once, twice);
                }
            }
        }
    };
}

single_sided_props!(i008u008, I008U008, any::<i8>(), any::<u8>());

// §2 U→U narrowing into u8
single_sided_props!(u016u008, U016U008, any::<u16>(), any::<u8>());
single_sided_props!(u032u008, U032U008, any::<u32>(), any::<u8>());
single_sided_props!(u064u008, U064U008, any::<u64>(), any::<u8>());
single_sided_props!(u128u008, U128U008, any::<u128>(), any::<u8>());

// §4 I→U narrowing into u8
single_sided_props!(i016u008, I016U008, any::<i16>(), any::<u8>());
single_sided_props!(i032u008, I032U008, any::<i32>(), any::<u8>());
single_sided_props!(i064u008, I064U008, any::<i64>(), any::<u8>());
single_sided_props!(i128u008, I128U008, any::<i128>(), any::<u8>());
