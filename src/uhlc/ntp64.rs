//! `NTP64 ↔ u64` iso. `NTP64` is a transparent newtype with no
//! internal invariant (`uhlc-rs/src/ntp64.rs:75`: `pub struct
//! NTP64(pub u64)`), so the forward/back pair is direct field
//! access and the iso laws hold trivially.

use uhlc::NTP64;

const fn ntp64_to_u64(t: NTP64) -> u64 {
    t.0
}
const fn u64_to_ntp64(n: u64) -> NTP64 {
    NTP64(n)
}

crate::iso! {
    /// `NTP64 ↔ u64` — lossless iso over the transparent newtype.
    pub NDURU064 : NTP64 => u64 {
        forward: ntp64_to_u64,
        back:    u64_to_ntp64,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::conn::{ConnL, ConnR};
    use crate::prop::conn as conn_laws;
    use proptest::prelude::*;

    // `NTP64` doesn't derive `Debug`, so proptest strategies can't
    // yield `NTP64` directly (shrink display would fail to print).
    // Generate a `u64` and construct `NTP64` in the body instead.

    proptest! {
        #[test]
        fn iso_roundtrip_l(n in any::<u64>()) {
            let t = NTP64(n);
            prop_assert!(conn_laws::iso_roundtrip_l(&NDURU064.conn_l(), t));
        }
        #[test]
        fn roundtrip_ceil(n in any::<u64>()) {
            prop_assert!(conn_laws::roundtrip_ceil(&NDURU064.conn_l(), n));
        }
        #[test]
        fn galois_l(n in any::<u64>(), m in any::<u64>()) {
            let t = NTP64(n);
            prop_assert!(conn_laws::galois_l(&NDURU064.conn_l(), t, m));
        }
        #[test]
        fn galois_r(n in any::<u64>(), m in any::<u64>()) {
            let t = NTP64(n);
            prop_assert!(conn_laws::galois_r(&NDURU064.conn_r(), t, m));
        }
        #[test]
        fn floor_le_ceil(n in any::<u64>()) {
            let t = NTP64(n);
            prop_assert!(conn_laws::floor_le_ceil(&NDURU064, t));
        }
    }

    #[test]
    fn boundary_values() {
        // The two corners of the u64 range round-trip losslessly.
        assert_eq!(crate::conn::ceil(&NDURU064, NTP64(0)), 0);
        assert_eq!(crate::conn::upper(&NDURU064, 0), NTP64(0));
        assert_eq!(crate::conn::ceil(&NDURU064, NTP64(u64::MAX)), u64::MAX);
        assert_eq!(crate::conn::upper(&NDURU064, u64::MAX), NTP64(u64::MAX));
    }
}
