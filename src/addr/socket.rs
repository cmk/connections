//! Socket-address connections.
//!
//! Two Conns project the `std::net::SocketAddr` sum onto its
//! variant-specific subtypes:
//!
//! - [`SOVXSOV4`] — `SocketAddr → Extended<SocketAddrV4>` — extract
//!   the V4 variant; V6 inputs saturate above all V4 values.
//! - [`SOVXSOV6`] — `SocketAddr → Extended<SocketAddrV6>` — extract
//!   the V6 variant; V4 inputs saturate below all V6 values.
//!
//! The orientation puts the **more-specific** variant type on the
//! right (the natural composition `<chain> → SocketAddr → V4` reads
//! left-to-right toward the projection). All three types implement
//! the same total `Ord` Rust derives for them, so the saturation arms
//! line up cleanly with the Ord-induced lattice: V4 variants sort
//! below all V6 variants, and within each variant Ord is
//! lexicographic over the inner fields.
//!
//! Both Conns ship as one-sided ([`Conn::new_l`] for `SOVXSOV4`,
//! [`Conn::new_r`] for `SOVXSOV6`). The full triple isn't lawful
//! for these projections because the source `SocketAddr`'s MIN/MAX
//! coincides with `inner`'s synthetic-end values, making `inner`
//! non-order-reflecting and forcing a `floor_le_ceil` violation.
//! `new_left`/`new_right` set `floor = ceil` as a fn pointer, so the
//! rounding sandwich holds trivially at the cost of asserting only
//! the constructor's side of Galois (L for `new_left`, R for `new_right`).

use crate::conn::Conn;
use crate::extended::Extended;
use std::net::{Ipv4Addr, Ipv6Addr, SocketAddr, SocketAddrV4, SocketAddrV6};

const SOV4_MIN: SocketAddrV4 = SocketAddrV4::new(Ipv4Addr::UNSPECIFIED, 0);

/// SocketAddrV6's lex-MAX: highest Ipv6, port, flowinfo, and scope_id.
const fn sov6_max() -> SocketAddrV6 {
    SocketAddrV6::new(Ipv6Addr::from_bits(u128::MAX), u16::MAX, u32::MAX, u32::MAX)
}

/// `SocketAddr → Extended<SocketAddrV4>` — V4 extraction from the
/// SocketAddr sum.
///
/// One-sided ceil-adjoint Conn ([`Conn::new_l`]): only `ceil ⊣
/// inner` holds (`galois_l`); the right-Galois law does not. The
/// full triple isn't lawful for this projection because the source
/// SocketAddr's MIN (`V4(0.0.0.0:0)`) coincides with `inner(NegInf
/// rung)`, making `inner` non-order-reflecting at the bottom and
/// forcing a `floor_le_ceil` violation. `new_left` sets `floor =
/// ceil` as a fn pointer, sidestepping the violation.
///
/// V4 inputs project to `Finite(addr)` except at the source MIN
/// where Galois forces `ceil(V4(0.0.0.0:0)) = NegInf`. V6 inputs
/// saturate up to `PosInf` (above all V4 in the coproduct order).
///
/// # Examples
///
/// ```rust
/// use connections::addr::socket::SOVXSOV4;
/// use connections::extended::Extended;
/// use std::net::{Ipv4Addr, Ipv6Addr, SocketAddr, SocketAddrV4, SocketAddrV6};
///
/// let v4 = SocketAddrV4::new(Ipv4Addr::new(127, 0, 0, 1), 80);
/// assert_eq!(connections::conn::ceil(&SOVXSOV4, SocketAddr::V4(v4)), Extended::Finite(v4));
///
/// // V6 input saturates above all V4 values.
/// let v6 = SocketAddrV6::new(Ipv6Addr::LOCALHOST, 80, 0, 0);
/// assert_eq!(connections::conn::ceil(&SOVXSOV4, SocketAddr::V6(v6)),  Extended::PosInf);
///
/// // SOVXSOV4 is a one-sided ConnL — `floor(&SOVXSOV4, ...)` does not
/// // type-check. `upper` is the surviving L-side accessor.
/// let _: SocketAddr = connections::conn::upper(&SOVXSOV4, Extended::Finite(v4));
/// ```
pub const SOVXSOV4: crate::conn::Conn<SocketAddr, Extended<SocketAddrV4>> = {
    fn ceil(s: SocketAddr) -> Extended<SocketAddrV4> {
        match s {
            // Galois forces ceil(MIN) = NegInf because inner(NegInf) = SOV4_MIN
            // (the source MIN) and there's no SocketAddr below it.
            SocketAddr::V4(v4) if v4 == SOV4_MIN => Extended::NegInf,
            SocketAddr::V4(v4) => Extended::Finite(v4),
            SocketAddr::V6(_) => Extended::PosInf,
        }
    }

    fn inner(b: Extended<SocketAddrV4>) -> SocketAddr {
        match b {
            Extended::NegInf => SocketAddr::V4(SOV4_MIN),
            Extended::Finite(v4) => SocketAddr::V4(v4),
            // Galois L's right adjoint formula: inner(PosInf) = sup{a : ceil(a) ≤ PosInf}.
            // PosInf is top, so all a satisfy → sup = source MAX = V6(sov6_max()).
            Extended::PosInf => SocketAddr::V6(sov6_max()),
        }
    }

    Conn::new_l(ceil, inner)
};

/// `SocketAddr → Extended<SocketAddrV6>` — V6 extraction from the
/// SocketAddr sum.
///
/// One-sided floor-adjoint Conn ([`Conn::new_r`]): only `inner ⊣
/// floor` holds (`galois_r`); the left-Galois law does not. The
/// full triple isn't lawful here because the source SocketAddr's MAX
/// (`V6(SOV6_MAX)`) coincides with `inner(PosInf rung)`, making
/// `inner` non-order-reflecting at the top and forcing a
/// `floor_le_ceil` violation. `new_right` sets `ceil = floor` as a fn
/// pointer, sidestepping the violation.
///
/// V6 inputs project to `Finite(addr)` except at the source MAX
/// where Galois forces `floor(V6(MAX)) = PosInf`. V4 inputs saturate
/// down to `NegInf` (below all V6 in the coproduct order).
///
/// # Examples
///
/// ```rust
/// use connections::addr::socket::SOVXSOV6;
/// use connections::extended::Extended;
/// use std::net::{Ipv4Addr, Ipv6Addr, SocketAddr, SocketAddrV4, SocketAddrV6};
///
/// let v6 = SocketAddrV6::new(Ipv6Addr::LOCALHOST, 80, 0, 0);
/// assert_eq!(connections::conn::floor(&SOVXSOV6, SocketAddr::V6(v6)), Extended::Finite(v6));
///
/// // V4 input saturates below all V6 values.
/// let v4 = SocketAddrV4::new(Ipv4Addr::new(127, 0, 0, 1), 80);
/// assert_eq!(connections::conn::floor(&SOVXSOV6, SocketAddr::V4(v4)), Extended::NegInf);
///
/// // SOVXSOV6 is a one-sided ConnR — `ceil(&SOVXSOV6, ...)` does not
/// // type-check. `lower` is the surviving R-side accessor.
/// let _: SocketAddr = connections::conn::lower(&SOVXSOV6, Extended::Finite(v6));
/// ```
pub const SOVXSOV6: crate::conn::Conn<SocketAddr, Extended<SocketAddrV6>, crate::conn::R> = {
    fn inner(b: Extended<SocketAddrV6>) -> SocketAddr {
        match b {
            // R-Galois `inner(b) ≤ a ⟺ b ≤ floor(a)` with b = NegInf forces
            // inner(NegInf) ≤ a for every source a. The smallest source value
            // satisfying that is the source MIN, V4(0.0.0.0:0) (since Rust's
            // SocketAddr orders V4 < V6).
            Extended::NegInf => SocketAddr::V4(SOV4_MIN),
            Extended::Finite(v6) => SocketAddr::V6(v6),
            Extended::PosInf => SocketAddr::V6(sov6_max()),
        }
    }

    fn floor(s: SocketAddr) -> Extended<SocketAddrV6> {
        match s {
            // V4 saturates to NegInf — no V6 ≤ V4(_).
            SocketAddr::V4(_) => Extended::NegInf,
            // Galois forces floor(MAX) = PosInf because inner(PosInf) = V6(MAX)
            // (the source MAX) and there's no SocketAddr above it.
            SocketAddr::V6(v6) if v6 == sov6_max() => Extended::PosInf,
            SocketAddr::V6(v6) => Extended::Finite(v6),
        }
    }

    Conn::new_r(inner, floor)
};

#[cfg(test)]
mod tests {
    use super::*;
    #[allow(unused_imports)]
    use crate::conn::{ConnL, ConnR};
    use crate::prop::arb::{
        arb_extended_socket_addr_v4, arb_extended_socket_addr_v6, arb_socket_addr,
    };
    use crate::prop::conn as conn_laws;
    use proptest::prelude::*;

    proptest! {
        // ── SOVXSOV4 (one-sided ceil-adjoint) law battery ───────
        //
        // new_left contract: Galois L holds, Galois R does not.
        // floor_le_ceil holds trivially (floor = ceil structurally).

        #[test]
        fn sovxsov4_galois_l(a in arb_socket_addr(), b in arb_extended_socket_addr_v4()) {
            prop_assert!(conn_laws::galois_l(&SOVXSOV4, a, b));
        }

        #[test]
        fn sovxsov4_closure_l(a in arb_socket_addr()) {
            prop_assert!(conn_laws::closure_l(&SOVXSOV4, a));
        }

        #[test]
        fn sovxsov4_kernel_l(b in arb_extended_socket_addr_v4()) {
            prop_assert!(conn_laws::kernel_l(&SOVXSOV4, b));
        }

        #[test]
        fn sovxsov4_idempotent(a in arb_socket_addr()) {
            prop_assert!(conn_laws::idempotent(&SOVXSOV4, a));
        }

        // ── SOVXSOV6 (one-sided floor-adjoint) law battery ──────
        //
        // new_right contract: Galois R holds, Galois L does not.
        // floor_le_ceil holds trivially (ceil = floor structurally).

        #[test]
        fn sovxsov6_galois_r(a in arb_socket_addr(), b in arb_extended_socket_addr_v6()) {
            prop_assert!(conn_laws::galois_r(&SOVXSOV6, a, b));
        }

        #[test]
        fn sovxsov6_closure_r(a in arb_socket_addr()) {
            prop_assert!(conn_laws::closure_r(&SOVXSOV6, a));
        }

        #[test]
        fn sovxsov6_kernel_r(b in arb_extended_socket_addr_v6()) {
            prop_assert!(conn_laws::kernel_r(&SOVXSOV6, b));
        }

        #[test]
        fn sovxsov6_idempotent_r(b in arb_extended_socket_addr_v6()) {
            prop_assert!(conn_laws::idempotent_r(&SOVXSOV6, b));
        }
    }
}
