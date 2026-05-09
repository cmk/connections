//! Conns sourced from [`super::F032`] (`ExtendedFloat<f32>`).
//!
//! Houses `F032F016` (`ExtendedFloat<f32> -> ExtendedFloat<f16>`)
//! behind the `f16` cargo feature.

#[cfg(feature = "f16")]
use super::f016::{F016, ceil_f32_f16, floor_f32_f16};
#[cfg(feature = "f16")]
use super::{ExtendedFloat, F032};

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
