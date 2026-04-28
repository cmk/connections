//! **Deprecated module path — see [`crate::fixed::i128`].**
//!
//! Re-export shim so existing `crate::int::i128::*` references continue
//! to resolve during the int → fixed migration. Removed in T10.

pub use crate::fixed::i128::*;
