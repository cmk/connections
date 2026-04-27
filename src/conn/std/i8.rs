//! Conns landing on `i8`. Per the right-side-wins module rule, this
//! file hosts every Conn whose destination type is `i8`.
//!
//! - **`I??I008`** narrowing (T3): wider signed → `i8` saturating
//!   cast (`int_int_narrow!`).
//! - **`U??I008`** non-widening (T5): unsigned source → `i8` with
//!   negative-clip on `inner` (`uint_int_sat!`, right-Galois).
//!
//! No widening lands here: `i8` is the narrowest signed primitive,
//! so nothing widens *into* it.
