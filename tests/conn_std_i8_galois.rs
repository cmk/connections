//! Galois-law proptest battery for `conn::std::i8`. Integration
//! test — see `tests/conn_std_u8_galois.rs` for rationale.
//!
//! No widening lands on `i8` (it's the narrowest signed primitive),
//! so this file is a placeholder until T3 (I→I narrowing) and T5
//! (U→I non-widening) commits add invocations.
