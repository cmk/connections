# MR !7 — `compose_conn!` declarative macro for const composition

## Summary

`Conn<A, B>` stores three bare `fn` pointers by design (`const`-
constructible, `Copy`, no heap). That rules out a generic `.then()`
method — a composed fn would need to capture both input `Conn`s,
which a bare `fn` pointer cannot. Today any "chain two Conns"
use-case either hand-composes at the call site
(`F06F00.ceil(F12F06.ceil(x))`) or hand-writes a new named
constant with its own triple of fn items.

This MR adds `compose_conn!`, a declarative macro that takes two
`const Conn`s and expands to a fresh `const Conn`, covering the
compile-time-known case that accounts for ~95 % of real usage:

```rust
compose_conn! {
    pub const F12F00_VIA_MICRO: Conn<Pico, Uni> = F12F06, F06F00;
}
```

The macro parses a full `const`-declaration form because the
emitted `fn ceil / inner / floor` items need explicit signatures,
which Rust fn items cannot infer. The user names only the two
boundary types (`Pico`, `Uni` above); the intermediate type
(`Micro` here) is inferred from `$FIRST.ceil(x): B` being fed to
`$SECOND.ceil(B)` and never appears in the emitted source.

- **`src/conn.rs`** gains the `#[macro_export] macro_rules!
  compose_conn!` definition, placed above the `Conn` struct so the
  macro and the type it composes live side by side. The expansion
  references `$crate::conn::Conn::new` so it resolves from any call
  site.
- **Tests** (seven new, in `conn::tests`): a parity spot check vs.
  the hand-written `F12F00`; left- and right-identity spot checks
  using `Conn::<T, T>::identity()`; and four proptests
  (`compose_conn_agrees_with_hand_written`,
  `_inner_agrees_with_hand_written`, `_galois_upper`,
  `_galois_lower`) using locally-scoped `bounded_pico` /
  `bounded_uni` strategies. All composed constants are declared at
  module scope with `const` so the test exercises the macro's
  compile-time code path, not a runtime wrapper.
- **Docs**: a §Composition paragraph in `src/lib.rs`'s crate doc +
  a runnable doctest; `doc/design.md`'s §Composition now
  distinguishes the aspirational `.then()` from the shipping
  `compose_conn!`. Runtime composition (`DynConn`) stays deferred.

Net: one macro (~13 lines), seven tests, two doc updates. Test
count 505 → 512, all green; clippy clean.

## Test plan

- [x] `cargo build` — clean.
- [x] `cargo test` — 512 passed (505 unit/integration + 2 doc + 5
  new compose), 0 failed, 0 ignored.
- [x] `cargo clippy --all-targets -- -D warnings` — clean.
- [x] Left-identity + right-identity proven at representative
  values (`compose_conn_left_identity`, `_right_identity`),
  confirming the macro interoperates with `Conn::identity()`.
- [x] Seven representative values cross-checked against the hand-
  written `F12F00` (boundaries 0, ±1, ±10¹², exact + off-by-one).
