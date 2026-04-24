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

## Local review (2026-04-24)

**Branch:** `feat/compose-macro`
**Commits:** 3 (origin/main..feat/compose-macro)
**Reviewer:** Claude (sonnet, independent)

---

### Commit Hygiene

`plan:` + `feat:` + `doc:` across three atomic commits, all under
72 characters, conventional prefixes, each leaves the repo buildable.

### Code Quality

- **Macro correctness**: ceil/floor compose covariantly (`FIRST → SECOND`),
  inner contravariantly (`SECOND → FIRST`); matches Galois
  composition and design.md §Composition.
- **Macro hygiene**: `$crate::conn::Conn` path-qualified in the
  expansion, so external callers don't need `Conn` imported for
  anything except the user-written type annotation.
- **Const correctness**: expansion is a real `const`-init; the test
  module declares `F12F00_VIA_MICRO`, `LEFT_ID_COMPOSED`, and
  `RIGHT_ID_COMPOSED` all at `const` scope — no runtime allocation.
- **Clippy**: clean under `-D warnings`.

### Test Coverage

Eight new tests covering: construction (three composed `const`s),
parity vs. hand-written `F12F00`, left + right identity, four
proptests on the composed Conn (agreement + Galois upper/lower),
plus an explicit spot check at the Uni safe boundary
(`|c| = i64::MAX / 10¹²`). `bounded_pico` uses the same
`Just(i64::MAX)` / `Just(i64::MIN + 1)` + `any::<i64>()` pattern
as the existing `bounded_fine` — no generator-bounded-to-safe-
region anti-pattern.

### Plan Conformance

T1, T2, T3 all implemented as specified. No deviations.

### Risks

- `#[macro_export]` is a semver commitment at the next minor bump;
  acknowledged in the MR description.
- `$FIRST`/`$SECOND` evaluate once per `ceil/floor/inner` call.
  Callers pass `const` identifiers (the macro's purpose), so side-
  effect expressions are not a real concern.

### Recommendations

**Must fix before push:**
- ~~`bounded_uni` lacks an explicit boundary spot check per
  CLAUDE.md.~~ **Addressed** — added
  `compose_conn_inner_at_uni_safe_boundary`, which exercises
  `Uni(±limit)` and `Uni(±(limit − 1))` with parity against the
  hand-written `F12F00`.

**Follow-up (not blocking):**
- Monotonicity / `floor_le_ceil` proptests on the composed Conn.
  Composition preserves both structurally; adding them would catch
  future compose-refactor regressions earlier than a Galois
  failure.
- A `compose_conn!` expansion inside `fixed.rs` to replace one of
  the non-adjacent `fix_fix!` constants as a compile-time parity
  regression. Captured in the plan's Deferred section; out of scope
  for this MR.
