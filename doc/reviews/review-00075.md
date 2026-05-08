# MR !75 — Narrow `lift_l!` / `lift_r!` to `:path` (MR !74 follow-up)

## Summary

- Address three findings from `claude-review` on the merged MR !74
  (post-merge, advisory). Two were `must-fix`, one was follow-up.
- Narrow `lift_l!` and `lift_r!` from `$parent:expr` to
  `$parent:path`, matching `lift_k!`'s constraint and eliminating
  the double-evaluation footgun: with `:expr`, a function-call
  parent like `lift_l!(build_conn())` would silently re-invoke
  `build_conn()` on every `.ceil()` / `.upper()` call. The closure-
  coercion check catches let-bound locals; only the
  global-function-call case slipped through.
- Update the one in-tree expression-form call site
  (`LIFTED_ID_I64`'s parent) to pre-bind the parent Conn to a
  `const`. Refresh the macro rustdoc and the module-level paragraph
  to spell out the rationale.
- Rewrite the misleading
  `lift_k_compose_chain_runtime_smoke` comment that described the
  `compose_l!` constraint as "must be referenceable as paths" — the
  actual constraint is "operand expression must compile to a
  non-capturing closure body".

## Test plan

- [x] `cargo build --features testing --tests` compiles after the
  fragment narrowing (the `:path` strictness trips no other call site).
- [x] `cargo test --features testing --lib extended::` — 40 tests
  pass (no count change; the narrowing is API-tightening only).
- [x] `cargo test --features "testing macros hifi byte" --doc -- extended` —
  6 doctests pass.
- [x] `cargo test --features "testing macros hifi byte" --lib` —
  1494 tests pass (matches MR !74 baseline; no regressions).
- [x] `cargo clippy --all-targets --features testing -- -D warnings` clean.
- [x] `cargo fmt --all -- --check` clean.
- [x] `RUSTDOCFLAGS="-D warnings" cargo doc --no-deps --features testing
  --document-private-items` clean.
- [x] `scripts/check-pii.sh` clean.
- [x] `scripts/check_readme_mirror.sh` clean.
