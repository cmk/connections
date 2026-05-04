# MR !55 — Plan 35: `conn_l!` / `conn_r!` macros for one-sided Conns

## Summary

- Adds `conn_l!` and `conn_r!` declaration-form macros next to
  `triple!` / `iso!` in `src/conn.rs`. They emit a bare
  `pub const ConnL<A, B> = Conn::new_l(...)` (or `ConnR<A, B>`) from
  a named-field block, completing the macro family for the five Conn
  shapes (`compose!`, `triple!`, `iso!`, `conn_l!`, `conn_r!`).
- Primary motivation is footgun avoidance: `Conn::new_l` takes
  `(ceil, inner)` while `Conn::new_r` takes `(inner, floor)` — the
  positional mismatch means a `new_l → new_r` flip silently swaps the
  slots. Named fields close that hole. The boilerplate savings vs.
  raw `Conn::new_l(...)` is intentionally small (~1 line per site).
- Converts the ~10 hand-written one-sided Conn consts in `time/clock`,
  `time/date`, `time/datetime`, `time/offset`, `time/duration`, and
  `lattice.rs` to the new macros; per-family generator macros stay
  as-is. Public type signatures unchanged at every converted site.

## Test plan

- [ ] `cargo test --workspace` — all green; new
      `conn_l_macro_expands_to_new_l` and
      `conn_r_macro_expands_to_new_r` unit tests visible; existing
      `time/*` round-trip props pass unchanged.
- [ ] `cargo test --doc` — definition-site doctests on `conn_l!` /
      `conn_r!` pass (or are `ignore`-blocked alongside `triple!` /
      `iso!`'s).
- [ ] `cargo clippy --all-targets -- -D warnings` — clean.
- [ ] `cargo fmt --all -- --check` — clean.
- [ ] Local pre-push hook (`RUSTDOCFLAGS="-D warnings" cargo doc
      --no-deps --features testing --document-private-items`) —
      clean.
