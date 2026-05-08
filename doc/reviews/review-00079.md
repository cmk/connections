# Review 79 — Eliminate `Conn<Extended<A>, Extended<B>>` antipattern

## Summary

- Strip `Extended` from both sides of `U032CHAR`, `SDURU064`, `SDURU128`
  and from the `Extended<StdDuration>` codomain of `F064SDUR` /
  `F032SDUR`. Synthetic-top promotion in `inner` preserves Galois L;
  `U032CHAR` and `SDURU064` demote from `conn_k!` to `conn_l!`.
- Add a `scripts/check_no_ext_ext_conn.sh` pre-commit guardrail
  (Layer 1 + Layer 2) that blocks new `Extended<…> => Extended<…>`
  shapes outside `src/extended.rs`, with a `// allow(ext-ext-conn):`
  per-line escape hatch for legitimate exceptions.
- See `doc/plans/plan-2026-05-08-04.md` for the full Verification
  table, dependency graph, and design rationale (why both ConnK
  members had to demote, why synthetic-top in `inner` is the
  correct trade rather than asymmetric stripping).

## Test plan

- [ ] `cargo test --workspace` — all green.
- [ ] `cargo clippy --all-targets -- -D warnings` — clean.
- [ ] `cargo doc --no-deps --features byte,testing,macros --document-private-items` (with `RUSTDOCFLAGS="-D warnings"`) — clean.
- [ ] `bash scripts/check_no_ext_ext_conn.sh` exits 0 on the staged tree.
- [ ] Inject a mock `Extended<X> => Extended<Y>` violation; confirm
      pre-commit blocks the commit.
- [ ] Add `// allow(ext-ext-conn): smoke test` to the mock; confirm
      pre-commit accepts it.
