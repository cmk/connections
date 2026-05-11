# MR !60 — Plan 37: Restore conn.rs doctests cut by Plan 29

## Summary

- Restores the 14 worked doctests stripped from `src/conn.rs` in
  commit `5a4a033` (Plan 29) when the file was refactored to the
  phantom-kind `Conn<A, B, K>` + `ConnK : ConnL + ConnR` shape. Free-fn
  examples (`interval`, `midpoint`, `truncate{,1,2}`, `round{,1,2}`,
  `median` ×2) live at the function-definition sites unchanged in
  spirit. Inherent-method examples that had previously sat on free
  `upper` / `ceiling` / `ceiling1` / `floor1` move to the four
  inherent methods on `Conn<_, _, L>` / `Conn<_, _, R>` that replaced
  them; `ceiling*` is renamed to `ceil*` per the Plan 36 surface.
  The `compose!` macro's `ignore`-fenced placeholder is replaced
  with the three-step `Conn::identity()` example.
- The `median` examples no longer have access to the old 3-arg
  `Conn::new(ceil, inner, floor)` constructor; both rebuild their
  triple via the `conn_k!` declaration macro inline (an i32-ordered
  lattice for the integer-median example, and a custom N5 lattice
  over `ExtendedFloat<f32>` for the NaN-escalation example). The
  `round` example's `F064F032.inner(...)` call (also gone) is
  rewritten as `F064F032.upper(...)`, the surviving `ConnL`
  embedding-side method.
- Adds a new `## ConnK` subsections under `# Usage` in `src/lib.rs`:
  the new section contains a 9-bullet index linking each `ConnK`
  helper to its per-fn doctest (`median`'s two examples co-locate
  under one bullet). The π-bracket pedagogical thread (`upper` →
  `interval` → `midpoint` → `round1` Newton step → `round2`
  catastrophic cancellation) now reads coherently in `cargo doc`.

## Test plan

- [ ] `cargo test --doc` — 51 passed, 9 ignored, 0 failed. 14 newly
      restored doctests included (compose!, Conn::ceil, Conn::upper,
      Conn::ceil1, Conn::floor1, interval, midpoint, truncate,
      truncate1, truncate2, round, round1, round2, median ×2; plus
      the `## ConnL` exemplar mirror in lib.rs).
- [ ] `cargo test --workspace --quiet` — full suite green
      (45 + 51 = 96 tests, 0 failed).
- [ ] `RUSTDOCFLAGS="-D warnings" cargo doc --no-deps
      --document-private-items` — clean (matches Plan 26's
      pre-push Layer-3 gate; verifies the `## ConnK` bullet
      links resolve).
- [ ] `cargo clippy --all-targets -- -D warnings` — clean.
- [ ] `cargo fmt --all -- --check` — clean.
- [ ] `scripts/check-pii.sh` — exits 0.
- [ ] `scripts/check_readme_mirror.sh` — exits 0 (no README mirror
      applies; per `CLAUDE.md`'s "Doctest + README discipline"
      rule, the mirror covers headline-Conn doctests for new
      `pub const Conn`s, and this sprint introduces none).
