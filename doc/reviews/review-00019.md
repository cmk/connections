# MR !19 — `conn::time` per-domain restructure

## Summary

- Split `src/conn/time.rs` (~1144 lines, five `Conn` constants, four
  `*_preorder` proptest mods, five Conn-specific test mods) into a
  slim parent file plus four domain-typed sub-modules, mirroring
  `conn::fixed`'s layout:
    - `src/conn/time.rs` — parent: module docs + `pub mod`
      declarations + `pub use` re-exports so the public path stays
      `connections::conn::time::DURNSECS`.
    - `src/conn/time/date.rs` — `DATEJDAY` + Date preorder battery.
    - `src/conn/time/clock.rs` — `TIMENANO` + `TIMESECS` + Time
      preorder battery.
    - `src/conn/time/duration.rs` — `DURNSECS` + Duration preorder
      battery.
    - `src/conn/time/datetime.rs` — `PDTMDATE` + PrimitiveDateTime
      preorder battery.
- Update `README.md`'s `## Layout` tree: show `conn/time/` as a
  directory (not `conn/time.rs`).

Pure structural refactor — every constant, every spot check, every
proptest stays. The only behavior change visible to callers is the
test-name path: `conn::time::tests::datejday::galois_l` is now
`conn::time::date::tests::galois_l`. The public API surface is
identical thanks to the parent's `pub use` re-exports.

Originally this branch also carried a `task: Rename src/conn/mod.rs
→ src/conn.rs` commit, which has since shipped in MR !18 ("Drop
Ple; adopt Eq + PartialOrd"). After rebasing on main that commit
was dropped (`patch contents already upstream`), and the four `Ple`
impls this MR placed in the parent file have been removed in the
conflict resolution — the time-crate types derive `Eq + PartialOrd`
upstream and need no per-crate trait impls.

## Test plan

- [ ] `cargo test --workspace` — 1626 lib tests pass (same total as
      pre-restructure post-MR !18).
- [ ] `cargo test --doc` — 18 doctests pass (same total; paths now
      report as `conn::time::clock::TIMENANO` etc.).
- [ ] `cargo clippy --all-targets --no-deps -- -D warnings` — clean.
- [ ] `cargo doc --no-deps` — 5 pre-existing warnings (i16/i32/i64/i128
      module-vs-primitive, `[arb]` link); no new warnings.
- [ ] Pre-commit hook green on every commit.
- [ ] Manual smoke: `connections::conn::time::DURNSECS.ceil(...)` still
      compiles and behaves identically (the public path is unchanged).

## Local review (rebased, 2026-04-26)

**Branch:** sprint/time-restructure (rebased on origin/main post-MR-!18)
**Commits:** 2 (origin/main..sprint/time-restructure)
**Reviewer:** Claude (sonnet, independent)

---

### Commit Hygiene

`task:` and `doc:` prefixes both in CLAUDE.md's allowlist; the
original `refactor:` prefix on the split commit was flagged as a
must-fix and amended to `task:`.

### Code Quality

**Const body fidelity — no semantic drift.** All five Conn const
bodies (`DATEJDAY`, `TIMENANO`, `TIMESECS`, `DURNSECS`, `PDTMDATE`)
are byte-for-byte identical to the post-MR-!18 baseline. No `Ple`
imports or impls survive in the parent or sub-modules. All four
`lattice_antisymmetric` calls use the 2-arg form.

**Parent file** carries only module docs + `pub mod` declarations +
`pub use` re-exports — matches `conn::fixed.rs` template exactly.

**`pub use` re-exports** cover all five constants; the public path
`connections::conn::time::DURNSECS` (etc.) remains intact. No
caller migration needed.

### Test Coverage

20 preorder tests (5 per type × 4 types) and the full Galois law
battery for each Conn — all present in their respective sub-modules.
1626 lib + 18 doctests, same totals as `origin/main`. No `#[ignore]`
annotations introduced.

### Plan Conformance

T1 (split) and T2 (README Layout `conn/time/` as directory) both
present.

### Risks

`lib.rs` re-exports and the README doctest both still resolve
through the `pub use` family-flat path. No import-site changes
needed elsewhere.

### Recommendations

**Must fix before push:** none remaining.

**Follow-up (future work):** none.
