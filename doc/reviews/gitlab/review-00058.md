# MR !58 — Plan 36: `ConnL`/`ConnR`/`ConnK` rename + README/rustdoc refactor

## Summary

- Reshapes `ViewL`/`ViewR`/`Triple` capability traits as
  `ConnL`/`ConnR`/`ConnK` with method-shape (`conn_l(&self) ->
  Conn<A, B, L>`, `conn_r(&self) -> Conn<A, B, R>`) and blanket impls
  on `Conn<A, B, L>` / `Conn<A, B, R>`. The trait names match the
  value-type spellings on purpose: a generic `T: ConnL<A, B>` bound
  accepts both triple markers and raw `Conn<A, B, L>` values
  uniformly. The old `ConnL` / `ConnR` type aliases are dropped —
  value type is `Conn<A, B>` (L is the default kind) or
  `Conn<A, B, R>` everywhere.
- Pre-1.0, no back-compat aliases ship: `ceiling`, `inner`, `ceiling1`,
  `ceiling2` removed from inherent and trait surface. Final method set
  is exactly `ceil` / `upper` (L-side) and `floor` / `lower` (R-side);
  triples and `ConnK` bounds expose all four. Macro renames:
  `triple!` → `conn_k!`, `compose!` → `compose_k!`; new `compose!`
  forwarder to `compose_l!` mirrors the `K = L` default.
- README + lib.rs preamble + module preambles reordered so everyday
  readers meet `.ceil/.floor/.upper` on a named const (the new "Get
  started in 30 seconds" block) before any trait name. New "Naming
  the methods" sidebar explains the two naming axes (direction vs
  position) and why there's no `.inner` method. New "When NOT to use
  a Conn" section drafted from feedback on runtime-parameterised
  helpers, validation wrappers, and policy-injection sites.

## Test plan

- [ ] `cargo test --workspace` — all 887 lib unit tests pass; all
      11 integration tests (`int_*`, `fixed_nz_iso_galois`,
      `compile_fail`, `macros_feature_smoke`) green; doctest count
      unchanged (44 passed, 11 ignored).
- [ ] `cargo clippy --all-targets -- -D warnings` — clean.
- [ ] `cargo fmt --all -- --check` — clean.
- [ ] Local pre-push hook (`RUSTDOCFLAGS="-D warnings" cargo doc
      --no-deps --features testing --document-private-items`) —
      clean.
- [ ] `scripts/check_readme_mirror.sh` — exits 0 (manifest stays
      empty by design — README narrative examples and const-site
      doctests serve distinct purposes).
- [ ] Spot check: the README "Get started in 30 seconds" block,
      Examples 1, 5, 7 all compile and pass with the new names.

## Local review (2026-05-04)

**Branch:** sprint/connl-rename-and-docs
**Commits:** 8 (origin/main..sprint/connl-rename-and-docs)
**Reviewer:** Claude (sonnet, independent)

---

### Commit Hygiene

Eight commits, all conventional-subject, all atomic for their declared scope. The dependency chain is clean: `doc:` plan → `feat:` rename → `doc:` README → `doc:` lib.rs → `doc:` module preambles → `doc:` time.rs alignment → `doc:` MR description → `fix:` rustdoc links. The `fix:` cleanup commit at the tip (intra-doc link corrections) is slightly unfortunate — it should have been squashed into the preceding `doc:` commit rather than landing as a separate commit, since it fixes omissions introduced three commits earlier. Not a blocking issue for a pre-1.0 sprint, but worth noting: the CLAUDE.md CI-repair protocol (`git commit --fixup`) is the intended shape for this, and `scripts/autosquash.sh` would have collapsed it before push.

---

### Code Quality

**Blanket impls** (`impl ConnL for Conn<A,B,L>` / `impl ConnR for Conn<A,B,R>`): correctly bounded — both endpoints are `Copy`, the method just returns `*self`. The `#[inline]` annotation is appropriate since the body is a single pointer copy. Trait coherence: no overlap risk since `Conn<A,B,L>` and `Conn<A,B,R>` are distinct types (distinct phantom `K`).

**Why-method-not-const explanation** in the `ConnL` trait doc is accurate: constant slots in trait impls cannot reference instance state (`self`), so the blanket impl on `Conn<A,B,L>` genuinely requires method shape to return `*self`. The explanation in the doc comment is correct and cites the right constraint.

**`compose!` forwarder macro**: `macro_rules! compose { ($($t:tt)*) => { $crate::compose_l!($($t)*) }; }` — the `tt*` passthrough is correct and handles all variadic forms. The test `compose_alias_matches_compose_l` in `src/conn.rs:899` confirms it produces the same output as `compose_l!` for a two-operand case.

**`law_battery!` `:expr` flip**: The change from `$c:ty` to `$c:expr` is correctly threaded through all eight public arms and all four `@batch` arms. The `full` batch now adds `use $crate::conn::{ConnL as _, ConnR as _};` so `.conn_l()` / `.conn_r()` resolve on both marker instances and raw `Conn` values. The `l_only` batch adds `ConnL as _`, `r_only` adds `ConnR as _`, `iso_only` adds `ConnL as _`. That's correct. The inlined `floor_le_ceil` and `order_reflecting` blocks are replaced by calls to the free-standing predicates in `prop::conn`, which is a net improvement.

**`ceiling1` / `ceiling2` → `ceil1` / `ceil2`**: fully threaded through both inherent methods on `Conn<A,B,L>` and callers in `src/prop/conn.rs`. The public predicate names in `prop::conn` are `ceiling1_id_kernel` and `ceiling2_id_diag` (old names retained in the predicate function names, though their doc strings updated and their bodies use the renamed methods). This is a mild inconsistency — the predicate function names still say `ceiling1` / `ceiling2` while everything else says `ceil1` / `ceil2` — but those predicates are not part of the public API boundary (they're in `prop::conn`, used only by the law battery) and the function bodies are correct.

**Two stale references in `src/lib.rs`** (lines 190 and 200): a prose comment block that was partially updated. The diff changed line 193 ("floor / ceil are bare function names") and added/updated adjacent lines, but lines 190 and 200 were not updated. The comment still reads:

```
// ergonomic access (`connections::ceiling(&c, x)` rather than the module path).
// …prefer named imports (`use connections::{ceiling, floor};`)
```

`connections::ceiling` no longer exists as a free function or re-export. `use connections::{ceiling, floor}` would fail to compile (there is no `ceiling` at the crate root). These are non-code comment lines, so they don't break the build, but they will mislead a reader trying to follow the example.

**`src/fixed/i8.rs` line 15 module-doc comment**: `// brings .ceil/.inner in via default methods` — `.inner` was removed. The correct comment is `.ceil/.upper`.

**Stale `.inner` references in prose** across `src/fixed/u32.rs:184`, `u64.rs:175`, `u8.rs:319`, `u128.rs:215`, `u16.rs:224`, and `src/prop/arb.rs:428`: these are in doc comments and test-comment prose, not in code expressions. They reference method names that no longer exist on the public API. They're not wrong about what the function *does* (the embedding direction), but a reader copy-pasting `.inner(...)` will get a compile error. They should be `Q032Q031.upper(...)` etc. This is a lower-priority cleanup.

---

### Test Coverage

**Blanket-impl smoke test**: `conn_value_impls_trait` in `src/conn.rs:955` directly tests that a raw `Conn<i64,i32,L>` flows through a `T: ConnL<i64,i32>` bound and that a raw `Conn<i64,i32,R>` flows through `T: ConnR<i64,i32>`. Present and correct.

**`compose!` forwarder**: `compose_alias_matches_compose_l` in `src/conn.rs:899` proves the two-operand case produces the same value. The test only exercises two operands; `compose_l!` supports N operands via the variadic arm. There is no test that `compose!(A, B, C)` (three operands) forwards correctly. Given `compose_l!` is tested separately at three operands, this is an acceptable gap but worth noting.

**`law_battery!` `:expr` on both shapes**: The battery is now exercised via marker values (`DURNSECS`, `U032CHAR`, `F064F032` are triple markers) and one-sided `Conn` consts (`U032IPV4`, `U128IPV6` isos in `addr/ip.rs` are actually triple shapes via `iso!`; one-sided `l_only` examples are `fixed/i8`, `i16`, `i32`, `i64`, `i128`). The `law_battery!` itself is never directly called with a raw `Conn<A,B,L>` const in the `full` batch (which would fail at compile time on `floor_le_ceil`/`order_reflecting` since those are `ConnK`-bound). That's correct — callers of `full` use triple-shaped values, callers of `l_only`/`r_only` use one-sided consts.

**No new `#[ignore]` tests**: confirmed.

---

### Plan Conformance

**T1** (reshape `ViewL`/`ViewR` → `ConnL`/`ConnR` traits): present and complete. Traits have exactly the method shape specified. Blanket impls are present. Inherent method trimming is complete — `ceiling`, `inner`, `ceiling1`, `ceiling2` removed; `ceil1`/`ceil2` renamed from `ceiling1`/`ceiling2`. Two-sided helpers updated to use `t.conn_l()` / `t.conn_r()` calls.

**T1b** (rename `Triple` → `ConnK`): present and complete. The blanket `impl<T> ConnK for T where T: ConnL + ConnR` is present. `Conn<A,B,L>` and `Conn<A,B,R>` correctly do not auto-satisfy `ConnK`.

**T2** (macro renames): present and complete. `triple!` → `conn_k!`, `compose!` → `compose_k!`, new `compose!` forwarder added. `conn_l!` / `conn_r!` output types updated to `Conn<A,B>` / `Conn<A,B,R>`. All `pub const FOO: ConnL<A,B>` / `ConnR<A,B>` sites updated. `law_battery!` dispatch updated. `lib.rs:200` re-exports updated.

**T3** (re-green and commit): tests pass; committed as one `feat:` commit.

**T4** (README refactor): present — "Get started in 30 seconds" block, "Naming the methods" sidebar, "When NOT to use a Conn" section. Trait mentions demoted. `.inner(...)` substitutions made throughout. **One regression**: Example 6 (the `.conn_l().ceil(...)` assert_eq) became a self-equality tautology; see Recommendations.

**T5** (`lib.rs` preamble reorder): present — "Cast operations" leads, then composition, then codegen macros, then naming. `ViewL`/`ViewR`/`Triple` references updated. **Two stale prose lines** at 190 and 200 (`connections::ceiling` and `use connections::{ceiling, floor}`).

**T6** (module preamble unification): present — `float.rs`, `fixed.rs` preambles updated with constants table and runnable example. `time.rs` doctest updated to use `.upper` and drop `// brings .ceil/.inner`.

**T7** (lift representative doctests): the plan said "move (don't copy) one ~5-line doctest from README to the const def site." All five named consts (`U032I032`, `F064F032`, `DURNSECS`, `U032CHAR`, `IPVXIPV4`) have substantial doctests at their definition sites. The agent reported this as no-op since const sites already had rich doctests. The plan's intent to keep a single authoritative copy was not enforced; both README and const-site copies remain. Minor scope slip; not recorded in the plan's Review section.

**T8** (activate README mirror manifest): `scripts/readme_mirrors.txt` is empty by design per the MR description, and `check_readme_mirror.sh` exits 0. The agent chose not to mirror the duplicated examples on the grounds they "serve distinct purposes." Reasonable call but not recorded in the plan's Review section (which remains unfilled).

---

### Risks

**Downstream breaking changes**: Pre-1.0, but the rename from `ViewL`/`ViewR`/`Triple` to `ConnL`/`ConnR`/`ConnK`, removal of `ceiling`/`inner` methods, and drop of `ConnL<A,B>`/`ConnR<A,B>` aliases are source-breaking for any code currently compiling against `origin/main`. The agogo crate is the named downstream; per the plan, the agogo-side fix is out of scope and tracked as deferred. The README/CHANGELOG should call this out explicitly as a breaking change — there's no explicit "Breaking changes in this release" section.

**`prop/conn.rs` function names**: `ceiling1_id_kernel` and `ceiling2_id_diag` retain old names while their bodies and doc strings reference `ceil1` / `ceil2`. Inconsistency that will confuse readers; not a correctness issue.

**`src/fixed/i8.rs:15` doc comment**: `// brings .ceil/.inner in via default methods` — `.inner` is removed; misleads readers of the module-level example.

**`src/prop/arb.rs:428` comment**: `STDRU128.inner` — refers to a method that no longer exists. Prose-only.

**No TODOs, stubs, or unsafe code**: confirmed clean.

**The plan's `## Review` section is unfilled** (`To be filled in after implementation.`). Per CLAUDE.md step 6, this should record deviations and design decisions. T7's "no-op" call and T8's "distinct purposes" decision for the mirror manifest are both worth recording there.

---

### Recommendations

**Must fix before push:**

1. **`README.md` Example 6, lines 537–542**: The `assert_eq!` is self-equal (`U008I016.conn_l().ceil(x) == U008I016.conn_l().ceil(x)`) and the comment says "ceil is the named alias of ceil." The original intent was to demonstrate that `ceiling` and `ceil` produced the same result (the two old names). Since `ceiling` is gone, the assertion should be removed or replaced with something meaningful — e.g., `U008I016.conn_l().ceil(x) == U008I016.ceil(x)` to show that `.conn_l().ceil()` and `.ceil()` are equivalent via the blanket impl.

2. **`src/lib.rs` lines 190 and 200**: The prose comment still reads `connections::ceiling(&c, x)` (line 190) and `use connections::{ceiling, floor};` (line 200). Neither name exists. Update or drop.

3. **`src/fixed/i8.rs` line 15** module-level doc comment: `// brings .ceil/.inner in via default methods` — `.inner` no longer exists. Change to `.ceil/.upper`.

4. **Plan `## Review` section** (`doc/plans/plan-2026-05-04-01.md:224`): fill it in before push per CLAUDE.md step 6. Record the T7 "no-op" rationale (const sites already had doctests) and the T8 "empty mirror manifest" decision. One paragraph is sufficient.

**Follow-up (future work):**

- `src/prop/conn.rs` predicate function names `ceiling1_id_kernel` and `ceiling2_id_diag`: rename to `ceil1_id_kernel` and `ceil2_id_diag` for consistency. Low-risk, no behavioral change.
- Stale `.inner` references in prose across `fixed/u*.rs` and `prop/arb.rs`: update to `.upper(...)` / `.lower(...)` as appropriate. No build impact now.
- The `fix:` commit at the tip (rustdoc link fixes) would be cleaner as a `--fixup` squashed into the commit that introduced the broken links. Consider squashing via `scripts/autosquash.sh` before merge.
- Add a three-operand `compose!(A, B, C)` test alongside the existing two-operand alias test to close the variadic coverage gap.
- A "Breaking changes" callout in the README or CHANGELOG would be courteous, even pre-1.0.
