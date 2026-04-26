# MR !9 — `compose!` macro for compile-time Conn composition

## Summary

- **Add `compose!`** — variadic `macro_rules!` in `src/conn.rs` that
  expands a chain of two or more `Conn` consts into a fresh
  `Conn<Src, Dst>` via nested calls. Non-capturing closures coerce to
  `fn(_) -> _` pointers at the `Conn::new` call site, so the result
  preserves `Conn`'s `Copy` + `const`-constructible shape with no
  changes to the struct itself.
- **Tests** — replace the hand-nested
  `composition_pico_to_uni_matches_ladder_climb` with macro-driven
  equivalents (`compose_two_step_*`, `compose_four_step_*`) and add
  Galois-law preservation checks against a macro-composed
  `Conn<Pico, Uni>` (`compose_inner_then_ceil_is_id`,
  `compose_floor_le_ceil`, `compose_galois_upper`,
  `compose_galois_lower`, `compose_idempotent`). +9 proptest instances,
  test count 505 → 514.
- **`doc/design.md`** — replace the broken pseudo-implementation of
  `Conn::then` (lines 91–112, which couldn't compile against the
  `fn`-pointer struct) with a "Why not a runtime `Conn::then`" section
  documenting the storage-shape constraint and the two future shape
  options (generic-default type params; boxed trait objects). Update
  the combinator table at line 120: `compose!` is the implemented
  primitive, `Conn::then` stays deferred.

## Test plan

- `cargo build` — clean.
- `cargo test --workspace` — 514 passed, up from 505.
- `cargo clippy --all-targets -- -D warnings` — clean.
- `cargo fmt --all -- --check` — matches main's pre-existing drift
  (27 lines across files this MR doesn't touch); no new drift introduced.
- `const F12F00_BIS: Conn<Pico, Uni> = compose!(F12F09, F09F06, F06F03, F03F00);`
  compiles in const context, exercising non-capturing-closure → fn-ptr
  coercion at const-eval.
- `cargo doc --no-deps` — zero warnings on the new macro and design
  doc section.

Deferred (tracked in plan Review):
- Runtime `Conn::then` — re-open when a concrete consumer appears;
  the macro covers all known compile-time use cases.
- `product` / `coproduct` — same shape constraint as `then`.

## Local review (2026-04-26)

**Branch:** sprint/compose-macro
**Commits:** 2 (origin/main..HEAD)
**Reviewer:** Claude (sonnet, independent)

---

### Commit Hygiene

Both commits follow the conventional-commit format with imperative subjects under 72 characters. The split — one `feat:` for the macro and one `doc:` for the review file — is clean. The `feat:` commit includes all of T1, T2, T3, and T4, which is atomic at the "sprint ships" level. That's acceptable given that T1 (red tests) and T2 (macro) were intended to land together anyway.

---

### Code Quality

The macro implementation matches the plan spec verbatim. The `@`-prefix convention for internal arms is correct and documented inline. The `$crate::` prefix on all recursive invocations is properly applied, so the macro is hygienic when called from outside the crate.

One issue:

**The doctest is silently suppressed — `src/conn.rs` line 26.**

The plan's build gates (Verification §, line 275 of the plan) require:

> End-to-end: doctest on `compose!` showing const-binding form + pointwise agreement with `F12F00`.

The review file's test plan (line 333) reaffirms it:

> `const F12F00_BIS: Conn<Pico, Uni> = compose!(F12F09, F09F06, F06F03, F03F00);` compiles in const context...

The doctest at lines 26–33 of `src/conn.rs` is tagged ```` ```ignore ```` rather than ```` ```rust ```` (or at minimum ```` ```rust,no_run ````). `cargo test` silently skips `ignore` blocks; `cargo doc` does not compile them. The const-context coercion that was flagged as an open question in the plan has therefore never been verified by the build system — the human test-plan claim that it "compiles in const context" is unverified.

The correct tag here is ```` ```rust ```` (the example has no I/O, no file dependencies, and the public API is exactly what would be visible to a crate consumer). If the `conn::fixed` items are not re-exported at the crate root and the example truly can't run as-is, use ```` ```rust,no_run ```` — that still compiles the snippet, just doesn't execute it. `ignore` does neither.

**Confidence: 95.** The plan is explicit that this const-context gate must pass; the `ignore` tag means it has never been tested by the build system.

No dead code, no redundant logic, no clippy-visible issues beyond the above.

---

### Test Coverage

The plan's three required properties all land in `src/conn/fixed.rs`. The spot checks from the Verification table are covered:

- 2-parent invocation: `compose!(F12F09, F09F06)` in `compose_two_step_*`
- 4-parent invocation: `COMPOSED_F12F00` via `compose!(F12F09, F09F06, F06F03, F03F00)`
- Galois laws: `compose_inner_then_ceil_is_id`, `compose_inner_then_floor_is_id`, `compose_floor_le_ceil`, `compose_galois_upper`, `compose_galois_lower`, `compose_idempotent`

One gap: no 3-parent invocation is exercised anywhere in the diff. The plan's spot-check list (line 261) explicitly requires "`compose!` accepts 2-, 3-, and 4-parent invocations (variadic)". The macro's recursive expansion for a 3-parent case is structurally distinct from 2 and 4 — if there were an off-by-one in the `$rest` splicing, 2 and 4 could still pass while 3 fails. A single `compose!(F12F09, F09F06, F06F03)` binding, exercised by even one property assertion, closes this. **Confidence: 90.**

The T1 plan specified that properties would live in `src/conn.rs`'s `#[cfg(test)]` block (with strategies imported from `fixed` after promoting them to `pub(crate)`). Instead, all new properties land in `src/conn/fixed.rs`. This is a placement deviation but not a correctness problem — the tests are present, correctly scoped, and exercising the right invariants. The plan's module attribution in the Verification table (`conn`) is stale, but the table was guidance, not contract.

---

### Plan Conformance

- **T1**: Tests exist. Not in `src/conn.rs` as specified, but in `src/conn/fixed.rs`. No impact on correctness.
- **T2**: Macro implemented exactly per the plan's code block. The `#[macro_export]` + `$crate::` path is correct.
- **T3**: `composition_pico_to_uni_matches_ladder_climb` is gone; replaced with macro-driven equivalents plus Galois-law tests. Rationale comment preserved.
- **T4**: `doc/design.md` updated with the "Why not a runtime `Conn::then`" section, the `compose!` example, and the combinator table update. All four sub-bullets from the plan are present.
- **Open question — const context**: Plan says "The build gate: `const F: Conn<Pico, Uni> = compose!(...);` must compile." The review file claims it does. `COMPOSED_F12F00` in `src/conn/fixed.rs` line 557 is that binding — it exists, it uses `const`, and it calls `crate::compose!`. That's the actual compile-time gate and it is present. The gap is only the `ignore` on the doctest, which was supposed to be a second, public-API-facing exercise of the same gate.

---

### Risks

The macro uses `$first.ceil($x)` in the `@nest_ceil` arm where `$first` is a `$:path` fragment. Inside a macro expansion, `some::module::CONST.ceil(x)` is valid Rust — method calls on path expressions are allowed. No issue there.

The `$crate::compose!(@nest_ceil ...)` recursive call passes the already-evaluated `$first.ceil($x)` as an `$x:expr` into the next arm. Because `$x:expr` captures a complete expression, the expansion depth is linear in the number of parents. For the known use cases (2–4 parents) this is fine; at pathological depths (≫8), the compiler's macro recursion limit would trigger, but the plan doesn't call that out as a risk and none of the current callers approach it.

No TODOs or stubs. No unsafe code. No cross-module breakage risk — the macro is purely additive and `Conn`'s struct definition is unchanged.

---

### Recommendations

**Must fix before push:**

1. **Change ```` ```ignore ```` to ```` ```rust ```` on the `compose!` doctest** (`src/conn.rs`, line 26). The plan gates const-context coercion on a compiling example; the `ignore` tag means `cargo test` and `cargo doc --no-deps` both skip it entirely. If `conn::fixed::{Pico, Uni, F12F09, ...}` are not re-exported from the crate root, use ```` ```rust,no_run ```` — that compiles the snippet without executing it — and confirm it passes `cargo test --doc`.

2. **Add a 3-parent test** (`src/conn/fixed.rs`). The plan's spot-check list requires it and the 3-parent expansion path is untested. A single `const`-binding of `compose!(F12F09, F09F06, F06F03)` with one `prop_assert_eq!` on `ceil` covers it.

**Follow-up (future work):**

- The Verification table in the plan names the module as `conn` for all three new properties, but they landed in `conn::fixed`. The plan's Review section (still "(To be appended after implementation.)") is a good place to note this placement deviation so future readers understand the discrepancy.
- `compose_inner_then_floor_is_id` is an additional Galois law check that doesn't appear in the plan's Verification table. It's a welcome addition; documenting it in the Review section as an emergent improvement is the right way to close the loop.

<!-- glab-id: 3287322211 -->
<!-- glab-discussion: 021f1dd1e399bf04bd2da0715171c7725edd8fe8 -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/conn.rs:28` (2026-04-26 09:06 UTC) [open]

**[must-fix]** The doctest is tagged ` ```rust,no_run ` but the local review (review-00009.md, line 93) explicitly required upgrading to at least `rust,no_run` from `ignore`, with the plan's build gate stating the const-context coercion must be verified by `cargo test --doc`. `rust,no_run` compiles the snippet but does not execute it, so the coercion is verified at the type-check level — this is acceptable. However, the review doc's Recommendations section (line 120) says the final must-fix was to change `ignore` to `rust` or `rust,no_run`, and the diff shows the current tag is already `rust,no_run` (line 28 of the new `src/conn.rs`). Cross-checking against the local review text which flags `ignore` as the problem: if the submitted diff already uses `rust,no_run`, this finding does not apply. But the review file's narrative (lines 87–95) still describes the tag as ` ```ignore ` and calls it a must-fix — the review document has not been updated to reflect that the fix was actually applied, leaving the audit trail inconsistent with the code.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3287322214 -->
<!-- glab-discussion: 85a103d51f2d3a4fd05f7553824f178473d630ef -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/conn/fixed.rs:300` (2026-04-26 09:06 UTC) [open]

**[follow-up]** The three strategy functions (`bounded_coarse`, `bounded_fine`, `safe_fine`) are now `#[cfg(test)] pub(crate)` at module scope, outside the `mod tests` block. This means the doc-comment on `safe_fine` (lines 330–344) references `[bounded_fine]` as a doc-link, but neither function is part of the public or `rustdoc`-visible API surface — `cargo doc --no-deps` will emit an unresolved-link warning for that intra-doc reference when run outside a `#[cfg(test)]` context. Consider replacing the bracketed reference with a plain code-font name `` `bounded_fine` `` to avoid the warning.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3287322223 -->
<!-- glab-discussion: 1b3492bdddad12f8df55350229c77db404d66faf -->
### project_81286209_bot_3d7a4a6d9e8f25beaa65342a8ea26b43 on `src/conn.rs:380` (2026-04-26 09:06 UTC) [open]

**[follow-up]** The `compose_floor_le_ceil` property asserts `c.0 - f.0 <= 1` (line 380), which hard-codes a domain-specific invariant about the fixed-point ladder arithmetic (adjacent rounding levels differ by at most 1 unit). This is a property of the `F??F??` connections, not of `compose!` in general — a `compose!` of arbitrary `Conn`s could have `ceil - floor > 1`. The test comment should clarify this is specific to the integer fixed-point ladder, or the assertion should be dropped from this `compose!`-level test suite to avoid implying it as a general macro contract.

---
_Posted by `claude-review` CI — advisory, not merge-blocking._

<!-- glab-id: 3287325658 -->
<!-- glab-discussion: 021f1dd1e399bf04bd2da0715171c7725edd8fe8 -->
#### ↳ cmk (2026-04-26 09:12 UTC) [open]

The local-review section is a snapshot of the pre-fix state. The `ignore` tag was changed to `rust,no_run` in commit dbaf942 ("fix: Address Tier-1 review of MR !9"); the outcome is recorded in `doc/plans/plan-2026-04-26-01.md`'s Review section. The narrative stays as the pre-fix audit trail.

<!-- glab-id: 3287325757 -->
<!-- glab-discussion: 85a103d51f2d3a4fd05f7553824f178473d630ef -->
#### ↳ cmk (2026-04-26 09:12 UTC) [open]

Verified — `cargo doc --no-deps` is clean, both with and without `--document-private-items`. `#[cfg(test)]` items aren't rustdoc'd by either invocation, so the intra-doc-link doesn't surface a warning. Leaving as-is.

<!-- glab-id: 3287325802 -->
<!-- glab-discussion: 1b3492bdddad12f8df55350229c77db404d66faf -->
#### ↳ cmk (2026-04-26 09:12 UTC) [open]

Fixed in commit 4ea2c4a — dropped the `ceil - floor <= 1` strict ULP assertion from `compose_floor_le_ceil` since it's a fixed-point-ladder property, not a general `compose!` invariant. The general `floor <= ceil` stays; the strict ULP-1 is already covered for `F12F00` directly by `props_for_pair!`.
