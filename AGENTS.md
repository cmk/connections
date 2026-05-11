# AGENTS.md

`AGENTS.md` is the shared instruction file for Codex, Claude Code, and
other coding agents. `CLAUDE.md` is a compatibility symlink back to this
file. Claude Code-specific commands and settings remain under `.claude/`.

## What this repo is

A Rust library encoding Galois connections as first-class values, with a
hierarchy of lattice structures built on top. Port of the Haskell
[`connections`](https://github.com/cmk/connections) library. The crate
ships the algebra plus per-host-crate cast families; domain-specific
numeric ladders (audio sample rates, picosecond time, etc.) live in
downstream crates. See `doc/design.md` for the full design rationale.

The workflow tooling under `.github/`, `.githooks/`, `.claude/commands/`,
and `scripts/pr_*` / `scripts/git_*` is synced from
[`template-rust`](https://github.com/cmk/template-rust) via
`scripts/template_sync.sh`.

## Architecture

```
Cargo.toml              — single crate (library)
rust-toolchain.toml     — pinned Rust 1.88 + components
rustfmt.toml            — formatter config (edition 2024)
deny.toml               — cargo-deny policy
src/                    — library source
  conn.rs               — Conn<A, B, K> type + compose/triple/iso macros
  float.rs              — ExtendedFloat<T>, ULP machinery
  core/                 — std-int / fixed-int / float / char / NonZero Conns
  fixed/                — Q-format wrappers (fixed-crate types)
  time/                 — calendar + clock + duration (time + std::time)
  hifi/                 — hifitime (nanosecond + epoch)
  addr/                 — IP + socket
tests/                  — Rust integration tests
doc/                    — design, plans, reviews, notes, audits
```

Bumping MSRV requires updating three places together: `rust-version` in
`Cargo.toml`, the channel in `rust-toolchain.toml`, and the action ref
in `.github/workflows/*.yml`.

`doc/notes/` is gitignored and holds the user's personal notes. Agents
may read from it for context but must not write to it unless asked.

## Library conventions

- **No unsafe code**: every module declares `#![forbid(unsafe_code)]`
  where the macro layer permits it.
- **Test fixtures are gitignored**; a fresh checkout passes `cargo test`
  with zero setup. Fixture-dependent tests use the `fixture_or_skip!`
  macro and `return` cleanly when absent — **do not** `#[ignore]` them
  and do not panic.
- **Property-based testing is mandatory** for any module that parses,
  encodes, or transforms data (`proptest` workspace dev-dep):
  - Strategies are functions returning `impl Strategy`, not `Arbitrary`
    derive. Use `prop_oneof!` with frequency weights to bias toward
    boundary values.
  - Cross-module strategies live in `src/prop/arb.rs`. Module-local
    strategies stay in that module's `#[cfg(test)]` block.
  - Sprint-blocking properties go in the plan's **Verification** table
    before any code is written. Temporary `#[ignore]` requires a
    Review-section reason and a re-enable plan.
- **Modern module layout** (no `mod.rs` — sibling file one level up,
  named after the directory). Document any deviation.

## Conn naming convention

Every public `Conn` constant has an **8-character** identifier split
into two **4-character sides**. The smaller-resolution / coarser tier
goes on the right. Each side independently follows one of four
letter / digit shapes:

| Shape       | L+D | Example side | Use                                               |
|-------------|-----|--------------|---------------------------------------------------|
| `A123` form | 1+3 | `F064`       | most families: `F`, `I`, `U`, `Q`, `N`            |
| `AB12` form | 2+2 | `FD12`       | reserved (lifted-out decimal `FD<dd>`)            |
| `ABC1` form | 3+1 | `FDX1`       | reserved — no current uses                        |
| `ABCD` form | 4+0 | `DURN`       | domain mnemonics: `time` (`DURNSECS`, `DATEJDAY`, `OFDTNANO`, …), `addr` (`IPV4`, `IPV6`, `SOV4`, …), `char` |

The two sides may pick **independently**: a Conn that bridges two
families with different prefix lengths is allowed and expected.

Single-letter prefix meanings (1L+3D shape, where the digits encode
either bit-width or frac-bits depending on the prefix):

| Prefix | Side denotes                                                | Digits         |
|--------|-------------------------------------------------------------|----------------|
| `F`    | IEEE binary float (`f32`/`f64`/`f16`) or `ExtendedFloat<_>` | bit-width      |
| `I`    | signed std primitive (`iN`) or `Extended<iN>`               | bit-width      |
| `U`    | unsigned std primitive (`uN`) or `Extended<uN>`             | bit-width      |
| `Q`    | `FixedI<N>`/`FixedU<N>` Q-format wrapper (sign by module)   | frac bits      |
| `N`    | `NonZero<iN>` / `NonZero<uN>` (sign by module)              | bit-width      |
| `S`    | (legacy / reserved)                                         | —              |

The prefix letter alone disambiguates Fixed-wrapper sides (`Q`) from
std-primitive sides (`I`/`U`); the host bit-width / sign of a `Q*` or
`N*` side comes from the **module path** (`fixed::i8` → signed 8-bit,
`fixed::u8` → unsigned 8-bit, etc.).

Canonical examples:

| Example       | Meaning                                                     |
|---------------|-------------------------------------------------------------|
| `I064I128`    | `Extended<i64>` → `i128` (signed widening)                  |
| `F064F032`    | `ExtendedFloat<f64>` → `ExtendedFloat<f32>` (lossy IEEE narrowing) |
| `Q008Q004`    | `FixedI8<U8>` → `FixedI8<U4>` in `fixed::i8` (Q0.8 → Q4.4)  |
| `U032CHAR`    | `Extended<u32>` → `Extended<char>` (codepoint projection)   |
| `DURNSECS`    | `Duration` → `Extended<i64>` (whole seconds, 4L+0D both sides) |

Hard rules:

- The total identifier is **exactly 8 ASCII chars**. Names shorter than
  8 chars (e.g. the legacy `S88S44`) are not permitted.
- Each side is **exactly 4 chars**, picking one of `{A123, AB12, ABC1,
  ABCD}` independently. Sides shorter or longer than 4 chars are not
  permitted.
- Digits are zero-padded (e.g. `S048`, not `S48`).
- Letters and digits only — no underscores, hyphens, or other separators.
- Cross-module name collisions are **allowed** and resolved by
  qualified-import; e.g. `fixed::i8::Q008Q000` and `fixed::i64::Q008Q000`
  co-exist by `use … as alias;`.

This applies to all `pub const`s of type `Conn<_, _>` exported from
`connections`. Type wrappers that show up as either side of a Conn
follow the same per-side shape so the Conn constant name is the literal
concatenation of its two endpoint type codes.

## Module organization

**The crate's only top-level domain split is `core/` vs `fixed/`**: every
Conn whose endpoints all ship in Rust `core`/`std` lives in `core/`;
every Conn where at least one endpoint is a
[`fixed`](https://docs.rs/fixed)-crate `FixedI<N><F>` / `FixedU<N><F>`
wrapper lives in `fixed/`. The IEEE infrastructure (`ExtendedFloat<T>`,
ULP machinery, rounding helpers, `float_ext_int!` macros) stays in
`src/float.rs` as a type-and-helpers module; only the per-IEEE-width
Conn submodules moved into `core/`.

Per-domain Conn families:

| Submodule | Host crates                                | Files (one per host type)                                  |
|-----------|--------------------------------------------|------------------------------------------------------------|
| `core`    | `core`/`std` (i8…u128, f16/f32/f64, char, bool, NonZero) | `i008.rs`–`i128.rs`, `u008.rs`–`u128.rs` (std-int + NonZero), `f016.rs`/`f032.rs`/`f064.rs` (IEEE), `char.rs`, `bool.rs` |
| `fixed`   | `fixed`                                    | `i008.rs`–`i128.rs`, `u008.rs`–`u128.rs` (Q-format + cross-crate iso `I###Q000` + float-bridge `F0XXQ###`) |
| `time`    | `time`, `std::time`                        | `clock.rs`, `date.rs`, `datetime.rs`, `duration.rs`, `offset.rs` |
| `float`   | (this crate)                               | `ExtendedFloat<T>` + ULP/rounding helpers + `float_ext_int!` macros |
| `addr`    | `std::net`                                 | `ip.rs`, `socket.rs` |
| `conn`    | (this crate)                               | `Conn<A, B, K>`, `compose!` / `triple!` / `iso!` macros, free fns operating on a `Conn` |

**Modules are keyed by host crate by default**, except where one
algebraic domain is shared across crates — `time/` hosts both `time`
crate types and `std::time::Duration` (`STDRU064` etc.) under
`time/duration.rs`. Domain-specific numeric ladders (decimal-SI for
picosecond time, audio sample rates) live in downstream crates such as
[`agogo`](https://gitlab.com/cmk/agogo); this crate ships the algebra
plus per-host-crate cast families.

Numeric filenames use side-code spelling in lowercase (`i008.rs`,
`f064.rs`, …). Semantic modules keep domain names (`date.rs`,
`duration.rs`).

## Conn placement

When deciding where a new `Conn<A, B>` const lives, apply the following
precedence in order:

1. **Specificity: more-specific type wins over more-general type.** The
   Conn lives in the module of the more-specific endpoint. Specificity
   is roughly:
       domain types (Duration, Date, OffsetDateTime, FixedI8)
       > generic numeric wrappers (Extended<T>, ExtendedFloat<T>, FD<N>)
       > std primitives (i8, …, i128, u8, …, u128, f16, f32, f64).
   When ambiguous, the more-semantically-loaded type wins.
2. **Same-tier tie-breaker: left/source side wins.** If both endpoints
   sit at the same specificity tier, the Conn lives in the module of
   the source type named by the const prefix.

**(1) subsumes "external-crate type beats `std`":** std primitives are
at the bottom of the specificity order, so any Conn touching a `fixed`-
or `time`-crate type is hosted in that crate's submodule by rule (1)
alone.

Worked examples:

| Conn          | Sides                              | Rule                       | Module          |
|---------------|------------------------------------|----------------------------|-----------------|
| `F064F032`    | `f64` / `f32`                      | tie → source wins          | `core::f064`    |
| `I008U016`    | `i8` / `u16`                       | tie → source wins          | `core::i008`    |
| `Q008Q004`    | `FixedI8<U8>` / `FixedI8<U4>`      | host Q-format file wins    | `fixed::i008`   |
| `I008Q000`    | `i8` / `FixedI8<U0>`               | (1) FixedI8 more specific  | `fixed::i008`   |
| `U032CHAR`    | `Extended<u32>` / `Extended<char>` | (1) char more specific     | `core::char`    |
| `DATEJDAY`    | `Extended<Date>` / `i32`           | (1) `Date` more specific   | `time::date`    |
| `OFDTNANO`    | `Extended<OffsetDateTime>` / `i128`| (1) `OffsetDateTime` wins  | `time::offset`  |

Cross-module name collisions are allowed — e.g. `fixed::i8::Q008Q000`
and `fixed::i64::Q008Q000` both exist; users resolve by qualified
import.

## Repository conventions

### Parallel work

At the start of each conversation, ask: "Are any other agent instances
working in this repo right now?" If yes, a worktree is **mandatory** —
two agents in the same worktree stall on cargo's `target/` lock. Naming:
`../<repo>.plan-YYYY-MM-DD-NN` + branch `plan/YYYY-MM-DD-NN` (TDD step
1). The primary checkout stays clean on `main` for humans and other
agents.

Verify worktrees aren't sharing `target/` (would happen if
`CARGO_TARGET_DIR` is set or `~/.cargo/config.toml` overrides
`build.target-dir`):
`cargo metadata --format-version 1 --no-deps | jq -r .target_directory`
in each — different paths = safe.

### The gardener rule

Weeds are weeds, regardless of who planted them. Whenever you spot a
violation of any rule above — stale comment, mis-bounded proptest
generator, lying `expect()` string, undocumented `#[ignore]`, missing
verification-table property — flag it even if you didn't write it.

- **Flag** in the plan's `## Review` section: `file:line — rule —
  consequence`.
- **Fix** if local, single-file, no API change, no scope expansion — ask
  the user before merging.
- **Defer** otherwise — name the cleanup specifically enough for the
  next plan branch to pick up.

Review labels ("optional", "nit", "follow-up", suppressed,
low-confidence) are not discounts. Treat with the same seriousness;
defer only when large, complex, outside the sprint, or incorrect.

CI gates (fmt, clippy, gitleaks, the `check_*.sh` scripts) catch their
own drift. The gardener rule covers what lives *below* the gate: prose,
doc links, decorative tests, mis-bounded generators, stale section
headers, panic strings that contradict preconditions, deferred
Verification-table properties.

### Session notes

Session notes live in `doc/notes/note-YYYY-MM-DD-nn.md`. The final field
`nn` is a counter that resets to 01 each day.

When the user says "print to notes", append the requested responses to
the current day's notes file in markdown format. Create the file if it
doesn't exist.

### Git hooks

Hooks are activated by `git config core.hooksPath .githooks`. Bypass
(`--no-verify`) only when explicitly authorized; CI re-runs the same
gates plus a `gitleaks` history scan as defense-in-depth.

- **Each pushed commit must be green.** `pre-push` runs `cargo test` +
  `cargo clippy --all-targets -- -D warnings` + `cargo doc` with
  `RUSTDOCFLAGS=-D warnings`. Intra-branch commits can be transiently
  red — pre-push is the gate, CI is the source of truth for
  `origin/main`'s bisect property. `pre-commit` runs the cheap chain on
  every commit: `cargo fmt --check`, `scripts/check_pii.sh`,
  `scripts/check_readme_mirror.sh`. There's also an agent `PreToolUse`
  layer in `.claude/settings.json` that catches PII drift on agent-
  invoked `git commit*` — but use separate `git add` and `git commit`
  calls, since chained `add && commit` sees an empty pre-add diff and
  slips through.
- **No merge commits.** Always rebase onto main; history is linear.
- **Mechanical repair commits are fixups.** CI repairs, local-review
  cleanups, and GitHub review rounds that do not change design use
  `git commit --fixup=<sha>` against the implementation commit they
  repair. Review-doc mirror changes use a separate fixup targeting the
  finalized-doc commit. Design-changing feedback may stay as a
  standalone `fix:` or `feat:` commit. Run
  `scripts/git_autosquash_finalize.sh` before merge.

### Sprint workflow

The sprint workflow is a finite state machine, not a menu. The full
review-round lifecycle and `/pr-watch` loop are diagrammed in
`doc/workflow.md` (the prose here is authoritative if the two
disagree). Identify the current state before committing, running local
review, pushing, replying, or merging — take only the documented
transition. Use `scripts/workflow_state.sh` when the state isn't
obvious.

```
main_clean → on_branch → plan_committed → impl_green → plan_finalized
  → local_reviewed → pushed → gh_review → items_pulled → round_unpushed
  → gh_review → autosquash_finalized → merged
```

Workflow-sensitive actions go through repo scripts/commands:

- Local review: `/pr-review` (Claude Code) or `scripts/pr_review.sh`.
- PR body: `scripts/pr_report.py path` / `body`.
- GitHub review ingestion: `scripts/pr_report.py reviews`.
- Replies: `/pr-reply` (wraps `scripts/pr_reply.py` + `pr_report.py
  reviews`).
- Finalization: `scripts/git_autosquash_finalize.sh`.
- Merge: `scripts/git_merge.sh`, **not** `gh pr merge`.

When a `gh`-backed command errors (auth prompt, network, missing
permission), surface the error — **don't silently fall back** to git
plumbing or MCP tools. They almost always do the wrong thing for
GitHub-side state.

### Test-driven development (TDD) workflow

A plan at `doc/plans/plan-YYYY-MM-DD-NN.md` maps to branch
`plan/YYYY-MM-DD-NN` and (optionally) worktree
`../<repo>.plan-YYYY-MM-DD-NN`. One slug, three places.

1. **Pick the filename.** `ls doc/plans/plan-YYYY-MM-DD-*.md` to find
   the next unused `NN`. No writes yet — main stays clean.
2. **Worktree or branch?** Worktree if another agent is active, else
   user's call. `git worktree add ../<repo>.plan-YYYY-MM-DD-NN -b
   plan/YYYY-MM-DD-NN` or `git switch -c plan/YYYY-MM-DD-NN`.
3. **Write the plan.** The Verification table lists property tests that
   must pass to ship. Commit as `plan: <one-line goal>`.
4. Write proptest properties + test skeletons that compile but fail.
5. Implement until green.
6. Commit on the branch when green.
7. **Finalize sprint docs** in one commit: append Deferred/Review
   sections to the plan; create the review file at
   `$(scripts/pr_report.py path)` with `# PR #<N> — <title>` +
   `## Summary` (the PR body, written for a human reviewer — not a
   ship-report). `review-00000.md` is a protected sentinel; real reviews
   start at `00001`. Commit as `doc: Finalize plan NN and PR
   description`. **Must precede local review** — the local-review
   command aborts if `## Summary` is missing.
8. Run `/pr-review` (or `scripts/pr_review.sh`).
9. Open the PR:
   `gh pr create --body-file <(scripts/pr_report.py body N)`.
10. Before merge, run `scripts/git_autosquash_finalize.sh`. It
    autosquashes fixup commits, reruns full gates, and force-pushes the
    cleaned branch with lease.
11. Rebase + land: `git fetch origin && git rebase origin/main`, then
    `git merge --ff-only`. (Worktree case: main is checked out in the
    *primary* worktree, so run the merge from there.)
12. `git worktree remove ...` (if used), then `git branch -d ...`.

### Code review

#### Tier 1 — Local (pre-push)

Before pushing, run `/pr-review` (or `scripts/pr_review.sh`). It
examines `git diff origin/main...HEAD`, appends a
`## Local review (YYYY-MM-DD)` section, commits that artifact as a
fixup to the finalized-doc commit, and aborts if the review file or
`## Summary` is missing.

If another PR opens between TDD step 7 and your push, the predicted
review number can drift — re-run `scripts/pr_report.py path` and `mv`
the file if needed.

#### Tier 2 — GitHub (post-push)

CI runs tests + clippy. Auto-review agents and Copilot review the PR.

After GitHub review activity:
1. `/pr-report <N>` fetches comments and **appends** them to
   `review-NNNNN.md` (idempotent via `<!-- gh-id: NNNNN -->` markers).
2. Address findings as **uncommitted edits** in the working tree.
3. `/pr-reply <N>` posts replies, mirrors them into the doc, and creates
   one or two commits for the round: code/test/product-doc mechanical
   fixes as `fixup! <implementation>`, review-doc mirror changes as
   `fixup! <finalized-doc>`. Design-changing feedback may be a
   standalone `fix:` or `feat:` commit, still paired with a review-doc
   fixup when the mirror changed.
4. `git push` once.

**Do not pre-commit the fix** — `/pr-reply` starts from `gh_review` and
produces the round commits itself. **Do not merge from `round_unpushed`
or before `autosquash_finalized`** — use `scripts/git_merge.sh`, which
refuses if the branch is ahead of origin or still contains
autosquashable commits. Recovery, if a merge dropped a round commit:
cherry-pick the stranded SHA into the next plan branch's first commit.

#### Documented blind spot: type-claim soundness

Automated reviewers are advisory, not a soundness gate. An earlier
round shipped three float Conns whose `iso!` claimed a Galois law the
impl violated on NaN, and both Claude reviewers ratified the author's
"weaker test predicate" framing instead of auditing the type claim.
See `doc/reviews/review-calibration.md` for the few-shot pattern.
Type-system soundness on the diff you wrote remains your
responsibility, not the bot's.

#### Automated poll loop (optional)

`/loop 10m /pr-watch <N>` runs the round cycle on a timer; never
merges. See `doc/workflow.md` → *`/pr-watch` dynamic-mode loop*.

### Commit style

Conventional commits, present-tense imperative subject. Accepted
prefixes: `plan`, `feat`, `fix`, `fmt`, `doc`, `test`, `task`, `debt`.
Scopes allowed (`doc(skills):`, etc.). Sprint-opener is a `plan:`
commit adding the plan doc; subsequent commits cover the implementation.

```
plan: Widget-format parser, sprint goals and verification table
feat: Add parser for widget format
fix(codec): Handle timeout on reconnect
test: Add round-trip property tests for codec
debt: Remove dead handshake branch
```

Keep subjects under 72 characters. Use the body for non-obvious
decisions.

Historical note: `doc/reviews/gitlab/review-00002.md..review-00098.md`
carry GitLab-era `<!-- glab-id: -->` / `<!-- glab-discussion: -->`
markers and MR-iid references; those resolve against the old GitLab
project and are audit-trail only. The `gitlab/` subdirectory exists
so GitHub-issued PR numbers can reclaim `doc/reviews/review-NNNNN.md`
without colliding with the frozen GitLab archive. New review files
use `<!-- gh-id: -->` via `scripts/pr_report.py`.

## Sprint plan format

```markdown
# Plan NN — Title

## Goal
One sentence.

## Dependency Graph
T1 → T2, T3 → T4, ...

## Tasks
T1, T2, ... — each with: problem/motivation, solution/approach,
types or API surface.

## Verification

### Properties (must pass)
| Property | Module | Invariant |
|----------|--------|-----------|
| `msg_round_trips` | `crate_foo::codec` | encode then decode recovers original |

### Spot checks
Unit test names + specific assertions.

### Build gates
- cargo build, test, clippy --all-targets — all clean
- End-to-end scenario description

## Deferred
What was intentionally left out, why.

## Review
- Any `#[ignore]`d properties — which, why, re-enablement plan
- Design deviations from the plan
- **Drift caught** (file:line — rule — fixed-here / deferred). See
  the gardener rule.
- Recommendations
```
