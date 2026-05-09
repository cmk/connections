# CLAUDE.md

## What this repo is

A Rust library encoding Galois connections as first-class values, with
a hierarchy of lattice structures built on top. Port of the Haskell
[connections](https://github.com/cmk/connections) library.

## Parallel work

At the start of each conversation, ask the user:
"Are any other Claude instances working in this repo right now?"

Before making any file edits, run `git worktree list` and
`git branch --show-current`. If the current directory is the primary
checkout shown by `git worktree list`, treat it as shared
coordination space and create a task worktree before editing, even if
the primary checkout is currently on a feature branch. The primary
checkout should stay clean on `main` for humans and other agents.

If another Claude instance is working in the repo, if the user says
"work in a worktree", or if you are in the primary checkout, create a
git worktree before making any changes:

```zsh
git worktree add ../project-<task> -b <branch>
```

Never run two Claude instances in the same worktree, and never use the
primary checkout for task edits. Cargo target-dir locks, fd contention,
and uncommitted shared-root changes will break one or more sessions.

## Architecture

See `doc/design.md` for the full design rationale.

### Layout

```
Cargo.toml              — single crate
src/                    — library source
doc/                    — design docs, notes, plans
```

## Repository conventions

- **Each commit must leave the repo in a state where `cargo test` passes.**
  Do not commit a library module without the tests that cover it in the
  same commit. Never commit a red test suite.
- **No merge commits.** Always rebase onto main — never `git merge`. The
  history must be linear.
- **No unsafe code**: `#![forbid(unsafe_code)]` when possible.
- **Test fixtures are gitignored**, and a fresh checkout must pass
  `cargo test --workspace` with zero setup. Tests that depend on a
  fixture file must use the `fixture_or_skip!` macro from the core
  crate and `return` cleanly when the fixture is absent — **do not**
  `#[ignore]` them and do not panic.
- **Property-based testing is mandatory** for any module that parses,
  encodes, or transforms data. Use `proptest` (workspace dev-dep).
  - Define strategies as functions returning `impl Strategy`, not
    `Arbitrary` derive. Use `prop_oneof!` with frequency weights to
    bias toward boundary values and edge cases.
  - Strategies shared across crates live in `crates/core/src/arb.rs`.
    Strategies local to one module stay colocated in that module's
    `#[cfg(test)]` block.
  - Properties that must hold for a sprint to ship are defined **in
    the plan's Verification table** before any code is written.
  - If a property test blocks progress during implementation, you may
    `#[ignore]` it temporarily **but you must document it** in the
    plan's Review section with the reason and a plan to re-enable.

### Conn-name format (mandatory)

Every public `Conn` constant has an **8-character** identifier split
into two **4-character sides**. The smaller-resolution / coarser tier
goes on the right. Each side independently follows one of four
letter / digit shapes:

| Shape          | Letters | Digits | Example side | Use                                               |
|----------------|---------|--------|--------------|---------------------------------------------------|
| `A123` form    | 1       | 3      | `F064`       | most families: `F`, `I`, `U`, `Q`, `N`, `S`       |
| `AB12` form    | 2       | 2      | `FD12`       | reserved — last used by the (lifted-out) decimal `FD<dd>` family; available for future 2-letter-prefix families |
| `ABC1` form    | 3       | 1      | `FDX1`       | reserved — no current uses                        |
| `ABCD` form    | 4       | 0      | `DURN`       | domain-mnemonic families: `time` (`DURNSECS`, `DATEJDAY`, `TIMENANO`, `OFDTNANO`, `OFDTSECS`, `PDTMDATE`, …); `addr` (`IPV4`, `IPV6`, `IPVX`, `SOV4`, `SOV6`, `SOVX`); `char` (`CHAR`) |

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

The prefix letter alone disambiguates Fixed-wrapper sides (`Q`)
from std-primitive sides (`I`/`U`); the host bit-width / sign of a
`Q*` or `N*` side comes from the **module path** (`fixed::i8` →
signed 8-bit, `fixed::u8` → unsigned 8-bit, etc.).

Canonical examples:

| Pattern              | Example       | Meaning                                                     |
|----------------------|---------------|-------------------------------------------------------------|
| `A123X456` (1L+3D both) | `I064I128` | `Extended<i64>` → `i128` (signed widening)                  |
| `A123X456`           | `F064F032`    | `ExtendedFloat<f64>` → `ExtendedFloat<f32>` (lossy IEEE narrowing) |
| `A123X456`           | `Q008Q004`    | `FixedI8<U8>` → `FixedI8<U4>` in `fixed::i8` (Q0.8 → Q4.4)  |
| `A123X456`           | `Q000I008`    | `FixedI8<U0>` → `i8` in `fixed::i8` (cross-crate iso)       |
| `A123X456`           | `I008N008`    | `i8` → `NonZeroI8` in `fixed::i8`                           |
| `A123X456` (1L+3D both) | `U032CHAR` | `Extended<u32>` → `Extended<char>` (codepoint projection)   |
| `ABCDXYZW` (4L+0D both) | `DURNSECS` | `Duration` → `Extended<i64>` (whole seconds)                |

Hard rules:

- The total identifier is **exactly 8 ASCII chars**. Names shorter
  than 8 chars (e.g. the legacy `S88S44`) are not permitted.
- Each side is **exactly 4 chars**, picking one of `{A123, AB12,
  ABC1, ABCD}` independently. Sides shorter or longer than 4 chars
  are not permitted.
- Digits are zero-padded to fill the digit count for the side's
  shape (e.g. `S048`, not `S48`).
- Letters and digits only — no underscores, hyphens, or other
  separators inside the name.
- Cross-module name collisions are **allowed** and resolved by
  qualified-import; e.g. `fixed::i8::Q008Q000` and
  `fixed::i64::Q008Q000` co-exist by `use … as alias;`.

This applies to all `pub const`s of type `Conn<_, _>` exported from
`connections`. Type wrappers that show up as either side of a Conn
follow the same per-side shape so the Conn constant name is the
literal concatenation of its two endpoint type codes.

### Module organization

**The crate's only top-level domain split is `float/` vs `fixed/`**:
every IEEE-binary type lives in `float/`, and every
finite-precision-with-integer-storage type — `fixed`-crate Q-format
wrappers, std-int primitives (interpreted as Q*N*.0), and
`core::num::NonZero<T>` (punctured Q*N*.0) — lives in `fixed/`.

Per-domain Conn families:

| Submodule | Host crates                                | Files (one per host type)                                  |
|-----------|--------------------------------------------|------------------------------------------------------------|
| `fixed`   | `fixed`, `std` (i8…u128), `core::num` (NonZero) | `i8.rs`–`i128.rs`, `u8.rs`–`u128.rs` (per-destination type) |
| `time`    | `time`, `std::time`                        | `clock.rs`, `date.rs`, `datetime.rs`, `duration.rs`, `offset.rs` |
| `float`   | (this crate)                               | `ExtendedFloat<T>` + IEEE narrowing Conns; submodules `f32.rs` (target `F032`) and `f16.rs` (target `F016`, gated on `f16` cargo feature → nightly required) |
| `addr`    | `std::net`                                 | `ip.rs`, `socket.rs` |
| `char`    | `core` (primitive)                         | `char.rs` (`U032CHAR` codepoint projection)                |
| `conn`    | (this crate)                               | The `Conn<A, B, K>` type, the `compose!` / `triple!` / `iso!` macros, free fns operating on a `Conn` (`round`, `truncate`, `interval`, `midpoint`, `median`, lifters), and `Conn::new_l` / `new_r` constructors |

**Modules are keyed by host crate by default**, except where a single
domain is meaningfully shared across crates. `time/` is the worked
example: it hosts both the [`time`](https://docs.rs/time) crate's
calendar / clock / signed-`Duration` Conns and the
[`std::time`](https://doc.rust-lang.org/std/time/) `Duration` family
(`STDRU064`, `STDRU128`, `F064STDR`, `F032STDR`) under `time/duration.rs`.
The principle: when two crates ship structurally-similar types in the
same algebraic domain, fold them into one module rather than mirroring
the per-crate split. Plan 25 (the `int` ⊕ `fixed` merge) applies the
same principle to the integer / Q-format / NonZero stack.

Per-host-type files in `fixed/X.rs` are sectioned (§1 std-int /
§2 Q-format / §3 NonZero / §4 cross-crate iso). Std-int Conns
(generated by `ext_int!` / `int_int_narrow!` / etc.) keep `I`/`U`
prefixes on both sides; Q-format Conns (from `fix_fix_iN!` /
`fix_fix_uN!`) use `Q` on both sides; cross-crate iso Conns
straddle (`Q000I008`, `Q000U008`, etc.). The legacy `int/` submodule
exists only as thin re-export shims pointing at `fixed::*` and is
removed in Plan 25 T10.

Domain-specific numeric ladders live in downstream crates rather
than here. The custom decimal-SI ladder (`FD<N>` rungs, intra-
decimal `FD<M>FD<N>` Conns, float-decimal `F064FD<N>` bridges)
shipped briefly under `int::i64::decimal` and was lifted
out before 0.1.0; it now belongs in whatever downstream crate
needs picosecond-resolution time. Audio sample-rate ladders
similarly live in the [`agogo`](https://gitlab.com/cmk/agogo)
crate. The rule of thumb: this crate ships the algebra plus
per-host-crate cast families; downstream crates ship the named
constants for their own domain ladders.

**Filenames follow the host type name verbatim** — `i8.rs`,
`u128.rs`, `f64.rs`, `f16.rs`, `date.rs`, `duration.rs`. The 8-char
zero-padded form (`Q008Q004`, `I064I128`) is reserved for Conn const
**identifiers** (per §Conn-name format) and is **never** used as a
module path.

#### Conn placement: which module hosts each `pub const`?

When deciding where a new `Conn<A, B>` const lives, apply the
following precedence in order:

1. **Specificity: more-specific type wins over more-general type.**
   The Conn lives in the module of the more-specific endpoint.
   Specificity is roughly:
       domain types (Duration, Date, OffsetDateTime, FixedI8)
       > generic numeric wrappers (Extended<T>, ExtendedFloat<T>, FD<N>)
       > std primitives (i8, …, i128, u8, …, u128, f16, f32, f64).
   When ambiguous, the more-semantically-loaded type wins.
2. **Same-tier tie-breaker: right-side wins over left-side.** If
   both endpoints sit at the same specificity tier, the Conn lives
   in the module of the **right-hand-side** type — which is the
   coarser / smaller-resolution side per the §Conn-name format
   rule.

**(1) subsumes "external-crate type beats `std`":** std primitives
are at the bottom of the specificity order, so any Conn touching a
`fixed`- or `time`-crate type is hosted in that crate's submodule
by rule (1) alone.

Worked examples:

| Conn          | Sides                              | Rule                          | Module                          |
|---------------|------------------------------------|-------------------------------|---------------------------------|
| `F064F032`    | `f64` / `f32`                      | tie → right wins              | `float::f32`                    |
| `F064F016`    | `f64` / `f16`                      | tie → right wins              | `float::f16` (`f16` feature)    |
| `F032F016`    | `f32` / `f16`                      | tie → right wins              | `float::f16` (`f16` feature)    |
| `I008I016`    | `Extended<i8>` / `i16`             | tie → right wins              | `fixed::i16`                    |
| `U008I016`    | `Extended<u8>` / `i16`             | tie → right wins              | `fixed::i16`                    |
| `I008U016`    | `i8` / `u16`                       | tie → right wins              | `fixed::u16`                    |
| `Q008Q004`    | `FixedI8<U8>` / `FixedI8<U4>`      | tie → right wins              | `fixed::i8`                     |
| `Q000I008`    | `FixedI8<U0>` / `i8`               | (1) FixedI8 more specific     | `fixed::i8`                     |
| `I008N008`    | `i8` / `NonZeroI8`                 | (1) NonZero more specific     | `fixed::i8`                     |
| `DATEJDAY`    | `Extended<Date>` / `i32`           | (1) `Date` more specific      | `time::date`                    |
| `OFDTNANO`    | `Extended<OffsetDateTime>` / `i128`| (1) `OffsetDateTime` wins     | `time::offset`                  |
| `PDTMDATE`    | `PrimitiveDateTime` / `Extended<Date>` | (1) `PDT` more semantic   | `time::datetime`                |

Cross-module name collisions are allowed (per §Conn-name format) —
e.g. `fixed::i8::Q008Q000` and `fixed::i64::Q008Q000` both exist;
users resolve by qualified import.

### Session notes

Session notes live in `doc/notes/note-YYYY-MM-DD-nn.md`. The final field
`nn` is a counter that resets to 01 each day.

When the user says "print to notes", append the requested responses to
the current day's notes file in markdown format. Create the file if it
doesn't exist.

### Commit style

Conventional commits, present-tense imperative subject:

```
feat: Add parser for widget format
fix: Handle timeout on reconnect
test: Add round-trip property tests for codec
doc: Append Sprint 2 completion report
task: Add serde to core dependencies
```

Keep subjects under 72 characters. Use the body for non-obvious decisions.

## TDD workflow

Every sprint follows this order. This is a **two-tier review loop**:
Tier 1 is local (`/sprint-review` pre-push), Tier 2 is GitLab MR
round-trip (`/pull-reviews` → fix → `/reply-reviews` → push).

1. Write the plan to `doc/plans/plan-YYYY-MM-DD-nn.md` before touching source.
   The plan's **Verification** table must list the property tests that
   must pass for the sprint to ship (e.g., "message round-trips through
   encode/decode", "parser never panics on arbitrary input").
2. Create a worktree and branch for the sprint:
   `git worktree add ../project-<sprint> -b sprint/<name>`
3. Write proptest properties and test skeletons that compile but
   trivially fail. Properties come first — they define the contract.
4. Implement the module until all tests are green.
5. Commit on the branch, when green. Conventional subjects
   (`feat:`/`fix:`/`test:`/`doc:`/`task:`/`debt:`), ≤72 chars.
6. Append **Deferred** and **Review** sections to the plan document.
7. **Finalize the plan and draft the MR description.** Predict the MR
   iid via `scripts/next_mr_number.sh`, create
   `doc/reviews/review-NNNNN.md` with a `## Summary` section holding the
   1–3 bullet MR description, and `## Test plan`. Commit it as a
   `doc:` or fold into the last `plan:` commit. The review file is the
   single source of truth for the MR description — `glab mr create`
   pulls from it verbatim via `scripts/extract_mr_body.sh`.
8. Run `/sprint-review` — Tier 1 local review against `origin/main...HEAD`.
   Appends a `## Local review (YYYY-MM-DD)` section to
   `doc/reviews/review-NNNNN.md`. If the review lists must-fix items,
   loop back to step 4.
9. Push and open the MR:
   ```
   git push -o ci.skip -u origin sprint/<name>
   glab mr create --title "<title>" \
     --description "$(scripts/extract_mr_body.sh NNNNN)"
   ```
   Use `ci.skip` only for this first publication push: before the MR
   exists, GitLab cannot suppress the duplicate branch pipeline. The
   merge-request pipeline starts when `glab mr create` opens the MR;
   later review-round pushes do not use `ci.skip`.
10. **Per review round**: `/pull-reviews <N>` fetches new discussions,
    fix them as a single **unpushed** fix commit, then `/reply-reviews <N>`
    posts replies, mirrors them back into the review doc, and amends
    the mirror into the fix commit. Push once — code + replies + audit
    trail in one trip. For unattended polling, `/watch-mr <N>` (with
    or without `/loop`) automates this per round. MR review comments
    must flow through `/pull-reviews` and `/reply-reviews`; raw
    `glab mr note`, `glab api`, or inline shell-quoted Markdown is
    fallback-only and must be justified in the review-round notes.
11. Rebase onto main: `git rebase main` then fast-forward main.
12. Clean up: `git worktree remove ../project-<sprint>`.
13. If any property tests were `#[ignore]`d during implementation,
    document the reason and the re-enablement plan in the plan's
    Review section before merge.

### CI-repair / fix commits

Review-round fixes are full commits (`fix: Address review feedback on
MR !<N>`); `/reply-reviews` amends the review-doc mirror into that same
commit via `git commit --amend --no-edit`, so each round is exactly one
push.

**CI-repair fixups** are a separate case: when CI on a pushed branch
fails (a test flake, a clippy lint only the linux image catches), make
a `git commit --fixup <sha>` commit against whichever earlier commit
owns the regression. Before the next push/merge, collapse fixups via
`scripts/autosquash.sh` so `main`'s linear history doesn't gain commits
that temporarily broke the build. `/sprint-review` runs this check
automatically at Step 0.

### Pre-commit / pre-push hooks

Two complementary layers guard every commit, plus a once-per-push
layer for heavier checks:

**Layer 1 — Claude Code `PreToolUse`** (`.claude/settings.json`):
fires on agent-invoked Bash calls matching `git commit*`. Catches
issues during agent iteration without invoking git for real.
Limitation: hooks run in **Claude Code's session cwd**, not the cwd a
`cd` inside a matched compound command would reach. So an agent's
`cd <worktree> && git commit -m "..."` call has this layer's
`cargo fmt` / `cargo clippy` checking the launch directory, not the
worktree. Direct `git commit` runs from the project root are caught
fine.

**Layer 2 — Git `pre-commit`** (`.githooks/pre-commit`): fires at
git's standard `pre-commit` hook point — AFTER staging, BEFORE the
commit object is created, in the actual repo working directory. So
it sees the actual staged content regardless of how the commit was
invoked: chained `git add && git commit`, agent-invoked Bash calls in
any worktree, terminal commits, IDE commits, all paths. This is the
unbypassable safety net.

**Layer 3 — Git `pre-push`** (`.githooks/pre-push`): fires once per
`git push`, before any refs are sent to the remote. Runs checks too
expensive to gate every commit but cheap once a sprint:

1. `RUSTDOCFLAGS="-D warnings" cargo doc --no-deps --features
   testing,macros,time --document-private-items` — fails on broken
   intra-doc links and rustdoc warnings. Mirrors the CI `doc:` job and
   docs.rs feature surface. CI catches these on MR pipelines and
   post-merge `main`, but mid-sprint feature-branch pushes don't
   trigger an MR pipeline, so accumulated link rot can land unnoticed
   until an MR is opened. Running locally before push closes that gap.

Activate Layers 2 and 3 on a fresh clone:

```
git config core.hooksPath .githooks
```

Layers 1 and 2 run the same check chain, in order. Every step is
blocking — the chain short-circuits on the first failure and the
commit is aborted:

1. `cargo fmt --all -- --check` — fmt drift aborts the commit. Was
   non-blocking through Plan 25; flipped to blocking in Plan 26 after
   MR !39 hit a real CI fmt failure (import ordering + the rustfmt
   indent-instability bug on the new `nz_*_ext!` macros) that local
   tooling let through.
2. `scripts/check-pii.sh` — fails if staged diff contains absolute
   user-home paths or common API-token shapes.
3. `scripts/check_readme_mirror.sh` — fails if README sections that
   are mirrored from rustdoc have drifted out of sync.
4. `cargo test --workspace --quiet`.
5. `cargo clippy --all-targets --quiet -- -D warnings`.

`/sprint-review` is the manual quality gate; all three hook layers
are the automated ones. Never bypass with `--no-verify` unless Chris
explicitly authorizes it.

### Commands (`.claude/commands/`)

- **`/sprint-review`** — Tier 1 local pre-push review. Appends to
  `doc/reviews/review-NNNNN.md`. Gates the push.
- **`/pull-reviews <N>`** — fetch GitLab MR discussions into the review
  doc. Idempotent via `<!-- glab-id: -->` markers.
- **`/reply-reviews <N>`** — post replies, mirror back, amend into the
  round's unpushed fix commit. Refuses to run if the fix commit is
  already pushed. Use the repo script path for replies; pass Markdown,
  backticks, multiline text, and code references via stdin or
  `--body-file`, then rerun `/pull-reviews` and verify the mirrored
  body before amending.
- **`/watch-mr <N>`** — one polling tick: triage new items, auto-fix
  the trivially-clear ones, run `/reply-reviews`, stop before push.
  Designed for `/loop /watch-mr <N>` dynamic backoff.

### `doc/reviews/` audit trail

One file per MR: `doc/reviews/review-NNNNN.md` (zero-padded iid). Its
`## Summary` is the MR description (pulled by `extract_mr_body.sh`);
subsequent sections accumulate local reviews and GitLab discussion
mirrors. `review-00000.md` is a deliberate sentinel — do not delete.

### Automated MR reviewer (`claude-review` CI job)

`.gitlab-ci.yml` runs a `claude-review` job on every MR that posts
Claude's review findings as MR discussion notes, anchored inline
(file:line) where the diff permits, falling back to general comments
otherwise. The job is **advisory-only** (`allow_failure: true`) — the
AI never blocks merges; its findings flow through the normal
`/pull-reviews` → fix → `/reply-reviews` loop.

The job is gated behind two CI variables and silently no-ops if
either is missing:

- `ANTHROPIC_API_KEY` — Claude API key (Project → Settings → CI/CD →
  Variables; masked, protected).
- `GITLAB_TOKEN` — Project Access Token or PAT with `api` scope
  (same place; masked). Required for posting discussions.

Optional `CLAUDE_MODEL` overrides the default `claude-sonnet-4-6`
(set to `claude-opus-4-7` for deeper review at ~2× cost and latency).

Implementation: `scripts/claude_review.py` — prompt-cached system
prompt + CLAUDE.md + calibration examples, then the diff. Parses
Claude's JSON finding array and POSTs each to
`/projects/:id/merge_requests/:iid/discussions` with the required
`position[*]` fields for inline anchoring. The Anthropic client is
configured with `max_retries=5` for transient 5xx/529 windows, and
the job has `retry: 2` so GitLab reruns the whole thing if the SDK
still surfaces an error (two layers of backoff, one in-process, one
scheduled by the runner).

#### Re-triggering a review manually

Useful when the prior review was truncated, hit 529 Overloaded too
many times, or you just want a fresh read. Two ways:

**CLI:**

```
glab ci run --variables "CLAUDE_REVIEW_MR=<iid>" \
  --branch "$(glab mr view <iid> -F json | jq -r .source_branch)"
```

**Web UI:** Project → Build → Pipelines → **Run pipeline** → Ref =
the MR's source branch → add variable `CLAUDE_REVIEW_MR` = iid →
Run.

When triggered this way, the script reads `CLAUDE_REVIEW_MR` instead
of the MR-event env vars, fetches the MR's base/head SHAs from
`/projects/:id/merge_requests/:iid` via the GitLab API, ensures both
are present locally (`git fetch origin <sha>`), then runs the same
review and posts findings to the same MR.

#### Documented blind spot: type-claim soundness

The automated reviewers (local `/sprint-review` agent, GitLab
`claude-review` bot) are advisory — treat them as a coverage net,
not a soundness gate. MR !70 shipped three float Conns whose `iso!`
declaration claimed a Galois law the impl violated on NaN, and both
Claude reviewers ratified the author's "weaker test predicate"
framing instead of auditing the type claim. Codex one-shot it in
round 2. The mitigations are: (a) the reviewer prompts now require
a trait-claim audit before any other review work; (b)
`/sprint-review` runs in two passes so the plan doesn't pre-frame
the diff; (c) Pattern 9 in `doc/reviews/review-calibration.md`
captures the failure shape as a few-shot example. None of those is
a guarantee — type-system soundness on the diff you wrote remains
your responsibility, not the bot's.

## Sprint plan format

```markdown
# Plan NN — Title

## Goal
One sentence.

## Dependency Graph
ASCII art showing task dependencies (T1 → T2, T3 → T4, etc.)

## Tasks
Each task is T1, T2, etc. Each task section includes:
- Problem or motivation
- Solution / implementation approach
- Types or API surface

## Verification

### Properties (must pass)
Table of proptest property names, the module they live in, and the
invariant they assert. These are the contract — if a property can't
be satisfied, the sprint isn't done.

| Property | Module | Invariant |
|----------|--------|-----------|
| `msg_round_trips` | `crate_foo::codec` | encode then decode recovers original |

### Spot checks
Table of unit test names + specific assertions.

### Build gates
- cargo build — no errors
- cargo test — all pass (no `#[ignore]` without Review documentation)
- cargo clippy --all-targets — no errors
- End-to-end scenario description

## Deferred
What was intentionally left out and why.

## Review
- Any `#[ignore]`d properties: which ones, why, re-enablement plan
- Design deviations from the plan
- Recommendations
```
