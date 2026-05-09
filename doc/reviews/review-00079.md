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

## Local review (2026-05-08)

**Branch:** sprint/audit-2026-05-08
**Commits:** 4 (origin/main..HEAD)
**Reviewer:** Claude (sonnet, independent)

---

# Review 79 — Eliminate `Conn<Extended<A>, Extended<B>>` antipattern

## P1.A — Trait-Claim Audit

### 1. `U032CHAR : u32 => char` — `conn_l!` (`src/char.rs`)

**Contract.** `conn_l!` declares a `Conn<u32, char, L>`, claiming Galois L: `ceil(a) ≤ b ⟺ a ≤ upper(b)` for all `(a: u32, b: char)`.

**Implementation.**
- `ceil`: if `u > 0x10FFFF` → `'\u{10FFFF}'`; surrogate range → `'\u{E000}'`; otherwise `char::from_u32(u)` (total on the non-surrogate, in-range domain; fallback arm returns `'\u{10FFFF}'`).
- `inner`: if `c == '\u{10FFFF}'` → `u32::MAX`; otherwise `c as u32`.

**Consistency.** Consistent and sound. Key boundary cases:
- `a = u32::MAX, b = '\u{10FFFF}'`: `ceil(MAX) = '\u{10FFFF}' ≤ '\u{10FFFF}'` (True) iff `MAX ≤ inner('\u{10FFFF}') = u32::MAX` (True). Holds.
- `a = 0xD800, b = '\u{D7FF}'`: `ceil = '\u{E000}' ≤ '\u{D7FF}'` (False) iff `0xD800 ≤ 0xD7FF` (False). Holds.
- `closure_l` at `a = u32::MAX`: `inner(ceil(MAX)) = inner('\u{10FFFF}') = u32::MAX ≥ u32::MAX`. Holds.

The ConnK demotion to ConnL is correct: `inner('\u{10FFFF}') = u32::MAX ≠ 0x10FFFF`, so `floor` cannot satisfy `inner ⊣ floor` simultaneously with `ceil ⊣ inner`.

### 2. `SDURU064 : StdDuration => u64` — `conn_l!` (`src/time/duration.rs`)

**Contract.** `Conn<StdDuration, u64, L>`, claiming Galois L over all `(StdDuration, u64)`.

**Implementation.**
- `ceil`: `d.as_secs() + (subsec > 0 ? 1 : 0)`, with `saturating_add(1)` at the overflow boundary (as_secs == `u64::MAX` and subsec > 0 → `u64::MAX`).
- `inner`: `if s == u64::MAX { StdDuration::MAX } else { StdDuration::from_secs(s) }`.

**Consistency.** Consistent and sound.
- At `a = StdDuration::MAX` (as_secs = `u64::MAX`, subsec = 999_999_999), `b = u64::MAX`: `ceil(MAX) = u64::MAX ≤ u64::MAX` (True) iff `MAX ≤ inner(u64::MAX) = StdDuration::MAX` (True). Holds.
- At `a = StdDuration::MAX, b = u64::MAX - 1`: `u64::MAX ≤ u64::MAX-1` (False) iff `MAX ≤ from_secs(u64::MAX-1)` — `MAX.as_secs() = u64::MAX > u64::MAX-1`, so False. Holds.
- `closure_l` at `a = MAX-1ns`: `inner(ceil(MAX-1ns)) = inner(u64::MAX) = StdDuration::MAX ≥ MAX-1ns`. Holds.

ConnK demotion is correct.

### 3. `SDURU128 : StdDuration => u128` — `conn_l!` (`src/time/duration.rs`)

**Contract.** `Conn<StdDuration, u128, L>`, claiming Galois L. Previously `Extended<StdDuration> => Extended<u128>`, shape unchanged to ConnL.

**Implementation.**
- `ceil`: `d.as_nanos()` (exact, no overflow since `StdDuration::MAX.as_nanos()` ≪ `u128::MAX`).
- `inner`: if `n > StdDuration::MAX.as_nanos()` → `StdDuration::MAX`; otherwise reconstruct.

**Consistency.** Consistent. The above-max saturation was already present; stripping the `Extended` wrapper removes the dead `NegInf`/`PosInf` arms.

### 4. `F064SDUR : F064 => StdDuration` — `conn_l!` (`src/time/duration.rs`)

**Contract.** `Conn<ExtendedFloat<f64>, StdDuration, L>`, claiming Galois L over all `(ExtendedFloat<f64>, StdDuration)`.

**Implementation.**
- `ceil`: `Bot → ZERO`, `Top → MAX`, `Extend(NaN) → MAX`, `Extend(+∞) → MAX`, `Extend(v ≤ 0) → ZERO`, `Extend(v > max_secs) → MAX`; otherwise walk-based ceil.
- `inner`: `MAX → Top`; otherwise `Extend(d.as_secs_f64())`.

**Consistency.** Consistent and sound.
- `a = Top, b = MAX`: `ceil(Top) = MAX ≤ MAX` (True) iff `Top ≤ inner(MAX) = Top` (True). Holds.
- `a = Top, b = MAX - 1ns`: `MAX ≤ MAX-1ns` (False) iff `Top ≤ inner(MAX-1ns) = Extend(...)` (False, Top is maximum). Holds.
- `a = Extend(neg), b = ZERO`: `ZERO ≤ ZERO` (True) iff `Extend(neg) ≤ inner(ZERO) = Extend(0.0)` (True). Holds.
- `a = Bot, b = ZERO`: `ZERO ≤ ZERO` (True) iff `Bot ≤ Extend(0.0)` (True). Holds.

One gap: the `galois_l` and `kernel_l` proptests use `arb_std_duration_bounded_f64()` (secs ≤ 1e9), which excludes `StdDuration::MAX`. The `f64_sdur_synthetic_top` spot test covers `inner(MAX) = Top`. Same coverage shape as before the diff; no regression.

### 5. `F032SDUR : F032 => StdDuration` — `conn_l!` (`src/time/duration.rs`)

**Contract.** `Conn<ExtendedFloat<f32>, StdDuration, L>`, same shape as F064SDUR.

**Implementation.** Mirrors F064SDUR with `f32`.

**Consistency.** Consistent by the same argument as F064SDUR.

## P1.B — Standard Review

### Commit Hygiene

Four commits, conventional subjects (`plan:`, `refactor:` ×2, `task:`), cleanly scoped. The SDUR commit message says "Strip Extended<…> from SDUR family Conns" — F064SDUR/F032SDUR had `Extended<StdDuration>` on the codomain only, not both sides. Accurate enough given the body.

### Code Quality

- No unsafe code introduced. `const fn ceil_u32_char` is const-eligible; the `match char::from_u32` fallback arm (returning `'\u{10FFFF}'`) is dead code on the non-surrogate in-range domain, but it keeps the function `const`.
- The `sduru064_inner` comment correctly derives why `u64::MAX → StdDuration::MAX` is required.
- `src/time.rs` line 124 references `"the Plan 2026-05-08 antipattern strip"`. Plan identifiers are internal process artifacts; public docs should be self-contained.
- No clippy-visible issues observed.

### Test Coverage

**Property tests.** All five changed Conns receive `law_battery!(…, subset: l_only)` or equivalent hand-rolled proptest coverage for `galois_l`, `closure_l`, `kernel_l`, `monotone_l`, `idempotent`. The SDURU128 switch from hand-rolled `proptest!` blocks to `law_battery!` is a net improvement. `arb_u32_char_boundary` is correctly biased toward the six Unicode boundary values.

**Shell tests for `check_no_ext_ext_conn.sh`.** The plan's Verification table lists three properties (`no_ext_ext_conn_clean_tree`, `no_ext_ext_conn_blocks_violation`, `no_ext_ext_conn_allow_pragma_works`) in `tests/no_ext_ext_*`. **No such tests exist in the diff.** The guardrail's correctness is untested beyond manual inspection. This is the primary gap.

### Risks

- Guardrail reads staged blobs (`git show :$f`) — correct.
- Regex `Extended<[^>]*>` does not handle nested generics. No such types exist; documented.
- The plan's pseudocode reads from worktree, the shipped script reads from staged blob — shipped version is strictly better.
- All five Conns now use bare types. Pre-1.0; breaking API changes acceptable per CLAUDE.md.

## P2.A — Test-Exception Escalation

Plan explicitly notes "ConnL only — Galois R fails at the top boundary by saturation" and "synthetic-top promotion breaks the dual `inner ⊣ floor` adjunction". Both type declarations are `conn_l!` (not `conn_k!`). No unrelaxed law is claimed. No escalation needed.

## P2.B — Plan Conformance

| Task | Planned | Implemented |
|------|---------|-------------|
| T1a: `U032CHAR` demoted to ConnL, bare types | Yes | Yes |
| T1a: `synthetic_top` spot test | Yes | Yes |
| T1a: `floor_le_ceil` proptest dropped | Yes | Yes |
| T1a: `law_battery!(…, subset: l_only)` | Yes | Yes |
| T1a: `arb_u32_char_boundary` strategy | Yes | Yes |
| T1b: F064SDUR / F032SDUR codomain stripped | Yes | Yes |
| T1b: SDURU064 demoted to ConnL | Yes | Yes |
| T1b: SDURU128 bare types, law_battery | Yes | Yes |
| T1b: Kani proof update (`time_pure.rs`) | Yes | Yes |
| T1b: Module docs rewritten | Yes | Yes |
| T2: `scripts/check_no_ext_ext_conn.sh` | Yes | Yes |
| T2: Wired into `.githooks/pre-commit` and `.claude/settings.json` | Yes | Yes |
| T2: Shell tests for the guardrail (`tests/no_ext_ext_*`) | Yes | **Missing** |
| `arb_extended_*` strategies removed | Yes | Yes |

## Recommendations

### Must fix before push

1. **Shell tests for `check_no_ext_ext_conn.sh` are absent.** The plan's Verification table lists three properties as must-pass; none shipped. Add a minimal `tests/no_ext_ext_conn.sh` that: (a) asserts script exits 0 on the staged tree; (b) creates a temp file with `Extended<X> => Extended<Y>`, stages, asserts exit 1; (c) re-stages with `// allow(ext-ext-conn):` pragma, asserts exit 0.

### Follow-up (future work)

2. **`src/time.rs` module-level doc references plan identifier.** Line 124: `"per the Plan 2026-05-08 antipattern strip"`. Replace with `"(MR !79 — bare-type refactor)"` so public rustdoc is self-contained.

3. **`galois_l` / `kernel_l` for F???SDUR not proptest'd at `b = StdDuration::MAX`.** Bounded strategy predates this diff (not a regression). Extending `arb_std_duration_bounded_f64` to occasionally emit `StdDuration::MAX` (1:8 weight alongside the existing boundary values) would close this gap.
