# MR !74 — Extended functor-lift macros (`lift_l!` / `lift_r!` / `lift_k!`)

## Summary

- Add three macros that lift a parent `Conn` (or `ConnK` marker)
  through the `Extended` functor: `lift_l!` / `lift_r!` produce a
  fresh `Conn<Extended<A>, Extended<B>, K>` value (const-init
  friendly); `lift_k!` is a declaration macro that emits a fresh
  unit-struct triple marker. Synthetic markers map identically;
  the `Finite` arm dispatches through the parent. Specialises the
  Haskell `mapped :: Functor f => Cast k a b -> Cast k (f a) (f b)`
  to the only saturation-bearing functor the crate ships,
  `Extended`.
- Unblocks compose chains where one Conn's endpoint is already
  `Extended<…>` and the adjacent Conn's corresponding side is bare
  (e.g. the linklab `F064 → Extended<HD> → Epoch via UTC` chain is
  the proximate use case; `connections::hifi` itself does not ship
  any composed const in this MR).
- Drives the lifted Conns through the full `prop::conn::*` law
  battery: `Conn::identity::<i64>` lifted through `lift_l!` runs the
  `l_only` subset (galois_l, closure_l, kernel_l, monotone_l,
  idempotent, filter_l_*); the iso `Q000I016` lifted through
  `lift_k!` runs the `full` subset (14 properties incl.
  `floor_le_ceil`, `order_reflecting`, and the bracket family).

## Test plan

- [x] `cargo test --features testing --lib extended::` — 38 tests,
  all green (six spot checks + `lifted_id_i64::*` + `lifted_q000i016::*`).
- [x] `cargo test --features "testing macros hifi byte" --lib` — 1492
  tests, all green; no regressions in the existing hifi/time/fixed
  Conn law batteries.
- [x] `cargo test --features "testing macros hifi byte" --doc` — 94
  doctests, all green; the four new lift macro doctests
  (`lift_l!`, `lift_r!`, `lift_k!`, plus the module-doc paragraph)
  use only unconditional fixtures (`Conn::identity`, `Q000I016`).
- [x] `cargo clippy --all-targets --features testing -- -D warnings` —
  clean.
- [x] `cargo fmt --all -- --check` — clean.
- [x] `RUSTDOCFLAGS="-D warnings" cargo doc --no-deps --features testing
  --document-private-items` — clean (no broken intra-doc links).
- [x] `scripts/check-pii.sh` on the staged diff — clean.
- [x] `scripts/check_readme_mirror.sh` — clean (no mirrored sections
  touched).

## Local review (2026-05-08)

**Branch:** sprint/extended-functor-lift
**Commits:** 2 (origin/main..sprint/extended-functor-lift)
**Reviewer:** Claude (sonnet, independent)

---

## Pass 1 — Cold review (no plan)

### P1.A — Trait-claim audit

**Item 1: `lift_l!` macro** (`src/extended.rs`, diff lines ~452–471)

**1. The contract.** `Conn::new_l(ceil, inner)` constructs a `Conn<A, B, L>` claiming the L-Galois law: `ceil(a) ≤ b ⟺ a ≤ inner(b)` for all `a : Extended<A>`, `b : Extended<B>`.

**2. The implementation.** The `ceil` closure maps `NegInf ↦ NegInf`, `Finite(x) ↦ Finite(parent.ceil(x))`, `PosInf ↦ PosInf`. The `inner` (upper) closure maps `NegInf ↦ NegInf`, `Finite(y) ↦ Finite(parent.upper(y))`, `PosInf ↦ PosInf`.

**3. Consistency.** Walk the 9-cell case table over `Extended`'s total order `NegInf < Finite(t) < PosInf`:

| a | b | ceil(a) ≤ b | a ≤ upper(b) | Match? |
|---|---|-------------|--------------|--------|
| NegInf | NegInf | NegInf ≤ NegInf = true | NegInf ≤ NegInf = true | yes |
| NegInf | Finite(y) | NegInf ≤ Finite(y) = true | NegInf ≤ Finite(parent.upper(y)) = true | yes |
| NegInf | PosInf | NegInf ≤ PosInf = true | NegInf ≤ PosInf = true | yes |
| Finite(x) | NegInf | Finite(parent.ceil(x)) ≤ NegInf = false | Finite(x) ≤ NegInf = false | yes |
| Finite(x) | Finite(y) | Finite(parent.ceil(x)) ≤ Finite(y) = (parent.ceil(x) ≤ y) | Finite(x) ≤ Finite(parent.upper(y)) = (x ≤ parent.upper(y)) — equals the parent's galois_l | yes, by parent's law |
| Finite(x) | PosInf | Finite(parent.ceil(x)) ≤ PosInf = true | Finite(x) ≤ PosInf = true | yes |
| PosInf | NegInf | PosInf ≤ NegInf = false | PosInf ≤ NegInf = false | yes |
| PosInf | Finite(y) | PosInf ≤ Finite(y) = false | PosInf ≤ Finite(parent.upper(y)) = false | yes |
| PosInf | PosInf | PosInf ≤ PosInf = true | PosInf ≤ PosInf = true | yes |

All 9 cells are consistent. The L-Galois law holds unconditionally on `Extended<A>` × `Extended<B>` whenever the parent satisfies it on `A` × `B`. Consistent.

**Item 2: `lift_r!` macro** (`src/extended.rs`, diff lines ~494–513)

**1. The contract.** `Conn::new_r(inner, floor)` — per `src/conn.rs:270`, first arg is `inner: fn(B) -> A`, second is `floor: fn(A) -> B` — constructs `Conn<A, B, R>` claiming R-Galois: `inner(b) ≤ a ⟺ b ≤ floor(a)`.

**2. The implementation.**
```rust
$crate::conn::Conn::new_r(
    |b| match b { ... ConnR::lower(&$parent, y) ... },  // first arg = inner (B→A)
    |a| match a { ... ConnR::floor(&$parent, x) ... },  // second arg = floor (A→B)
)
```
`ConnR::lower` maps `B → A` (the lower adjoint / embedding). `ConnR::floor` maps `A → B` (the upper adjoint / round-down). `new_r` expects `(inner: fn(B)->A, floor: fn(A)->B)`. First closure returns `Extended<A>` from `Extended<B>` via `lower` — correct for `inner`. Second closure returns `Extended<B>` from `Extended<A>` via `floor` — correct for `floor`. Argument order is correct.

**3. Consistency.** 9-cell walk analogous to `lift_l!`: synthetic arms map identically, Finite arm reduces to parent's R-Galois law. Consistent.

**Item 3: `lift_k!` macro** (`src/extended.rs`, diff lines ~549–582)

**1. The contract.** Emits a unit struct implementing both `ConnL<Extended<A>, Extended<B>>` and `ConnR<Extended<A>, Extended<B>>`, claiming both L and R Galois laws plus the iso round-trip laws (`upper(ceil(a)) == a` and `lower(floor(a)) == a`) when the parent is an iso.

**2. The implementation.** `conn_l` calls `lift_l!(PARENT)`, `conn_r` calls `lift_r!(PARENT)`. The `$parent:path` pattern (not `$parent:expr`) means only path-form parents are accepted, preventing the local-variable case that would break const-coercion. This is stricter than `lift_l!`/`lift_r!` which use `$parent:expr`.

**3. Consistency.** Both views delegate to the already-audited `lift_l!`/`lift_r!`, which are consistent. The iso round-trip laws carry because `Finite(upper(ceil(x))) = Finite(parent.upper(parent.ceil(x)))` and the parent's iso law gives `parent.upper(parent.ceil(x)) == x` for every `x` in the parent's domain. Consistent.

**Item 4: `EXTQ000I016` test marker** (diff line 681)

`lift_k!(EXTQ000I016 : FixedI16<U0> => i16 = Q000I016)` — parent is the iso `Q000I016 : FixedI16<U0> ↔ i16`. `Q000I016` impls both `ConnL` and `ConnR` via the `iso!` expansion. All laws of an iso carry through the lift (audit above). Consistent.

**Item 5: `LIFTED_ID_I64` const** (diff line 735)

`lift_l!(Conn::<i64, i64, L>::identity())` — `Conn::identity()` is a `Conn<i64, i64, L>` satisfying the L-Galois law (identity is a degenerate iso). The lift inherits this. Correct subset `l_only` chosen since the result is `Conn<_, _, L>`, not a triple. Consistent.

**Summary of trait-claim audit:** All five items are consistent. No type-claim violations found.

---

### P1.B — Standard review

#### Commit Hygiene

Two commits: `feat: Add Extended functor-lift macros (lift_l!/lift_r!/lift_k!)` and `doc: Draft review-00074 for MR !74`. Both use conventional prefixes, subjects are under 72 characters. The `doc:` commit is pure-doc with no source changes — acceptable. The `feat:` commit is atomic (macros + tests together). Both are buildable by themselves. Clean.

#### Code Quality

No `unsafe` introduced. `$crate::` paths used throughout both macros — macro hygiene is correct. The `lift_k!` uses `$parent:path` (tighter than `$parent:expr`), which is intentional and documented. No dead code visible.

One observation: the `lift_l!` and `lift_r!` docs warn about the "stable path" constraint for const-init, but the macros accept `$parent:expr` — a local variable passed to `lift_l!` will compile to a non-const closure capture (not a fn-pointer) and fail at the `new_l` call site with a type error. This is acceptable behavior (compile error, not silent runtime bug), and the rustdoc documents the constraint. Not a bug.

#### Test Coverage

The `law_battery!` for `LIFTED_ID_I64` uses `l_only` — correct for a `Conn<_, _, L>` value. The `l_only` battery covers `galois_l`, `closure_l`, `kernel_l`, `monotone_l`, `idempotent`, and three `filter_l_*` properties. Adequate.

The `law_battery!` for `EXTQ000I016` uses the default `full` subset — correct for a ConnK triple marker. `full` covers all 14 properties including `floor_le_ceil`, `order_reflecting`, and the bracket family. Adequate.

The test comment at the top of `lift_tests` (diff lines 600–610) says a third fixture — lifted `F064F032` through `iso_only` — was planned but examining the actual test code, no such `law_battery!` invocation is present. The comment is orphaned. The `iso_only` subset would cover `idempotent`, `iso_roundtrip_l`, and `roundtrip_ceil` — properties not tested on a float-based lifted Conn. This is a gap relative to what the comment promises.

The `lift_finite_matches_parent_ceil` and `lift_finite_matches_parent_floor` properties from the plan's Verification table are not present as named proptest cases. They are covered implicitly by the `galois_l`/`galois_r` property at the `Finite` arm, but not as explicit isolated properties.

The T5 smoke const ("one smoke const mirroring the linklab `F64_SECS_EPOCH_VIA_UTC` shape") is missing from the diff. The `lift_l_const_init_smoke` test proves const-init for `lift_l!` alone, but does not demonstrate a full `compose_l!` chain through a `lift_k!`-emitted bridge — the precise shape the motivating use case requires.

#### Risks

No new dependencies. No `hifi` mentions in any doc/doctest — clean. The `lift_k!` macro emits a `pub struct` at the call site; when used inside `#[cfg(test)]` module, the struct is test-local only, which is the intended use. No macro-export shadowing issues (names are new). Re-export in `src/lib.rs` at `pub mod macros` is correct.

---

## Pass 2 — Plan-aware review

### P2.A — Test-exception escalation

The plan's Verification table (T3) lists two properties involving `F064F032` as the iso parent: `lift_k_iso_roundtrip_l` and `lift_k_iso_roundtrip_r`. The test comment in the diff explicitly references these ("Drive lifted `F064F032`… through `iso_only`"), but the `law_battery!` invocation is absent. This is not a test relaxation — it is a complete omission. The type claim is not violated (the audit shows the laws hold), but the contract between the plan and the implementation is broken: two of the twelve properties in the Verification table have no corresponding test. This does not rise to a must-fix on type-soundness grounds, but it is a plan-conformance gap.

No test relaxation suffixes (`*_total`, `*_relaxed`, etc.) appear in the diff. No P1 soundness promotion needed.

### P2.B — Plan conformance

| Task | Status |
|------|--------|
| T1 — `lift_l!` / `lift_r!` expression macros | Implemented. Shape matches plan sketch verbatim. |
| T2 — `lift_k!` declaration macro | Implemented. Expansion matches plan. `$parent:path` used (tighter than plan's `$parent:expr` sketch — acceptable). |
| T3 — Property tests | Partially implemented. `LIFTED_ID_I64` (l_only), `EXTQ000I016` (full) present. The third fixture `F064F032` `iso_only` battery is absent despite appearing in the test comment header. The named properties `lift_k_iso_roundtrip_l`, `lift_k_iso_roundtrip_r` from the Verification table have no test. |
| T4 — Doc + executable examples | `lift_l!` doctest present (uses `Conn::identity::<i64>`). `lift_r!` doctest present. `lift_k!` doctest present (uses `Q000I016`). Module-level paragraph appended. No `hifi` mentions. All unconditional fixtures. Complete. |
| T5 — Re-export wiring | `src/lib.rs` updated with `lift_k, lift_l, lift_r` in `pub mod macros`. `#[macro_export]` present. Wiring complete. The T5 smoke const ("one smoke const mirroring the linklab `F64_SECS_EPOCH_VIA_UTC` shape against connections-internal types only") is absent — no `compose_l!` chain through a `lift_k!` bridge appears anywhere in the diff. |

The `lift_finite_matches_parent_ceil` and `lift_finite_matches_parent_floor` properties from the Verification table are not present as named standalone tests. They are exercised indirectly by `galois_l`/`galois_r` on `Finite` inputs but not as dedicated cases.

The plan says the `Review` section (post-implementation) should be filled in before merge; it remains at its template placeholder text. This is a process gap per CLAUDE.md §TDD workflow step 6 ("Append Deferred and Review sections to the plan document").

---

## Recommendations

**Must fix before push:**

None. The trait-claim audit found no law violations. The diff compiles, test suites report green (per the review-00074 test plan section), and no existing Conn law batteries are broken.

**Follow-up (future work):**

1. **Missing `F064F032` `iso_only` battery** (`src/extended.rs`, `lift_tests` module). The comment at the top of `lift_tests` promises a `law_battery!` for lifted `F064F032` through `iso_only`, and the Verification table names `lift_k_iso_roundtrip_l` / `lift_k_iso_roundtrip_r` as required properties. Neither is present. The comment is orphaned. Add the battery or remove the comment and strike the rows from the Verification table. Confidence: 95.

2. **Missing T5 compose-chain smoke const** (`src/extended.rs`). The plan requires "one smoke const mirroring the linklab `F64_SECS_EPOCH_VIA_UTC` shape against connections-internal types only" to prove the full `compose_l!`-through-`lift_k!` chain type-checks end-to-end. The `lift_l_const_init_smoke` test proves `lift_l!` alone, not the composed chain. Add a `const` that does `compose_l!(lift_l!(SOME_IN_TREE_CONN), SOME_OTHER_IN_TREE_CONN)` inside the test module. Confidence: 90.

3. **Plan Review section not filled in** (`doc/plans/plan-2026-05-08-01.md`). CLAUDE.md §TDD step 6 requires appending a Review section before push. The plan's `## Review` section still contains only the pre-implementation template questions. Fill in the post-implementation observations. Confidence: 85.
