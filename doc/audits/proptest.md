---
name: proptest
day: mon
paths: [src/, tests/]
---
You are auditing the connections repo at the path you are launched in.
Your job: detect proptest generators or property batteries that have
been "relaxed" — under-sampling boundaries, dropping required laws,
or weakening the contract in ways that mask bugs.

Read first:
- CLAUDE.md (esp. the "Property-based testing is mandatory" section).
- doc/reviews/review-calibration.md (tone & severity standard).
- doc/chats/triple-adjunctions.md (full context on the FINE_MAX bug
  class this audit guards against).

Mechanical pass (run first; if it flags anything, report and stop —
LLM judgment not needed for these):

1. Q-format / Fixed-point strategies that don't bias boundaries.
   Pattern: any line in src/ or tests/ matching
       any::<[iu]\d+>\(\)\.prop_map\(Fixed[IU]\d+
   that is NOT inside a `prop_oneof![` block and NOT preceded by a
   `// uniform-sampling-ok:` justification comment.
   Why this matters: for TN ≥ 16 bits, P(hit MIN/MAX) is effectively
   zero with 256 cases. The Plan 32 saturation-plateau bugs were
   caught by manual trace, not by these proptests, because of this
   exact issue. Reference: MR !52, doc/chats/triple-adjunctions.md.
   Severity: must-fix.

2. `triple!` sites without `order_reflecting` coverage.
   For every `triple!` invocation under src/ (`grep -rn 'triple!' src/`),
   confirm there is either (a) a `law_battery!` invocation with
   `subset: full` covering it, or (b) an inline `order_reflecting`
   proptest. If neither, this is a Plan 33 escape (the
   `order_reflecting` predicate exists in src/prop/conn.rs precisely
   so future triples can't regress to non-order-reflecting `inner`
   undetected).
   Severity: must-fix.

3. `#[ignore]`d proptests without re-enablement notes.
   Pattern: `#[ignore]` immediately preceding a `proptest!` block or a
   `#[test]` named `*_galois_*` / `*_law_*` / `*_property_*` or any
   test in a `prop::` module, where the same file lacks an
   `// ignore: reason: ...` or `// re-enable: ...` comment within 5
   lines. CLAUDE.md TDD §13 requires re-enablement plans for any
   `#[ignore]`d property test.
   Severity: must-fix.

4. `subset: l_only` or `subset: r_only` on a `triple!`-marked Conn.
   Pattern: a `law_battery!` invocation referencing a marker that is
   defined via `triple!` but uses a one-sided subset. After Plan 32
   this should never happen — true triples need `subset: full` to get
   `floor_le_ceil` and `order_reflecting` coverage.
   Severity: must-fix.

5. `proptest_config` overrides that silently weaken cases.
   Pattern: `cases: N` where N < 32, or `max_global_rejects` /
   `max_local_rejects` set to a value that would cause silent test
   skipping. Acknowledge cap-of-64 for u128/i128 (documented), flag
   anything stricter without an explicit comment.
   Severity: follow-up.

Judgment pass (only if mechanical pass found nothing — the agent
earns its keep here):

6. Strategies that *appear* boundary-biased but use weights that
   suppress boundaries (e.g., `prop_oneof![1 => Just(MIN), 9999 =>
   any::<T>()]` — technically biased, effectively uniform). Walk every
   `prop_oneof!` in src/ and tests/, compute the boundary probability,
   and flag any where P(boundary) < 5%.

7. Custom `Arbitrary` / strategy functions in src/prop/arb.rs that
   have a "narrow" interior: e.g., `arb_extended_stdr_nanos_in_range`
   excludes values that would exercise the saturation arms of the
   Conn it generates inputs for. Read the function body, check what
   it excludes, and judge whether the exclusion masks a tested code
   path.

Output format:
- One section per category that has findings.
- Use the exact severity labels `[must-fix]` and `[follow-up]`.
- Each finding: file:line, the offending excerpt (≤5 lines), the rule
  it violates (cite CLAUDE.md / plan / doc), and the bug class it
  enables (1 sentence).
- If there are zero findings across all 7 checks: output exactly the
  single line `no findings` and nothing else (the harness greps for
  this to decide whether to append to the audit log).

Anti-themes (do NOT flag):
- A strategy using uniform `any::<T>()` *for the rung side of a Conn
  whose source has its own boundary-biased arb function*. The rung is
  the target type; biasing happens on the source.
- An apparent missing `order_reflecting` test on a `Conn::new_l` /
  `Conn::new_r` site. These are one-sided by construction; the
  predicate is `Triple`-bound and won't compile against them.
