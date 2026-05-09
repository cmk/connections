#!/usr/bin/env bash
# Block the `Conn<Extended<A>, Extended<B>>` antipattern from
# entering the source tree by hand.
#
# Scans staged .rs files for two related shapes:
#   1. Declaration arrow:  `Extended<X> => Extended<Y>`
#      (used by `conn_l!`/`conn_k!`/`conn_r!` macro bodies)
#   2. Type annotation:    `Conn<Extended<X>, Extended<Y>` (any K)
#
# Allowlist:
#   - `src/extended.rs` — home of `lift_l!`/`lift_r!`/`lift_k!`,
#     which legitimately *produce* the Ext-Ext shape from a non-Ext
#     parent. Doc-comment examples in this file may also reference
#     the shape.
#   - Lines preceded by a `// allow(ext-ext-conn): <reason>` comment
#     on the immediately previous line.
#
# `lift_l!`/`lift_r!`/`compose_l!`/`compose_r!` macro INVOCATIONS
# elsewhere in the tree synthesize the Ext-Ext shape at the type
# level but produce no source-text match because their bodies use
# `Conn::new_l` / `Conn::new_r` on the lifted closures — they do not
# declare `Extended<…> => Extended<…>` syntactically. So no special
# casing is needed for them.
#
# Runtime is O(staged-rust-files), not O(repo).
set -euo pipefail

# Match either:
#   - `Extended<…> => Extended<…>`   (declaration arrow)
#   - `Conn<Extended<…>, Extended<` (type annotation)
patterns=(
  'Extended<[^>]*>[[:space:]]*=>[[:space:]]*Extended<'
  'Conn<Extended<[^>]*>,[[:space:]]*Extended<'
)
alt=$(IFS='|'; echo "${patterns[*]}")

exit_status=0

# ACMR = Added / Copied / Modified / Renamed; excludes pure
# deletions. The exclusion list keeps `src/extended.rs` and this
# script itself out of the scan. Read names via NUL terminators so
# paths with spaces survive.
while IFS= read -r -d '' f; do
  [ -z "$f" ] && continue
  case "$f" in
    *.rs) ;;
    *) continue ;;
  esac

  # Use the staged blob (vs. the worktree file) so the check sees
  # exactly what's about to be committed.
  staged=$(git show ":$f" 2>/dev/null || true)
  [ -z "$staged" ] && continue

  while IFS=: read -r lineno line; do
    [ -z "$lineno" ] && continue
    if [ "$lineno" -gt 1 ]; then
      prev_line=$(printf '%s\n' "$staged" | sed -n "$((lineno - 1))p")
      if [[ "$prev_line" =~ //[[:space:]]*allow\(ext-ext-conn\): ]]; then
        continue
      fi
    fi
    echo "error: $f:$lineno — Conn<Extended<…>, Extended<…>> antipattern" >&2
    echo "  $line" >&2
    exit_status=1
  done < <(printf '%s\n' "$staged" | grep -nE "$alt" || true)
done < <(
  git diff --cached --name-only -z --diff-filter=ACMR -- \
    . ':(exclude)src/extended.rs' \
    ':(exclude)scripts/check_no_ext_ext_conn.sh'
)

if [ $exit_status -ne 0 ]; then
  cat >&2 <<'HINT'

The Conn<Extended<A>, Extended<B>> shape adds dead synthetic rungs
on whichever side has no real semantic content. To compose into an
Ext-Ext shape, derive it via `lift_l!`/`lift_r!`/`compose_l!`/
`compose_r!` from a non-Ext parent (those macros produce the same
type at use-site without a hand-rolled declaration).

If you genuinely need a hand-rolled Ext-Ext Conn (rare), add
'// allow(ext-ext-conn): <one-line reason>' on the line directly
above the offending line.
HINT
fi

exit $exit_status
