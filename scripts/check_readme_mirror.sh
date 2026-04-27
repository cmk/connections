#!/usr/bin/env bash
# Verify that headline-Conn doctests stay byte-identical between
# their src-file rustdoc and the mirrored code block in README.md.
#
# `cargo test --doc` already runs both — if the API breaks, both
# fail. This script catches *cosmetic* drift (a comment edit in one
# place that didn't propagate to the other), which the build does
# not.
#
# Mirror entries live in `scripts/readme_mirrors.txt`. Run manually
# before push or via the pre-commit hook in `.claude/settings.json`.

set -euo pipefail

cd "$(git rev-parse --show-toplevel)"

MANIFEST="scripts/readme_mirrors.txt"
README="README.md"

if [[ ! -f "$MANIFEST" ]]; then
    echo "ERROR: manifest not found at $MANIFEST" >&2
    exit 1
fi

drift=0

while IFS='|' read -r conn src_file anchor; do
    # Skip blank lines and comments.
    [[ -z "$conn" || "$conn" =~ ^[[:space:]]*# ]] && continue

    # Trim whitespace.
    conn="${conn#"${conn%%[![:space:]]*}"}"
    conn="${conn%"${conn##*[![:space:]]}"}"
    src_file="${src_file#"${src_file%%[![:space:]]*}"}"
    src_file="${src_file%"${src_file##*[![:space:]]}"}"
    anchor="${anchor#"${anchor%%[![:space:]]*}"}"
    anchor="${anchor%"${anchor##*[![:space:]]}"}"

    if [[ ! -f "$src_file" ]]; then
        echo "ERROR: $conn manifest points at missing file $src_file" >&2
        drift=1
        continue
    fi

    # Extract the rustdoc doctest. The doctest's first non-blank
    # line is the anchor; the closing `/// ` ``` ends the block.
    src_doc=$(
        sed -n "/^\/\/\/ ${anchor}\$/,/^\/\/\/ \`\`\`\$/p" "$src_file" \
            | sed -E 's|^/// ?||'
    )
    src_doc=$(printf '%s\n' "$src_doc" | sed '$d')

    # Extract the matching block from README.md.
    readme_block=$(
        sed -n "/^${anchor}\$/,/^\`\`\`\$/p" "$README"
    )
    readme_block=$(printf '%s\n' "$readme_block" | sed '$d')

    if [[ -z "$src_doc" ]]; then
        echo "ERROR: $conn doctest not found in $src_file (anchor: $anchor)" >&2
        drift=1
        continue
    fi
    if [[ -z "$readme_block" ]]; then
        echo "ERROR: $conn mirror block not found in $README (anchor: $anchor)" >&2
        drift=1
        continue
    fi

    if [[ "$src_doc" != "$readme_block" ]]; then
        {
            echo "ERROR: $conn doctest mirror has drifted between"
            echo "       $src_file (rustdoc) and $README."
            echo ""
            echo "--- $src_file (rustdoc, /// stripped)"
            echo "+++ $README (mirrored block)"
            diff -u <(printf '%s' "$src_doc") <(printf '%s' "$readme_block") || true
            echo ""
        } >&2
        drift=1
        continue
    fi

    echo "OK: $conn doctest mirror in sync ($src_file ↔ $README)"
done < "$MANIFEST"

exit "$drift"
