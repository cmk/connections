#!/usr/bin/env bash
# Verify that the F064B016 doctest in src/conn/float/f64.rs and the
# F064B016 code block mirrored into README.md remain identical.
#
# `cargo test --doc` already runs both — if the API breaks, both fail.
# This script catches *cosmetic* drift (a comment edit in one place
# that didn't propagate to the other), which the build does not.
#
# Run manually before push, or wire into a pre-commit hook.

set -euo pipefail

cd "$(git rev-parse --show-toplevel)"

SRC_FILE="src/conn/float/f64.rs"
README="README.md"
ANCHOR='use connections::conn::float::f64::F064B016;'

# Extract the F064B016 rustdoc doctest. The doctest's first non-blank
# line is the import of F064B016 (anchor). The closing fence `/// \`\`\``
# ends the block.
src_doc=$(
    sed -n "/^\/\/\/ ${ANCHOR}\$/,/^\/\/\/ \`\`\`\$/p" "$SRC_FILE" \
        | sed -E 's|^/// ?||'
)

# Drop the trailing ``` fence (the only remaining ``` after stripping).
src_doc=$(printf '%s\n' "$src_doc" | sed '$d')

# Extract the matching block from README.md — bounded by the same
# anchor line and the next ``` fence.
readme_block=$(
    sed -n "/^${ANCHOR}\$/,/^\`\`\`\$/p" "$README"
)
readme_block=$(printf '%s\n' "$readme_block" | sed '$d')

if [ "$src_doc" != "$readme_block" ]; then
    {
        echo "ERROR: F064B016 doctest mirror has drifted between"
        echo "       ${SRC_FILE} (rustdoc) and ${README}."
        echo ""
        echo "--- ${SRC_FILE} (rustdoc, /// stripped)"
        echo "+++ ${README} (mirrored block)"
        diff -u <(printf '%s' "$src_doc") <(printf '%s' "$readme_block") || true
    } >&2
    exit 1
fi

echo "OK: F064B016 doctest mirror in sync"
