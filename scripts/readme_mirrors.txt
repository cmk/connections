# Manifest of headline-Conn doctests that must stay byte-identical
# between their definition-site rustdoc and the mirrored block in
# README.md.
#
# Format: one entry per line, three pipe-separated fields:
#   <conn>|<src-file>|<anchor>
#
# - <conn>     — Conn const name, used in error messages.
# - <src-file> — path to the .rs file whose rustdoc owns the doctest.
# - <anchor>   — first non-blank line of both blocks; the script
#                slices from this line through the next ``` fence.
#
# Lines starting with `#` and blank lines are ignored.
#
# Every new headline Conn (one whose introduction motivated a
# README quick-tour example) should add an entry. Symmetric
# extensions of an existing family don't need a mirror — only
# Conns whose example block ships in README.

