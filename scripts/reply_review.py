#!/usr/bin/env python3
"""Post a reply into an existing MR discussion thread on GitLab.

GitLab's review model is discussions-of-notes: to reply to a specific
comment, you add a note to the discussion that comment lives in. This
script takes a note id and looks up its discussion, then appends a new
note to that discussion via
`POST /projects/:id/merge_requests/:iid/discussions/:discussion_id/notes`.

Prints the new note's id and web URL on success.

Requires: `glab` CLI authenticated for the current project.

Usage:
    scripts/reply_review.py <MR> <IN_REPLY_TO_ID> <BODY>
    scripts/reply_review.py <MR> <IN_REPLY_TO_ID> -    # read body from stdin
    scripts/reply_review.py <MR> <IN_REPLY_TO_ID> --body-file reply.md
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import subprocess
import sys

from _glab import resolve_mr

SHELL_RISK_CHARS = frozenset("`$\\\n\r")


def has_shell_risk_chars(value: str) -> bool:
    """Return whether an inline body is risky to pass through a shell."""
    return any(ch in value for ch in SHELL_RISK_CHARS)


def read_body(args: argparse.Namespace) -> str:
    """Read and validate the reply body from stdin, a file, or argv."""
    if args.body_file is not None:
        if args.body is not None:
            print(
                "error: pass either BODY/- or --body-file, not both",
                file=sys.stderr,
            )
            raise SystemExit(2)
        try:
            body = Path(args.body_file).read_text(encoding="utf-8")
        except OSError as exc:
            print(f"error: cannot read body file: {exc}", file=sys.stderr)
            raise SystemExit(1) from exc
    elif args.body == "-":
        body = sys.stdin.read()
    elif args.body is not None:
        body = args.body
        if has_shell_risk_chars(body) and not args.allow_inline_body:
            print(
                "error: inline BODY contains Markdown/shell-sensitive "
                "characters; pass '-' for stdin or --body-file PATH "
                "instead, or use --allow-inline-body if you intentionally "
                "handled quoting",
                file=sys.stderr,
            )
            raise SystemExit(2)
    else:
        print(
            "error: missing reply body; pass BODY, '-' for stdin, or "
            "--body-file PATH",
            file=sys.stderr,
        )
        raise SystemExit(2)

    body = body.strip()
    if not body:
        print("error: empty body", file=sys.stderr)
        raise SystemExit(1)
    return body


def find_discussion_for_note(project_id: str, mr: int, note_id: int) -> str:
    """Return the discussion_id that contains the given note_id."""
    page = 1
    while True:
        path = (
            f"projects/{project_id}/merge_requests/{mr}/discussions"
            f"?per_page=100&page={page}"
        )
        try:
            raw = json.loads(
                subprocess.check_output(
                    ["glab", "api", path], text=True, stderr=subprocess.PIPE
                )
            )
        except FileNotFoundError:
            print(
                "error: `glab` CLI not found; install GitLab CLI and ensure it is on PATH",
                file=sys.stderr,
            )
            raise SystemExit(1)
        except subprocess.CalledProcessError as exc:
            detail = (exc.stderr or "").strip()
            msg = f": {detail}" if detail else ""
            print(
                f"error: `glab api` failed for `{path}`{msg}", file=sys.stderr,
            )
            raise SystemExit(1)
        if not isinstance(raw, list) or not raw:
            break
        for d in raw:
            for n in d.get("notes", []) or []:
                # Coerce both sides: `note_id` comes from argparse as
                # int, but some GitLab API versions return note ids as
                # strings. Type-mismatched `==` is always False and
                # would exhaust the paging loop with a misleading
                # "not found" error.
                try:
                    api_id = int(n.get("id", 0))
                except (TypeError, ValueError):
                    continue
                if api_id == note_id:
                    return d["id"]
        if len(raw) < 100:
            break
        page += 1
    print(
        f"error: note id {note_id} not found in any discussion on MR !{mr}",
        file=sys.stderr,
    )
    raise SystemExit(1)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("mr", type=int, help="MR number (iid)")
    ap.add_argument(
        "in_reply_to_id",
        type=int,
        help="glab-id of the note you are replying to",
    )
    ap.add_argument(
        "body",
        nargs="?",
        help="Reply body (markdown). Pass '-' to read from stdin.",
    )
    ap.add_argument(
        "--body-file",
        metavar="PATH",
        help="Read reply body from a UTF-8 Markdown file.",
    )
    ap.add_argument(
        "--allow-inline-body",
        action="store_true",
        help=(
            "Allow inline BODY even if it contains shell-sensitive "
            "Markdown characters. Prefer '-' or --body-file instead."
        ),
    )
    ap.add_argument("--repo", default=None, help="group/project (default: auto)")
    args = ap.parse_args()

    try:
        body = read_body(args)
    except SystemExit as exc:
        return int(exc.code or 0)

    project_id = resolve_mr(args.mr, args.repo)
    discussion_id = find_discussion_for_note(project_id, args.mr, args.in_reply_to_id)
    path = (
        f"projects/{project_id}/merge_requests/{args.mr}"
        f"/discussions/{discussion_id}/notes"
    )

    try:
        result = subprocess.run(
            ["glab", "api", "--method", "POST", path, "-f", f"body={body}"],
            capture_output=True,
            text=True,
            check=True,
        )
    except FileNotFoundError:
        print(
            "error: `glab` CLI not found; install GitLab CLI and ensure it is on PATH",
            file=sys.stderr,
        )
        return 1
    except subprocess.CalledProcessError as exc:
        if exc.stderr:
            sys.stderr.write(exc.stderr)
        return exc.returncode or 1

    data = json.loads(result.stdout)
    print(f"posted reply id={data['id']} discussion={discussion_id}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
