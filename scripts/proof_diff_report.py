#!/usr/bin/env python3
"""Emit a Markdown proof/tactic diff summary for a PR (Lean files only)."""
from __future__ import annotations

import re
import subprocess
import sys


def git_diff_lean(base: str, head: str) -> str:
    return subprocess.check_output(
        ["git", "diff", base, head, "--", "*.lean"],
        text=True,
        stderr=subprocess.DEVNULL,
    )


def diff_lines(diff: str, prefix: str) -> list[str]:
    out: list[str] = []
    plen = len(prefix)
    for line in diff.splitlines():
        if line.startswith(prefix) and not line.startswith(prefix * 2):
            out.append(line[plen:])
    return out


def count_matches(lines: list[str], pattern: re.Pattern[str]) -> int:
    return sum(1 for line in lines if pattern.search(line))


def main() -> int:
    if len(sys.argv) != 4:
        print("usage: proof_diff_report.py <base_sha> <head_sha> <out_md>", file=sys.stderr)
        return 2
    base, head, out_path = sys.argv[1], sys.argv[2], sys.argv[3]
    diff = git_diff_lean(base, head)
    added = diff_lines(diff, "+")
    removed = diff_lines(diff, "-")

    # Tactic-like tokens (conservative: avoid matching substrings like in identifiers)
    yo_pat = re.compile(r"(?:^|\s)(?:by\s+)?yo(?![a-zA-Z0-9_?'])")
    nat_pat = re.compile(r"naturality!")
    yoq_pat = re.compile(r"yo\?")
    natq_pat = re.compile(r"naturality\?")

    a_yo = count_matches(added, yo_pat)
    r_yo = count_matches(removed, yo_pat)
    a_nat = count_matches(added, nat_pat)
    r_nat = count_matches(removed, nat_pat)
    a_yoq = count_matches(added, yoq_pat)
    r_yoq = count_matches(removed, yoq_pat)
    a_natq = count_matches(added, natq_pat)
    r_natq = count_matches(removed, natq_pat)

    lines_added = len(added)
    lines_removed = len(removed)

    md = f"""## Proof diff (Lean files)

Comparing `{base[:7]}` … `{head[:7]}`.

### Tactic mentions (added / removed lines)

| Pattern | Added | Removed | Net |
|---------|------:|--------:|----:|
| `yo` | {a_yo} | {r_yo} | {a_yo - r_yo} |
| `naturality!` | {a_nat} | {r_nat} | {a_nat - r_nat} |
| `yo?` | {a_yoq} | {r_yoq} | {a_yoq - r_yoq} |
| `naturality?` | {a_natq} | {r_natq} | {a_natq - r_natq} |

### Line churn (proof context)

| Metric | Count |
|--------|------:|
| Lines added (in .lean) | {lines_added} |
| Lines removed (in .lean) | {lines_removed} |

_Heuristic only: counts are regex hits on diff lines, not AST-aware._
"""
    with open(out_path, "w", encoding="utf-8") as f:
        f.write(md)
    print(md)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
