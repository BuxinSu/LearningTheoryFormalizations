#!/usr/bin/env python3
"""Inventory Lean/Lake warnings from one or more run_logged.py logs."""

from __future__ import annotations

import argparse
import collections
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]
WARNING = re.compile(r"^warning:\s+(?:(.+?\.lean):(\d+):(\d+):\s+)?(.*)$")
LINTER_OPTION = re.compile(r"set_option\s+(linter\.[A-Za-z0-9_.]+)\s+false")
BLOCK_BOUNDARY = re.compile(r"^(?:warning:|error:|info:|finished:|[✔⚠✖]\s+\[)")


def classify(block: str) -> str:
    lower = block.lower()
    if (
        "declaration uses 'sorry'" in lower
        or 'declaration uses "sorry"' in lower
        or "declaration uses `sorry`" in lower
    ):
        return "sorry"
    if "deprecated" in lower:
        return "deprecation"
    if "declaration has metavariables" in lower:
        return "metavariable"
    option = LINTER_OPTION.search(block)
    if option is not None:
        return option.group(1)
    return "other"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("logs", nargs="+", type=Path)
    args = parser.parse_args()
    rows: collections.Counter[tuple[str, str, str, str]] = collections.Counter()
    totals: collections.Counter[str] = collections.Counter()
    per_log: collections.Counter[tuple[str, str]] = collections.Counter()
    malformed = 0
    for supplied in args.logs:
        path = supplied if supplied.is_absolute() else ROOT / supplied
        lines = path.read_text(encoding="utf-8", errors="replace").splitlines()
        for index, line in enumerate(lines):
            if not line.startswith("warning:"):
                continue
            match = WARNING.match(line)
            if match is None:
                malformed += 1
                continue
            source, number, _column, _message = match.groups()
            source = source or "<no-source-location>"
            number = number or "-"
            block_lines = [line]
            cursor = index + 1
            while cursor < len(lines) and not BLOCK_BOUNDARY.match(lines[cursor]):
                block_lines.append(lines[cursor])
                cursor += 1
            kind = classify("\n".join(block_lines))
            rows[(source, number, kind, path.name)] += 1
            totals[kind] += 1
            per_log[(path.name, kind)] += 1

    print("WARNING INVENTORY")
    print("=================")
    print("scope: lake build logs (lakefile linter options active)")
    print(f"log_count: {len(args.logs)}")
    print(f"warning_header_count: {sum(totals.values())}")
    print(f"unparsed_warning_headers: {malformed}")
    print()
    print("[class totals]")
    for kind, count in sorted(totals.items()):
        print(f"{kind}: {count}")
    print()
    print("[per log]")
    for (log, kind), count in sorted(per_log.items()):
        print(f"{log}\t{kind}\t{count}")
    print()
    print("| File | Line | Warning class | Count | Build log |")
    print("|---|---:|---|---:|---|")
    for (source, number, kind, log), count in sorted(rows.items()):
        print(f"| `{source}` | {number} | {kind} | {count} | `{log}` |")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
