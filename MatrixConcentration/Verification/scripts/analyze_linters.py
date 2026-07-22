#!/usr/bin/env python3
"""Structure and classify the V8 package-lint and clean-build warning output."""

from __future__ import annotations

import csv
import re
from collections import Counter
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]
LOGS = ROOT / "MatrixConcentration" / "Verification" / "logs"

BUILD_INFO_CLASSES = {
    "linter.style.header",
    "linter.style.longLine",
    "linter.style.maxHeartbeats",
    "linter.style.setOption",
    "linter.style.show",
}


def write_tsv(path: Path, header: list[str], rows: list[list[object]]) -> None:
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.writer(handle, delimiter="\t", lineterminator="\n")
        writer.writerow(header)
        writer.writerows(rows)


def analyze_build_warnings() -> tuple[int, Counter, Counter, Counter]:
    source = LOGS / "build_warning_inventory.tsv"
    rows: list[list[str]] = []
    by_class: Counter[tuple[str, str]] = Counter()
    by_module: Counter[tuple[str, str]] = Counter()
    by_severity: Counter[str] = Counter()
    with source.open(encoding="utf-8", newline="") as handle:
        for row in csv.DictReader(handle, delimiter="\t"):
            severity = "INFO" if row["class"] in BUILD_INFO_CLASSES else "MINOR"
            rows.append(
                [
                    row["file"],
                    row["line"],
                    row["column"],
                    row["class"],
                    severity,
                    row["message"],
                ]
            )
            by_class[(row["class"], severity)] += 1
            by_module[(row["file"], severity)] += 1
            by_severity[severity] += 1
    write_tsv(
        LOGS / "v8_build_warnings_classified.tsv",
        ["file", "line", "column", "class", "severity", "message"],
        rows,
    )
    write_tsv(
        LOGS / "v8_build_warnings_by_class.tsv",
        ["class", "severity", "count"],
        [[kind, severity, count] for (kind, severity), count in sorted(by_class.items())],
    )
    module_rows: list[list[object]] = []
    for module in sorted({key[0] for key in by_module}):
        module_rows.append(
            [
                module,
                by_module[(module, "MINOR")],
                by_module[(module, "INFO")],
                by_module[(module, "MINOR")] + by_module[(module, "INFO")],
            ]
        )
    write_tsv(
        LOGS / "v8_build_warnings_by_module.tsv",
        ["file", "minor", "info", "total"],
        module_rows,
    )
    return len(rows), by_class, by_module, by_severity


def analyze_package_lint() -> tuple[int, int, int, list[list[str]]]:
    text = (LOGS / "v8_lint_full.log").read_text(encoding="utf-8")
    scope = re.search(
        r"Found (\d+) errors in (\d+) declarations "
        r"\(plus (\d+) automatically generated ones\) in MatrixConcentration "
        r"with (\d+) linters",
        text,
    )
    if scope is None:
        raise SystemExit("package-scope header missing from v8_lint_full.log")
    error_count, named_count, generated_count, linter_count = map(int, scope.groups())
    if named_count + generated_count < 1000:
        raise SystemExit("package lint scope collapsed below 1,000 declarations")

    linter = ""
    module = ""
    rows: list[list[str]] = []
    for line in text.splitlines():
        linter_match = re.search(r"The `([^`]+)` linter reports:", line)
        if linter_match:
            linter = linter_match.group(1)
            continue
        module_match = re.match(r"-- (MatrixConcentration\.[A-Za-z0-9_]+)$", line)
        if module_match:
            module = module_match.group(1)
            continue
        hit_match = re.match(r"#check (@?\S+) /- (.+) -/$", line)
        if hit_match:
            if not linter or not module:
                raise SystemExit(f"unscoped package-lint hit: {line}")
            rows.append(
                [
                    module,
                    linter,
                    "MINOR",
                    hit_match.group(1),
                    hit_match.group(2),
                ]
            )
    if len(rows) != error_count:
        raise SystemExit(
            f"parsed {len(rows)} package-lint hits but header reports {error_count}"
        )
    write_tsv(
        LOGS / "v8_package_lint.tsv",
        ["module", "linter", "severity", "declaration", "message"],
        rows,
    )
    write_tsv(
        LOGS / "v8_package_lint_by_linter.tsv",
        ["linter", "minor", "info", "total"],
        [
            [kind, sum(row[1] == kind for row in rows), 0, sum(row[1] == kind for row in rows)]
            for kind in sorted({row[1] for row in rows})
        ],
    )
    write_tsv(
        LOGS / "v8_package_lint_by_module.tsv",
        ["module", "minor", "info", "total"],
        [
            [
                mod,
                sum(row[0] == mod for row in rows),
                0,
                sum(row[0] == mod for row in rows),
            ]
            for mod in sorted({row[0] for row in rows})
        ],
    )
    return named_count, generated_count, linter_count, rows


def main() -> None:
    total, _, _, severity = analyze_build_warnings()
    named, generated, linters, lint_rows = analyze_package_lint()
    summary = "\n".join(
        [
            "V8 LINTER ANALYSIS",
            f"package_named_declarations={named}",
            f"package_generated_declarations={generated}",
            f"package_total_declarations={named + generated}",
            f"package_linters={linters}",
            f"package_hits={len(lint_rows)}",
            f"package_minor={sum(row[2] == 'MINOR' for row in lint_rows)}",
            f"package_info={sum(row[2] == 'INFO' for row in lint_rows)}",
            f"build_warnings={total}",
            f"build_warning_minor={severity['MINOR']}",
            f"build_warning_info={severity['INFO']}",
            "scope_calibration=PASS",
            "",
        ]
    )
    (LOGS / "v8_lint_summary.txt").write_text(summary, encoding="utf-8")
    print(summary, end="")


if __name__ == "__main__":
    main()
