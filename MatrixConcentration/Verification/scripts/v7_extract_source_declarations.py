#!/usr/bin/env python3
"""Extract the complete public source-declaration inventory for V7.

The extraction is lexical but comment/string aware.  It uses the same fixed
14-module source scope as the other verification scripts and records private
declarations separately so that visibility is measured rather than inferred.
"""

from __future__ import annotations

import csv
import json
import re
from pathlib import Path

from lean_source_scan import LOGS, ROOT, lexical_contexts, relative


SOURCE = ROOT / "MatrixConcentration"
DECLARATION = re.compile(
    r"(?m)^[ \t]*(?:@\[[^\n]*\]\s*)*"
    r"(?:(?:private|protected|noncomputable)\s+)*"
    r"(?P<keyword>theorem|lemma|def|structure|class)\s+"
    r"(?P<name>[^\s({:\[]+)"
)


def mask_noncode(text: str) -> str:
    contexts = lexical_contexts(text)
    return "".join(
        character if context == 0 or character == "\n" else " "
        for character, context in zip(text, contexts, strict=True)
    )


def main() -> int:
    paths = sorted(SOURCE.glob("*.lean"))
    if len(paths) != 14:
        raise RuntimeError(f"expected 14 flat source modules, found {len(paths)}")

    rows: list[dict[str, object]] = []
    for path in paths:
        text = path.read_text(encoding="utf-8")
        masked = mask_noncode(text)
        for match in DECLARATION.finditer(masked):
            prefix = masked[match.start() : match.start("keyword")]
            rows.append(
                {
                    "module": f"MatrixConcentration.{path.stem}",
                    "path": relative(path),
                    "line": masked.count("\n", 0, match.start("keyword")) + 1,
                    "keyword": match.group("keyword"),
                    "raw_name": match.group("name"),
                    "visibility": (
                        "private"
                        if re.search(r"\bprivate\b", prefix)
                        else "public"
                    ),
                }
            )

    for source_id, row in enumerate(rows, start=1):
        row["all_source_id"] = source_id
    public = [row for row in rows if row["visibility"] == "public"]
    private = [row for row in rows if row["visibility"] == "private"]
    for source_id, row in enumerate(public, start=1):
        row["source_id"] = source_id

    all_output = LOGS / "v7_all_source_declarations.tsv"
    all_fields = [
        "all_source_id",
        "module",
        "path",
        "line",
        "keyword",
        "raw_name",
        "visibility",
    ]
    with all_output.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(
            handle, fieldnames=all_fields, delimiter="\t", extrasaction="ignore"
        )
        writer.writeheader()
        writer.writerows(rows)

    output = LOGS / "v7_public_source_declarations.tsv"
    fields = [
        "source_id",
        "module",
        "path",
        "line",
        "keyword",
        "raw_name",
        "visibility",
    ]
    with output.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(
            handle, fieldnames=fields, delimiter="\t", extrasaction="ignore"
        )
        writer.writeheader()
        writer.writerows(public)

    counts = {
        keyword: sum(row["keyword"] == keyword for row in public)
        for keyword in ("theorem", "lemma", "def", "structure", "class")
    }
    private_counts = {
        keyword: sum(row["keyword"] == keyword for row in private)
        for keyword in ("theorem", "lemma", "def", "structure", "class")
    }
    expected = {
        "theorem": 467,
        "lemma": 841,
        "def": 135,
        "structure": 0,
        "class": 0,
    }
    summary = {
        "source_modules": len(paths),
        "public_declarations": len(public),
        "public_counts": counts,
        "private_declarations": len(private),
        "private_counts": private_counts,
        "expected_public_counts": expected,
        "coverage_match": counts == expected and len(public) == 1443,
    }
    (LOGS / "v7_source_inventory_summary.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    (LOGS / "v7_source_inventory_summary.log").write_text(
        "\n".join(
            [
                "V7 PUBLIC SOURCE DECLARATION INVENTORY",
                f"SOURCE_MODULES {len(paths)}",
                f"PUBLIC_DECLARATIONS {len(public)}",
                *(f"PUBLIC_{key.upper()} {value}" for key, value in counts.items()),
                f"PRIVATE_DECLARATIONS {len(private)}",
                *(
                    f"PRIVATE_{key.upper()} {value}"
                    for key, value in private_counts.items()
                ),
                f"COVERAGE_MATCH {str(summary['coverage_match']).lower()}",
                f"VERDICT {'PASS' if summary['coverage_match'] else 'FAIL'}",
                "",
            ]
        ),
        encoding="utf-8",
    )
    if not summary["coverage_match"]:
        raise RuntimeError(f"source inventory coverage mismatch: {summary}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
