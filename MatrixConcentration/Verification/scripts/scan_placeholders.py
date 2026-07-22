#!/usr/bin/env python3
"""V3 calibrated census of sorry-like placeholders and unfinished markers."""

from __future__ import annotations

import argparse
from collections import Counter
import csv
import json
from pathlib import Path
import sys

from lean_source_scan import (
    LOGS,
    ROOT,
    WORK,
    compile_pattern,
    find_hits,
    lean_universe,
    relative,
    tsv_safe,
)


IDENT_LEFT = r"(?<![A-Za-z0-9_'])"
IDENT_RIGHT = r"(?![A-Za-z0-9_'])"
PATTERNS = [
    ("sorryAx", compile_pattern(IDENT_LEFT + r"sorryAx" + IDENT_RIGHT)),
    ("sorry", compile_pattern(IDENT_LEFT + r"sorry" + IDENT_RIGHT)),
    ("admit", compile_pattern(IDENT_LEFT + r"admit" + IDENT_RIGHT)),
    ("proof_wanted", compile_pattern(IDENT_LEFT + r"proof_wanted" + IDENT_RIGHT)),
    ("#exit", compile_pattern(r"(?<![A-Za-z0-9_'])#exit" + IDENT_RIGHT)),
    ("stop", compile_pattern(IDENT_LEFT + r"stop" + IDENT_RIGHT)),
    ("TODO", compile_pattern(IDENT_LEFT + r"TODO" + IDENT_RIGHT, ignore_case=True)),
    ("WIP", compile_pattern(IDENT_LEFT + r"WIP" + IDENT_RIGHT, ignore_case=True)),
]


def classify(pattern: str, context: str) -> str:
    if pattern in {"TODO", "WIP"}:
        return "unfinished_marker" if context != "string" else "textual_mention"
    return "active_construct" if context == "code" else "textual_mention"


def scan(paths: list[Path]) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for hit in find_hits(paths, PATTERNS):
        rows.append(
            {
                "path": relative(hit.path),
                "line": hit.line,
                "column": hit.column,
                "pattern": hit.pattern,
                "matched": hit.matched,
                "context": hit.context,
                "classification": classify(hit.pattern, hit.context),
                "snippet": hit.snippet,
            }
        )
    rows.sort(
        key=lambda row: (
            str(row["path"]),
            int(row["line"]),
            int(row["column"]),
            str(row["pattern"]),
        )
    )
    return rows


def write_tsv(path: Path, rows: list[dict[str, object]]) -> None:
    fields = [
        "path",
        "line",
        "column",
        "pattern",
        "matched",
        "context",
        "classification",
        "snippet",
    ]
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields, delimiter="\t")
        writer.writeheader()
        for row in rows:
            writer.writerow({key: tsv_safe(row[key]) for key in fields})


def production() -> int:
    LOGS.mkdir(parents=True, exist_ok=True)
    paths = lean_universe()
    rows = scan(paths)
    active = [row for row in rows if row["classification"] != "textual_mention"]
    contexts = Counter((str(row["pattern"]), str(row["context"])) for row in rows)
    pattern_active = Counter(str(row["pattern"]) for row in active)

    write_tsv(LOGS / "sorry_audit.tsv", rows)
    result = {
        "universe_definition": (
            "all .lean files physically under the project root, excluding .lake/**, "
            "MatrixConcentration/Verification/**, and .audit_work/**"
        ),
        "universe_count": len(paths),
        "universe": [relative(path) for path in paths],
        "total_textual_hits": len(rows),
        "active_construct_or_marker_hits": len(active),
        "active_counts": {name: pattern_active.get(name, 0) for name, _ in PATTERNS},
        "context_counts": {
            f"{pattern}:{context}": count
            for (pattern, context), count in sorted(contexts.items())
        },
    }
    (LOGS / "sorry_audit.json").write_text(
        json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    with (LOGS / "sorry_audit_summary.txt").open("w", encoding="utf-8") as out:
        out.write("V3 PLACEHOLDER CENSUS\n")
        out.write(f"project_root\t{ROOT}\n")
        out.write(f"universe_files\t{len(paths)}\n")
        for path in paths:
            out.write(f"universe_file\t{relative(path)}\n")
        out.write(f"textual_hits_all_contexts\t{len(rows)}\n")
        out.write(f"active_construct_or_marker_hits\t{len(active)}\n")
        for name, _ in PATTERNS:
            out.write(f"active_{name}\t{pattern_active.get(name, 0)}\n")
        out.write("lexical_contexts\tcode,line_comment,block_comment,doc_comment,string\n")
        out.write("result\t" + ("CLEAN\n" if not active else "HITS_REQUIRE_REVIEW\n"))

    print(f"universe_files={len(paths)}")
    print(f"textual_hits_all_contexts={len(rows)}")
    print(f"active_construct_or_marker_hits={len(active)}")
    print(f"evidence={relative(LOGS / 'sorry_audit.tsv')}")
    return 0 if not active else 1


def calibration() -> int:
    LOGS.mkdir(parents=True, exist_ok=True)
    plant = WORK / "SorryPlant.lean"
    if not plant.is_file():
        print(f"missing calibration plant: {plant}", file=sys.stderr)
        return 2
    rows = scan([plant])
    write_tsv(LOGS / "sorry_text_calibration.tsv", rows)
    active_sorries = [
        row
        for row in rows
        if row["pattern"] == "sorry" and row["classification"] == "active_construct"
    ]
    with (LOGS / "sorry_text_calibration.txt").open("w", encoding="utf-8") as out:
        out.write("V3 TEXTUAL SCANNER CALIBRATION\n")
        out.write(f"plant\t{relative(plant)}\n")
        out.write(f"expected_active_sorry_hits\t2\n")
        out.write(f"observed_active_sorry_hits\t{len(active_sorries)}\n")
        for row in active_sorries:
            out.write(
                f"hit\t{row['path']}:{row['line']}:{row['column']}\t"
                f"{row['snippet']}\n"
            )
        out.write(
            "result\t"
            + ("PASS\n" if len(active_sorries) == 2 else "FAIL\n")
        )
    print(f"expected_active_sorry_hits=2")
    print(f"observed_active_sorry_hits={len(active_sorries)}")
    print(f"evidence={relative(LOGS / 'sorry_text_calibration.tsv')}")
    return 0 if len(active_sorries) == 2 else 1


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "mode",
        choices=("production", "calibration"),
        nargs="?",
        default="production",
    )
    args = parser.parse_args()
    return calibration() if args.mode == "calibration" else production()


if __name__ == "__main__":
    raise SystemExit(main())

