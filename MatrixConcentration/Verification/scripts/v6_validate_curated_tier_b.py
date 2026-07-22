#!/usr/bin/env python3
"""Independent structural validation for the curated V6 Tier-B merge."""

from __future__ import annotations

import csv
import json
import sys
from collections import Counter
from pathlib import Path

import v6_merge_curated_tier_b as merger


SCRIPT = Path(__file__).resolve()
VERIFICATION = SCRIPT.parent.parent
LOGS = VERIFICATION / "logs"
REVIEW = LOGS / "v6_tier_b_review.tsv"
OUTPUT_JSON = LOGS / "v6_tier_b_note_validation.json"
OUTPUT_LOG = LOGS / "v6_tier_b_note_validation.log"


def read(path: Path) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as handle:
        return list(csv.DictReader(handle, delimiter="\t"))


def main() -> int:
    errors: list[str] = []
    rows = read(REVIEW)
    if len(rows) != 467:
        errors.append(f"merged review has {len(rows)} rows, expected 467")
    chapters = Counter(row["chapter"] for row in rows)
    if chapters != Counter(merger.EXPECTED):
        errors.append(f"chapter counts drift: {dict(chapters)}")
    kinds = Counter(row["endpoint_kind"] for row in rows)
    if kinds != Counter({"theorem": 401, "definition": 66}):
        errors.append(f"endpoint-kind counts drift: {dict(kinds)}")
    verdicts = Counter(row["verdict"] for row in rows)
    if verdicts != merger.EXPECTED_VERDICTS:
        errors.append(f"verdict counts drift: {dict(verdicts)}")
    if any(row["verdict"] not in merger.VERDICTS for row in rows):
        errors.append("merged review contains an invalid verdict")

    rationale_tuples: set[tuple[str, ...]] = set()
    for row in rows:
        values = tuple(row[field].strip() for field in merger.CHECKLIST)
        if any(len(value) < 35 for value in values):
            errors.append(f"{row['declaration']}: short checklist cell")
        if values in rationale_tuples:
            errors.append(
                f"{row['declaration']}: duplicated four-cell checklist tuple"
            )
        rationale_tuples.add(values)
        expected_fragments = [
            f"(1) {values[0]}",
            f"(2) {values[1]}",
            f"(3) {values[2]}",
            f"(4) {values[3]}",
            f"Adjudication: {row['adjudication']}",
            f"Evidence: {row['evidence_refs']}",
        ]
        if any(fragment not in row["justification"] for fragment in expected_fragments):
            errors.append(
                f"{row['declaration']}: merged justification does not preserve "
                "all curated fields verbatim"
            )
        for phrase in merger.LEGACY_GENERIC_PHRASES:
            if phrase.casefold() in row["justification"].casefold():
                errors.append(
                    f"{row['declaration']}: legacy generated phrase survives"
                )
        errors.extend(
            merger.validate_source_reference(
                row["declaration"], row["evidence_refs"]
            )
        )

    by_name = {row["declaration"]: row for row in rows}
    for name, anchors in merger.REQUIRED_BOUNDARY_ROWS.items():
        row = by_name.get(name)
        if row is None:
            errors.append(f"required boundary row missing: {name}")
            continue
        combined = " ".join(
            [
                row["check2_nontrivial"],
                row["adjudication"],
                row["evidence_refs"],
            ]
        ).casefold()
        if not any(anchor.casefold() in combined for anchor in anchors):
            errors.append(
                f"{name}: boundary anchors absent; expected one of {anchors}"
            )

    status = "PASS" if not errors else "FAIL"
    result = {
        "status": status,
        "rows": len(rows),
        "chapter_counts": dict(sorted(chapters.items())),
        "endpoint_kind_counts": dict(sorted(kinds.items())),
        "verdict_counts": dict(sorted(verdicts.items())),
        "distinct_four_cell_rationales": len(rationale_tuples),
        "required_boundary_rows": sorted(merger.REQUIRED_BOUNDARY_ROWS),
        "errors": errors,
    }
    OUTPUT_JSON.write_text(
        json.dumps(result, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    lines = [
        "V6 CURATED TIER-B INDEPENDENT VALIDATION",
        f"STATUS {status}",
        f"ROWS {len(rows)}",
        f"DISTINCT_FOUR_CELL_RATIONALES {len(rationale_tuples)}",
        f"REQUIRED_BOUNDARY_ROWS {len(merger.REQUIRED_BOUNDARY_ROWS)}",
        f"ERRORS {len(errors)}",
        *(f"ERROR {error}" for error in errors),
    ]
    OUTPUT_LOG.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print("\n".join(lines))
    return 0 if status == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
