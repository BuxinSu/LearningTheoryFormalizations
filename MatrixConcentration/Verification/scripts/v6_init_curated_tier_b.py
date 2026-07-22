#!/usr/bin/env python3
"""Initialize blank, chapter-sharded V6 Tier-B curation ledgers.

This is deliberately an initializer, not a review generator. It writes only
immutable metadata and refuses to overwrite any existing chapter ledger.
Human reviewers must supply every verdict and checklist field.
"""

from __future__ import annotations

import csv
import sys
from pathlib import Path


SCRIPT = Path(__file__).resolve()
VERIFICATION = SCRIPT.parent.parent
LOGS = VERIFICATION / "logs"
CURATION = VERIFICATION / "curation"
ROWS = LOGS / "v6_correspondence_rows.tsv"
ENDPOINTS = LOGS / "v6_endpoint_telescopes.tsv"

FIELDS = [
    "global_row",
    "chapter",
    "chapter_row",
    "readme_line",
    "book_source",
    "declaration",
    "endpoint_kind",
    "verdict",
    "check1_model",
    "check2_nontrivial",
    "check3_typeclasses",
    "check4_quantifiers",
    "adjudication",
    "evidence_refs",
]


def read(path: Path) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as handle:
        return list(csv.DictReader(handle, delimiter="\t"))


def main() -> int:
    rows = read(ROWS)
    endpoints = {row["global_row"]: row for row in read(ENDPOINTS)}
    if len(rows) != 467 or len(endpoints) != 467:
        raise RuntimeError("fixed inputs must both contain exactly 467 rows")
    CURATION.mkdir(parents=True, exist_ok=True)
    existing = [
        CURATION / f"v6_tier_b_chapter_{chapter}.tsv"
        for chapter in range(1, 9)
        if (CURATION / f"v6_tier_b_chapter_{chapter}.tsv").exists()
    ]
    if existing:
        print("REFUSING TO OVERWRITE CURATED FILES", file=sys.stderr)
        for path in existing:
            print(path, file=sys.stderr)
        return 1
    for chapter in range(1, 9):
        output = CURATION / f"v6_tier_b_chapter_{chapter}.tsv"
        chapter_rows: list[dict[str, str]] = []
        for row in rows:
            if int(row["chapter"]) != chapter:
                continue
            endpoint = endpoints[row["global_row"]]
            if endpoint["readme_name"] != row["declaration"]:
                raise RuntimeError(
                    f"endpoint mismatch at global row {row['global_row']}"
                )
            chapter_rows.append(
                {
                    "global_row": row["global_row"],
                    "chapter": row["chapter"],
                    "chapter_row": row["chapter_row"],
                    "readme_line": row["readme_line"],
                    "book_source": row["book_source"],
                    "declaration": row["declaration"],
                    "endpoint_kind": endpoint["kind"],
                    "verdict": "",
                    "check1_model": "",
                    "check2_nontrivial": "",
                    "check3_typeclasses": "",
                    "check4_quantifiers": "",
                    "adjudication": "",
                    "evidence_refs": "",
                }
            )
        with output.open("w", newline="", encoding="utf-8") as handle:
            writer = csv.DictWriter(
                handle, fieldnames=FIELDS, delimiter="\t", lineterminator="\n"
            )
            writer.writeheader()
            writer.writerows(chapter_rows)
        print(f"CREATED {output.relative_to(VERIFICATION)} rows={len(chapter_rows)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
