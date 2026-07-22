#!/usr/bin/env python3
"""Initialize the dynamic Tier-C evidence manifest from current obligations.

The initializer writes immutable obligation metadata only and refuses to
overwrite an existing evidence manifest. Evidence choices remain manual.
"""

from __future__ import annotations

import csv
import sys
from pathlib import Path


SCRIPT = Path(__file__).resolve()
VERIFICATION = SCRIPT.parent.parent
LOGS = VERIFICATION / "logs"
OUTPUT = VERIFICATION / "curation" / "v6_tier_c_evidence.tsv"
SAMPLE = LOGS / "v6_tier_c_sample.tsv"
TIER_B = LOGS / "v6_tier_b_review.tsv"

FIELDS = [
    "global_row",
    "chapter",
    "chapter_row",
    "declaration",
    "endpoint_kind",
    "tier_b_verdict",
    "obligation_kind",
    "evidence_method",
    "evidence_names",
    "premise_class",
    "substantive_premises",
    "model_names",
    "discharge_detail",
    "application_site",
]


def read(path: Path) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as handle:
        return list(csv.DictReader(handle, delimiter="\t"))


def obligation_metadata(
    row: dict[str, str],
    obligation_kind: str,
) -> dict[str, str]:
    """Map the Tier-B ledger schema into immutable Tier-C metadata."""
    return {
        "global_row": row["global_row"],
        "chapter": row["chapter"],
        "chapter_row": row["chapter_row"],
        "declaration": row["declaration"],
        "endpoint_kind": row["endpoint_kind"],
        "tier_b_verdict": row["verdict"],
        "obligation_kind": obligation_kind,
    }


def main() -> int:
    if OUTPUT.exists():
        print(f"REFUSING TO OVERWRITE {OUTPUT}", file=sys.stderr)
        return 1
    tier_b = read(TIER_B)
    by_global = {row["global_row"]: row for row in tier_b}
    obligations: list[dict[str, str]] = []
    for sample in read(SAMPLE):
        row = by_global[sample["global_row"]]
        if row["verdict"] != "OK":
            raise RuntimeError(
                f"sample row {row['global_row']} is no longer Tier-B OK"
            )
        obligations.append(
            obligation_metadata(row, "sampled_OK")
        )
    for row in tier_b:
        if row["verdict"] in {"SUSPECT", "VACUOUS"}:
            obligations.append(
                obligation_metadata(row, f"TierB_{row['verdict']}")
            )
    if len({row["global_row"] for row in obligations}) != len(obligations):
        raise RuntimeError("dynamic Tier-C obligations contain duplicate rows")
    blank = {field: "" for field in FIELDS[7:]}
    with OUTPUT.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(
            handle, fieldnames=FIELDS, delimiter="\t", lineterminator="\n"
        )
        writer.writeheader()
        for row in obligations:
            writer.writerow({**row, **blank})
    print(f"CREATED {OUTPUT.relative_to(VERIFICATION)}")
    print(f"SAMPLED_OK {sum(r['obligation_kind'] == 'sampled_OK' for r in obligations)}")
    print(f"SUSPECT {sum(r['obligation_kind'] == 'TierB_SUSPECT' for r in obligations)}")
    print(f"VACUOUS {sum(r['obligation_kind'] == 'TierB_VACUOUS' for r in obligations)}")
    print(f"TOTAL {len(obligations)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
