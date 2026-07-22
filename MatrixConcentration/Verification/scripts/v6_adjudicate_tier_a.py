#!/usr/bin/env python3
"""Validate and record human adjudication of the calibrated Tier-A hit set."""

from __future__ import annotations

import csv
import sys
from pathlib import Path


SCRIPT = Path(__file__).resolve()
VERIFICATION = SCRIPT.parent.parent
LOGS = VERIFICATION / "logs"
HITS = LOGS / "v6_tier_a_hits.tsv"
OUTPUT = LOGS / "v6_tier_a_adjudication.tsv"
RUN_LOG = LOGS / "v6_tier_a_adjudication.log"


ADJUDICATION = {
    "lambdaMax_of_isEmpty": {
        "classification": "DELIBERATE-BOUNDARY-HELPER",
        "tier_b_followup": "lambdaMax correspondence definition marked SUSPECT",
        "justification": (
            "This lemma documents the definition's explicit empty-dimension "
            "sentinel. Nonempty spectral uses are substantive; the boundary and "
            "a nonzero Fin-2 model are both compiled in V6Witnesses."
        ),
    },
    "lambdaMin_of_isEmpty": {
        "classification": "DELIBERATE-BOUNDARY-HELPER",
        "tier_b_followup": "lambdaMin correspondence definition marked SUSPECT",
        "justification": (
            "This lemma documents the definition's explicit empty-dimension "
            "sentinel. Nonempty spectral uses are substantive; the boundary and "
            "a nonzero Fin-2 model are both compiled in V6Witnesses."
        ),
    },
    "matrix_rosenthal_pinelis_symmetric_empty_index": {
        "classification": "DELIBERATE-EMPTY-BRANCH-HELPER",
        "tier_b_followup": "not a correspondence endpoint",
        "justification": (
            "This is the named empty-index branch used by the general "
            "Rosenthal–Pinelis assembly (direct source calls at lines 2275 and "
            "3000). It is not catalogued as a main theorem and does not empty "
            "the nonempty branch."
        ),
    },
}


def main() -> int:
    with HITS.open(newline="", encoding="utf-8") as handle:
        hits = list(csv.DictReader(handle, delimiter="\t"))
    actual = {row["name"] for row in hits}
    expected = set(ADJUDICATION)
    errors: list[str] = []
    if actual != expected:
        errors.append(
            f"Tier-A hit-set drift: missing={sorted(expected - actual)}, "
            f"unexpected={sorted(actual - expected)}"
        )
    if len(hits) != len(actual):
        errors.append("Tier-A hit ledger contains duplicate declaration names")

    rows: list[dict[str, str]] = []
    for hit in hits:
        decision = ADJUDICATION.get(
            hit["name"],
            {
                "classification": "UNADJUDICATED",
                "tier_b_followup": "required",
                "justification": "No fixed adjudication exists for this hit.",
            },
        )
        rows.append(
            {
                "path": hit["path"],
                "line": hit["line"],
                "name": hit["name"],
                "flags": hit["flags"],
                **decision,
                "finding": "NONE" if hit["name"] in ADJUDICATION else "REQUIRED",
            }
        )

    fields = [
        "path",
        "line",
        "name",
        "flags",
        "classification",
        "tier_b_followup",
        "justification",
        "finding",
    ]
    with OUTPUT.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(
            handle, fieldnames=fields, delimiter="\t", lineterminator="\n"
        )
        writer.writeheader()
        writer.writerows(rows)

    status = "PASS" if not errors else "FAIL"
    lines = [
        "command: python3 MatrixConcentration/Verification/scripts/"
        "v6_adjudicate_tier_a.py",
        f"status: {status}",
        f"tier_a_hits: {len(hits)}",
        f"adjudicated: {sum(row['finding'] == 'NONE' for row in rows)}",
        f"findings_required: {sum(row['finding'] == 'REQUIRED' for row in rows)}",
    ]
    lines.extend(f"ERROR: {error}" for error in errors)
    RUN_LOG.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print("\n".join(lines))
    return 0 if status == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
