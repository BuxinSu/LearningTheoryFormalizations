#!/usr/bin/env python3
"""Stratified reproducible sample of five Tier-B OK rows per chapter."""

from __future__ import annotations

import csv
import random
import re
from pathlib import Path


SCRIPT = Path(__file__).resolve()
VERIFY = SCRIPT.parent.parent
LOGS = VERIFY / "logs"
REVIEW = LOGS / "v6_tier_b_review.tsv"
SOURCE_MANIFEST = LOGS / "source_manifest.txt"


def source_manifest_seed() -> str:
    """Use the certified source snapshot digest as the sampling seed."""

    text = SOURCE_MANIFEST.read_text(encoding="utf-8")
    match = re.search(
        r"(?m)^TOP_LEVEL_SHA256\s+([0-9a-f]{64})\s*$",
        text,
    )
    if match is None:
        raise RuntimeError(
            "source manifest lacks a valid TOP_LEVEL_SHA256 sampling seed"
        )
    return match.group(1)


def main() -> int:
    seed = source_manifest_seed()
    with REVIEW.open(encoding="utf-8", newline="") as handle:
        rows = list(csv.DictReader(handle, delimiter="\t"))
    samples: list[dict[str, str]] = []
    lines = [
        "V6 TIER C REPRODUCIBLE OK-ROW SAMPLE",
        f"SEED {seed}",
        "ALGORITHM for each chapter, preserve README order; eligible rows have "
        "Tier-B verdict OK. If the chapter has OK definitions, select one "
        "definition with the chapter RNG, then sample four rows from all "
        "remaining OK rows; otherwise sample five OK theorems. This visibly "
        "exercises definition evidence while retaining randomized coverage.",
    ]
    for chapter in range(1, 9):
        eligible = [
            row
            for row in rows
            if int(row["chapter"]) == chapter
            and row["verdict"] == "OK"
        ]
        if len(eligible) < 5:
            raise RuntimeError(
                f"chapter {chapter}: only {len(eligible)} eligible OK rows"
            )
        rng = random.Random(f"{seed}:ch{chapter}")
        definitions = [
            row for row in eligible if row["endpoint_kind"] == "definition"
        ]
        if definitions:
            selected_definition = rng.choice(definitions)
            remainder = [
                row
                for row in eligible
                if row["global_row"] != selected_definition["global_row"]
            ]
            selected = [selected_definition, *rng.sample(remainder, 4)]
        else:
            selected = rng.sample(eligible, 5)
        lines.append(f"CHAPTER_{chapter}_ELIGIBLE {len(eligible)}")
        lines.append(
            f"CHAPTER_{chapter}_ELIGIBLE_DEFINITIONS {len(definitions)}"
        )
        for index, row in enumerate(selected, start=1):
            samples.append(
                {
                    "chapter": str(chapter),
                    "sample_index": str(index),
                    "global_row": row["global_row"],
                    "chapter_row": row["chapter_row"],
                    "declaration": row["declaration"],
                    "endpoint_kind": row["endpoint_kind"],
                    "tier_b_verdict": row["verdict"],
                }
            )
            lines.append(
                f"CHAPTER_{chapter}_SAMPLE_{index} "
                f"row={row['chapter_row']} kind={row['endpoint_kind']} "
                f"declaration={row['declaration']}"
            )
    fields = [
        "chapter",
        "sample_index",
        "global_row",
        "chapter_row",
        "declaration",
        "endpoint_kind",
        "tier_b_verdict",
    ]
    with (LOGS / "v6_tier_c_sample.tsv").open(
        "w", encoding="utf-8", newline=""
    ) as handle:
        writer = csv.DictWriter(handle, delimiter="\t", fieldnames=fields)
        writer.writeheader()
        writer.writerows(samples)
    valid = (
        len(samples) == 40
        and all(row["tier_b_verdict"] == "OK" for row in samples)
        and all(
            not any(
                row["chapter"] == str(chapter)
                and row["verdict"] == "OK"
                and row["endpoint_kind"] == "definition"
                for row in rows
            )
            or any(
                row["chapter"] == str(chapter)
                and row["endpoint_kind"] == "definition"
                for row in samples
            )
            for chapter in range(1, 9)
        )
    )
    lines.extend([f"TOTAL_SAMPLED {len(samples)}", f"VERDICT {'PASS' if valid else 'FAIL'}"])
    (LOGS / "v6_tier_c_sampling.log").write_text(
        "\n".join(lines) + "\n", encoding="utf-8"
    )
    print("\n".join(lines))
    return 0 if valid else 1


if __name__ == "__main__":
    raise SystemExit(main())
