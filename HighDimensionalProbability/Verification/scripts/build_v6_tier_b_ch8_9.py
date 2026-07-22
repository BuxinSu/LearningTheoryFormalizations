#!/usr/bin/env python3
"""Deterministically validate/canonicalize the V6 Tier-B Chapters 8--9 ledger.

This is a static checker.  It reads frozen inventories and source text only;
it never invokes Lean, Lake, Git, or a network tool.  The TSV is the reviewed
evidence record.  The checker reconstructs its canonical TSV serialization,
checks it byte-for-byte and by SHA-256, and verifies exact inventory coverage.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import io
import json
from collections import Counter
from pathlib import Path

import build_v6_tier_b_ch0_4 as common


PROJECT = Path(__file__).resolve().parents[3]
VERIFICATION = PROJECT / "HighDimensionalProbability" / "Verification"
INVENTORY = VERIFICATION / "inventory"
OUTPUT = VERIFICATION / "review" / "v6_tier_b_ch8_9.tsv"
SUMMARY = VERIFICATION / "review" / "v6_tier_b_ch8_9_summary.txt"

EXPECTED_SHA256 = "15dd44a07ad8187f38917ce562b6a869a9a71165f76d25aaed96b3e0e9b5476e"
EXPECTED_ROW_COUNT = 177
EXPECTED_ENDPOINT_COUNT = 181

FIELDS = (
    "row_set",
    "sample_kind",
    "sample_rank",
    "row_id",
    "chapter",
    "book_label",
    "resolved_declarations",
    "verdict",
    "joint_satisfiability",
    "nontrivial_conclusion",
    "typeclass_nondegeneracy",
    "quantifier_usability",
    "justification",
    "witness_by_citation_candidate",
    "source_locations",
    "tier_c_required",
)

ALLOWED = {"OK", "SUSPECT", "VACUOUS"}


def read_tsv(path: Path) -> tuple[list[str], list[dict[str, str]]]:
    with path.open(encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle, delimiter="\t")
        rows = list(reader)
        return list(reader.fieldnames or ()), rows


def canonical_bytes(rows: list[dict[str, str]]) -> bytes:
    buffer = io.StringIO(newline="")
    writer = csv.DictWriter(
        buffer,
        fieldnames=FIELDS,
        delimiter="\t",
        lineterminator="\n",
        quoting=csv.QUOTE_MINIMAL,
    )
    writer.writeheader()
    writer.writerows(rows)
    return buffer.getvalue().encode("utf-8")


def refresh_current_rows(rows: list[dict[str, str]]) -> list[dict[str, str]]:
    """Reanchor preserved judgments without changing their semantic fields."""

    source_index = common.build_source_index()
    refreshed: list[dict[str, str]] = []
    allowed_changes = {
        "witness_by_citation_candidate",
        "source_locations",
    }
    for old in rows:
        row = dict(old)
        endpoints = row["resolved_declarations"].split(";")
        old_locations = row["source_locations"].split("; ")
        if len(endpoints) != len(old_locations):
            raise AssertionError(
                f"endpoint/location arity mismatch: {row['row_id']}"
            )
        new_locations: list[str] = []
        for endpoint, old_location in zip(endpoints, old_locations, strict=True):
            path, line, _kind = common.resolve_endpoint(endpoint, source_index)
            new_location = f"{path}:{line}"
            new_locations.append(new_location)
            row["witness_by_citation_candidate"] = row[
                "witness_by_citation_candidate"
            ].replace(old_location, new_location)
        row["source_locations"] = "; ".join(new_locations)
        changed = {
            field for field in FIELDS if row[field] != old[field]
        }
        if changed - allowed_changes:
            raise AssertionError(
                f"semantic field changed while reanchoring {row['row_id']}: "
                f"{sorted(changed - allowed_changes)}"
            )
        refreshed.append(row)
    return refreshed


def source_line(location: str) -> str:
    path_text, line_text = location.rsplit(":", 1)
    path = PROJECT / path_text
    if not path.is_file():
        raise AssertionError(f"missing source path: {path_text}")
    line_number = int(line_text)
    lines = path.read_text(encoding="utf-8").splitlines()
    if not 1 <= line_number <= len(lines):
        raise AssertionError(f"source line out of range: {location}")
    return lines[line_number - 1]


def validate(rows: list[dict[str, str]], raw: bytes) -> None:
    if len(rows) != EXPECTED_ROW_COUNT:
        raise AssertionError(f"expected {EXPECTED_ROW_COUNT} rows, found {len(rows)}")
    if len({row["row_id"] for row in rows}) != len(rows):
        raise AssertionError("duplicate row_id")
    if canonical_bytes(rows) != raw:
        raise AssertionError("TSV is not its canonical byte-for-byte serialization")
    digest = hashlib.sha256(raw).hexdigest()
    if digest != EXPECTED_SHA256:
        raise AssertionError(f"SHA-256 mismatch: {digest}")

    row_sets = Counter(row["row_set"] for row in rows)
    if row_sets != Counter(
        {"readme_correspondence": 161, "exercise_leaf_sample": 6,
         "ok_review_queue_head": 10}
    ):
        raise AssertionError(f"unexpected row-set counts: {row_sets}")
    chapters = Counter(row["chapter"] for row in rows)
    if chapters != Counter({"Chapter 8": 108, "Chapter 9": 69}):
        raise AssertionError(f"unexpected chapter counts: {chapters}")

    _, readme_rows = read_tsv(INVENTORY / "readme_correspondence.tsv")
    readme_rows = [
        row for row in readme_rows
        if row["chapter"] in {"Chapter 8", "Chapter 9"}
    ]
    readme_by_id = {row["row_id"]: row for row in readme_rows}

    _, plan_rows = read_tsv(INVENTORY / "sampling_plan.tsv")
    plan_rows = [
        row for row in plan_rows
        if row["chapter"] in {"Chapter 8", "Chapter 9"}
        and row["sample_kind"] in
        {"exercise_leaf_close_read", "ok_review_queue_head"}
    ]
    plan_by_id = {row["target_id"]: row for row in plan_rows}

    got_readme = {
        row["row_id"] for row in rows
        if row["row_set"] == "readme_correspondence"
    }
    if got_readme != set(readme_by_id):
        raise AssertionError("README row-ID set is not exact")
    got_samples = {
        row["row_id"] for row in rows
        if row["row_set"] != "readme_correspondence"
    }
    if got_samples != set(plan_by_id):
        raise AssertionError("sampling-plan target-ID set is not exact")

    endpoint_count = 0
    for row in rows:
        if row["verdict"] not in ALLOWED:
            raise AssertionError(f"bad verdict: {row['row_id']}")
        for field in (
            "joint_satisfiability",
            "nontrivial_conclusion",
            "typeclass_nondegeneracy",
            "quantifier_usability",
        ):
            if row[field] not in ALLOWED:
                raise AssertionError(f"bad {field}: {row['row_id']}")
        for tag in ("H(", "C(", "T(", "Q("):
            if tag not in row["justification"]:
                raise AssertionError(f"missing {tag}: {row['row_id']}")
        for tag in ("D(", "S("):
            if tag not in row["witness_by_citation_candidate"]:
                raise AssertionError(f"missing {tag}: {row['row_id']}")

        endpoints = row["resolved_declarations"].split(";")
        locations = row["source_locations"].split("; ")
        if len(endpoints) != len(locations):
            raise AssertionError(f"endpoint/location arity mismatch: {row['row_id']}")
        endpoint_count += len(endpoints)
        for endpoint, location in zip(endpoints, locations):
            if endpoint.rsplit(".", 1)[-1] not in source_line(location):
                raise AssertionError(
                    f"endpoint not declared at source location: {endpoint} {location}"
                )

        if row["row_set"] == "readme_correspondence":
            expected = json.loads(readme_by_id[row["row_id"]]["endpoint_names"])
            if endpoints != expected:
                raise AssertionError(f"README endpoint mismatch: {row['row_id']}")
            if row["sample_kind"] or row["sample_rank"]:
                raise AssertionError(f"README row has sample provenance: {row['row_id']}")
        else:
            plan = plan_by_id[row["row_id"]]
            if endpoints != [plan["endpoint"]]:
                raise AssertionError(f"sample endpoint mismatch: {row['row_id']}")
            if (
                row["sample_kind"] != plan["sample_kind"]
                or row["sample_rank"] != plan["rank"]
                or row["chapter"] != plan["chapter"]
            ):
                raise AssertionError(f"sample provenance mismatch: {row['row_id']}")

        tier_c = row["tier_c_required"].startswith("YES")
        if tier_c != (row["row_set"] == "ok_review_queue_head"):
            raise AssertionError(f"Tier-C marker mismatch: {row['row_id']}")

    if endpoint_count != EXPECTED_ENDPOINT_COUNT:
        raise AssertionError(
            f"expected {EXPECTED_ENDPOINT_COUNT} endpoints, found {endpoint_count}"
        )
    if Counter(row["verdict"] for row in rows) != Counter({"OK": 177}):
        raise AssertionError("verdict census changed")


def validate_summary() -> None:
    text = SUMMARY.read_text(encoding="utf-8")
    required = (
        f"tsv_sha256: {EXPECTED_SHA256}",
        "matched SHA-256 " + EXPECTED_SHA256 + ".",
        "MajorizingMeasureLowerPrinciple is declared in "
        "HighDimensionalProbability/Chapter8_Chaining.lean:21395.",
    )
    missing = [fragment for fragment in required if fragment not in text]
    if missing:
        raise AssertionError(
            "Chapters 8--9 review summary is stale: " + ", ".join(missing)
        )


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--check", action="store_true", help="validate only (default)")
    mode.add_argument(
        "--write",
        action="store_true",
        help="mechanically reanchor preserved judgments to current source",
    )
    args = parser.parse_args()

    common.require_round10_source_identity()

    header, rows = read_tsv(OUTPUT)
    if tuple(header) != FIELDS:
        raise AssertionError(f"schema mismatch: {header}")
    if args.write:
        rows = refresh_current_rows(rows)
        rendered = canonical_bytes(rows)
        digest = hashlib.sha256(rendered).hexdigest()
        if digest != EXPECTED_SHA256:
            raise AssertionError(
                "current reanchor SHA-256 mismatch before write: "
                f"{digest}"
            )
        OUTPUT.write_bytes(rendered)
    raw = OUTPUT.read_bytes()
    validate(rows, raw)
    validate_summary()
    print(
        "PASS v6_tier_b_ch8_9: "
        "177 rows; 181 endpoints; exact inventory/sample coverage; "
        f"sha256={EXPECTED_SHA256}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
