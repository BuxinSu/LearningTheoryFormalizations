#!/usr/bin/env python3
"""Validate/canonicalize the endpoint-only V6 supplement for Chapters 8--9.

Selection is exact: endpoint_union rows whose source_kinds JSON value is
exactly ["review_census_direct"], whose chapters include Chapter 8 or 9, and
whose endpoint is absent from the 177-row main ledger.  This static checker
never invokes Lean, Lake, Git, or the network.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import io
import json
from collections import Counter
from pathlib import Path

import build_v6_tier_b_supplement_ch0_4 as common


PROJECT = Path(__file__).resolve().parents[3]
VERIFICATION = PROJECT / "HighDimensionalProbability" / "Verification"
INVENTORY = VERIFICATION / "inventory"
REVIEW = VERIFICATION / "review"
MAIN = REVIEW / "v6_tier_b_ch8_9.tsv"
OUTPUT = REVIEW / "v6_tier_b_supplement_ch8_9.tsv"
SUMMARY = REVIEW / "v6_tier_b_supplement_ch8_9_summary.txt"

EXPECTED_SHA256 = "195a8cd1951c418e3f228e23bfa6cc45ba81a25a68e560faedc31a5c4203e660"
EXPECTED_ROW_COUNT = 53

FIELDS = (
    "row_id",
    "endpoint",
    "chapters",
    "source_row_ids",
    "book_refs",
    "source_kinds",
    "resolution_status",
    "declaration_kind",
    "source_location",
    "status",
    "joint_satisfiability",
    "nontrivial_conclusion",
    "typeclass_nondegeneracy",
    "quantifier_usability",
    "justification",
    "dependency_path",
    "witness_by_citation_candidate",
    "v9_stale_claim",
    "v9_mismatched_claim",
    "v9_note",
)

ALLOWED = {"OK", "SUSPECT", "VACUOUS"}
EXPECTED_SUSPECT: set[str] = set()
EXPECTED_STALE: set[str] = set()


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


def selected_inventory(main_endpoints: set[str]) -> list[dict[str, str]]:
    _, inventory_rows = read_tsv(INVENTORY / "endpoint_union.tsv")
    return [
        row for row in inventory_rows
        if json.loads(row["source_kinds"]) == ["review_census_direct"]
        and any(
            chapter in {"Chapter 8", "Chapter 9"}
            for chapter in json.loads(row["chapters"])
        )
        and row["endpoint"] not in main_endpoints
    ]


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


def stable_id(endpoint: str) -> str:
    return "supp-" + hashlib.sha256(endpoint.encode("utf-8")).hexdigest()[:16]


def refresh_current_rows(rows: list[dict[str, str]]) -> list[dict[str, str]]:
    """Preserve reviewed evidence while projecting it to current endpoints."""

    _, main_rows = read_tsv(MAIN)
    main_endpoints: set[str] = set()
    for row in main_rows:
        main_endpoints.update(row["resolved_declarations"].split(";"))
    inventory_rows = selected_inventory(main_endpoints)
    old_by_endpoint = {row["endpoint"]: row for row in rows}
    missing_review = sorted(
        row["endpoint"]
        for row in inventory_rows
        if row["endpoint"] not in old_by_endpoint
    )
    if missing_review:
        raise AssertionError(
            f"current selection lacks reviewed evidence: {missing_review}"
        )

    source_index = common.build_source_index()
    refreshed: list[dict[str, str]] = []
    for inventory in inventory_rows:
        endpoint = inventory["endpoint"]
        row = dict(old_by_endpoint[endpoint])
        row["chapters"] = ";".join(json.loads(inventory["chapters"]))
        row["source_row_ids"] = ";".join(
            json.loads(inventory["source_row_ids"])
        )
        row["book_refs"] = ";".join(json.loads(inventory["book_refs"]))
        row["source_kinds"] = "review_census_direct"

        resolution = common.resolve_endpoint(endpoint, source_index)
        if resolution is None:
            raise AssertionError(
                f"current endpoint does not resolve in source: {endpoint}"
            )
        path_text, line, kind = resolution
        old_location = row["source_location"]
        new_location = f"{path_text}:{line}"
        row["resolution_status"] = "RESOLVED"
        row["declaration_kind"] = kind
        row["source_location"] = new_location
        row["witness_by_citation_candidate"] = row[
            "witness_by_citation_candidate"
        ].replace(old_location, new_location)

        if endpoint == (
            "HDP.Chapter8.exercise_8_39b_"
            "gaussian_chevet_reverse_arbitrary"
        ):
            row["v9_stale_claim"] = "NO"
            row["v9_note"] = (
                "The current census narrows the retained conclusion to "
                "Exercise 8.39(b), matching this unconditional core-proved "
                "endpoint."
            )
        refreshed.append(row)
    return refreshed


def validate(rows: list[dict[str, str]], raw: bytes) -> None:
    if len(rows) != EXPECTED_ROW_COUNT:
        raise AssertionError(f"expected {EXPECTED_ROW_COUNT} rows, found {len(rows)}")
    if len({row["row_id"] for row in rows}) != len(rows):
        raise AssertionError("duplicate row_id")
    if len({row["endpoint"] for row in rows}) != len(rows):
        raise AssertionError("duplicate endpoint")
    if canonical_bytes(rows) != raw:
        raise AssertionError("TSV is not its canonical byte-for-byte serialization")
    digest = hashlib.sha256(raw).hexdigest()
    if EXPECTED_SHA256 and digest != EXPECTED_SHA256:
        raise AssertionError(f"SHA-256 mismatch: {digest}")

    _, main_rows = read_tsv(MAIN)
    main_endpoints: set[str] = set()
    for row in main_rows:
        main_endpoints.update(row["resolved_declarations"].split(";"))
    expected = selected_inventory(main_endpoints)
    expected_by_endpoint = {row["endpoint"]: row for row in expected}

    actual_endpoints = {row["endpoint"] for row in rows}
    if actual_endpoints != set(expected_by_endpoint):
        missing = sorted(set(expected_by_endpoint) - actual_endpoints)
        extra = sorted(actual_endpoints - set(expected_by_endpoint))
        raise AssertionError(f"non-exact supplemental set; missing={missing}; extra={extra}")
    if actual_endpoints & main_endpoints:
        raise AssertionError("supplement overlaps main-ledger endpoints")
    if [row["endpoint"] for row in rows] != [row["endpoint"] for row in expected]:
        raise AssertionError("supplement is not in deterministic endpoint_inventory order")

    source_index = common.build_source_index()
    for row in rows:
        endpoint = row["endpoint"]
        inventory = expected_by_endpoint[endpoint]
        if row["row_id"] != stable_id(endpoint):
            raise AssertionError(f"unstable row ID: {endpoint}")
        expected_cells = {
            "chapters": ";".join(json.loads(inventory["chapters"])),
            "source_row_ids": ";".join(json.loads(inventory["source_row_ids"])),
            "book_refs": ";".join(json.loads(inventory["book_refs"])),
            "source_kinds": "review_census_direct",
        }
        for field, value in expected_cells.items():
            if row[field] != value:
                raise AssertionError(f"inventory metadata mismatch {field}: {endpoint}")

        if row["resolution_status"] != "RESOLVED":
            raise AssertionError(f"unresolved declaration location: {endpoint}")
        if row["declaration_kind"] not in {"theorem", "lemma", "def", "class"}:
            raise AssertionError(f"bad declaration kind: {endpoint}")
        line = source_line(row["source_location"])
        short_name = endpoint.rsplit(".", 1)[-1]
        if short_name not in line or row["declaration_kind"] not in line:
            raise AssertionError(
                f"declaration mismatch at {row['source_location']}: {endpoint}"
            )
        resolution = common.resolve_endpoint(endpoint, source_index)
        expected_resolution = (
            row["source_location"].rsplit(":", 1)[0],
            int(row["source_location"].rsplit(":", 1)[1]),
            row["declaration_kind"],
        )
        if resolution != expected_resolution:
            raise AssertionError(
                f"source anchor is not the mechanically resolved declaration: "
                f"{endpoint}: {expected_resolution} != {resolution}"
            )

        if row["status"] not in ALLOWED:
            raise AssertionError(f"bad status: {endpoint}")
        for field in (
            "joint_satisfiability",
            "nontrivial_conclusion",
            "typeclass_nondegeneracy",
            "quantifier_usability",
        ):
            if row[field] not in ALLOWED:
                raise AssertionError(f"bad {field}: {endpoint}")
        for tag in ("H(", "C(", "T(", "Q("):
            if tag not in row["justification"]:
                raise AssertionError(f"missing {tag}: {endpoint}")
        for tag in ("D(", "S("):
            if tag not in row["witness_by_citation_candidate"]:
                raise AssertionError(f"missing {tag}: {endpoint}")
        if not row["dependency_path"]:
            raise AssertionError(f"missing dependency path: {endpoint}")
        for field in ("v9_stale_claim", "v9_mismatched_claim"):
            if row[field] not in {"YES", "NO"}:
                raise AssertionError(f"bad {field}: {endpoint}")
        if not row["v9_note"]:
            raise AssertionError(f"missing V9 note: {endpoint}")

    suspect = {row["endpoint"] for row in rows if row["status"] == "SUSPECT"}
    if suspect != EXPECTED_SUSPECT:
        raise AssertionError(f"suspect endpoint census changed: {suspect}")
    stale = {
        row["endpoint"] for row in rows if row["v9_stale_claim"] == "YES"
    }
    if stale != EXPECTED_STALE:
        raise AssertionError(f"stale-claim census changed: {stale}")
    if Counter(row["status"] for row in rows) != Counter(
        {"OK": 53}
    ):
        raise AssertionError("status census changed")
    if Counter(row["v9_mismatched_claim"] for row in rows) != Counter(
        {"NO": 31, "YES": 22}
    ):
        raise AssertionError("V9 mismatch census changed")


def validate_summary() -> None:
    text = SUMMARY.read_text(encoding="utf-8")
    required = (
        f"tsv_sha256: {EXPECTED_SHA256}",
        "matched SHA-256 " + EXPECTED_SHA256 + ".",
        "exercise_8_39b_gaussian_chevet_reverse_arbitrary at "
        "HighDimensionalProbability/Chapter8_Chaining.lean:25116",
        "theorem_8_6_1_subgaussian_chevet_arbitrary_bounded_real at "
        "HighDimensionalProbability/Chapter8_Chaining.lean:25007",
    )
    missing = [fragment for fragment in required if fragment not in text]
    if missing:
        raise AssertionError(
            "Chapters 8--9 supplement summary is stale: "
            + ", ".join(missing)
        )


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--check", action="store_true", help="validate only (default)")
    mode.add_argument(
        "--write",
        action="store_true",
        help="project preserved reviewed evidence onto the current endpoint set",
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
        "PASS v6_tier_b_supplement_ch8_9: "
        "53 exact endpoints; 0 main-ledger overlap; "
        "53 OK; 0 SUSPECT; 0 stale; 22 mismatch flags; "
        f"sha256={hashlib.sha256(raw).hexdigest()}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
