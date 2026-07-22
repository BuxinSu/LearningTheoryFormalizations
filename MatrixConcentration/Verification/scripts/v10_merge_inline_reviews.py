#!/usr/bin/env python3
"""Validate and atomically merge the three V10 inline-review chunks."""

from __future__ import annotations

import argparse
import csv
import hashlib
import os
from pathlib import Path


SCRIPT = Path(__file__).resolve()
VERIFY = SCRIPT.parent.parent
ROOT = VERIFY.parent.parent
LOGS = VERIFY / "logs"
CURATION = VERIFY / "curation" / "v10_inline_adjudication.tsv"
QUEUE = LOGS / "v10_inline_review_queue.tsv"
OBLIGATIONS = LOGS / "v10_inline_review_obligations.tsv"
CHUNKS = [
    ROOT / ".audit_work" / "v10_inline_review_chunk_a.tsv",
    ROOT / ".audit_work" / "v10_inline_review_chunk_b.tsv",
    ROOT / ".audit_work" / "v10_inline_review_chunk_c.tsv",
]

HEADER = ["type_hash", "adjudication", "evidence", "reviewer_note"]
QUEUE_HEADER = [
    "type_hash",
    "occurrence_count",
    "declaration_count",
    "categories",
    "review_states",
    "declarations",
    "normalized_type",
]
ALLOWED = {
    "ROUTINE_EXPLICIT_HYPOTHESIS",
    "DISCHARGED_BY_SOURCE_CALLER",
    "DISCLOSED_CONDITIONAL_INFRASTRUCTURE",
    "UNDISCLOSED_CONDITIONAL_PRINCIPLE",
    "UNRESOLVED_REVIEW_RISK",
}


def read_tsv(path: Path, header: list[str]) -> list[dict[str, str]]:
    with path.open(encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle, delimiter="\t")
        if reader.fieldnames != header:
            raise RuntimeError(
                f"{path}: header {reader.fieldnames!r}, expected {header!r}"
            )
        rows = list(reader)
    for line, row in enumerate(rows, start=2):
        if None in row or any(value is None for value in row.values()):
            raise RuntimeError(f"{path}:{line}: malformed TSV row")
    return rows


def validate_review_rows(
    path: Path,
    rows: list[dict[str, str]],
) -> None:
    seen: set[str] = set()
    for line, row in enumerate(rows, start=2):
        digest = row["type_hash"]
        if (
            len(digest) != 64
            or any(char not in "0123456789abcdef" for char in digest)
        ):
            raise RuntimeError(f"{path}:{line}: invalid SHA-256 {digest!r}")
        if digest in seen:
            raise RuntimeError(f"{path}:{line}: duplicate hash {digest}")
        seen.add(digest)
        if row["adjudication"] not in ALLOWED:
            raise RuntimeError(
                f"{path}:{line}: invalid adjudication {row['adjudication']!r}"
            )
        for field in ("evidence", "reviewer_note"):
            if len(row[field].strip()) < 20:
                raise RuntimeError(f"{path}:{line}: non-substantive {field}")


def digest_rows(rows: list[dict[str, str]]) -> str:
    canonical = "\n".join(
        "\t".join(row[field] for field in HEADER)
        for row in sorted(rows, key=lambda row: row["type_hash"])
    )
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--apply",
        action="store_true",
        help="atomically replace the live curation after validation",
    )
    args = parser.parse_args()

    base = read_tsv(CURATION, HEADER)
    queue = read_tsv(QUEUE, QUEUE_HEADER)
    obligations = read_tsv(OBLIGATIONS, QUEUE_HEADER)
    chunks = [read_tsv(path, HEADER) for path in CHUNKS]
    validate_review_rows(CURATION, base)
    for path, rows in zip(CHUNKS, chunks, strict=True):
        validate_review_rows(path, rows)

    if len(queue) % len(CHUNKS) != 0:
        raise RuntimeError(
            f"queue size {len(queue)} is not divisible by {len(CHUNKS)}"
        )
    chunk_size = len(queue) // len(CHUNKS)
    for index, (path, rows) in enumerate(zip(CHUNKS, chunks, strict=True)):
        expected = [
            row["type_hash"]
            for row in queue[index * chunk_size : (index + 1) * chunk_size]
        ]
        measured = [row["type_hash"] for row in rows]
        if measured != expected:
            raise RuntimeError(
                f"{path}: assigned ordered hash set mismatch "
                f"(expected {len(expected)}, measured {len(measured)})"
            )

    base_hashes = {row["type_hash"] for row in base}
    new_rows = [row for chunk in chunks for row in chunk]
    new_hashes = {row["type_hash"] for row in new_rows}
    queue_hashes = {row["type_hash"] for row in queue}
    obligation_hashes = {row["type_hash"] for row in obligations}
    if len(new_rows) != len(new_hashes):
        raise RuntimeError("review chunks contain cross-chunk duplicate hashes")
    if new_hashes != queue_hashes:
        raise RuntimeError("review chunk union does not equal the live queue")
    if base_hashes & new_hashes:
        raise RuntimeError("base curation overlaps the new review chunks")
    if base_hashes | new_hashes != obligation_hashes:
        raise RuntimeError(
            "base/new curation union does not equal the persistent obligations"
        )

    merged = sorted(base + new_rows, key=lambda row: row["type_hash"])
    finding_rows = [
        row
        for row in merged
        if row["adjudication"]
        in {
            "DISCLOSED_CONDITIONAL_INFRASTRUCTURE",
            "UNDISCLOSED_CONDITIONAL_PRINCIPLE",
            "UNRESOLVED_REVIEW_RISK",
        }
    ]
    print("V10 INLINE REVIEW MERGE")
    print(f"BASE_ROWS {len(base)}")
    print(f"QUEUE_ROWS {len(queue)}")
    print(f"CHUNK_ROWS {len(new_rows)}")
    print(f"OBLIGATION_ROWS {len(obligations)}")
    print(f"MERGED_ROWS {len(merged)}")
    print(f"FINDING_ROWS {len(finding_rows)}")
    print(f"MERGED_CONTENT_SHA256 {digest_rows(merged)}")

    if args.apply:
        temporary = CURATION.with_name(CURATION.name + ".tmp")
        with temporary.open("w", encoding="utf-8", newline="") as handle:
            writer = csv.DictWriter(
                handle,
                fieldnames=HEADER,
                delimiter="\t",
                lineterminator="\n",
            )
            writer.writeheader()
            writer.writerows(merged)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, CURATION)
        print(f"APPLIED {CURATION.relative_to(ROOT)}")
    else:
        print("APPLIED false")
    print("VERDICT PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
