#!/usr/bin/env python3
"""Build the reproducible V6 Tier-C random-control sample.

The legacy V6 review contains fifty deliberately chosen Tier-C controls.  This
builder retains those controls and draws five *additional* controls for the
Appetizer and each numbered chapter from the remaining Tier-B OK population.

The sampling unit is a canonical Tier-B row together with its exact resolved
endpoint cell.  Every OK Tier-B row is in the base, including rows resolved to
definitions or Mathlib declarations.  Exact endpoint cells already covered by
a legacy control are removed, and duplicate endpoint cells retain the
lexicographically first row as their canonical representative.  These two
steps prevent a preselected or multiply catalogued endpoint from receiving
extra sampling weight; they do not narrow the base by declaration kind.

The seed is the frozen semantic-baseline source-manifest digest.  The audited
Round 10 docstring-only successor therefore retains the exact same sample
frame.  For a canonical row ``r`` in chapter ``c`` its pseudorandom score is

    SHA256(UTF8(seed + NUL + c + NUL + r.row_id)).

The five lexicographically smallest scores are selected without replacement.
This hash-ranking construction is independent of Python's PRNG version and of
the input ledger order.
"""

from __future__ import annotations

import argparse
import collections
import csv
import hashlib
import io
from dataclasses import dataclass
from pathlib import Path

import run_v6_tier_c_ch0_4 as ch0
import run_v6_tier_c_ch5_7 as ch5
import run_v6_tier_c_ch8_9 as ch8
import build_v6_tier_b_ch0_4 as tier_b_common
from source_manifest import build_manifest


ROOT = Path(__file__).resolve().parents[3]
VERIFY = ROOT / "HighDimensionalProbability" / "Verification"
LOGS = VERIFY / "logs"
REVIEW = VERIFY / "review"

SOURCE_MANIFEST = LOGS / "source_manifest.txt"
MAIN_LEDGERS = (
    REVIEW / "v6_tier_b_ch0_4.tsv",
    REVIEW / "v6_tier_b_ch5_7.tsv",
    REVIEW / "v6_tier_b_ch8_9.tsv",
)
SUPPLEMENT_LEDGERS = (
    REVIEW / "v6_tier_b_supplement_ch0_4.tsv",
    REVIEW / "v6_tier_b_supplement_ch5_7.tsv",
    REVIEW / "v6_tier_b_supplement_ch8_9.tsv",
)
LEDGERS = (*MAIN_LEDGERS, *SUPPLEMENT_LEDGERS)

POPULATION = REVIEW / "recert_v6_tier_c_seeded_population.tsv"
FRAME = REVIEW / "recert_v6_tier_c_seeded_frame.tsv"
SAMPLE = REVIEW / "recert_v6_tier_c_seeded_sample.tsv"
SUMMARY = REVIEW / "recert_v6_tier_c_seeded_sample_summary.txt"

CHAPTERS = ("Appetizer", *(f"Chapter {index}" for index in range(1, 10)))
SAMPLE_SIZE = 5
MANIFEST_PREFIX = "# digest_of_digests: "
SEMANTIC_BASELINE_DIGEST = (
    "83678e994eecf416759cb099d5e69f9d03c15921960d4f3b69d055a7a9e8fe27"
)
POPULATION_FIELDS = (
    "chapter",
    "ledger",
    "row_id",
    "row_provenance",
    "book_label",
    "verdict",
    "resolved_declarations",
    "eligible_endpoints_after_fixed_controls",
    "sampling_status",
    "canonical_row_id",
    "score_sha256",
    "selected",
)
FRAME_FIELDS = (
    "chapter",
    "rank",
    "score_sha256",
    "row_id",
    "ledger",
    "row_provenance",
    "book_label",
    "eligible_endpoints",
    "duplicate_row_ids",
    "selected",
)
SAMPLE_FIELDS = (
    "chapter",
    "sample_rank",
    "score_sha256",
    "row_id",
    "ledger",
    "row_provenance",
    "book_label",
    "eligible_endpoints",
    "source_locations",
    "tier_b_justification",
)


class SamplingFailure(RuntimeError):
    pass


@dataclass(frozen=True)
class TierBRow:
    chapter: str
    ledger: str
    row_id: str
    row_provenance: str
    book_label: str
    verdict: str
    resolved_declarations: tuple[str, ...]
    source_locations: str
    tier_b_justification: str


@dataclass(frozen=True)
class FrameRow:
    chapter: str
    score: str
    row: TierBRow
    eligible_endpoints: tuple[str, ...]
    duplicate_row_ids: tuple[str, ...]


@dataclass(frozen=True)
class SamplingResult:
    seed: str
    legacy_fixed_endpoints: frozenset[str]
    population_rows: tuple[dict[str, str], ...]
    frame_rows: tuple[FrameRow, ...]
    selected_rows: tuple[FrameRow, ...]
    counts: dict[str, collections.Counter[str]]


def read_tsv(path: Path) -> list[dict[str, str]]:
    with path.open(encoding="utf-8", newline="") as handle:
        return list(csv.DictReader(handle, delimiter="\t"))


def split_cells(text: str) -> tuple[str, ...]:
    return tuple(cell.strip() for cell in text.split(";") if cell.strip())


def current_manifest_digest() -> str:
    matches = [
        line[len(MANIFEST_PREFIX):].strip()
        for line in SOURCE_MANIFEST.read_text(encoding="utf-8").splitlines()
        if line.startswith(MANIFEST_PREFIX)
    ]
    if len(matches) != 1 or len(matches[0]) != 64:
        raise SamplingFailure("source manifest has no unique SHA-256 digest")
    try:
        bytes.fromhex(matches[0])
    except ValueError as error:
        raise SamplingFailure("source-manifest digest is not hexadecimal") from error
    return matches[0]


def manifest_seed() -> str:
    """Return the semantic sampling seed for the current exact snapshot.

    Round 10 changed only 97 one-line declaration docstrings, and the later
    Exercise reorganization changed only paths plus forced imports/comments.
    Authenticate each successor through its exact delta certificate and keep
    the substantive baseline digest as the stable semantic seed.
    """

    current = current_manifest_digest()
    rendered, actual = build_manifest()
    if actual != current or SOURCE_MANIFEST.read_text(encoding="utf-8") != rendered:
        raise SamplingFailure(
            "source manifest is stale or does not identify the current source tree"
        )
    if current != SEMANTIC_BASELINE_DIGEST:
        try:
            tier_b_common.require_round10_source_identity()
        except ValueError as error:
            raise SamplingFailure(
                f"source-identity certificate chain failed: {error}"
            ) from error
    return SEMANTIC_BASELINE_DIGEST


def legacy_fixed_endpoints() -> frozenset[str]:
    cells: list[str] = []
    cells.extend(spec.target for spec in ch0.QUEUE_SPECS)
    cells.extend(spec.endpoint for spec in ch8.QUEUE_SPECS)
    ch5_rows = {
        row["row_id"]: row
        for row in read_tsv(REVIEW / "v6_tier_b_ch5_7.tsv")
    }
    for row_ids in ch5.QUEUE_IDS.values():
        for row_id in row_ids:
            if row_id not in ch5_rows:
                raise SamplingFailure(f"legacy fixed row disappeared: {row_id}")
            cells.append(ch5_rows[row_id]["resolved_declarations"])
    endpoints = {
        endpoint
        for cell in cells
        for endpoint in split_cells(cell)
    }
    if len(endpoints) != 53:
        raise SamplingFailure(
            f"expected 53 unique fixed endpoints, got {len(endpoints)}"
        )
    return frozenset(endpoints)


def normalize_tier_b_rows() -> list[TierBRow]:
    rows: list[TierBRow] = []
    for path in LEDGERS:
        ledger = path.relative_to(ROOT).as_posix()
        for raw in read_tsv(path):
            verdict = raw.get("verdict") or raw.get("status", "")
            if verdict != "OK":
                continue
            declarations = split_cells(
                raw.get("resolved_declarations") or raw.get("endpoint", "")
            )
            chapters = split_cells(
                raw.get("chapter") or raw.get("chapters", "")
            )
            if not chapters:
                raise SamplingFailure(f"{ledger}:{raw['row_id']}: no chapter")
            provenance = (
                raw.get("sample_kind")
                or raw.get("row_set")
                or "direct_census_supplement"
            )
            book_label = raw.get("book_label") or raw.get("book_refs", "")
            locations = (
                raw.get("source_locations") or raw.get("source_location", "")
            )
            justification = raw.get("justification", "")
            for chapter in chapters:
                if chapter not in CHAPTERS:
                    raise SamplingFailure(
                        f"{ledger}:{raw['row_id']}: unexpected chapter {chapter!r}"
                    )
                rows.append(
                    TierBRow(
                        chapter=chapter,
                        ledger=ledger,
                        row_id=raw["row_id"],
                        row_provenance=provenance,
                        book_label=book_label,
                        verdict=verdict,
                        resolved_declarations=declarations,
                        source_locations=locations,
                        tier_b_justification=justification,
                    )
                )
    keys = [(row.chapter, row.ledger, row.row_id) for row in rows]
    if len(keys) != len(set(keys)):
        raise SamplingFailure("duplicate chapter/ledger/row identity in OK population")
    return rows


def is_legacy_fixed_row(row: TierBRow) -> bool:
    return row.row_provenance == "ok_review_queue_head"


def random_score(seed: str, chapter: str, row_id: str) -> str:
    payload = f"{seed}\0{chapter}\0{row_id}".encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def build_sampling_result() -> SamplingResult:
    seed = manifest_seed()
    fixed = legacy_fixed_endpoints()
    rows = normalize_tier_b_rows()

    eligible_by_cell: dict[
        tuple[str, tuple[str, ...]], list[TierBRow]
    ] = collections.defaultdict(list)
    status_by_identity: dict[tuple[str, str, str], str] = {}
    eligible_by_identity: dict[
        tuple[str, str, str], tuple[str, ...]
    ] = {}
    canonical_by_identity: dict[tuple[str, str, str], str] = {}

    for row in rows:
        identity = (row.chapter, row.ledger, row.row_id)
        remaining = tuple(
            endpoint
            for endpoint in row.resolved_declarations
            if endpoint not in fixed
        )
        eligible_by_identity[identity] = remaining
        if is_legacy_fixed_row(row):
            status_by_identity[identity] = "LEGACY_FIXED_CONTROL_ROW"
        elif not remaining:
            status_by_identity[identity] = "EXCLUDED_FIXED_ENDPOINT_ONLY"
        else:
            eligible_by_cell[(row.chapter, remaining)].append(row)

    frame_rows: list[FrameRow] = []
    for (chapter, endpoints), group in sorted(eligible_by_cell.items()):
        ordered = sorted(group, key=lambda row: (row.row_id, row.ledger))
        canonical = ordered[0]
        duplicates = tuple(row.row_id for row in ordered[1:])
        canonical_identity = (
            canonical.chapter,
            canonical.ledger,
            canonical.row_id,
        )
        status_by_identity[canonical_identity] = "ELIGIBLE_CANONICAL_FRAME_ROW"
        canonical_by_identity[canonical_identity] = canonical.row_id
        for duplicate in ordered[1:]:
            identity = (
                duplicate.chapter,
                duplicate.ledger,
                duplicate.row_id,
            )
            status_by_identity[identity] = "EXCLUDED_DUPLICATE_ENDPOINT_CELL"
            canonical_by_identity[identity] = canonical.row_id
        frame_rows.append(
            FrameRow(
                chapter=chapter,
                score=random_score(seed, chapter, canonical.row_id),
                row=canonical,
                eligible_endpoints=endpoints,
                duplicate_row_ids=duplicates,
            )
        )

    selected_rows: list[FrameRow] = []
    for chapter in CHAPTERS:
        chapter_frame = sorted(
            (row for row in frame_rows if row.chapter == chapter),
            key=lambda row: (row.score, row.row.row_id),
        )
        if len(chapter_frame) < SAMPLE_SIZE:
            raise SamplingFailure(
                f"{chapter}: only {len(chapter_frame)} eligible canonical rows"
            )
        chapter_selected = chapter_frame[:SAMPLE_SIZE]
        if len({row.row.row_id for row in chapter_selected}) != SAMPLE_SIZE:
            raise SamplingFailure(f"{chapter}: sampled a duplicate row")
        endpoint_sets = [set(row.eligible_endpoints) for row in chapter_selected]
        for index, left in enumerate(endpoint_sets):
            for right in endpoint_sets[index + 1:]:
                if left & right:
                    raise SamplingFailure(
                        f"{chapter}: selected endpoint cells overlap: "
                        f"{sorted(left & right)}"
                    )
        selected_rows.extend(chapter_selected)

    selected_identities = {
        (row.chapter, row.row.ledger, row.row.row_id)
        for row in selected_rows
    }
    population_rows: list[dict[str, str]] = []
    counts: dict[str, collections.Counter[str]] = {
        chapter: collections.Counter() for chapter in CHAPTERS
    }
    for row in sorted(
        rows, key=lambda item: (CHAPTERS.index(item.chapter), item.row_id, item.ledger)
    ):
        identity = (row.chapter, row.ledger, row.row_id)
        status = status_by_identity.get(identity)
        if status is None:
            raise SamplingFailure(f"unclassified population row: {identity}")
        counts[row.chapter][status] += 1
        remaining = eligible_by_identity[identity]
        score = (
            random_score(seed, row.chapter, row.row_id)
            if status == "ELIGIBLE_CANONICAL_FRAME_ROW"
            else ""
        )
        population_rows.append(
            {
                "chapter": row.chapter,
                "ledger": row.ledger,
                "row_id": row.row_id,
                "row_provenance": row.row_provenance,
                "book_label": row.book_label,
                "verdict": row.verdict,
                "resolved_declarations": ";".join(row.resolved_declarations),
                "eligible_endpoints_after_fixed_controls": ";".join(remaining),
                "sampling_status": status,
                "canonical_row_id": canonical_by_identity.get(identity, ""),
                "score_sha256": score,
                "selected": "YES" if identity in selected_identities else "NO",
            }
        )

    if len(selected_rows) != SAMPLE_SIZE * len(CHAPTERS):
        raise SamplingFailure("seeded sample does not contain exactly fifty rows")
    if len(
        {
            (row.chapter, row.row.row_id)
            for row in selected_rows
        }
    ) != len(selected_rows):
        raise SamplingFailure("seeded sample chapter/row identities are not unique")
    return SamplingResult(
        seed=seed,
        legacy_fixed_endpoints=fixed,
        population_rows=tuple(population_rows),
        frame_rows=tuple(frame_rows),
        selected_rows=tuple(selected_rows),
        counts=counts,
    )


def render_dict_tsv(
    fields: tuple[str, ...],
    rows: list[dict[str, str]] | tuple[dict[str, str], ...],
) -> str:
    buffer = io.StringIO(newline="")
    writer = csv.DictWriter(
        buffer, fieldnames=fields, delimiter="\t", lineterminator="\n"
    )
    writer.writeheader()
    writer.writerows(rows)
    return buffer.getvalue()


def ordered_frame(result: SamplingResult) -> list[FrameRow]:
    return sorted(
        result.frame_rows,
        key=lambda row: (
            CHAPTERS.index(row.chapter),
            row.score,
            row.row.row_id,
        ),
    )


def render_frame(result: SamplingResult) -> str:
    selected = {
        (row.chapter, row.row.row_id) for row in result.selected_rows
    }
    ranks = collections.Counter()
    rows: list[dict[str, str]] = []
    for frame_row in ordered_frame(result):
        ranks[frame_row.chapter] += 1
        rows.append(
            {
                "chapter": frame_row.chapter,
                "rank": str(ranks[frame_row.chapter]),
                "score_sha256": frame_row.score,
                "row_id": frame_row.row.row_id,
                "ledger": frame_row.row.ledger,
                "row_provenance": frame_row.row.row_provenance,
                "book_label": frame_row.row.book_label,
                "eligible_endpoints": ";".join(frame_row.eligible_endpoints),
                "duplicate_row_ids": ";".join(frame_row.duplicate_row_ids),
                "selected": (
                    "YES"
                    if (frame_row.chapter, frame_row.row.row_id) in selected
                    else "NO"
                ),
            }
        )
    return render_dict_tsv(FRAME_FIELDS, rows)


def render_sample(result: SamplingResult) -> str:
    rows: list[dict[str, str]] = []
    ranks = collections.Counter()
    for frame_row in sorted(
        result.selected_rows,
        key=lambda row: (CHAPTERS.index(row.chapter), row.score),
    ):
        ranks[frame_row.chapter] += 1
        rows.append(
            {
                "chapter": frame_row.chapter,
                "sample_rank": str(ranks[frame_row.chapter]),
                "score_sha256": frame_row.score,
                "row_id": frame_row.row.row_id,
                "ledger": frame_row.row.ledger,
                "row_provenance": frame_row.row.row_provenance,
                "book_label": frame_row.row.book_label,
                "eligible_endpoints": ";".join(frame_row.eligible_endpoints),
                "source_locations": frame_row.row.source_locations,
                "tier_b_justification": frame_row.row.tier_b_justification,
            }
        )
    return render_dict_tsv(SAMPLE_FIELDS, rows)


def render_summary(result: SamplingResult) -> str:
    lines = [
        "V6 TIER-C MANIFEST-SEEDED RANDOM CONTROL SAMPLE",
        "================================================",
        "verdict: PASS",
        "seed_source: post-removal semantic baseline digest retained across "
        "the audited Round 10 docstring-only and Exercise-reorganization deltas",
        f"seed: {result.seed}",
        f"current_source_manifest: {current_manifest_digest()}",
        "seed_currentness_evidence: HighDimensionalProbability/Verification/"
        "logs/round10_docstring_delta.log;HighDimensionalProbability/"
        "Verification/logs/exercise_reorganization_delta.log",
        "algorithm: for each canonical row r in chapter c, rank ascending by "
        "SHA256(UTF8(seed + NUL + c + NUL + r.row_id)); take first 5",
        "sampling_mode: without replacement",
        "legacy_fixed_controls_retained: 50",
        "legacy_unique_resolved_endpoints_excluded: "
        f"{len(result.legacy_fixed_endpoints)}",
        "new_seeded_controls: 50",
        "new_seeded_controls_per_chapter: 5",
        "sampling_command: python3 -B "
        "HighDimensionalProbability/Verification/scripts/"
        "build_v6_tier_c_seeded_sample.py --write",
        "",
        "[legacy_fixed_resolved_endpoints]",
        *sorted(result.legacy_fixed_endpoints),
        "",
        "[per_chapter_population_and_frame]",
        "chapter\tfull_ok_rows\tlegacy_fixed_rows\tfixed_endpoint_only\t"
        "duplicate_endpoint_cell\tcanonical_frame\tselected",
    ]
    for chapter in CHAPTERS:
        counter = result.counts[chapter]
        full = sum(counter.values())
        lines.append(
            "\t".join(
                (
                    chapter,
                    str(full),
                    str(counter["LEGACY_FIXED_CONTROL_ROW"]),
                    str(counter["EXCLUDED_FIXED_ENDPOINT_ONLY"]),
                    str(counter["EXCLUDED_DUPLICATE_ENDPOINT_CELL"]),
                    str(counter["ELIGIBLE_CANONICAL_FRAME_ROW"]),
                    str(SAMPLE_SIZE),
                )
            )
        )
    lines.extend(
        (
            "",
            "[exclusion_rationale]",
            "LEGACY_FIXED_CONTROL_ROW: retained in Tier C but not eligible for "
            "the additional draw.",
            "EXCLUDED_FIXED_ENDPOINT_ONLY: every resolved endpoint in the row "
            "is already covered by a legacy fixed control.",
            "EXCLUDED_DUPLICATE_ENDPOINT_CELL: another OK Tier-B row has the "
            "same remaining resolved endpoint cell; the lexicographically first "
            "row_id is the canonical sampling unit.",
            "",
        )
    )
    return "\n".join(lines)


def artifacts(result: SamplingResult) -> dict[Path, str]:
    return {
        POPULATION: render_dict_tsv(
            POPULATION_FIELDS, result.population_rows
        ),
        FRAME: render_frame(result),
        SAMPLE: render_sample(result),
        SUMMARY: render_summary(result),
    }


def require_exact(path: Path, expected: str) -> None:
    if not path.is_file() or path.read_text(encoding="utf-8") != expected:
        raise SamplingFailure(f"artifact drift: {path.relative_to(ROOT)}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--write", action="store_true", help="write the canonical artifacts"
    )
    args = parser.parse_args()
    result = build_sampling_result()
    expected = artifacts(result)
    if args.write:
        for path, text in expected.items():
            path.write_text(text, encoding="utf-8")
    for path, text in expected.items():
        require_exact(path, text)
    print(
        "PASS build_v6_tier_c_seeded_sample: "
        f"seed={result.seed}; 50 new controls; 5 per chapter"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, KeyError, ValueError, SamplingFailure) as error:
        print(f"FAIL build_v6_tier_c_seeded_sample: {error}")
        raise SystemExit(1)
