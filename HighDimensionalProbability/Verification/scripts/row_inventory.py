#!/usr/bin/env python3
"""Build reproducible README/census inventories and deterministic V6 plans.

This is deliberately a mechanical inventory tool.  It does not decide whether
any mathematical statement is faithful, vacuous, or otherwise ``OK``.  In
particular, the "OK" output is a deterministic *candidate ordering*: after a
later close read assigns semantic verdicts, take the first five rows per
chapter whose verdict is actually ``OK``.

The exhaustive 838-row *frozen input* census is reconstructed from the three
row-level tables in the authenticated archive
``REVIEW_NOTES.pre-final-correction.md``:

* 717 frozen proved/stronger rows;
* 67 original Appendix-owned rows;
* 54 accepted rows from the 89-row gap disposition table.

The frozen proved/stronger table displays 724 rows because its prose says that
it also contains seven consolidated post-correction display entries.  Those
seven entries are retained in a separate artifact rather than silently
discarded.  This gives the explicit, checked identity
``724 - 7 + 67 + (89 - 35) = 838``.
"""

from __future__ import annotations

import argparse
import copy
import csv
import hashlib
import io
import json
import re
import sys
from collections import Counter, defaultdict
from pathlib import Path
from typing import Iterable, Mapping, Sequence

from file_universe import HDP, ROOT
from lean_source_scanner import mask_lean_noncode
from source_manifest import build_manifest
from v6_tier_a_scanner import extract_declarations
from verify_exercise_reorganization import (
    new_to_old_exercise_path,
    old_to_new_exercise_path,
    require_certificate as require_reorganization_certificate,
)


README = HDP / "README.md"
REVIEW = (
    HDP / "Verification" / "archive" / "REVIEW_NOTES.pre-final-correction.md"
)
LIVE_REVIEW = HDP / "Verification" / "REVIEW_NOTES.md"
FAITHFUL = HDP / "Verification" / "archive" / "FAITHFUL_PROOFREAD_REPORT.md"
DEFAULT_OUTPUT_DIR = HDP / "Verification" / "inventory"
SOURCE_MANIFEST = HDP / "Verification" / "logs" / "source_manifest.txt"
ROUND10_DELTA_LOG = (
    HDP / "Verification" / "logs" / "round10_docstring_delta.log"
)
SEMANTIC_BASELINE_DIGEST = (
    "83678e994eecf416759cb099d5e69f9d03c15921960d4f3b69d055a7a9e8fe27"
)
ROUND10_SOURCE_DIGEST = (
    "bca641bd4c523754aa472b97cb1ed5638a6eb7361f99158a3f231a03a7446460"
)
EXPECTED_REVIEW_SHA256 = (
    "53ac710d7882078e460ba9df8f7d94e9ca37110924ce17d86"
    "ecd991480ab1dc1"
)
# Curated Pass 07 records share the inventory directory but are not generated
# by this mechanical census builder.  The checker must preserve and permit
# them rather than treating them as stale generator output.
CURATED_INVENTORY_ARTIFACTS = {
    "frozen_inventory_provenance.tsv",
    "pass07_census_projection.tsv",
    "pass07_core_partial_resolutions.tsv",
    "pass07_declaration_changes.tsv",
    "pass07_declaration_changes_summary.json",
    "pass07_dependency_cones.tsv",
    "pass07_endpoint_replacements.tsv",
    "pass07_same_name_changes.tsv",
    "pass07_soundness_resolutions.tsv",
    "v10_consumers.tsv",
    "v10_environment_predicates.tsv",
    "v10_environment_text_diff.tsv",
    "v10_inline_hypotheses.tsv",
    "v10_predicate_census.tsv",
    "v10_textual_predicates.tsv",
}

SCHEMA_VERSION = 1
CHAPTERS = ["Appetizer", *(f"Chapter {number}" for number in range(1, 10))]
LEAN_CHAPTERS = [f"Chapter {number}" for number in range(1, 10)]
CHAPTER_ORDER = {chapter: index for index, chapter in enumerate(CHAPTERS)}

README_EXPECTED_BY_CHAPTER = {
    "Appetizer": 8,
    "Chapter 1": 51,
    "Chapter 2": 59,
    "Chapter 3": 75,
    "Chapter 4": 88,
    "Chapter 5": 68,
    "Chapter 6": 39,
    "Chapter 7": 62,
    "Chapter 8": 100,
    "Chapter 9": 61,
}
CENSUS_EXPECTED_BY_CHAPTER = {
    "Appetizer": 11,
    "Chapter 1": 63,
    "Chapter 2": 71,
    "Chapter 3": 97,
    "Chapter 4": 117,
    "Chapter 5": 112,
    "Chapter 6": 47,
    "Chapter 7": 82,
    "Chapter 8": 123,
    "Chapter 9": 115,
}
REVIEW_BUCKET_EXPECTED = {
    "core_formalized": 768,
    "appendix_proved": 65,
    "appendix_unresolved_or_deferred": 5,
}
CURRENT_CENSUS_EXPECTED_BY_CHAPTER = {
    **CENSUS_EXPECTED_BY_CHAPTER,
    "Chapter 3": 96,
    "Chapter 5": 111,
    "Chapter 8": 122,
}
CURRENT_REVIEW_BUCKET_EXPECTED = {
    "core_formalized": 769,
    "appendix_proved": 66,
}
CURRENT_REMOVED_ROW_IDS = {
    "census-bf1de680f35b52dc",
    "census-628be74004e48217",
    "census-939078c2ac4f78a5",
}
CURRENT_EXERCISE_8_39_ROW_ID = "census-8e50e84b6b82a573"
CURRENT_BROWNIAN_ROW_ID = "census-360c40946511e7a9"
CURRENT_EXERCISE_8_39_ENDPOINT = (
    "HDP.Chapter8.exercise_8_39b_gaussian_chevet_reverse_arbitrary"
)
CURRENT_BROWNIAN_ENDPOINT = (
    "HDP.Chapter7.brownianReflectionPrinciple_external"
)
REMOVED_CONDITIONAL_ENDPOINTS = {
    "HDP.Chapter5.positive_ricci_concentration",
    "HDP.Chapter8.exercise_8_39a_gaussian_chevet_arbitrary",
    "HDP.Chapter8.gaussianChevetUpperPrinciple_external",
    "HDP.Chapter8.remark_8_6_3_gaussian_chevet_arbitrary",
}
EXPECTED_FROZEN_CENSUS_TSV_SHA256 = (
    "184f44ef33c9318450b9b31282c02850868cdafb93fe7ad722219acd7e6e1857"
)
EXPECTED_FROZEN_CENSUS_JSON_SHA256 = (
    # The frozen rows are unchanged; this post-reorganization render records
    # their current Verification/archive source path and live-review path.
    "ca8b10e0fb72721e0d20dce7588974438fb1f5d8aafa84d74532b40006a6279d"
)

EXERCISE_SAMPLE_SEED = "hdp-v6-exercise-leaf-close-read-v1"
OK_SAMPLE_SEED = "hdp-v6-ok-row-candidate-order-v1"
EXERCISE_SAMPLE_SIZE = 3
OK_SAMPLE_SIZE = 5

REVIEW_GAP_HEADING = "## Disposition of the 89 frozen gap rows"
REVIEW_APPENDIX_HEADING = "## Appendix-owned coverage: not a core proof claim"
REVIEW_FROZEN_HEADING = (
    "## Row-level faithfulness, source, and citation notes on frozen "
    "proved/stronger rows"
)
REVIEW_AFTER_FROZEN_HEADING = (
    "## Cross-row and source-level faithfulness issues"
)

# The authenticated pre-final-correction review explicitly describes these
# as the seven extra consolidated display entries in the otherwise exhaustive
# 717-row frozen table.
FROZEN_DISPLAY_ONLY_EXTRAS = {
    ("Appetizer", "Theorem 0.0.2"),
    ("Appetizer", "Corollary 0.0.3"),
    ("Appetizer", "Theorem 0.0.4; (0.2)"),
    ("Appetizer", "(0.3)–(0.4)"),
    ("Appetizer", "Remark 0.0.5"),
    ("Appetizer", "Exercises 0.1(a), 0.2, 0.3"),
    ("Chapter 7", "Proposition 7.5.2"),
}

# These two accepted-gap rows predate the later stable Appendix blocker IDs.
# Their individual cells say only ``IN-APPENDIX``, while the immediately
# following archive prose explicitly includes both in the five unresolved
# rows.  Preserve that documented historical classification rather than
# applying the generic no-token => proved fallback.
HISTORICAL_DEFERRED_GAP_ROWS = {
    (
        "Chapter 3",
        "Example 3.4.6",
    ): "APPENDIX-UNRESOLVED-003",
    (
        "Chapter 7",
        "Sec. 7.2.1 Brownian reflection example",
    ): "APPENDIX-UNRESOLVED-004",
}

README_HEADER = (
    "Book source",
    "Result",
    "Lean declaration",
    "Final module",
)
GAP_HEADER = (
    "Chapter",
    "Book ref",
    "Validated disposition",
    "Result",
    "Located Lean evidence",
    "Audited file evidence",
    "Validation evidence and disposition",
)
APPENDIX_HEADER = (
    "Chapter",
    "Book ref",
    "Result",
    "Appendix/conditional evidence",
    "File evidence",
    "Final isolated status / notes",
)
FROZEN_HEADER = (
    "Chapter",
    "Book ref",
    "Audit class",
    "Result",
    "Faithfulness / source / citation note",
)
FAITHFUL_CENSUS_HEADER = (
    "Chapter",
    "Frozen rows",
    "Core formalized",
    "Core partial",
    "Appendix proved",
    "Appendix unresolved / deferred",
    "Missing",
    "Rejected",
    "Valid",
    "Practice exercises out of scope",
)
FAITHFUL_PARTIAL_HEADER = ("Chapter", "Book reference", "Missing part")
FAITHFUL_APPENDIX_HEADER = ("Chapter", "Book reference", "Status")

INLINE_CODE_RE = re.compile(r"(?<!`)`([^`\r\n]+)`(?!`)")
LEAN_IDENTIFIER_RE = re.compile(
    r"(?:«[^»]+»|[A-Za-z_][A-Za-z0-9_']*)"
    r"(?:\.(?:«[^»]+»|[A-Za-z_][A-Za-z0-9_']*))*"
)
APPENDIX_STATUS_RE = re.compile(
    r"APPENDIX-(?:PROVED|UNRESOLVED-\d+)"
)
STATUS_TOKEN_RE = re.compile(
    r"\b(?:FORMALIZED|STRONGER|REJECTED|IN-APPENDIX|PARTIAL|MISSING|"
    r"UNSURE|VERIFIED|PROVED|SKIPPED|APPENDIX-PROVED|"
    r"APPENDIX-UNRESOLVED-\d+)\b"
)

BOOK_REF_PATTERNS: tuple[tuple[str, re.Pattern[str]], ...] = (
    ("exercise", re.compile(r"\bexercises?\b", re.IGNORECASE)),
    ("theorem", re.compile(r"\btheorems?\b", re.IGNORECASE)),
    ("lemma", re.compile(r"\blemmas?\b", re.IGNORECASE)),
    ("proposition", re.compile(r"\bpropositions?\b", re.IGNORECASE)),
    ("corollary", re.compile(r"\bcorollar(?:y|ies)\b", re.IGNORECASE)),
    ("remark", re.compile(r"\bremarks?\b", re.IGNORECASE)),
    ("example", re.compile(r"\bexamples?\b", re.IGNORECASE)),
    ("definition", re.compile(r"\bdefinitions?\b", re.IGNORECASE)),
    ("question", re.compile(r"\bquestions?\b", re.IGNORECASE)),
    ("section", re.compile(r"(?:\bsec(?:tion)?\.?\b|§)", re.IGNORECASE)),
    ("notes", re.compile(r"\bnotes?\b", re.IGNORECASE)),
    ("proof", re.compile(r"\bproof\b", re.IGNORECASE)),
    ("prose", re.compile(r"\bprose\b", re.IGNORECASE)),
    (
        "equation",
        re.compile(
            r"(?:\beq(?:uation)?\.?\s*)?\(\d+(?:\.\d+)+(?:[a-z])?\)",
            re.IGNORECASE,
        ),
    ),
)

README_TSV_FIELDS = (
    "row_id",
    "source_line",
    "chapter",
    "book_ref",
    "book_ref_primary_kind",
    "book_ref_kinds",
    "result",
    "lean_declaration_cell",
    "endpoint_names",
    "endpoint_resolution_modes",
    "ignored_endpoint_code_spans",
    "final_module",
    "source_status_cell",
    "source_status_class",
    "coverage_bucket",
)
CENSUS_TSV_FIELDS = (
    "row_id",
    "census_component",
    "source_line",
    "chapter",
    "book_ref",
    "book_ref_primary_kind",
    "book_ref_kinds",
    "result",
    "source_status_cell",
    "source_status_class",
    "status_tokens",
    "status_classification_basis",
    "coverage_bucket",
    "evidence_cell",
    "file_evidence",
    "note",
    "direct_endpoint_names",
    "direct_endpoint_resolution_modes",
    "ignored_evidence_code_spans",
    "readme_match_ids",
    "readme_exact_endpoint_names",
    "endpoint_names",
    "endpoint_linkage",
    "faithful_historical_flag_ids",
)
GAP_TSV_FIELDS = CENSUS_TSV_FIELDS
EXTRA_TSV_FIELDS = (
    "row_id",
    "source_line",
    "chapter",
    "book_ref",
    "book_ref_primary_kind",
    "book_ref_kinds",
    "source_status_cell",
    "result",
    "note",
    "exclusion_reason",
)
FAITHFUL_TSV_FIELDS = (
    "row_id",
    "source_line",
    "chapter",
    "book_ref",
    "historical_status",
    "historical_detail",
    "book_ref_primary_kind",
    "book_ref_kinds",
    "candidate_census_ids",
    "census_match_mode",
)
ENDPOINT_TSV_FIELDS = (
    "endpoint",
    "namespace",
    "source_kinds",
    "source_row_ids",
    "chapters",
    "book_refs",
    "resolution_modes",
    "occurrence_count",
)
EXERCISE_DECL_TSV_FIELDS = (
    "declaration_id",
    "chapter",
    "path",
    "module",
    "namespace",
    "kind",
    "local_name",
    "endpoint",
    "start_line",
    "end_line",
    "parsed",
    "statement",
    "conclusion",
    "book_tags",
    "is_exercise_sample_candidate",
)
SAMPLE_TSV_FIELDS = (
    "sample_kind",
    "chapter",
    "rank",
    "quota",
    "seed",
    "sample_hash",
    "target_id",
    "target_kind",
    "path",
    "line",
    "endpoint",
    "book_ref",
    "result",
    "coverage_bucket",
    "semantic_verdict",
    "selection_instruction",
)


class InventoryError(RuntimeError):
    """Raised for a source-shape or count invariant failure."""


def _clean_markdown_text(value: str) -> str:
    return re.sub(r"\s+", " ", value).strip()


def split_markdown_row(line: str) -> list[str]:
    """Split one pipe-table row, ignoring escaped and inline-code pipes.

    Backtick runs of any length are paired, so a pipe within either `` `x|y` ``
    or a longer inline-code delimiter remains in its cell.
    """

    stripped = line.strip()
    if not stripped.startswith("|") or not stripped.endswith("|"):
        raise InventoryError(f"not a closed Markdown table row: {line!r}")
    payload = stripped[1:-1]
    cells: list[str] = []
    current: list[str] = []
    code_delimiter: int | None = None
    index = 0
    while index < len(payload):
        character = payload[index]
        if character == "\\" and index + 1 < len(payload):
            current.extend(payload[index : index + 2])
            index += 2
            continue
        if character == "`":
            end = index
            while end < len(payload) and payload[end] == "`":
                end += 1
            run_length = end - index
            if code_delimiter is None:
                code_delimiter = run_length
            elif code_delimiter == run_length:
                code_delimiter = None
            current.extend(payload[index:end])
            index = end
            continue
        if character == "|" and code_delimiter is None:
            cells.append(_clean_markdown_text("".join(current)))
            current = []
        else:
            current.append(character)
        index += 1
    if code_delimiter is not None:
        raise InventoryError(f"unterminated inline code in table row: {line!r}")
    cells.append(_clean_markdown_text("".join(current)))
    return cells


def _is_separator(cells: Sequence[str]) -> bool:
    return bool(cells) and all(
        re.fullmatch(r":?-{3,}:?", cell) is not None for cell in cells
    )


def _heading_level(heading: str) -> int:
    match = re.match(r"^(#+)\s", heading)
    if match is None:
        raise InventoryError(f"invalid Markdown heading: {heading!r}")
    return len(match.group(1))


def table_under_heading(
    lines: Sequence[str],
    heading: str,
    header: Sequence[str],
) -> list[tuple[int, list[str]]]:
    """Return the one table below an exact heading and before its peer."""

    try:
        start = lines.index(heading)
    except ValueError as error:
        raise InventoryError(f"missing heading {heading!r}") from error
    level = _heading_level(heading)
    end = len(lines)
    for index in range(start + 1, len(lines)):
        candidate = lines[index]
        if not candidate.startswith("#"):
            continue
        match = re.match(r"^(#+)\s", candidate)
        if match is not None and len(match.group(1)) <= level:
            end = index
            break

    header_tuple = tuple(header)
    found_header = False
    rows: list[tuple[int, list[str]]] = []
    for index in range(start + 1, end):
        line = lines[index]
        if not line.strip().startswith("|"):
            if found_header and rows:
                break
            continue
        cells = split_markdown_row(line)
        if tuple(cells) == header_tuple:
            if found_header:
                raise InventoryError(f"duplicate table header below {heading!r}")
            found_header = True
            continue
        if not found_header or _is_separator(cells):
            continue
        if len(cells) != len(header_tuple):
            raise InventoryError(
                f"{index + 1}: expected {len(header_tuple)} cells below "
                f"{heading!r}, found {len(cells)}"
            )
        rows.append((index + 1, cells))
    if not found_header:
        raise InventoryError(f"missing expected table below {heading!r}")
    if not rows:
        raise InventoryError(f"empty expected table below {heading!r}")
    return rows


def _typographic_normalize(value: str) -> str:
    translation = str.maketrans(
        {
            "–": "-",
            "—": "-",
            "−": "-",
            "‑": "-",
            "“": '"',
            "”": '"',
            "’": "'",
            " ": " ",
        }
    )
    return re.sub(
        r"\s+",
        " ",
        value.translate(translation).replace("`", ""),
    ).strip().casefold()


def _strip_emphasis(value: str) -> str:
    return value.replace("**", "").replace("__", "").strip()


def canonical_chapter(value: str) -> str:
    cleaned = _strip_emphasis(value).strip()
    if cleaned == "Appetizer":
        return cleaned
    if cleaned.isdigit():
        cleaned = f"Chapter {cleaned}"
    match = re.fullmatch(r"Chapter\s+([1-9])", cleaned, re.IGNORECASE)
    if match is None:
        raise InventoryError(f"unrecognized chapter label: {value!r}")
    return f"Chapter {match.group(1)}"


def classify_book_ref(value: str) -> tuple[str, list[str]]:
    hits: list[tuple[int, int, str]] = []
    for pattern_index, (kind, pattern) in enumerate(BOOK_REF_PATTERNS):
        match = pattern.search(value)
        if match is not None:
            hits.append((match.start(), pattern_index, kind))
    hits.sort()
    kinds: list[str] = []
    for _, _, kind in hits:
        if kind not in kinds:
            kinds.append(kind)
    if not kinds:
        kinds = ["named_or_prose_result"]
    return kinds[0], kinds


def _stable_id(prefix: str, *parts: object) -> str:
    payload = "\0".join(str(part) for part in parts).encode("utf-8")
    return f"{prefix}-{hashlib.sha256(payload).hexdigest()[:16]}"


def resolve_endpoint_cell(cell: str) -> tuple[list[dict[str, str]], list[str]]:
    """Extract Lean-like inline-code names with left-to-right inheritance."""

    occurrences: list[dict[str, str]] = []
    ignored: list[str] = []
    inherited_namespace: str | None = None
    for raw in INLINE_CODE_RE.findall(cell):
        candidate = raw.strip()
        if LEAN_IDENTIFIER_RE.fullmatch(candidate) is None:
            ignored.append(candidate)
            continue
        if "." in candidate:
            resolved = candidate
            inherited_namespace = candidate.rsplit(".", 1)[0]
            mode = "qualified"
            inherited_from = ""
        elif inherited_namespace is not None:
            resolved = f"{inherited_namespace}.{candidate}"
            mode = "namespace_inherited"
            inherited_from = inherited_namespace
        else:
            resolved = candidate
            mode = "bare_global"
            inherited_from = ""
        occurrences.append(
            {
                "raw": candidate,
                "resolved": resolved,
                "mode": mode,
                "inherited_from": inherited_from,
            }
        )
    return occurrences, ignored


def _endpoint_names(occurrences: Sequence[Mapping[str, str]]) -> list[str]:
    return sorted({occurrence["resolved"] for occurrence in occurrences})


def _endpoint_modes(occurrences: Sequence[Mapping[str, str]]) -> list[str]:
    return sorted({occurrence["mode"] for occurrence in occurrences})


def _status_tokens(cell: str) -> list[str]:
    return sorted(set(STATUS_TOKEN_RE.findall(cell)))


def parse_readme() -> list[dict[str, object]]:
    lines = README.read_text(encoding="utf-8").splitlines()
    try:
        start = lines.index("## Book → Lean correspondence")
    except ValueError as error:
        raise InventoryError("README correspondence heading is missing") from error

    chapter: str | None = None
    table_ready = False
    rows: list[dict[str, object]] = []
    for index in range(start + 1, len(lines)):
        line = lines[index]
        chapter_match = re.match(
            r"^###\s+(Appetizer|Chapter\s+[1-9])\b", line
        )
        if chapter_match is not None:
            chapter = canonical_chapter(chapter_match.group(1))
            table_ready = False
            continue
        if not line.strip().startswith("|"):
            continue
        cells = split_markdown_row(line)
        if tuple(cells) == README_HEADER:
            if chapter is None:
                raise InventoryError(
                    f"README:{index + 1}: table has no chapter heading"
                )
            table_ready = True
            continue
        if _is_separator(cells):
            continue
        if not table_ready:
            continue
        if len(cells) != len(README_HEADER):
            raise InventoryError(
                f"README:{index + 1}: correspondence row has {len(cells)} cells"
            )
        book_ref, result, declaration_cell, final_module = cells
        primary_kind, kinds = classify_book_ref(book_ref)
        endpoints, ignored = resolve_endpoint_cell(declaration_cell)
        if not endpoints:
            raise InventoryError(
                f"README:{index + 1}: no endpoint in {declaration_cell!r}"
            )
        row_id = _stable_id("readme", chapter, book_ref, result)
        rows.append(
            {
                "row_id": row_id,
                "source_document": README.relative_to(ROOT).as_posix(),
                "source_section": "Book → Lean correspondence",
                "source_line": index + 1,
                "chapter": chapter,
                "book_ref": book_ref,
                "book_ref_match_key": _typographic_normalize(book_ref),
                "book_ref_primary_kind": primary_kind,
                "book_ref_kinds": kinds,
                "result": result,
                "lean_declaration_cell": declaration_cell,
                "endpoint_occurrences": endpoints,
                "endpoint_names": _endpoint_names(endpoints),
                "endpoint_resolution_modes": _endpoint_modes(endpoints),
                "ignored_endpoint_code_spans": ignored,
                "final_module": final_module,
                "source_status_cell": "",
                "source_status_class": "VERIFIED",
                "status_tokens": ["VERIFIED"],
                "status_classification_basis": (
                    "README section prose states all 611 rows are verified; "
                    "the four-column table has no row status column"
                ),
                "coverage_bucket": "publication_verified",
            }
        )
    return rows


def _review_lines() -> list[str]:
    observed = hashlib.sha256(REVIEW.read_bytes()).hexdigest()
    if observed != EXPECTED_REVIEW_SHA256:
        raise InventoryError(
            "frozen REVIEW archive hash mismatch: "
            f"{observed} != {EXPECTED_REVIEW_SHA256}"
        )
    return REVIEW.read_text(encoding="utf-8").splitlines()


def _review_table_between(
    lines: Sequence[str],
    start_heading: str,
    end_heading: str,
    header: Sequence[str],
) -> list[tuple[int, list[str]]]:
    try:
        start = lines.index(start_heading)
        end = lines.index(end_heading, start + 1)
    except ValueError as error:
        raise InventoryError(
            f"missing REVIEW table bounds {start_heading!r} / {end_heading!r}"
        ) from error
    found_header = False
    rows: list[tuple[int, list[str]]] = []
    for index in range(start + 1, end):
        line = lines[index]
        if not line.strip().startswith("|"):
            continue
        cells = split_markdown_row(line)
        if tuple(cells) == tuple(header):
            found_header = True
            continue
        if not found_header or _is_separator(cells):
            continue
        if len(cells) != len(header):
            raise InventoryError(
                f"REVIEW:{index + 1}: expected {len(header)} cells, "
                f"found {len(cells)}"
            )
        rows.append((index + 1, cells))
    if not found_header or not rows:
        raise InventoryError(f"no rows found between {start_heading!r} and peer")
    return rows


def _base_review_row(
    *,
    component: str,
    line: int,
    chapter: str,
    book_ref: str,
    result: str,
    status_cell: str,
    status_class: str,
    status_basis: str,
    coverage_bucket: str,
    evidence_cell: str,
    file_evidence: str,
    note: str,
) -> dict[str, object]:
    primary_kind, kinds = classify_book_ref(book_ref)
    occurrences, ignored = resolve_endpoint_cell(evidence_cell)
    return {
        "row_id": _stable_id(
            "census", component, chapter, book_ref, result
        ),
        "census_component": component,
        "source_document": REVIEW.relative_to(ROOT).as_posix(),
        "source_line": line,
        "chapter": chapter,
        "book_ref": book_ref,
        "book_ref_match_key": _typographic_normalize(book_ref),
        "book_ref_primary_kind": primary_kind,
        "book_ref_kinds": kinds,
        "result": result,
        "source_status_cell": status_cell,
        "source_status_class": status_class,
        "status_tokens": _status_tokens(
            f"{status_cell} {status_class} {note}"
        ),
        "status_classification_basis": status_basis,
        "coverage_bucket": coverage_bucket,
        "evidence_cell": evidence_cell,
        "file_evidence": file_evidence,
        "note": note,
        "direct_endpoint_occurrences": occurrences,
        "direct_endpoint_names": _endpoint_names(occurrences),
        "direct_endpoint_resolution_modes": _endpoint_modes(occurrences),
        "ignored_evidence_code_spans": ignored,
        "readme_match_ids": [],
        "readme_exact_endpoint_names": [],
        "endpoint_names": _endpoint_names(occurrences),
        "endpoint_linkage": "direct" if occurrences else "none",
        "faithful_historical_flag_ids": [],
    }


def parse_review() -> tuple[
    list[dict[str, object]],
    list[dict[str, object]],
    list[dict[str, object]],
    dict[str, object],
]:
    lines = _review_lines()
    gap_raw = _review_table_between(
        lines,
        REVIEW_GAP_HEADING,
        REVIEW_APPENDIX_HEADING,
        GAP_HEADER,
    )
    appendix_raw = _review_table_between(
        lines,
        REVIEW_APPENDIX_HEADING,
        REVIEW_FROZEN_HEADING,
        APPENDIX_HEADER,
    )
    frozen_raw = _review_table_between(
        lines,
        REVIEW_FROZEN_HEADING,
        REVIEW_AFTER_FROZEN_HEADING,
        FROZEN_HEADER,
    )

    extras: list[dict[str, object]] = []
    frozen_rows: list[dict[str, object]] = []
    seen_extras: Counter[tuple[str, str]] = Counter()
    for line, cells in frozen_raw:
        chapter = canonical_chapter(cells[0])
        book_ref, status_cell, result, note = cells[1:]
        key = (chapter, book_ref)
        if key in FROZEN_DISPLAY_ONLY_EXTRAS:
            seen_extras[key] += 1
            primary_kind, kinds = classify_book_ref(book_ref)
            extras.append(
                {
                    "row_id": _stable_id(
                        "display-extra", chapter, book_ref, result
                    ),
                    "source_document": REVIEW.relative_to(ROOT).as_posix(),
                    "source_line": line,
                    "chapter": chapter,
                    "book_ref": book_ref,
                    "book_ref_primary_kind": primary_kind,
                    "book_ref_kinds": kinds,
                    "source_status_cell": status_cell,
                    "result": result,
                    "note": note,
                    "exclusion_reason": (
                        "REVIEW section prose identifies seven consolidated "
                        "post-correction display entries beyond the 717 frozen "
                        "rows: six Appetizer entries and Proposition 7.5.2"
                    ),
                }
            )
            continue
        frozen_rows.append(
            _base_review_row(
                component="frozen_proved_or_stronger",
                line=line,
                chapter=chapter,
                book_ref=book_ref,
                result=result,
                status_cell=status_cell,
                status_class=status_cell,
                status_basis=(
                    "Audit class cell in the frozen proved/stronger table; "
                    "FORMALIZED and STRONGER both belong to the 717 current "
                    "core-formalized inputs"
                ),
                coverage_bucket="core_formalized",
                evidence_cell="",
                file_evidence="",
                note=note,
            )
        )
    if set(seen_extras) != FROZEN_DISPLAY_ONLY_EXTRAS or any(
        count != 1 for count in seen_extras.values()
    ):
        raise InventoryError(
            "the seven declared frozen display-only entries were not found "
            "exactly once"
        )

    appendix_rows: list[dict[str, object]] = []
    for line, cells in appendix_raw:
        chapter = canonical_chapter(cells[0])
        book_ref, result, evidence, file_evidence, note = cells[1:]
        statuses = APPENDIX_STATUS_RE.findall(note)
        if len(set(statuses)) > 1:
            raise InventoryError(
                f"REVIEW:{line}: ambiguous Appendix statuses {statuses}"
            )
        if statuses:
            status_class = statuses[0]
            status_basis = "explicit final-status token in the row note"
        elif chapter == "Chapter 9":
            status_class = "APPENDIX-PROVED"
            status_basis = (
                "Appendix-table preamble explicitly says every Chapter 9 row "
                "has final isolated status APPENDIX-PROVED"
            )
        else:
            raise InventoryError(
                f"REVIEW:{line}: Appendix row lacks an explicit status and "
                "is not covered by the Chapter 9 preamble"
            )
        bucket = (
            "appendix_unresolved_or_deferred"
            if "UNRESOLVED" in status_class
            else "appendix_proved"
        )
        appendix_rows.append(
            _base_review_row(
                component="original_appendix_owned",
                line=line,
                chapter=chapter,
                book_ref=book_ref,
                result=result,
                status_cell=note,
                status_class=status_class,
                status_basis=status_basis,
                coverage_bucket=bucket,
                evidence_cell=evidence,
                file_evidence=file_evidence,
                note=note,
            )
        )

    all_gap_rows: list[dict[str, object]] = []
    accepted_gap_rows: list[dict[str, object]] = []
    for line, cells in gap_raw:
        chapter = canonical_chapter(cells[0])
        book_ref, disposition, result, evidence, file_evidence, note = cells[1:]
        if disposition == "FORMALIZED":
            status_class = "FORMALIZED"
            status_basis = "Validated disposition cell"
            bucket = "core_formalized"
        elif disposition == "REJECTED":
            status_class = "REJECTED"
            status_basis = "Validated disposition cell"
            bucket = "rejected_outside_valid_census"
        elif disposition == "IN-APPENDIX":
            explicit = APPENDIX_STATUS_RE.findall(note)
            if len(set(explicit)) > 1:
                raise InventoryError(
                    f"REVIEW:{line}: ambiguous accepted-gap Appendix status"
                )
            if explicit:
                status_class = explicit[0]
                status_basis = (
                    "IN-APPENDIX disposition plus explicit final-status token"
                )
            elif (chapter, book_ref) in HISTORICAL_DEFERRED_GAP_ROWS:
                status_class = HISTORICAL_DEFERRED_GAP_ROWS[
                    (chapter, book_ref)
                ]
                status_basis = (
                    "IN-APPENDIX disposition plus the archive's immediately "
                    "following exhaustive five-row unresolved list"
                )
            else:
                status_class = "APPENDIX-PROVED"
                status_basis = (
                    "IN-APPENDIX disposition with no unresolved token; the "
                    "newly-deferred section explicitly classifies Eq. (5.2) "
                    "as APPENDIX-PROVED"
                )
            bucket = (
                "appendix_unresolved_or_deferred"
                if "UNRESOLVED" in status_class
                else "appendix_proved"
            )
        else:
            raise InventoryError(
                f"REVIEW:{line}: unknown gap disposition {disposition!r}"
            )
        row = _base_review_row(
            component="accepted_gap"
            if disposition != "REJECTED"
            else "rejected_gap",
            line=line,
            chapter=chapter,
            book_ref=book_ref,
            result=result,
            status_cell=disposition,
            status_class=status_class,
            status_basis=status_basis,
            coverage_bucket=bucket,
            evidence_cell=evidence,
            file_evidence=file_evidence,
            note=note,
        )
        all_gap_rows.append(row)
        if disposition != "REJECTED":
            accepted_gap_rows.append(row)

    census = [*frozen_rows, *appendix_rows, *accepted_gap_rows]
    census.sort(
        key=lambda row: (
            CHAPTER_ORDER[str(row["chapter"])],
            _typographic_normalize(str(row["book_ref"])),
            str(row["census_component"]),
            int(row["source_line"]),
        )
    )
    metadata = {
        "raw_frozen_display_rows": len(frozen_raw),
        "frozen_display_only_extras": len(extras),
        "frozen_census_rows": len(frozen_rows),
        "original_appendix_rows": len(appendix_rows),
        "raw_gap_rows": len(all_gap_rows),
        "accepted_gap_rows": len(accepted_gap_rows),
        "rejected_gap_rows": sum(
            row["coverage_bucket"] == "rejected_outside_valid_census"
            for row in all_gap_rows
        ),
        "derivation": "724 - 7 + 67 + (89 - 35) = 838",
        "record_scope": (
            "Authenticated pre-final-correction REVIEW_NOTES input rows; "
            "the live Pass 07 REVIEW_NOTES publishes the explicit 66/4 "
            "current projection without mutating this frozen 65/5 census"
        ),
        "frozen_review_sha256": EXPECTED_REVIEW_SHA256,
        "live_review_document": LIVE_REVIEW.relative_to(ROOT).as_posix(),
    }
    return census, all_gap_rows, extras, metadata


def _replace_direct_evidence(
    row: dict[str, object],
    *,
    evidence_cell: str,
    file_evidence: str,
) -> None:
    occurrences, ignored = resolve_endpoint_cell(evidence_cell)
    row["evidence_cell"] = evidence_cell
    row["file_evidence"] = file_evidence
    row["direct_endpoint_occurrences"] = occurrences
    row["direct_endpoint_names"] = _endpoint_names(occurrences)
    row["direct_endpoint_resolution_modes"] = _endpoint_modes(occurrences)
    row["ignored_evidence_code_spans"] = ignored


def project_current_census(
    frozen_census: Sequence[dict[str, object]],
) -> tuple[list[dict[str, object]], dict[str, object]]:
    """Apply the completed-interface-removal overlay to the frozen census.

    The authenticated 838 rows remain immutable historical evidence.  This
    function deep-copies them, removes the three conclusions no longer
    represented by the current source-facing API, narrows the aggregate
    Exercise 8.39 row to its proved reverse half, and records the completed
    Brownian proof.  Stable row IDs intentionally preserve the projection's
    provenance back to the frozen census.
    """

    frozen_by_id = {
        str(row["row_id"]): row
        for row in frozen_census
    }
    required = {
        *CURRENT_REMOVED_ROW_IDS,
        CURRENT_EXERCISE_8_39_ROW_ID,
        CURRENT_BROWNIAN_ROW_ID,
    }
    missing = sorted(required - set(frozen_by_id))
    if missing:
        raise InventoryError(
            f"current census projection lacks frozen source rows: {missing}"
        )

    current = [
        copy.deepcopy(row)
        for row in frozen_census
        if str(row["row_id"]) not in CURRENT_REMOVED_ROW_IDS
    ]
    current_by_id = {
        str(row["row_id"]): row
        for row in current
    }

    exercise = current_by_id[CURRENT_EXERCISE_8_39_ROW_ID]
    exercise["book_ref"] = "Exercise 8.39(b)"
    exercise["book_ref_match_key"] = _typographic_normalize(
        str(exercise["book_ref"])
    )
    primary_kind, kinds = classify_book_ref(str(exercise["book_ref"]))
    exercise["book_ref_primary_kind"] = primary_kind
    exercise["book_ref_kinds"] = kinds
    exercise["result"] = "Sharp Gaussian Chevet reverse inequality."
    exercise["source_status_cell"] = "FORMALIZED"
    exercise["source_status_class"] = "FORMALIZED"
    exercise["status_tokens"] = ["FORMALIZED"]
    exercise["status_classification_basis"] = (
        "Current-tree projection after removal of the unproved arbitrary "
        "upper half; the retained part (b) theorem is unconditional"
    )
    exercise["coverage_bucket"] = "core_formalized"
    exercise["note"] = (
        "The current API retains only Book Exercise 8.39(b), proved "
        "unconditionally by the arbitrary-set reverse Chevet theorem."
    )
    _replace_direct_evidence(
        exercise,
        evidence_cell=f"`{CURRENT_EXERCISE_8_39_ENDPOINT}`",
        file_evidence="`HighDimensionalProbability/Chapter8_Chaining.lean`",
    )

    brownian = current_by_id[CURRENT_BROWNIAN_ROW_ID]
    brownian["source_status_class"] = "APPENDIX-PROVED"
    brownian["status_tokens"] = ["APPENDIX-PROVED", "IN-APPENDIX"]
    brownian["status_classification_basis"] = (
        "Current-tree projection records the completed source-faithful "
        "Brownian reflection proof"
    )
    brownian["coverage_bucket"] = "appendix_proved"
    brownian["note"] = (
        "The isolated appendix proves the finite-subfamily Brownian "
        "reflection interface and the expected-maximum identity."
    )
    _replace_direct_evidence(
        brownian,
        evidence_cell=f"`{CURRENT_BROWNIAN_ENDPOINT}`",
        file_evidence=(
            "`HighDimensionalProbability/Appendix/BrownianReflection.lean`"
        ),
    )

    current.sort(
        key=lambda row: (
            CHAPTER_ORDER[str(row["chapter"])],
            _typographic_normalize(str(row["book_ref"])),
            str(row["census_component"]),
            int(row["source_line"]),
        )
    )
    metadata = {
        "record_scope": (
            "Current active census projected mechanically from the immutable "
            "authenticated 838-row archive after completed conditional-"
            "interface removals"
        ),
        "frozen_source_artifact": (
            "HighDimensionalProbability/Verification/inventory/"
            "review_census_838.tsv"
        ),
        "frozen_row_count": len(frozen_census),
        "removed_row_ids": sorted(CURRENT_REMOVED_ROW_IDS),
        "transformed_row_ids": {
            CURRENT_EXERCISE_8_39_ROW_ID: (
                "Exercise 8.39(a--b) deferred -> Exercise 8.39(b) "
                "core_formalized"
            ),
            CURRENT_BROWNIAN_ROW_ID: (
                "appendix_unresolved_or_deferred -> appendix_proved"
            ),
        },
        "derivation": "838 - 3 removed conclusions = 835",
    }
    return current, metadata


def _integer_cell(cell: str) -> int:
    cleaned = _strip_emphasis(cell).replace(",", "").strip()
    if not re.fullmatch(r"\d+", cleaned):
        raise InventoryError(f"expected integer table cell, found {cell!r}")
    return int(cleaned)


def _number_tokens(book_ref: str) -> set[str]:
    normalized = _typographic_normalize(_strip_emphasis(book_ref))
    return set(
        re.findall(r"(?<!\d)([0-9]+\.[0-9]+(?:\.[0-9]+)?)(?!\d)", normalized)
    )


def parse_faithful(
    census: Sequence[dict[str, object]],
) -> tuple[list[dict[str, object]], dict[str, object]]:
    lines = FAITHFUL.read_text(encoding="utf-8").splitlines()
    census_summary_raw = table_under_heading(
        lines,
        "## 4. Definitive comprehensiveness census",
        FAITHFUL_CENSUS_HEADER,
    )
    summary_rows: list[dict[str, int | str]] = []
    for line, cells in census_summary_raw:
        chapter_cell = _strip_emphasis(cells[0])
        chapter = (
            "Total"
            if chapter_cell == "Total"
            else canonical_chapter(chapter_cell)
        )
        values = [_integer_cell(cell) for cell in cells[1:]]
        summary_rows.append(
            {
                "source_line": line,
                "chapter": chapter,
                **dict(zip(FAITHFUL_CENSUS_HEADER[1:], values)),
            }
        )

    partial_raw = table_under_heading(
        lines,
        "### 4.1 Full partial list",
        FAITHFUL_PARTIAL_HEADER,
    )
    appendix_raw = table_under_heading(
        lines,
        "### 4.3 Full appendix-unresolved/deferred list",
        FAITHFUL_APPENDIX_HEADER,
    )

    flags: list[dict[str, object]] = []
    for historical_status, raw_rows in (
        ("HISTORICAL-CORE-PARTIAL", partial_raw),
        ("HISTORICAL-APPENDIX-UNRESOLVED", appendix_raw),
    ):
        for line, cells in raw_rows:
            chapter = canonical_chapter(cells[0])
            book_ref = _strip_emphasis(cells[1])
            detail = cells[2]
            primary_kind, kinds = classify_book_ref(book_ref)
            exact_key = _typographic_normalize(
                re.sub(r"^Book\s+", "", book_ref, flags=re.IGNORECASE)
            )
            exact_candidates = [
                row
                for row in census
                if row["chapter"] == chapter
                and row["book_ref_match_key"] == exact_key
            ]
            if exact_candidates:
                candidates = exact_candidates
                match_mode = "typographic_exact_after_Book_prefix"
            else:
                numbers = _number_tokens(book_ref)
                number_candidates = [
                    row
                    for row in census
                    if row["chapter"] == chapter
                    and numbers
                    and numbers.intersection(
                        _number_tokens(str(row["book_ref"]))
                    )
                ]
                same_kind = [
                    row
                    for row in number_candidates
                    if primary_kind in row["book_ref_kinds"]
                ]
                candidates = same_kind or number_candidates
                match_mode = (
                    (
                        "chapter_plus_reference_number_and_kind_candidates"
                        if same_kind
                        else "chapter_plus_reference_number_candidates"
                    )
                    if candidates
                    else "unmatched"
                )
            flag_id = _stable_id(
                "faithful-history", historical_status, chapter, book_ref
            )
            flags.append(
                {
                    "row_id": flag_id,
                    "source_document": FAITHFUL.relative_to(ROOT).as_posix(),
                    "source_line": line,
                    "chapter": chapter,
                    "book_ref": book_ref,
                    "historical_status": historical_status,
                    "historical_detail": detail,
                    "book_ref_primary_kind": primary_kind,
                    "book_ref_kinds": kinds,
                    "candidate_census_ids": sorted(
                        str(row["row_id"]) for row in candidates
                    ),
                    "census_match_mode": match_mode,
                }
            )

    by_census_id: dict[str, list[str]] = defaultdict(list)
    for flag in flags:
        for census_id in flag["candidate_census_ids"]:
            by_census_id[str(census_id)].append(str(flag["row_id"]))
    for row in census:
        row["faithful_historical_flag_ids"] = sorted(
            by_census_id.get(str(row["row_id"]), [])
        )

    total_rows = [
        row for row in summary_rows if row["chapter"] == "Total"
    ]
    if len(total_rows) != 1:
        raise InventoryError("FAITHFUL census summary must have one Total row")
    metadata = {
        "record_scope": (
            "FAITHFUL_PROOFREAD_REPORT body is explicitly marked historical "
            "by its Pass 07 action notice"
        ),
        "summary_rows": summary_rows,
        "historical_flag_row_count": len(flags),
        "historical_partial_row_count": sum(
            flag["historical_status"] == "HISTORICAL-CORE-PARTIAL"
            for flag in flags
        ),
        "historical_appendix_unresolved_row_count": sum(
            flag["historical_status"]
            == "HISTORICAL-APPENDIX-UNRESOLVED"
            for flag in flags
        ),
    }
    return flags, metadata


def link_readme(
    census: Sequence[dict[str, object]],
    readme_rows: Sequence[dict[str, object]],
) -> None:
    by_ref: dict[tuple[str, str], list[dict[str, object]]] = defaultdict(list)
    for row in readme_rows:
        by_ref[
            (str(row["chapter"]), str(row["book_ref_match_key"]))
        ].append(row)
    duplicate_keys = [key for key, rows in by_ref.items() if len(rows) > 1]
    if duplicate_keys:
        raise InventoryError(
            f"README chapter/reference match keys are not unique: "
            f"{duplicate_keys[:5]}"
        )
    for row in census:
        matches = by_ref.get(
            (str(row["chapter"]), str(row["book_ref_match_key"])), []
        )
        match_ids = sorted(str(match["row_id"]) for match in matches)
        matched_endpoints = sorted(
            {
                str(endpoint)
                for match in matches
                for endpoint in match["endpoint_names"]
            }
        )
        direct = set(str(name) for name in row["direct_endpoint_names"])
        row["readme_match_ids"] = match_ids
        row["readme_exact_endpoint_names"] = matched_endpoints
        row["endpoint_names"] = sorted(direct.union(matched_endpoints))
        if direct and matches:
            row["endpoint_linkage"] = "direct_and_readme_exact_ref"
        elif direct:
            row["endpoint_linkage"] = "direct"
        elif matches:
            row["endpoint_linkage"] = "readme_exact_ref"
        else:
            row["endpoint_linkage"] = "none"


def build_endpoint_union(
    readme_rows: Sequence[dict[str, object]],
    census: Sequence[dict[str, object]],
) -> tuple[list[dict[str, object]], list[dict[str, object]]]:
    """Union direct evidence occurrences, without duplicating README links."""

    occurrences: list[dict[str, object]] = []
    for source_kind, rows, occurrence_key in (
        ("readme_publication", readme_rows, "endpoint_occurrences"),
        ("review_census_direct", census, "direct_endpoint_occurrences"),
    ):
        for row in rows:
            for occurrence in row[occurrence_key]:
                occurrences.append(
                    {
                        "endpoint": occurrence["resolved"],
                        "raw": occurrence["raw"],
                        "resolution_mode": occurrence["mode"],
                        "inherited_from": occurrence["inherited_from"],
                        "source_kind": source_kind,
                        "source_row_id": row["row_id"],
                        "chapter": row["chapter"],
                        "book_ref": row["book_ref"],
                    }
                )
    occurrences.sort(
        key=lambda row: (
            str(row["endpoint"]),
            str(row["source_kind"]),
            str(row["source_row_id"]),
            str(row["raw"]),
        )
    )

    grouped: dict[str, list[dict[str, object]]] = defaultdict(list)
    for occurrence in occurrences:
        grouped[str(occurrence["endpoint"])].append(occurrence)
    union: list[dict[str, object]] = []
    for endpoint, endpoint_occurrences in sorted(grouped.items()):
        namespace = endpoint.rsplit(".", 1)[0] if "." in endpoint else ""
        union.append(
            {
                "endpoint": endpoint,
                "namespace": namespace,
                "source_kinds": sorted(
                    {
                        str(occurrence["source_kind"])
                        for occurrence in endpoint_occurrences
                    }
                ),
                "source_row_ids": sorted(
                    {
                        str(occurrence["source_row_id"])
                        for occurrence in endpoint_occurrences
                    }
                ),
                "chapters": sorted(
                    {
                        str(occurrence["chapter"])
                        for occurrence in endpoint_occurrences
                    },
                    key=CHAPTER_ORDER.get,
                ),
                "book_refs": sorted(
                    {
                        str(occurrence["book_ref"])
                        for occurrence in endpoint_occurrences
                    }
                ),
                "resolution_modes": sorted(
                    {
                        str(occurrence["resolution_mode"])
                        for occurrence in endpoint_occurrences
                    }
                ),
                "occurrence_count": len(endpoint_occurrences),
            }
        )
    return union, occurrences


def _line_offset(text: str, line: int) -> int:
    if line <= 1:
        return 0
    offset = 0
    for index, item in enumerate(text.splitlines(keepends=True), start=1):
        if index == line:
            return offset
        offset += len(item)
    return len(text)


def _preceding_doc_comment(text: str, offset: int) -> str:
    prefix = text[:offset]
    end = prefix.rfind("-/")
    if end < 0:
        return ""
    end += 2
    between = prefix[end:]
    # Allow whitespace and one-line attributes between docstring and command.
    if re.sub(r"(?m)^\s*@\[[^\r\n]*\]\s*$", "", between).strip():
        return ""
    start = prefix.rfind("/--", 0, end)
    return "" if start < 0 else prefix[start:end]


def _declaration_namespace(text: str, line: int) -> str:
    code, diagnostics = mask_lean_noncode(text)
    if diagnostics:
        raise InventoryError(
            f"exercise leaf has lexer diagnostics before namespace extraction: "
            f"{diagnostics}"
        )
    prefix = code[: _line_offset(text, line)]
    namespaces = re.findall(
        r"(?m)^[ \t]*namespace[ \t]+"
        r"(HDP\.Chapter[1-9](?:\.[A-Za-z_][A-Za-z0-9_']*)*)[ \t]*$",
        prefix,
    )
    if not namespaces:
        raise InventoryError(
            f"no HDP.Chapter namespace found before declaration line {line}"
        )
    return namespaces[-1]


def _round10_semantic_baseline_insertions() -> dict[str, list[int]]:
    """Return pure-insertion lines used to preserve the frozen V6 seed frame.

    Exercise declaration IDs historically included physical source lines.  On
    the authenticated Round 10 successor, compute those IDs with the semantic
    baseline lines so docstrings cannot silently resample the review frame.
    """

    rendered, digest = build_manifest()
    if (
        not SOURCE_MANIFEST.is_file()
        or SOURCE_MANIFEST.read_text(encoding="utf-8") != rendered
    ):
        raise InventoryError("source manifest is stale for V6 sampling")
    if digest == SEMANTIC_BASELINE_DIGEST:
        return {}
    if digest != ROUND10_SOURCE_DIGEST:
        try:
            certified_digest = require_reorganization_certificate()
        except (OSError, RuntimeError, TypeError, ValueError) as error:
            raise InventoryError(
                f"exercise-reorganization certificate failed: {error}"
            ) from error
        if certified_digest != digest:
            raise InventoryError(
                "exercise-reorganization certificate identifies another source "
                f"digest: {certified_digest} != {digest}"
            )

    if not ROUND10_DELTA_LOG.is_file():
        raise InventoryError("Round 10 docstring-delta certificate is missing")
    delta = ROUND10_DELTA_LOG.read_text(encoding="utf-8", errors="replace")
    required = (
        f"baseline_digest: {SEMANTIC_BASELINE_DIGEST}",
        f"current_digest: {ROUND10_SOURCE_DIGEST}",
        "file_walk_lean_files_compared: 222",
        "root_aggregator_compared: true",
        "changed_lean_files: 25",
        "one_line_docstrings_added: 97",
        "blank_lines_replaced: 1",
        "nonblank_nondoc_source_changes: 0",
        "ROUND10_DOCSTRING_DELTA: PASS",
    )
    missing = [fragment for fragment in required if fragment not in delta]
    lines = delta.splitlines()
    if missing or lines[-1:] != ["exit_code: 0"]:
        raise InventoryError(
            "Round 10 docstring-delta certificate is incomplete: "
            + ", ".join(missing or ["final exit_code: 0"])
        )

    header = "path\tline\treplaced_blank\tdocstring"
    try:
        start = lines.index(header) + 1
        stop = lines.index("ROUND10_DOCSTRING_DELTA: PASS", start)
    except ValueError as error:
        raise InventoryError(
            "Round 10 docstring-delta detail table is malformed"
        ) from error

    insertions: dict[str, list[int]] = defaultdict(list)
    addition_count = 0
    replacement_count = 0
    changed_paths: set[str] = set()
    for record in lines[start:stop]:
        if not record:
            continue
        cells = record.split("\t", 3)
        if len(cells) != 4 or cells[2] not in {"true", "false"}:
            raise InventoryError(
                f"malformed Round 10 docstring-delta record: {record!r}"
            )
        path_text, line_text, replaced_text, docstring = cells
        try:
            line = int(line_text)
        except ValueError as error:
            raise InventoryError(
                f"noninteger Round 10 docstring line: {record!r}"
            ) from error
        current_path_text = old_to_new_exercise_path(path_text)
        source = ROOT / current_path_text
        if not source.is_file():
            raise InventoryError(
                f"Round 10 source path is missing after reorganization: "
                f"{path_text} -> {current_path_text}"
            )
        source_lines = source.read_text(encoding="utf-8").splitlines()
        if not 1 <= line <= len(source_lines):
            raise InventoryError(f"Round 10 source line is invalid: {record!r}")
        if source_lines[line - 1].strip() != docstring:
            raise InventoryError(
                f"Round 10 docstring no longer matches source: {path_text}:{line}"
            )
        addition_count += 1
        changed_paths.add(current_path_text)
        if replaced_text == "true":
            replacement_count += 1
        else:
            insertions[current_path_text].append(line)

    if (addition_count, len(changed_paths), replacement_count) != (97, 25, 1):
        raise InventoryError(
            "Round 10 docstring-delta detail census changed: "
            f"additions={addition_count}, files={len(changed_paths)}, "
            f"blank_replacements={replacement_count}"
        )
    for path_lines in insertions.values():
        path_lines.sort()
    return dict(insertions)


def parse_exercise_leaf_declarations() -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    round10_insertions = _round10_semantic_baseline_insertions()
    for chapter_number in range(1, 10):
        chapter = f"Chapter {chapter_number}"
        directory = HDP / "Exercise" / f"Chapter{chapter_number}"
        paths = sorted(directory.glob("*.lean"))
        if not paths:
            raise InventoryError(f"no exercise leaves found for {chapter}")
        for path in paths:
            text = path.read_text(encoding="utf-8")
            for declaration in extract_declarations(path):
                namespace = _declaration_namespace(text, declaration.start_line)
                local_name = declaration.name
                endpoint = (
                    local_name
                    if local_name.startswith("HDP.")
                    else f"{namespace}.{local_name}"
                )
                doc = _preceding_doc_comment(
                    text, _line_offset(text, declaration.start_line)
                )
                book_tags = [
                    _clean_markdown_text(tag)
                    for tag in re.findall(
                        r"\*\*Book\s+([^*]+)\*\*", doc, flags=re.IGNORECASE
                    )
                ]
                candidate = local_name.startswith("exercise_") or any(
                    tag.casefold().startswith("exercise")
                    for tag in book_tags
                )
                relative = path.relative_to(ROOT).as_posix()
                semantic_start_line = declaration.start_line - sum(
                    insertion_line < declaration.start_line
                    for insertion_line in round10_insertions.get(relative, ())
                )
                if semantic_start_line < 1:
                    raise InventoryError(
                        f"invalid semantic source anchor: {relative}:"
                        f"{declaration.start_line} -> {semantic_start_line}"
                    )
                row_id = _stable_id(
                    "exercise-decl",
                    new_to_old_exercise_path(relative),
                    semantic_start_line,
                    endpoint,
                )
                rows.append(
                    {
                        "declaration_id": row_id,
                        "chapter": chapter,
                        "path": relative,
                        "module": declaration.module,
                        "namespace": namespace,
                        "kind": declaration.kind,
                        "local_name": local_name,
                        "endpoint": endpoint,
                        "start_line": declaration.start_line,
                        "end_line": declaration.end_line,
                        "parsed": declaration.parsed,
                        "statement": declaration.statement,
                        "conclusion": declaration.conclusion,
                        "book_tags": book_tags,
                        "is_exercise_sample_candidate": candidate,
                    }
                )
    rows.sort(
        key=lambda row: (
            CHAPTER_ORDER[str(row["chapter"])],
            str(row["path"]),
            int(row["start_line"]),
            str(row["endpoint"]),
        )
    )
    return rows


def _sample_hash(seed: str, chapter: str, target_id: str) -> str:
    payload = f"{seed}\0{chapter}\0{target_id}".encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def build_sampling_plan(
    exercise_rows: Sequence[dict[str, object]],
    census: Sequence[dict[str, object]],
) -> tuple[
    list[dict[str, object]],
    list[dict[str, object]],
    list[dict[str, object]],
]:
    exercise_samples: list[dict[str, object]] = []
    for chapter in LEAN_CHAPTERS:
        candidates = [
            row
            for row in exercise_rows
            if row["chapter"] == chapter
            and row["is_exercise_sample_candidate"]
        ]
        ranked = sorted(
            candidates,
            key=lambda row: (
                _sample_hash(
                    EXERCISE_SAMPLE_SEED,
                    chapter,
                    str(row["declaration_id"]),
                ),
                str(row["declaration_id"]),
            ),
        )
        for rank, row in enumerate(
            ranked[:EXERCISE_SAMPLE_SIZE], start=1
        ):
            exercise_samples.append(
                {
                    "sample_kind": "exercise_leaf_close_read",
                    "chapter": chapter,
                    "rank": rank,
                    "quota": EXERCISE_SAMPLE_SIZE,
                    "seed": EXERCISE_SAMPLE_SEED,
                    "sample_hash": _sample_hash(
                        EXERCISE_SAMPLE_SEED,
                        chapter,
                        str(row["declaration_id"]),
                    ),
                    "target_id": row["declaration_id"],
                    "target_kind": row["kind"],
                    "path": row["path"],
                    "line": row["start_line"],
                    "endpoint": row["endpoint"],
                    "book_ref": "; ".join(row["book_tags"]),
                    "result": row["statement"],
                    "coverage_bucket": "exercise_leaf",
                    "semantic_verdict": "",
                    "selection_instruction": (
                        "Close-read this source statement; selection is "
                        "deterministic and is not a semantic verdict."
                    ),
                }
            )

    ok_ranking: list[dict[str, object]] = []
    ok_head: list[dict[str, object]] = []
    for chapter in CHAPTERS:
        candidates = [
            row
            for row in census
            if row["chapter"] == chapter
            and "exercise" not in row["book_ref_kinds"]
            and row["coverage_bucket"]
            in {"core_formalized", "appendix_proved"}
            and row["source_status_class"] != "STRONGER"
        ]
        ranked = sorted(
            candidates,
            key=lambda row: (
                _sample_hash(
                    OK_SAMPLE_SEED, chapter, str(row["row_id"])
                ),
                str(row["row_id"]),
            ),
        )
        for rank, row in enumerate(ranked, start=1):
            sample = {
                "sample_kind": "ok_row_candidate_order",
                "chapter": chapter,
                "rank": rank,
                "quota": OK_SAMPLE_SIZE,
                "seed": OK_SAMPLE_SEED,
                "sample_hash": _sample_hash(
                    OK_SAMPLE_SEED, chapter, str(row["row_id"])
                ),
                "target_id": row["row_id"],
                "target_kind": row["book_ref_primary_kind"],
                "path": row["source_document"],
                "line": row["source_line"],
                "endpoint": "; ".join(row["endpoint_names"]),
                "book_ref": row["book_ref"],
                "result": row["result"],
                "coverage_bucket": row["coverage_bucket"],
                "semantic_verdict": "",
                "selection_instruction": (
                    "After semantic review, take the first five rows in this "
                    "chapter ranking whose recorded verdict is actually OK. "
                    "The current row is only a candidate."
                ),
            }
            ok_ranking.append(sample)
            if rank <= OK_SAMPLE_SIZE:
                ok_head.append(
                    {
                        **sample,
                        "sample_kind": "ok_review_queue_head",
                    }
                )
    return exercise_samples, ok_ranking, ok_head


def _counts_by(
    rows: Iterable[Mapping[str, object]], key: str
) -> dict[str, int]:
    return dict(
        sorted(
            Counter(str(row[key]) for row in rows).items(),
            key=lambda item: (
                CHAPTER_ORDER.get(item[0], 999),
                item[0],
            ),
        )
    )


def _source_hash(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate_inventory(
    *,
    readme_rows: Sequence[dict[str, object]],
    frozen_census: Sequence[dict[str, object]],
    current_census: Sequence[dict[str, object]],
    gap_rows: Sequence[dict[str, object]],
    extras: Sequence[dict[str, object]],
    review_metadata: Mapping[str, object],
    faithful_flags: Sequence[dict[str, object]],
    faithful_metadata: Mapping[str, object],
    endpoint_union: Sequence[dict[str, object]],
    exercise_rows: Sequence[dict[str, object]],
    exercise_samples: Sequence[dict[str, object]],
    ok_ranking: Sequence[dict[str, object]],
    ok_head: Sequence[dict[str, object]],
) -> None:
    errors: list[str] = []

    def expect(label: str, observed: object, expected: object) -> None:
        if observed != expected:
            errors.append(f"{label}: observed {observed!r}, expected {expected!r}")

    expect("README row count", len(readme_rows), 611)
    expect(
        "README chapter counts",
        _counts_by(readme_rows, "chapter"),
        README_EXPECTED_BY_CHAPTER,
    )
    readme_endpoints = {
        str(endpoint)
        for row in readme_rows
        for endpoint in row["endpoint_names"]
    }
    expect("README unique endpoint count", len(readme_endpoints), 540)
    expect(
        "README rows without endpoints",
        sum(not row["endpoint_names"] for row in readme_rows),
        0,
    )

    expect("raw frozen display rows", review_metadata["raw_frozen_display_rows"], 724)
    expect("frozen display-only extras", len(extras), 7)
    expect("frozen census rows", review_metadata["frozen_census_rows"], 717)
    expect("original Appendix rows", review_metadata["original_appendix_rows"], 67)
    expect("raw gap rows", len(gap_rows), 89)
    expect(
        "gap disposition counts",
        _counts_by(gap_rows, "source_status_cell"),
        {"FORMALIZED": 51, "IN-APPENDIX": 3, "REJECTED": 35},
    )
    expect("accepted gap rows", review_metadata["accepted_gap_rows"], 54)
    expect("frozen valid census row count", len(frozen_census), 838)
    expect(
        "frozen valid census chapter counts",
        _counts_by(frozen_census, "chapter"),
        CENSUS_EXPECTED_BY_CHAPTER,
    )
    expect(
        "frozen valid census REVIEW bucket counts",
        _counts_by(frozen_census, "coverage_bucket"),
        REVIEW_BUCKET_EXPECTED,
    )
    expect("current valid census row count", len(current_census), 835)
    expect(
        "current valid census chapter counts",
        _counts_by(current_census, "chapter"),
        CURRENT_CENSUS_EXPECTED_BY_CHAPTER,
    )
    expect(
        "current valid census REVIEW bucket counts",
        _counts_by(current_census, "coverage_bucket"),
        CURRENT_REVIEW_BUCKET_EXPECTED,
    )
    frozen_ids = {str(row["row_id"]) for row in frozen_census}
    current_ids = {str(row["row_id"]) for row in current_census}
    expect(
        "current census stable-ID projection",
        current_ids,
        frozen_ids - CURRENT_REMOVED_ROW_IDS,
    )
    current_by_id = {
        str(row["row_id"]): row
        for row in current_census
    }
    exercise = current_by_id.get(CURRENT_EXERCISE_8_39_ROW_ID)
    if exercise is None:
        errors.append("current Exercise 8.39(b) projection row is missing")
    else:
        expect(
            "current Exercise 8.39 book reference",
            exercise["book_ref"],
            "Exercise 8.39(b)",
        )
        expect(
            "current Exercise 8.39 bucket",
            exercise["coverage_bucket"],
            "core_formalized",
        )
        expect(
            "current Exercise 8.39 endpoint",
            exercise["direct_endpoint_names"],
            [CURRENT_EXERCISE_8_39_ENDPOINT],
        )
    brownian = current_by_id.get(CURRENT_BROWNIAN_ROW_ID)
    if brownian is None:
        errors.append("current Brownian projection row is missing")
    else:
        expect(
            "current Brownian bucket",
            brownian["coverage_bucket"],
            "appendix_proved",
        )
        expect(
            "current Brownian endpoint",
            brownian["direct_endpoint_names"],
            [CURRENT_BROWNIAN_ENDPOINT],
        )

    total_rows = [
        row
        for row in faithful_metadata["summary_rows"]
        if row["chapter"] == "Total"
    ]
    if len(total_rows) == 1:
        expect("FAITHFUL historical valid total", total_rows[0]["Valid"], 838)
        expect("FAITHFUL historical rejected total", total_rows[0]["Rejected"], 35)
    expect("FAITHFUL historical flag rows", len(faithful_flags), 10)
    expect(
        "FAITHFUL historical partial rows",
        faithful_metadata["historical_partial_row_count"],
        5,
    )
    expect(
        "FAITHFUL historical Appendix-unresolved rows",
        faithful_metadata["historical_appendix_unresolved_row_count"],
        5,
    )

    expect(
        "endpoint union duplicate names",
        len(endpoint_union),
        len({str(row["endpoint"]) for row in endpoint_union}),
    )
    union_names = {str(row["endpoint"]) for row in endpoint_union}
    if not readme_endpoints.issubset(
        union_names
    ):
        errors.append("endpoint union does not contain every README endpoint")
    unexpected_removed_endpoints = sorted(
        REMOVED_CONDITIONAL_ENDPOINTS.intersection(union_names)
    )
    if unexpected_removed_endpoints:
        errors.append(
            "current endpoint union retains removed conditional endpoints: "
            f"{unexpected_removed_endpoints}"
        )
    for endpoint in (
        CURRENT_EXERCISE_8_39_ENDPOINT,
        CURRENT_BROWNIAN_ENDPOINT,
    ):
        if endpoint not in union_names:
            errors.append(
                f"current endpoint union lacks retained endpoint {endpoint}"
            )

    all_ids = [
        *(str(row["row_id"]) for row in readme_rows),
        *(str(row["row_id"]) for row in current_census),
        *(str(row["row_id"]) for row in gap_rows),
        *(str(row["row_id"]) for row in extras),
        *(str(row["row_id"]) for row in faithful_flags),
        *(str(row["declaration_id"]) for row in exercise_rows),
    ]
    duplicates = [
        row_id for row_id, count in Counter(all_ids).items() if count > 1
    ]
    # Accepted gap rows intentionally occur in both the all-gap and census
    # artifacts.  All other duplicate identifiers are forbidden.
    allowed_duplicates = {
        str(row["row_id"])
        for row in gap_rows
        if row["source_status_cell"] != "REJECTED"
    }
    unexpected_duplicates = sorted(set(duplicates) - allowed_duplicates)
    if unexpected_duplicates:
        errors.append(
            f"unexpected duplicate stable row IDs: {unexpected_duplicates[:10]}"
        )

    if any(not row["parsed"] for row in exercise_rows):
        errors.append("one or more exercise-leaf declarations did not parse")
    for chapter in LEAN_CHAPTERS:
        candidates = [
            row
            for row in exercise_rows
            if row["chapter"] == chapter
            and row["is_exercise_sample_candidate"]
        ]
        if len(candidates) < EXERCISE_SAMPLE_SIZE:
            errors.append(
                f"{chapter}: only {len(candidates)} exercise sample candidates"
            )
        expect(
            f"{chapter} exercise sample size",
            sum(
                row["chapter"] == chapter for row in exercise_samples
            ),
            EXERCISE_SAMPLE_SIZE,
        )
        expect(
            f"{chapter} distinct exercise sample targets",
            len(
                {
                    str(row["target_id"])
                    for row in exercise_samples
                    if row["chapter"] == chapter
                }
            ),
            EXERCISE_SAMPLE_SIZE,
        )

    for chapter in CHAPTERS:
        ranked = [
            row for row in ok_ranking if row["chapter"] == chapter
        ]
        if len(ranked) < OK_SAMPLE_SIZE:
            errors.append(
                f"{chapter}: only {len(ranked)} mechanically eligible "
                "OK-row candidates"
            )
        expect(
            f"{chapter} OK queue-head size",
            sum(row["chapter"] == chapter for row in ok_head),
            OK_SAMPLE_SIZE,
        )
        expect(
            f"{chapter} OK candidate ranks",
            [int(row["rank"]) for row in ranked],
            list(range(1, len(ranked) + 1)),
        )

    if errors:
        raise InventoryError(
            "inventory validation failed:\n  - " + "\n  - ".join(errors)
        )


def _json_text(payload: object) -> str:
    return (
        json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True)
        + "\n"
    )


def _tsv_cell(value: object) -> object:
    if isinstance(value, bool):
        return str(value).lower()
    if value is None:
        return ""
    if isinstance(value, (list, dict, tuple)):
        return json.dumps(
            value, ensure_ascii=False, separators=(",", ":"), sort_keys=True
        )
    return value


def _tsv_text(
    rows: Sequence[Mapping[str, object]], fields: Sequence[str]
) -> str:
    buffer = io.StringIO(newline="")
    writer = csv.DictWriter(
        buffer,
        fieldnames=list(fields),
        delimiter="\t",
        lineterminator="\n",
        extrasaction="ignore",
    )
    writer.writeheader()
    for row in rows:
        writer.writerow({field: _tsv_cell(row.get(field, "")) for field in fields})
    return buffer.getvalue()


def build_artifacts() -> tuple[dict[str, str], dict[str, object]]:
    readme_rows = parse_readme()
    frozen_census, gap_rows, extras, review_metadata = parse_review()
    faithful_flags, faithful_metadata = parse_faithful(frozen_census)
    link_readme(frozen_census, readme_rows)
    current_census, current_metadata = project_current_census(
        frozen_census
    )
    link_readme(current_census, readme_rows)
    endpoint_union, endpoint_occurrences = build_endpoint_union(
        readme_rows, current_census
    )
    exercise_rows = parse_exercise_leaf_declarations()
    exercise_samples, ok_ranking, ok_head = build_sampling_plan(
        exercise_rows, current_census
    )

    validate_inventory(
        readme_rows=readme_rows,
        frozen_census=frozen_census,
        current_census=current_census,
        gap_rows=gap_rows,
        extras=extras,
        review_metadata=review_metadata,
        faithful_flags=faithful_flags,
        faithful_metadata=faithful_metadata,
        endpoint_union=endpoint_union,
        exercise_rows=exercise_rows,
        exercise_samples=exercise_samples,
        ok_ranking=ok_ranking,
        ok_head=ok_head,
    )

    summary: dict[str, object] = {
        "schema_version": SCHEMA_VERSION,
        "semantic_verdicts_assigned": False,
        "source_sha256": {
            README.relative_to(ROOT).as_posix(): _source_hash(README),
            REVIEW.relative_to(ROOT).as_posix(): _source_hash(REVIEW),
            FAITHFUL.relative_to(ROOT).as_posix(): _source_hash(FAITHFUL),
        },
        "readme": {
            "row_count": len(readme_rows),
            "chapter_counts": _counts_by(readme_rows, "chapter"),
            "unique_endpoint_count": len(
                {
                    str(endpoint)
                    for row in readme_rows
                    for endpoint in row["endpoint_names"]
                }
            ),
            "namespace_inherited_occurrence_count": sum(
                occurrence["mode"] == "namespace_inherited"
                for row in readme_rows
                for occurrence in row["endpoint_occurrences"]
            ),
        },
        "frozen_review_census": {
            **review_metadata,
            "row_count": len(frozen_census),
            "chapter_counts": _counts_by(frozen_census, "chapter"),
            "coverage_bucket_counts": _counts_by(
                frozen_census, "coverage_bucket"
            ),
            "readme_exact_ref_linked_rows": sum(
                bool(row["readme_match_ids"]) for row in frozen_census
            ),
            "direct_endpoint_rows": sum(
                bool(row["direct_endpoint_names"]) for row in frozen_census
            ),
            "rows_with_any_mechanical_endpoint_link": sum(
                bool(row["endpoint_names"]) for row in frozen_census
            ),
        },
        "review_census": {
            **current_metadata,
            "row_count": len(current_census),
            "chapter_counts": _counts_by(current_census, "chapter"),
            "coverage_bucket_counts": _counts_by(
                current_census, "coverage_bucket"
            ),
            "readme_exact_ref_linked_rows": sum(
                bool(row["readme_match_ids"]) for row in current_census
            ),
            "direct_endpoint_rows": sum(
                bool(row["direct_endpoint_names"]) for row in current_census
            ),
            "rows_with_any_mechanical_endpoint_link": sum(
                bool(row["endpoint_names"]) for row in current_census
            ),
        },
        "faithful_historical": faithful_metadata,
        "endpoint_union": {
            "unique_endpoint_count": len(endpoint_union),
            "occurrence_count": len(endpoint_occurrences),
            "source_kind_counts": _counts_by(
                endpoint_occurrences, "source_kind"
            ),
        },
        "exercise_leaf_inventory": {
            "declaration_count": len(exercise_rows),
            "chapter_counts": _counts_by(exercise_rows, "chapter"),
            "candidate_counts": _counts_by(
                [
                    row
                    for row in exercise_rows
                    if row["is_exercise_sample_candidate"]
                ],
                "chapter",
            ),
            "sample_seed": EXERCISE_SAMPLE_SEED,
            "sample_size_per_chapter": EXERCISE_SAMPLE_SIZE,
            "sample_chapters": LEAN_CHAPTERS,
        },
        "ok_candidate_plan": {
            "semantic_status": (
                "No row is called OK by this tool.  After close reading, take "
                "the first five genuinely-OK rows in each deterministic "
                "chapter ranking."
            ),
            "seed": OK_SAMPLE_SEED,
            "quota_per_chapter": OK_SAMPLE_SIZE,
            "ranking_counts": _counts_by(ok_ranking, "chapter"),
            "queue_head_counts": _counts_by(ok_head, "chapter"),
            "chapters": CHAPTERS,
        },
        "validation": {
            "ok": True,
            "identities": [
                "README: 611 rows, 540 unique mechanically resolved endpoints",
                "frozen REVIEW census: 724 - 7 + 67 + (89 - 35) = 838",
                "frozen REVIEW status buckets: 768 + 65 + 5 = 838",
                "current REVIEW census: 838 - 3 = 835",
                "current REVIEW status buckets: 769 + 66 + 0 = 835",
                "exercise leaf close-read sample: 3 per Chapter 1–9",
                "OK candidate queue head: 5 per Appetizer/Chapter 1–9",
            ],
        },
    }

    common = {
        "schema_version": SCHEMA_VERSION,
        "semantic_verdicts_assigned": False,
    }
    sample_rows = sorted(
        [*exercise_samples, *ok_head],
        key=lambda row: (
            str(row["sample_kind"]),
            CHAPTER_ORDER[str(row["chapter"])],
            int(row["rank"]),
        ),
    )
    artifacts = {
        "readme_correspondence.json": _json_text(
            {**common, "rows": readme_rows}
        ),
        "readme_correspondence.tsv": _tsv_text(
            readme_rows, README_TSV_FIELDS
        ),
        "review_census_838.json": _json_text(
            {
                **common,
                "metadata": review_metadata,
                "rows": frozen_census,
            }
        ),
        "review_census_838.tsv": _tsv_text(
            frozen_census, CENSUS_TSV_FIELDS
        ),
        "review_census_835.json": _json_text(
            {
                **common,
                "metadata": current_metadata,
                "rows": current_census,
            }
        ),
        "review_census_835.tsv": _tsv_text(
            current_census, CENSUS_TSV_FIELDS
        ),
        "review_gap_disposition_89.json": _json_text(
            {**common, "rows": gap_rows}
        ),
        "review_gap_disposition_89.tsv": _tsv_text(
            gap_rows, GAP_TSV_FIELDS
        ),
        "review_display_only_extras_7.json": _json_text(
            {**common, "rows": extras}
        ),
        "review_display_only_extras_7.tsv": _tsv_text(
            extras, EXTRA_TSV_FIELDS
        ),
        "faithful_historical_status_rows.json": _json_text(
            {**common, "metadata": faithful_metadata, "rows": faithful_flags}
        ),
        "faithful_historical_status_rows.tsv": _tsv_text(
            faithful_flags, FAITHFUL_TSV_FIELDS
        ),
        "endpoint_union.json": _json_text(
            {
                **common,
                "rows": endpoint_union,
                "occurrences": endpoint_occurrences,
            }
        ),
        "endpoint_union.tsv": _tsv_text(
            endpoint_union, ENDPOINT_TSV_FIELDS
        ),
        "exercise_leaf_declarations.json": _json_text(
            {**common, "rows": exercise_rows}
        ),
        "exercise_leaf_declarations.tsv": _tsv_text(
            exercise_rows, EXERCISE_DECL_TSV_FIELDS
        ),
        "sampling_plan.json": _json_text(
            {
                **common,
                "exercise_leaf_close_read": exercise_samples,
                "ok_candidate_ranking": ok_ranking,
                "ok_review_queue_head": ok_head,
            }
        ),
        "sampling_plan.tsv": _tsv_text(sample_rows, SAMPLE_TSV_FIELDS),
        "inventory_summary.json": _json_text(summary),
        "inventory_summary.tsv": _tsv_text(
            [
                {
                    "metric": "readme_rows",
                    "value": len(readme_rows),
                },
                {
                    "metric": "readme_unique_endpoints",
                    "value": summary["readme"]["unique_endpoint_count"],
                },
                {
                    "metric": "frozen_census_rows",
                    "value": len(frozen_census),
                },
                {
                    "metric": "census_rows",
                    "value": len(current_census),
                },
                {
                    "metric": "endpoint_union_unique",
                    "value": len(endpoint_union),
                },
                {
                    "metric": "exercise_leaf_declarations",
                    "value": len(exercise_rows),
                },
                {
                    "metric": "exercise_samples",
                    "value": len(exercise_samples),
                },
                {
                    "metric": "ok_candidate_queue_head",
                    "value": len(ok_head),
                },
                {"metric": "validation_ok", "value": True},
            ],
            ("metric", "value"),
        ),
    }
    for name, expected_sha256 in (
        (
            "review_census_838.tsv",
            EXPECTED_FROZEN_CENSUS_TSV_SHA256,
        ),
        (
            "review_census_838.json",
            EXPECTED_FROZEN_CENSUS_JSON_SHA256,
        ),
    ):
        observed_sha256 = hashlib.sha256(
            artifacts[name].encode("utf-8")
        ).hexdigest()
        if observed_sha256 != expected_sha256:
            raise InventoryError(
                f"frozen {name} render changed: "
                f"{observed_sha256} != {expected_sha256}"
            )
    return artifacts, summary


def _write_or_check(
    artifacts: Mapping[str, str], output_dir: Path, *, check: bool
) -> list[str]:
    mismatches: list[str] = []
    if check:
        for name, expected in sorted(artifacts.items()):
            path = output_dir / name
            if not path.is_file():
                mismatches.append(f"missing {path}")
            elif path.read_text(encoding="utf-8") != expected:
                mismatches.append(f"stale {path}")
        unexpected = sorted(
            path.name
            for path in output_dir.glob("*")
            if path.is_file()
            and path.suffix in {".json", ".tsv"}
            and path.name not in artifacts
            and path.name not in CURATED_INVENTORY_ARTIFACTS
        )
        mismatches.extend(
            f"unexpected artifact {output_dir / name}" for name in unexpected
        )
        return mismatches

    output_dir.mkdir(parents=True, exist_ok=True)
    for name, content in sorted(artifacts.items()):
        (output_dir / name).write_text(content, encoding="utf-8")
    return mismatches


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Parse the 611-row publication map, retain the exact frozen "
            "838-row REVIEW census, and emit the projected current 835-row "
            "census plus deterministic current review plans"
        )
    )
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=DEFAULT_OUTPUT_DIR,
        help="artifact directory (default: Verification/inventory)",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="validate that existing artifacts equal a fresh in-memory render",
    )
    args = parser.parse_args(argv)
    output_dir = (
        args.output_dir
        if args.output_dir.is_absolute()
        else ROOT / args.output_dir
    )

    try:
        artifacts, summary = build_artifacts()
        mismatches = _write_or_check(
            artifacts, output_dir, check=args.check
        )
    except (InventoryError, OSError, ValueError) as error:
        print(f"row inventory failed: {error}", file=sys.stderr)
        return 1
    if mismatches:
        print("row inventory artifact check failed:", file=sys.stderr)
        for mismatch in mismatches:
            print(f"  - {mismatch}", file=sys.stderr)
        return 1

    action = "checked" if args.check else "wrote"
    print(
        f"{action} {len(artifacts)} deterministic artifacts in "
        f"{output_dir.relative_to(ROOT) if output_dir.is_relative_to(ROOT) else output_dir}"
    )
    print(
        "validated: "
        f"README={summary['readme']['row_count']}, "
        f"README-endpoints={summary['readme']['unique_endpoint_count']}, "
        f"census={summary['review_census']['row_count']}, "
        f"endpoint-union={summary['endpoint_union']['unique_endpoint_count']}, "
        f"exercise-samples={EXERCISE_SAMPLE_SIZE}/Chapter1-9, "
        f"OK-candidate-head={OK_SAMPLE_SIZE}/chapter"
    )
    print("semantic_verdicts_assigned: false")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
