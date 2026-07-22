#!/usr/bin/env python3
"""Fail-closed merge of the eight human-curated V6 Tier-B chapter ledgers.

No verdict or rationale is synthesized here.  The script accepts only a
complete, chapter-sharded review record whose immutable metadata matches both
the README extraction and the compiled endpoint environment.
"""

from __future__ import annotations

import csv
import json
import re
import sys
from collections import Counter
from functools import lru_cache
from pathlib import Path


SCRIPT = Path(__file__).resolve()
VERIFICATION = SCRIPT.parent.parent
SOURCE_ROOT = VERIFICATION.parent
LOGS = VERIFICATION / "logs"
CURATION = VERIFICATION / "curation"
ROWS = LOGS / "v6_correspondence_rows.tsv"
ENDPOINTS = LOGS / "v6_endpoint_telescopes.tsv"

EXPECTED = {"1": 21, "2": 136, "3": 35, "4": 55, "5": 71, "6": 62, "7": 63, "8": 24}
EXPECTED_VERDICTS = Counter({"OK": 433, "SUSPECT": 34, "VACUOUS": 0})
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
IMMUTABLE = FIELDS[:7]
CHECKLIST = FIELDS[8:12]
VERDICTS = {"OK", "SUSPECT", "VACUOUS"}

LEGACY_GENERIC_PHRASES = (
    "close reading of the displayed conclusion",
    "standard nondegenerate instances",
    "explicit nonzero inhabitants of the scalar",
    "nonzero identity, diagonal, or matrix-unit data on the finite dimensions",
    "bounded finite two-point matrix law (product Rademacher/Bernoulli when",
    "every single-letter Sort binder has explicit source evidence",
    "every parameter is explicit or section-declared, and the telescope audit",
)

REQUIRED_BOUNDARY_ROWS = {
    "intdim": ("0 / 0", "zero"),
    "weakVariance": ("empty", "sSup"),
    "gChernoff": ("L = 0", "zero"),
    "gBernstein": ("θ * L = 3", "theta"),
    "perspectiveFun": ("a = 0", "denominator"),
    "sparsifyProb": ("zero matrix", "zero"),
    "sparsifyValue": ("zero matrix", "prob"),
    "matmulProb": ("jointly zero", "zero"),
    "matmulValue": ("zero", "prob"),
    "bernoulliMeasureReal": ("outside", "[0,1]"),
    "IsBernoulli": ("outside", "[0,1]"),
    "normalizedLapMatrix": ("isolated", "degree"),
}

SOURCE_REF_RE = re.compile(
    r"\bsource:\s*(?:MatrixConcentration/)?"
    r"(?P<path>[A-Za-z0-9_./-]+\.lean):"
    r"(?P<start>[0-9]+)(?:-(?P<end>[0-9]+))?"
)


def declaration_pattern(name: str) -> re.Pattern[str]:
    return re.compile(
        r"^\s*(?:@\[[^\]]+\]\s*)*"
        r"(?:(?:private|protected|noncomputable|unsafe)\s+)*"
        r"(?:theorem|lemma|def|abbrev|opaque)\s+"
        + re.escape(name)
        + r"(?=$|[\s({:\[])"
    )


@lru_cache(maxsize=1)
def derived_source_index() -> dict[str, list[tuple[Path, int]]]:
    """Index declarations directly from the 14 source modules once."""

    declaration = re.compile(
        r"^\s*(?:@\[[^\]]+\]\s*)*"
        r"(?:(?:private|protected|noncomputable|unsafe)\s+)*"
        r"(?:theorem|lemma|def|abbrev|opaque)\s+"
        r"(?P<name>[^\s({:\[]+)"
        r"(?=$|[\s({:\[])"
    )
    index: dict[str, list[tuple[Path, int]]] = {}
    for path in sorted(SOURCE_ROOT.glob("*.lean")):
        for line_number, line in enumerate(
            path.read_text(encoding="utf-8").splitlines(), 1
        ):
            match = declaration.match(line)
            if match is not None:
                index.setdefault(match.group("name"), []).append(
                    (path, line_number)
                )
    return index


def derived_source_locations(name: str) -> list[tuple[Path, int]]:
    """Locate an endpoint without consuming V7 or curator-supplied output."""

    return derived_source_index().get(name, [])


def validate_source_reference(
    declaration: str,
    evidence: str,
) -> list[str]:
    problems: list[str] = []
    match = SOURCE_REF_RE.search(evidence)
    if match is None:
        return [
            f"{declaration}: evidence_refs lacks a parseable primary "
            "`source: File.lean:line[-line]` reference"
        ]
    cited_rel = Path(match.group("path"))
    cited_path = SOURCE_ROOT / cited_rel
    start = int(match.group("start"))
    end = int(match.group("end") or start)
    if start <= 0 or end < start:
        problems.append(
            f"{declaration}: invalid cited source range {start}-{end}"
        )
    if not cited_path.is_file():
        problems.append(
            f"{declaration}: cited source file does not exist: {cited_rel}"
        )
        return problems
    lines = cited_path.read_text(encoding="utf-8").splitlines()
    if end > len(lines):
        problems.append(
            f"{declaration}: cited source range ends at {end}, but "
            f"{cited_rel} has {len(lines)} lines"
        )
        return problems
    pattern = declaration_pattern(declaration)
    cited_declaration_lines = [
        line_number
        for line_number in range(start, end + 1)
        if pattern.match(lines[line_number - 1])
    ]
    if not cited_declaration_lines:
        problems.append(
            f"{declaration}: cited range {cited_rel}:{start}-{end} does "
            "not contain the endpoint declaration"
        )
    derived = derived_source_locations(declaration)
    if len(derived) != 1:
        rendered = [
            f"{path.relative_to(SOURCE_ROOT)}:{line}" for path, line in derived
        ]
        problems.append(
            f"{declaration}: direct source derivation found {len(derived)} "
            f"locations: {rendered}"
        )
    else:
        derived_path, derived_line = derived[0]
        if derived_path.resolve() != cited_path.resolve():
            problems.append(
                f"{declaration}: cited file {cited_rel} differs from "
                f"derived file {derived_path.relative_to(SOURCE_ROOT)}"
            )
        if not (start <= derived_line <= end):
            problems.append(
                f"{declaration}: derived declaration line {derived_line} "
                f"is outside cited range {start}-{end}"
            )
    return problems


def read(path: Path) -> tuple[list[str], list[dict[str, str]]]:
    with path.open(newline="", encoding="utf-8") as handle:
        reader = csv.DictReader(handle, delimiter="\t")
        return list(reader.fieldnames or []), list(reader)


def normalized(text: str) -> str:
    return re.sub(r"\s+", " ", text).strip()


def markdown_table(rows: list[dict[str, str]]) -> str:
    lines: list[str] = []
    for chapter in range(1, 9):
        chapter_rows = [
            row for row in rows if int(row["chapter"]) == chapter
        ]
        counts = Counter(row["verdict"] for row in chapter_rows)
        lines.extend(
            [
                f"### Chapter {chapter}",
                "",
                f"Measured fixed rows: **{len(chapter_rows)}**.",
                "",
                "| Row / book item | Declaration | Verdict | Four-point checklist justification |",
                "|---|---|---|---|",
            ]
        )
        for row in chapter_rows:
            justification = row["justification"].replace("|", "\\|")
            book = row["book_source"].replace("|", "\\|")
            lines.append(
                f"| C{chapter}-{int(row['chapter_row']):03d} · {book} "
                f"| `{row['declaration']}` | {row['verdict']} "
                f"| {justification} |"
            )
        lines.extend(
            [
                "",
                "Result: "
                + ", ".join(
                    f"**{counts[verdict]} {verdict}**"
                    for verdict in ("OK", "SUSPECT", "VACUOUS")
                )
                + ".",
                "",
            ]
        )
    return "\n".join(lines)


def main() -> int:
    errors: list[str] = []
    _, source_rows = read(ROWS)
    _, endpoint_rows = read(ENDPOINTS)
    endpoints = {row["global_row"]: row for row in endpoint_rows}
    source_by_global = {row["global_row"]: row for row in source_rows}
    if len(source_rows) != 467 or len(endpoints) != 467:
        errors.append(
            f"fixed inputs must contain 467 rows: README={len(source_rows)}, "
            f"environment={len(endpoints)}"
        )

    curated: list[dict[str, str]] = []
    for chapter in range(1, 9):
        path = CURATION / f"v6_tier_b_chapter_{chapter}.tsv"
        if not path.is_file():
            errors.append(f"missing curated chapter file: {path}")
            continue
        fields, chapter_rows = read(path)
        if fields != FIELDS:
            errors.append(
                f"chapter {chapter}: field schema drift: {fields!r}"
            )
        if len(chapter_rows) != EXPECTED[str(chapter)]:
            errors.append(
                f"chapter {chapter}: {len(chapter_rows)} rows, "
                f"expected {EXPECTED[str(chapter)]}"
            )
        curated.extend(chapter_rows)

    seen_global: set[str] = set()
    seen_keys: set[tuple[str, str]] = set()
    seen_rationales: dict[tuple[str, ...], str] = {}
    boundary_seen: set[str] = set()
    merged: list[dict[str, str]] = []

    for row in curated:
        global_row = row.get("global_row", "")
        declaration = row.get("declaration", "")
        if global_row in seen_global:
            errors.append(f"duplicate curated global row {global_row}")
        seen_global.add(global_row)
        key = (row.get("chapter", ""), row.get("chapter_row", ""))
        if key in seen_keys:
            errors.append(f"duplicate curated chapter row {key}")
        seen_keys.add(key)

        source = source_by_global.get(global_row)
        endpoint = endpoints.get(global_row)
        if source is None or endpoint is None:
            errors.append(
                f"{declaration or '<unnamed>'}: global row {global_row} "
                "does not join to fixed inputs"
            )
            continue
        expected_metadata = {
            "global_row": source["global_row"],
            "chapter": source["chapter"],
            "chapter_row": source["chapter_row"],
            "readme_line": source["readme_line"],
            "book_source": source["book_source"],
            "declaration": source["declaration"],
            "endpoint_kind": endpoint["kind"],
        }
        for field in IMMUTABLE:
            if row.get(field, "") != expected_metadata[field]:
                errors.append(
                    f"global row {global_row}: immutable {field} drift: "
                    f"{row.get(field, '')!r} != {expected_metadata[field]!r}"
                )

        verdict = row.get("verdict", "")
        if verdict not in VERDICTS:
            errors.append(f"{declaration}: invalid/blank verdict {verdict!r}")
        values = tuple(normalized(row.get(field, "")) for field in CHECKLIST)
        for field, value in zip(CHECKLIST, values):
            if len(value) < 35:
                errors.append(
                    f"{declaration}: {field} is blank/too short "
                    f"({len(value)} characters)"
                )
            for phrase in LEGACY_GENERIC_PHRASES:
                if phrase.casefold() in value.casefold():
                    errors.append(
                        f"{declaration}: {field} retains generated generic "
                        f"phrase {phrase!r}"
                    )
        if values in seen_rationales:
            errors.append(
                f"{declaration}: duplicates all four checklist cells from "
                f"{seen_rationales[values]}"
            )
        else:
            seen_rationales[values] = declaration

        adjudication = normalized(row.get("adjudication", ""))
        if len(adjudication) < 50:
            errors.append(f"{declaration}: adjudication is blank/too short")
        if declaration and declaration not in adjudication:
            errors.append(
                f"{declaration}: adjudication must name the declaration"
            )
        evidence = normalized(row.get("evidence_refs", ""))
        if len(evidence) < 30:
            errors.append(f"{declaration}: evidence_refs is blank/too short")
        for marker in ("source:", "telescope:"):
            if marker not in evidence:
                errors.append(
                    f"{declaration}: evidence_refs lacks required {marker!r}"
                )
        errors.extend(validate_source_reference(declaration, evidence))

        if declaration in REQUIRED_BOUNDARY_ROWS:
            boundary_seen.add(declaration)
            combined = " ".join(
                [values[1], adjudication, evidence]
            ).casefold()
            anchors = REQUIRED_BOUNDARY_ROWS[declaration]
            if not any(anchor.casefold() in combined for anchor in anchors):
                errors.append(
                    f"{declaration}: required boundary adjudication lacks "
                    f"one of {anchors!r}"
                )

        justification = (
            f"(1) {values[0]} "
            f"(2) {values[1]} "
            f"(3) {values[2]} "
            f"(4) {values[3]} "
            f"Adjudication: {adjudication} "
            f"Evidence: {evidence}"
        )
        merged.append(
            {
                **source,
                "endpoint_kind": endpoint["kind"],
                "verdict": verdict,
                "check1_model": values[0],
                "check2_nontrivial": values[1],
                "check3_typeclasses": values[2],
                "check4_quantifiers": values[3],
                "adjudication": adjudication,
                "evidence_refs": evidence,
                "justification": justification,
            }
        )

    if seen_global != set(source_by_global):
        errors.append(
            "curated global-row set mismatch: "
            f"missing={sorted(set(source_by_global) - seen_global)}, "
            f"extra={sorted(seen_global - set(source_by_global))}"
        )
    missing_boundaries = set(REQUIRED_BOUNDARY_ROWS) - boundary_seen
    if missing_boundaries:
        errors.append(
            "required boundary rows absent: " + ", ".join(sorted(missing_boundaries))
        )

    merged.sort(key=lambda row: int(row["global_row"]))
    verdict_counts = Counter(row["verdict"] for row in merged)
    if verdict_counts != EXPECTED_VERDICTS:
        errors.append(
            "curated verdict counts drift: "
            f"{dict(verdict_counts)} != {dict(EXPECTED_VERDICTS)}"
        )
    status = "PASS" if not errors else "FAIL"
    output = LOGS / "v6_tier_b_review.tsv"
    output_fields = list(source_rows[0]) + [
        "endpoint_kind",
        "verdict",
        "check1_model",
        "check2_nontrivial",
        "check3_typeclasses",
        "check4_quantifiers",
        "adjudication",
        "evidence_refs",
        "justification",
    ]
    with output.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(
            handle, fieldnames=output_fields, delimiter="\t", lineterminator="\n"
        )
        writer.writeheader()
        writer.writerows(merged)
    (LOGS / "v6_tier_b_tables.md").write_text(
        markdown_table(merged), encoding="utf-8"
    )
    kind_counts = Counter(row["endpoint_kind"] for row in merged)
    chapter_counts = Counter(row["chapter"] for row in merged)
    summary = {
        "status": status,
        "rows": len(merged),
        "chapter_counts": dict(sorted(chapter_counts.items())),
        "verdict_counts": dict(sorted(verdict_counts.items())),
        "endpoint_kind_counts": dict(sorted(kind_counts.items())),
        "curated_files": [
            f"curation/v6_tier_b_chapter_{chapter}.tsv"
            for chapter in range(1, 9)
        ],
        "checklist_complete": not any(
            "blank/too short" in error for error in errors
        ),
        "required_boundary_rows": sorted(REQUIRED_BOUNDARY_ROWS),
        "errors": errors,
    }
    (LOGS / "v6_tier_b_summary.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    lines = [
        "V6 TIER B CURATED FIXED-ROW MERGE",
        f"STATUS {status}",
        f"ROWS {len(merged)}",
        *(f"CHAPTER_{chapter} {chapter_counts[str(chapter)]}" for chapter in range(1, 9)),
        f"THEOREM_ENDPOINTS {kind_counts['theorem']}",
        f"DEFINITION_ENDPOINTS {kind_counts['definition']}",
        f"OK {verdict_counts['OK']}",
        f"SUSPECT {verdict_counts['SUSPECT']}",
        f"VACUOUS {verdict_counts['VACUOUS']}",
        f"ERRORS {len(errors)}",
        "NOTE no verdict or checklist rationale is synthesized by this merger",
        *(f"ERROR {error}" for error in errors),
    ]
    (LOGS / "v6_tier_b_run.log").write_text(
        "\n".join(lines) + "\n", encoding="utf-8"
    )
    print("\n".join(lines))
    return 0 if status == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
