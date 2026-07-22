#!/usr/bin/env python3
"""Build the exact project-theorem endpoint set used by V7.

V6 Tier B has two mandatory semantic row sources:

* all 611 rows in the public README correspondence table; and
* the current 91 direct-census endpoint rows not already represented by that
  table.

The close-reading ledgers also contain exercise samples and the deterministic
Tier-C queue.  Those are useful V6 evidence but are not part of the mandatory
Tier-B endpoint union and are deliberately excluded here.

One book row may resolve to several Lean declarations.  This script expands
those semicolon-separated names, joins them to V4's environment inventory,
and emits exactly the project-local theorem constants.  Mathlib endpoints and
project definitions are retained in a separate exclusions ledger rather than
being silently dropped.
"""

from __future__ import annotations

import argparse
import collections
import csv
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable


ROOT = Path(__file__).resolve().parents[3]
VERIFICATION = ROOT / "HighDimensionalProbability" / "Verification"
REVIEW = VERIFICATION / "review"
LOGS = VERIFICATION / "logs"

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
DEFAULT_V4 = LOGS / "recert_axiom_audit.tsv"
DEFAULT_OUTPUT = LOGS / "recert_v6_tier_b_endpoints.tsv"
DEFAULT_EXCLUSIONS = LOGS / "recert_v6_tier_b_endpoint_exclusions.tsv"
DEFAULT_SUMMARY = LOGS / "recert_v6_tier_b_endpoint_summary.txt"

EXPECTED_README_ROWS = 611
EXPECTED_SUPPLEMENT_ROWS = 91
EXPECTED_SUSPECT_ROWS = 0
PROJECT_PREFIXES = (
    "HDP.",
    "HighDimensionalProbability.",
    "MatrixConcentration.",
    "_private.HighDimensionalProbability.",
    "_private.MatrixConcentration.",
)


@dataclass(frozen=True)
class SelectedRow:
    ledger: str
    row_set: str
    row_id: str
    chapter: str
    book_label: str
    verdict: str
    resolved_declarations: tuple[str, ...]
    source_locations: tuple[str, ...]


def _read_tsv(path: Path) -> list[dict[str, str]]:
    with path.open(encoding="utf-8", newline="") as handle:
        return list(csv.DictReader(handle, delimiter="\t"))


def _split_names(text: str) -> tuple[str, ...]:
    return tuple(part.strip() for part in text.split(";") if part.strip())


def _split_locations(text: str) -> tuple[str, ...]:
    return tuple(part.strip() for part in text.split(";") if part.strip())


def _select_rows(
    main_ledgers: Iterable[Path],
    supplement_ledgers: Iterable[Path],
) -> tuple[list[SelectedRow], list[SelectedRow]]:
    main: list[SelectedRow] = []
    supplements: list[SelectedRow] = []

    for path in main_ledgers:
        for row in _read_tsv(path):
            if row.get("row_set") != "readme_correspondence":
                continue
            main.append(
                SelectedRow(
                    ledger=path.relative_to(ROOT).as_posix(),
                    row_set=row["row_set"],
                    row_id=row["row_id"],
                    chapter=row["chapter"],
                    book_label=row["book_label"],
                    verdict=row["verdict"],
                    resolved_declarations=_split_names(
                        row["resolved_declarations"]
                    ),
                    source_locations=_split_locations(
                        row["source_locations"]
                    ),
                )
            )

    for path in supplement_ledgers:
        for row in _read_tsv(path):
            # Ch0--7 supplements use the common close-reading schema.  The
            # independently generated Ch8--9 supplement carries the same
            # semantics under endpoint-oriented column names; normalize both
            # explicitly instead of silently dropping either format.
            row_set = row.get("row_set") or "direct_census_supplement"
            chapter = row.get("chapter") or row.get("chapters", "")
            book_label = row.get("book_label") or row.get("book_refs", "")
            verdict = row.get("verdict") or row.get("status", "")
            declarations = (
                row.get("resolved_declarations") or row.get("endpoint", "")
            )
            locations = (
                row.get("source_locations") or row.get("source_location", "")
            )
            supplements.append(
                SelectedRow(
                    ledger=path.relative_to(ROOT).as_posix(),
                    row_set=row_set,
                    row_id=row["row_id"],
                    chapter=chapter,
                    book_label=book_label,
                    verdict=verdict,
                    resolved_declarations=_split_names(declarations),
                    source_locations=_split_locations(locations),
                )
            )
    return main, supplements


def _read_v4(path: Path) -> dict[str, dict[str, str]]:
    rows = _read_tsv(path)
    if not rows:
        raise ValueError(f"{path}: V4 audit contains no rows")
    required = {"module", "name", "kind"}
    if not required <= set(rows[0]):
        raise ValueError(f"{path}: V4 audit lacks {sorted(required)}")
    by_name: dict[str, dict[str, str]] = {}
    for row in rows:
        name = row["name"]
        if name in by_name:
            raise ValueError(f"{path}: duplicate V4 declaration {name}")
        by_name[name] = row
    return by_name


def _looks_external(row: SelectedRow, name: str) -> bool:
    if name.startswith(PROJECT_PREFIXES):
        return False
    # A correspondence row can expand to both project wrappers and Mathlib
    # primitives, so its location list is intentionally mixed.  For a
    # non-project-qualified name, one pinned-package source location is
    # sufficient external provenance once V4 confirms the name is not a
    # project constant.
    return bool(row.source_locations) and any(
        location.startswith(".lake/packages/")
        for location in row.source_locations
    )


def build(
    *,
    v4_path: Path,
    output_path: Path,
    exclusions_path: Path,
    summary_path: Path,
) -> int:
    main, supplements = _select_rows(MAIN_LEDGERS, SUPPLEMENT_LEDGERS)
    errors: list[str] = []
    if len(main) != EXPECTED_README_ROWS:
        errors.append(
            f"mandatory README rows: expected {EXPECTED_README_ROWS}, "
            f"observed {len(main)}"
        )
    if len(supplements) != EXPECTED_SUPPLEMENT_ROWS:
        errors.append(
            f"supplemental census rows: expected {EXPECTED_SUPPLEMENT_ROWS}, "
            f"observed {len(supplements)}"
        )
    selected = [*main, *supplements]
    row_ids = [row.row_id for row in selected]
    duplicate_row_ids = sorted(
        row_id
        for row_id, count in collections.Counter(row_ids).items()
        if count > 1
    )
    if duplicate_row_ids:
        errors.append(
            "duplicate selected Tier-B row IDs: "
            + ", ".join(duplicate_row_ids[:20])
        )

    v4 = _read_v4(v4_path)
    endpoint_rows: dict[str, list[SelectedRow]] = collections.defaultdict(list)
    exclusions: list[tuple[SelectedRow, str, str, str, str]] = []
    suspect_rows = 0
    suspect_stale_endpoint_rows = 0
    for row in selected:
        if row.verdict not in {"OK", "SUSPECT", "VACUOUS"}:
            errors.append(
                f"{row.ledger}:{row.row_id}: unknown verdict {row.verdict!r}"
            )
            continue
        if row.verdict == "SUSPECT":
            suspect_rows += 1
        if not row.resolved_declarations:
            if row.verdict == "SUSPECT":
                suspect_stale_endpoint_rows += 1
                exclusions.append(
                    (
                        row,
                        "",
                        "SUSPECT_STALE_ENDPOINT_ROW",
                        "",
                        "exact inventory name is absent; explanatory replacement "
                        "evidence is not substituted",
                    )
                )
            else:
                errors.append(
                    f"{row.ledger}:{row.row_id}: resolved row has no declaration"
                )
            continue
        for name in row.resolved_declarations:
            v4_row = v4.get(name)
            if v4_row is None:
                classification = (
                    "EXTERNAL_MATHLIB_ENDPOINT"
                    if _looks_external(row, name)
                    else "MISSING_PROJECT_ENDPOINT"
                )
                exclusions.append(
                    (
                        row,
                        name,
                        classification,
                        "",
                        "name is absent from the complete current V4 environment",
                    )
                )
                if classification == "MISSING_PROJECT_ENDPOINT":
                    errors.append(
                        f"{row.ledger}:{row.row_id}: project endpoint absent "
                        f"from V4: {name}"
                    )
                continue
            if v4_row["kind"] != "theorem":
                exclusions.append(
                    (
                        row,
                        name,
                        "PROJECT_NON_THEOREM_ENDPOINT",
                        v4_row["kind"],
                        "V7 threshold rule is defined over Tier-B theorem endpoints",
                    )
                )
                continue
            endpoint_rows[name].append(row)

    if suspect_rows != EXPECTED_SUSPECT_ROWS:
        errors.append(
            f"explicitly suspect Tier-B rows: expected "
            f"{EXPECTED_SUSPECT_ROWS}, observed {suspect_rows}"
        )

    output_path.parent.mkdir(parents=True, exist_ok=True)
    with output_path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.writer(handle, delimiter="\t", lineterminator="\n")
        writer.writerow(
            [
                "name",
                "module",
                "v4_kind",
                "tier_b_row_count",
                "row_sets",
                "row_ids",
                "chapters",
                "book_labels",
                "source_ledgers",
            ]
        )
        for name in sorted(endpoint_rows):
            rows = endpoint_rows[name]
            v4_row = v4[name]
            writer.writerow(
                [
                    name,
                    v4_row["module"],
                    v4_row["kind"],
                    len(rows),
                    ";".join(sorted({row.row_set for row in rows})),
                    ";".join(sorted(row.row_id for row in rows)),
                    ";".join(sorted({row.chapter for row in rows})),
                    ";".join(sorted({row.book_label for row in rows})),
                    ";".join(sorted({row.ledger for row in rows})),
                ]
            )

    with exclusions_path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.writer(handle, delimiter="\t", lineterminator="\n")
        writer.writerow(
            [
                "row_id",
                "row_set",
                "chapter",
                "book_label",
                "name",
                "classification",
                "v4_kind",
                "reason",
                "ledger",
                "source_locations",
            ]
        )
        for row, name, classification, kind, reason in sorted(
            exclusions,
            key=lambda item: (
                item[2],
                item[0].ledger,
                item[0].row_id,
                item[1],
            ),
        ):
            writer.writerow(
                [
                    row.row_id,
                    row.row_set,
                    row.chapter,
                    row.book_label,
                    name,
                    classification,
                    kind,
                    reason,
                    row.ledger,
                    ";".join(row.source_locations),
                ]
            )

    exclusion_counts = collections.Counter(item[2] for item in exclusions)
    selected_reference_count = sum(
        len(row.resolved_declarations)
        for row in selected
    )
    lines = [
        "V6 TIER-B PROJECT THEOREM ENDPOINT UNION",
        "==========================================",
        f"verdict: {'PASS' if not errors else 'FAIL'}",
        f"mandatory_readme_rows: {len(main)}",
        f"supplemental_census_rows: {len(supplements)}",
        f"selected_union_rows: {len(selected)}",
        f"explicitly_suspect_rows: {suspect_rows}",
        f"suspect_stale_endpoint_rows: {suspect_stale_endpoint_rows}",
        f"resolved_declaration_references: {selected_reference_count}",
        f"unique_project_theorem_endpoints: {len(endpoint_rows)}",
        f"excluded_declaration_references: {len(exclusions)}",
        "",
        "[exclusion_counts]",
        *(
            f"{classification}: {count}"
            for classification, count in sorted(exclusion_counts.items())
        ),
        "",
        "[errors]",
        *(errors or ["(none)"]),
    ]
    summary_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print("\n".join(lines))
    return 1 if errors else 0


def self_test() -> int:
    assert _split_names("A; B ;") == ("A", "B")
    assert _split_locations(".lake/packages/x:1; .lake/packages/y:2") == (
        ".lake/packages/x:1",
        ".lake/packages/y:2",
    )
    external = SelectedRow(
        ledger="x.tsv",
        row_set="readme_correspondence",
        row_id="r",
        chapter="Chapter 1",
        book_label="Lemma 1",
        verdict="OK",
        resolved_declarations=("Finset.foo",),
        source_locations=(".lake/packages/mathlib/Mathlib/X.lean:1",),
    )
    project = SelectedRow(
        ledger="x.tsv",
        row_set="readme_correspondence",
        row_id="p",
        chapter="Chapter 1",
        book_label="Lemma 2",
        verdict="OK",
        resolved_declarations=("HDP.Chapter1.foo",),
        source_locations=("HighDimensionalProbability/Chapter1_X.lean:1",),
    )
    assert _looks_external(external, "Finset.foo")
    assert not _looks_external(project, "HDP.Chapter1.foo")
    print("PASS: V6 Tier-B endpoint-union self-test")
    return 0


def _resolve(path: Path) -> Path:
    return path if path.is_absolute() else ROOT / path


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument(
        "--v4-audit",
        type=Path,
        default=DEFAULT_V4.relative_to(ROOT),
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=DEFAULT_OUTPUT.relative_to(ROOT),
    )
    parser.add_argument(
        "--exclusions",
        type=Path,
        default=DEFAULT_EXCLUSIONS.relative_to(ROOT),
    )
    parser.add_argument(
        "--summary",
        type=Path,
        default=DEFAULT_SUMMARY.relative_to(ROOT),
    )
    args = parser.parse_args()
    if args.self_test:
        return self_test()
    return build(
        v4_path=_resolve(args.v4_audit),
        output_path=_resolve(args.output),
        exclusions_path=_resolve(args.exclusions),
        summary_path=_resolve(args.summary),
    )


if __name__ == "__main__":
    raise SystemExit(main())
