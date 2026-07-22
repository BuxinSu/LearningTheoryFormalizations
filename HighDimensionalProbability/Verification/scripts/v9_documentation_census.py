#!/usr/bin/env python3
"""Static V9 audit of current documentation and census claims.

This audit deliberately does not invoke Lean, Lake, Git, or the network.  It
keeps two census layers visibly separate:

* ``review_census_838`` is immutable historical evidence; and
* ``review_census_835`` is the active post-removal projection.

The active projection removes three conclusions, retains Exercise 8.39(b) as
core-proved, and retains the Brownian row as Appendix-proved.  Its exact split
is ``835 = 769 core + 66 Appendix proved + 0 deferred``.  The active Appendix
registry is independently ``14/14`` source-faithful targets; its fifteenth
direct import is the non-target Borell domain-support module.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import io
import json
import re
import runpy
import sys
from collections import Counter
from pathlib import Path
from typing import Iterable, Mapping


ROOT = Path(__file__).resolve().parents[3]
HDP = ROOT / "HighDimensionalProbability"
VERIFICATION = HDP / "Verification"
INVENTORY = VERIFICATION / "inventory"
REVIEW = VERIFICATION / "review"
OUTPUT = REVIEW / "recert_v9_documentation_census.tsv"
SUMMARY = REVIEW / "recert_v9_documentation_census_summary.txt"
FROZEN_CENSUS_TSV = INVENTORY / "review_census_838.tsv"
FROZEN_CENSUS_JSON = INVENTORY / "review_census_838.json"
ACTIVE_CENSUS_TSV = INVENTORY / "review_census_835.tsv"
ACTIVE_CENSUS_JSON = INVENTORY / "review_census_835.json"

EXPECTED_FROZEN_CENSUS_TSV_SHA256 = (
    "184f44ef33c9318450b9b31282c02850868cdafb93fe7ad722219acd7e6e1857"
)
EXPECTED_FROZEN_CENSUS_JSON_SHA256 = (
    "facc370aac1cd62dbcbbbe1bad54ff6175ea6768cda31111eb630aed1e5de284"
)
REMOVED_ROW_IDS = frozenset(
    {
        "census-bf1de680f35b52dc",
        "census-628be74004e48217",
        "census-939078c2ac4f78a5",
    }
)
BROWNIAN_ROW_ID = "census-360c40946511e7a9"
EXERCISE_8_39_ROW_ID = "census-8e50e84b6b82a573"
REMOVED_DECLARATIONS = (
    "GaussianChevetUpperPrinciple",
    "exercise_8_39a_gaussian_chevet_arbitrary_envelope",
    "gaussianChevetExpectationEnvelope_ne_top_of_isBounded",
    "remark_8_6_3_gaussian_chevet_arbitrary_envelope",
    "exercise_8_39a_gaussian_chevet_arbitrary",
    "remark_8_6_3_gaussian_chevet_arbitrary",
    "gaussianChevetUpperPrinciple_external",
    "positive_ricci_concentration",
    "positive_ricci_concentration_psi2",
    "positive_ricci_concentration_psi2_of_lipschitz",
    "BorellConvexBodyPsiOnePrinciple",
    "convexBodyUniform_marginal_subExponential_of_borell",
)
REMOVED_FILES = (
    HDP / "Appendix" / "GaussianChevet.lean",
    HDP / "Appendix" / "PositiveRicciConcentration.lean",
)

ROOT_README = ROOT / "README.md"
PACKAGE_README = HDP / "README.md"
REVIEW_NOTES = VERIFICATION / "REVIEW_NOTES.md"
CORRECTION_LEDGER = VERIFICATION / "CORRECTION_LEDGER.md"
APPENDIX_SUMMARY = HDP / "APPENDIX_SUMMARY.md"
APPENDIX_REGISTRY = HDP / "Appendix.lean"

REQUESTED_REVIEW_CENSUS = HDP / "REVIEW_CENSUS.md"
REQUESTED_PLACEHOLDER_LEDGER = HDP / "PLACEHOLDER_LEDGER.md"

FIELDS = (
    "claim_id",
    "category",
    "severity",
    "verdict",
    "claim_file",
    "claim_line",
    "claim_scope",
    "claim",
    "claimed_value",
    "observed_value",
    "evidence",
    "recommended_action",
)

ALLOWED_VERDICTS = {"MATCH", "STALE", "OVERSTATED", "UNVERIFIABLE"}
ALLOWED_SEVERITIES = {"CRITICAL", "MAJOR", "MINOR"}


def relative(path: Path) -> str:
    try:
        return path.relative_to(ROOT).as_posix()
    except ValueError:
        return path.as_posix()


def find_line(path: Path, fragment: str, *, occurrence: int = 1) -> int:
    """Return the exact one-based line containing the selected fragment."""

    seen = 0
    for number, line in enumerate(
        path.read_text(encoding="utf-8").splitlines(), start=1
    ):
        if fragment in line:
            seen += 1
            if seen == occurrence:
                return number
    raise RuntimeError(f"{relative(path)}: fragment not found: {fragment!r}")


def find_semantic_paragraph(path: Path, fragments: tuple[str, ...]) -> int:
    """Return the unique paragraph containing every normalized semantic anchor."""

    if not fragments:
        raise ValueError("semantic paragraph search requires at least one fragment")
    lines = path.read_text(encoding="utf-8").splitlines()
    paragraphs: list[tuple[int, str]] = []
    start: int | None = None
    body: list[str] = []
    for number, line in enumerate((*lines, ""), start=1):
        if line.strip():
            if start is None:
                start = number
            body.append(line.strip())
            continue
        if start is not None:
            paragraphs.append((start, " ".join(" ".join(body).split())))
            start = None
            body = []
    normalized = tuple(" ".join(fragment.split()) for fragment in fragments)
    matches = [
        line
        for line, paragraph in paragraphs
        if all(fragment in paragraph for fragment in normalized)
    ]
    if len(matches) != 1:
        raise RuntimeError(
            f"{relative(path)}: semantic paragraph anchors matched "
            f"{len(matches)} paragraphs, expected 1: {normalized!r}"
        )
    return matches[0]


def read_tsv(path: Path) -> list[dict[str, str]]:
    with path.open(encoding="utf-8", newline="") as handle:
        return list(csv.DictReader(handle, delimiter="\t"))


def json_list(cell: str) -> list[str]:
    value = json.loads(cell)
    if not isinstance(value, list) or not all(isinstance(item, str) for item in value):
        raise RuntimeError(f"expected a JSON string list, got {cell!r}")
    return value


def mask_lean_noncode(text: str) -> str:
    """Mask Lean comments and strings without changing offsets."""

    masked = list(text)
    index = 0
    state = "code"
    block_depth = 0
    while index < len(text):
        if state == "code":
            if text.startswith("--", index):
                state = "line_comment"
                masked[index] = " "
                if index + 1 < len(text):
                    masked[index + 1] = " "
                index += 2
            elif text.startswith("/-", index):
                state = "block_comment"
                block_depth = 1
                masked[index] = " "
                if index + 1 < len(text):
                    masked[index + 1] = " "
                index += 2
            elif text[index] == '"':
                state = "string"
                masked[index] = " "
                index += 1
            else:
                index += 1
        elif state == "line_comment":
            if text[index] in "\r\n":
                state = "code"
            else:
                masked[index] = " "
            index += 1
        elif state == "block_comment":
            if text.startswith("/-", index):
                block_depth += 1
                masked[index] = " "
                if index + 1 < len(text):
                    masked[index + 1] = " "
                index += 2
            elif text.startswith("-/", index):
                block_depth -= 1
                masked[index] = " "
                if index + 1 < len(text):
                    masked[index + 1] = " "
                index += 2
                if block_depth == 0:
                    state = "code"
            else:
                if text[index] not in "\r\n":
                    masked[index] = " "
                index += 1
        else:
            if text[index] == "\\":
                masked[index] = " "
                index += 1
                if index < len(text):
                    if text[index] not in "\r\n":
                        masked[index] = " "
                    index += 1
            elif text[index] == '"':
                masked[index] = " "
                index += 1
                state = "code"
            else:
                if text[index] not in "\r\n":
                    masked[index] = " "
                index += 1
    if state in {"block_comment", "string"}:
        raise RuntimeError(f"unterminated Lean {state}")
    return "".join(masked)


def code_token_count(paths: Iterable[Path], expression: str) -> int:
    pattern = re.compile(expression, re.MULTILINE)
    return sum(
        len(list(pattern.finditer(mask_lean_noncode(path.read_text(encoding="utf-8")))))
        for path in paths
    )


def declaration_exists(paths: Iterable[Path], name: str) -> bool:
    escaped = re.escape(name)
    pattern = re.compile(
        rf"(?m)^[ \t]*(?:@\[[^\n]*\][ \t]*)?"
        rf"(?:(?:private|protected|noncomputable|unsafe|local)[ \t]+)*"
        rf"(?:theorem|lemma|def|abbrev|structure|class|alias|irreducible_def)"
        rf"[ \t]+{escaped}(?=[ \t({{[:=]|$)"
    )
    return any(
        pattern.search(mask_lean_noncode(path.read_text(encoding="utf-8")))
        for path in paths
        if path.is_file()
    )


def declaration_signature(path: Path, name: str) -> str:
    """Return the code from a declaration keyword through its ``:=``."""

    code = mask_lean_noncode(path.read_text(encoding="utf-8"))
    match = re.search(
        rf"(?ms)^[ \t]*(?:theorem|lemma|def)[ \t]+{re.escape(name)}\b(.*?):=",
        code,
    )
    if match is None:
        raise RuntimeError(f"{relative(path)}: declaration not found: {name}")
    return match.group(0)


def count_marked_exercise_sorries(paths: Iterable[Path]) -> tuple[int, int, int]:
    total = 0
    files_with = 0
    marked = 0
    for path in paths:
        text = path.read_text(encoding="utf-8")
        code = mask_lean_noncode(text)
        matches = list(re.finditer(r"\bsorry\b", code))
        if matches:
            files_with += 1
        previous = 0
        for match in matches:
            total += 1
            if "EXERCISE-SORRY" in text[previous : match.start()]:
                marked += 1
            previous = match.end()
    return total, files_with, marked


def audit_declaration_counts() -> dict[str, object]:
    """Reuse the repository's canonical lexical docstring scanner."""

    module = runpy.run_path(str(ROOT / "scripts" / "audit_docstrings.py"))
    lean_files = list(module["lean_files"](HDP.resolve()))
    declarations = []
    issues = []
    for path in lean_files:
        file_declarations, file_issues = module["audit_file"](path, HDP.resolve())
        declarations.extend(file_declarations)
        issues.extend(file_issues)

    core_files = sorted((HDP / "Prelude").rglob("*.lean")) + sorted(
        HDP.glob("Chapter*.lean")
    )
    core_declarations = []
    for path in core_files:
        file_declarations, _ = module["audit_file"](path, HDP.resolve())
        core_declarations.extend(file_declarations)

    return {
        "documentation_files": len(lean_files),
        "documentation_total": len(declarations),
        "documentation_kinds": Counter(item.kind for item in declarations),
        "documentation_issues": len(issues),
        "core_files": len(core_files),
        "core_total": len(core_declarations),
        "core_kinds": Counter(item.kind for item in core_declarations),
    }


def current_observations() -> dict[str, object]:
    frozen_census = read_tsv(FROZEN_CENSUS_TSV)
    active_census = read_tsv(ACTIVE_CENSUS_TSV)
    frozen_by_id = {row["row_id"]: row for row in frozen_census}
    active_by_id = {row["row_id"]: row for row in active_census}
    if len(frozen_by_id) != len(frozen_census):
        raise RuntimeError("duplicate row ID in frozen 838 census")
    if len(active_by_id) != len(active_census):
        raise RuntimeError("duplicate row ID in active 835 census")

    frozen_digest = hashlib.sha256(FROZEN_CENSUS_TSV.read_bytes()).hexdigest()
    frozen_json_digest = hashlib.sha256(FROZEN_CENSUS_JSON.read_bytes()).hexdigest()
    active_payload = json.loads(ACTIVE_CENSUS_JSON.read_text(encoding="utf-8"))
    active_metadata = active_payload["metadata"]
    if active_metadata["removed_row_ids"] != sorted(REMOVED_ROW_IDS):
        raise RuntimeError("active-census JSON removed-row metadata disagrees")
    if set(active_by_id) != set(frozen_by_id) - REMOVED_ROW_IDS:
        raise RuntimeError("active census is not exactly frozen census minus three rows")
    if len(active_payload["rows"]) != len(active_census):
        raise RuntimeError("active census JSON/TSV row counts disagree")

    frozen_buckets = Counter(row["coverage_bucket"] for row in frozen_census)
    active_buckets = Counter(row["coverage_bucket"] for row in active_census)
    brownian_row = active_by_id[BROWNIAN_ROW_ID]
    exercise_8_39_row = active_by_id[EXERCISE_8_39_ROW_ID]

    readme_payload = json.loads(
        (INVENTORY / "readme_correspondence.json").read_text(encoding="utf-8")
    )
    readme_rows = readme_payload["rows"]
    readme_endpoints = {
        endpoint for row in readme_rows for endpoint in row["endpoint_names"]
    }
    readme_chapters = Counter(row["chapter"] for row in readme_rows)

    v6_paths = (
        REVIEW / "v6_tier_b_ch0_4.tsv",
        REVIEW / "v6_tier_b_ch5_7.tsv",
        REVIEW / "v6_tier_b_ch8_9.tsv",
    )
    v6_rows = [row for path in v6_paths for row in read_tsv(path)]
    v6_readme_rows = [
        row
        for row in v6_rows
        if row.get("row_set") == "readme_correspondence"
        or row.get("sample_kind") == "mandatory_readme"
    ]
    readme_ids = {row["row_id"] for row in readme_rows}
    v6_ids = {row["row_id"] for row in v6_readme_rows}
    if readme_ids != v6_ids:
        raise RuntimeError(
            "V6 evidence does not exactly cover the current 611 README row IDs"
        )

    declaration_counts = audit_declaration_counts()
    exercise_paths = sorted(HDP.glob("Exercise/Chapter*/*.lean"))
    exercise_sorries, exercise_files_with_sorry, marked_sorries = (
        count_marked_exercise_sorries(exercise_paths)
    )
    exercise_inventory = read_tsv(INVENTORY / "exercise_leaf_declarations.tsv")
    sampling_plan = read_tsv(INVENTORY / "sampling_plan.tsv")

    appendix_paths = [APPENDIX_REGISTRY, *sorted((HDP / "Appendix").rglob("*.lean"))]
    all_hdp_paths = sorted(
        path
        for path in HDP.rglob("*.lean")
        if "Verification" not in path.parts and not path.is_symlink()
    )
    source_paths = [ROOT / "HighDimensionalProbability.lean", *all_hdp_paths]
    matrix_paths = sorted(
        path
        for path in (ROOT / "MatrixConcentration").rglob("*.lean")
        if not path.is_symlink()
    )
    forbidden = {
        "sorry": code_token_count(appendix_paths, r"\bsorry\b"),
        "admit": code_token_count(appendix_paths, r"\badmit\b"),
        "axiom": code_token_count(appendix_paths, r"^[ \t]*axiom\b"),
        "unsafe": code_token_count(appendix_paths, r"\bunsafe\b"),
        "native_decide": code_token_count(appendix_paths, r"\bnative_decide\b"),
    }
    whole_escape = {
        "admit": code_token_count(source_paths, r"\badmit\b"),
        "axiom": code_token_count(source_paths, r"^[ \t]*axiom\b"),
        "unsafe": code_token_count(source_paths, r"\bunsafe\b"),
        "native_decide": code_token_count(source_paths, r"\bnative_decide\b"),
    }

    core_files = sorted((HDP / "Prelude").rglob("*.lean")) + sorted(
        HDP.glob("Chapter*.lean")
    )
    core_forbidden = sum(
        code_token_count(core_files, pattern)
        for pattern in (
            r"\bsorry\b",
            r"\badmit\b",
            r"^[ \t]*axiom\b",
            r"\bunsafe\b",
        )
    )

    nonappendix_paths = [
        path
        for path in source_paths
        if path != APPENDIX_REGISTRY and (HDP / "Appendix") not in path.parents
    ]
    appendix_import_leaks = 0
    for path in nonappendix_paths:
        code = mask_lean_noncode(path.read_text(encoding="utf-8"))
        appendix_import_leaks += len(
            re.findall(
                r"(?m)^import[ \t]+HighDimensionalProbability\.Appendix(?:\.|[ \t]*$)",
                code,
            )
        )

    registry_imports = [
        line
        for line in APPENDIX_REGISTRY.read_text(encoding="utf-8").splitlines()
        if line.startswith("import HighDimensionalProbability.Appendix.")
    ]
    appendix_summary_lines = APPENDIX_SUMMARY.read_text(encoding="utf-8").splitlines()
    active_registry_rows = [
        line
        for line in appendix_summary_lines[:40]
        if re.match(r"^\|\s*\d+\s*\|", line)
    ]

    chapter8 = HDP / "Chapter8_Chaining.lean"
    finite_chevet_signatures = {
        name: declaration_signature(chapter8, name)
        for name in (
            "exercise_8_39a_gaussian_chevet",
            "remark_8_6_3_gaussian_chevet",
        )
    }
    removed_reference_counts = {
        name: code_token_count(source_paths, rf"(?<![\w']){re.escape(name)}(?![\w'])")
        for name in REMOVED_DECLARATIONS
    }
    borell_file = HDP / "Appendix" / "BorellConvexBody.lean"
    borell_support_declarations = [
        name
        for name in (
            "convexBodyUniformMeasure",
            "convexBodyUniformMeasure_isProbability",
            "convexBodyUniformVector_measurable",
            "convexBodyUniformVector_memLp_two",
            "convexBodyUniformVector_isIsotropicRandomVector",
        )
        if declaration_exists([borell_file], name)
    ]
    endpoint_presence = {
        "finite_chevet_a": declaration_exists(
            [chapter8], "exercise_8_39a_gaussian_chevet"
        ),
        "finite_chevet_remark": declaration_exists(
            [chapter8], "remark_8_6_3_gaussian_chevet"
        ),
        "chevet_reverse": declaration_exists(
            [chapter8], "exercise_8_39b_gaussian_chevet_reverse_arbitrary"
        ),
        "brownian": declaration_exists(
            [HDP / "Appendix" / "BrownianReflection.lean"],
            "brownianReflectionPrinciple_external",
        ),
    }

    summary_tsv = {
        row["metric"]: row["value"]
        for row in read_tsv(INVENTORY / "inventory_summary.tsv")
    }
    endpoint_union = read_tsv(INVENTORY / "endpoint_union.tsv")
    endpoint_union_names = {row["endpoint"] for row in endpoint_union}

    inventory_json = json.loads(
        (INVENTORY / "inventory_summary.json").read_text(encoding="utf-8")
    )
    hash_matches = {}
    for source, recorded in inventory_json["source_sha256"].items():
        observed = hashlib.sha256((ROOT / source).read_bytes()).hexdigest()
        hash_matches[source] = observed == recorded

    return {
        "census": active_census,
        "frozen_census": frozen_census,
        "active_census": active_census,
        "frozen_by_id": frozen_by_id,
        "active_by_id": active_by_id,
        "frozen_buckets": frozen_buckets,
        "current_buckets": active_buckets,
        "active_buckets": active_buckets,
        "active_metadata": active_metadata,
        "frozen_digest": frozen_digest,
        "frozen_json_digest": frozen_json_digest,
        "brownian_row": brownian_row,
        "exercise_8_39_row": exercise_8_39_row,
        "readme_rows": readme_rows,
        "readme_endpoints": readme_endpoints,
        "readme_chapters": readme_chapters,
        "v6_readme_rows": v6_readme_rows,
        "v6_all_ok": all(row["verdict"] == "OK" for row in v6_readme_rows),
        "v6_locations_complete": all(
            bool(row["source_locations"]) for row in v6_readme_rows
        ),
        "declarations": declaration_counts,
        "exercise_paths": exercise_paths,
        "exercise_sorries": exercise_sorries,
        "exercise_files_with_sorry": exercise_files_with_sorry,
        "marked_sorries": marked_sorries,
        "exercise_inventory": exercise_inventory,
        "sampling_plan": sampling_plan,
        "appendix_paths": appendix_paths,
        "appendix_forbidden": forbidden,
        "whole_escape": whole_escape,
        "core_forbidden": core_forbidden,
        "appendix_import_leaks": appendix_import_leaks,
        "registry_imports": registry_imports,
        "active_registry_rows": active_registry_rows,
        "endpoint_presence": endpoint_presence,
        "finite_chevet_signatures": finite_chevet_signatures,
        "removed_reference_counts": removed_reference_counts,
        "removed_files_absent": all(not path.exists() for path in REMOVED_FILES),
        "borell_support_declarations": borell_support_declarations,
        "inventory_summary_tsv": summary_tsv,
        "inventory_summary_json": inventory_json,
        "inventory_hash_matches": hash_matches,
        "endpoint_union": endpoint_union,
        "endpoint_union_names": endpoint_union_names,
        "physical_hdp_files": len(all_hdp_paths),
        "physical_matrix_files": len(matrix_paths),
        "physical_library_files": len(all_hdp_paths) + len(matrix_paths),
    }


def build_claims(observed: Mapping[str, object]) -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []

    def add(
        claim_id: str,
        category: str,
        severity: str,
        verdict: str,
        path: Path,
        line: int,
        scope: str,
        claim: str,
        claimed: str,
        value: str,
        evidence: str,
        action: str,
    ) -> None:
        if verdict not in ALLOWED_VERDICTS:
            raise RuntimeError(f"{claim_id}: invalid verdict {verdict}")
        if severity not in ALLOWED_SEVERITIES:
            raise RuntimeError(f"{claim_id}: invalid severity {severity}")
        rows.append(
            {
                "claim_id": claim_id,
                "category": category,
                "severity": severity,
                "verdict": verdict,
                "claim_file": relative(path),
                "claim_line": str(line),
                "claim_scope": scope,
                "claim": claim,
                "claimed_value": claimed,
                "observed_value": value,
                "evidence": evidence,
                "recommended_action": action,
            }
        )

    census = observed["census"]
    frozen = observed["frozen_buckets"]
    current = observed["current_buckets"]
    declarations = observed["declarations"]
    readme_rows = observed["readme_rows"]
    endpoints = observed["readme_endpoints"]
    chapters = observed["readme_chapters"]
    presence = observed["endpoint_presence"]
    appendix_forbidden = observed["appendix_forbidden"]

    frozen_text = (
        f"{len(census)} = {frozen['core_formalized']} core + "
        f"{frozen['appendix_proved']} Appendix proved + "
        f"{frozen['appendix_unresolved_or_deferred']} deferred"
    )
    current_text = (
        f"{len(census)} = {current['core_formalized']} core + "
        f"{current['appendix_proved']} Appendix proved + "
        f"{current['appendix_unresolved_or_deferred']} deferred"
    )
    decl_core = declarations["core_kinds"]
    decl_docs = declarations["documentation_kinds"]
    core_text = (
        f"{declarations['core_total']} = {decl_core['theorem']} theorem + "
        f"{decl_core['lemma']} lemma + {decl_core['def']} def in "
        f"{declarations['core_files']} files"
    )
    docs_text = (
        f"{declarations['documentation_total']} = {decl_docs['theorem']} theorem + "
        f"{decl_docs['lemma']} lemma + {decl_docs['def']} def in "
        f"{declarations['documentation_files']} files; "
        f"{declarations['documentation_issues']} doc/citation issues"
    )
    map_text = (
        f"{len(readme_rows)} rows, {len(endpoints)} unique endpoint names; "
        f"V6 row-ID coverage {len(observed['v6_readme_rows'])}, "
        f"all OK={str(observed['v6_all_ok']).lower()}, "
        f"all locations present={str(observed['v6_locations_complete']).lower()}"
    )
    chapter_text = (
        f"Appetizer {chapters['Appetizer']}; Chapters 1-9 "
        + "/".join(str(chapters[f"Chapter {number}"]) for number in range(1, 10))
    )
    appendix_token_text = ", ".join(
        f"{name}={count}" for name, count in appendix_forbidden.items()
    )

    # Requested-but-absent document names.
    add(
        "MISSING_REVIEW_CENSUS_DOCUMENT",
        "document_presence",
        "MINOR",
        "UNVERIFIABLE" if not REQUESTED_REVIEW_CENSUS.exists() else "MATCH",
        REQUESTED_REVIEW_CENSUS,
        0,
        "requested document",
        "A REVIEW_CENSUS.md document is available for direct audit.",
        "present",
        "missing; current equivalent is review_census_838.tsv plus REVIEW_NOTES.md",
        f"{relative(REQUESTED_REVIEW_CENSUS)} does not exist; "
        f"{relative(INVENTORY / 'review_census_838.tsv')}:1 has {len(census)} rows",
        "Use the current equivalent paths; do not invent the missing filename.",
    )
    add(
        "MISSING_PLACEHOLDER_LEDGER_DOCUMENT",
        "document_presence",
        "MINOR",
        "UNVERIFIABLE" if not REQUESTED_PLACEHOLDER_LEDGER.exists() else "MATCH",
        REQUESTED_PLACEHOLDER_LEDGER,
        0,
        "requested document",
        "A PLACEHOLDER_LEDGER.md document is available for direct audit.",
        "present",
        "missing; current equivalent is CORRECTION_LEDGER.md plus source scan",
        f"{relative(REQUESTED_PLACEHOLDER_LEDGER)} does not exist; "
        f"current record is {relative(CORRECTION_LEDGER)}",
        "Use the current equivalent paths; do not invent the missing filename.",
    )

    # Root README.
    root_line = find_line(ROOT_README, "together with 611 audited")
    add(
        "ROOT_README_611_ROWS",
        "publication_map",
        "MINOR",
        "MATCH" if len(readme_rows) == 611 else "STALE",
        ROOT_README,
        root_line,
        "current numeric count",
        "The public correspondence contains 611 mappings.",
        "611",
        map_text,
        f"{relative(INVENTORY / 'readme_correspondence.tsv')}:1; three V6 ledgers",
        "None.",
    )
    add(
        "ROOT_README_ALL_VERIFIED",
        "publication_map",
        "MINOR",
        "UNVERIFIABLE",
        ROOT_README,
        root_line,
        "semantic/kernel claim",
        "All 611 mappings are verified.",
        "all verified",
        map_text
        + "; V6 explicitly excludes full prose-to-endpoint correspondence and kernel checking",
        "V6 establishes static endpoint usability/location, not the blanket verification claim.",
        "Retain only with a separately reproducible PDF-faithfulness and kernel audit.",
    )
    add(
        "ROOT_README_838_TOTAL",
        "census",
        "MINOR",
        "MATCH" if len(census) == 838 else "STALE",
        ROOT_README,
        root_line,
        "current total",
        "The PDF-revalidated census has 838 valid conclusions.",
        "838",
        current_text,
        f"{relative(INVENTORY / 'review_census_838.tsv')}:1",
        "None.",
    )
    add(
        "ROOT_README_768_65_5",
        "census",
        "MAJOR",
        "STALE" if current["appendix_proved"] != 65 else "MATCH",
        ROOT_README,
        root_line,
        "present-tense current status",
        "The current census split is 768 / 65 / 5.",
        "768 core; 65 Appendix proved; 5 deferred",
        f"frozen artifact: {frozen_text}; current source projection: {current_text}",
        f"{relative(APPENDIX_SUMMARY)}:6-13 and Brownian source endpoint",
        "Label 65/5 as the frozen Pass-07 snapshot or publish the current 66/4 projection.",
    )
    add(
        "ROOT_README_CORE_DECLARATIONS",
        "declaration_counts",
        "MINOR",
        "MATCH" if declarations["core_total"] == 5630 else "STALE",
        ROOT_README,
        root_line,
        "current lexical source count",
        "The consolidated core has 5,630 = 2,867 / 1,608 / 1,155 target declarations.",
        "5630 = 2867 theorem + 1608 lemma + 1155 def",
        core_text,
        "Static canonical docstring scanner over Prelude plus Chapter0-9 consolidated files.",
        "None.",
    )
    add(
        "ROOT_README_DOCUMENTATION_DECLARATIONS",
        "declaration_counts",
        "MINOR",
        "MATCH" if declarations["documentation_total"] == 6078 else "STALE",
        ROOT_README,
        root_line,
        "current lexical source count",
        "The non-Appendix documentation audit covers 6,078 declarations in 101 files.",
        "6078 in 101",
        docs_text,
        "Static canonical docstring scanner over the non-Appendix source universe.",
        "None.",
    )

    # Package README headline counts.
    package_map_line = find_line(PACKAGE_README, "| Book → Lean correspondence |")
    add(
        "PACKAGE_README_611_ROWS_AND_STATUS",
        "publication_map",
        "MINOR",
        "UNVERIFIABLE",
        PACKAGE_README,
        package_map_line,
        "mixed numeric/semantic claim",
        "611 mappings are all verified, with zero partial.",
        "611 verified; 0 partial",
        map_text + "; numeric row count matches, blanket verification is outside static scope",
        f"{relative(INVENTORY / 'readme_correspondence.json')}:1 and V6 evidence",
        "Split the reproducible row/name count from the semantic/kernel verification claim.",
    )
    distribution_line = find_line(PACKAGE_README, "| Chapter distribution |")
    add(
        "PACKAGE_README_CHAPTER_DISTRIBUTION",
        "publication_map",
        "MINOR",
        "MATCH"
        if [chapters[f"Chapter {n}"] for n in range(1, 10)]
        == [51, 59, 75, 88, 68, 39, 62, 100, 61]
        else "STALE",
        PACKAGE_README,
        distribution_line,
        "current numeric count",
        "The 611 rows have the stated Appetizer/Chapter distribution.",
        "8; 51/59/75/88/68/39/62/100/61",
        chapter_text,
        f"{relative(INVENTORY / 'readme_correspondence.tsv')}:1",
        "None.",
    )
    package_census_line = find_line(PACKAGE_README, "| PDF-revalidated whole-book census |")
    add(
        "PACKAGE_README_838_TOTAL",
        "census",
        "MINOR",
        "MATCH" if len(census) == 838 else "STALE",
        PACKAGE_README,
        package_census_line,
        "current total",
        "The whole-book census contains 838 valid conclusions.",
        "838",
        current_text,
        f"{relative(INVENTORY / 'review_census_838.tsv')}:1",
        "None.",
    )
    add(
        "PACKAGE_README_768_65_5",
        "census",
        "MAJOR",
        "STALE" if current["appendix_proved"] == 66 else "MATCH",
        PACKAGE_README,
        package_census_line,
        "present-tense current status",
        "The current census split is 768 / 65 / 5.",
        "768 core; 65 Appendix proved; 5 deferred",
        f"frozen artifact: {frozen_text}; current source projection: {current_text}",
        f"{relative(APPENDIX_SUMMARY)}:6-13",
        "Label 65/5 historical or update the current projection to 66/4.",
    )
    package_core_line = find_line(PACKAGE_README, "| Consolidated core declarations |")
    add(
        "PACKAGE_README_CORE_DECLARATIONS",
        "declaration_counts",
        "MINOR",
        "MATCH" if declarations["core_total"] == 5630 else "STALE",
        PACKAGE_README,
        package_core_line,
        "current lexical source count",
        "The consolidated core declaration split is 5,630 = 2,867 / 1,608 / 1,155.",
        "5630 = 2867 theorem + 1608 lemma + 1155 def",
        core_text,
        "Static canonical docstring scanner.",
        "None.",
    )
    package_docs_line = find_line(PACKAGE_README, "| Non-Appendix documentation audit |")
    add(
        "PACKAGE_README_DOCUMENTATION_AUDIT",
        "declaration_counts",
        "MINOR",
        "MATCH"
        if declarations["documentation_total"] == 6078
        and declarations["documentation_files"] == 101
        and declarations["documentation_issues"] == 0
        else "STALE",
        PACKAGE_README,
        package_docs_line,
        "current lexical source count",
        "All 6,078 declarations in 101 files are documented with zero lexical issues.",
        "6078/6078 in 101; 3112/1610/1356; 0 issues",
        docs_text,
        "Static canonical docstring scanner.",
        "None.",
    )

    # Package README Appendix registry/table.
    package_registry_line = find_line(PACKAGE_README, "Of its 17 registered")
    add(
        "PACKAGE_README_APPENDIX_REGISTRY_COUNT",
        "appendix_registry",
        "MINOR",
        "MATCH" if len(observed["registry_imports"]) == 17 else "STALE",
        PACKAGE_README,
        package_registry_line,
        "current registry size",
        "The Appendix has 17 registered targets.",
        "17",
        f"{len(observed['registry_imports'])} target imports in Appendix.lean",
        f"{relative(APPENDIX_REGISTRY)}:1-17",
        "None.",
    )
    add(
        "PACKAGE_README_APPENDIX_13_PLUS_4",
        "appendix_registry",
        "MAJOR",
        "STALE",
        PACKAGE_README,
        package_registry_line,
        "implementation-registry status",
        "The registry has 13 source-faithful clean targets and four unresolved targets.",
        "13 proved + 4 unresolved",
        "14 source-faithful proved + 2 assumption-strengthened proved + 1 skipped",
        f"{relative(APPENDIX_SUMMARY)}:6-13,449-451",
        "Replace the obsolete registry split; keep census-level unresolved rows separate.",
    )
    add(
        "PACKAGE_README_APPENDIX_AXIOM_CLEAN",
        "kernel_verification",
        "MINOR",
        "UNVERIFIABLE",
        PACKAGE_README,
        package_registry_line + 1,
        "Lean kernel claim",
        "The source-faithful Appendix targets are axiom-clean.",
        "axiom-clean",
        f"Appendix source has zero forbidden tokens ({appendix_token_text}), "
        "but exact axiom dependencies require Lean elaboration",
        "No Lean/Lake invocation is permitted in this V9 static task.",
        "Bind the claim to a completed axiom log and exact source manifest.",
    )
    boundaries_line = find_line(PACKAGE_README, "boundaries remain explicit:")
    add(
        "PACKAGE_README_FOUR_BOUNDARIES_REMAIN",
        "appendix_registry",
        "MAJOR",
        "STALE",
        PACKAGE_README,
        boundaries_line,
        "implementation-registry status",
        "Chevet, positive Ricci, Borell, and Brownian all remain unresolved boundaries.",
        "4 unresolved targets",
        "Chevet/Ricci are assumption-strengthened proofs; Borell is skipped; Brownian is source-faithful proved",
        f"{relative(APPENDIX_SUMMARY)}:32-35",
        "Publish the current four-way outcomes, not the former blocker list.",
    )
    chevet_line = find_line(PACKAGE_README, "gaussianChevetUpperPrinciple_external")
    add(
        "PACKAGE_README_CHEVET_STATUS",
        "appendix_endpoint",
        "MAJOR",
        "STALE",
        PACKAGE_README,
        chevet_line,
        "implementation-registry status",
        "Gaussian Chevet is APPENDIX-UNRESOLVED-001.",
        "unresolved",
        f"endpoint exists={presence['chevet']}; proved only with explicit 0 ∈ T",
        f"{relative(HDP / 'Appendix' / 'GaussianChevet.lean')}:25",
        "Mark assumption-strengthened PROVED; retain two census rows as deferred.",
    )
    ricci_line = find_line(PACKAGE_README, "`HDP.Chapter5.positive_ricci_concentration`")
    add(
        "PACKAGE_README_POSITIVE_RICCI_STATUS",
        "appendix_endpoint",
        "MAJOR",
        "STALE",
        PACKAGE_README,
        ricci_line,
        "implementation-registry status",
        "Positive Ricci is APPENDIX-UNRESOLVED-002.",
        "unresolved",
        f"endpoint exists={presence['positive_ricci']}; proved with explicit RiemannianDiffusionLaw",
        f"{relative(HDP / 'Appendix' / 'PositiveRicciConcentration.lean')}:42",
        "Mark assumption-strengthened PROVED; retain its census row as deferred.",
    )
    borell_line = find_line(PACKAGE_README, "borellConvexBodyPsiOnePrinciple_external")
    add(
        "PACKAGE_README_BORELL_ENDPOINT_NAME",
        "appendix_endpoint",
        "MAJOR",
        "OVERSTATED" if not presence["borell_stale"] else "MATCH",
        PACKAGE_README,
        borell_line,
        "published declaration name",
        "HDP.Chapter3.borellConvexBodyPsiOnePrinciple_external is an Appendix declaration.",
        "named unconditional external witness",
        f"exact declaration exists={presence['borell_stale']}; "
        f"replacement interface={presence['borell_interface']}; "
        f"conditional theorem={presence['borell_conditional']}",
        f"{relative(HDP / 'Appendix' / 'BorellConvexBody.lean')}:114,133",
        "Replace the nonexistent name with the interface/conditional theorem and SKIPPED status.",
    )
    add(
        "PACKAGE_README_BORELL_STATUS",
        "appendix_endpoint",
        "MAJOR",
        "STALE",
        PACKAGE_README,
        borell_line,
        "implementation-registry status",
        "Borell is APPENDIX-UNRESOLVED-003.",
        "unresolved target",
        "Q3 is deliberately SKIPPED; no unconditional witness is exported",
        f"{relative(APPENDIX_SUMMARY)}:270-287",
        "Use SKIPPED for the registry and deferred for the source-faithful census row.",
    )
    brownian_line = find_line(PACKAGE_README, "brownianReflectionPrinciple_external")
    add(
        "PACKAGE_README_BROWNIAN_STATUS",
        "appendix_endpoint",
        "MAJOR",
        "STALE",
        PACKAGE_README,
        brownian_line,
        "implementation-registry and census status",
        "Brownian is APPENDIX-UNRESOLVED-004.",
        "unresolved",
        f"exact endpoint exists={presence['brownian']}; Appendix forbidden tokens: {appendix_token_text}",
        f"{relative(HDP / 'Appendix' / 'BrownianReflection.lean')}:159",
        "Mark source-faithful PROVED and move the census row from deferred to proved.",
    )
    repeated_map_line = find_line(PACKAGE_README, "This table records **611 audited mappings**")
    add(
        "PACKAGE_README_REPEATED_611_838",
        "publication_map",
        "MINOR",
        "UNVERIFIABLE",
        PACKAGE_README,
        repeated_map_line,
        "mixed numeric/semantic claim",
        "The publication map has 611 verified rows and the exhaustive census has 838.",
        "611 verified; 838 census",
        f"numeric counts match ({len(readme_rows)}, {len(census)}); blanket verified status remains outside static scope",
        f"{relative(INVENTORY / 'inventory_summary.tsv')}:2-4",
        "Separate reproducible counts from the semantic verification claim.",
    )

    # REVIEW_NOTES current and historical claims.
    review_boundary_line = find_line(REVIEW_NOTES, "four explicit research-scale appendix boundaries")
    add(
        "REVIEW_NOTES_FOUR_APPENDIX_BOUNDARIES",
        "appendix_registry",
        "MAJOR",
        "STALE",
        REVIEW_NOTES,
        review_boundary_line,
        "present-tense implementation status",
        "Four research-scale Appendix boundaries remain.",
        "4 unresolved targets",
        "current registry is 14 faithful + 2 assumption-strengthened + 1 skipped",
        f"{relative(APPENDIX_SUMMARY)}:6-13",
        "Update the live review or mark this section as the Pass-07 historical snapshot.",
    )
    review_total_line = find_line(REVIEW_NOTES, "**838 valid conclusions**")
    add(
        "REVIEW_NOTES_873_35_838",
        "census",
        "MINOR",
        "MATCH" if len(census) == 838 else "STALE",
        REVIEW_NOTES,
        review_total_line,
        "historical-row arithmetic and current total",
        "873 inputs minus 35 rejected gives 838 valid conclusions.",
        "873 - 35 = 838",
        f"review_census rows={len(census)}; gap disposition has 35 rejected rows",
        f"{relative(INVENTORY / 'review_gap_disposition_89.tsv')}:1",
        "None.",
    )
    review_bucket_line = find_line(REVIEW_NOTES, "**65 appendix-proved**")
    add(
        "REVIEW_NOTES_768_65_5",
        "census",
        "MAJOR",
        "STALE",
        REVIEW_NOTES,
        review_bucket_line,
        "present-tense final status",
        "The final current split is 768 / 65 / 5.",
        "768 core; 65 proved; 5 deferred",
        f"frozen artifact: {frozen_text}; current source projection: {current_text}",
        f"{relative(APPENDIX_SUMMARY)}:13 and Brownian endpoint",
        "Call 65/5 frozen Pass-07 data and publish 66/4 as the current projection.",
    )
    core_build_line = find_line(REVIEW_NOTES, "**Core build:**")
    add(
        "REVIEW_NOTES_CORE_BUILD_JOBS",
        "dynamic_verification",
        "MINOR",
        "UNVERIFIABLE",
        REVIEW_NOTES,
        core_build_line,
        "Lean/Lake run claim",
        "The core build passed 8,670 / 8,670 jobs.",
        "PASS 8670/8670",
        "not rerun; static source audit cannot authenticate an exit status or job count",
        f"{relative(VERIFICATION / 'logs' / 'build_full.log')} is evidence-only "
        "and records a differently scoped command",
        "Treat as recorded run metadata unless reproduced under the exact command/source manifest.",
    )
    appendix_build_line = find_line(REVIEW_NOTES, "**PASS, 8,699 / 8,699 jobs**")
    add(
        "REVIEW_NOTES_APPENDIX_BUILD_JOBS",
        "dynamic_verification",
        "MINOR",
        "UNVERIFIABLE",
        REVIEW_NOTES,
        appendix_build_line,
        "Lean/Lake run claim",
        "The isolated Appendix build passed 8,699 / 8,699 jobs.",
        "PASS 8699/8699",
        "not rerun; the current Appendix summary records a later 8,702-job target",
        f"{relative(APPENDIX_SUMMARY)}:623 and "
        f"{relative(VERIFICATION / 'logs' / 'build_appendix.log')}",
        "Mark 8,699 as an older run or replace it with source-bound completed evidence.",
    )
    practice_line = find_line(REVIEW_NOTES, "The **191** wholly non-load-bearing")
    add(
        "REVIEW_NOTES_191_PRACTICE_EXERCISES",
        "exercises",
        "MINOR",
        "MATCH",
        REVIEW_NOTES,
        practice_line,
        "record-policy count",
        "191 practice exercise numbers remain outside the census.",
        "191",
        "whole-book coverage table sums to 191; inventory preserves that record scope",
        f"{relative(REVIEW_NOTES)}:27-39",
        "None; this is a policy/count claim, not a source declaration count.",
    )
    whole_table_line = find_line(REVIEW_NOTES, "| **Whole book** |")
    add(
        "REVIEW_NOTES_WHOLE_BOOK_TABLE",
        "census",
        "MAJOR",
        "STALE",
        REVIEW_NOTES,
        whole_table_line,
        "mixed frozen/current table",
        "The whole-book table's 65/5 split is final current status.",
        "873; 768/0/65/5; 35; 838; 191",
        f"all arithmetic matches the frozen artifact, but current Appendix projection is {current_text}",
        f"{relative(INVENTORY / 'review_census_838.tsv')}:1 and Appendix current summary",
        "Label the table frozen or revise only the Brownian status/bucket totals.",
    )
    frozen_denominator_line = find_line(REVIEW_NOTES, "**717 proved / 55 partial")
    add(
        "REVIEW_NOTES_FROZEN_DENOMINATOR",
        "census",
        "MINOR",
        "MATCH",
        REVIEW_NOTES,
        frozen_denominator_line,
        "explicit historical snapshot",
        "The frozen input snapshot is 717/55/34/67 = 873.",
        "717 + 55 + 34 + 67 = 873",
        "explicitly labeled historical; inventory metadata preserves the same frozen denominator",
        f"{relative(INVENTORY / 'inventory_summary.json')}: faithful_historical",
        "None.",
    )
    gap_line = find_line(REVIEW_NOTES, "51 formalized, 35 rejected, and 3 appendix-owned")
    add(
        "REVIEW_NOTES_GAP_DISPOSITION",
        "census",
        "MINOR",
        "MATCH",
        REVIEW_NOTES,
        gap_line,
        "historical disposition arithmetic",
        "The 89 gap rows split 51/35/3.",
        "51 + 35 + 3 = 89",
        "review_gap_disposition_89.tsv has 89 rows with that disposition split",
        f"{relative(INVENTORY / 'review_gap_disposition_89.tsv')}:1",
        "None.",
    )
    final_split_line = find_line(REVIEW_NOTES, "**768 core-formalized / 0 core-partial / 65")
    add(
        "REVIEW_NOTES_FINAL_SPLIT_REPEATED",
        "census",
        "MAJOR",
        "STALE",
        REVIEW_NOTES,
        final_split_line,
        "present-tense final status",
        "The final split is 768/0/65/5.",
        "768/0/65/5",
        current_text,
        f"{relative(APPENDIX_SUMMARY)}:13 and Brownian source",
        "Replace final-current wording with frozen-snapshot wording or 66/4.",
    )
    review_docs_line = find_line(REVIEW_NOTES, "**6,078 / 6,078** target declarations")
    add(
        "REVIEW_NOTES_DOCUMENTATION_COUNTS",
        "declaration_counts",
        "MINOR",
        "MATCH"
        if declarations["documentation_total"] == 6078
        and declarations["documentation_issues"] == 0
        else "STALE",
        REVIEW_NOTES,
        review_docs_line,
        "current lexical source count",
        "6,078 declarations in 101 files are documented with zero issues.",
        "6078/6078; 101; 3112/1610/1356; 0",
        docs_text,
        "Static canonical docstring scanner.",
        "None.",
    )
    review_core_line = find_line(REVIEW_NOTES, "**Core declaration census:**")
    add(
        "REVIEW_NOTES_CORE_DECLARATION_COUNTS",
        "declaration_counts",
        "MINOR",
        "MATCH" if declarations["core_total"] == 5630 else "STALE",
        REVIEW_NOTES,
        review_core_line,
        "current lexical source count",
        "The consolidated core has 5,630 = 2,867/1,608/1,155 declarations.",
        "5630 = 2867/1608/1155",
        core_text,
        "Static canonical docstring scanner.",
        "None.",
    )
    change_line = find_line(REVIEW_NOTES, "Pass 07 added **100 core commands**")
    add(
        "REVIEW_NOTES_DECLARATION_CHANGE_LOG",
        "declaration_counts",
        "MINOR",
        "UNVERIFIABLE",
        REVIEW_NOTES,
        change_line,
        "historical diff claim",
        "Pass 07 added 100 core commands, 91 target kinds, and two Appendix targets.",
        "100; 91=64/4/23; +2 Appendix",
        "current source counts are reproducible, but the historical diff cannot be reconstructed without a trusted baseline/diff",
        "No Git command or historical checkout is used by this static audit.",
        "Keep only with an immutable before/after manifest.",
    )
    core_token_line = find_line(REVIEW_NOTES, "all **25** core files have zero")
    add(
        "REVIEW_NOTES_CORE_TOKEN_SCAN",
        "placeholders",
        "MINOR",
        "MATCH"
        if declarations["core_files"] == 25 and observed["core_forbidden"] == 0
        else "STALE",
        REVIEW_NOTES,
        core_token_line,
        "current lexical source scan",
        "All 25 core files have no sorry/admit/axiom/unsafe code tokens.",
        "25 files; 0 forbidden tokens",
        f"{declarations['core_files']} files; forbidden code tokens={observed['core_forbidden']}",
        "Lexer-aware static scan of Prelude plus consolidated Chapter0-9 files.",
        "None.",
    )
    exercise_token_line = find_line(REVIEW_NOTES, "The **228** remaining `sorry`")
    add(
        "REVIEW_NOTES_EXERCISE_PLACEHOLDERS",
        "exercises",
        "MINOR",
        "MATCH"
        if observed["exercise_sorries"] == 228
        and observed["exercise_files_with_sorry"] == 46
        and observed["marked_sorries"] == 228
        else "STALE",
        REVIEW_NOTES,
        exercise_token_line,
        "current lexical source scan",
        "228 marked exercise sorries occur in 46 exercise-leaf files.",
        "228 in 46; all 228 marked",
        f"{observed['exercise_sorries']} in {observed['exercise_files_with_sorry']} files; "
        f"marked={observed['marked_sorries']}",
        "Lexer-aware scan of 67 exercise-leaf source files.",
        "None.",
    )
    whole_sorry_line = find_line(REVIEW_NOTES, "**231 executable `sorry` proofs in total**")
    add(
        "REVIEW_NOTES_231_TOTAL_PLACEHOLDERS",
        "placeholders",
        "MAJOR",
        "STALE",
        REVIEW_NOTES,
        whole_sorry_line,
        "present-tense source scan",
        "There are 231 executable sorries, including three Appendix sorries.",
        "231 = 228 exercise + 3 Appendix",
        f"{observed['exercise_sorries']} exercise + "
        f"{appendix_forbidden['sorry']} Appendix = "
        f"{observed['exercise_sorries'] + appendix_forbidden['sorry']}",
        f"{relative(APPENDIX_SUMMARY)}:16-17 and lexer-aware source scan",
        "Update total to 228 and Appendix count to zero.",
    )
    map_audit_line = find_line(REVIEW_NOTES, "**PASS: 540 unique endpoints cover all 611")
    add(
        "REVIEW_NOTES_PUBLISHED_ENDPOINT_NAMES",
        "published_endpoints",
        "MINOR",
        "MATCH"
        if len(readme_rows) == 611
        and len(endpoints) == 540
        and observed["v6_locations_complete"]
        else "STALE",
        REVIEW_NOTES,
        map_audit_line,
        "static name/location coverage",
        "540 unique endpoint names cover all 611 publication rows.",
        "540 names / 611 rows",
        map_text,
        "readme_correspondence.json plus exact row-ID equality across the three V6 ledgers.",
        "None for name/location coverage.",
    )
    axiom_distribution_line = find_line(REVIEW_NOTES, "Distribution: **1** endpoint uses no axioms")
    add(
        "REVIEW_NOTES_PUBLISHED_AXIOM_DISTRIBUTION",
        "kernel_verification",
        "MINOR",
        "UNVERIFIABLE",
        REVIEW_NOTES,
        axiom_distribution_line,
        "Lean kernel claim",
        "The 540 endpoints have the exact stated axiom distribution and no sorryAx.",
        "1/1/2/536; no sorryAx",
        "endpoint names/locations are statically covered; axiom dependencies require Lean elaboration",
        "No Lean/Lake invocation is permitted in this V9 static task.",
        "Retain only with a source-bound completed axiom log.",
    )
    blocker_harness_line = find_line(REVIEW_NOTES, "exactly 3 `sorryAx` witnesses")
    add(
        "REVIEW_NOTES_APPENDIX_BLOCKER_HARNESS",
        "placeholders",
        "MAJOR",
        "STALE",
        REVIEW_NOTES,
        blocker_harness_line,
        "present-tense Appendix source status",
        "The Appendix blocker harness has exactly three sorryAx witnesses.",
        "3 sorryAx",
        f"Appendix code sorry tokens={appendix_forbidden['sorry']}; "
        "current registry has no placeholder-backed witness",
        f"{relative(APPENDIX_SUMMARY)}:16-17",
        "Replace with current 16 proved + one skipped classification; rerun kernel audit separately.",
    )
    readme_integrity_line = find_line(REVIEW_NOTES, "**README/master-map integrity:**")
    add(
        "REVIEW_NOTES_MAP_DISTRIBUTION",
        "publication_map",
        "MINOR",
        "MATCH",
        REVIEW_NOTES,
        readme_integrity_line,
        "static row count/distribution",
        "The master map has 611 rows with the stated chapter distribution.",
        "611; 8 + 51/59/75/88/68/39/62/100/61",
        f"{map_text}; {chapter_text}",
        f"{relative(INVENTORY / 'readme_correspondence.tsv')}:1",
        "None.",
    )
    review_registry_line = find_line(REVIEW_NOTES, "targets: thirteen proved and four unresolved")
    add(
        "REVIEW_NOTES_REGISTRY_13_PLUS_4",
        "appendix_registry",
        "MAJOR",
        "STALE",
        REVIEW_NOTES,
        review_registry_line,
        "implementation-registry status",
        "The 17-target registry is 13 proved + four unresolved.",
        "13 + 4",
        "14 source-faithful proved + 2 assumption-strengthened proved + 1 skipped",
        f"{relative(APPENDIX_SUMMARY)}:449-451",
        "Update registry status; do not conflate it with four deferred census rows.",
    )
    review_brownian_new_line = find_line(
        REVIEW_NOTES, "Remark 7.2.1 Brownian reflection formula | **`APPENDIX-UNRESOLVED-004`"
    )
    add(
        "REVIEW_NOTES_BROWNIAN_NEWLY_DEFERRED",
        "brownian",
        "MAJOR",
        "STALE",
        REVIEW_NOTES,
        review_brownian_new_line,
        "current census row status",
        "Brownian remains APPENDIX-UNRESOLVED-004.",
        "deferred",
        f"current endpoint exists={presence['brownian']}; current projection moves this row to Appendix proved",
        f"{relative(APPENDIX_SUMMARY)}:289-307",
        "Move this single row to Appendix proved and remove the former blocker ID.",
    )
    review_borell_name_line = find_line(
        REVIEW_NOTES, "`borellConvexBodyPsiOnePrinciple_external`"
    )
    add(
        "REVIEW_NOTES_BORELL_STALE_ENDPOINT",
        "published_endpoints",
        "MAJOR",
        "OVERSTATED" if not presence["borell_stale"] else "MATCH",
        REVIEW_NOTES,
        review_borell_name_line,
        "published declaration name",
        "borellConvexBodyPsiOnePrinciple_external exists.",
        "unconditional external witness",
        f"exists={presence['borell_stale']}; interface={presence['borell_interface']}; "
        f"conditional={presence['borell_conditional']}",
        f"{relative(HDP / 'Appendix' / 'BorellConvexBody.lean')}:114,133",
        "Replace the nonexistent endpoint with the exact interface and conditional theorem.",
    )
    review_brownian_table_line = find_line(
        REVIEW_NOTES, "| Chapter 7 | Remark 7.2.1 Brownian reflection formula | IN-APPENDIX"
    )
    add(
        "REVIEW_NOTES_BROWNIAN_GAP_TABLE",
        "brownian",
        "MAJOR",
        "STALE",
        REVIEW_NOTES,
        review_brownian_table_line,
        "current census row status",
        "The Brownian principle is unresolved in the gap table.",
        "APPENDIX-UNRESOLVED-004",
        "source-faithful endpoint exists with no forbidden Appendix proof token",
        f"{relative(HDP / 'Appendix' / 'BrownianReflection.lean')}:159",
        "Update the row to Appendix proved.",
    )
    review_65_5_line = find_line(REVIEW_NOTES, "**65 appendix-proved** and **5 unresolved/deferred**")
    add(
        "REVIEW_NOTES_APPENDIX_65_5_SECTION",
        "census",
        "MAJOR",
        "STALE",
        REVIEW_NOTES,
        review_65_5_line,
        "present-tense current status",
        "Appendix-owned coverage is 65 proved and five unresolved/deferred.",
        "65 + 5",
        f"current projection is {current['appendix_proved']} + "
        f"{current['appendix_unresolved_or_deferred']}",
        f"{relative(APPENDIX_SUMMARY)}:13 and current Brownian endpoint",
        "Update totals and remove Brownian from the unresolved list.",
    )
    source_faithful_line = find_line(REVIEW_NOTES, "unresolved Borell convex-body")
    add(
        "REVIEW_NOTES_REMAINING_FOUR_SOURCE_FAITHFUL_ROWS",
        "census",
        "MINOR",
        "MATCH",
        REVIEW_NOTES,
        source_faithful_line,
        "source-faithful census status",
        "Borell, positive Ricci, and two arbitrary-set Chevet rows remain non-source-faithful/deferred.",
        "4 rows",
        "; ".join(row["book_ref"] for row in observed["current_unresolved"]),
        f"{relative(INVENTORY / 'review_census_838.tsv')}: frozen five minus Brownian",
        "Clarify that Q1/Q2 have assumption-strengthened registry proofs and Q3 is skipped.",
    )
    final_five_line = find_line(REVIEW_NOTES, "The five unresolved/deferred census rows remain:")
    add(
        "REVIEW_NOTES_FINAL_FIVE_ROWS",
        "census",
        "MAJOR",
        "STALE",
        REVIEW_NOTES,
        final_five_line,
        "present-tense current status",
        "Five unresolved/deferred census rows remain.",
        "5",
        f"{len(observed['current_unresolved'])} remain after Brownian moves to proved",
        f"{relative(APPENDIX_SUMMARY)}:13",
        "Change five to four and remove the Brownian row.",
    )
    final_registry_line = find_line(REVIEW_NOTES, "The isolated registry is **17 targets = 13 proved + 4 unresolved**")
    add(
        "REVIEW_NOTES_FINAL_REGISTRY",
        "appendix_registry",
        "MAJOR",
        "STALE",
        REVIEW_NOTES,
        final_registry_line,
        "implementation-registry status",
        "The isolated registry is 17 = 13 proved + four unresolved, with three sorries.",
        "13 + 4; 3 sorries",
        f"17 = 14 faithful + 2 strengthened + 1 skipped; Appendix sorry={appendix_forbidden['sorry']}",
        f"{relative(APPENDIX_SUMMARY)}:449-451",
        "Replace the obsolete blocker accounting.",
    )
    no_verification_line = find_line(REVIEW_NOTES, "No `Verification/` directory exists")
    add(
        "REVIEW_NOTES_NO_VERIFICATION_DIRECTORY",
        "document_presence",
        "MAJOR",
        "STALE" if VERIFICATION.is_dir() else "MATCH",
        REVIEW_NOTES,
        no_verification_line,
        "present-tense repository status",
        "No Verification directory exists.",
        "absent",
        f"exists={VERIFICATION.is_dir()}; inventory/review/scripts/logs subdirectories are present",
        f"{relative(VERIFICATION)}",
        "Remove this obsolete sentence or mark it as historical.",
    )
    convergence_line = find_line(REVIEW_NOTES, "The only mathematical residue")
    add(
        "REVIEW_NOTES_FINAL_FOUR_BLOCKERS",
        "appendix_registry",
        "MAJOR",
        "STALE",
        REVIEW_NOTES,
        convergence_line,
        "present-tense implementation status",
        "The only residue is four Appendix blockers; IDs 001/003/004 have placeholders.",
        "4 blockers; 3 placeholders",
        "registry has two assumption-strengthened proofs, one skipped target, Brownian proved, and zero Appendix placeholders",
        f"{relative(APPENDIX_SUMMARY)}:6-17",
        "Replace with the current scoped closure statement.",
    )

    # Correction ledger.
    correction_harness_line = find_line(
        CORRECTION_LEDGER,
        "The corrected-endpoint harness checks 143 unique declarations",
    )
    add(
        "CORRECTION_LEDGER_HARNESS_COUNTS",
        "kernel_verification",
        "MAJOR",
        "STALE",
        CORRECTION_LEDGER,
        correction_harness_line,
        "mixed historical/current harness status",
        "The harnesses check 143 and 19 declarations, with exactly three Appendix sorryAx witnesses.",
        "143; 19=16 clean+3 sorryAx",
        f"exact harness cardinalities are not rerun; current Appendix code sorry="
        f"{appendix_forbidden['sorry']}, so the three-witness outcome is obsolete",
        f"{relative(APPENDIX_SUMMARY)}:16-17",
        "Keep old harness numbers as historical metadata and publish a fresh current axiom audit.",
    )
    correction_exercise_line = find_line(CORRECTION_LEDGER, "Static reconciliation finds 228 exercise")
    add(
        "CORRECTION_LEDGER_EXERCISE_PLACEHOLDERS",
        "exercises",
        "MINOR",
        "MATCH"
        if observed["exercise_sorries"] == 228
        and observed["exercise_files_with_sorry"] == 46
        else "STALE",
        CORRECTION_LEDGER,
        correction_exercise_line,
        "current lexical exercise source",
        "There are 228 exercise sorries in 46 files.",
        "228 in 46",
        f"{observed['exercise_sorries']} in {observed['exercise_files_with_sorry']} files",
        "Lexer-aware exercise source scan.",
        "None.",
    )
    add(
        "CORRECTION_LEDGER_231_TOTAL_PLACEHOLDERS",
        "placeholders",
        "MAJOR",
        "STALE",
        CORRECTION_LEDGER,
        correction_exercise_line,
        "present-tense whole-source status",
        "Three Appendix sorries make 231 executable placeholders.",
        "231 = 228 + 3",
        f"{observed['exercise_sorries']} + {appendix_forbidden['sorry']} = "
        f"{observed['exercise_sorries'] + appendix_forbidden['sorry']}",
        f"{relative(APPENDIX_SUMMARY)}:16-17",
        "Update the Appendix and total placeholder counts.",
    )
    correction_core_line = find_line(CORRECTION_LEDGER, "The current consolidated core census is")
    add(
        "CORRECTION_LEDGER_DECLARATION_COUNTS",
        "declaration_counts",
        "MINOR",
        "MATCH"
        if declarations["core_total"] == 5630
        and declarations["documentation_total"] == 6078
        else "STALE",
        CORRECTION_LEDGER,
        correction_core_line,
        "current lexical source counts",
        "Core is 5,630 and documentation scope is 6,078 in 101 files.",
        "5630; 6078 in 101",
        f"{core_text}; {docs_text}",
        "Static canonical docstring scanner.",
        "None.",
    )
    correction_borell_line = find_line(
        CORRECTION_LEDGER, "| `APPENDIX-UNRESOLVED-003` |"
    )
    add(
        "CORRECTION_LEDGER_BORELL_SOURCE_BOUNDARY",
        "borell",
        "MINOR",
        "MATCH",
        CORRECTION_LEDGER,
        correction_borell_line,
        "source-faithful census status",
        "The unconditional Borell source conclusion is not proved.",
        "unresolved/deferred source row",
        "Q3 is skipped; exact Prop and conditional specialization exist, no unconditional witness",
        f"{relative(HDP / 'Appendix' / 'BorellConvexBody.lean')}:114-148",
        "Change registry label to SKIPPED while retaining census deferred status.",
    )
    correction_brownian_line = find_line(
        CORRECTION_LEDGER, "| `APPENDIX-UNRESOLVED-004` |"
    )
    add(
        "CORRECTION_LEDGER_BROWNIAN_BOUNDARY",
        "brownian",
        "MAJOR",
        "STALE",
        CORRECTION_LEDGER,
        correction_brownian_line,
        "current implementation/census status",
        "Brownian still lacks the reflection theorem.",
        "unresolved",
        f"brownianReflectionPrinciple_external exists={presence['brownian']}; "
        f"Appendix sorry={appendix_forbidden['sorry']}",
        f"{relative(HDP / 'Appendix' / 'BrownianReflection.lean')}:159",
        "Record Brownian as source-faithful proved.",
    )
    correction_registry_line = find_line(
        CORRECTION_LEDGER, "target registry is now 17 targets, split 13 proved / 4 unresolved"
    )
    add(
        "CORRECTION_LEDGER_FIVE_AND_13_PLUS_4",
        "appendix_registry",
        "MAJOR",
        "STALE",
        CORRECTION_LEDGER,
        correction_registry_line,
        "present-tense implementation/census status",
        "Five census rows remain unresolved and registry is 13+4.",
        "5; 13+4",
        f"current census deferred={current['appendix_unresolved_or_deferred']}; "
        "registry=14 faithful +2 strengthened +1 skipped",
        f"{relative(APPENDIX_SUMMARY)}:6-13",
        "Update both layers explicitly.",
    )
    correction_brownian_historical_line = find_line(
        CORRECTION_LEDGER, "| Remark 7.2.1 Brownian reflection formula | missing"
    )
    add(
        "CORRECTION_LEDGER_BROWNIAN_HISTORICAL_ROW",
        "brownian",
        "MINOR",
        "STALE",
        CORRECTION_LEDGER,
        correction_brownian_historical_line,
        "historical row lacking current disposition",
        "Brownian is a registered Appendix blocker.",
        "APPENDIX-UNRESOLVED-004",
        "the historical registration was accurate then, but current endpoint is proved",
        f"{relative(APPENDIX_SUMMARY)}:289-307",
        "Annotate this historical row with the current proved disposition.",
    )

    # Current Appendix summary and import registry.
    appendix_count_line = find_line(APPENDIX_SUMMARY, "There are exactly **17 registered targets**")
    add(
        "APPENDIX_SUMMARY_17_TARGETS",
        "appendix_registry",
        "MINOR",
        "MATCH" if len(observed["registry_imports"]) == 17 else "STALE",
        APPENDIX_SUMMARY,
        appendix_count_line,
        "current registry size",
        "There are exactly 17 registered targets.",
        "17",
        f"Appendix.lean imports {len(observed['registry_imports'])} target modules",
        f"{relative(APPENDIX_REGISTRY)}:1-17",
        "None.",
    )
    appendix_split_line = find_line(APPENDIX_SUMMARY, "- **14 source-faithful PROVED**")
    add(
        "APPENDIX_SUMMARY_14_2_1",
        "appendix_registry",
        "MINOR",
        "MATCH",
        APPENDIX_SUMMARY,
        appendix_split_line,
        "current implementation-registry status",
        "Registry split is 14 source-faithful + 2 assumption-strengthened + 1 skipped.",
        "14 + 2 + 1 = 17",
        "Appendix.lean documents the same split; Q1/Q2/Q3/Q4 source shapes agree",
        f"{relative(APPENDIX_REGISTRY)}:23-33",
        "None.",
    )
    appendix_brownian_line = find_line(APPENDIX_SUMMARY, "Q4, the Brownian expected-running-maximum")
    add(
        "APPENDIX_SUMMARY_BROWNIAN_PROVED",
        "brownian",
        "MINOR",
        "MATCH" if presence["brownian"] and appendix_forbidden["sorry"] == 0 else "STALE",
        APPENDIX_SUMMARY,
        appendix_brownian_line,
        "static source completeness",
        "Q4 Brownian is fully proved in the original interface.",
        "source-faithful PROVED",
        f"endpoint exists={presence['brownian']}; Appendix forbidden tokens: {appendix_token_text}",
        f"{relative(HDP / 'Appendix' / 'BrownianReflection.lean')}:159",
        "Kernel/axiom confirmation remains a separate dynamic check.",
    )
    appendix_borell_line = find_line(APPENDIX_SUMMARY, "Q3 is deliberately **SKIPPED**")
    add(
        "APPENDIX_SUMMARY_BORELL_SKIPPED",
        "borell",
        "MINOR",
        "MATCH"
        if presence["borell_interface"]
        and presence["borell_conditional"]
        and not presence["borell_stale"]
        else "STALE",
        APPENDIX_SUMMARY,
        appendix_borell_line,
        "static source/API status",
        "Q3 is skipped; exact proposition and conditional theorem remain, with no unconditional witness.",
        "SKIPPED",
        f"interface={presence['borell_interface']}; conditional={presence['borell_conditional']}; "
        f"unconditional external={presence['borell_stale']}",
        f"{relative(HDP / 'Appendix' / 'BorellConvexBody.lean')}:114-148",
        "None.",
    )
    appendix_no_hole_line = find_semantic_paragraph(
        APPENDIX_SUMMARY,
        (
            "The source tree reports zero matches in the proof-construct scan",
            "That lexical result excludes proof holes",
        ),
    )
    appendix_complete_proof_line = find_semantic_paragraph(
        APPENDIX_SUMMARY,
        (
            "Final count:",
            "sixteen proved registered results",
            "has a complete proof",
        ),
    )
    add(
        "APPENDIX_SUMMARY_NO_FORBIDDEN_TOKENS",
        "placeholders",
        "MINOR",
        "MATCH" if sum(appendix_forbidden.values()) == 0 else "STALE",
        APPENDIX_SUMMARY,
        appendix_no_hole_line,
        "lexical proof-construct claim",
        "Appendix contains no sorry/admit/axiom/unsafe/native_decide code token.",
        "all zero",
        appendix_token_text,
        "Lexer-aware scan of Appendix.lean and Appendix/**/*.lean.",
        "None.",
    )
    add(
        "APPENDIX_SUMMARY_COMPLETE_PROOF_CLAIM",
        "kernel_verification",
        "MINOR",
        "UNVERIFIABLE",
        APPENDIX_SUMMARY,
        appendix_complete_proof_line,
        "Lean kernel claim",
        "Every exported theorem has a complete kernel-checked proof.",
        "all complete",
        "static source has zero forbidden tokens, but kernel checking is not performed by this task",
        "No Lean/Lake invocation is permitted in this V9 static task.",
        "Bind the claim to a completed build/axiom log and source manifest.",
    )
    final_count_line = appendix_complete_proof_line
    add(
        "APPENDIX_SUMMARY_FINAL_COUNT",
        "appendix_registry",
        "MINOR",
        "MATCH",
        APPENDIX_SUMMARY,
        final_count_line,
        "current implementation-registry status",
        "Final count is 14 + 2 + 1 = 17.",
        "14/2/1",
        "matches Appendix.lean import registry and current Q1-Q4 classifications",
        f"{relative(APPENDIX_REGISTRY)}:23-33",
        "None.",
    )
    axiom_line = find_semantic_paragraph(
        APPENDIX_SUMMARY,
        (
            "The completed V4 kernel audit records the public theorem rows above",
            "Q3's conditional theorem",
            "zero `sorryAx` or nonstandard-axiom rows",
        ),
    )
    add(
        "APPENDIX_SUMMARY_AXIOM_HARNESS",
        "kernel_verification",
        "MINOR",
        "UNVERIFIABLE",
        APPENDIX_SUMMARY,
        axiom_line,
        "Lean kernel claim",
        "All sixteen proved outcomes and Q3 conditional have the exact standard axiom set.",
        "17 checks; [propext, Classical.choice, Quot.sound]",
        "static endpoint/source checks match; exact axiom dependencies require Lean elaboration",
        "No completed source-bound axiom run is produced by this static audit.",
        "Retain only with a completed source-bound axiom log.",
    )
    build_line = find_line(APPENDIX_SUMMARY, "- Borell interface/domain module (Q3): PASS")
    add(
        "APPENDIX_SUMMARY_BUILD_JOB_COUNTS",
        "dynamic_verification",
        "MINOR",
        "UNVERIFIABLE",
        APPENDIX_SUMMARY,
        build_line,
        "Lean/Lake run claim",
        "The focused modules, Appendix target, and full build passed with the listed job counts.",
        "8571/8590/8591/8593/8702/8670",
        "not rerun; static source audit cannot authenticate job counts or exit status",
        f"{relative(VERIFICATION / 'logs' / 'build_appendix.log')} is evidence-only, not rerun here",
        "Treat job counts as recorded run metadata, not a static V9 result.",
    )
    scan_line = appendix_no_hole_line
    add(
        "APPENDIX_SUMMARY_SCAN_AND_ISOLATION",
        "isolation",
        "MINOR",
        "MATCH"
        if sum(appendix_forbidden.values()) == 0
        and observed["appendix_import_leaks"] == 0
        else "STALE",
        APPENDIX_SUMMARY,
        scan_line,
        "current static source status",
        "Appendix has zero forbidden-token matches and no import from the root/core/exercises.",
        "0 tokens; 0 import leaks",
        f"{appendix_token_text}; non-Appendix import leaks={observed['appendix_import_leaks']}",
        "Lexer-aware source scan.",
        "None.",
    )
    registry_doc_line = find_line(APPENDIX_REGISTRY, "for seventeen audited targets in total")
    add(
        "APPENDIX_LEAN_REGISTRY_DOCUMENTATION",
        "appendix_registry",
        "MINOR",
        "MATCH",
        APPENDIX_REGISTRY,
        registry_doc_line,
        "current source registry statement",
        "Appendix.lean records 17 targets, 14 faithful, Q1/Q2 strengthened, Q3 skipped, Q4 proved, and no placeholders.",
        "17; 14 faithful; 2 strengthened; 1 skipped",
        f"imports={len(observed['registry_imports'])}; {appendix_token_text}",
        f"{relative(APPENDIX_REGISTRY)}:1-33",
        "None.",
    )

    # Machine-readable inventories.
    census_header_line = 1
    add(
        "INVENTORY_CENSUS_ROW_COUNT",
        "inventory",
        "MINOR",
        "MATCH" if len(census) == 838 else "STALE",
        INVENTORY / "review_census_838.tsv",
        census_header_line,
        "physical artifact count",
        "review_census_838.tsv has 838 data rows.",
        "838",
        str(len(census)),
        f"{relative(INVENTORY / 'review_census_838.tsv')}:1",
        "None.",
    )
    add(
        "INVENTORY_FROZEN_BUCKET_COUNTS",
        "inventory",
        "MINOR",
        "MATCH"
        if frozen["core_formalized"] == 768
        and frozen["appendix_proved"] == 65
        and frozen["appendix_unresolved_or_deferred"] == 5
        else "STALE",
        INVENTORY / "review_census_838.tsv",
        census_header_line,
        "physical frozen-artifact encoding",
        "The frozen inventory encodes 768/65/5.",
        "768/65/5",
        frozen_text,
        "Direct Counter over coverage_bucket.",
        "Preserve as a frozen artifact if desired.",
    )
    brownian_inventory_line = find_line(
        INVENTORY / "review_census_838.tsv",
        str(observed["brownian_row"]["row_id"]),
    )
    add(
        "INVENTORY_BROWNIAN_BUCKET_CURRENTNESS",
        "inventory",
        "MAJOR",
        "STALE",
        INVENTORY / "review_census_838.tsv",
        brownian_inventory_line,
        "current semantic status",
        "The Brownian census row is still Appendix unresolved/deferred.",
        "appendix_unresolved_or_deferred",
        "current source endpoint is source-faithful proved; projected bucket is appendix_proved",
        f"{relative(HDP / 'Appendix' / 'BrownianReflection.lean')}:159",
        "Keep the frozen row immutable but publish a current-status overlay/projection.",
    )
    exercise_inventory_line = find_line(
        INVENTORY / "inventory_summary.tsv", "exercise_leaf_declarations"
    )
    add(
        "INVENTORY_EXERCISE_DECLARATIONS",
        "exercises",
        "MINOR",
        "MATCH"
        if len(observed["exercise_inventory"]) == 247
        and observed["inventory_summary_tsv"]["exercise_leaf_declarations"] == "247"
        else "STALE",
        INVENTORY / "inventory_summary.tsv",
        exercise_inventory_line,
        "current machine inventory",
        "There are 247 exercise-leaf theorem/lemma declarations.",
        "247",
        f"TSV rows={len(observed['exercise_inventory'])}; summary metric="
        f"{observed['inventory_summary_tsv']['exercise_leaf_declarations']}",
        f"{relative(INVENTORY / 'exercise_leaf_declarations.tsv')}:1",
        "None.",
    )
    exercise_samples_line = find_line(
        INVENTORY / "inventory_summary.tsv", "exercise_samples"
    )
    add(
        "INVENTORY_EXERCISE_SAMPLES_AND_QUEUE",
        "exercises",
        "MINOR",
        "MATCH"
        if observed["inventory_summary_tsv"]["exercise_samples"] == "27"
        and observed["inventory_summary_tsv"]["ok_candidate_queue_head"] == "50"
        else "STALE",
        INVENTORY / "inventory_summary.tsv",
        exercise_samples_line,
        "current machine inventory",
        "The deterministic plan has 27 exercise samples and a 50-row queue head.",
        "27; 50",
        f"sampling_plan rows={len(observed['sampling_plan'])}; "
        f"metrics={observed['inventory_summary_tsv']['exercise_samples']}/"
        f"{observed['inventory_summary_tsv']['ok_candidate_queue_head']}",
        f"{relative(INVENTORY / 'sampling_plan.tsv')}:1",
        "None.",
    )
    endpoint_union_line = find_line(
        INVENTORY / "inventory_summary.tsv", "endpoint_union_unique"
    )
    add(
        "INVENTORY_ENDPOINT_UNION",
        "published_endpoints",
        "MINOR",
        "MATCH"
        if len(observed["endpoint_union"]) == 641
        and observed["inventory_summary_tsv"]["endpoint_union_unique"] == "641"
        else "STALE",
        INVENTORY / "inventory_summary.tsv",
        endpoint_union_line,
        "physical machine inventory",
        "The endpoint union has 641 unique names.",
        "641",
        f"TSV rows={len(observed['endpoint_union'])}; summary metric="
        f"{observed['inventory_summary_tsv']['endpoint_union_unique']}",
        f"{relative(INVENTORY / 'endpoint_union.tsv')}:1",
        "None.",
    )
    borell_union_line = find_line(
        INVENTORY / "endpoint_union.tsv",
        "HDP.Chapter3.borellConvexBodyPsiOnePrinciple_external",
    )
    add(
        "INVENTORY_BORELL_STALE_ENDPOINT",
        "published_endpoints",
        "MAJOR",
        "OVERSTATED" if not presence["borell_stale"] else "MATCH",
        INVENTORY / "endpoint_union.tsv",
        borell_union_line,
        "current declaration-name validity",
        "The endpoint union contains a resolvable unconditional Borell external declaration.",
        "HDP.Chapter3.borellConvexBodyPsiOnePrinciple_external",
        f"exact declaration exists={presence['borell_stale']}; replacement interface and conditional theorem exist",
        f"{relative(HDP / 'Appendix' / 'BorellConvexBody.lean')}:114-148",
        "Preserve in the frozen inventory only with an explicit stale-name overlay.",
    )
    hash_line = find_line(INVENTORY / "inventory_summary.tsv", "validation_ok")
    add(
        "INVENTORY_SOURCE_HASH_FRESHNESS",
        "inventory",
        "MINOR",
        "MATCH" if all(observed["inventory_hash_matches"].values()) else "STALE",
        INVENTORY / "inventory_summary.tsv",
        hash_line,
        "inventory/source binding",
        "The inventory is bound to the current README/REVIEW/faithful-report source texts.",
        "all recorded SHA-256 values match",
        "; ".join(
            f"{path}={str(match).lower()}"
            for path, match in observed["inventory_hash_matches"].items()
        ),
        f"{relative(INVENTORY / 'inventory_summary.json')}: source_sha256",
        "None; note that Appendix source is intentionally not among these three hashes.",
    )

    if len({row["claim_id"] for row in rows}) != len(rows):
        raise RuntimeError("duplicate V9 claim_id")
    return rows


def build_current_claims(observed: Mapping[str, object]) -> list[dict[str, str]]:
    """Audit the post-correction publications.

    ``build_claims`` above is retained as the reproducible Pass 06 detector:
    its anchors intentionally name the pre-correction claims that generated
    V9-F3/F4/F6/F8.  Pass 07 replaced those publications, so the live
    generator uses this current-state claim set instead of pretending that
    the old detector still describes the corrected documents.
    """

    rows: list[dict[str, str]] = []

    def add(
        claim_id: str,
        category: str,
        severity: str,
        verdict: str,
        path: Path,
        line: int,
        scope: str,
        claim: str,
        claimed: str,
        value: str,
        evidence: str,
        action: str = "None.",
    ) -> None:
        if verdict not in ALLOWED_VERDICTS:
            raise RuntimeError(f"{claim_id}: invalid verdict {verdict}")
        if severity not in ALLOWED_SEVERITIES:
            raise RuntimeError(f"{claim_id}: invalid severity {severity}")
        rows.append(
            {
                "claim_id": claim_id,
                "category": category,
                "severity": severity,
                "verdict": verdict,
                "claim_file": relative(path),
                "claim_line": str(line),
                "claim_scope": scope,
                "claim": claim,
                "claimed_value": claimed,
                "observed_value": value,
                "evidence": evidence,
                "recommended_action": action,
            }
        )

    census = observed["census"]
    frozen = observed["frozen_buckets"]
    current = observed["current_buckets"]
    declarations = observed["declarations"]
    readme_rows = observed["readme_rows"]
    endpoints = observed["readme_endpoints"]
    chapters = observed["readme_chapters"]
    presence = observed["endpoint_presence"]
    forbidden = observed["appendix_forbidden"]
    appendix_token_text = ", ".join(
        f"{name}={count}" for name, count in forbidden.items()
    )
    core_kinds = declarations["core_kinds"]
    documentation_kinds = declarations["documentation_kinds"]
    core_text = (
        f"{declarations['core_total']} = {core_kinds['theorem']} theorem + "
        f"{core_kinds['lemma']} lemma + {core_kinds['def']} def in "
        f"{declarations['core_files']} files"
    )
    documentation_text = (
        f"{declarations['documentation_total']} = "
        f"{documentation_kinds['theorem']} theorem + "
        f"{documentation_kinds['lemma']} lemma + "
        f"{documentation_kinds['def']} def in "
        f"{declarations['documentation_files']} files; "
        f"issues={declarations['documentation_issues']}"
    )
    map_text = (
        f"{len(readme_rows)} rows / {len(endpoints)} unique endpoints; "
        f"V6 rows={len(observed['v6_readme_rows'])}, "
        f"all OK={str(observed['v6_all_ok']).lower()}, "
        f"locations complete={str(observed['v6_locations_complete']).lower()}"
    )
    current_text = (
        f"{len(census)} = {current['core_formalized']} core + "
        f"{current['appendix_proved']} Appendix proved + "
        f"{current['appendix_unresolved_or_deferred']} deferred"
    )
    frozen_text = (
        f"{len(census)} = {frozen['core_formalized']} core + "
        f"{frozen['appendix_proved']} Appendix proved + "
        f"{frozen['appendix_unresolved_or_deferred']} deferred"
    )
    chapter_text = (
        f"Appetizer {chapters['Appetizer']}; Chapters 1-9 "
        + "/".join(str(chapters[f"Chapter {number}"]) for number in range(1, 10))
    )

    resolution_path = INVENTORY / "pass07_soundness_resolutions.tsv"
    resolution_rows = read_tsv(resolution_path)
    resolution_dispositions = Counter(
        row["validation_disposition"] for row in resolution_rows
    )
    resolution_states = Counter(row["current_state"] for row in resolution_rows)
    resolution_ok = (
        len(resolution_rows) == 25
        and resolution_dispositions
        == Counter({"CONFIRMED": 10, "REVISED": 14, "REJECTED": 1})
        and resolution_states
        == Counter(
            {
                "FIXED": 8,
                "OUT_OF_SCOPE_BLOCKER": 9,
                "DOCUMENTED_SOURCE_LIMITATION": 1,
                "REVIEW_EVIDENCE_LIMITATION": 4,
                "RESOLVED_AS_NONDEFECT": 2,
                "NO_CHANGE": 1,
            }
        )
    )
    replacement_path = INVENTORY / "pass07_endpoint_replacements.tsv"
    replacement_text = replacement_path.read_text(encoding="utf-8")
    archive = VERIFICATION / "archive" / "REVIEW_NOTES.pre-final-correction.md"
    archive_sha = hashlib.sha256(archive.read_bytes()).hexdigest()
    expected_archive_sha = (
        "53ac710d7882078e460ba9df8f7d94e9ca37110924ce17d86"
        "ecd991480ab1dc1"
    )

    # Requested aliases that never existed are recorded as static-scope notes,
    # not confused with defects in the actual current records.
    add(
        "MISSING_REVIEW_CENSUS_DOCUMENT",
        "document_presence",
        "MINOR",
        "UNVERIFIABLE" if not REQUESTED_REVIEW_CENSUS.exists() else "MATCH",
        REQUESTED_REVIEW_CENSUS,
        0,
        "requested alias",
        "A REVIEW_CENSUS.md alias is available.",
        "present",
        "absent; canonical equivalent is review_census_838.tsv plus REVIEW_NOTES.md",
        f"{relative(INVENTORY / 'review_census_838.tsv')}:1; "
        f"{relative(REVIEW_NOTES)}",
        "Use the canonical current paths.",
    )
    add(
        "MISSING_PLACEHOLDER_LEDGER_DOCUMENT",
        "document_presence",
        "MINOR",
        "UNVERIFIABLE" if not REQUESTED_PLACEHOLDER_LEDGER.exists() else "MATCH",
        REQUESTED_PLACEHOLDER_LEDGER,
        0,
        "requested alias",
        "A PLACEHOLDER_LEDGER.md alias is available.",
        "present",
        "absent; canonical equivalent is CORRECTION_LEDGER.md plus V3",
        f"{relative(CORRECTION_LEDGER)}; "
        f"{relative(VERIFICATION / '03_sorry_audit.md')}",
        "Use the canonical current paths.",
    )

    # Root README.
    root_line = find_line(ROOT_README, "together with 611 audited")
    add(
        "ROOT_README_611_ROWS",
        "publication_map",
        "MINOR",
        "MATCH" if len(readme_rows) == 611 else "STALE",
        ROOT_README,
        root_line,
        "current numeric claim",
        "The public correspondence has 611 rows.",
        "611",
        map_text,
        f"{relative(INVENTORY / 'readme_correspondence.tsv')}:1",
    )
    add(
        "ROOT_README_ALL_VERIFIED",
        "publication_map",
        "MINOR",
        "UNVERIFIABLE",
        ROOT_README,
        root_line,
        "dynamic/kernel claim",
        "All 611 mappings are verified.",
        "all verified",
        map_text + "; semantic/kernel confirmation is outside this static script",
        f"{relative(VERIFICATION / 'logs' / 'v9_readme_axioms_summary.txt')}; "
        f"{relative(REVIEW_NOTES)}",
        "Retain only together with the separate source-bound endpoint and PDF audits.",
    )
    add(
        "ROOT_README_838_768_66_4",
        "census",
        "MINOR",
        "MATCH"
        if (
            len(census),
            current["core_formalized"],
            current["appendix_proved"],
            current["appendix_unresolved_or_deferred"],
        )
        == (838, 768, 66, 4)
        else "STALE",
        ROOT_README,
        root_line,
        "current census projection",
        "The current census is 838 = 768 + 66 + 4.",
        "838/768/66/4",
        current_text,
        f"{relative(INVENTORY / 'review_census_838.tsv')}:1; "
        f"{relative(APPENDIX_SUMMARY)}",
    )
    add(
        "ROOT_README_CORE_DECLARATIONS",
        "declaration_counts",
        "MINOR",
        "MATCH" if declarations["core_total"] == 5630 else "STALE",
        ROOT_README,
        root_line,
        "current lexical count",
        "The consolidated core has 5,630 target declarations.",
        "5630 = 2867/1608/1155",
        core_text,
        "Canonical docstring scanner over Prelude and consolidated chapters.",
    )
    add(
        "ROOT_README_DOCUMENTATION_DECLARATIONS",
        "declaration_counts",
        "MINOR",
        "MATCH"
        if (
            declarations["documentation_total"],
            declarations["documentation_files"],
            declarations["documentation_issues"],
        )
        == (6078, 101, 0)
        else "STALE",
        ROOT_README,
        root_line,
        "current scoped lexical count",
        "The non-Appendix, non-Verification audit is 6,078/101/0.",
        "6078 in 101; zero issues",
        documentation_text,
        "Canonical scoped docstring scanner.",
    )
    root_build_line = find_line(ROOT_README, "~/.elan/bin/lake build HighDimensionalProbability")
    add(
        "ROOT_README_BUILD_RECIPE",
        "build_recipe",
        "MINOR",
        "MATCH",
        ROOT_README,
        root_build_line,
        "published command",
        "The root README prints the authorized package build command.",
        "~/.elan/bin/lake build HighDimensionalProbability",
        "exact authorized command is present",
        f"{relative(ROOT_README)}:{root_build_line}",
    )

    # Package README.
    package_map_line = find_line(PACKAGE_README, "| Book → Lean correspondence |")
    add(
        "PACKAGE_README_611_ROWS",
        "publication_map",
        "MINOR",
        "MATCH" if len(readme_rows) == 611 else "STALE",
        PACKAGE_README,
        package_map_line,
        "current numeric claim",
        "The package map has 611 rows.",
        "611",
        map_text,
        f"{relative(INVENTORY / 'readme_correspondence.json')}:1",
    )
    add(
        "PACKAGE_README_ALL_VERIFIED",
        "publication_map",
        "MINOR",
        "UNVERIFIABLE",
        PACKAGE_README,
        package_map_line,
        "dynamic/kernel claim",
        "All 611 mappings are verified.",
        "611 verified; zero partial",
        map_text + "; the static census does not replay Lean or the PDF",
        f"{relative(VERIFICATION / 'logs' / 'v9_readme_axioms_summary.txt')}; "
        f"{relative(REVIEW_NOTES)}",
        "Treat the separate dynamic/PDF evidence as part of the claim.",
    )
    package_distribution_line = find_line(PACKAGE_README, "| Chapter distribution |")
    add(
        "PACKAGE_README_CHAPTER_DISTRIBUTION",
        "publication_map",
        "MINOR",
        "MATCH"
        if [chapters[f"Chapter {number}"] for number in range(1, 10)]
        == [51, 59, 75, 88, 68, 39, 62, 100, 61]
        else "STALE",
        PACKAGE_README,
        package_distribution_line,
        "current numeric claim",
        "The package README states the actual chapter distribution.",
        "8; 51/59/75/88/68/39/62/100/61",
        chapter_text,
        f"{relative(INVENTORY / 'readme_correspondence.tsv')}:1",
    )
    package_census_line = find_line(
        PACKAGE_README, "| PDF-revalidated whole-book census |"
    )
    add(
        "PACKAGE_README_838_768_66_4",
        "census",
        "MINOR",
        "MATCH"
        if (
            len(census),
            current["core_formalized"],
            current["appendix_proved"],
            current["appendix_unresolved_or_deferred"],
        )
        == (838, 768, 66, 4)
        else "STALE",
        PACKAGE_README,
        package_census_line,
        "current census projection",
        "The package README states 838 = 768 + 66 + 4.",
        "838/768/66/4",
        current_text,
        f"{relative(INVENTORY / 'review_census_838.tsv')}:1; "
        f"{relative(APPENDIX_SUMMARY)}",
    )
    package_core_line = find_line(PACKAGE_README, "| Consolidated core declarations |")
    add(
        "PACKAGE_README_CORE_DECLARATIONS",
        "declaration_counts",
        "MINOR",
        "MATCH" if declarations["core_total"] == 5630 else "STALE",
        PACKAGE_README,
        package_core_line,
        "current lexical count",
        "The package README states the 5,630 core declaration census.",
        "5630 = 2867/1608/1155",
        core_text,
        "Canonical docstring scanner.",
    )
    package_docs_line = find_line(PACKAGE_README, "| Non-Appendix documentation audit |")
    add(
        "PACKAGE_README_DOCUMENTATION_AUDIT",
        "declaration_counts",
        "MINOR",
        "MATCH"
        if (
            declarations["documentation_total"],
            declarations["documentation_files"],
            declarations["documentation_issues"],
        )
        == (6078, 101, 0)
        else "STALE",
        PACKAGE_README,
        package_docs_line,
        "current scoped lexical count",
        "The package README states 6,078/101/0.",
        "6078 in 101; zero issues",
        documentation_text,
        "Canonical scoped docstring scanner.",
    )
    package_registry_line = find_line(PACKAGE_README, "Its 17 registered")
    add(
        "PACKAGE_README_APPENDIX_REGISTRY",
        "appendix_registry",
        "MINOR",
        "MATCH" if len(observed["registry_imports"]) == 17 else "STALE",
        PACKAGE_README,
        package_registry_line,
        "current registry claim",
        "The registry is 17 = 14 faithful + 2 strengthened + 1 skipped.",
        "17/14/2/1",
        f"imports={len(observed['registry_imports'])}; source outcomes=14/2/1",
        f"{relative(APPENDIX_REGISTRY)}; {relative(APPENDIX_SUMMARY)}",
    )
    package_chevet_line = find_line(
        PACKAGE_README, "PROVED (assumption-strengthened: `0 ∈ T`)"
    )
    add(
        "PACKAGE_README_CHEVET_STATUS",
        "appendix_endpoint",
        "MINOR",
        "MATCH" if presence["chevet"] else "STALE",
        PACKAGE_README,
        package_chevet_line,
        "current source/API status",
        "Q1 is assumption-strengthened proved under 0 ∈ T.",
        "strengthened PROVED",
        f"endpoint exists={presence['chevet']}",
        f"{relative(HDP / 'Appendix' / 'GaussianChevet.lean')}",
    )
    package_ricci_line = find_line(
        PACKAGE_README,
        "PROVED (assumption-strengthened: explicit `RiemannianDiffusionLaw`)",
    )
    add(
        "PACKAGE_README_POSITIVE_RICCI_STATUS",
        "appendix_endpoint",
        "MINOR",
        "MATCH" if presence["positive_ricci"] else "STALE",
        PACKAGE_README,
        package_ricci_line,
        "current source/API status",
        "Q2 is assumption-strengthened proved at RiemannianDiffusionLaw.",
        "strengthened PROVED",
        f"endpoint exists={presence['positive_ricci']}",
        f"{relative(HDP / 'Appendix' / 'PositiveRicciConcentration.lean')}",
    )
    package_borell_line = find_line(PACKAGE_README, "(conditional theorem only)")
    add(
        "PACKAGE_README_BORELL_STATUS",
        "appendix_endpoint",
        "MINOR",
        "MATCH"
        if (
            not presence["borell_stale"]
            and presence["borell_interface"]
            and presence["borell_conditional"]
        )
        else "OVERSTATED",
        PACKAGE_README,
        package_borell_line,
        "current source/API status",
        "Q3 names the proposition/conditional theorem and is skipped.",
        "SKIPPED; no unconditional witness",
        f"stale external={presence['borell_stale']}; "
        f"interface={presence['borell_interface']}; "
        f"conditional={presence['borell_conditional']}",
        f"{relative(HDP / 'Appendix' / 'BorellConvexBody.lean')}",
    )
    package_brownian_line = find_line(
        PACKAGE_README, "`HDP.Chapter7.brownianReflectionPrinciple_external`"
    )
    add(
        "PACKAGE_README_BROWNIAN_STATUS",
        "appendix_endpoint",
        "MINOR",
        "MATCH" if presence["brownian"] else "STALE",
        PACKAGE_README,
        package_brownian_line,
        "current source/API status",
        "Q4 Brownian reflection is source-faithful proved.",
        "PROVED",
        f"endpoint exists={presence['brownian']}; {appendix_token_text}",
        f"{relative(HDP / 'Appendix' / 'BrownianReflection.lean')}",
    )

    # Fresh REVIEW_NOTES.
    review_pass05_line = find_line(REVIEW_NOTES, "9 CONFIRMED / 4 REVISED")
    add(
        "REVIEW_NOTES_PASS05_DISPOSITIONS",
        "finding_resolution",
        "MINOR",
        "MATCH",
        REVIEW_NOTES,
        review_pass05_line,
        "current validation record",
        "Pass 05 findings are 9 confirmed / 4 revised / 1 rejected.",
        "9/4/1",
        "14 exhaustive F rows with the same dispositions",
        f"{relative(CORRECTION_LEDGER)}",
    )
    review_pass06_line = find_line(REVIEW_NOTES, "10 CONFIRMED / 14 REVISED")
    add(
        "REVIEW_NOTES_PASS06_DISPOSITIONS",
        "finding_resolution",
        "MINOR",
        "MATCH" if resolution_ok else "STALE",
        REVIEW_NOTES,
        review_pass06_line,
        "current machine-readable resolution record",
        "Pass 06 non-INFO findings are 10/14/1.",
        "10/14/1",
        f"rows={len(resolution_rows)}; dispositions={dict(resolution_dispositions)}; "
        f"states={dict(resolution_states)}",
        f"{relative(resolution_path)}",
    )
    review_census_line = find_line(REVIEW_NOTES, "**838 = 768 core-formalized")
    add(
        "REVIEW_NOTES_838_768_66_4",
        "census",
        "MINOR",
        "MATCH"
        if (
            len(census),
            current["core_formalized"],
            current["appendix_proved"],
            current["appendix_unresolved_or_deferred"],
        )
        == (838, 768, 66, 4)
        else "STALE",
        REVIEW_NOTES,
        review_census_line,
        "current census projection",
        "The fresh review states 838 = 768 + 66 + 4.",
        "838/768/66/4",
        current_text,
        f"{relative(INVENTORY / 'review_census_838.tsv')}:1; "
        f"{relative(APPENDIX_SUMMARY)}",
    )
    review_table_line = find_line(REVIEW_NOTES, "| **Whole book** |")
    add(
        "REVIEW_NOTES_WHOLE_BOOK_TABLE",
        "census",
        "MINOR",
        "MATCH",
        REVIEW_NOTES,
        review_table_line,
        "current table arithmetic",
        "The whole-book row states 873/768/66/4/35/838.",
        "873/768/66/4/35/838",
        "873 - 35 = 838 and 768 + 66 + 4 = 838",
        f"{relative(REVIEW_NOTES)}:{review_table_line}",
    )
    review_practice_line = find_line(REVIEW_NOTES, "191")
    add(
        "REVIEW_NOTES_PRACTICE_SCOPE",
        "exercises",
        "MINOR",
        "MATCH",
        REVIEW_NOTES,
        review_practice_line,
        "record-policy count",
        "191 wholly non-load-bearing exercise numbers remain outside the census.",
        "191",
        "explicitly scoped policy count",
        f"{relative(REVIEW_NOTES)}:{review_practice_line}",
    )
    review_map_line = find_line(REVIEW_NOTES, "**611/611 verified mappings**")
    add(
        "REVIEW_NOTES_PUBLICATION_MAP",
        "publication_map",
        "MINOR",
        "UNVERIFIABLE",
        REVIEW_NOTES,
        review_map_line,
        "mixed static/dynamic claim",
        "The review records 611/611 mappings and 540 endpoints.",
        "611/611; 540",
        map_text + "; exact axiom/PDF verification is external to this static script",
        f"{relative(VERIFICATION / 'logs' / 'v9_readme_axioms_summary.txt')}",
        "Retain with the source-bound dynamic and PDF records.",
    )
    review_build_line = find_line(REVIEW_NOTES, "| Default whole-tree build |")
    add(
        "REVIEW_NOTES_FINAL_BUILD",
        "dynamic_verification",
        "MINOR",
        "UNVERIFIABLE",
        REVIEW_NOTES,
        review_build_line,
        "Lean/Lake run claim",
        "The default build passed 8,670/8,670 jobs.",
        "PASS 8670/8670",
        "not replayed by this static task",
        f"{relative(VERIFICATION / 'logs' / 'pass07_final_whole_build.log')}",
        "Bind to the separately recorded source manifest and exit log.",
    )
    review_appendix_build_line = find_line(REVIEW_NOTES, "Isolated Appendix build:")
    add(
        "REVIEW_NOTES_FINAL_APPENDIX_BUILD",
        "dynamic_verification",
        "MINOR",
        "UNVERIFIABLE",
        REVIEW_NOTES,
        review_appendix_build_line,
        "Lean/Lake run claim",
        "The isolated Appendix build passed 8,703/8,703 jobs.",
        "PASS 8703/8703",
        "not replayed by this static task",
        f"{relative(VERIFICATION / 'logs' / 'pass07_final_appendix_build.log')}",
        "Bind to the separately recorded source manifest and exit log.",
    )
    review_placeholder_line = find_line(
        REVIEW_NOTES, "exactly **228 executable `sorry` proofs**"
    )
    add(
        "REVIEW_NOTES_PLACEHOLDERS",
        "placeholders",
        "MINOR",
        "MATCH"
        if (
            observed["exercise_sorries"],
            observed["exercise_files_with_sorry"],
            observed["marked_sorries"],
            forbidden["sorry"],
        )
        == (228, 46, 228, 0)
        else "STALE",
        REVIEW_NOTES,
        review_placeholder_line,
        "current lexer-aware source count",
        "There are 228 marked exercise sorries and zero Appendix sorries.",
        "228/46/0",
        f"exercise={observed['exercise_sorries']} in "
        f"{observed['exercise_files_with_sorry']} files; "
        f"marked={observed['marked_sorries']}; Appendix={forbidden['sorry']}",
        f"{relative(VERIFICATION / 'logs' / 'v3_library.json')}",
    )
    review_docs_line = find_line(REVIEW_NOTES, "6,078/6,078 declarations")
    add(
        "REVIEW_NOTES_DOCUMENTATION_COUNTS",
        "declaration_counts",
        "MINOR",
        "MATCH"
        if (
            declarations["documentation_total"],
            declarations["documentation_files"],
            declarations["documentation_issues"],
        )
        == (6078, 101, 0)
        else "STALE",
        REVIEW_NOTES,
        review_docs_line,
        "current scoped lexical count",
        "The fresh review states 6,078/101/0.",
        "6078/101/0",
        documentation_text,
        "Canonical scoped docstring scanner.",
    )
    review_appendix_line = find_line(
        REVIEW_NOTES, "| Q1 | Exercise 8.39(a), related Remark 8.6.3 |"
    )
    add(
        "REVIEW_NOTES_APPENDIX_Q1_Q4",
        "appendix_registry",
        "MINOR",
        "MATCH"
        if (
            presence["chevet"]
            and presence["positive_ricci"]
            and not presence["borell_stale"]
            and presence["borell_interface"]
            and presence["borell_conditional"]
            and presence["brownian"]
        )
        else "STALE",
        REVIEW_NOTES,
        review_appendix_line,
        "current owner-selected outcomes",
        "Q1/Q2 are strengthened proved, Q3 skipped, Q4 faithful proved.",
        "strengthened/strengthened/skipped/proved",
        "all four source/API shapes agree",
        f"{relative(APPENDIX_SUMMARY)}",
    )
    review_archive_line = find_line(REVIEW_NOTES, expected_archive_sha)
    add(
        "REVIEW_NOTES_ARCHIVE_HASH",
        "archive_integrity",
        "MINOR",
        "MATCH" if archive_sha == expected_archive_sha else "STALE",
        REVIEW_NOTES,
        review_archive_line,
        "frozen input binding",
        "The archived Pass 05 input has the recorded SHA-256.",
        expected_archive_sha,
        archive_sha,
        f"{relative(archive)}",
    )
    review_round_line = find_line(
        REVIEW_NOTES,
        "**Round 8 — authoritative closure, 2026-07-19.**",
    )
    add(
        "REVIEW_NOTES_ROUND8",
        "iteration_record",
        "MINOR",
        "MATCH",
        REVIEW_NOTES,
        review_round_line,
        "current iteration record",
        "Round 8 is recorded as the authoritative current-source closure.",
        "Round 8",
        "present with explicit surviving limitations",
        f"{relative(REVIEW_NOTES)}:{review_round_line}",
    )

    # Correction ledger.
    correction_pass05_line = find_line(
        CORRECTION_LEDGER, "9 CONFIRMED**, **4 REVISED**, and **1 REJECTED"
    )
    add(
        "CORRECTION_LEDGER_PASS05",
        "finding_resolution",
        "MINOR",
        "MATCH",
        CORRECTION_LEDGER,
        correction_pass05_line,
        "current validation record",
        "The correction ledger records 9/4/1.",
        "9/4/1",
        "14 exhaustive F rows",
        f"{relative(CORRECTION_LEDGER)}",
    )
    correction_placeholder_line = find_line(
        CORRECTION_LEDGER, "Static reconciliation finds exactly 228 executable"
    )
    add(
        "CORRECTION_LEDGER_PLACEHOLDERS",
        "placeholders",
        "MINOR",
        "MATCH"
        if observed["exercise_sorries"] == 228 and forbidden["sorry"] == 0
        else "STALE",
        CORRECTION_LEDGER,
        correction_placeholder_line,
        "current source count",
        "The correction ledger records 228 exercise and zero Appendix sorries.",
        "228 + 0",
        f"{observed['exercise_sorries']} + {forbidden['sorry']}",
        f"{relative(VERIFICATION / 'logs' / 'v3_library.json')}",
    )
    correction_census_line = find_line(
        CORRECTION_LEDGER, "838 = 768 core + 66 Appendix proved + 4"
    )
    add(
        "CORRECTION_LEDGER_CENSUS",
        "census",
        "MINOR",
        "MATCH"
        if (
            current["core_formalized"],
            current["appendix_proved"],
            current["appendix_unresolved_or_deferred"],
        )
        == (768, 66, 4)
        else "STALE",
        CORRECTION_LEDGER,
        correction_census_line,
        "current census projection",
        "The ledger records 838 = 768 + 66 + 4.",
        "838/768/66/4",
        current_text,
        f"{relative(INVENTORY / 'review_census_838.tsv')}:1",
    )
    correction_q_line = find_line(CORRECTION_LEDGER, "| Q1 |")
    add(
        "CORRECTION_LEDGER_Q1_Q4",
        "appendix_registry",
        "MINOR",
        "MATCH",
        CORRECTION_LEDGER,
        correction_q_line,
        "current owner-selected outcomes",
        "The ledger records Q1/Q2 strengthened, Q3 skipped, Q4 proved.",
        "strengthened/strengthened/skipped/proved",
        "matches Appendix registry and source/API inspection",
        f"{relative(APPENDIX_SUMMARY)}",
    )

    # Appendix summary and source.
    appendix_count_line = find_line(APPENDIX_SUMMARY, "exactly **17 registered targets**")
    add(
        "APPENDIX_SUMMARY_REGISTRY",
        "appendix_registry",
        "MINOR",
        "MATCH" if len(observed["registry_imports"]) == 17 else "STALE",
        APPENDIX_SUMMARY,
        appendix_count_line,
        "current registry claim",
        "The Appendix registry is 17 = 14 + 2 + 1.",
        "17/14/2/1",
        f"imports={len(observed['registry_imports'])}; source outcomes=14/2/1",
        f"{relative(APPENDIX_REGISTRY)}",
    )
    appendix_q_line = find_line(APPENDIX_SUMMARY, "Q4, the Brownian expected-running-maximum")
    add(
        "APPENDIX_SUMMARY_Q1_Q4",
        "appendix_registry",
        "MINOR",
        "MATCH",
        APPENDIX_SUMMARY,
        appendix_q_line,
        "current owner-selected outcomes",
        "Q1/Q2 are strengthened proved, Q3 skipped, Q4 faithful proved.",
        "strengthened/strengthened/skipped/proved",
        "source/API shapes agree and no unconditional Borell witness exists",
        f"{relative(APPENDIX_REGISTRY)}; {relative(APPENDIX_SUMMARY)}",
    )
    appendix_scan_line = find_line(
        APPENDIX_SUMMARY, "source tree reports zero matches in the proof-construct scan"
    )
    add(
        "APPENDIX_SUMMARY_FORBIDDEN_TOKENS",
        "placeholders",
        "MINOR",
        "MATCH" if all(value == 0 for value in forbidden.values()) else "STALE",
        APPENDIX_SUMMARY,
        appendix_scan_line,
        "current lexer-aware source claim",
        "Appendix has no forbidden proof construct.",
        "all zero",
        appendix_token_text,
        "Lexer-aware scan of Appendix.lean and Appendix/**/*.lean.",
    )
    add(
        "APPENDIX_SUMMARY_ISOLATION",
        "isolation",
        "MINOR",
        "MATCH" if observed["appendix_import_leaks"] == 0 else "STALE",
        APPENDIX_SUMMARY,
        appendix_scan_line,
        "current static import claim",
        "No non-Appendix source imports the isolated Appendix.",
        "0 leaks",
        f"import leaks={observed['appendix_import_leaks']}",
        "Lexer-masked source import scan.",
    )
    appendix_axiom_line = find_line(
        APPENDIX_SUMMARY, "The completed V4 kernel audit records"
    )
    add(
        "APPENDIX_SUMMARY_AXIOM_REPLAY",
        "kernel_verification",
        "MINOR",
        "UNVERIFIABLE",
        APPENDIX_SUMMARY,
        appendix_axiom_line,
        "Lean kernel claim",
        "The current-source Appendix axiom replay is standard-only.",
        "20/20 standard-only",
        "not replayed by this static script",
        f"{relative(VERIFICATION / 'logs' / 'pass07_final_appendix_axioms.log')}",
        "Bind to the separately recorded source manifest and Lean transcript.",
    )
    appendix_build_line = find_line(
        APPENDIX_SUMMARY, "final isolated `HighDimensionalProbability.Appendix`"
    )
    add(
        "APPENDIX_SUMMARY_BUILD",
        "dynamic_verification",
        "MINOR",
        "UNVERIFIABLE",
        APPENDIX_SUMMARY,
        appendix_build_line,
        "Lean/Lake run claim",
        "The final Appendix build passed 8,703/8,703 jobs.",
        "PASS 8703/8703",
        "not replayed by this static script",
        f"{relative(VERIFICATION / 'logs' / 'pass07_final_appendix_build.log')}",
        "Bind to the separately recorded source manifest and exit log.",
    )

    # Frozen inventories plus explicit current overlays.
    inventory_census_line = 1
    add(
        "INVENTORY_CENSUS_ROW_COUNT",
        "inventory",
        "MINOR",
        "MATCH" if len(census) == 838 else "STALE",
        INVENTORY / "review_census_838.tsv",
        inventory_census_line,
        "physical artifact count",
        "The frozen review census has 838 rows.",
        "838",
        str(len(census)),
        f"{relative(INVENTORY / 'review_census_838.tsv')}:1",
    )
    add(
        "INVENTORY_FROZEN_BUCKETS",
        "inventory",
        "MINOR",
        "MATCH"
        if (
            frozen["core_formalized"],
            frozen["appendix_proved"],
            frozen["appendix_unresolved_or_deferred"],
        )
        == (768, 65, 5)
        else "STALE",
        INVENTORY / "review_census_838.tsv",
        inventory_census_line,
        "explicit historical artifact",
        "The frozen artifact encodes 768/65/5.",
        "768/65/5",
        frozen_text,
        f"{relative(INVENTORY / 'review_census_838.tsv')}:1",
    )
    add(
        "INVENTORY_CURRENT_PROJECTION",
        "inventory",
        "MINOR",
        "MATCH"
        if (
            current["core_formalized"],
            current["appendix_proved"],
            current["appendix_unresolved_or_deferred"],
        )
        == (768, 66, 4)
        else "STALE",
        INVENTORY / "review_census_838.tsv",
        inventory_census_line,
        "current overlay",
        "The current projection moves only Brownian from deferred to proved.",
        "768/66/4",
        current_text,
        f"{relative(REVIEW_NOTES)}; {relative(APPENDIX_SUMMARY)}",
    )
    add(
        "INVENTORY_ENDPOINT_REPLACEMENT_OVERLAY",
        "published_endpoints",
        "MINOR",
        "MATCH"
        if (
            "HDP.Chapter3.borellConvexBodyPsiOnePrinciple_external"
            in replacement_text
            and "HDP.Chapter3.BorellConvexBodyPsiOnePrinciple"
            in replacement_text
            and "HDP.Chapter5.LipschitzWith" in replacement_text
            and "LipschitzWith" in replacement_text
        )
        else "STALE",
        replacement_path,
        1,
        "historical-to-current name overlay",
        "Both stale endpoint keys have explicit current resolutions.",
        "Borell and Lipschitz overlays",
        "both historical keys and current interfaces are present",
        f"{relative(replacement_path)}",
    )
    exercise_summary_line = find_line(
        INVENTORY / "inventory_summary.tsv", "exercise_leaf_declarations"
    )
    add(
        "INVENTORY_EXERCISE_DECLARATIONS",
        "exercises",
        "MINOR",
        "MATCH"
        if len(observed["exercise_inventory"]) == 247
        and observed["inventory_summary_tsv"]["exercise_leaf_declarations"] == "247"
        else "STALE",
        INVENTORY / "inventory_summary.tsv",
        exercise_summary_line,
        "physical machine inventory",
        "There are 247 exercise-leaf theorem/lemma declarations.",
        "247",
        f"rows={len(observed['exercise_inventory'])}; "
        f"summary={observed['inventory_summary_tsv']['exercise_leaf_declarations']}",
        f"{relative(INVENTORY / 'exercise_leaf_declarations.tsv')}:1",
    )
    endpoint_summary_line = find_line(
        INVENTORY / "inventory_summary.tsv", "endpoint_union_unique"
    )
    add(
        "INVENTORY_ENDPOINT_UNION",
        "published_endpoints",
        "MINOR",
        "MATCH"
        if len(observed["endpoint_union"]) == 637
        and observed["inventory_summary_tsv"]["endpoint_union_unique"] == "637"
        else "STALE",
        INVENTORY / "inventory_summary.tsv",
        endpoint_summary_line,
        "physical machine inventory",
        "The frozen endpoint union has 637 unique names.",
        "637",
        f"rows={len(observed['endpoint_union'])}; "
        f"summary={observed['inventory_summary_tsv']['endpoint_union_unique']}",
        f"{relative(INVENTORY / 'endpoint_union.tsv')}:1",
    )
    hash_line = find_line(INVENTORY / "inventory_summary.tsv", "validation_ok")
    add(
        "INVENTORY_SOURCE_HASH_FRESHNESS",
        "inventory",
        "MINOR",
        "MATCH" if all(observed["inventory_hash_matches"].values()) else "STALE",
        INVENTORY / "inventory_summary.tsv",
        hash_line,
        "inventory/source binding",
        "The frozen inventories are bound to their named source inputs.",
        "all source hashes match",
        "; ".join(
            f"{path}={str(match).lower()}"
            for path, match in observed["inventory_hash_matches"].items()
        ),
        f"{relative(INVENTORY / 'inventory_summary.json')}:source_sha256",
        "Regenerate the frozen inventory metadata if a named input changed.",
    )
    add(
        "PASS07_SOUNDNESS_RESOLUTION_LEDGER",
        "finding_resolution",
        "MINOR",
        "MATCH" if resolution_ok else "STALE",
        resolution_path,
        1,
        "machine-readable current dispositions",
        "All 25 non-INFO soundness findings have one current disposition.",
        "25 = 10 confirmed + 14 revised + 1 rejected",
        f"rows={len(resolution_rows)}; dispositions={dict(resolution_dispositions)}; "
        f"states={dict(resolution_states)}",
        f"{relative(resolution_path)}",
    )

    if len({row["claim_id"] for row in rows}) != len(rows):
        raise RuntimeError("duplicate current V9 claim_id")
    return rows


def build_active_claims(observed: Mapping[str, object]) -> list[dict[str, str]]:
    """Build the live post-removal V9 claim ledger.

    The older detector functions above remain executable historical code for
    the Pass-06/Pass-07 publications.  This function is deliberately
    independent of their obsolete 17-target and 838-current assumptions.
    """

    rows: list[dict[str, str]] = []

    def add(
        claim_id: str,
        category: str,
        path: Path,
        fragment: str | None,
        claim: str,
        claimed: str,
        value: str,
        matches: bool,
        evidence: str,
        *,
        scope: str = "current static claim",
        failure: str = "STALE",
        action: str = "None.",
    ) -> None:
        verdict = "MATCH" if matches else failure
        if verdict not in ALLOWED_VERDICTS:
            raise RuntimeError(f"{claim_id}: invalid verdict {verdict}")
        rows.append(
            {
                "claim_id": claim_id,
                "category": category,
                "severity": "MINOR",
                "verdict": verdict,
                "claim_file": relative(path),
                "claim_line": str(find_line(path, fragment) if fragment else 0),
                "claim_scope": scope,
                "claim": claim,
                "claimed_value": claimed,
                "observed_value": value,
                "evidence": evidence,
                "recommended_action": action,
            }
        )

    def unverified(
        claim_id: str,
        category: str,
        path: Path,
        fragment: str | None,
        claim: str,
        claimed: str,
        value: str,
        evidence: str,
        action: str,
    ) -> None:
        rows.append(
            {
                "claim_id": claim_id,
                "category": category,
                "severity": "MINOR",
                "verdict": "UNVERIFIABLE",
                "claim_file": relative(path),
                "claim_line": str(find_line(path, fragment) if fragment else 0),
                "claim_scope": "dynamic, semantic, or requested-alias claim",
                "claim": claim,
                "claimed_value": claimed,
                "observed_value": value,
                "evidence": evidence,
                "recommended_action": action,
            }
        )

    def normalized(path: Path) -> str:
        return " ".join(path.read_text(encoding="utf-8").split())

    active = observed["active_census"]
    frozen = observed["frozen_census"]
    active_buckets = observed["active_buckets"]
    frozen_buckets = observed["frozen_buckets"]
    active_by_id = observed["active_by_id"]
    declarations = observed["declarations"]
    core_kinds = declarations["core_kinds"]
    documentation_kinds = declarations["documentation_kinds"]
    readme_rows = observed["readme_rows"]
    readme_endpoints = observed["readme_endpoints"]
    chapters = observed["readme_chapters"]
    forbidden = observed["appendix_forbidden"]
    inventory = observed["inventory_summary_tsv"]
    active_chapters = Counter(row["chapter"] for row in active)
    frozen_text = (
        f"{len(frozen)} = {frozen_buckets['core_formalized']} core + "
        f"{frozen_buckets['appendix_proved']} Appendix + "
        f"{frozen_buckets['appendix_unresolved_or_deferred']} deferred"
    )
    active_text = (
        f"{len(active)} = {active_buckets['core_formalized']} core + "
        f"{active_buckets['appendix_proved']} Appendix + "
        f"{active_buckets['appendix_unresolved_or_deferred']} deferred"
    )
    core_text = (
        f"{declarations['core_total']} = {core_kinds['theorem']} theorem + "
        f"{core_kinds['lemma']} lemma + {core_kinds['def']} def"
    )
    documentation_text = (
        f"{declarations['documentation_total']} = "
        f"{documentation_kinds['theorem']} theorem + "
        f"{documentation_kinds['lemma']} lemma + "
        f"{documentation_kinds['def']} def in "
        f"{declarations['documentation_files']} files; "
        f"issues={declarations['documentation_issues']}"
    )
    map_text = (
        f"{len(readme_rows)} rows / {len(readme_endpoints)} endpoints; "
        f"V6={len(observed['v6_readme_rows'])}, "
        f"all_ok={str(observed['v6_all_ok']).lower()}, "
        f"locations={str(observed['v6_locations_complete']).lower()}"
    )
    appendix_token_text = ", ".join(
        f"{key}={value}" for key, value in forbidden.items()
    )
    root_text = normalized(ROOT_README)
    package_text = normalized(PACKAGE_README)
    review_text = normalized(REVIEW_NOTES)
    correction_text = normalized(CORRECTION_LEDGER)
    appendix_text = normalized(APPENDIX_SUMMARY)

    active_expected = (
        len(active),
        active_buckets["core_formalized"],
        active_buckets["appendix_proved"],
        active_buckets["appendix_unresolved_or_deferred"],
    ) == (835, 769, 66, 0)
    frozen_expected = (
        len(frozen),
        frozen_buckets["core_formalized"],
        frozen_buckets["appendix_proved"],
        frozen_buckets["appendix_unresolved_or_deferred"],
    ) == (838, 768, 65, 5)
    source_absence = (
        observed["removed_files_absent"]
        and not any(observed["removed_reference_counts"].values())
    )
    finite_hzero = all(
        "hzero" in signature and "∈ T" in signature
        for signature in observed["finite_chevet_signatures"].values()
    )
    exercise_row = observed["exercise_8_39_row"]
    exercise_endpoints = json_list(exercise_row["direct_endpoint_names"])
    brownian_row = observed["brownian_row"]
    brownian_endpoints = json_list(brownian_row["direct_endpoint_names"])
    active_endpoint_names = {
        endpoint
        for row in active
        for endpoint in json_list(row["endpoint_names"])
    }
    removed_endpoint_suffixes = tuple(REMOVED_DECLARATIONS)
    no_removed_inventory_endpoint = not any(
        endpoint.endswith(removed_endpoint_suffixes)
        for endpoint in observed["endpoint_union_names"] | active_endpoint_names
    )
    chapter_distribution = [chapters[f"Chapter {n}"] for n in range(1, 10)]
    expected_active_chapters = {
        "Appetizer": 11,
        "Chapter 1": 63,
        "Chapter 2": 71,
        "Chapter 3": 96,
        "Chapter 4": 117,
        "Chapter 5": 111,
        "Chapter 6": 47,
        "Chapter 7": 82,
        "Chapter 8": 122,
        "Chapter 9": 115,
    }

    # Requested aliases are still absent; the two explicit census artifacts
    # are the auditable current interfaces.
    unverified(
        "MISSING_REVIEW_CENSUS_DOCUMENT",
        "document_presence",
        REQUESTED_REVIEW_CENSUS,
        None,
        "A REVIEW_CENSUS.md alias is available.",
        "present",
        "absent; frozen and active machine-readable censuses are present",
        f"{relative(FROZEN_CENSUS_TSV)}; {relative(ACTIVE_CENSUS_TSV)}",
        "Use the two explicit frozen/current census paths.",
    )
    unverified(
        "MISSING_PLACEHOLDER_LEDGER_DOCUMENT",
        "document_presence",
        REQUESTED_PLACEHOLDER_LEDGER,
        None,
        "A PLACEHOLDER_LEDGER.md alias is available.",
        "present",
        "absent; CORRECTION_LEDGER.md and V3 are canonical",
        f"{relative(CORRECTION_LEDGER)}; {relative(VERIFICATION / '03_sorry_audit.md')}",
        "Use the canonical correction and V3 records.",
    )

    # Root README.
    add(
        "ROOT_README_PUBLICATION_COUNT", "publication_map", ROOT_README,
        "together with 611 audited", "The public map has 611 rows.", "611",
        map_text, len(readme_rows) == 611,
        relative(INVENTORY / "readme_correspondence.tsv"),
    )
    unverified(
        "ROOT_README_ALL_VERIFIED", "publication_map", ROOT_README,
        "together with 611 audited", "All retained mappings are verified.",
        "all verified", map_text + "; static V9 does not replay Lean or the PDF",
        relative(VERIFICATION / "logs" / "recert_v9_readme_axioms_summary.txt"),
        "Join this static result to the endpoint replay and PDF review.",
    )
    add(
        "ROOT_README_ACTIVE_CENSUS", "census", ROOT_README,
        "active PDF-revalidated whole-book projection contains 835",
        "The active census is 835 = 769 + 66 + 0.", "835/769/66/0",
        active_text, active_expected, relative(ACTIVE_CENSUS_TSV),
    )
    add(
        "ROOT_README_APPENDIX_REGISTRY", "appendix_registry", ROOT_README,
        "14/14 source-faithful proved targets",
        "The active Appendix registry is 14/14 and Borell support is not a target.",
        "14/14; Borell support non-target",
        f"target rows={len(observed['active_registry_rows'])}; "
        f"direct imports={len(observed['registry_imports'])}",
        len(observed["active_registry_rows"]) == 14
        and len(observed["registry_imports"]) == 15,
        f"{relative(APPENDIX_SUMMARY)}; {relative(APPENDIX_REGISTRY)}",
    )
    add(
        "ROOT_README_DECLARATIONS", "declaration_counts", ROOT_README,
        "5,625 target-kind declarations", "The core declaration count is current.",
        "5625 = 2862/1608/1155", core_text,
        (
            declarations["core_total"],
            core_kinds["theorem"],
            core_kinds["lemma"],
            core_kinds["def"],
        ) == (5625, 2862, 1608, 1155),
        "Canonical documentation scanner over Prelude and consolidated chapters.",
    )
    add(
        "ROOT_README_DOCUMENTATION", "declaration_counts", ROOT_README,
        "6,073 target declarations in 101 files",
        "The scoped documentation count is current.", "6073 in 101",
        documentation_text,
        (
            declarations["documentation_total"],
            declarations["documentation_files"],
            declarations["documentation_issues"],
        ) == (6073, 101, 0),
        "Canonical non-Appendix documentation scanner.",
    )
    add(
        "ROOT_README_EXCLUDED_SCOPES", "coverage_scope", ROOT_README,
        "only excluded scopes are equation (5.8)",
        "The three removed source scopes are explicitly excluded.",
        "Eq. 5.8; arbitrary Chevet a/Remark; Borell half",
        f"source absence={source_absence}; retained finite hzero={finite_hzero}",
        source_absence
        and finite_hzero
        and all(
            fragment in root_text
            for fragment in (
                "arbitrary-set forms of Exercise 8.39(a) and Remark 8.6.3",
                "Borell half of Example 3.4.6",
                "Finite-set Chevet results and Exercise 8.39(b) remain covered",
            )
        ),
        "Lexer-aware source scan and finite-theorem signatures.",
    )
    add(
        "ROOT_README_BUILD_RECIPE", "build_recipe", ROOT_README,
        "~/.elan/bin/lake build HighDimensionalProbability",
        "The authorized root build recipe is printed.", "exact command",
        "present", True, f"{relative(ROOT_README)}",
    )

    # Package README.
    add(
        "PACKAGE_README_PUBLICATION_COUNT", "publication_map", PACKAGE_README,
        "| Book → Lean correspondence |", "The package map has 611 rows.", "611",
        map_text, len(readme_rows) == 611,
        relative(INVENTORY / "readme_correspondence.json"),
    )
    unverified(
        "PACKAGE_README_ALL_VERIFIED", "publication_map", PACKAGE_README,
        "| Book → Lean correspondence |", "All package mappings are verified.",
        "611 verified; zero partial", map_text + "; dynamic/PDF replay is separate",
        relative(VERIFICATION / "logs" / "recert_v9_readme_axioms_summary.txt"),
        "Join this static result to the endpoint replay and PDF review.",
    )
    add(
        "PACKAGE_README_CHAPTER_DISTRIBUTION", "publication_map", PACKAGE_README,
        "| Chapter distribution |", "The chapter distribution is current.",
        "8; 51/59/75/88/68/39/62/100/61",
        f"{chapters['Appetizer']}; {'/'.join(map(str, chapter_distribution))}",
        chapters["Appetizer"] == 8
        and chapter_distribution == [51, 59, 75, 88, 68, 39, 62, 100, 61],
        relative(INVENTORY / "readme_correspondence.tsv"),
    )
    add(
        "PACKAGE_README_ACTIVE_CENSUS", "census", PACKAGE_README,
        "| Active PDF-revalidated whole-book census |",
        "The package active census is 835 = 769 + 66 + 0.", "835/769/66/0",
        active_text, active_expected, relative(ACTIVE_CENSUS_TSV),
    )
    add(
        "PACKAGE_README_DECLARATIONS", "declaration_counts", PACKAGE_README,
        "| Consolidated core declarations |", "Core counts are current.",
        "5625 = 2862/1608/1155", core_text,
        declarations["core_total"] == 5625, "Canonical documentation scanner.",
    )
    add(
        "PACKAGE_README_DOCUMENTATION", "declaration_counts", PACKAGE_README,
        "| Non-Appendix documentation audit |", "Documentation counts are current.",
        "6073/6073 in 101", documentation_text,
        declarations["documentation_total"] == 6073
        and declarations["documentation_issues"] == 0,
        "Canonical documentation scanner.",
    )
    add(
        "PACKAGE_README_ACTIVE_REGISTRY", "appendix_registry", PACKAGE_README,
        "contains exactly **14/14 source-faithful proved targets**",
        "The active registry is 14/14; the Borell import is support only.",
        "14/14; 15 imports", f"{len(observed['active_registry_rows'])}/"
        f"{len(observed['registry_imports'])}",
        len(observed["active_registry_rows"]) == 14
        and len(observed["registry_imports"]) == 15,
        f"{relative(APPENDIX_SUMMARY)}; {relative(APPENDIX_REGISTRY)}",
    )
    add(
        "PACKAGE_README_REMOVAL_SCOPE", "coverage_scope", PACKAGE_README,
        "assumption-strengthened Gaussian-Chevet target",
        "The three non-source-faithful target families are described as removed.",
        "three families removed", f"source absence={source_absence}",
        source_absence
        and all(
            fragment in package_text
            for fragment in (
                "positive-Ricci target",
                "skipped Borell target",
                "Borell module remains only as proved domain infrastructure",
            )
        ),
        "Lexer-aware source scan.",
    )
    add(
        "PACKAGE_README_RETAINED_SCOPE", "coverage_scope", PACKAGE_README,
        "finite-set Chevet rows and Exercise 8.39(b) remain covered",
        "Finite Chevet and reverse Exercise 8.39(b) remain.",
        "finite hzero + arbitrary reverse",
        f"hzero={finite_hzero}; reverse={observed['endpoint_presence']['chevet_reverse']}",
        finite_hzero and observed["endpoint_presence"]["chevet_reverse"],
        relative(HDP / "Chapter8_Chaining.lean"),
    )

    # Authoritative active review.
    add(
        "REVIEW_NOTES_ACTIVE_CENSUS", "census", REVIEW_NOTES,
        "**835 = 769 core-formalized",
        "The authoritative review publishes 835 = 769 + 66 + 0.",
        "835/769/66/0", active_text, active_expected, relative(ACTIVE_CENSUS_TSV),
    )
    add(
        "REVIEW_NOTES_CHAPTER_TABLE", "census", REVIEW_NOTES,
        "| **Whole book** | **873** | **769**",
        "The active per-chapter census totals are exact.",
        "11/63/71/96/117/111/47/82/122/115",
        "/".join(str(active_chapters[key]) for key in expected_active_chapters),
        dict(active_chapters) == expected_active_chapters,
        relative(ACTIVE_CENSUS_TSV),
    )
    add(
        "REVIEW_NOTES_OVERLAY_ROWS", "census", REVIEW_NOTES,
        "remove `census-bf1de680f35b52dc`",
        "The exact three removed row IDs are documented.",
        ";".join(sorted(REMOVED_ROW_IDS)),
        ";".join(observed["active_metadata"]["removed_row_ids"]),
        set(observed["active_metadata"]["removed_row_ids"]) == REMOVED_ROW_IDS
        and all(row_id in review_text for row_id in REMOVED_ROW_IDS),
        relative(ACTIVE_CENSUS_JSON),
    )
    add(
        "REVIEW_NOTES_EXERCISE_TRANSFORM", "census", REVIEW_NOTES,
        "retain `census-8e50e84b6b82a573` as **Exercise 8.39(b)**",
        "The combined Chevet row is transformed to Exercise 8.39(b).",
        "Exercise 8.39(b); core_formalized; reverse endpoint",
        f"{exercise_row['book_ref']}; {exercise_row['coverage_bucket']}; "
        f"{exercise_endpoints}",
        exercise_row["book_ref"] == "Exercise 8.39(b)"
        and exercise_row["coverage_bucket"] == "core_formalized"
        and exercise_endpoints
        == ["HDP.Chapter8.exercise_8_39b_gaussian_chevet_reverse_arbitrary"],
        relative(ACTIVE_CENSUS_TSV),
    )
    add(
        "REVIEW_NOTES_BROWNIAN_TRANSFORM", "census", REVIEW_NOTES,
        "retain the existing Round 9 Brownian move",
        "The Brownian row remains Appendix-proved.",
        "appendix_proved; Brownian endpoint",
        f"{brownian_row['coverage_bucket']}; {brownian_endpoints}",
        brownian_row["coverage_bucket"] == "appendix_proved"
        and brownian_endpoints
        == ["HDP.Chapter7.brownianReflectionPrinciple_external"],
        relative(ACTIVE_CENSUS_TSV),
    )
    add(
        "REVIEW_NOTES_BEFORE_AFTER", "census", REVIEW_NOTES,
        "| Valid conclusions | 838 | 835 |",
        "The before/after census and registry table is current.",
        "838→835; 768→769; 66→66; 4→0; 17→14; "
        "5630→5625; 6078→6073; 224→222",
        f"{frozen_text}; {active_text}; registry={len(observed['active_registry_rows'])}",
        frozen_expected and active_expected
        and len(observed["active_registry_rows"]) == 14
        and all(
            fragment in review_text
            for fragment in (
                "| Valid conclusions | 838 | 835 |",
                "| Core-formalized conclusions | 768 | 769 |",
                "| Appendix-proved conclusions | 66 | 66 |",
                "| Deferred/source-limited conclusions | 4 | 0 |",
                "| Registered Appendix targets | 17 | 14 |",
                "| Consolidated core target-kind declarations | 5,630 | 5,625 |",
                "| Documented non-Appendix target declarations | 6,078 | 6,073 |",
                "| Physical source files on checked surfaces | 224 | 222 |",
            )
        ),
        f"{relative(FROZEN_CENSUS_TSV)}; {relative(ACTIVE_CENSUS_TSV)}",
    )
    add(
        "REVIEW_NOTES_PUBLICATION_MAP", "publication_map", REVIEW_NOTES,
        "**611/611 verified mappings**",
        "The review distinguishes the unchanged map from the active census.",
        "611/540 unchanged", map_text,
        len(readme_rows) == 611
        and len(readme_endpoints) == 540
        and "None of the three removed scope rows appeared" in review_text,
        relative(INVENTORY / "readme_correspondence.tsv"),
    )
    add(
        "REVIEW_NOTES_APPENDIX_OUTCOMES", "coverage_scope", REVIEW_NOTES,
        "| Q1 | arbitrary-set Exercise 8.39(a)",
        "Q1/Q2/Q3 are removed and Q4 remains source-faithful.",
        "removed/removed/removed/proved",
        f"source absence={source_absence}; Brownian="
        f"{observed['endpoint_presence']['brownian']}",
        source_absence and observed["endpoint_presence"]["brownian"],
        "Current source declarations and removed files.",
    )
    add(
        "REVIEW_NOTES_PLACEHOLDERS", "placeholders", REVIEW_NOTES,
        "exactly **228 executable `sorry` proofs**",
        "The current placeholder count is 228 marked Exercise leaves and zero Appendix.",
        "228 in 46; Appendix 0",
        f"{observed['exercise_sorries']} in "
        f"{observed['exercise_files_with_sorry']}; "
        f"marked={observed['marked_sorries']}; Appendix={forbidden['sorry']}",
        (
            observed["exercise_sorries"],
            observed["exercise_files_with_sorry"],
            observed["marked_sorries"],
            forbidden["sorry"],
        ) == (228, 46, 228, 0),
        relative(VERIFICATION / "03_sorry_audit.md"),
    )
    add(
        "REVIEW_NOTES_DOCUMENTATION", "declaration_counts", REVIEW_NOTES,
        "**6,073/6,073 declarations**",
        "The active documentation count is current.", "6073/6073 in 101",
        documentation_text,
        declarations["documentation_total"] == 6073
        and declarations["documentation_issues"] == 0,
        "Canonical documentation scanner.",
    )
    unverified(
        "REVIEW_NOTES_BUILD_REPLAY", "dynamic_verification", REVIEW_NOTES,
        "| Default whole-tree build |",
        "The final whole-tree replay passes.", "PASS",
        "not replayed by this static script",
        relative(VERIFICATION / "logs" / "build_full_recertification.log"),
        "Bind to the separately completed build log and source manifest.",
    )
    unverified(
        "REVIEW_NOTES_APPENDIX_BUILD_REPLAY", "dynamic_verification", REVIEW_NOTES,
        "| Isolated Appendix build |",
        "The final isolated Appendix replay passes.", "PASS",
        "not replayed by this static script",
        relative(VERIFICATION / "logs" / "build_appendix_recertification.log"),
        "Bind to the separately completed build log and source manifest.",
    )

    # Correction ledger.
    add(
        "CORRECTION_LEDGER_REMOVAL_OUTCOMES", "coverage_scope", CORRECTION_LEDGER,
        "| Q1 | **Book Exercise 8.39(a)**",
        "The ledger records all three source-family removals.",
        "Q1/Q2/Q3 resolved by removal", f"source absence={source_absence}",
        source_absence
        and all(
            fragment in correction_text
            for fragment in (
                "| Q2 | **Book equation (5.8)**",
                "| Q3 | **Book Example 3.4.6**",
                "Five unconditional convex-body domain declarations remain",
            )
        ),
        "Lexer-aware source scan.",
    )
    add(
        "CORRECTION_LEDGER_ACTIVE_CENSUS", "census", CORRECTION_LEDGER,
        "**835 = 769 core + 66 Appendix proved + 0 deferred/source-limited**",
        "The correction ledger publishes the active census.",
        "835/769/66/0", active_text, active_expected, relative(ACTIVE_CENSUS_TSV),
    )
    add(
        "CORRECTION_LEDGER_REGISTRY", "appendix_registry", CORRECTION_LEDGER,
        "**14/14 source-faithful proved**",
        "The correction ledger publishes 14 targets and 15 direct imports.",
        "14/14; 15 imports",
        f"{len(observed['active_registry_rows'])}; {len(observed['registry_imports'])}",
        len(observed["active_registry_rows"]) == 14
        and len(observed["registry_imports"]) == 15,
        f"{relative(APPENDIX_SUMMARY)}; {relative(APPENDIX_REGISTRY)}",
    )
    add(
        "CORRECTION_LEDGER_PUBLICATION_MAP", "publication_map", CORRECTION_LEDGER,
        "611-row public correspondence contains none of the removed scope rows",
        "The public map is unchanged and excludes the removed census rows.",
        "611/540; removed rows absent", map_text,
        len(readme_rows) == 611 and len(readme_endpoints) == 540,
        relative(INVENTORY / "readme_correspondence.tsv"),
    )
    add(
        "CORRECTION_LEDGER_PLACEHOLDERS", "placeholders", CORRECTION_LEDGER,
        "Static reconciliation finds exactly 228 executable",
        "The ledger's placeholder claim is current.", "228; Appendix 0",
        f"{observed['exercise_sorries']}; {forbidden['sorry']}",
        observed["exercise_sorries"] == 228 and forbidden["sorry"] == 0,
        relative(VERIFICATION / "03_sorry_audit.md"),
    )
    add(
        "CORRECTION_LEDGER_DOCUMENTATION", "declaration_counts", CORRECTION_LEDGER,
        "6,073 non-Appendix target declarations in 101",
        "The ledger's documentation count is current.", "6073 in 101",
        documentation_text,
        declarations["documentation_total"] == 6073
        and declarations["documentation_files"] == 101,
        "Canonical documentation scanner.",
    )

    # Appendix active header and explicit historical boundary.
    add(
        "APPENDIX_SUMMARY_ACTIVE_REGISTRY", "appendix_registry", APPENDIX_SUMMARY,
        "exactly **14/14 source-faithful proved",
        "The active registry table has fourteen targets.", "14",
        str(len(observed["active_registry_rows"])),
        len(observed["active_registry_rows"]) == 14,
        f"{relative(APPENDIX_SUMMARY)}; {relative(APPENDIX_REGISTRY)}",
    )
    add(
        "APPENDIX_SUMMARY_IMPORT_COUNT", "appendix_registry", APPENDIX_SUMMARY,
        "aggregator has 15 direct imports",
        "The aggregator has fifteen imports, one non-target Borell module.",
        "15; Borell non-target", str(len(observed["registry_imports"])),
        len(observed["registry_imports"]) == 15
        and any("BorellConvexBody" in row for row in observed["registry_imports"]),
        relative(APPENDIX_REGISTRY),
    )
    add(
        "APPENDIX_SUMMARY_REMOVALS", "coverage_scope", APPENDIX_SUMMARY,
        "three former non-source-faithful scopes are closed by removal",
        "The active Appendix header records the three removals.",
        "three removed families", f"source absence={source_absence}",
        source_absence
        and all(
            fragment in appendix_text
            for fragment in (
                "`GaussianChevet.lean` wrapper/module were deleted",
                "`PositiveRicciConcentration.lean` and its three",
                "universal principle and conditional specialization were deleted",
            )
        ),
        "Lexer-aware source scan.",
    )
    add(
        "APPENDIX_SUMMARY_ACTIVE_CENSUS", "census", APPENDIX_SUMMARY,
        "active whole-book projection is **835 = 769 core + 66 Appendix + 0",
        "The Appendix active header publishes 835 = 769 + 66 + 0.",
        "835/769/66/0", active_text, active_expected, relative(ACTIVE_CENSUS_TSV),
    )
    add(
        "APPENDIX_SUMMARY_HISTORICAL_SCOPE", "historical_scope", APPENDIX_SUMMARY,
        "## Historical 17-target reconstruction record",
        "The stale 17-target dossier is explicitly scoped as historical.",
        "historical, not active",
        "header and non-active disclaimer present",
        "they are not the active registry above" in appendix_text,
        f"{relative(APPENDIX_SUMMARY)}: historical section",
    )
    add(
        "APPENDIX_SUMMARY_BORELL_SUPPORT", "appendix_endpoint", APPENDIX_SUMMARY,
        "retains five unconditional domain-support declarations only",
        "Borell retains exactly five domain-support declarations and no tail principle.",
        "5 support; 0 removed principle",
        f"support={len(observed['borell_support_declarations'])}; "
        f"removed refs={observed['removed_reference_counts']}",
        len(observed["borell_support_declarations"]) == 5
        and observed["removed_reference_counts"]["BorellConvexBodyPsiOnePrinciple"] == 0
        and observed["removed_reference_counts"][
            "convexBodyUniform_marginal_subExponential_of_borell"
        ] == 0,
        relative(HDP / "Appendix" / "BorellConvexBody.lean"),
    )
    add(
        "APPENDIX_SUMMARY_FINITE_CHEVET", "appendix_endpoint", APPENDIX_SUMMARY,
        "direct finite-set theorems remain in core with explicit `0 ∈ T`",
        "Both direct finite Chevet statements visibly require zero membership.",
        "two visible hzero binders", str(finite_hzero), finite_hzero,
        relative(HDP / "Chapter8_Chaining.lean"),
    )
    add(
        "APPENDIX_SUMMARY_SOURCE_CLEAN", "placeholders", APPENDIX_SUMMARY,
        "active Appendix registry contains exactly",
        "The active Appendix source has no forbidden proof construct.",
        "all zero", appendix_token_text, all(value == 0 for value in forbidden.values()),
        "Lexer-aware scan of Appendix.lean and Appendix/**/*.lean.",
    )

    # Direct source/API checks.
    add(
        "SOURCE_REMOVED_FILES", "source_removal", APPENDIX_SUMMARY,
        "`GaussianChevet.lean` wrapper/module were deleted",
        "Both removed modules are absent.", "2 absent",
        ", ".join(f"{relative(path)}={path.exists()}" for path in REMOVED_FILES),
        observed["removed_files_absent"], "Direct filesystem existence check.",
        failure="OVERSTATED",
    )
    add(
        "SOURCE_REMOVED_DECLARATIONS", "source_removal", APPENDIX_SUMMARY,
        "universal principle and conditional specialization were deleted",
        "All twelve removed declaration names have zero live source references.",
        "12 names; all zero",
        "; ".join(
            f"{name}={count}"
            for name, count in observed["removed_reference_counts"].items()
        ),
        not any(observed["removed_reference_counts"].values()),
        "Lexer-masked scan over non-Verification Lean source.",
        failure="OVERSTATED",
    )
    add(
        "SOURCE_FINITE_CHEVET_SIGNATURES", "source_retention", REVIEW_NOTES,
        "finite Gaussian-Chevet theorems remain in core with an explicit",
        "Both retained finite theorem names have visible 0 ∈ T binders.",
        "2/2 hzero", str(finite_hzero),
        observed["endpoint_presence"]["finite_chevet_a"]
        and observed["endpoint_presence"]["finite_chevet_remark"]
        and finite_hzero,
        relative(HDP / "Chapter8_Chaining.lean"),
    )
    add(
        "SOURCE_REVERSE_CHEVET", "source_retention", REVIEW_NOTES,
        "Exercise 8.39(b) remains core-proved",
        "The arbitrary-set reverse theorem remains.",
        "exercise_8_39b_gaussian_chevet_reverse_arbitrary",
        str(observed["endpoint_presence"]["chevet_reverse"]),
        observed["endpoint_presence"]["chevet_reverse"],
        relative(HDP / "Chapter8_Chaining.lean"),
    )
    add(
        "SOURCE_BORELL_DOMAIN_SUPPORT", "source_retention", APPENDIX_SUMMARY,
        "five unconditional domain-support declarations only",
        "The Borell module exports five unconditional domain declarations.",
        "5", str(len(observed["borell_support_declarations"])),
        len(observed["borell_support_declarations"]) == 5,
        relative(HDP / "Appendix" / "BorellConvexBody.lean"),
    )
    add(
        "SOURCE_BROWNIAN_ENDPOINT", "source_retention", PACKAGE_README,
        "`HDP.Chapter7.brownianReflectionPrinciple_external`",
        "The Brownian source-faithful endpoint remains.",
        "present", str(observed["endpoint_presence"]["brownian"]),
        observed["endpoint_presence"]["brownian"],
        relative(HDP / "Appendix" / "BrownianReflection.lean"),
    )
    add(
        "SOURCE_APPENDIX_ISOLATION", "isolation", APPENDIX_REGISTRY,
        "outside the root import graph",
        "No non-Appendix source imports the Appendix.", "0 leaks",
        str(observed["appendix_import_leaks"]),
        observed["appendix_import_leaks"] == 0,
        "Lexer-masked import scan.",
    )
    add(
        "SOURCE_PHYSICAL_FILES", "source_inventory", REVIEW_NOTES,
        "**222 physical library files**",
        "The active physical library universe is 222 = 212 HDP + 10 Matrix.",
        "222/212/10",
        f"{observed['physical_library_files']}/"
        f"{observed['physical_hdp_files']}/"
        f"{observed['physical_matrix_files']}",
        (
            observed["physical_library_files"],
            observed["physical_hdp_files"],
            observed["physical_matrix_files"],
        ) == (222, 212, 10),
        "Direct non-symlink .lean enumeration; no MatrixConcentration writes.",
    )

    # Frozen and active machine-readable inventories.
    add(
        "INVENTORY_FROZEN_TSV_AUTHENTIC", "inventory", FROZEN_CENSUS_TSV,
        None, "The frozen 838 TSV is byte-authentic.", EXPECTED_FROZEN_CENSUS_TSV_SHA256,
        observed["frozen_digest"],
        observed["frozen_digest"] == EXPECTED_FROZEN_CENSUS_TSV_SHA256,
        "Direct SHA-256.",
    )
    add(
        "INVENTORY_FROZEN_JSON_AUTHENTIC", "inventory", FROZEN_CENSUS_JSON,
        None, "The frozen 838 JSON is byte-authentic.", EXPECTED_FROZEN_CENSUS_JSON_SHA256,
        observed["frozen_json_digest"],
        observed["frozen_json_digest"] == EXPECTED_FROZEN_CENSUS_JSON_SHA256,
        "Direct SHA-256.",
    )
    add(
        "INVENTORY_FROZEN_COUNTS", "inventory", FROZEN_CENSUS_TSV,
        None, "The frozen census remains 838 = 768 + 65 + 5.", "838/768/65/5",
        frozen_text, frozen_expected, "Counter over immutable TSV.",
    )
    add(
        "INVENTORY_ACTIVE_COUNTS", "inventory", ACTIVE_CENSUS_TSV,
        None, "The active census is 835 = 769 + 66 + 0.", "835/769/66/0",
        active_text, active_expected, "Counter over active TSV.",
    )
    add(
        "INVENTORY_ACTIVE_EXACT_SUBTRACTION", "inventory", ACTIVE_CENSUS_JSON,
        None, "The active row-ID set is frozen minus exactly three rows.",
        "838 - 3 = 835",
        observed["active_metadata"]["derivation"],
        set(active_by_id) == set(observed["frozen_by_id"]) - REMOVED_ROW_IDS
        and observed["active_metadata"]["derivation"]
        == "838 - 3 removed conclusions = 835",
        f"{relative(FROZEN_CENSUS_TSV)}; {relative(ACTIVE_CENSUS_TSV)}",
    )
    add(
        "INVENTORY_ACTIVE_EXERCISE_ROW", "inventory", ACTIVE_CENSUS_TSV,
        None, "The retained Chevet row is Exercise 8.39(b) only.",
        "core_formalized reverse endpoint",
        f"{exercise_row['book_ref']}; {exercise_row['coverage_bucket']}; "
        f"{exercise_endpoints}",
        exercise_row["book_ref"] == "Exercise 8.39(b)"
        and exercise_row["coverage_bucket"] == "core_formalized"
        and exercise_endpoints
        == ["HDP.Chapter8.exercise_8_39b_gaussian_chevet_reverse_arbitrary"],
        relative(ACTIVE_CENSUS_JSON),
    )
    add(
        "INVENTORY_ACTIVE_BROWNIAN_ROW", "inventory", ACTIVE_CENSUS_TSV,
        None, "The Brownian row is Appendix-proved.", "appendix_proved",
        f"{brownian_row['coverage_bucket']}; {brownian_endpoints}",
        brownian_row["coverage_bucket"] == "appendix_proved"
        and brownian_endpoints
        == ["HDP.Chapter7.brownianReflectionPrinciple_external"],
        relative(ACTIVE_CENSUS_JSON),
    )
    add(
        "INVENTORY_ENDPOINT_UNION", "inventory", INVENTORY / "endpoint_union.tsv",
        None, "The active endpoint union has 634 unique endpoints.", "634",
        str(len(observed["endpoint_union"])),
        len(observed["endpoint_union"]) == 634
        and inventory["endpoint_union_unique"] == "634",
        relative(INVENTORY / "inventory_summary.tsv"),
    )
    add(
        "INVENTORY_NO_REMOVED_ENDPOINTS", "inventory",
        INVENTORY / "endpoint_union.tsv", None,
        "No active inventory endpoint names a removed conditional interface.",
        "zero removed endpoint names", str(no_removed_inventory_endpoint),
        no_removed_inventory_endpoint,
        f"{relative(INVENTORY / 'endpoint_union.tsv')}; {relative(ACTIVE_CENSUS_TSV)}",
        failure="OVERSTATED",
    )
    add(
        "INVENTORY_SUMMARY_COUNTS", "inventory",
        INVENTORY / "inventory_summary.tsv", "census_rows",
        "The summary publishes 611/540, frozen 838, active 835, and union 634.",
        "611/540/838/835/634",
        "/".join(
            inventory[key]
            for key in (
                "readme_rows",
                "readme_unique_endpoints",
                "frozen_census_rows",
                "census_rows",
                "endpoint_union_unique",
            )
        ),
        [
            inventory[key]
            for key in (
                "readme_rows",
                "readme_unique_endpoints",
                "frozen_census_rows",
                "census_rows",
                "endpoint_union_unique",
            )
        ] == ["611", "540", "838", "835", "634"],
        relative(INVENTORY / "inventory_summary.json"),
    )
    add(
        "INVENTORY_EXERCISE_AND_SAMPLE_COUNTS", "inventory",
        INVENTORY / "inventory_summary.tsv", "exercise_leaf_declarations",
        "Exercise and deterministic sampling counts remain 247/27/50.",
        "247/27/50",
        f"{len(observed['exercise_inventory'])}/"
        f"{inventory['exercise_samples']}/"
        f"{inventory['ok_candidate_queue_head']}",
        len(observed["exercise_inventory"]) == 247
        and len(observed["sampling_plan"]) == 77
        and inventory["exercise_samples"] == "27"
        and inventory["ok_candidate_queue_head"] == "50",
        f"{relative(INVENTORY / 'exercise_leaf_declarations.tsv')}; "
        f"{relative(INVENTORY / 'sampling_plan.tsv')}",
    )
    add(
        "INVENTORY_SOURCE_HASHES", "inventory",
        INVENTORY / "inventory_summary.json", None,
        "The generated inventory source hashes match current inputs.",
        "all true",
        "; ".join(
            f"{path}={str(match).lower()}"
            for path, match in observed["inventory_hash_matches"].items()
        ),
        all(observed["inventory_hash_matches"].values()),
        relative(INVENTORY / "inventory_summary.json"),
    )
    add(
        "INVENTORY_V6_PUBLICATION_JOIN", "publication_map",
        INVENTORY / "readme_correspondence.tsv", None,
        "V6 covers all 611 map row IDs with OK dispositions and locations.",
        "611/611 OK with locations", map_text,
        len(observed["v6_readme_rows"]) == 611
        and observed["v6_all_ok"]
        and observed["v6_locations_complete"],
        f"{relative(REVIEW / 'v6_tier_b_ch0_4.tsv')}; "
        f"{relative(REVIEW / 'v6_tier_b_ch5_7.tsv')}; "
        f"{relative(REVIEW / 'v6_tier_b_ch8_9.tsv')}",
    )

    if len({row["claim_id"] for row in rows}) != len(rows):
        raise RuntimeError("duplicate V9 active claim_id")
    return rows


def render_tsv(rows: list[dict[str, str]]) -> str:
    buffer = io.StringIO(newline="")
    writer = csv.DictWriter(
        buffer,
        fieldnames=FIELDS,
        delimiter="\t",
        lineterminator="\n",
        extrasaction="raise",
    )
    writer.writeheader()
    writer.writerows(rows)
    return buffer.getvalue()


def render_summary(
    rows: list[dict[str, str]], observed: Mapping[str, object], tsv_text: str
) -> str:
    verdicts = Counter(row["verdict"] for row in rows)
    issues = [row for row in rows if row["verdict"] != "MATCH"]
    severities = Counter(row["severity"] for row in issues)
    current = observed["current_buckets"]
    frozen = observed["frozen_buckets"]
    critical = [row for row in issues if row["severity"] == "CRITICAL"]
    major = [row for row in issues if row["severity"] == "MAJOR"]
    overstated = [row for row in rows if row["verdict"] == "OVERSTATED"]
    unverified = [row for row in rows if row["verdict"] == "UNVERIFIABLE"]

    lines = [
        "V9 STATIC DOCUMENTATION / CENSUS INTEGRITY",
        "==========================================",
        f"ledger: {relative(OUTPUT)}",
        f"script: {relative(Path(__file__).resolve())}",
        "method: deterministic static source/document/inventory scan; no Lean, Lake, Git, cp, or network",
        f"tsv_sha256: {hashlib.sha256(tsv_text.encode('utf-8')).hexdigest()}",
        "",
        "[canonical reconciliation: selected path 2]",
        f"frozen artifact: 838 = {frozen['core_formalized']} core + "
        f"{frozen['appendix_proved']} Appendix proved + "
        f"{frozen['appendix_unresolved_or_deferred']} deferred",
        f"current source-aligned projection: 838 = {current['core_formalized']} core + "
        f"{current['appendix_proved']} Appendix proved + "
        f"{current['appendix_unresolved_or_deferred']} deferred",
        "derivation: only Remark 7.2.1 Brownian moves from deferred to source-faithful proved",
        "remaining four census rows: Borell, positive Ricci, and two arbitrary-set Chevet rows",
        "registry layer: 17 = 14 source-faithful PROVED + 2 assumption-strengthened PROVED + 1 SKIPPED",
        "",
        "[claim ledger]",
        f"rows: {len(rows)}",
        "verdicts: "
        + ", ".join(f"{key}={verdicts[key]}" for key in sorted(ALLOWED_VERDICTS)),
        "issue severities (MATCH excluded): "
        + ", ".join(f"{key}={severities[key]}" for key in ("CRITICAL", "MAJOR", "MINOR")),
        f"critical findings: {len(critical)}",
        "",
        "[principal major findings]",
    ]
    if major:
        lines.extend(
            f"{row['claim_id']}\t{row['verdict']}\t"
            f"{row['claim_file']}:{row['claim_line']}\t{row['observed_value']}"
            for row in major
        )
    else:
        lines.append("none")

    lines.extend(("", "[overstated endpoint-name claims]"))
    if overstated:
        lines.extend(
            f"{row['claim_id']}\t{row['claim_file']}:{row['claim_line']}\t"
            f"{row['observed_value']}"
            for row in overstated
        )
    else:
        lines.append("none")

    lines.extend(("", "[static-scope limitations]"))
    if unverified:
        lines.extend(
            f"{row['claim_id']}\t{row['claim_file']}:{row['claim_line']}\t"
            f"{row['claim']}"
            for row in unverified
        )
    else:
        lines.append("none")

    lines.extend(
        (
            "",
            "[measured current source]",
            f"core declarations: {observed['declarations']['core_total']} in "
            f"{observed['declarations']['core_files']} files",
            f"documented non-Appendix declarations: "
            f"{observed['declarations']['documentation_total']} in "
            f"{observed['declarations']['documentation_files']} files; "
            f"issues={observed['declarations']['documentation_issues']}",
            f"exercise placeholders: {observed['exercise_sorries']} in "
            f"{observed['exercise_files_with_sorry']} files; "
            f"marked={observed['marked_sorries']}",
            "Appendix forbidden tokens: "
            + ", ".join(
                f"{key}={value}"
                for key, value in observed["appendix_forbidden"].items()
            ),
            f"Appendix imports outside Appendix: {observed['appendix_import_leaks']}",
            f"publication map: {len(observed['readme_rows'])} rows / "
            f"{len(observed['readme_endpoints'])} unique endpoint names",
            "",
            "[missing requested filenames]",
            f"{relative(REQUESTED_REVIEW_CENSUS)}: missing; audited "
            f"{relative(INVENTORY / 'review_census_838.tsv')} and "
            f"{relative(REVIEW_NOTES)}",
            f"{relative(REQUESTED_PLACEHOLDER_LEDGER)}: missing; audited "
            f"{relative(CORRECTION_LEDGER)} and current source tokens",
            "",
            "verdict definitions:",
            "MATCH = the exact scoped claim agrees with static evidence.",
            "STALE = formerly/historically plausible, but contradicted by current source/status.",
            "OVERSTATED = the document/inventory asserts a declaration or result not exported.",
            "UNVERIFIABLE = missing document or a PDF/kernel/build claim outside static scope.",
            "",
        )
    )
    return "\n".join(lines)


def render_active_summary(
    rows: list[dict[str, str]],
    observed: Mapping[str, object],
    tsv_text: str,
) -> str:
    """Render the current 835-census summary without historical ambiguity."""

    verdicts = Counter(row["verdict"] for row in rows)
    actionable = [
        row
        for row in rows
        if row["verdict"] in {"STALE", "OVERSTATED"}
    ]
    unverified = [row for row in rows if row["verdict"] == "UNVERIFIABLE"]
    active = observed["active_buckets"]
    frozen = observed["frozen_buckets"]
    lines = [
        "V9 STATIC DOCUMENTATION / CURRENT-CENSUS INTEGRITY",
        "==================================================",
        f"ledger: {relative(OUTPUT)}",
        f"script: {relative(Path(__file__).resolve())}",
        "method: deterministic static source/document/inventory scan; no Lean, Lake, Git, cp, or network",
        f"tsv_sha256: {hashlib.sha256(tsv_text.encode('utf-8')).hexdigest()}",
        "",
        "[census layers]",
        f"frozen historical artifact: {len(observed['frozen_census'])} = "
        f"{frozen['core_formalized']} core + {frozen['appendix_proved']} Appendix + "
        f"{frozen['appendix_unresolved_or_deferred']} deferred",
        f"frozen_tsv_sha256: {observed['frozen_digest']}",
        f"frozen_json_sha256: {observed['frozen_json_digest']}",
        f"active projection: {len(observed['active_census'])} = "
        f"{active['core_formalized']} core + {active['appendix_proved']} Appendix + "
        f"{active['appendix_unresolved_or_deferred']} deferred",
        "derivation: immutable 838 minus three removed conclusions; "
        "Exercise 8.39(b) retained as core; Brownian retained as Appendix",
        "removed row IDs: " + ", ".join(sorted(REMOVED_ROW_IDS)),
        "active Appendix registry: 14 source-faithful targets / 15 direct imports "
        "(Borell support is not a target)",
        "",
        "[claim ledger]",
        f"rows: {len(rows)}",
        "verdicts: "
        + ", ".join(f"{key}={verdicts[key]}" for key in sorted(ALLOWED_VERDICTS)),
        f"actionable current mismatches: {len(actionable)}",
        "",
        "[actionable current mismatches]",
    ]
    if actionable:
        lines.extend(
            f"{row['claim_id']}\t{row['verdict']}\t"
            f"{row['claim_file']}:{row['claim_line']}\t{row['observed_value']}"
            for row in actionable
        )
    else:
        lines.append("none")

    lines.extend(("", "[static-scope limitations]"))
    if unverified:
        lines.extend(
            f"{row['claim_id']}\t{row['claim_file']}:{row['claim_line']}\t"
            f"{row['claim']}"
            for row in unverified
        )
    else:
        lines.append("none")

    lines.extend(
        (
            "",
            "[measured current source]",
            f"physical library files: {observed['physical_library_files']} = "
            f"{observed['physical_hdp_files']} HDP + "
            f"{observed['physical_matrix_files']} MatrixConcentration",
            f"core declarations: {observed['declarations']['core_total']} in "
            f"{observed['declarations']['core_files']} files",
            f"documented non-Appendix declarations: "
            f"{observed['declarations']['documentation_total']} in "
            f"{observed['declarations']['documentation_files']} files; "
            f"issues={observed['declarations']['documentation_issues']}",
            f"exercise placeholders: {observed['exercise_sorries']} in "
            f"{observed['exercise_files_with_sorry']} files; "
            f"marked={observed['marked_sorries']}",
            "Appendix forbidden tokens: "
            + ", ".join(
                f"{key}={value}"
                for key, value in observed["appendix_forbidden"].items()
            ),
            "removed declaration source references: "
            + ", ".join(
                f"{key}={value}"
                for key, value in observed["removed_reference_counts"].items()
            ),
            f"Appendix imports outside Appendix: {observed['appendix_import_leaks']}",
            f"publication map: {len(observed['readme_rows'])} rows / "
            f"{len(observed['readme_endpoints'])} unique endpoint names",
            f"active endpoint union: {len(observed['endpoint_union'])}",
            "",
            "[missing requested filenames]",
            f"{relative(REQUESTED_REVIEW_CENSUS)}: missing; audited "
            f"{relative(FROZEN_CENSUS_TSV)}, {relative(ACTIVE_CENSUS_TSV)}, "
            f"and {relative(REVIEW_NOTES)}",
            f"{relative(REQUESTED_PLACEHOLDER_LEDGER)}: missing; audited "
            f"{relative(CORRECTION_LEDGER)} and current source tokens",
            "",
            "verdict definitions:",
            "MATCH = the exact current scoped claim agrees with static evidence.",
            "STALE = a present-tense claim is contradicted by current source/status.",
            "OVERSTATED = a current interface or inventory asserts removed source.",
            "UNVERIFIABLE = a missing alias or PDF/kernel/build claim is outside static scope.",
            "",
        )
    )
    return "\n".join(lines)


def write_or_check(path: Path, content: str, *, check: bool) -> bool:
    if check:
        return path.is_file() and path.read_text(encoding="utf-8") == content
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")
    return True


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--check",
        action="store_true",
        help="verify that committed outputs equal a fresh static reconstruction",
    )
    args = parser.parse_args(argv)

    observed = current_observations()
    rows = build_active_claims(observed)
    tsv_text = render_tsv(rows)
    summary_text = render_active_summary(rows, observed, tsv_text)

    tsv_ok = write_or_check(OUTPUT, tsv_text, check=args.check)
    summary_ok = write_or_check(SUMMARY, summary_text, check=args.check)
    if args.check and not (tsv_ok and summary_ok):
        if not tsv_ok:
            print(f"stale or missing: {relative(OUTPUT)}", file=sys.stderr)
        if not summary_ok:
            print(f"stale or missing: {relative(SUMMARY)}", file=sys.stderr)
        return 1

    verdicts = Counter(row["verdict"] for row in rows)
    print(
        f"V9 documentation/census: rows={len(rows)}, "
        + ", ".join(f"{key}={verdicts[key]}" for key in sorted(ALLOWED_VERDICTS))
    )
    print(f"ledger: {relative(OUTPUT)}")
    print(f"summary: {relative(SUMMARY)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
