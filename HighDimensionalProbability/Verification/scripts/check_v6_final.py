#!/usr/bin/env python3
"""Fail-closed, no-Lean validation of the final current-tree V6 packet."""

from __future__ import annotations

import argparse
import csv
import json
import re
import sys
from collections import Counter
from pathlib import Path

import recert_v6_tier_c as recert
from verify_exercise_reorganization import require_certificate


VERIFICATION = Path(__file__).resolve().parents[1]
REPORT = VERIFICATION / "06_vacuity_triviality.md"
REVIEW = VERIFICATION / "review"
LOGS = VERIFICATION / "logs"
SEED = "83678e994eecf416759cb099d5e69f9d03c15921960d4f3b69d055a7a9e8fe27"
CHAPTERS = ("Appetizer", *(f"Chapter {index}" for index in range(1, 10)))
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED_TIER_A_ESCALATIONS = {
    "HDP.Chapter6.Exercise.exercise_6_25",
    "HDP.Chapter7.exercise_7_7_logPartitionDerivativeExpression_nonpos",
    "HDP.matrixSingularValue_of_finrank_le",
}
REMOVED_CONDITIONAL_INTERFACES = {
    "HDP.Chapter3.BorellConvexBodyPsiOnePrinciple",
    "HDP.Chapter3.convexBodyUniform_marginal_subExponential_of_borell",
    "HDP.Chapter5.positive_ricci_concentration",
    "HDP.Chapter5.positive_ricci_concentration_psi2",
    "HDP.Chapter5.positive_ricci_concentration_psi2_of_lipschitz",
    "HDP.Chapter8.GaussianChevetUpperPrinciple",
    "HDP.Chapter8.exercise_8_39a_gaussian_chevet_arbitrary_envelope",
    "HDP.Chapter8.gaussianChevetExpectationEnvelope_ne_top_of_isBounded",
    "HDP.Chapter8.remark_8_6_3_gaussian_chevet_arbitrary_envelope",
    "HDP.Chapter8.exercise_8_39a_gaussian_chevet_arbitrary",
    "HDP.Chapter8.gaussianChevetUpperPrinciple_external",
    "HDP.Chapter8.remark_8_6_3_gaussian_chevet_arbitrary",
}

EXPECTED_FRAME = {
    "Appetizer": (17, 5, 5, 0, 7, 5),
    "Chapter 1": (60, 5, 5, 0, 50, 5),
    "Chapter 2": (73, 5, 5, 6, 57, 5),
    "Chapter 3": (93, 5, 6, 1, 81, 5),
    "Chapter 4": (99, 5, 11, 16, 67, 5),
    "Chapter 5": (88, 5, 9, 9, 65, 5),
    "Chapter 6": (47, 5, 5, 6, 31, 5),
    "Chapter 7": (72, 5, 12, 12, 43, 5),
    "Chapter 8": (120, 5, 10, 15, 90, 5),
    "Chapter 9": (111, 5, 6, 15, 85, 5),
}

POSITIVE_LOGS = (
    "recert_v6_tier_c_seeded_sample_build.log",
    "recert_v6_tier_c_ch0_4_build.log",
    "recert_v6_tier_c_ch0_4_axiom_build.log",
    "recert_v6_tier_c_ch5_7_build.log",
    "recert_v6_tier_c_ch5_7_axioms.log",
    "recert_v6_tier_c_ch8_9_build.log",
    "recert_v6_tier_c_ch8_9_axioms.log",
    "recert_v6_tier_c_command.log",
    "recert_v6_tier_c_check.log",
)


def read_tsv(path: Path) -> list[dict[str, str]]:
    with path.open(encoding="utf-8", newline="") as handle:
        return list(csv.DictReader(handle, delimiter="\t"))


def unexpected_axioms(axioms: set[str]) -> set[str]:
    return axioms - ALLOWED_AXIOMS


def has_unique_row_ids(rows: list[dict[str, str]]) -> bool:
    ids = [row["row_id"] for row in rows]
    return len(ids) == len(set(ids))


def tier_b_endpoint_names(rows: list[dict[str, str]]) -> set[str]:
    """Return every declaration named by any of the Tier-B ledger schemas."""
    return {
        endpoint.strip()
        for row in rows
        for column in ("resolved_declarations", "inventory_endpoint", "endpoint")
        for endpoint in row.get(column, "").split(";")
        if endpoint.strip()
    }


def removed_interfaces_in_code(code: str) -> set[str]:
    """Return removed interfaces still named in comment/string-masked Lean code."""
    return {
        qualified
        for qualified in REMOVED_CONDITIONAL_INTERFACES
        if re.search(rf"\b{re.escape(qualified.rsplit('.', 1)[-1])}\b", code)
    }


def self_test() -> int:
    if unexpected_axioms({"propext", "sorryAx"}) != {"sorryAx"}:
        print("FAIL V6 final checker self-test: planted sorryAx was not rejected")
        return 1
    if has_unique_row_ids([{"row_id": "duplicate"}, {"row_id": "duplicate"}]):
        print("FAIL V6 final checker self-test: duplicate sample row escaped")
        return 1
    if unexpected_axioms(ALLOWED_AXIOMS) or not has_unique_row_ids(
        [{"row_id": "left"}, {"row_id": "right"}]
    ):
        print("FAIL V6 final checker self-test: clean controls were rejected")
        return 1
    if tier_b_endpoint_names(
        [{"resolved_declarations": "HDP.left; HDP.removed;HDP.right"}]
    ) != {"HDP.left", "HDP.removed", "HDP.right"}:
        print(
            "FAIL V6 final checker self-test: multi-endpoint Tier-B cell "
            "was not fully enumerated"
        )
        return 1
    planted_code, planted_diagnostics = recert.mask_lean_noncode(
        "/- positive_ricci_concentration is prose only -/\n"
        "class GaussianChevetUpperPrinciple : Type where"
    )
    if planted_diagnostics or removed_interfaces_in_code(planted_code) != {
        "HDP.Chapter8.GaussianChevetUpperPrinciple"
    }:
        print(
            "FAIL V6 final checker self-test: planted removed interface "
            "was not detected"
        )
        return 1
    print(
        "PASS V6 final checker self-test: planted sorryAx and duplicate "
        "sample row rejected; multi-endpoint and removed-interface "
        "detectors calibrated"
    )
    return 0


def main() -> int:
    errors: list[str] = []

    def require(condition: bool, message: str) -> None:
        if not condition:
            errors.append(message)

    try:
        current_source_digest = require_certificate()
    except (OSError, RuntimeError, TypeError, ValueError) as error:
        errors.append(f"exercise-reorganization certificate failed: {error}")
        current_source_digest = "UNVERIFIED"

    # Reuse the authoritative read-only gates: exact seeded artifacts, source
    # lexical gate, legacy queue identity, axiom parsing, and planted bad row.
    for label, action in (
        ("legacy fixed queue", recert.validate_fixed_queue),
        ("witness source", recert.validate_sources),
        ("removed Borell boundary", recert.ch0.check_borell_boundary),
        (
            "seeded sampling artifacts",
            lambda: recert.validate_seeded_artifacts(write=False),
        ),
        ("planted bad witness", recert.validate_planted_bad),
    ):
        try:
            action()
        except Exception as error:  # fail closed and report every independent gate
            errors.append(f"{label} gate failed: {error}")

    try:
        axiom_evidence = recert.collect_axiom_evidence()
    except Exception as error:
        errors.append(f"compiled axiom evidence gate failed: {error}")
        axiom_evidence = {}

    register = read_tsv(REVIEW / "recert_v6_tier_c.tsv")
    require(len(register) == 103, f"Tier-C register has {len(register)} rows, not 103")
    require(has_unique_row_ids(register), "Tier-C register row IDs are not unique")
    require(
        Counter(row["category"] for row in register)
        == Counter(
            {
                "fixed_ok_sample": 50,
                "seeded_random_ok_sample": 50,
                "tier_a_escalation": 3,
            }
        ),
        "Tier-C category census is not 50 fixed + 50 seeded + 3 Tier-A",
    )
    require(
        Counter(row["evidence_kind"] for row in register)
        == Counter(
            {
                "COMPILED_NAMED_WITNESS": 91,
                "EXACT_V4_DIRECT_VALUE_CITATION": 12,
            }
        ),
        "Tier-C evidence census is not 91 witnesses + 12 citations",
    )
    require(
        Counter(row["semantic_verdict"] for row in register)
        == Counter({"OK": 103}),
        "Tier-C semantic verdict census is not 103 OK",
    )
    require(
        Counter(row["tier_c_status"] for row in register)
        == Counter({"PASS": 103}),
        "Tier-C status census drifted",
    )

    expected_per_chapter = Counter({chapter: 5 for chapter in CHAPTERS})
    for category in ("fixed_ok_sample", "seeded_random_ok_sample"):
        require(
            Counter(
                row["chapter"] for row in register if row["category"] == category
            )
            == expected_per_chapter,
            f"{category} is not exactly five rows per chapter",
        )

    compiled_rows = [
        row
        for row in register
        if row["evidence_kind"] == "COMPILED_NAMED_WITNESS"
    ]
    witness_names = {
        name.strip()
        for row in compiled_rows
        for name in row["evidence_name"].split(";")
        if name.strip()
    }
    require(
        Counter(
            len(
                [
                    name
                    for name in row["evidence_name"].split(";")
                    if name.strip()
                ]
            )
            for row in compiled_rows
        )
        == Counter({1: 89, 2: 2}),
        "compiled witness endpoint-cell multiplicity drifted",
    )
    require(
        len(witness_names) == 93,
        "compiled witness evidence does not reference 93 distinct declarations",
    )
    missing_axioms = witness_names - set(axiom_evidence)
    require(
        not missing_axioms,
        f"compiled witnesses missing axiom evidence: {sorted(missing_axioms)}",
    )
    violations = {
        name: sorted(unexpected_axioms(axiom_evidence[name]))
        for name in witness_names & set(axiom_evidence)
        if unexpected_axioms(axiom_evidence[name])
    }
    require(not violations, f"compiled witnesses have disallowed axioms: {violations}")
    require(
        all(
            row["axiom_status"] == "PASS_ALLOWED_STANDARD_SET"
            for row in register
        ),
        "a positive Tier-C evidence row lacks PASS_ALLOWED_STANDARD_SET",
    )

    sample = read_tsv(REVIEW / "recert_v6_tier_c_seeded_sample.tsv")
    require(len(sample) == 50, f"seeded sample has {len(sample)} rows, not 50")
    require(has_unique_row_ids(sample), "seeded sample row IDs are not unique")
    require(
        Counter(row["chapter"] for row in sample) == expected_per_chapter,
        "seeded sample is not exactly five rows per chapter",
    )
    for chapter in CHAPTERS:
        ranks = {
            int(row["sample_rank"]) for row in sample if row["chapter"] == chapter
        }
        require(ranks == set(range(1, 6)), f"{chapter}: sample ranks are not 1--5")
    seeded_register_ids = {
        row["source_row_id"]
        for row in register
        if row["category"] == "seeded_random_ok_sample"
    }
    require(
        seeded_register_ids == {row["row_id"] for row in sample},
        "Tier-C seeded register IDs differ from the selected sample",
    )

    population = read_tsv(REVIEW / "recert_v6_tier_c_seeded_population.tsv")
    frame = read_tsv(REVIEW / "recert_v6_tier_c_seeded_frame.tsv")
    require(len(population) == 780, "seeded population is not 780 chapter-row units")
    require(len(frame) == 576, "canonical seeded frame is not 576 rows")
    require(
        Counter(row["sampling_status"] for row in population)
        == Counter(
            {
                "LEGACY_FIXED_CONTROL_ROW": 50,
                "EXCLUDED_FIXED_ENDPOINT_ONLY": 74,
                "EXCLUDED_DUPLICATE_ENDPOINT_CELL": 80,
                "ELIGIBLE_CANONICAL_FRAME_ROW": 576,
            }
        ),
        "seeded population exclusion census drifted",
    )
    for chapter, expected in EXPECTED_FRAME.items():
        pop = [row for row in population if row["chapter"] == chapter]
        frm = [row for row in frame if row["chapter"] == chapter]
        observed = (
            len(pop),
            sum(row["sampling_status"] == "LEGACY_FIXED_CONTROL_ROW" for row in pop),
            sum(row["sampling_status"] == "EXCLUDED_FIXED_ENDPOINT_ONLY" for row in pop),
            sum(
                row["sampling_status"] == "EXCLUDED_DUPLICATE_ENDPOINT_CELL"
                for row in pop
            ),
            len(frm),
            sum(row["selected"] == "YES" for row in frm),
        )
        require(observed == expected, f"{chapter}: frame census {observed} != {expected}")

    tier_a_json_path = LOGS / "recert_v6_tier_a_final.json"
    tier_a_review_path = REVIEW / "recert_v6_tier_a_full_review.tsv"
    v4_types_path = LOGS / "recert_axiom_declaration_types.tsv"
    v4_binders_path = LOGS / "recert_axiom_declaration_binders.tsv"
    try:
        tier_a = json.loads(tier_a_json_path.read_text(encoding="utf-8"))
        tier_a_summary = tier_a["summary"]
        v4_metadata = tier_a_summary["v4_metadata"]
    except (OSError, ValueError, KeyError, TypeError) as error:
        errors.append(f"fresh Tier-A JSON is missing or malformed: {error}")
        tier_a_summary = {}
        v4_metadata = {}
    require(
        {
            "scanned_file_count": tier_a_summary.get("scanned_file_count"),
            "declaration_count": tier_a_summary.get("declaration_count"),
            "parsed_declaration_count": tier_a_summary.get(
                "parsed_declaration_count"
            ),
            "unparsed_declaration_count": tier_a_summary.get(
                "unparsed_declaration_count"
            ),
            "flagged_declaration_count": tier_a_summary.get(
                "flagged_declaration_count"
            ),
            "v4_join_contract": tier_a_summary.get("v4_join_contract"),
        }
        == {
            "scanned_file_count": 222,
            "declaration_count": 7411,
            "parsed_declaration_count": 7411,
            "unparsed_declaration_count": 0,
            "flagged_declaration_count": 13,
            "v4_join_contract": "PASS",
        },
        "fresh Tier-A census is not 222 files / 7,411 declarations / 13 hits",
    )
    require(
        tier_a_summary.get("reason_counts")
        == {
            "contradictory_numeric_bounds": 2,
            "fin_zero_domain": 2,
            "is_empty_domain": 2,
            "near_degenerate_numeric_bounds": 4,
            "zero_fintype_card": 3,
        },
        "fresh Tier-A reason census drifted",
    )
    require(
        {
            "unique_type_match_count": v4_metadata.get("unique_type_match_count"),
            "complete_binder_telescope_count": v4_metadata.get(
                "complete_binder_telescope_count"
            ),
            "unmatched_type_count": v4_metadata.get("unmatched_type_count"),
            "ambiguous_type_match_count": v4_metadata.get(
                "ambiguous_type_match_count"
            ),
            "auto_bound_candidate_count": v4_metadata.get(
                "auto_bound_candidate_count"
            ),
        }
        == {
            "unique_type_match_count": 7411,
            "complete_binder_telescope_count": 7411,
            "unmatched_type_count": 0,
            "ambiguous_type_match_count": 0,
            "auto_bound_candidate_count": 0,
        },
        "fresh Tier-A V4 telescope join census drifted",
    )
    try:
        tier_a_review = read_tsv(tier_a_review_path)
    except OSError as error:
        errors.append(f"fresh Tier-A review is absent: {error}")
        tier_a_review = []
    require(len(tier_a_review) == 13, "Tier-A full review does not have 13 rows")
    require(
        Counter(row.get("semantic_verdict") for row in tier_a_review)
        == Counter({"OK_FALSE_POSITIVE": 13}),
        "Tier-A full review verdict census drifted",
    )
    require(
        {
            row.get("qualified_name")
            for row in tier_a_review
            if row.get("tier_c_required") == "YES"
        }
        == EXPECTED_TIER_A_ESCALATIONS,
        "Tier-A escalation set drifted",
    )
    for evidence_path in (v4_types_path, v4_binders_path):
        require(evidence_path.is_file(), f"missing fresh V4 artifact: {evidence_path.name}")
        if evidence_path.is_file() and tier_a_json_path.is_file():
            require(
                tier_a_json_path.stat().st_mtime_ns >= evidence_path.stat().st_mtime_ns,
                f"Tier-A JSON predates fresh V4 artifact: {evidence_path.name}",
            )
    if tier_a_json_path.is_file() and tier_a_review_path.is_file():
        require(
            tier_a_review_path.stat().st_mtime_ns
            >= tier_a_json_path.stat().st_mtime_ns,
            "Tier-A full review predates the fresh Tier-A JSON",
        )
    tier_a_logs = {
        "recert_v6_tier_a_calibration.log": None,
        "recert_v6_tier_a_final_scan.log": tier_a_json_path,
        "recert_v6_tier_a_review_check.log": tier_a_review_path,
    }
    for relative, generated_artifact in tier_a_logs.items():
        log_path = LOGS / relative
        require(log_path.is_file(), f"missing Tier-A evidence log: {relative}")
        if not log_path.is_file():
            continue
        log_text = log_path.read_text(encoding="utf-8")
        require(
            re.search(r"(?m)^exit_code: 0\s*$", log_text) is not None,
            f"{relative}: missing exit_code: 0",
        )
        if generated_artifact is not None and generated_artifact.is_file():
            require(
                log_path.stat().st_mtime_ns
                >= generated_artifact.stat().st_mtime_ns,
                f"{relative}: predates its generated Tier-A artifact",
            )
    calibration_text = (
        LOGS / "recert_v6_tier_a_calibration.log"
    ).read_text(encoding="utf-8")
    require(
        "Ran 17 tests" in calibration_text,
        "Tier-A calibration log does not record all 17 tests",
    )

    sample_summary = (
        REVIEW / "recert_v6_tier_c_seeded_sample_summary.txt"
    ).read_text(encoding="utf-8")
    for line in (
        "verdict: PASS",
        f"seed: {SEED}",
        f"current_source_manifest: {current_source_digest}",
        "seed_currentness_evidence: HighDimensionalProbability/Verification/logs/round10_docstring_delta.log;HighDimensionalProbability/Verification/logs/exercise_reorganization_delta.log",
        "sampling_mode: without replacement",
        "legacy_fixed_controls_retained: 50",
        "new_seeded_controls: 50",
        "new_seeded_controls_per_chapter: 5",
        "sampling_command: python3 -B HighDimensionalProbability/Verification/scripts/build_v6_tier_c_seeded_sample.py --write",
        "algorithm: for each canonical row r in chapter c, rank ascending by SHA256(UTF8(seed + NUL + c + NUL + r.row_id)); take first 5",
    ):
        require(line in sample_summary, f"seeded sampling summary lacks: {line}")

    summary = (REVIEW / "recert_v6_tier_c_summary.txt").read_text(
        encoding="utf-8"
    )
    for line in (
        "verdict_under_R6: PASS",
        "rows: 103",
        "legacy_fixed_ok_sample_rows: 50",
        "manifest_seeded_random_ok_sample_rows: 50",
        f"manifest_seed: {SEED}",
        f"current_source_manifest: {current_source_digest}",
        "sampling_seed_policy: post-removal semantic baseline retained across the independently verified Round 10 docstring-only and Exercise-reorganization deltas",
        "compiled_named_witness_rows: 91",
        "compiled_named_witness_declarations_referenced: 93",
        "exact_v4_direct_citation_rows: 12",
        "fail_closed_negative_search_rows: 0",
        "removed_conditional_interfaces_absent: true",
        "planted_bad_witness_rejected: true",
    ):
        require(line in summary, f"Tier-C summary lacks: {line}")

    for relative in POSITIVE_LOGS:
        path = LOGS / relative
        require(path.is_file(), f"missing V6 build/axiom log: {relative}")
        if path.is_file():
            text = path.read_text(encoding="utf-8")
            require(
                re.search(r"(?m)^exit_code: 0\s*$", text) is not None,
                f"{relative}: missing exit_code: 0",
            )
    v4_summary_path = LOGS / "recert_axiom_summary.txt"
    require(v4_summary_path.is_file(), "missing fresh V4 completion summary")
    freshness_paths = [
        REVIEW / "recert_v6_tier_c.tsv",
        REVIEW / "recert_v6_tier_c_summary.txt",
        LOGS / "recert_v6_tier_c_ch0_4_axioms.tsv",
        *(
            LOGS / relative
            for relative in POSITIVE_LOGS
            if relative != "recert_v6_tier_c_seeded_sample_build.log"
        ),
        LOGS / "recert_v6_tier_c_planted_bad.log",
    ]
    if v4_summary_path.is_file():
        for artifact in freshness_paths:
            require(artifact.is_file(), f"missing post-V4 Tier-C artifact: {artifact.name}")
            if artifact.is_file():
                require(
                    artifact.stat().st_mtime_ns
                    >= v4_summary_path.stat().st_mtime_ns,
                    f"Tier-C artifact predates fresh V4 completion: {artifact.name}",
                )
    for relative in (
        "recert_v6_tier_c_command.log",
        "recert_v6_tier_c_check.log",
    ):
        require(
            "PASS recert_v6_tier_c: 103 rows"
            in (LOGS / relative).read_text(encoding="utf-8"),
            f"{relative}: lacks the final 103-row PASS",
        )
    planted = (LOGS / "recert_v6_tier_c_planted_bad.log").read_text(
        encoding="utf-8"
    )
    require("declaration uses `sorry`" in planted, "planted bad log lacks sorry warning")
    require(
        "recertPlantedBadWitness\tsorryAx" in planted,
        "planted bad log lacks the sorryAx marker",
    )
    require(
        re.search(r"(?m)^exit_code: 0\s*$", planted) is not None,
        "planted bad Lean calibration did not elaborate",
    )

    tier_b_expected_counts = {
        "v6_tier_b_ch0_4.tsv": 318,
        "v6_tier_b_ch5_7.tsv": 193,
        "v6_tier_b_ch8_9.tsv": 177,
        "v6_tier_b_supplement_ch0_4.tsv": 24,
        "v6_tier_b_supplement_ch5_7.tsv": 14,
        "v6_tier_b_supplement_ch8_9.tsv": 53,
    }
    tier_b_by_file = {
        name: read_tsv(REVIEW / name) for name in tier_b_expected_counts
    }
    require(
        {name: len(rows) for name, rows in tier_b_by_file.items()}
        == tier_b_expected_counts,
        "Tier-B per-ledger row census drifted",
    )
    all_tier_b = [
        row for rows in tier_b_by_file.values() for row in rows
    ]
    require(len(all_tier_b) == 779, "Tier-B assignment is not exactly 779 rows")
    require(
        not REMOVED_CONDITIONAL_INTERFACES & tier_b_endpoint_names(all_tier_b),
        "a removed conditional endpoint remains in Tier B",
    )
    require(
        not [
            row for row in all_tier_b
            if (row.get("verdict") or row.get("status")) != "OK"
        ],
        "Tier B contains a non-OK row",
    )
    current_census = read_tsv(VERIFICATION / "inventory/review_census_835.tsv")
    frozen_census = read_tsv(VERIFICATION / "inventory/review_census_838.tsv")
    require(len(current_census) == 835, "current review census is not 835 rows")
    require(len(frozen_census) == 838, "frozen review census is not 838 rows")
    endpoint_rows = read_tsv(LOGS / "recert_v6_tier_b_endpoints.tsv")
    exclusion_rows = read_tsv(LOGS / "recert_v6_tier_b_endpoint_exclusions.tsv")
    require(
        len(endpoint_rows) == 519,
        "mandatory Tier-B union does not have 519 unique theorem endpoints",
    )
    require(
        len(exclusion_rows) == 124,
        "mandatory Tier-B union does not have 124 explicit exclusions",
    )
    endpoint_summary = (
        LOGS / "recert_v6_tier_b_endpoint_summary.txt"
    ).read_text(encoding="utf-8")
    for line in (
        "verdict: PASS",
        "mandatory_readme_rows: 611",
        "supplemental_census_rows: 91",
        "selected_union_rows: 702",
        "resolved_declaration_references: 744",
        "unique_project_theorem_endpoints: 519",
        "excluded_declaration_references: 124",
        "EXTERNAL_MATHLIB_ENDPOINT: 14",
        "PROJECT_NON_THEOREM_ENDPOINT: 110",
    ):
        require(line in endpoint_summary, f"Tier-B endpoint summary lacks: {line}")
    source_occurrences: dict[str, list[str]] = {}
    package = VERIFICATION.parent
    for source_path in package.rglob("*.lean"):
        if VERIFICATION in source_path.parents:
            continue
        code, diagnostics = recert.mask_lean_noncode(
            source_path.read_text(encoding="utf-8")
        )
        require(
            not diagnostics,
            "Lean lexical diagnostics while checking removed interfaces: "
            f"{source_path.relative_to(package.parent)}: {diagnostics}",
        )
        for qualified in removed_interfaces_in_code(code):
            source_occurrences.setdefault(qualified, []).append(
                source_path.relative_to(package.parent).as_posix()
            )
    require(
        not source_occurrences,
        "removed conditional interfaces remain in source code: "
        f"{source_occurrences}",
    )

    report = REPORT.read_text(encoding="utf-8")
    require(
        re.findall(r"(?m)^\*\*Verdict: ([A-Z-]+)\*\*$", report) == ["PASS"],
        "V6 report does not contain exactly one PASS verdict",
    )
    require(not re.findall(r"\bV6-F\d+\b", report), "V6 report contains a finding ID")
    for phrase in (
        "exactly 103 rows",
        "91 compiled named witnesses",
        "12 exact clean V4 direct-value",
        SEED,
        "0 SUSPECT",
        "removed conditional interfaces",
        "build_v6_tier_c_seeded_sample.py --write",
    ):
        require(phrase in report, f"V6 report lacks required disposition: {phrase}")
    require(
        not re.findall(
            r"(?i)\b(?:TBD|TO[_ -]?FILL|PENDING|FIXME)\b|\?\?\?", report
        ),
        "V6 report contains a drafting marker",
    )
    for destination in re.findall(r"\[[^\]]*\]\(([^)]+)\)", report):
        if re.match(r"^[a-z]+://", destination) or destination.startswith("#"):
            continue
        require(
            (VERIFICATION / destination.split("#", 1)[0]).exists(),
            f"broken V6 report link: {destination}",
        )

    if errors:
        print(f"FAIL V6 final static audit: {len(errors)} error(s)")
        for error in errors:
            print(f"- {error}")
        return 1

    print("PASS V6 final static audit")
    print("verdict: PASS")
    print("tier_c: 103 rows = 50 fixed + 50 seeded + 3 Tier-A")
    print(
        "evidence: 91 compiled-witness rows (93 declarations) "
        "+ 12 exact citations"
    )
    print(f"seed: {SEED}; five controls per Appetizer/Chapter 1--9")
    print("planted_bad: sorryAx detected and rejected")
    print("conditional_interfaces: removed; 0 SUSPECT rows")
    print("lean_or_lake_invocations: 0")
    return 0


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--self-test",
        action="store_true",
        help="run in-memory planted-negative calibrations",
    )
    arguments = parser.parse_args()
    sys.exit(self_test() if arguments.self_test else main())
