#!/usr/bin/env python3
"""Build and reject-vacuity audit for the V6 Tier-C Chapters 8--9 suite."""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import os
import re
import shlex
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Sequence

from lean_source_scanner import mask_lean_noncode
from v6_tier_a_scanner import (
    AUTO_BOUND_REASON_ID,
    validate_v4_join_contract,
)


ROOT = Path(__file__).resolve().parents[3]
RUNNER_REL = Path(__file__).resolve().relative_to(ROOT)
WITNESS_REL = Path(
    "HighDimensionalProbability/Verification/scripts/witnesses/"
    "V6TierCCh8_9.lean"
)
LEDGER_REL = Path(
    "HighDimensionalProbability/Verification/review/v6_tier_b_ch8_9.tsv"
)
SUPPLEMENT_REL = Path(
    "HighDimensionalProbability/Verification/review/"
    "v6_tier_b_supplement_ch8_9.tsv"
)
TIER_A_REVIEW_REL = Path(
    "HighDimensionalProbability/Verification/review/"
    "v6_tier_c_ch8_9_tier_a_review.tsv"
)
FULL_TIER_A_REVIEW_REL = Path(
    "HighDimensionalProbability/Verification/review/"
    "v6_tier_a_full_review.tsv"
)
AXIOM_HARNESS_REL = Path(
    "HighDimensionalProbability/Verification/scripts/witnesses/"
    "V6TierCCh8_9Axioms.lean"
)
PLANTED_BAD_REL = Path(".audit_work/verification/V6TierCPlantedBad.lean")
LOG_DIR_REL = Path("HighDimensionalProbability/Verification/logs")
SCAN_JSON_REL = LOG_DIR_REL / "v6_tier_c_ch8_9_tier_a_scan.json"
RESULT_JSON_REL = LOG_DIR_REL / "v6_tier_c_ch8_9_results.json"
SUMMARY_REL = LOG_DIR_REL / "v6_tier_c_ch8_9_summary.txt"
V4_TYPES_REL = LOG_DIR_REL / "recert_axiom_declaration_types.tsv"
V4_BINDERS_REL = LOG_DIR_REL / "recert_axiom_declaration_binders.tsv"
V4_DIRECT_DEPENDENCIES_REL = (
    LOG_DIR_REL / "recert_axiom_direct_dependencies.tsv"
)
V4_SUMMARY_REL = LOG_DIR_REL / "recert_axiom_summary.txt"
EXPECTED_TIER_A_DECLARATION_COUNT = 7_411
EXPECTED_V4_AUDITED_DECLARATION_COUNT = 15_022

LEAN_OPTIONS = (
    "-Dpp.unicode.fun=true",
    "-DrelaxedAutoImplicit=false",
    "-Dweak.linter.mathlibStandardSet=true",
    "-DmaxSynthPendingDepth=3",
)

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN_PROOF_TOKEN = re.compile(r"\b(?:sorry|admit)\b")
FORBIDDEN_COMMAND = re.compile(
    r"(?m)^[ \t]*(?:axiom|unsafe)[ \t]+"
)
DECLARATION = re.compile(
    r"(?m)^[ \t]*(?:theorem|alias)[ \t]+([A-Za-z_][A-Za-z0-9_']*)"
)
FORBIDDEN_IMPORT = "MatrixConcentration.Appendix_RosenthalPinelis"


@dataclass(frozen=True)
class QueueSpec:
    chapter: str
    rank: int
    row_id: str
    endpoint: str
    mode: str
    citation_candidate: str
    witness: str


QUEUE_SPECS = (
    QueueSpec(
        "Chapter 8",
        1,
        "census-9868b5ae3cf371d8",
        "HDP.Chapter8.exercise_8_4a_weightedBasis_actualGaussianWidth",
        "fresh",
        "",
        "HDP.Verification.V6TierC.queue_ch8_weightedBasis_actualWidth_dimension_two",
    ),
    QueueSpec(
        "Chapter 8",
        2,
        "census-846343e6e45de2c0",
        "HDP.gamma2_le_chainCost",
        "citation",
        "HDP.Chapter8.gamma2_ofReal_ne_top",
        "HDP.Verification.V6TierC.queue_ch8_gamma2_finiteness_downstream",
    ),
    QueueSpec(
        "Chapter 8",
        3,
        "census-0bd7be9049383381",
        "HDP.Chapter8.remark_8_2_2_dimension_free_monteCarlo",
        "fresh",
        "",
        "HDP.Verification.V6TierC.queue_ch8_dimensionFreeMonteCarlo_two_sample_model",
    ),
    QueueSpec(
        "Chapter 8",
        4,
        "census-a60e5325864e45e1",
        "HDP.Chapter8.empiricalRisk",
        "citation",
        "HDP.Chapter8.exists_empiricalRiskMinimizer",
        "HDP.Verification.V6TierC.queue_ch8_empiricalRisk_minimizer_downstream",
    ),
    QueueSpec(
        "Chapter 8",
        5,
        "census-c585c977c1a8c5e1",
        "HDP.Chapter8.lemma_8_3_7_pajor",
        "citation",
        "HDP.Chapter8.lemma_8_3_9_zero_vc",
        "HDP.Verification.V6TierC.queue_ch8_pajor_zero_vc_downstream",
    ),
    QueueSpec(
        "Chapter 9",
        1,
        "census-3076196060b076ae",
        "HDP.Chapter9.theorem_9_1_2_subGaussianIncrements",
        "citation",
        "HDP.Chapter9.theorem_9_1_1_matrixDeviation",
        "HDP.Verification.V6TierC.queue_ch9_subGaussianIncrements_matrixDeviation_downstream",
    ),
    QueueSpec(
        "Chapter 9",
        2,
        "census-3431787859863524",
        "HDP.Chapter9.SublinearFunctional.lipschitzWith_of_growth",
        "citation",
        "HDP.Chapter9.theorem_9_6_4_subgaussianIncrements",
        "HDP.Verification.V6TierC.queue_ch9_sublinear_lipschitz_subgaussian_downstream",
    ),
    QueueSpec(
        "Chapter 9",
        3,
        "census-d7012787ce2e3507",
        "HDP.Chapter7.gaussianComplexity_difference",
        "citation",
        "HDP.Chapter9.randomMatrixImageDiameter_expectation",
        "HDP.Verification.V6TierC.queue_ch9_gaussianComplexity_projectionDiameter_downstream",
    ),
    QueueSpec(
        "Chapter 9",
        4,
        "census-99f751a84d306ec2",
        "HDP.Chapter9.euclideanSetGaussianWidth_approximatelySparseUnitSet_le",
        "citation",
        "HDP.Chapter9.remark_9_5_4_improvedExactRecoveryWidth",
        "HDP.Verification.V6TierC.queue_ch9_approximatelySparseWidth_remark_downstream",
    ),
    QueueSpec(
        "Chapter 9",
        5,
        "census-8d9f7d9eeb12f014",
        "HDP.Chapter9.theorem_9_1_2_subGaussianIncrements",
        "citation",
        "HDP.Chapter9.exercise_9_3_quadraticMatrixDeviation",
        "HDP.Verification.V6TierC.queue_ch9_subGaussianIncrements_quadraticDeviation_downstream",
    ),
)

FACTOR_WITNESS = (
    "HDP.Verification.V6TierC."
    "equation_8_46_exists_chainCost_le_two_mul_gamma2"
)
GRADIENT_WITNESSES = (
    "HDP.Verification.V6TierC."
    "tierA_gradient_term_fin1_indicator_nonzero",
    "HDP.Verification.V6TierC."
    "tierA_gradient_term_symmetric_fin1_indicator_instance",
)
LEGACY_SEEDED_WITNESSES = tuple(
    "HDP.Verification.V6TierC." + name
    for name in (
        "seeded_ch8_discrepancy_fin1_two_ranges",
        "seeded_ch8_talagrandComparison_canonical_fin2",
        "seeded_ch8_example_8_3_8_full_family",
        "seeded_ch8_growthFunction_binary_strings",
        "seeded_ch9_sparseRecovery_conditional",
        "seeded_ch9_twoSidedChevet_two_point_sets",
        "seeded_ch9_innerSublinearFunctional_real",
    )
)
CURRENT_SEEDED_WITNESSES = (
    "HDP.Verification.V6TierC.seeded_current_ch8_dudley_supremum_of_increments",
    "HDP.Verification.V6TierC.seeded_current_ch9_exercise_9_29_part_b",
)
WITNESS_NAMES = LEGACY_SEEDED_WITNESSES + tuple(
    spec.witness for spec in QUEUE_SPECS[:5]
) + (
    FACTOR_WITNESS,
) + GRADIENT_WITNESSES + tuple(spec.witness for spec in QUEUE_SPECS[5:])
WITNESS_NAMES += CURRENT_SEEDED_WITNESSES

EXPECTED_TIER_A_HITS = {
    (
        "HighDimensionalProbability/Chapter8_Chaining.lean",
        "optimalDyadicScaleRadius_eq_zero_of_coverCard_one",
        ("zero_fintype_card",),
    ),
    (
        "HighDimensionalProbability/Chapter8_Chaining.lean",
        "empiricalAverage_zero",
        ("fin_zero_domain",),
    ),
    (
        "HighDimensionalProbability/Exercise/Chapter9/Sec03.lean",
        "exercise_9_14_part_b",
        ("near_degenerate_numeric_bounds",),
    ),
    (
        "HighDimensionalProbability/Chapter9_DeviationsOfRandomMatricesOnSets.lean",
        "exercise_9_11_additive_error_is_necessary_zeroDim_compat",
        ("fin_zero_domain",),
    ),
}

REMOVED_CONDITIONAL_ENDPOINTS = {
    "HDP.Chapter8.exercise_8_39a_gaussian_chevet_arbitrary",
    "HDP.Chapter8.remark_8_6_3_gaussian_chevet_arbitrary",
}


@dataclass(frozen=True)
class CommandResult:
    command: tuple[str, ...]
    returncode: int
    output: str


class AuditFailure(RuntimeError):
    pass


def project_path(relative: Path) -> Path:
    return ROOT / relative


def sha256_file(relative: Path) -> str:
    digest = hashlib.sha256()
    with project_path(relative).open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def write_text(relative: Path, text: str) -> None:
    path = project_path(relative)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def run_logged(command: Sequence[str], log_relative: Path) -> CommandResult:
    environment = os.environ.copy()
    environment["PYTHONDONTWRITEBYTECODE"] = "1"
    completed = subprocess.run(
        list(command),
        cwd=ROOT,
        env=environment,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    output = completed.stdout
    log = "\n".join(
        [
            f"cwd: {ROOT}",
            f"command: {shlex.join(command)}",
            "",
            output.rstrip("\n"),
            "",
            f"exit_code: {completed.returncode}",
            "",
        ]
    )
    write_text(log_relative, log)
    return CommandResult(tuple(command), completed.returncode, output)


def masked_source(relative: Path) -> str:
    text = project_path(relative).read_text(encoding="utf-8")
    masked, diagnostics = mask_lean_noncode(text)
    if diagnostics:
        raise AuditFailure(f"{relative}: Lean lexical diagnostics: {diagnostics!r}")
    return masked


def forbidden_tokens(relative: Path) -> list[str]:
    return FORBIDDEN_PROOF_TOKEN.findall(masked_source(relative))


def check_queue() -> dict[str, object]:
    with project_path(LEDGER_REL).open(encoding="utf-8", newline="") as handle:
        rows = list(csv.DictReader(handle, delimiter="\t"))
    queue = [
        row
        for row in rows
        if row["row_set"] == "ok_review_queue_head"
        and row["sample_kind"] == "ok_review_queue_head"
    ]
    if len(queue) != len(QUEUE_SPECS):
        raise AuditFailure(
            f"expected {len(QUEUE_SPECS)} queue rows, found {len(queue)}"
        )
    observed: list[dict[str, object]] = []
    for spec in QUEUE_SPECS:
        matches = [
            row
            for row in queue
            if row["chapter"] == spec.chapter
            and int(row["sample_rank"]) == spec.rank
        ]
        if len(matches) != 1:
            raise AuditFailure(
                f"{spec.chapter} rank {spec.rank}: expected one queue row"
            )
        row = matches[0]
        actual = (row["row_id"], row["resolved_declarations"])
        expected = (spec.row_id, spec.endpoint)
        if actual != expected:
            raise AuditFailure(
                f"{spec.chapter} rank {spec.rank}: expected {expected!r}, "
                f"found {actual!r}"
            )
        if row["verdict"] != "OK" or not row["tier_c_required"].startswith(
            "YES"
        ):
            raise AuditFailure(
                f"{spec.chapter} rank {spec.rank}: row is not OK/Tier-C"
            )
        observed.append(
            {
                "chapter": spec.chapter,
                "rank": spec.rank,
                "row_id": spec.row_id,
                "endpoint": spec.endpoint,
                "mode": spec.mode,
                "citation_candidate": spec.citation_candidate,
                "witness": spec.witness,
            }
        )
    for chapter in ("Chapter 8", "Chapter 9"):
        ranks = [item["rank"] for item in observed if item["chapter"] == chapter]
        if ranks != [1, 2, 3, 4, 5]:
            raise AuditFailure(f"{chapter}: queue ranks are not exactly 1--5")
    citation_count = sum(spec.mode == "citation" for spec in QUEUE_SPECS)
    fresh_count = sum(spec.mode == "fresh" for spec in QUEUE_SPECS)
    if (citation_count, fresh_count) != (8, 2):
        raise AuditFailure(
            "strict witness split changed: expected citation=8, fresh=2"
        )
    return {
        "row_count": len(observed),
        "citation_rows": citation_count,
        "fresh_model_rows": fresh_count,
        "rows": observed,
    }


def check_removed_conditional_interfaces() -> dict[str, object]:
    with project_path(SUPPLEMENT_REL).open(
        encoding="utf-8", newline=""
    ) as handle:
        rows = list(csv.DictReader(handle, delimiter="\t"))
    suspect = [row for row in rows if row["status"] == "SUSPECT"]
    if suspect:
        raise AuditFailure(
            "current Chapter 8--9 supplement retains SUSPECT rows: "
            f"{[row['endpoint'] for row in suspect]!r}"
        )
    present = REMOVED_CONDITIONAL_ENDPOINTS & {
        row["endpoint"] for row in rows
    }
    if present:
        raise AuditFailure(
            f"removed conditional endpoints remain in Tier B: {sorted(present)!r}"
        )
    return {
        "count": 0,
        "removed_endpoints": sorted(REMOVED_CONDITIONAL_ENDPOINTS),
        "verdict": "PASS_ABSENT",
    }


def check_gradient_review() -> dict[str, object]:
    with project_path(FULL_TIER_A_REVIEW_REL).open(
        encoding="utf-8", newline=""
    ) as handle:
        rows = list(csv.DictReader(handle, delimiter="\t"))
    matches = [
        row
        for row in rows
        if row["qualified_name"]
        == "BernoulliLSI.gradient_term_symmetric"
    ]
    if matches:
        raise AuditFailure(
            "the repaired gradient theorem must no longer be a Tier-A hit"
        )
    return {
        "endpoint": "BernoulliLSI.gradient_term_symmetric",
        "semantic_verdict": "REPAIRED_NONVACUOUS",
        "tier_c_required": False,
        "calibration_witnesses": list(GRADIENT_WITNESSES),
        "current_statement_rehabilitated": True,
    }


def check_witness_source() -> dict[str, object]:
    source = project_path(WITNESS_REL).read_text(encoding="utf-8")
    code = masked_source(WITNESS_REL)
    if FORBIDDEN_IMPORT in source:
        raise AuditFailure(f"{WITNESS_REL}: imports known-broken isolated path")
    if "set_option autoImplicit false" not in code:
        raise AuditFailure(f"{WITNESS_REL}: missing `set_option autoImplicit false`")
    tokens = FORBIDDEN_PROOF_TOKEN.findall(code)
    if tokens:
        raise AuditFailure(f"{WITNESS_REL}: forbidden proof tokens: {tokens!r}")
    if FORBIDDEN_COMMAND.search(code):
        raise AuditFailure(f"{WITNESS_REL}: contains an axiom/unsafe command")
    local_names = DECLARATION.findall(code)
    expected_local = [name.rsplit(".", 1)[1] for name in WITNESS_NAMES]
    if local_names != expected_local:
        raise AuditFailure(
            "witness declaration list mismatch:\n"
            f"expected={expected_local!r}\nobserved={local_names!r}"
        )
    for spec in QUEUE_SPECS:
        local = spec.witness.rsplit(".", 1)[1]
        if spec.mode == "citation":
            pattern = re.compile(
                rf"(?m)^[ \t]*alias[ \t]+{re.escape(local)}[ \t]*:=[ \t]*"
                rf"\s*{re.escape(spec.citation_candidate)}"
            )
            if not pattern.search(code):
                raise AuditFailure(
                    f"citation alias {local} does not name "
                    f"{spec.citation_candidate}"
                )
        elif spec.mode == "fresh":
            if not re.search(
                rf"(?m)^[ \t]*theorem[ \t]+{re.escape(local)}\b", code
            ):
                raise AuditFailure(f"fresh witness {local} is not a theorem")
            if code.count(spec.endpoint) < 1:
                raise AuditFailure(
                    f"fresh witness source does not apply {spec.endpoint}"
                )
        else:
            raise AuditFailure(
                f"{spec.chapter} rank {spec.rank}: unknown mode {spec.mode!r}"
            )
    return {
        "path": str(WITNESS_REL),
        "sha256": sha256_file(WITNESS_REL),
        "queue_declaration_count": len(QUEUE_SPECS),
        "citation_alias_count": sum(
            spec.mode == "citation" for spec in QUEUE_SPECS
        ),
        "fresh_model_theorem_count": sum(
            spec.mode == "fresh" for spec in QUEUE_SPECS
        ),
        "factor_two_theorem_count": 1,
        "gradient_calibration_theorem_count": len(GRADIENT_WITNESSES),
        "audited_declaration_count": len(local_names),
        "forbidden_proof_token_count": 0,
        "forbidden_command_count": 0,
        "autoImplicit_false": True,
        "known_broken_import": False,
    }


def check_citation_edges() -> dict[str, object]:
    path = project_path(V4_DIRECT_DEPENDENCIES_REL)
    summary_path = project_path(V4_SUMMARY_REL)
    if not path.is_file():
        raise AuditFailure("V4 direct-dependency TSV is absent")
    if not summary_path.is_file():
        raise AuditFailure(
            "V4 completion summary is absent; refusing to certify a live "
            "direct-dependency stream"
        )
    for artifact in (
        path,
        project_path(V4_TYPES_REL),
        project_path(V4_BINDERS_REL),
    ):
        if not artifact.is_file():
            raise AuditFailure(f"V4 artifact is absent: {artifact}")
        if summary_path.stat().st_mtime_ns < artifact.stat().st_mtime_ns:
            raise AuditFailure(
                "V4 completion summary predates an evidence artifact; "
                "refusing to certify a possibly live stream"
            )
    summary = summary_path.read_text(encoding="utf-8")
    required_summary_lines = {
        (
            "declarations_audited: "
            f"{EXPECTED_V4_AUDITED_DECLARATION_COUNT}"
        ),
        "type_telescope_dump: PASS",
        "direct_dependency_dump: PASS",
    }
    missing_summary_lines = sorted(
        line for line in required_summary_lines if line not in summary.splitlines()
    )
    if missing_summary_lines:
        raise AuditFailure(
            "V4 completion summary lacks required contracts: "
            f"{missing_summary_lines!r}"
        )
    with path.open(encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle, delimiter="\t")
        expected_header = (
            "source_module",
            "source",
            "source_kind",
            "origin",
            "target_module",
            "target",
        )
        if tuple(reader.fieldnames or ()) != expected_header:
            raise AuditFailure("V4 direct-dependency TSV header changed")
        value_edges = {
            (row["source"], row["target"])
            for row in reader
            if row["origin"] == "value"
        }
    expected = {
        (spec.citation_candidate, spec.endpoint)
        for spec in QUEUE_SPECS
        if spec.mode == "citation"
    }
    missing = sorted(expected - value_edges)
    if missing:
        rendered = "\n".join(
            f"  {source} -> {target}" for source, target in missing
        )
        raise AuditFailure(
            "V4 is missing required direct value dependency edges:\n"
            f"{rendered}"
        )
    return {
        "artifact": str(V4_DIRECT_DEPENDENCIES_REL),
        "completion_summary": str(V4_SUMMARY_REL),
        "required_edge_count": len(expected),
        "verified_edge_count": len(expected),
        "edges": [
            {"consumer": source, "endpoint": target}
            for source, target in sorted(expected)
        ],
    }


def is_ch8_9_source_path(path: str) -> bool:
    if not path.startswith("HighDimensionalProbability/"):
        return False
    if path.startswith("HighDimensionalProbability/Verification/"):
        return False
    return (
        path.startswith("HighDimensionalProbability/Chapter8_")
        or path.startswith("HighDimensionalProbability/Chapter8/")
        or path.startswith("HighDimensionalProbability/Chapter9_")
        or path.startswith("HighDimensionalProbability/Chapter9/")
        or path.startswith("HighDimensionalProbability/Exercise/Chapter8/")
        or path.startswith("HighDimensionalProbability/Exercise/Chapter9/")
    )


def read_tier_a_review() -> set[tuple[str, str, tuple[str, ...]]]:
    with project_path(TIER_A_REVIEW_REL).open(
        encoding="utf-8", newline=""
    ) as handle:
        reader = csv.DictReader(handle, delimiter="\t")
        expected_header = (
            "path",
            "name",
            "reason_ids",
            "tier_b_verdict",
            "requires_tier_c_witness",
            "review",
        )
        if tuple(reader.fieldnames or ()) != expected_header:
            raise AuditFailure("Tier-A manual-review TSV header changed")
        rows = list(reader)
    if any(
        row["tier_b_verdict"] != "OK_FALSE_POSITIVE"
        or row["requires_tier_c_witness"] != "no"
        or not row["review"].strip()
        for row in rows
    ):
        raise AuditFailure("Tier-A manual-review TSV has an incomplete verdict")
    return {
        (
            row["path"],
            row["name"],
            tuple(sorted(filter(None, row["reason_ids"].split(";")))),
        )
        for row in rows
    }


def fresh_tier_a_scan() -> dict[str, object]:
    command = [
        sys.executable,
        str(
            project_path(
                Path(
                    "HighDimensionalProbability/Verification/scripts/"
                    "scan_v6_vacuity_tier_a.py"
                )
            )
        ),
        "--scope",
        "library",
        "--v4-types-tsv",
        str(project_path(V4_TYPES_REL)),
        "--v4-binders-tsv",
        str(project_path(V4_BINDERS_REL)),
        "--format",
        "json",
        "--output",
        str(project_path(SCAN_JSON_REL)),
    ]
    result = run_logged(
        command, LOG_DIR_REL / "v6_tier_c_ch8_9_tier_a_scan.log"
    )
    if result.returncode != 0:
        raise AuditFailure(f"fresh Tier-A scan exited {result.returncode}")
    report = json.loads(project_path(SCAN_JSON_REL).read_text(encoding="utf-8"))
    try:
        v4_join = validate_v4_join_contract(
            report,
            expected_types_tsv=str(V4_TYPES_REL),
            expected_binders_tsv=str(V4_BINDERS_REL),
            expected_declaration_count=EXPECTED_TIER_A_DECLARATION_COUNT,
        )
    except ValueError as error:
        raise AuditFailure(f"Tier-A V4 join contract failed: {error}") from error
    relevant = {
        (
            declaration["path"],
            declaration["name"],
            tuple(
                sorted(
                    reason["reason_id"]
                    for reason in declaration["triage_reasons"]
                    if reason["reason_id"] != AUTO_BOUND_REASON_ID
                )
            ),
        )
        for declaration in report["declarations"]
        if is_ch8_9_source_path(declaration["path"])
        and any(
            reason["reason_id"] != AUTO_BOUND_REASON_ID
            for reason in declaration["triage_reasons"]
        )
    }
    chapter_auto_bound_count = sum(
        is_ch8_9_source_path(declaration["path"])
        and any(
            reason["reason_id"] == AUTO_BOUND_REASON_ID
            for reason in declaration["triage_reasons"]
        )
        for declaration in report["declarations"]
    )
    manual = read_tier_a_review()
    if relevant != EXPECTED_TIER_A_HITS or manual != relevant:
        raise AuditFailure(
            "fresh Chapter 8--9 Tier-A review set changed:\n"
            f"expected={sorted(EXPECTED_TIER_A_HITS)!r}\n"
            f"manual={sorted(manual)!r}\n"
            f"observed={sorted(relevant)!r}"
        )
    return {
        "summary": report["summary"],
        "v4_join": v4_join,
        "chapter_8_9_auto_bound_flagged_declarations": (
            chapter_auto_bound_count
        ),
        "chapter_8_9_hits": [
            {"path": path, "name": name, "reason_ids": list(reasons)}
            for path, name, reasons in sorted(relevant)
        ],
        "semantic_verdict_counts": {
            "OK_FALSE_POSITIVE": len(relevant),
            "SUSPECT": 0,
            "VACUOUS": 0,
        },
        "additional_tier_c_witnesses_required": 0,
    }


def parse_axiom_markers(output: str) -> dict[str, set[str]]:
    rows: dict[str, set[str]] = {}
    for line in output.splitlines():
        fields = line.split("\t")
        if not fields or fields[0] != "V6_TIER_C_AXIOM":
            continue
        if len(fields) != 3:
            raise AuditFailure(f"malformed axiom marker: {line!r}")
        name = fields[1]
        if name in rows:
            raise AuditFailure(f"duplicate axiom marker for {name}")
        rows[name] = {item for item in fields[2].split(";") if item}
    return rows


def build_witness_module() -> dict[str, object]:
    module = (
        "HighDimensionalProbability.Verification.scripts.witnesses."
        "V6TierCCh8_9"
    )
    result = run_logged(
        ["lake", "build", module],
        LOG_DIR_REL / "v6_tier_c_ch8_9_build.log",
    )
    if result.returncode != 0:
        raise AuditFailure(f"witness build exited {result.returncode}")
    return {
        "module": module,
        "exit_code": result.returncode,
        "project_lean_options": list(LEAN_OPTIONS),
    }


def audit_axioms() -> dict[str, list[str]]:
    result = run_logged(
        [
            "lake",
            "env",
            "lean",
            *LEAN_OPTIONS,
            str(project_path(AXIOM_HARNESS_REL)),
        ],
        LOG_DIR_REL / "v6_tier_c_ch8_9_axioms.log",
    )
    if result.returncode != 0:
        raise AuditFailure(f"axiom harness exited {result.returncode}")
    rows = parse_axiom_markers(result.output)
    if set(rows) != set(WITNESS_NAMES):
        raise AuditFailure(
            "axiom marker declaration set mismatch:\n"
            f"missing={sorted(set(WITNESS_NAMES) - set(rows))!r}\n"
            f"extra={sorted(set(rows) - set(WITNESS_NAMES))!r}"
        )
    violations = {
        name: sorted(axioms - ALLOWED_AXIOMS)
        for name, axioms in rows.items()
        if axioms - ALLOWED_AXIOMS
    }
    if violations:
        raise AuditFailure(f"disallowed witness axioms: {violations!r}")
    return {name: sorted(rows[name]) for name in WITNESS_NAMES}


def calibrate_planted_bad() -> dict[str, object]:
    source_tokens = forbidden_tokens(PLANTED_BAD_REL)
    static_rejected = bool(source_tokens)
    result = run_logged(
        [
            "lake",
            "env",
            "lean",
            *LEAN_OPTIONS,
            str(project_path(PLANTED_BAD_REL)),
        ],
        LOG_DIR_REL / "v6_tier_c_ch8_9_planted_bad.log",
    )
    rows = parse_axiom_markers(result.output)
    bad_name = "HDP.Verification.V6TierC.plantedBadWitness"
    bad_axioms = rows.get(bad_name, set())
    axiom_rejected = bool(bad_axioms - ALLOWED_AXIOMS)
    if result.returncode != 0:
        raise AuditFailure(
            f"planted-bad Lean calibration unexpectedly exited {result.returncode}"
        )
    if not static_rejected:
        raise AuditFailure("planted bad witness escaped the lexical checker")
    if "sorryAx" not in bad_axioms or not axiom_rejected:
        raise AuditFailure(
            f"planted bad witness escaped axiom checker: {sorted(bad_axioms)!r}"
        )
    return {
        "shared_path": str(PLANTED_BAD_REL),
        "source_tokens": source_tokens,
        "static_rejected": static_rejected,
        "axioms": sorted(bad_axioms),
        "axiom_rejected": axiom_rejected,
        "checker_verdict": "REJECT",
    }


def render_summary(report: dict[str, object]) -> str:
    lines = [
        "V6 Tier-C Chapters 8--9 witness checker",
        f"overall: {report['overall']}",
        f"queue_rows: {report['queue']['row_count']} "
        "(Chapter 8=5, Chapter 9=5)",
        "queue_witnesses: "
        f"{report['source']['queue_declaration_count']} "
        f"(citation={report['source']['citation_alias_count']}, "
        f"fresh_models={report['source']['fresh_model_theorem_count']})",
        "v4_direct_value_edges: "
        f"{report['citations']['verified_edge_count']}/"
        f"{report['citations']['required_edge_count']} VERIFIED",
        f"factor_two_witnesses: {report['source']['factor_two_theorem_count']}",
        "gradient_calibration_witnesses: "
        f"{report['source']['gradient_calibration_theorem_count']}",
        "gradient_endpoint_semantic_verdict: "
        f"{report['gradient_review']['semantic_verdict']}",
        "gradient_current_statement_rehabilitated: "
        f"{str(report['gradient_review']['current_statement_rehabilitated']).lower()}",
        "source_sorry_admit: 0",
        "fresh_tier_a_hits: "
        f"{len(report['tier_a']['chapter_8_9_hits'])}",
        "fresh_tier_a_semantic_verdicts: "
        f"{report['tier_a']['semantic_verdict_counts']}",
        "v4_join_complete_binder_telescopes: "
        f"{report['tier_a']['v4_join']['complete_binder_telescopes']}",
        "v4_auto_bound_flagged_declarations: "
        f"{report['tier_a']['v4_join']['auto_bound_flagged_declaration_count']}",
        "v4_auto_bound_ch8_9_flagged_declarations: "
        f"{report['tier_a']['chapter_8_9_auto_bound_flagged_declarations']}",
        "additional_tier_c_witnesses_for_tier_a: 0",
        "removed_arbitrary_gaussian_chevet_wrappers: "
        f"{report['conditional_interfaces']['count']} current rows",
    ]
    if "build" in report:
        lines.extend(
            [
                "witness_build: PASS",
                f"axiom_audited_witnesses: {len(report['axioms'])}",
                "allowed_axioms: Classical.choice, Quot.sound, propext",
                "planted_bad_static: REJECT",
                "planted_bad_axioms: REJECT (sorryAx)",
            ]
        )
    return "\n".join(lines) + "\n"


def run(*, static_only: bool) -> dict[str, object]:
    report: dict[str, object] = {
        "profile": "V6-Tier-C-Ch8-9",
        "queue": check_queue(),
        "source": check_witness_source(),
        "citations": check_citation_edges(),
        "tier_a": fresh_tier_a_scan(),
        "gradient_review": check_gradient_review(),
        "conditional_interfaces": check_removed_conditional_interfaces(),
    }
    if not static_only:
        report["build"] = build_witness_module()
        report["axioms"] = audit_axioms()
        report["planted_bad"] = calibrate_planted_bad()
    provenance_paths = [
        RUNNER_REL,
        WITNESS_REL,
        LEDGER_REL,
        SUPPLEMENT_REL,
        TIER_A_REVIEW_REL,
        FULL_TIER_A_REVIEW_REL,
        AXIOM_HARNESS_REL,
        PLANTED_BAD_REL,
        V4_TYPES_REL,
        V4_BINDERS_REL,
        V4_DIRECT_DEPENDENCIES_REL,
        V4_SUMMARY_REL,
    ]
    if not static_only:
        provenance_paths.extend(
            [
                LOG_DIR_REL / "v6_tier_c_ch8_9_build.log",
                LOG_DIR_REL / "v6_tier_c_ch8_9_axioms.log",
                LOG_DIR_REL / "v6_tier_c_ch8_9_planted_bad.log",
            ]
        )
    report["provenance"] = {
        "mode": "static" if static_only else "full",
        "sha256": {
            str(path): sha256_file(path) for path in provenance_paths
        },
    }
    report["overall"] = "PASS"
    return report


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--static-only",
        action="store_true",
        help="check ledgers/source/fresh Tier-A scan without invoking Lean",
    )
    args = parser.parse_args(argv)
    try:
        report = run(static_only=args.static_only)
    except AuditFailure as error:
        failure = {
            "profile": "V6-Tier-C-Ch8-9",
            "overall": "FAIL",
            "error": str(error),
        }
        write_text(RESULT_JSON_REL, json.dumps(failure, indent=2) + "\n")
        text = (
            "V6 Tier-C Chapters 8--9 witness checker\n"
            f"overall: FAIL\nerror: {error}\n"
        )
        write_text(SUMMARY_REL, text)
        write_text(LOG_DIR_REL / "v6_tier_c_ch8_9_runner.log", text)
        print(f"FAIL: {error}", file=sys.stderr)
        return 1
    write_text(RESULT_JSON_REL, json.dumps(report, indent=2) + "\n")
    summary = render_summary(report)
    write_text(SUMMARY_REL, summary)
    write_text(LOG_DIR_REL / "v6_tier_c_ch8_9_runner.log", summary)
    print(summary, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
