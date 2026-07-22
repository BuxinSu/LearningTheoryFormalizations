#!/usr/bin/env python3
"""Build and reject-vacuity audit for the V6 Tier-C Chapters 5--7 suite."""

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
WITNESS_REL = Path(
    "HighDimensionalProbability/Verification/scripts/witnesses/"
    "V6TierCCh5_7.lean"
)
LEDGER_REL = Path(
    "HighDimensionalProbability/Verification/review/v6_tier_b_ch5_7.tsv"
)
SAMPLING_PLAN_REL = Path(
    "HighDimensionalProbability/Verification/inventory/sampling_plan.json"
)
INVENTORY_SUMMARY_REL = Path(
    "HighDimensionalProbability/Verification/inventory/inventory_summary.json"
)
AXIOM_HARNESS_REL = Path(
    "HighDimensionalProbability/Verification/scripts/witnesses/"
    "V6TierCCh5_7Axioms.lean"
)
PLANTED_BAD_REL = Path(
    ".audit_work/verification/V6TierCPlantedBad.lean"
)
LOG_DIR_REL = Path("HighDimensionalProbability/Verification/logs")
SCAN_JSON_REL = LOG_DIR_REL / "v6_tier_c_ch5_7_tier_a_scan.json"
RESULT_JSON_REL = LOG_DIR_REL / "v6_tier_c_ch5_7_results.json"
BUILD_LOG_REL = LOG_DIR_REL / "v6_tier_c_ch5_7_build.log"
AXIOM_LOG_REL = LOG_DIR_REL / "v6_tier_c_ch5_7_axioms.log"
PLANTED_BAD_LOG_REL = LOG_DIR_REL / "v6_tier_c_ch5_7_planted_bad.log"
RUNNER_LOG_REL = LOG_DIR_REL / "v6_tier_c_ch5_7_runner.log"
WITNESS_OLEAN_REL = Path(
    ".lake/build/lib/lean/HighDimensionalProbability/Verification/"
    "scripts/witnesses/V6TierCCh5_7.olean"
)
V4_TYPES_REL = LOG_DIR_REL / "recert_axiom_declaration_types.tsv"
V4_BINDERS_REL = LOG_DIR_REL / "recert_axiom_declaration_binders.tsv"
V4_AXIOMS_REL = LOG_DIR_REL / "recert_axiom_audit.tsv"
V4_DEPENDENCIES_REL = LOG_DIR_REL / "recert_axiom_direct_dependencies.tsv"
EXPECTED_TIER_A_DECLARATION_COUNT = 7_411

LEAN_OPTIONS = (
    "-Dpp.unicode.fun=true",
    "-DrelaxedAutoImplicit=false",
    "-Dweak.linter.mathlibStandardSet=true",
    "-DmaxSynthPendingDepth=3",
)

QUEUE_IDS = {
    "Chapter 5": (
        "census-4873958abc52b612",
        "census-9a8303edb533db45",
        "census-28ee26691f687a9c",
        "census-a42f06353bdaf063",
        "census-636ecf0b5c2c32b0",
    ),
    "Chapter 6": (
        "census-78a4a177ee6726a5",
        "census-f5a50680149423f4",
        "census-1edd5d9d59f81553",
        "census-15e0e28502a3aa01",
        "census-96eaba74736a906b",
    ),
    "Chapter 7": (
        "census-0560df665cff4b2d",
        "census-bd0478c6633a1f9d",
        "census-ea1c69d973f1e27b",
        "census-a334813e84362d44",
        "census-158ae90881f0f306",
    ),
}

WITNESS_NAMES = (
    "HDP.Verification.V6TierC.seeded_ch5_gaussian_norm_concentration_fin2",
    "HDP.Verification.V6TierC.seeded_ch5_lipschitzSeminorm_real_identity",
    "HDP.Verification.V6TierC.seeded_ch6_exercise_6_2a_independent_rademacher",
    "HDP.Verification.V6TierC.seeded_ch7_finiteGaussianProcess_identical_fin1",
    "HDP.Verification.V6TierC.seeded_ch7_polytopeCovering_fin1_segment",
    "HDP.Verification.V6TierC.queue_ch5_grassmannian_fin2_line",
    "HDP.Verification.V6TierC.queue_ch5_matrixNorm_loewner_diagonal_fin2",
    "HDP.Verification.V6TierC.queue_ch7_gaussianInterpolation_fin1_half",
    "HDP.Verification.V6TierC.queue_ch7_crossPolytope_dimension_two",
    "HDP.Verification.V6TierC.queue_ch7_multivariateGaussianIBP_fin1",
    "HDP.Verification.V6TierC.tierA_ch6_exercise625_two_branches_nonvacuous",
    "HDP.Verification.V6TierC.tierA_ch7_logPartition_positiveBeta_fin2",
    "HDP.Verification.V6TierC.seeded_current_ch5_remark_5_6_2",
    "HDP.Verification.V6TierC.seeded_current_ch5_exercise_5_2c",
    "HDP.Verification.V6TierC.seeded_current_ch5_random_lieb_real",
    "HDP.Verification.V6TierC.seeded_current_ch6_theorem_6_4_1",
    "HDP.Verification.V6TierC.seeded_current_ch7_exercise_7_1b",
    "HDP.Verification.V6TierC.seeded_current_ch7_phase_transition_sum_equiv_max",
    "HDP.Verification.V6TierC.seeded_current_ch7_exercise_7_16_symmetric_pair",
    "HDP.Verification.V6TierC.seeded_current_ch7_exercise_7_27a",
)

COMPILED_QUEUE_WITNESSES = {
    "census-4873958abc52b612":
        "HDP.Verification.V6TierC.queue_ch5_grassmannian_fin2_line",
    "census-9a8303edb533db45":
        "HDP.Verification.V6TierC.queue_ch5_matrixNorm_loewner_diagonal_fin2",
    "census-0560df665cff4b2d":
        "HDP.Verification.V6TierC.queue_ch7_gaussianInterpolation_fin1_half",
    "census-bd0478c6633a1f9d":
        "HDP.Verification.V6TierC.queue_ch7_crossPolytope_dimension_two",
    "census-ea1c69d973f1e27b":
        "HDP.Verification.V6TierC.queue_ch7_multivariateGaussianIBP_fin1",
}

CITATION_EVIDENCE = {
    "census-28ee26691f687a9c": {
        "target": "HDP.Chapter5.matrixBernsteinExpectation",
        "citing": "HDP.Chapter5.sparseSBM_expectedNoise_exact",
        "location": (
            "HighDimensionalProbability/"
            "Chapter5_ConcentrationWithoutIndependence.lean:8194"
        ),
        "rationale": (
            "The sparse-SBM theorem constructs the centered matrix summands, "
            "measurability, uniform bound, expectation-zero certificates, and "
            "independence before applying matrix Bernstein."
        ),
    },
    "census-a42f06353bdaf063": {
        "target": "HDP.Chapter5.blowUp_of_centered_concentration",
        "citing": "HDP.Chapter5.sphere_blowUp",
        "location": (
            "HighDimensionalProbability/"
            "Chapter5_ConcentrationWithoutIndependence.lean:1394"
        ),
        "rationale": (
            "The sphere theorem fixes the Borel sphere probability law and "
            "constructs the distance-to-set observable, including its "
            "measurability, nonnegativity, zero-on-set, and concentration "
            "certificates.  Its forwarded measurable half-mass set guards "
            "are jointly realized, for example, by the whole sphere."
        ),
    },
    "census-636ecf0b5c2c32b0": {
        "target": "HDP.Chapter5.randomProjection_secondMoment",
        "citing": "HDP.Chapter5.randomProjection_rms",
        "location": (
            "HighDimensionalProbability/"
            "Chapter5_ConcentrationWithoutIndependence.lean:5092"
        ),
        "rationale": (
            "The RMS theorem invokes the exact second-moment result on the "
            "Grassmann Haar projection model.  Its forwarded guards have the "
            "concrete nondegenerate realization m=1, n=2 (and the theorem "
            "accepts a nonzero z), so the application is not empty-domain "
            "only."
        ),
    },
    "census-78a4a177ee6726a5": {
        "target": (
            "HDP.Chapter6."
            "symmetricRandomMatrix_expectedNorm_upper_of_symmetrization"
        ),
        "citing": "HDP.Chapter6.theorem_6_4_1",
        "location": (
            "HighDimensionalProbability/"
            "Chapter6_QuadraticFormsSymmetrizationContraction.lean:5319"
        ),
        "rationale": (
            "The Chapter 6 theorem first derives the required symmetrization "
            "inequality from centered independent coordinates and Rademacher "
            "signs, then applies the analytic endpoint."
        ),
    },
    "census-f5a50680149423f4": {
        "target": "HDP.Chapter6.gaussianSymmetrization_upper",
        "citing": "HDP.Chapter6.gaussianSymmetrization_source",
        "location": (
            "HighDimensionalProbability/"
            "Chapter6_QuadraticFormsSymmetrizationContraction.lean:9353"
        ),
        "rationale": (
            "The source-facing lemma applies the upper comparison after "
            "passing all measurable, integrable, centered, independence, "
            "Rademacher, and Gaussian-law certificates; finite Rademacher "
            "product space together with the canonical Gaussian product "
            "gives a concrete joint realization of those guards."
        ),
    },
    "census-1edd5d9d59f81553": {
        "target": (
            "HDP.Chapter6."
            "quadraticForm_sub_integral_eq_diagonal_add_offDiagonal"
        ),
        "citing": "HDP.Chapter6.hansonWright",
        "location": (
            "HighDimensionalProbability/"
            "Chapter6_QuadraticFormsSymmetrizationContraction.lean:3592"
        ),
        "rationale": (
            "The Hanson--Wright proof applies the decomposition to its finite "
            "independent centered L² coordinate family before estimating the "
            "two resulting terms.  Independent bounded Rademacher "
            "coordinates and a nonzero finite matrix realize the forwarded "
            "family assumptions."
        ),
    },
    "census-15e0e28502a3aa01": {
        "target": "HDP.Chapter6.gaussianReplacement",
        "citing": "HDP.Chapter6.hansonWright_offDiagonal_lmgf",
        "location": (
            "HighDimensionalProbability/"
            "Chapter6_QuadraticFormsSymmetrizationContraction.lean:3260"
        ),
        "rationale": (
            "The off-diagonal MGF proof instantiates replacement with two "
            "structurally independent centered subgaussian vectors, their "
            "bounded ψ₂ data, and the off-diagonal linear map."
        ),
    },
    "census-96eaba74736a906b": {
        "target": (
            "HDP.Chapter6."
            "integral_norm_le_integral_norm_add_independent_centered"
        ),
        "citing": "HDP.Chapter6.symmetrization",
        "location": (
            "HighDimensionalProbability/"
            "Chapter6_QuadraticFormsSymmetrizationContraction.lean:4623"
        ),
        "rationale": (
            "The symmetrization proof applies the endpoint to the original "
            "sum and an independent centered copy on a product probability "
            "space, discharging integrability and centering internally."
        ),
    },
    "census-a334813e84362d44": {
        "target": "HDP.Chapter7.gaussianIntegrationByParts",
        "citing": "HDP.Chapter7.gaussianIntegrationByParts_measure",
        "location": "HighDimensionalProbability/Chapter7_RandomProcesses.lean:1176",
        "rationale": (
            "The private measure bridge supplies the derivative and all three "
            "density-product integrability certificates, then converts the "
            "scalar identity to the Gaussian measure formulation.  Its "
            "forwarded Gaussian-integrability guards have a concrete "
            "nonconstant realization f(x)=x, f'(x)=1."
        ),
    },
    "census-158ae90881f0f306": {
        "target": "HDP.Chapter7.cubeGaussianWidth_eq_source",
        "citing": "HDP.Chapter9.example_9_7_4_cubeGaussianWidth",
        "location": (
            "HighDimensionalProbability/"
            "Chapter9_DeviationsOfRandomMatricesOnSets.lean:19620"
        ),
        "rationale": (
            "The Chapter 9 cube example directly specializes the exact cube "
            "width formula at arbitrary finite dimension and uses the result "
            "as a downstream book conclusion."
        ),
    },
}

EXPECTED_TIER_A_HITS = {
    (
        "HighDimensionalProbability/Exercise/Chapter6/Sec03.lean",
        "exercise_6_25",
    ),
    (
        "HighDimensionalProbability/Chapter7_RandomProcesses.lean",
        "exercise_7_7_logPartitionDerivativeExpression_nonpos",
    ),
}

ALLOWED_AXIOMS = {
    "propext",
    "Classical.choice",
    "Quot.sound",
}

FORBIDDEN_PROOF_TOKEN = re.compile(r"\b(?:sorry|admit)\b")
WITNESS_DECL = re.compile(
    r"(?m)^[ \t]*(?:theorem|alias)[ \t]+([A-Za-z_][A-Za-z0-9_']*)"
)
FORBIDDEN_IMPORT = "MatrixConcentration.Appendix_RosenthalPinelis"


@dataclass(frozen=True)
class CommandResult:
    command: tuple[str, ...]
    returncode: int
    output: str


class AuditFailure(RuntimeError):
    pass


def project_path(relative: Path) -> Path:
    return ROOT / relative


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


def check_queue() -> dict[str, object]:
    compiled_names = set(COMPILED_QUEUE_WITNESSES.values())
    if compiled_names != {
        "HDP.Verification.V6TierC.queue_ch5_grassmannian_fin2_line",
        "HDP.Verification.V6TierC.queue_ch5_matrixNorm_loewner_diagonal_fin2",
        "HDP.Verification.V6TierC.queue_ch7_gaussianInterpolation_fin1_half",
        "HDP.Verification.V6TierC.queue_ch7_crossPolytope_dimension_two",
        "HDP.Verification.V6TierC.queue_ch7_multivariateGaussianIBP_fin1",
    }:
        raise AuditFailure(
            "compiled queue witness declarations disagree with WITNESS_NAMES"
        )
    if len(CITATION_EVIDENCE) != 10 or len(compiled_names) != 5:
        raise AuditFailure(
            "expected the fixed 10-citation/5-compiled queue partition"
        )

    sampling_plan = json.loads(
        project_path(SAMPLING_PLAN_REL).read_text(encoding="utf-8")
    )
    if sampling_plan.get("schema_version") != 1:
        raise AuditFailure(
            f"{SAMPLING_PLAN_REL}: expected schema_version 1"
        )
    if sampling_plan.get("semantic_verdicts_assigned") is not False:
        raise AuditFailure(
            f"{SAMPLING_PLAN_REL}: mechanical plan must not assign verdicts"
        )
    candidate_ranking = sampling_plan.get("ok_candidate_ranking")
    plan_head = sampling_plan.get("ok_review_queue_head")
    if not isinstance(candidate_ranking, list) or not isinstance(
        plan_head, list
    ):
        raise AuditFailure(
            f"{SAMPLING_PLAN_REL}: missing OK ranking/queue arrays"
        )

    inventory_summary = json.loads(
        project_path(INVENTORY_SUMMARY_REL).read_text(encoding="utf-8")
    )
    try:
        census_count = int(
            inventory_summary["review_census"]["row_count"]
        )
    except (KeyError, TypeError, ValueError) as error:
        raise AuditFailure(
            f"{INVENTORY_SUMMARY_REL}: missing review-census row count"
        ) from error
    if census_count != 835:
        raise AuditFailure(
            f"{INVENTORY_SUMMARY_REL}: expected 835 current census rows, "
            f"found {census_count}"
        )
    if inventory_summary["review_census"].get("frozen_row_count") != 838:
        raise AuditFailure(
            f"{INVENTORY_SUMMARY_REL}: frozen 838-row archive contract drifted"
        )

    plan_ids_by_chapter: dict[str, list[str]] = {}
    for chapter, expected_ids in QUEUE_IDS.items():
        ranked = sorted(
            (
                row
                for row in candidate_ranking
                if isinstance(row, dict) and row.get("chapter") == chapter
            ),
            key=lambda row: int(row["rank"]),
        )
        if [int(row["rank"]) for row in ranked] != list(
            range(1, len(ranked) + 1)
        ):
            raise AuditFailure(
                f"{chapter}: sampling-plan candidate ranks are not contiguous"
            )
        if len(ranked) < 5:
            raise AuditFailure(
                f"{chapter}: sampling plan has fewer than five candidates"
            )
        first_five = [str(row["target_id"]) for row in ranked[:5]]
        if tuple(first_five) != expected_ids:
            raise AuditFailure(
                f"{chapter}: first five full-census candidates changed: "
                f"expected {expected_ids!r}, found {tuple(first_five)!r}"
            )
        head_rows = sorted(
            (
                row
                for row in plan_head
                if isinstance(row, dict) and row.get("chapter") == chapter
            ),
            key=lambda row: int(row["rank"]),
        )
        if [int(row["rank"]) for row in head_rows] != [1, 2, 3, 4, 5]:
            raise AuditFailure(
                f"{chapter}: sampling-plan queue ranks are not exactly 1--5"
            )
        head_ids = [str(row["target_id"]) for row in head_rows]
        if head_ids != first_five:
            raise AuditFailure(
                f"{chapter}: queue head differs from the first five "
                "full-census candidates"
            )
        plan_ids_by_chapter[chapter] = head_ids

    with project_path(LEDGER_REL).open(encoding="utf-8", newline="") as handle:
        rows = list(csv.DictReader(handle, delimiter="\t"))
    queue = [
        row
        for row in rows
        if row["row_set"] == "sampling_plan"
        and row["sample_kind"] == "ok_review_queue_head"
    ]
    if len(queue) != 15:
        raise AuditFailure(f"expected 15 queue rows, found {len(queue)}")
    observed: dict[str, list[str]] = {}
    for chapter in QUEUE_IDS:
        chapter_rows = sorted(
            (row for row in queue if row["chapter"] == chapter),
            key=lambda row: int(row["sample_rank"]),
        )
        if [int(row["sample_rank"]) for row in chapter_rows] != [1, 2, 3, 4, 5]:
            raise AuditFailure(f"{chapter}: queue ranks are not exactly 1--5")
        ids = [row["row_id"] for row in chapter_rows]
        if tuple(ids) != QUEUE_IDS[chapter]:
            raise AuditFailure(
                f"{chapter}: queue IDs changed: expected "
                f"{QUEUE_IDS[chapter]!r}, found {tuple(ids)!r}"
            )
        if ids != plan_ids_by_chapter[chapter]:
            raise AuditFailure(
                f"{chapter}: Tier-B ledger queue differs from sampling plan"
            )
        if any(row["verdict"] != "OK" or row["tier_c_required"] != "yes"
               for row in chapter_rows):
            raise AuditFailure(f"{chapter}: queue contains a non-OK/non-required row")
        for row in chapter_rows:
            row_id = row["row_id"]
            if row_id in CITATION_EVIDENCE:
                evidence = CITATION_EVIDENCE[row_id]
                if row["witness_by_citation_candidate"] != evidence["citing"]:
                    raise AuditFailure(
                        f"{row_id}: citation candidate changed: expected "
                        f"{evidence['citing']!r}, found "
                        f"{row['witness_by_citation_candidate']!r}"
                    )
                resolved = {
                    name.strip()
                    for name in row["resolved_declarations"].split(";")
                    if name.strip()
                }
                if evidence["target"] not in resolved:
                    raise AuditFailure(
                        f"{row_id}: target {evidence['target']} is absent "
                        "from resolved_declarations"
                    )
            elif row_id in COMPILED_QUEUE_WITNESSES:
                if not row["witness_by_citation_candidate"].startswith(
                    "FRESH_NAMED_WITNESS:"
                ):
                    raise AuditFailure(
                        f"{row_id}: compiled-witness row no longer requests "
                        "a fresh named witness"
                    )
            else:
                raise AuditFailure(
                    f"{row_id}: queue row has no Tier-C evidence assignment"
                )
        observed[chapter] = ids
    if set(CITATION_EVIDENCE) | set(COMPILED_QUEUE_WITNESSES) != {
        row["row_id"] for row in queue
    }:
        raise AuditFailure(
            "citation/compiled evidence partition does not exactly cover queue"
        )
    return {
        "row_count": len(queue),
        "citation_row_count": len(CITATION_EVIDENCE),
        "compiled_row_count": len(COMPILED_QUEUE_WITNESSES),
        "sampling_frame": {
            "census_row_count": census_count,
            "candidate_source": "full current 835-row census",
            "queue_rule": "fixed-hash ranks 1--5 per chapter",
        },
        "ids_by_chapter": observed,
    }


def masked_source(relative: Path) -> str:
    text = project_path(relative).read_text(encoding="utf-8")
    masked, diagnostics = mask_lean_noncode(text)
    if diagnostics:
        raise AuditFailure(f"{relative}: Lean lexical diagnostics: {diagnostics!r}")
    return masked


def forbidden_tokens(relative: Path) -> list[str]:
    return FORBIDDEN_PROOF_TOKEN.findall(masked_source(relative))


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
    local_names = WITNESS_DECL.findall(code)
    expected_local = [name.rsplit(".", 1)[1] for name in WITNESS_NAMES]
    if local_names != expected_local:
        raise AuditFailure(
            "witness declaration list mismatch:\n"
            f"expected={expected_local!r}\nobserved={local_names!r}"
        )
    return {
        "path": str(WITNESS_REL),
        "theorem_count": len(local_names),
        "forbidden_proof_token_count": 0,
        "autoImplicit_false": True,
        "known_broken_import": False,
    }


def is_ch5_7_source_path(path: str) -> bool:
    if not path.startswith("HighDimensionalProbability/"):
        return False
    if path.startswith("HighDimensionalProbability/Verification/"):
        return False
    return (
        path.startswith("HighDimensionalProbability/Chapter5_")
        or path.startswith("HighDimensionalProbability/Chapter5/")
        or path.startswith("HighDimensionalProbability/Chapter6_")
        or path.startswith("HighDimensionalProbability/Chapter6/")
        or path.startswith("HighDimensionalProbability/Chapter7_")
        or path.startswith("HighDimensionalProbability/Chapter7/")
        or path.startswith("HighDimensionalProbability/Exercise/Chapter5/")
        or path.startswith("HighDimensionalProbability/Exercise/Chapter6/")
        or path.startswith("HighDimensionalProbability/Exercise/Chapter7/")
    )


def validate_tier_a_report(report: dict[str, object]) -> dict[str, object]:
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
        (declaration["path"], declaration["name"])
        for declaration in report["declarations"]
        if is_ch5_7_source_path(declaration["path"])
        and any(
            not isinstance(reason, dict)
            or reason.get("reason_id") != AUTO_BOUND_REASON_ID
            for reason in declaration["triage_reasons"]
        )
    }
    chapter_auto_bound_count = sum(
        is_ch5_7_source_path(declaration["path"])
        and any(
            isinstance(reason, dict)
            and reason.get("reason_id") == AUTO_BOUND_REASON_ID
            for reason in declaration["triage_reasons"]
        )
        for declaration in report["declarations"]
    )
    if relevant != EXPECTED_TIER_A_HITS:
        raise AuditFailure(
            "fresh Chapter 5--7 Tier-A hit set changed:\n"
            f"expected={sorted(EXPECTED_TIER_A_HITS)!r}\n"
            f"observed={sorted(relevant)!r}"
        )
    return {
        "summary": report["summary"],
        "v4_join": v4_join,
        "chapter_5_7_auto_bound_flagged_declarations": (
            chapter_auto_bound_count
        ),
        "chapter_5_7_hits": [
            {"path": path, "name": name} for path, name in sorted(relevant)
        ],
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
        command, LOG_DIR_REL / "v6_tier_c_ch5_7_tier_a_scan.log"
    )
    if result.returncode != 0:
        raise AuditFailure(f"fresh Tier-A scan exited {result.returncode}")
    report = json.loads(project_path(SCAN_JSON_REL).read_text(encoding="utf-8"))
    return validate_tier_a_report(report)


def parse_axiom_field(text: str) -> set[str]:
    return {
        axiom.strip()
        for axiom in re.split(r"[;,]", text)
        if axiom.strip()
    }


def source_path_for_module(module: str) -> str:
    parts = module.split(".")
    if parts[0] == "HighDimensionalProbability":
        if len(parts) == 1:
            return "HighDimensionalProbability.lean"
        return "/".join(parts) + ".lean"
    if parts[0] == "MatrixConcentration":
        if len(parts) == 1:
            return "MatrixConcentration.lean"
        return "/".join(("Pre_MatrixConcentration", *parts[1:])) + ".lean"
    raise AuditFailure(f"citation module is outside the project: {module!r}")


def validate_citation_evidence() -> list[dict[str, object]]:
    """Require each citation witness to be a clean direct proof dependency."""
    expected_aliases = {
        str(evidence[key])
        for evidence in CITATION_EVIDENCE.values()
        for key in ("target", "citing")
    }
    matches: dict[str, list[dict[str, str]]] = {
        alias: [] for alias in expected_aliases
    }
    axiom_path = project_path(V4_AXIOMS_REL)
    with axiom_path.open(encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle, delimiter="\t")
        required = {
            "module",
            "name",
            "kind",
            "private_user_name",
            "axioms",
        }
        if not required <= set(reader.fieldnames or ()):
            raise AuditFailure(
                f"{V4_AXIOMS_REL}: missing columns "
                f"{sorted(required - set(reader.fieldnames or ()))!r}"
            )
        for row in reader:
            for alias in (row["name"], row["private_user_name"]):
                if alias in matches:
                    matches[alias].append(row)
    ambiguous = {
        alias: len(rows)
        for alias, rows in matches.items()
        if len(rows) != 1
    }
    if ambiguous:
        raise AuditFailure(
            "citation V4 declaration resolution is not one-to-one: "
            f"{ambiguous!r}"
        )
    resolved = {alias: rows[0] for alias, rows in matches.items()}
    for alias, row in resolved.items():
        if row["kind"] != "theorem":
            raise AuditFailure(
                f"citation declaration {alias} has V4 kind {row['kind']!r}"
            )
        extras = parse_axiom_field(row["axioms"]) - ALLOWED_AXIOMS
        if extras:
            raise AuditFailure(
                f"citation declaration {alias} has disallowed axioms "
                f"{sorted(extras)!r}"
            )
    for row_id, evidence in CITATION_EVIDENCE.items():
        relative, separator, line_text = str(evidence["location"]).rpartition(":")
        if not separator:
            raise AuditFailure(
                f"{row_id}: malformed citation source location"
            )
        try:
            line_number = int(line_text)
        except ValueError as error:
            raise AuditFailure(
                f"{row_id}: malformed citation source line {line_text!r}"
            ) from error
        citing_row = resolved[str(evidence["citing"])]
        expected_relative = source_path_for_module(citing_row["module"])
        if relative != expected_relative:
            raise AuditFailure(
                f"{row_id}: citation source path {relative!r} differs from "
                f"V4 module path {expected_relative!r}"
            )
        lines = project_path(Path(relative)).read_text(
            encoding="utf-8"
        ).splitlines()
        if not 1 <= line_number <= len(lines):
            raise AuditFailure(
                f"{row_id}: citation source line is out of range"
            )
        target_short_name = str(evidence["target"]).rsplit(".", 1)[-1]
        if target_short_name not in lines[line_number - 1]:
            raise AuditFailure(
                f"{row_id}: recorded citation line does not contain "
                f"{target_short_name!r}"
            )

    needed_edges: dict[tuple[str, str], str] = {}
    for row_id, evidence in CITATION_EVIDENCE.items():
        source = resolved[str(evidence["citing"])]["name"]
        target = resolved[str(evidence["target"])]["name"]
        key = (source, target)
        if key in needed_edges:
            raise AuditFailure(
                f"duplicate citation edge assignment for {key!r}"
            )
        needed_edges[key] = row_id
    observed: dict[tuple[str, str], list[dict[str, str]]] = {
        key: [] for key in needed_edges
    }
    dependency_path = project_path(V4_DEPENDENCIES_REL)
    with dependency_path.open(encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle, delimiter="\t")
        expected_columns = {
            "source_module",
            "source",
            "source_kind",
            "origin",
            "target_module",
            "target",
        }
        if set(reader.fieldnames or ()) != expected_columns:
            raise AuditFailure(
                f"{V4_DEPENDENCIES_REL}: columns "
                f"{reader.fieldnames!r} do not match "
                f"{sorted(expected_columns)!r}"
            )
        for row in reader:
            key = (row["source"], row["target"])
            if key in observed:
                observed[key].append(row)
    invalid_edges: dict[str, object] = {}
    for key, edges in observed.items():
        value_edges = [
            edge
            for edge in edges
            if edge["origin"] == "value"
            and edge["source_kind"] == "theorem"
        ]
        if len(value_edges) != 1:
            invalid_edges[needed_edges[key]] = {
                "source_target": key,
                "all_matching_edges": edges,
                "valid_value_theorem_edges": len(value_edges),
            }
    if invalid_edges:
        raise AuditFailure(
            "citation evidence lacks an exact unique V4 direct value edge: "
            f"{invalid_edges!r}"
        )

    result: list[dict[str, object]] = []
    for row_id in sorted(CITATION_EVIDENCE):
        evidence = CITATION_EVIDENCE[row_id]
        source_row = resolved[str(evidence["citing"])]
        target_row = resolved[str(evidence["target"])]
        edge = next(
            edge
            for edge in observed[(source_row["name"], target_row["name"])]
            if edge["origin"] == "value"
            and edge["source_kind"] == "theorem"
        )
        result.append(
            {
                "row_id": row_id,
                "citing": evidence["citing"],
                "citing_internal_name": source_row["name"],
                "target": evidence["target"],
                "target_internal_name": target_row["name"],
                "source_location": evidence["location"],
                "direct_dependency_origin": edge["origin"],
                "citing_axioms": sorted(
                    parse_axiom_field(source_row["axioms"])
                ),
                "target_axioms": sorted(
                    parse_axiom_field(target_row["axioms"])
                ),
                "rationale": evidence["rationale"],
            }
        )
    return result


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
        "V6TierCCh5_7"
    )
    result = run_logged(
        ["lake", "build", module],
        BUILD_LOG_REL,
    )
    if result.returncode != 0:
        raise AuditFailure(f"witness build exited {result.returncode}")
    return {"module": module, "exit_code": result.returncode}


def audit_axioms() -> dict[str, list[str]]:
    result = run_logged(
        [
            "lake",
            "env",
            "lean",
            *LEAN_OPTIONS,
            str(project_path(AXIOM_HARNESS_REL)),
        ],
        AXIOM_LOG_REL,
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
        PLANTED_BAD_LOG_REL,
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
        "path": str(PLANTED_BAD_REL),
        "source_tokens": source_tokens,
        "static_rejected": static_rejected,
        "axioms": sorted(bad_axioms),
        "axiom_rejected": axiom_rejected,
        "checker_verdict": "REJECT",
    }


def render_runner_log(report: dict[str, object]) -> str:
    lines = [
        "V6 Tier-C Chapters 5--7 witness checker",
        f"overall: {report['overall']}",
        f"execution_mode: {report['execution_mode']}",
        f"lean_execution_complete: "
        f"{str(report['lean_execution_complete']).lower()}",
        f"queue_rows: {report['queue']['row_count']}",
        "queue_sampling_census_rows: "
        f"{report['queue']['sampling_frame']['census_row_count']}",
        "queue_sampling_rule: fixed-hash ranks 1--5 per chapter",
        f"queue_citation_witnesses: {report['queue']['citation_row_count']}",
        f"queue_compiled_witnesses: {report['queue']['compiled_row_count']}",
        f"compiled_witness_theorems_including_tier_a: "
        f"{report['source']['theorem_count']}",
        f"v4_direct_citation_edges: {len(report['citations'])}",
        "source_sorry_admit: 0",
    ]
    if "tier_a" in report:
        lines.extend(
            [
                "fresh_tier_a_hits: "
                f"{len(report['tier_a']['chapter_5_7_hits'])}",
                "v4_join_complete_binder_telescopes: "
                f"{report['tier_a']['v4_join']['complete_binder_telescopes']}",
                "v4_auto_bound_flagged_declarations: "
                f"{report['tier_a']['v4_join']['auto_bound_flagged_declaration_count']}",
                "v4_auto_bound_ch5_7_flagged_declarations: "
                f"{report['tier_a']['chapter_5_7_auto_bound_flagged_declarations']}",
            ]
        )
    if "axioms" in report:
        lines.extend(
            [
                f"axiom_audited_witnesses: {len(report['axioms'])}",
                "allowed_axioms: Classical.choice, Quot.sound, propext",
            ]
        )
    if "planted_bad" in report:
        lines.extend(
            [
                "planted_bad_static: REJECT",
                "planted_bad_axioms: REJECT (sorryAx)",
            ]
        )
    return "\n".join(lines) + "\n"


def file_sha256(relative: Path) -> str:
    return hashlib.sha256(project_path(relative).read_bytes()).hexdigest()


def successful_log(relative: Path, required_text: str) -> str:
    path = project_path(relative)
    if not path.is_file():
        raise AuditFailure(f"missing final evidence log: {relative}")
    text = path.read_text(encoding="utf-8")
    if not re.search(r"(?m)^exit_code: 0$", text):
        raise AuditFailure(f"final evidence log has no exit_code 0: {relative}")
    if required_text not in text:
        raise AuditFailure(
            f"final evidence log lacks {required_text!r}: {relative}"
        )
    return text


def validate_existing_axiom_log(text: str) -> dict[str, list[str]]:
    rows = parse_axiom_markers(text)
    if set(rows) != set(WITNESS_NAMES):
        raise AuditFailure(
            "recorded axiom declaration set mismatch:\n"
            f"missing={sorted(set(WITNESS_NAMES) - set(rows))!r}\n"
            f"extra={sorted(set(rows) - set(WITNESS_NAMES))!r}"
        )
    violations = {
        name: sorted(axioms - ALLOWED_AXIOMS)
        for name, axioms in rows.items()
        if axioms - ALLOWED_AXIOMS
    }
    if violations:
        raise AuditFailure(f"recorded witness axioms are disallowed: {violations!r}")
    return {name: sorted(rows[name]) for name in WITNESS_NAMES}


def validate_existing_planted_bad_log(text: str) -> dict[str, object]:
    source_tokens = forbidden_tokens(PLANTED_BAD_REL)
    rows = parse_axiom_markers(text)
    bad_name = "HDP.Verification.V6TierC.plantedBadWitness"
    bad_axioms = rows.get(bad_name, set())
    if not source_tokens:
        raise AuditFailure("recorded planted bad source is no longer lexically bad")
    if "sorryAx" not in bad_axioms or not (bad_axioms - ALLOWED_AXIOMS):
        raise AuditFailure(
            "recorded planted bad witness is no longer rejected by axioms: "
            f"{sorted(bad_axioms)!r}"
        )
    return {
        "path": str(PLANTED_BAD_REL),
        "source_tokens": source_tokens,
        "static_rejected": True,
        "axioms": sorted(bad_axioms),
        "axiom_rejected": True,
        "checker_verdict": "REJECT",
    }


def check_existing() -> str:
    """Read-only replay of static contracts and the preserved final evidence."""
    queue = check_queue()
    source = check_witness_source()
    citations = validate_citation_evidence()
    scan_path = project_path(SCAN_JSON_REL)
    if not scan_path.is_file():
        raise AuditFailure(f"missing final Tier-A scan: {SCAN_JSON_REL}")
    tier_a = validate_tier_a_report(
        json.loads(scan_path.read_text(encoding="utf-8"))
    )

    build_log = successful_log(
        BUILD_LOG_REL, "Build completed successfully (8646 jobs)."
    )
    axiom_log = successful_log(
        AXIOM_LOG_REL, "V6_TIER_C_AXIOM\t"
    )
    planted_bad_log = successful_log(
        PLANTED_BAD_LOG_REL, "\tsorryAx"
    )
    axioms = validate_existing_axiom_log(axiom_log)
    planted_bad = validate_existing_planted_bad_log(planted_bad_log)

    runner_path = project_path(RUNNER_LOG_REL)
    if not runner_path.is_file():
        raise AuditFailure(f"missing final runner log: {RUNNER_LOG_REL}")
    runner_log = runner_path.read_text(encoding="utf-8")
    if "overall: PASS" not in runner_log or "lean_execution_complete: true" not in runner_log:
        raise AuditFailure("preserved runner log is not a completed PASS")

    result_path = project_path(RESULT_JSON_REL)
    if not result_path.is_file():
        raise AuditFailure(f"missing final result: {RESULT_JSON_REL}")
    result = json.loads(result_path.read_text(encoding="utf-8"))
    if (
        result.get("profile") != "V6-Tier-C-Ch5-7"
        or result.get("overall") != "PASS"
        or result.get("execution_mode") != "full"
        or result.get("lean_execution_complete") is not True
    ):
        raise AuditFailure("preserved result JSON is not the final full PASS")
    expected_build = {
        "module": (
            "HighDimensionalProbability.Verification.scripts.witnesses."
            "V6TierCCh5_7"
        ),
        "exit_code": 0,
    }
    comparisons = {
        "queue": queue,
        "source": source,
        "tier_a": tier_a,
        "citations": citations,
        "build": expected_build,
        "axioms": axioms,
        "planted_bad": planted_bad,
    }
    for key, expected in comparisons.items():
        if result.get(key) != expected:
            raise AuditFailure(f"preserved result field is stale: {key}")

    witness_path = project_path(WITNESS_REL)
    olean_path = project_path(WITNESS_OLEAN_REL)
    build_path = project_path(BUILD_LOG_REL)
    axiom_path = project_path(AXIOM_LOG_REL)
    planted_path = project_path(PLANTED_BAD_LOG_REL)
    if not olean_path.is_file():
        raise AuditFailure(f"missing compiled witness artifact: {WITNESS_OLEAN_REL}")
    if witness_path.stat().st_mtime_ns > olean_path.stat().st_mtime_ns:
        raise AuditFailure("witness source is newer than its compiled olean")
    if olean_path.stat().st_mtime_ns > build_path.stat().st_mtime_ns:
        raise AuditFailure("compiled witness is newer than the preserved build log")
    for evidence_path in (build_path, axiom_path, planted_path):
        if evidence_path.stat().st_mtime_ns > result_path.stat().st_mtime_ns:
            raise AuditFailure(
                f"final result predates evidence: {evidence_path.relative_to(ROOT)}"
            )
    if runner_path.stat().st_mtime_ns < result_path.stat().st_mtime_ns:
        raise AuditFailure("final runner log predates the preserved result JSON")

    hash_paths = (
        WITNESS_REL,
        WITNESS_OLEAN_REL,
        RESULT_JSON_REL,
        BUILD_LOG_REL,
        AXIOM_LOG_REL,
        PLANTED_BAD_LOG_REL,
        SCAN_JSON_REL,
    )
    lines = [
        "V6 Tier-C Chapters 5--7 read-only evidence replay",
        "overall: PASS",
        "lean_or_lake_invocations: 0",
        f"queue_rows: {queue['row_count']}",
        f"queue_citation_witnesses: {queue['citation_row_count']}",
        f"queue_compiled_witnesses: {queue['compiled_row_count']}",
        f"v4_direct_citation_edges: {len(citations)}",
        f"axiom_audited_witnesses: {len(axioms)}",
        "planted_bad_static: REJECT",
        "planted_bad_axioms: REJECT (sorryAx)",
        "artifact_sha256:",
    ]
    lines.extend(
        f"  {relative}: {file_sha256(relative)}" for relative in hash_paths
    )
    return "\n".join(lines) + "\n"


def run(*, static_only: bool) -> dict[str, object]:
    report: dict[str, object] = {
        "profile": "V6-Tier-C-Ch5-7",
        "execution_mode": "static-only" if static_only else "full",
        "lean_execution_complete": False,
        "queue": check_queue(),
        "source": check_witness_source(),
        "tier_a": fresh_tier_a_scan(),
        "citations": validate_citation_evidence(),
    }
    if not static_only:
        report["build"] = build_witness_module()
        report["axioms"] = audit_axioms()
        report["planted_bad"] = calibrate_planted_bad()
        report["lean_execution_complete"] = True
    report["overall"] = "STATIC_PASS" if static_only else "PASS"
    return report


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument(
        "--static-only",
        action="store_true",
        help="check ledger/source/fresh Tier-A scan without invoking Lean",
    )
    mode.add_argument(
        "--check",
        action="store_true",
        help="read-only replay of static contracts and preserved final evidence",
    )
    args = parser.parse_args(argv)
    try:
        if args.check:
            print(check_existing(), end="")
            return 0
        report = run(static_only=args.static_only)
    except (AuditFailure, OSError, ValueError, csv.Error) as error:
        if args.check:
            print(f"FAIL: {error}", file=sys.stderr)
            return 1
        failure = {
            "profile": "V6-Tier-C-Ch5-7",
            "overall": "FAIL",
            "error": str(error),
        }
        write_text(RESULT_JSON_REL, json.dumps(failure, indent=2) + "\n")
        write_text(
            RUNNER_LOG_REL,
            f"V6 Tier-C Chapters 5--7 witness checker\noverall: FAIL\n"
            f"error: {error}\n",
        )
        print(f"FAIL: {error}", file=sys.stderr)
        return 1
    write_text(RESULT_JSON_REL, json.dumps(report, indent=2) + "\n")
    runner_log = render_runner_log(report)
    write_text(RUNNER_LOG_REL, runner_log)
    print(runner_log, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
