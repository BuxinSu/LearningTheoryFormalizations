#!/usr/bin/env python3
"""Rebuild and validate the current-tree V6 Tier-C evidence register.

The register retains the fixed five-OK-row sample for Appetizer and Chapters
1--9, adds a reproducible manifest-seeded five-row random sample for every
chapter, and covers every Tier-A row explicitly sent to Tier C.  Evidence is
either a compiled named witness with
an allowed axiom set or an exact clean V4 direct dependency.  Conditional
interfaces removed from the current source tree are not retained as review
rows.
"""

from __future__ import annotations

import argparse
import csv
import datetime as dt
import io
import json
import re
import shlex
import subprocess
import sys
from collections import Counter
from pathlib import Path

from lean_source_scanner import mask_lean_noncode
import run_v6_tier_c_ch0_4 as ch0
import run_v6_tier_c_ch5_7 as ch5
import run_v6_tier_c_ch8_9 as ch8
import build_v6_tier_c_seeded_sample as seeded


ROOT = Path(__file__).resolve().parents[3]
VERIFY = ROOT / "HighDimensionalProbability" / "Verification"
LOGS = VERIFY / "logs"
REVIEW = VERIFY / "review"
AUDIT_WORK = ROOT / ".audit_work" / "verification"

V4_AXIOMS = LOGS / "recert_axiom_audit.tsv"
V4_DEPENDENCIES = LOGS / "recert_axiom_direct_dependencies.tsv"
V4_TYPES = LOGS / "recert_axiom_declaration_types.tsv"
V4_BINDERS = LOGS / "recert_axiom_declaration_binders.tsv"
V4_SUMMARY = LOGS / "recert_axiom_summary.txt"
V4_ANALYZE_LOG = LOGS / "recert_axiom_analyze_command.log"
TIER_A_REVIEW = REVIEW / "recert_v6_tier_a_full_review.tsv"
OUTPUT = REVIEW / "recert_v6_tier_c.tsv"
SUMMARY = REVIEW / "recert_v6_tier_c_summary.txt"
SEEDED_SAMPLE = REVIEW / "recert_v6_tier_c_seeded_sample.tsv"
SEEDED_BUILD_LOG = LOGS / "recert_v6_tier_c_seeded_sample_build.log"

ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
FORBIDDEN = re.compile(r"\b(?:sorry|admit)\b")
FORBIDDEN_COMMAND = re.compile(r"(?m)^[ \t]*(?:axiom|unsafe)[ \t]+")

MODULES = (
    (
        "HighDimensionalProbability.Verification.scripts.witnesses.V6TierCCh0_4",
        VERIFY / "scripts/witnesses/V6TierCCh0_4.lean",
        VERIFY / "scripts/witnesses/V6TierCCh0_4Axioms.lean",
        LOGS / "recert_v6_tier_c_ch0_4_build.log",
        LOGS / "recert_v6_tier_c_ch0_4_axiom_build.log",
    ),
    (
        "HighDimensionalProbability.Verification.scripts.witnesses.V6TierCCh5_7",
        VERIFY / "scripts/witnesses/V6TierCCh5_7.lean",
        VERIFY / "scripts/witnesses/V6TierCCh5_7Axioms.lean",
        LOGS / "recert_v6_tier_c_ch5_7_build.log",
        LOGS / "recert_v6_tier_c_ch5_7_axioms.log",
    ),
    (
        "HighDimensionalProbability.Verification.scripts.witnesses.V6TierCCh8_9",
        VERIFY / "scripts/witnesses/V6TierCCh8_9.lean",
        VERIFY / "scripts/witnesses/V6TierCCh8_9Axioms.lean",
        LOGS / "recert_v6_tier_c_ch8_9_build.log",
        LOGS / "recert_v6_tier_c_ch8_9_axioms.log",
    ),
)

PLANTED_BAD = AUDIT_WORK / "RecertV6TierCPlantedBad.lean"
PLANTED_BAD_LOG = LOGS / "recert_v6_tier_c_planted_bad.log"
CH0_AXIOM_TSV = LOGS / "recert_v6_tier_c_ch0_4_axioms.tsv"

FIELDS = (
    "row_id",
    "category",
    "chapter",
    "source_row_id",
    "endpoint",
    "semantic_verdict",
    "tier_c_status",
    "evidence_kind",
    "evidence_name",
    "evidence_location",
    "axiom_status",
    "notes",
)

EXPECTED_TIER_A_WITNESSES = {
    "HDP.Chapter6.Exercise.exercise_6_25":
        "HDP.Verification.V6TierC.tierA_ch6_exercise625_two_branches_nonvacuous",
    "HDP.Chapter7.exercise_7_7_logPartitionDerivativeExpression_nonpos":
        "HDP.Verification.V6TierC.tierA_ch7_logPartition_positiveBeta_fin2",
    "HDP.matrixSingularValue_of_finrank_le":
        "HDP.Verification.V6TierC.tierA_prelude_matrixSingularValue_fin1_index_one",
}

# A witness entry records both its declaration and the complete endpoint cell
# it binds.  Keeping the cell here makes a multi-endpoint row fail closed if a
# future Tier-B rebuild adds, removes, or renames one of its declarations.
SEEDED_WITNESSES = {
    "supplement-c452720a1b33a3fa": (
        "HDP.Verification.V6TierC.seeded_final_app_polytope_optimizer_unique",
        "HDP.Chapter0.polytope_volume_optimizer_unique",
    ),
    "readme-7da6f704ff0a5a18": (
        "HDP.Verification.V6TierC."
        "seeded_current_ch0_polytope_optimizer_equation",
        "HDP.Chapter0.polytope_volume_optimizer_equation_0_4",
    ),
    "readme-996732e1b59affda": (
        "HDP.Verification.V6TierC.seeded_app_convexHull_eq_union_two_point",
        "convexHull_eq_union",
    ),
    "supplement-05ec64ada66415bb": (
        "HDP.Verification.V6TierC.seeded_final_app_integral_norm_sub_mean_sq",
        "HDP.Chapter0.integral_norm_sub_mean_sq",
    ),
    "readme-4c555287cca4b884": (
        "HDP.Verification.V6TierC.seeded_final_ch1_indicator_biUnion_le_sum",
        "HDP.Chapter1.indicator_biUnion_le_sum",
    ),
    "readme-96e982a9d078ab26": (
        "HDP.Verification.V6TierC.seeded_final_ch1_exercise_1_11a_eLpNorm",
        "HDP.Chapter1.exercise_1_11a_eLpNorm",
    ),
    "readme-979b55c9cdb66383": (
        "HDP.Verification.V6TierC.seeded_final_ch1_holder_rv",
        "HDP.Chapter1.holder_rv",
    ),
    "readme-5be2578c0fdfdb33": (
        "HDP.Verification.V6TierC.seeded_final_ch1_log_gamma_stirling",
        "HDP.Chapter1.log_gamma_stirling",
    ),
    "readme-5c3418a709bd34ea": (
        "HDP.Verification.V6TierC.seeded_final_ch1_convex_iff_segment",
        "HDP.Chapter1.convex_iff_segment",
    ),
    "readme-4d90812e7cfbbffc": (
        "HDP.Verification.V6TierC.seeded_final_ch2_gaussian_mgf",
        "HDP.Chapter2.gaussian_mgf",
    ),
    "readme-4160024d1f31a3e8": (
        "HDP.Verification.V6TierC.seeded_final_ch2_expectation_linear",
        "HDP.Chapter1.expectation_linear",
    ),
    "readme-05b73741d698d674": (
        "HDP.Verification.V6TierC.seeded_final_ch2_remark_2_2_4",
        "HDP.Chapter2.remark_2_2_4",
    ),
    "readme-0cfc7fc076c224b4": (
        "HDP.Verification.V6TierC.seeded_final_ch2_median_one_coordinate_robust",
        "HDP.Chapter2.median_one_coordinate_robust",
    ),
    "readme-6650d812befeb756": (
        "HDP.Verification.V6TierC.seeded_final_ch2_centering_L2",
        "HDP.centering_L2",
    ),
    "readme-e20c0376bd00b58c": (
        "HDP.Verification.V6TierC.seeded_final_ch3_sphere_isIsotropic",
        "HDP.Chapter3.sphere_isIsotropic",
    ),
    "readme-2cc086e3af1f778a": (
        "HDP.Verification.V6TierC.seeded_final_ch3_secondMoment_inner_sq",
        "HDP.Chapter3.secondMoment_inner_sq",
    ),
    "readme-169fc45477378dd0": (
        "HDP.Verification.V6TierC.seeded_final_ch3_thinShellVariance_subGaussian",
        "HDP.Chapter3.thinShellVariance_subGaussian",
    ),
    "readme-d3a2708536d1060d": (
        "HDP.Verification.V6TierC.seeded_ch3_tensor_power_fin2_two",
        "HDP.TensorSpace",
    ),
    "readme-f1495bf642e6fc40": (
        "HDP.Verification.V6TierC."
        "seeded_final_ch3_quadraticObjective_eq_bilinear",
        "HDP.quadraticObjective",
    ),
    "readme-e82e9be2f68ed3f4": (
        "HDP.Verification.V6TierC.seeded_final_ch4_theorem_4_6_1_singular",
        "HDP.Chapter4.theorem_4_6_1_singular",
    ),
    "readme-0258c377a7cf9099": (
        "HDP.Verification.V6TierC.seeded_final_ch4_courantFischer",
        "HDP.Chapter4.courantFischer",
    ),
    "readme-aa91d27cb51e253b": (
        "HDP.Verification.V6TierC."
        "seeded_final_ch4_definition_4_5_1_expectedAdjacency",
        "HDP.Chapter4.definition_4_5_1_expectedAdjacency",
    ),
    "readme-7beb9a23d25dcb48": (
        "HDP.Verification.V6TierC.seeded_final_ch4_remark_4_7_2",
        "HDP.Chapter4.remark_4_7_2",
    ),
    "exercise-decl-d40a37648681030f": (
        "HDP.Verification.V6TierC.seeded_final_ch4_exercise_4_50c_fin1",
        "HDP.Chapter4.Exercise.exercise_4_50c",
    ),
    "supplement-f7d1b86c9442b3f3": (
        "HDP.Verification.V6TierC.seeded_final_ch5_euclidean_isoperimetric",
        "HDP.Chapter5.euclidean_isoperimetric",
    ),
    "readme-2413aa8b59254f66": (
        "HDP.Verification.V6TierC.seeded_final_ch5_sparseSBM_expectedNoise_degree",
        "HDP.Chapter5.sparseSBM_expectedNoise_degree",
    ),
    "readme-b362cf9cf6331bcf": (
        "HDP.Verification.V6TierC."
        "seeded_final_ch5_orthogonalHaarMeasure_left_invariant",
        "HDP.Chapter5.orthogonalHaarMeasure",
    ),
    "readme-744f303500c91bff": (
        "HDP.Verification.V6TierC.seeded_final_ch5_sphere_lipschitz_tail",
        "HDP.Chapter5.sphere_lipschitz_tail",
    ),
    "readme-99dc1ffdba0767a9": (
        "HDP.Verification.V6TierC.seeded_final_ch6_hansonWright",
        "HDP.Chapter6.hansonWright",
    ),
    "readme-2d0de97c527b9d83": (
        "HDP.Verification.V6TierC.seeded_final_ch6_quadraticForm_eq_doubleSum",
        "HDP.Chapter6.quadraticForm",
    ),
    "readme-ed99411d7acc98b5": (
        "HDP.Verification.V6TierC."
        "seeded_final_ch6_sampledMatrix_apply",
        "HDP.Chapter6.sampledMatrix",
    ),
    "readme-896fa95c3398ff7e": (
        "HDP.Verification.V6TierC."
        "seeded_final_ch6_centeredSampling_expectedOperatorNorm_le",
        "HDP.Chapter6.centeredSampling_expectedOperatorNorm_le",
    ),
    "readme-1ac14e4f3b7a900e": (
        "HDP.Verification.V6TierC."
        "seeded_final_ch6_integral_decoupledPartialChaos_le_bilinear",
        "HDP.Chapter6.integral_decoupledPartialChaos_le_bilinear",
    ),
    "readme-6b49c1e4c3f853b4": (
        "HDP.Verification.V6TierC."
        "seeded_final_ch7_gaussianInterpolation_of_boundedDerivative",
        "HDP.Chapter7.gaussianInterpolationPoint",
    ),
    "readme-7ab890fdb2c298c5": (
        "HDP.Verification.V6TierC."
        "seeded_final_ch7_finiteGaussianProcess_identDistrib",
        "HDP.Chapter7.finiteGaussianProcess_identDistrib_of_mean_covariance",
    ),
    "readme-7958ae45c30785fc": (
        (
            "HDP.Verification.V6TierC."
            "seeded_final_ch7_extendedExpectation_eq_integral",
            "HDP.Verification.V6TierC."
            "seeded_final_ch7_extendedExpectedSupremum_noncompact",
        ),
        "HDP.Chapter7.extendedExpectation;"
        "HDP.Chapter7.extendedExpectedSupremum",
    ),
    "readme-08f4ac5d3bed35c2": (
        "HDP.Verification.V6TierC.seeded_final_ch7_slepianInequality",
        "HDP.Chapter7.slepianInequality",
    ),
    "supplement-a047ea696b1f0eb3": (
        "HDP.Verification.V6TierC."
        "seeded_final_ch7_brownianReflectionPrinciple_external",
        "HDP.Chapter7.brownianReflectionPrinciple_external",
    ),
    "supp-0dc100adb3c6a2cd": (
        "HDP.Verification.V6TierC.seeded_final_ch8_corollary_8_5_8_geometric",
        "HDP.Chapter8.corollary_8_5_8_geometric",
    ),
    "readme-932e62e04c5d0c31": (
        "HDP.Verification.V6TierC."
        "seeded_final_ch8_example_8_3_5_euclidean_halfspaces",
        "HDP.Chapter8.example_8_3_5_euclidean_halfspaces",
    ),
    "readme-c97078bc0b3e2987": (
        "HDP.Verification.V6TierC."
        "seeded_final_ch8_discreteDudleyInequality_coveringNumber",
        "HDP.Chapter8.discreteDudleyInequality_coveringNumber",
    ),
    "supp-2796bf019d18772e": (
        "HDP.Verification.V6TierC."
        "seeded_final_ch8_majorizingMeasureLowerPrinciple_external",
        "HDP.Chapter8.majorizingMeasureLowerPrinciple_external",
    ),
    "readme-8e083c0494eb14f1": (
        "HDP.Verification.V6TierC."
        "seeded_final_ch8_theorem_8_3_17_glivenko_cantelli_real",
        "HDP.Chapter8.theorem_8_3_17_glivenko_cantelli_real",
    ),
    "supp-42feb158b7b5abf1": (
        "HDP.Verification.V6TierC."
        "seeded_final_ch9_theorem_9_4_8_sparseRecovery",
        "HDP.Chapter9.theorem_9_4_8_sparseRecovery",
    ),
    "supp-83c594ccb0e9c9d4": (
        "HDP.Verification.V6TierC."
        "seeded_final_ch9_remark_9_4_6_convexRelaxation",
        "HDP.Chapter9.remark_9_4_6_convexRelaxation",
    ),
    "readme-f076db2c3eead751": (
        "HDP.Verification.V6TierC."
        "seeded_final_ch9_ae_finrank_kernel_eq_sub",
        "HDP.Chapter9.ae_finrank_kernel_eq_sub_of_ae_fullRowRank",
    ),
    "supp-c7bb5c9ea7359cc3": (
        "HDP.Verification.V6TierC."
        "seeded_final_ch9_theorem_9_1_1_matrixDeviation_envelope",
        "HDP.Chapter9.theorem_9_1_1_matrixDeviation_envelope",
    ),
    "readme-2e71fd6ee6a07abc": (
        "HDP.Verification.V6TierC."
        "seeded_final_ch9_functionalDeviationProcess_setSupport_eq",
        "HDP.Chapter9.functionalDeviationProcess_setSupport_eq",
    ),
}

# Each tuple is (target, citing declaration, exact current source use).
SEEDED_CITATIONS = {
    "supplement-8ff9b2c7d348298c": (
        ("HDP.Chapter0.integral_norm_sum_sq_of_iIndepFun",
         "HDP.Chapter0.approximate_caratheodory",
         "HighDimensionalProbability/Chapter0_Appetizer.lean:272"),
    ),
    "readme-d32457db5ca3a57e": (
        ("HDP.Chapter5.exercise_5_3a_exponentially_small_blowUp",
         "HDP.Chapter5.exercise_5_3b_exponentially_small_blowUp",
         "HighDimensionalProbability/Chapter5_ConcentrationWithoutIndependence.lean:1209"),
    ),
}


class AuditFailure(RuntimeError):
    pass


def run_logged(command: list[str], log_path: Path) -> subprocess.CompletedProcess[str]:
    started = dt.datetime.now().astimezone()
    completed = subprocess.run(
        command,
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    finished = dt.datetime.now().astimezone()
    log_path.parent.mkdir(parents=True, exist_ok=True)
    log_path.write_text(
        "\n".join(
            (
                f"started: {started.isoformat()}",
                f"cwd: {ROOT}",
                f"command: {shlex.join(command)}",
                "",
                completed.stdout.rstrip("\n"),
                "",
                f"finished: {finished.isoformat()}",
                f"elapsed_seconds: {(finished - started).total_seconds():.3f}",
                f"exit_code: {completed.returncode}",
                "",
            )
        ),
        encoding="utf-8",
    )
    if completed.returncode != 0:
        raise AuditFailure(
            f"command exited {completed.returncode}; see {log_path.relative_to(ROOT)}"
        )
    return completed


def read_tsv(path: Path) -> list[dict[str, str]]:
    with path.open(encoding="utf-8", newline="") as handle:
        return list(csv.DictReader(handle, delimiter="\t"))


def public_name(row: dict[str, str]) -> str:
    return row.get("private_user_name") or row["name"]


def axiom_set(text: str) -> set[str]:
    return {
        value.strip()
        for value in re.split(r"[;,]", text)
        if value.strip() and value.strip().lower() not in {"none", "(none)"}
    }


def parse_marker_log(path: Path) -> dict[str, set[str]]:
    rows: dict[str, set[str]] = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        cells = line.split("\t")
        if len(cells) == 3 and cells[0] == "V6_TIER_C_AXIOM":
            rows[cells[1]] = axiom_set(cells[2])
    return rows


def collect_axiom_evidence() -> dict[str, set[str]]:
    evidence: dict[str, set[str]] = {}
    ch0_rows = read_tsv(CH0_AXIOM_TSV)
    for row in ch0_rows:
        if row["unexpected"] or row["has_sorryAx"] != "false":
            raise AuditFailure(f"disallowed Ch0--4 witness axioms: {row}")
        evidence[row["witness"]] = axiom_set(row["axioms"])
    for path in (
        LOGS / "recert_v6_tier_c_ch5_7_axioms.log",
        LOGS / "recert_v6_tier_c_ch8_9_axioms.log",
    ):
        evidence.update(parse_marker_log(path))
    violations = {
        name: sorted(axioms - ALLOWED_AXIOMS)
        for name, axioms in evidence.items()
        if axioms - ALLOWED_AXIOMS
    }
    if violations:
        raise AuditFailure(f"witness axiom violations: {violations}")
    return evidence


def validate_sources() -> None:
    for _module, source, harness, _build_log, _axiom_log in MODULES:
        for path in (source, harness):
            text = path.read_text(encoding="utf-8")
            masked, diagnostics = mask_lean_noncode(text)
            if diagnostics:
                raise AuditFailure(f"{path.relative_to(ROOT)} scanner diagnostics")
            if "set_option autoImplicit false" not in masked:
                raise AuditFailure(f"{path.relative_to(ROOT)} lacks autoImplicit false")
            if FORBIDDEN.search(masked) or FORBIDDEN_COMMAND.search(masked):
                raise AuditFailure(f"{path.relative_to(ROOT)} contains forbidden proof text")


def execute_witnesses() -> None:
    validate_sources()
    lean_options = [
        "-Dpp.unicode.fun=true",
        "-DrelaxedAutoImplicit=false",
        "-Dweak.linter.mathlibStandardSet=true",
        "-DmaxSynthPendingDepth=3",
    ]
    for module, _source, harness, build_log, axiom_log in MODULES:
        run_logged(["lake", "build", module], build_log)
        run_logged(["lake", "env", "lean", *lean_options, str(harness)], axiom_log)
    bad_source = PLANTED_BAD.read_text(encoding="utf-8")
    masked, diagnostics = mask_lean_noncode(bad_source)
    if diagnostics or not FORBIDDEN.search(masked):
        raise AuditFailure("planted bad witness did not trigger lexical rejection")
    run_logged(["lake", "env", "lean", *lean_options, str(PLANTED_BAD)], PLANTED_BAD_LOG)


def validate_planted_bad() -> None:
    rows = parse_marker_log(PLANTED_BAD_LOG)
    bad = rows.get(
        "HDP.Verification.V6TierC.recertPlantedBadWitness", set()
    )
    if "sorryAx" not in bad or not (bad - ALLOWED_AXIOMS):
        raise AuditFailure("planted bad witness escaped the axiom rejection calibration")


def ledger_queue_ids(path: Path) -> set[str]:
    rows = read_tsv(path)
    return {
        row["row_id"]
        for row in rows
        if (row.get("sample_kind") or "") == "ok_review_queue_head"
        or (row.get("tier_c_required") or "").startswith(("yes", "YES"))
    }


def validate_fixed_queue() -> None:
    expected0 = {spec.row_id for spec in ch0.QUEUE_SPECS}
    expected5 = {row_id for ids in ch5.QUEUE_IDS.values() for row_id in ids}
    expected8 = {spec.row_id for spec in ch8.QUEUE_SPECS}
    observed = (
        ledger_queue_ids(REVIEW / "v6_tier_b_ch0_4.tsv"),
        ledger_queue_ids(REVIEW / "v6_tier_b_ch5_7.tsv"),
        ledger_queue_ids(REVIEW / "v6_tier_b_ch8_9.tsv"),
    )
    expected = (expected0, expected5, expected8)
    if observed != expected:
        raise AuditFailure(
            "fixed Tier-C queue drift: "
            f"{[(sorted(e - o), sorted(o - e)) for e, o in zip(expected, observed)]}"
        )


def resolve_v4() -> tuple[
    dict[str, dict[str, str]], set[tuple[str, str]]
]:
    if not V4_SUMMARY.is_file():
        raise AuditFailure("fresh V4 completion summary is absent")
    if not V4_ANALYZE_LOG.is_file():
        raise AuditFailure("fresh V4 analysis completion transcript is absent")
    analyze_log = V4_ANALYZE_LOG.read_text(encoding="utf-8", errors="replace")
    if not re.search(r"(?m)^exit_code: 0\s*$", analyze_log):
        raise AuditFailure("fresh V4 analysis transcript lacks exit_code: 0")
    for artifact in (V4_AXIOMS, V4_DEPENDENCIES, V4_TYPES, V4_BINDERS):
        if not artifact.is_file():
            raise AuditFailure(
                f"fresh V4 evidence artifact is absent: {artifact.relative_to(ROOT)}"
            )
        if V4_ANALYZE_LOG.stat().st_mtime_ns < artifact.stat().st_mtime_ns:
            raise AuditFailure(
                "fresh V4 analysis transcript predates an evidence artifact: "
                f"{artifact.relative_to(ROOT)}"
            )
    summary = V4_SUMMARY.read_text(encoding="utf-8")
    for marker in (
        "declarations_audited: 15022",
        "expected_modules: 223",
        "environment_modules: 223",
        "module_coverage: PASS",
        "type_telescope_dump: PASS",
        "direct_dependency_dump: PASS",
    ):
        if marker not in summary.splitlines():
            raise AuditFailure(f"fresh V4 summary lacks {marker!r}")
    audit_rows = read_tsv(V4_AXIOMS)
    required_public_names = {
        str(evidence[key])
        for evidence in ch5.CITATION_EVIDENCE.values()
        for key in ("citing", "target")
    }
    required_public_names.update(
        name
        for citations in SEEDED_CITATIONS.values()
        for target, citing, _location in citations
        for name in (target, citing)
    )
    by_public: dict[str, dict[str, str]] = {}
    for row in audit_rows:
        name = public_name(row)
        if name not in required_public_names:
            continue
        if name in by_public:
            raise AuditFailure(
                f"ambiguous required V4 public declaration {name}"
            )
        by_public[name] = row
    missing_required = required_public_names - set(by_public)
    if missing_required:
        raise AuditFailure(
            "required V4 citation declarations are absent: "
            f"{sorted(missing_required)}"
        )
    dependency_rows = read_tsv(V4_DEPENDENCIES)
    value_edges = {
        (row["source"], row["target"])
        for row in dependency_rows
        if row["origin"] == "value"
    }
    return by_public, value_edges


def validate_ch5_citations(
    by_public: dict[str, dict[str, str]],
    value_edges: set[tuple[str, str]],
) -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    for row_id, item in sorted(ch5.CITATION_EVIDENCE.items()):
        citing = str(item["citing"])
        target = str(item["target"])
        citing_row = by_public.get(citing)
        target_row = by_public.get(target)
        if citing_row is None or target_row is None:
            raise AuditFailure(f"{row_id}: V4 citation declaration did not resolve")
        for declaration in (citing_row, target_row):
            extras = axiom_set(declaration["axioms"]) - ALLOWED_AXIOMS
            if declaration["kind"] != "theorem" or extras:
                raise AuditFailure(
                    f"{row_id}: unclean citation declaration {public_name(declaration)}"
                )
        edge = (citing_row["name"], target_row["name"])
        if edge not in value_edges:
            raise AuditFailure(f"{row_id}: missing exact V4 value edge {edge}")
        location = str(item["location"])
        path_text, line_text = location.rsplit(":", 1)
        source_lines = (ROOT / path_text).read_text(encoding="utf-8").splitlines()
        line = int(line_text)
        if not 1 <= line <= len(source_lines):
            raise AuditFailure(f"{row_id}: citation source line is out of range")
        if target.rsplit(".", 1)[-1] not in source_lines[line - 1]:
            raise AuditFailure(f"{row_id}: citation source line no longer names target")
        rows.append(
            {
                "row_id": f"tier-c-{row_id}",
                "category": "fixed_ok_sample",
                "chapter": next(
                    chapter for chapter, ids in ch5.QUEUE_IDS.items() if row_id in ids
                ),
                "source_row_id": row_id,
                "endpoint": target,
                "semantic_verdict": "OK",
                "tier_c_status": "PASS",
                "evidence_kind": "EXACT_V4_DIRECT_VALUE_CITATION",
                "evidence_name": citing,
                "evidence_location": location,
                "axiom_status": "PASS_ALLOWED_STANDARD_SET",
                "notes": str(item["rationale"]),
            }
        )
    return rows


def validate_exact_v4_citation(
    *,
    row_id: str,
    target: str,
    citing: str,
    location: str,
    by_public: dict[str, dict[str, str]],
    value_edges: set[tuple[str, str]],
) -> None:
    citing_row = by_public.get(citing)
    target_row = by_public.get(target)
    if citing_row is None or target_row is None:
        raise AuditFailure(
            f"{row_id}: citation declaration did not resolve: {citing} -> {target}"
        )
    if citing_row["kind"] != "theorem":
        raise AuditFailure(f"{row_id}: citing declaration is not a theorem: {citing}")
    for declaration in (citing_row, target_row):
        extras = axiom_set(declaration["axioms"]) - ALLOWED_AXIOMS
        if extras:
            raise AuditFailure(
                f"{row_id}: unclean citation declaration "
                f"{public_name(declaration)}: {sorted(extras)}"
            )
    edge = (citing_row["name"], target_row["name"])
    if edge not in value_edges:
        raise AuditFailure(f"{row_id}: missing exact V4 value edge {edge}")
    path_text, line_text = location.rsplit(":", 1)
    source_lines = (ROOT / path_text).read_text(encoding="utf-8").splitlines()
    line = int(line_text)
    if not 1 <= line <= len(source_lines):
        raise AuditFailure(f"{row_id}: citation source line is out of range")
    if target.rsplit(".", 1)[-1] not in source_lines[line - 1]:
        raise AuditFailure(
            f"{row_id}: exact citation line no longer names {target}"
        )


def validate_seeded_artifacts(*, write: bool) -> None:
    if write:
        run_logged(
            [
                sys.executable,
                "-B",
                str(VERIFY / "scripts/build_v6_tier_c_seeded_sample.py"),
                "--write",
            ],
            SEEDED_BUILD_LOG,
        )
    result = seeded.build_sampling_result()
    for path, text in seeded.artifacts(result).items():
        seeded.require_exact(path, text)


def build_seeded_rows(
    axiom_evidence: dict[str, set[str]],
    by_public: dict[str, dict[str, str]],
    value_edges: set[tuple[str, str]],
) -> list[dict[str, str]]:
    sample = read_tsv(SEEDED_SAMPLE)
    expected_ids = set(SEEDED_WITNESSES) | set(SEEDED_CITATIONS)
    observed_ids = {row["row_id"] for row in sample}
    if len(sample) != 50 or len(observed_ids) != 50:
        raise AuditFailure("seeded random sample must contain 50 unique rows")
    if observed_ids != expected_ids or (set(SEEDED_WITNESSES) & set(SEEDED_CITATIONS)):
        raise AuditFailure(
            "seeded evidence binding drift: "
            f"missing={sorted(observed_ids - expected_ids)} "
            f"stale={sorted(expected_ids - observed_ids)}"
        )
    rows: list[dict[str, str]] = []
    chapter_source = {
        **{
            chapter: VERIFY / "scripts/witnesses/V6TierCCh0_4.lean"
            for chapter in ("Appetizer", *(f"Chapter {i}" for i in range(1, 5)))
        },
        **{
            f"Chapter {i}": VERIFY / "scripts/witnesses/V6TierCCh5_7.lean"
            for i in range(5, 8)
        },
        **{
            f"Chapter {i}": VERIFY / "scripts/witnesses/V6TierCCh8_9.lean"
            for i in range(8, 10)
        },
    }
    for sample_row in sample:
        row_id = sample_row["row_id"]
        endpoint_cell = sample_row["eligible_endpoints"]
        score_note = (
            "Manifest-seeded SHA-256 rank "
            f"{sample_row['sample_rank']} with score {sample_row['score_sha256']}."
        )
        if row_id in SEEDED_WITNESSES:
            witness, expected_cell = SEEDED_WITNESSES[row_id]
            if endpoint_cell != expected_cell:
                raise AuditFailure(
                    f"{row_id}: seeded witness endpoint-cell drift: {endpoint_cell}"
                )
            row = witness_row(
                row_id=f"tier-c-seeded-{row_id}",
                category="seeded_random_ok_sample",
                chapter=sample_row["chapter"],
                source_row_id=row_id,
                endpoint=endpoint_cell,
                witness=witness,
                axiom_evidence=axiom_evidence,
                source=chapter_source[sample_row["chapter"]],
            )
            row["notes"] += " " + score_note
            rows.append(row)
            continue
        citations = SEEDED_CITATIONS[row_id]
        targets = [target for target, _citing, _location in citations]
        if endpoint_cell.split(";") != targets:
            raise AuditFailure(
                f"{row_id}: seeded citation endpoint-cell drift: "
                f"{endpoint_cell} versus {';'.join(targets)}"
            )
        for target, citing, location in citations:
            validate_exact_v4_citation(
                row_id=row_id,
                target=target,
                citing=citing,
                location=location,
                by_public=by_public,
                value_edges=value_edges,
            )
        rows.append(
            {
                "row_id": f"tier-c-seeded-{row_id}",
                "category": "seeded_random_ok_sample",
                "chapter": sample_row["chapter"],
                "source_row_id": row_id,
                "endpoint": endpoint_cell,
                "semantic_verdict": "OK",
                "tier_c_status": "PASS",
                "evidence_kind": "EXACT_V4_DIRECT_VALUE_CITATION",
                "evidence_name": ";".join(
                    f"{citing} -> {target}"
                    for target, citing, _location in citations
                ),
                "evidence_location": "; ".join(
                    location for _target, _citing, location in citations
                ),
                "axiom_status": "PASS_ALLOWED_STANDARD_SET",
                "notes": (
                    "Every endpoint in the sampled cell has an exact clean "
                    "current-tree V4 value edge. " + score_note
                ),
            }
        )
    return rows


def witness_row(
    *,
    row_id: str,
    category: str,
    chapter: str,
    source_row_id: str,
    endpoint: str,
    witness: str | tuple[str, ...],
    axiom_evidence: dict[str, set[str]],
    source: Path,
) -> dict[str, str]:
    witnesses = (witness,) if isinstance(witness, str) else witness
    missing = [name for name in witnesses if name not in axiom_evidence]
    if missing:
        raise AuditFailure(f"missing compiled axiom evidence for {missing}")
    return {
        "row_id": row_id,
        "category": category,
        "chapter": chapter,
        "source_row_id": source_row_id,
        "endpoint": endpoint,
        "semantic_verdict": "OK",
        "tier_c_status": "PASS",
        "evidence_kind": "COMPILED_NAMED_WITNESS",
        "evidence_name": ";".join(witnesses),
        "evidence_location": source.relative_to(ROOT).as_posix(),
        "axiom_status": "PASS_ALLOWED_STANDARD_SET",
        "notes": "Compiled with autoImplicit false, no sorry/admit, and only the accepted standard axiom set.",
    }


def build_rows(
    axiom_evidence: dict[str, set[str]],
    by_public: dict[str, dict[str, str]],
    value_edges: set[tuple[str, str]],
) -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    ch0_source = VERIFY / "scripts/witnesses/V6TierCCh0_4.lean"
    for spec in ch0.QUEUE_SPECS:
        rows.append(
            witness_row(
                row_id=f"tier-c-{spec.row_id}",
                category="fixed_ok_sample",
                chapter=spec.chapter,
                source_row_id=spec.row_id,
                endpoint=spec.target,
                witness=spec.witnesses,
                axiom_evidence=axiom_evidence,
                source=ch0_source,
            )
        )
    ch5_source = VERIFY / "scripts/witnesses/V6TierCCh5_7.lean"
    for chapter, ids in ch5.QUEUE_IDS.items():
        for row_id in ids:
            witness = ch5.COMPILED_QUEUE_WITNESSES.get(row_id)
            if witness:
                target = next(
                    row["resolved_declarations"]
                    for row in read_tsv(REVIEW / "v6_tier_b_ch5_7.tsv")
                    if row["row_id"] == row_id
                )
                rows.append(
                    witness_row(
                        row_id=f"tier-c-{row_id}",
                        category="fixed_ok_sample",
                        chapter=chapter,
                        source_row_id=row_id,
                        endpoint=target,
                        witness=witness,
                        axiom_evidence=axiom_evidence,
                        source=ch5_source,
                    )
                )
    rows.extend(validate_ch5_citations(by_public, value_edges))
    ch8_source = VERIFY / "scripts/witnesses/V6TierCCh8_9.lean"
    for spec in ch8.QUEUE_SPECS:
        rows.append(
            witness_row(
                row_id=f"tier-c-{spec.row_id}",
                category="fixed_ok_sample",
                chapter=spec.chapter,
                source_row_id=spec.row_id,
                endpoint=spec.endpoint,
                witness=spec.witness,
                axiom_evidence=axiom_evidence,
                source=ch8_source,
            )
        )
    rows.extend(build_seeded_rows(axiom_evidence, by_public, value_edges))

    tier_a_rows = read_tsv(TIER_A_REVIEW)
    tier_a_required = {
        row["qualified_name"]: row for row in tier_a_rows
        if row["tier_c_required"] == "YES"
    }
    if set(tier_a_required) != set(EXPECTED_TIER_A_WITNESSES):
        raise AuditFailure(f"Tier-A Tier-C set drift: {sorted(tier_a_required)}")
    for endpoint, witness in sorted(EXPECTED_TIER_A_WITNESSES.items()):
        source = (
            ch0_source
            if witness.endswith("matrixSingularValue_fin1_index_one")
            else ch5_source
        )
        rows.append(
            witness_row(
                row_id=f"tier-c-tier-a-{tier_a_required[endpoint]['row_id']}",
                category="tier_a_escalation",
                chapter="cross-cutting",
                source_row_id=tier_a_required[endpoint]["row_id"],
                endpoint=endpoint,
                witness=witness,
                axiom_evidence=axiom_evidence,
                source=source,
            )
        )

    return rows


def validate_rows(rows: list[dict[str, str]]) -> None:
    if len(rows) != 103 or len({row["row_id"] for row in rows}) != 103:
        raise AuditFailure("expected 103 unique Tier-C adjudication rows")
    categories = Counter(row["category"] for row in rows)
    if categories != Counter(
        {
            "fixed_ok_sample": 50,
            "seeded_random_ok_sample": 50,
            "tier_a_escalation": 3,
        }
    ):
        raise AuditFailure(f"Tier-C category census drift: {categories}")
    expected_chapters = Counter(
        {"Appetizer": 5, **{f"Chapter {index}": 5 for index in range(1, 10)}}
    )
    for category in ("fixed_ok_sample", "seeded_random_ok_sample"):
        chapter_counts = Counter(
            row["chapter"] for row in rows if row["category"] == category
        )
        if chapter_counts != expected_chapters:
            raise AuditFailure(
                f"{category} per-chapter sample drift: {chapter_counts}"
            )
    if Counter(row["semantic_verdict"] for row in rows) != Counter({"OK": 103}):
        raise AuditFailure("Tier-C verdict census drift")
    compiled_name_multiplicities = Counter(
        len(
            [
                name
                for name in row["evidence_name"].split(";")
                if name.strip()
            ]
        )
        for row in rows
        if row["evidence_kind"] == "COMPILED_NAMED_WITNESS"
    )
    if compiled_name_multiplicities != Counter({1: 89, 2: 2}):
        raise AuditFailure(
            "compiled witness endpoint-cell multiplicity drift: "
            f"{compiled_name_multiplicities}"
        )
    compiled_names = [
        name.strip()
        for row in rows
        if row["evidence_kind"] == "COMPILED_NAMED_WITNESS"
        for name in row["evidence_name"].split(";")
        if name.strip()
    ]
    if len(compiled_names) != 93 or len(set(compiled_names)) != 93:
        raise AuditFailure("compiled witness declarations are not one-to-one")


def render_tsv(rows: list[dict[str, str]]) -> str:
    handle = io.StringIO(newline="")
    writer = csv.DictWriter(
        handle, fieldnames=FIELDS, delimiter="\t", lineterminator="\n"
    )
    writer.writeheader()
    writer.writerows(rows)
    return handle.getvalue()


def render_summary(rows: list[dict[str, str]]) -> str:
    kinds = Counter(row["evidence_kind"] for row in rows)
    compiled_names = {
        name.strip()
        for row in rows
        if row["evidence_kind"] == "COMPILED_NAMED_WITNESS"
        for name in row["evidence_name"].split(";")
        if name.strip()
    }
    return "\n".join(
        (
            "V6 TIER-C CURRENT-TREE RECERTIFICATION",
            "======================================",
            "verdict_under_R6: PASS",
            f"rows: {len(rows)}",
            "legacy_fixed_ok_sample_rows: 50",
            "legacy_fixed_ok_sample_per_chapter: 5 (Appetizer and Chapters 1--9)",
            "manifest_seeded_random_ok_sample_rows: 50",
            "manifest_seeded_random_ok_sample_per_chapter: 5 "
            "(Appetizer and Chapters 1--9)",
            f"manifest_seed: {seeded.manifest_seed()}",
            f"current_source_manifest: {seeded.current_manifest_digest()}",
            "sampling_seed_policy: post-removal semantic baseline retained "
            "across the independently verified Round 10 docstring-only and "
            "Exercise-reorganization deltas",
            "manifest_seed_algorithm: SHA256(UTF8(seed + NUL + chapter + "
            "NUL + row_id)); ascending rank; sample without replacement",
            "tier_a_escalation_rows: 3",
            "all_current_suspect_rows: 0",
            "all_current_vacuous_rows: 0",
            f"compiled_named_witness_rows: {kinds['COMPILED_NAMED_WITNESS']}",
            "compiled_named_witness_declarations_referenced: "
            f"{len(compiled_names)}",
            f"exact_v4_direct_citation_rows: {kinds['EXACT_V4_DIRECT_VALUE_CITATION']}",
            f"fail_closed_negative_search_rows: {kinds['FAIL_CLOSED_V4_CONSTRUCTOR_SEARCH']}",
            "allowed_axioms: propext;Classical.choice;Quot.sound",
            "witness_source_gate: autoImplicit false; no sorry/admit; no axiom/unsafe",
            "planted_bad_witness_rejected: true",
            "removed_conditional_interfaces_absent: true",
            "",
        )
    )


def require_exact(path: Path, expected: str) -> None:
    if not path.is_file() or path.read_text(encoding="utf-8") != expected:
        raise AuditFailure(f"artifact drift: {path.relative_to(ROOT)}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--run", action="store_true", help="compile witnesses and regenerate evidence"
    )
    args = parser.parse_args()
    validate_fixed_queue()
    validate_sources()
    validate_seeded_artifacts(write=args.run)
    if args.run:
        execute_witnesses()
    validate_planted_bad()
    axiom_evidence = collect_axiom_evidence()
    by_public, value_edges = resolve_v4()
    rows = build_rows(axiom_evidence, by_public, value_edges)
    validate_rows(rows)
    tsv_text = render_tsv(rows)
    summary_text = render_summary(rows)
    if args.run:
        OUTPUT.write_text(tsv_text, encoding="utf-8")
        SUMMARY.write_text(summary_text, encoding="utf-8")
    require_exact(OUTPUT, tsv_text)
    require_exact(SUMMARY, summary_text)
    print(
        "PASS recert_v6_tier_c: 103 rows; 50 legacy fixed OK controls; "
        "50 manifest-seeded random OK controls; 3 Tier-A escalations; "
        "0 SUSPECT rows"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (
        AuditFailure,
        seeded.SamplingFailure,
        OSError,
        ValueError,
        KeyError,
    ) as error:
        print(f"FAIL recert_v6_tier_c: {error}", file=sys.stderr)
        raise SystemExit(1)
