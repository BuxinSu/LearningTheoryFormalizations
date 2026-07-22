#!/usr/bin/env python3
"""Build and verify the V6 Tier-C witnesses for Appetizer--Chapter 4."""

from __future__ import annotations

import argparse
import csv
import hashlib
import io
import json
import os
import re
import shlex
import subprocess
import sys
import textwrap
from dataclasses import dataclass
from pathlib import Path
from typing import Sequence

from lean_source_scanner import mask_lean_noncode
from v6_tier_a_scanner import (
    AUTO_BOUND_REASON_ID,
    validate_v4_join_contract,
)


ROOT = Path(__file__).resolve().parents[3]
VERIFY = Path("HighDimensionalProbability/Verification")
WITNESS_REL = (
    VERIFY / "scripts/witnesses/V6TierCCh0_4.lean"
)
AXIOM_HARNESS_REL = (
    VERIFY / "scripts/witnesses/V6TierCCh0_4Axioms.lean"
)
QUEUE_REL = VERIFY / "review/v6_tier_b_ch0_4.tsv"
LEDGER_REL = VERIFY / "review/v6_tier_c_ch0_4.tsv"
SUMMARY_REL = VERIFY / "review/v6_tier_c_ch0_4_summary.txt"
LOG_DIR_REL = VERIFY / "logs"
SCAN_JSON_REL = LOG_DIR_REL / "v6_tier_c_ch0_4_tier_a_scan.json"
SCAN_LOG_REL = LOG_DIR_REL / "v6_tier_c_ch0_4_tier_a_scan.log"
V4_TYPES_REL = LOG_DIR_REL / "recert_axiom_declaration_types.tsv"
V4_BINDERS_REL = LOG_DIR_REL / "recert_axiom_declaration_binders.tsv"
V4_AXIOMS_REL = LOG_DIR_REL / "recert_axiom_audit.tsv"
V4_DIRECT_DEPENDENCIES_REL = (
    LOG_DIR_REL / "recert_axiom_direct_dependencies.tsv"
)
V4_BUILD_LOG_REL = LOG_DIR_REL / "recert_axiom_audit_build.log"
V4_SUMMARY_REL = LOG_DIR_REL / "recert_axiom_summary.txt"
V4_MODULES_REL = LOG_DIR_REL / "recert_axiom_modules.txt"
V4_COVERAGE_REL = LOG_DIR_REL / "recert_axiom_module_coverage.txt"
EXPECTED_TIER_A_DECLARATION_COUNT = 7_411
EXPECTED_V4_MODULE_COUNT = 223
BUILD_LOG_REL = LOG_DIR_REL / "v6_tier_c_ch0_4_build.log"
AXIOM_LOG_REL = LOG_DIR_REL / "v6_tier_c_ch0_4_axiom_build.log"
AXIOM_TSV_REL = LOG_DIR_REL / "recert_v6_tier_c_ch0_4_axioms.tsv"
RESULT_JSON_REL = LOG_DIR_REL / "v6_tier_c_ch0_4_results.json"
RUNNER_LOG_REL = LOG_DIR_REL / "v6_tier_c_ch0_4_runner.log"

# This calibration was planted once for the Chapters 5--7 suite.  This suite
# reuses that exact source and raw-log location instead of planting another.
PLANTED_BAD_REL = Path(".audit_work/verification/V6TierCPlantedBad.lean")
PLANTED_BAD_LOG_REL = LOG_DIR_REL / "v6_tier_c_ch5_7_planted_bad.log"

WITNESS_MODULE = (
    "HighDimensionalProbability.Verification.scripts.witnesses."
    "V6TierCCh0_4"
)
LEAN_OPTIONS = (
    "-Dpp.unicode.fun=true",
    "-DrelaxedAutoImplicit=false",
    "-Dweak.linter.mathlibStandardSet=true",
    "-DmaxSynthPendingDepth=3",
)
ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
FORBIDDEN_IMPORT = "MatrixConcentration.Appendix_RosenthalPinelis"
FORBIDDEN_PROOF_TOKEN = re.compile(r"\b(?:sorry|admit)\b")
DECLARATION = re.compile(
    r"(?m)^[ \t]*(?:theorem|alias)[ \t]+([A-Za-z_][A-Za-z0-9_']*)"
)
REMOVED_BORELL_INTERFACES = (
    "BorellConvexBodyPsiOnePrinciple",
    "convexBodyUniform_marginal_subExponential_of_borell",
    "borellConvexBodyPsiOnePrinciple_external",
)
RETAINED_BORELL_DOMAIN_DECLARATIONS = (
    "convexBodyUniformMeasure",
    "convexBodyUniformMeasure_isProbability",
    "convexBodyUniformVector_measurable",
    "convexBodyUniformVector_memLp_two",
    "convexBodyUniformVector_isIsotropicRandomVector",
)


@dataclass(frozen=True)
class QueueSpec:
    row_id: str
    chapter: str
    rank: int
    target: str
    mode: str
    candidate: str
    witnesses: tuple[str, ...]


PREFIX = "HDP.Verification.V6TierC."
WITNESS_BY_CITATION = "WITNESS-BY-CITATION"
CONCRETE_MODEL = "CONCRETE-NONDEGENERATE-MODEL"
QUEUE_SPECS = (
    QueueSpec(
        "census-267f53840f7e9669", "Appetizer", 1,
        "HDP.Chapter0.polytope_volume_remark_0_0_5", CONCRETE_MODEL, "",
        (PREFIX + "queue_ch0_polytope_volume_remark_constant_two",),
    ),
    QueueSpec(
        "census-3a5e7fbc0e9c1199", "Appetizer", 2,
        "HDP.Chapter0.exists_polytope_cover", WITNESS_BY_CITATION,
        "HDP.Chapter0.polytope_volume_le_card_mul_ball",
        (PREFIX + "queue_ch0_polytope_cover_downstream",),
    ),
    QueueSpec(
        "census-b5a26cf1bfc1ad02", "Appetizer", 3,
        "HDP.Chapter0.polytope_volume_equation_0_3", WITNESS_BY_CITATION,
        "HDP.Chapter0.polytope_volume_le_theorem_0_0_4",
        (PREFIX + "queue_ch0_polytope_equation_downstream",),
    ),
    QueueSpec(
        "census-0407bd4f173c5018", "Appetizer", 4,
        "HDP.Chapter0.polytope_volume_theorem_0_0_4", CONCRETE_MODEL, "",
        (PREFIX + "queue_ch0_polytope_volume_fin1_two_vertices",),
    ),
    QueueSpec(
        "census-6d302c76844756f6", "Appetizer", 5,
        "HDP.Chapter0.approximate_caratheodory", WITNESS_BY_CITATION,
        "HDP.Chapter0.exists_polytope_cover",
        (PREFIX + "queue_ch0_approximate_caratheodory_downstream",),
    ),
    QueueSpec(
        "census-9f31959287a10a6f", "Chapter 1", 1,
        "HDP.Chapter1.example_1_4_2_calc", WITNESS_BY_CITATION,
        "HDP.Chapter1.example_1_4_2",
        (PREFIX + "queue_ch1_example_1_4_2_calc_downstream",),
    ),
    QueueSpec(
        "census-2d26ccb495448c13", "Chapter 1", 2,
        "HDP.Chapter1.union_bound", WITNESS_BY_CITATION,
        "HDP.Chapter1.union_bound_fintype",
        (PREFIX + "queue_ch1_union_bound_downstream",),
    ),
    QueueSpec(
        "census-da73b26c72381b81", "Chapter 1", 3,
        "HDP.Chapter1.bookCDF", WITNESS_BY_CITATION,
        "HDP.Chapter1.tail_eq_one_sub_cdf",
        (PREFIX + "queue_ch1_bookCDF_downstream",),
    ),
    QueueSpec(
        "census-fec3d811788b995d", "Chapter 1", 4,
        "HDP.Chapter1.stirling_approximation", WITNESS_BY_CITATION,
        "HDP.Chapter1.stirling_ratio_tendsto_one",
        (PREFIX + "queue_ch1_stirling_downstream",),
    ),
    QueueSpec(
        "census-e21f4bd7ac0aa1f2", "Chapter 1", 5,
        "HDP.Chapter1.factorial_robbins_two_sided", CONCRETE_MODEL, "",
        (PREFIX + "queue_ch1_robbins_stirling_n_two",),
    ),
    QueueSpec(
        "census-9f946e24c21c0d16", "Chapter 2", 1,
        "HDP.psi2Norm_eq_zero_iff", WITNESS_BY_CITATION,
        "HDP.psi2Norm_sum_sq_le",
        (PREFIX + "queue_ch2_psi2_zero_downstream",),
    ),
    QueueSpec(
        "census-eb2cb15c80bf5d1d", "Chapter 2", 2,
        "HDP.Chapter2.medianOfMeans_explicit", WITNESS_BY_CITATION,
        "HDP.Chapter2.medianOfMeans_theorem_2_4_1",
        (PREFIX + "queue_ch2_median_of_means_downstream",),
    ),
    QueueSpec(
        "census-2122a3c307b06378", "Chapter 2", 3,
        "HDP.pythagorean_identity", WITNESS_BY_CITATION, "HDP.khintchine",
        (PREFIX + "queue_ch2_pythagorean_downstream",),
    ),
    QueueSpec(
        "census-5ca87340a1da981b", "Chapter 2", 4,
        "HDP.SubGaussian.tail_bound", WITNESS_BY_CITATION,
        "HDP.subgaussian_hoeffding",
        (PREFIX + "queue_ch2_tail_bound_downstream",),
    ),
    QueueSpec(
        "census-245bfc29931f8f1f", "Chapter 2", 5,
        "HDP.psi2Norm_sum_sq_le", WITNESS_BY_CITATION,
        "HDP.subgaussian_hoeffding",
        (PREFIX + "queue_ch2_psi2_sum_downstream",),
    ),
    QueueSpec(
        "census-224df4d887e11824", "Chapter 3", 1,
        "HDP.map_gaussianDirection_stdGaussian", WITNESS_BY_CITATION,
        "HDP.Chapter3.map_projectiveGaussianDirection",
        (PREFIX + "queue_ch3_gaussian_direction_downstream",),
    ),
    QueueSpec(
        "census-d718684b7c04a068", "Chapter 3", 2,
        "HDP.SimpleGraph.cutSize", WITNESS_BY_CITATION,
        "HDP.Chapter3.graphCutObjective_eq_cutValue",
        (PREFIX + "queue_ch3_cut_size_downstream",),
    ),
    QueueSpec(
        "census-2b0c5af75c707385", "Chapter 3", 3,
        "HDP.Chapter3.pca_kth_component_le", WITNESS_BY_CITATION,
        "HDP.Chapter3.pca_kth_maximum_principle",
        (PREFIX + "queue_ch3_pca_kth_downstream",),
    ),
    QueueSpec(
        "census-9cd803067f94be16", "Chapter 3", 4,
        "HDP.Chapter3.relaxation_is_sdp", WITNESS_BY_CITATION,
        "HDP.Chapter3.exercise_3_52a",
        (PREFIX + "queue_ch3_relaxation_downstream",),
    ),
    QueueSpec(
        "census-c103da4532e6de9a", "Chapter 3", 5,
        "HDP.Chapter3.isotropic_finiteShannonEntropy_and_support_lower_bounds; "
        "HDP.Chapter3.isotropic_subgaussian_finite_support_entropy_and_card",
        CONCRETE_MODEL, "",
        (
            PREFIX + "queue_ch3_isotropic_entropy_fin2_model",
            PREFIX + "queue_ch3_isotropic_finite_support_fin2_model",
        ),
    ),
    QueueSpec(
        "census-f0adfeea6d016929", "Chapter 4", 1,
        "HDP.Chapter4.remark_4_7_3", CONCRETE_MODEL, "",
        (PREFIX + "queue_ch4_covariance_tail_gaussian_mixture_fin1",),
    ),
    QueueSpec(
        "census-8398f0da580bf50e", "Chapter 4", 2,
        "HDP.Chapter4.lemma_4_1_10", CONCRETE_MODEL, "",
        (PREFIX + "queue_ch4_orthogonal_invariance_fin1_nonzero",),
    ),
    QueueSpec(
        "census-07ea02d9a6c34534", "Chapter 4", 3,
        "HDP.Chapter4.theorem_4_6_1_gram", WITNESS_BY_CITATION,
        "HDP.Chapter4.theorem_4_6_1_singular_normalized",
        (PREFIX + "queue_ch4_gram_tail_downstream",),
    ),
    QueueSpec(
        "census-b72ca80e04954340", "Chapter 4", 4,
        "HDP.Chapter4.remark_4_1_12", CONCRETE_MODEL, "",
        (PREFIX + "queue_ch4_rayleigh_fin1_identity",),
    ),
    QueueSpec(
        "census-b8473c9d92ff7d07", "Chapter 4", 5,
        "HDP.Chapter4.theorem_4_4_3", WITNESS_BY_CITATION,
        "HDP.Chapter4.exercise_4_41a",
        (PREFIX + "queue_ch4_operator_norm_tail_downstream",),
    ),
)

# A concrete-model witness is accepted only when it is a closed declaration
# (no arbitrary data or repeated theorem hypotheses) and its own source block
# contains every row-specific nondegeneracy marker below.  These markers are
# deliberately redundant with the Lean type: they make a future regression
# to a generic wrapper fail before compilation.
CONCRETE_MODEL_CONTRACTS = {
    PREFIX + "queue_ch0_polytope_volume_remark_constant_two": (
        ("HDP.Chapter0.polytope_volume_remark_0_0_5",),
        (
            "fun _ : ℕ ↦ 2",
            "Real.log (2 : ℝ)",
            "tendsto_natCast_atTop_atTop",
        ),
    ),
    PREFIX + "queue_ch0_polytope_volume_fin1_two_vertices": (
        ("HDP.Chapter0.polytope_volume_theorem_0_0_4",),
        ("Fin 1", "e ∈ V", "-e ∈ V", "let V", "{e, -e}"),
    ),
    PREFIX + "queue_ch1_robbins_stirling_n_two": (
        ("HDP.Chapter1.factorial_robbins_two_sided",),
        ("(2 : ℕ)", "(n := 2)", "(by norm_num)"),
    ),
    PREFIX + "queue_ch3_isotropic_entropy_fin2_model": (
        (
            "HDP.Chapter3."
            "isotropic_finiteShannonEntropy_and_support_lower_bounds",
        ),
        (
            "Fin 2",
            "fun _ ↦ (1 / 2 : ℝ)",
            "Function.Injective x",
            "0 < p i",
            "![e, -e]",
        ),
    ),
    PREFIX + "queue_ch3_isotropic_finite_support_fin2_model": (
        (
            "HDP.Chapter3."
            "isotropic_subgaussian_finite_support_entropy_and_card",
        ),
        (
            "Fin 2",
            "uniformOn (Set.univ : Set (Fin 2))",
            "coordinateParsevalFrame 2",
            "coordinateDistribution_isIsotropic 2",
            "Function.Injective X",
            "0 < μ.real {ω}",
        ),
    ),
    PREFIX + "queue_ch4_covariance_tail_gaussian_mixture_fin1": (
        ("HDP.Chapter4.remark_4_7_3",),
        (
            "GaussianMixtureSample 1 1",
            "gaussianMixtureSampleMeasure 1 1",
            "gaussianMixtureAugmentedMatrix",
            "gaussianMixtureFactorMatrix",
            "(K := (4 : ℝ))",
            "(u := (16 : ℝ))",
        ),
    ),
    PREFIX + "queue_ch4_orthogonal_invariance_fin1_nonzero": (
        ("HDP.Chapter4.lemma_4_1_10",),
        ("Fin 1", "(2 : ℝ) •", "orthogonalGroup", "one_mem"),
    ),
    PREFIX + "queue_ch4_rayleigh_fin1_identity": (
        ("HDP.Chapter4.remark_4_1_12",),
        ("Fin 1", "IsGreatest", "Matrix.isHermitian_one"),
    ),
}

EXPECTED_CITATION_EDGES = frozenset(
    (spec.candidate, spec.target)
    for spec in QUEUE_SPECS
    if spec.mode == WITNESS_BY_CITATION
)

TIER_A_WITNESS = (
    PREFIX + "tierA_prelude_matrixSingularValue_fin1_index_one"
)
LEGACY_SEEDED_PREFIX = (
    PREFIX + "seeded_app_finset_convexHull_two_point",
    PREFIX + "seeded_app_convexHull_eq_union_two_point",
)
LEGACY_SEEDED_SUFFIX = tuple(
    PREFIX + name
    for name in (
        "seeded_ch0_polytope_optimizer_exp_one",
        "seeded_ch0_mean_minimizes_rademacher",
        "seeded_ch1_integrated_tail_bernoulli",
        "seeded_ch1_minkowski_two_point",
        "seeded_ch1_expectation_covariance_rademacher",
        "seeded_ch2_rademacher_psi2_attainment",
        "seeded_ch3_sine_feature_fin1",
        "seeded_ch3_tensor_power_fin2_two",
        "seeded_ch3_gaussianRoundingLabel_real",
        "seeded_ch3_unitSphere_fin1_all_endpoints",
        "seeded_ch4_relative_compactness_two_point",
        "seeded_ch4_matrix_form_svd_fin1",
        "seeded_ch4_sbm_expected_adjacency_interior",
    )
)
CURRENT_SEEDED_WITNESSES = tuple(
    PREFIX + name
    for name in (
        "seeded_current_ch0_polytope_optimizer_equation",
        "seeded_current_ch1_norm_expectation_le",
        "seeded_current_ch1_l2InnerRV_and_inner_def",
        "seeded_current_ch1_exercise_1_3b",
        "seeded_current_ch2_exercise_2_40c_gaussian",
        "seeded_current_ch2_exercise_2_8",
        "seeded_current_ch2_central_binomial_asymptotic",
        "seeded_current_ch3_random_graph_cut_half_approximation",
        "seeded_current_ch4_independent_rows",
        "seeded_current_ch4_example_4_3_2",
    )
)
QUEUE_WITNESS_NAMES = tuple(
    witness for spec in QUEUE_SPECS for witness in spec.witnesses
)
WITNESS_NAMES = (
    LEGACY_SEEDED_PREFIX
    + QUEUE_WITNESS_NAMES
    + (TIER_A_WITNESS,)
    + LEGACY_SEEDED_SUFFIX
    + CURRENT_SEEDED_WITNESSES
)
EXPECTED_SHARED_TIER_A = {
    (
        "HighDimensionalProbability/Prelude/Matrix.lean",
        "matrixSingularValue_of_finrank_le",
    )
}


class AuditFailure(RuntimeError):
    pass


def path(relative: Path) -> Path:
    return ROOT / relative


def sha256(relative: Path) -> str:
    return hashlib.sha256(path(relative).read_bytes()).hexdigest()


def write_text(relative: Path, text: str) -> None:
    destination = path(relative)
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(text, encoding="utf-8")


def masked_source(relative: Path) -> str:
    text = path(relative).read_text(encoding="utf-8")
    masked, diagnostics = mask_lean_noncode(text)
    if diagnostics:
        raise AuditFailure(f"{relative}: Lean lexical diagnostics: {diagnostics!r}")
    return masked


def declaration_blocks(code: str) -> dict[str, str]:
    matches = list(DECLARATION.finditer(code))
    blocks: dict[str, str] = {}
    for index, match in enumerate(matches):
        end = (
            matches[index + 1].start()
            if index + 1 < len(matches)
            else len(code)
        )
        name = match.group(1)
        if name in blocks:
            raise AuditFailure(f"duplicate witness declaration {name}")
        blocks[name] = code[match.start():end]
    return blocks


def strip_leading_concrete_data_binders(type_body: str) -> str:
    """Remove leading `let`/`∃` data binders, but not proof wrappers.

    Function arrows are legitimate inside the type of a concrete datum, for
    example `∃ p : Fin 2 → ℝ, ...`.  After those leading data binders have
    been removed, an arrow or a leading universal quantifier is a
    proposition-level wrapper and must be rejected.
    """
    residual = textwrap.dedent(type_body).strip()
    while residual:
        if re.match(r"^let\b", residual):
            lines = residual.splitlines()
            next_top_level = next(
                (
                    index
                    for index, line in enumerate(lines[1:], start=1)
                    if line.strip() and not line[0].isspace()
                ),
                None,
            )
            if next_top_level is None:
                return ""
            residual = "\n".join(lines[next_top_level:]).strip()
            continue
        if re.match(r"^(?:∃|exists\b)", residual):
            depths = {"(": 0, "[": 0, "{": 0}
            closing = {")": "(", "]": "[", "}": "{"}
            comma = None
            for index, char in enumerate(residual):
                if char in depths:
                    depths[char] += 1
                elif char in closing:
                    opener = closing[char]
                    depths[opener] = max(0, depths[opener] - 1)
                elif char == "," and not any(depths.values()):
                    comma = index
                    break
            if comma is None:
                return residual
            residual = textwrap.dedent(residual[comma + 1:]).strip()
            continue
        return residual
    return residual


def validate_concrete_model_block(
    full_name: str,
    block: str,
    targets: Sequence[str],
    markers: Sequence[str],
) -> None:
    local = full_name.rsplit(".", 1)[1]
    if not re.search(
        rf"\Atheorem[ \t]+{re.escape(local)}[ \t]*:",
        block,
    ):
        raise AuditFailure(
            f"{local}: concrete witness must be a closed theorem with no "
            "arbitrary binders before `:`"
        )
    type_text = block.split(":= by", 1)[0]
    type_body = type_text.split(":", 1)[1]
    proposition_body = strip_leading_concrete_data_binders(type_body)
    if (
        re.match(r"^(?:∀|forall\b)", proposition_body) is not None
        or "→" in proposition_body
        or "->" in proposition_body
    ):
        raise AuditFailure(
            f"{local}: concrete witness may not repackage assumptions "
            "as implications"
        )
    if re.search(r"(?m)^[ \t]*alias[ \t]+", block):
        raise AuditFailure(f"{local}: a concrete model may not be an alias")
    if "have _ :=" in block or "have _ : " in block:
        raise AuditFailure(
            f"{local}: ignored-hypothesis wrapper idiom is forbidden"
        )
    missing_targets = [target for target in targets if target not in block]
    if missing_targets:
        raise AuditFailure(
            f"{local}: concrete proof does not apply targets "
            f"{missing_targets!r}"
        )
    missing_markers = [marker for marker in markers if marker not in block]
    if missing_markers:
        raise AuditFailure(
            f"{local}: nondegenerate model markers missing "
            f"{missing_markers!r}"
        )


def check_concrete_model_contracts(main_code: str) -> dict[str, object]:
    blocks = declaration_blocks(main_code)
    for full_name, (targets, markers) in CONCRETE_MODEL_CONTRACTS.items():
        local = full_name.rsplit(".", 1)[1]
        block = blocks.get(local)
        if block is None:
            raise AuditFailure(f"missing concrete-model witness {local}")
        validate_concrete_model_block(
            full_name,
            block,
            targets,
            markers,
        )
    return {
        "closed_concrete_model_declarations": len(
            CONCRETE_MODEL_CONTRACTS
        ),
        "generic_hypothesis_wrappers": 0,
        "nondegeneracy_contracts": "PASS",
    }


def validate_required_citation_edges(
    observed_value_edges: set[tuple[str, str]],
    required_edges: set[tuple[str, str]] | frozenset[tuple[str, str]],
) -> None:
    missing = sorted(set(required_edges) - observed_value_edges)
    if missing:
        formatted = ", ".join(
            f"{candidate} -> {target}" for candidate, target in missing
        )
        raise AuditFailure(
            "WITNESS-BY-CITATION lacks a final V4 direct value edge: "
            + formatted
        )


def parse_axiom_names(text: str) -> frozenset[str]:
    return frozenset(
        name.strip()
        for name in re.split(r"[;,]", text)
        if name.strip()
    )


def parse_report_section(text: str, section: str) -> tuple[str, ...]:
    lines = text.splitlines()
    marker = f"[{section}]"
    try:
        start = lines.index(marker) + 1
    except ValueError as error:
        raise AuditFailure(
            f"V4 coverage report lacks section {marker}"
        ) from error
    values: list[str] = []
    for line in lines[start:]:
        stripped = line.strip()
        if not stripped or (
            stripped.startswith("[") and stripped.endswith("]")
        ):
            break
        if stripped != "(none)":
            values.append(stripped)
    return tuple(values)


def validate_v4_coverage_contract(
    summary: str,
    coverage: str,
    environment_modules: set[str],
) -> None:
    required_summary_lines = {
        "verdict: PASS",
        "declarations_audited: 15022",
        f"expected_modules: {EXPECTED_V4_MODULE_COUNT}",
        f"environment_modules: {EXPECTED_V4_MODULE_COUNT}",
        "module_coverage: PASS",
        "direct_dependency_dump: PASS",
        "nonstandard_non_sorry_axiom_declarations: 0",
    }
    summary_lines = set(summary.splitlines())
    missing_summary = sorted(required_summary_lines - summary_lines)
    if missing_summary:
        raise AuditFailure(
            "V4 summary lacks fixed completion contracts: "
            f"{missing_summary!r}"
        )
    if "[hard_failures]\n(none)" not in summary:
        raise AuditFailure("V4 summary contains a hard failure")
    if len(environment_modules) != EXPECTED_V4_MODULE_COUNT:
        raise AuditFailure(
            "V4 environment module count changed: "
            f"{len(environment_modules)}"
        )
    if len(environment_modules) != len(set(environment_modules)):
        raise AuditFailure("V4 environment module list contains duplicates")
    coverage_lines = set(coverage.splitlines())
    required_coverage_lines = {
        f"expected_modules: {EXPECTED_V4_MODULE_COUNT}",
        f"environment_modules: {EXPECTED_V4_MODULE_COUNT}",
        "missing_modules: 0",
        "extra_modules: 0",
    }
    missing_coverage = sorted(required_coverage_lines - coverage_lines)
    if missing_coverage:
        raise AuditFailure(
            "V4 module coverage lacks fixed contracts: "
            f"{missing_coverage!r}"
        )
    observed_missing = frozenset(
        parse_report_section(coverage, "missing_modules")
    )
    if observed_missing:
        raise AuditFailure(
            f"V4 coverage contains missing modules: {observed_missing!r}"
        )
    observed_extra = parse_report_section(coverage, "extra_modules")
    if observed_extra:
        raise AuditFailure(
            f"V4 coverage contains unexpected modules: {observed_extra!r}"
        )
def validate_clean_citation_endpoints(
    rows_by_name: dict[str, list[dict[str, str]]],
    required_names: set[str],
    environment_modules: set[str],
) -> dict[str, dict[str, str]]:
    ambiguous = {
        name: len(rows_by_name.get(name, []))
        for name in sorted(required_names)
        if len(rows_by_name.get(name, [])) != 1
    }
    if ambiguous:
        raise AuditFailure(
            "V4 citation endpoint resolution is not one-to-one: "
            f"{ambiguous!r}"
        )
    resolved = {
        name: rows_by_name[name][0] for name in sorted(required_names)
    }
    for name, row in resolved.items():
        module = row["module"]
        if module not in environment_modules:
            raise AuditFailure(
                f"V4 citation endpoint {name} belongs to absent module "
                f"{module}"
            )
        disallowed = parse_axiom_names(row["axioms"]) - ALLOWED_AXIOMS
        if disallowed:
            raise AuditFailure(
                f"V4 citation endpoint {name} has disallowed axioms "
                f"{sorted(disallowed)!r}"
            )
    return resolved


def check_citation_edges() -> dict[str, object]:
    build_text = path(V4_BUILD_LOG_REL).read_text(
        encoding="utf-8", errors="replace"
    )
    exits = re.findall(r"(?m)^exit_code:\s*(-?\d+)\s*$", build_text)
    if exits != ["0"] or not re.search(r"(?m)^finished:\s*\S+", build_text):
        raise AuditFailure(
            "final completed V4 build evidence is unavailable; citation "
            "witnesses remain unconfirmed"
        )
    summary = path(V4_SUMMARY_REL).read_text(
        encoding="utf-8", errors="replace"
    )
    coverage = path(V4_COVERAGE_REL).read_text(
        encoding="utf-8", errors="replace"
    )
    module_lines = [
        line.strip()
        for line in path(V4_MODULES_REL).read_text(
            encoding="utf-8", errors="replace"
        ).splitlines()
        if line.strip()
    ]
    if len(module_lines) != len(set(module_lines)):
        raise AuditFailure("V4 environment module list contains duplicates")
    environment_modules = set(module_lines)
    validate_v4_coverage_contract(
        summary,
        coverage,
        environment_modules,
    )

    endpoint_names = {
        endpoint
        for edge in EXPECTED_CITATION_EDGES
        for endpoint in edge
    }
    expected_axiom_columns = (
        "module",
        "name",
        "kind",
        "is_private",
        "private_user_name",
        "is_internal",
        "axioms",
    )
    rows_by_name: dict[str, list[dict[str, str]]] = {
        name: [] for name in endpoint_names
    }
    with path(V4_AXIOMS_REL).open(
        encoding="utf-8", newline=""
    ) as handle:
        reader = csv.DictReader(handle, delimiter="\t")
        if tuple(reader.fieldnames or ()) != expected_axiom_columns:
            raise AuditFailure(
                "V4 axiom TSV schema changed: "
                f"{reader.fieldnames!r}"
            )
        for row in reader:
            if row["name"] in rows_by_name:
                rows_by_name[row["name"]].append(row)
    resolved = validate_clean_citation_endpoints(
        rows_by_name,
        endpoint_names,
        environment_modules,
    )

    expected_columns = (
        "source_module",
        "source",
        "source_kind",
        "origin",
        "target_module",
        "target",
    )
    with path(V4_DIRECT_DEPENDENCIES_REL).open(
        encoding="utf-8", newline=""
    ) as handle:
        reader = csv.DictReader(handle, delimiter="\t")
        if tuple(reader.fieldnames or ()) != expected_columns:
            raise AuditFailure(
                "V4 direct-dependency TSV schema changed: "
                f"{reader.fieldnames!r}"
            )
        observed: dict[
            tuple[str, str], list[dict[str, str]]
        ] = {edge: [] for edge in EXPECTED_CITATION_EDGES}
        for row in reader:
            edge = (row["source"], row["target"])
            if edge in observed:
                observed[edge].append(row)
    invalid: dict[str, object] = {}
    value_edges: set[tuple[str, str]] = set()
    for edge, rows in observed.items():
        candidate, target = edge
        candidate_row = resolved[candidate]
        target_row = resolved[target]
        exact_value_rows = [
            row for row in rows
            if row["origin"] == "value"
            and row["source_kind"] == candidate_row["kind"]
            and row["source_module"] == candidate_row["module"]
            and row["target_module"] == target_row["module"]
        ]
        if len(exact_value_rows) != 1:
            invalid[f"{candidate} -> {target}"] = {
                "matching_rows": rows,
                "exact_value_rows": len(exact_value_rows),
            }
        else:
            value_edges.add(edge)
    if invalid:
        raise AuditFailure(
            "WITNESS-BY-CITATION lacks an exact unique V4 proof-value "
            f"edge: {invalid!r}"
        )
    validate_required_citation_edges(
        value_edges,
        EXPECTED_CITATION_EDGES,
    )
    return {
        "required_edges": len(EXPECTED_CITATION_EDGES),
        "confirmed_direct_value_edges": len(EXPECTED_CITATION_EDGES),
        "clean_endpoint_declarations": len(endpoint_names),
        "environment_modules": len(environment_modules),
        "missing_modules": sorted(EXPECTED_V4_MISSING_MODULES),
        "status": "PASS",
        "evidence": {
            "axioms": str(V4_AXIOMS_REL),
            "dependencies": str(V4_DIRECT_DEPENDENCIES_REL),
            "modules": str(V4_MODULES_REL),
            "coverage": str(V4_COVERAGE_REL),
        },
    }


def run_logged(command: Sequence[str], log_relative: Path) -> str:
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
    log = "\n".join(
        [
            f"cwd: {ROOT}",
            f"command: {shlex.join(command)}",
            "",
            completed.stdout.rstrip("\n"),
            "",
            f"exit_code: {completed.returncode}",
            "",
        ]
    )
    write_text(log_relative, log)
    if completed.returncode != 0:
        raise AuditFailure(
            f"{shlex.join(command)} exited {completed.returncode}; "
            f"see {log_relative}"
        )
    return completed.stdout


def check_queue() -> dict[str, object]:
    with path(QUEUE_REL).open(encoding="utf-8", newline="") as handle:
        rows = list(csv.DictReader(handle, delimiter="\t"))
    selected = [
        row for row in rows
        if row["row_set"] == "sampling_plan"
        and row["sample_kind"] == "ok_review_queue_head"
        and row["tier_c_required"] == "yes"
    ]
    if len(selected) != 25:
        raise AuditFailure(f"expected 25 Tier-C queue rows, found {len(selected)}")
    by_id = {row["row_id"]: row for row in selected}
    if set(by_id) != {spec.row_id for spec in QUEUE_SPECS}:
        raise AuditFailure("Tier-C queue row-ID set changed")
    chapter_counts: dict[str, int] = {}
    for spec in QUEUE_SPECS:
        row = by_id[spec.row_id]
        if (
            row["chapter"] != spec.chapter
            or int(row["sample_rank"]) != spec.rank
            or row["resolved_declarations"] != spec.target
            or row["witness_by_citation_candidate"] != spec.candidate
            or row["verdict"] != "OK"
        ):
            raise AuditFailure(f"queue metadata changed for {spec.row_id}")
        chapter_counts[spec.chapter] = chapter_counts.get(spec.chapter, 0) + 1
    if set(chapter_counts.values()) != {5}:
        raise AuditFailure(f"chapter bucket counts are not all five: {chapter_counts}")
    citation_count = sum(
        spec.mode == WITNESS_BY_CITATION for spec in QUEUE_SPECS
    )
    model_count = sum(spec.mode == CONCRETE_MODEL for spec in QUEUE_SPECS)
    if (citation_count, model_count) != (18, 7):
        raise AuditFailure("expected the fixed 18-citation/7-model split")
    model_witnesses = {
        witness
        for spec in QUEUE_SPECS
        if spec.mode == CONCRETE_MODEL
        for witness in spec.witnesses
    }
    if model_witnesses != set(CONCRETE_MODEL_CONTRACTS):
        raise AuditFailure(
            "concrete-model contract set differs from queue witnesses"
        )
    return {
        "row_count": 25,
        "chapter_counts": chapter_counts,
        "citation_rows": citation_count,
        "concrete_model_rows": model_count,
    }


def check_sources() -> dict[str, object]:
    main_code = masked_source(WITNESS_REL)
    harness_code = masked_source(AXIOM_HARNESS_REL)
    main_text = path(WITNESS_REL).read_text(encoding="utf-8")
    harness_text = path(AXIOM_HARNESS_REL).read_text(encoding="utf-8")
    for relative, code, text in (
        (WITNESS_REL, main_code, main_text),
        (AXIOM_HARNESS_REL, harness_code, harness_text),
    ):
        if "set_option autoImplicit false" not in code:
            raise AuditFailure(f"{relative}: missing autoImplicit false")
        tokens = FORBIDDEN_PROOF_TOKEN.findall(code)
        if tokens:
            raise AuditFailure(f"{relative}: forbidden proof tokens {tokens!r}")
        if FORBIDDEN_IMPORT in text:
            raise AuditFailure(f"{relative}: imports the broken Rosenthal path")
        if re.search(r"(?m)^[ \t]*(?:axiom|unsafe)[ \t]+", code):
            raise AuditFailure(f"{relative}: contains an axiom/unsafe command")
    local_names = DECLARATION.findall(main_code)
    expected = [name.rsplit(".", 1)[1] for name in WITNESS_NAMES]
    if local_names != expected:
        raise AuditFailure(
            "witness declaration order/set mismatch:\n"
            f"expected={expected!r}\nobserved={local_names!r}"
        )
    harness_names = re.findall(
        r"``(HDP\.Verification\.V6TierC\.[A-Za-z_][A-Za-z0-9_']*)",
        harness_text,
    )
    if tuple(harness_names) != WITNESS_NAMES:
        raise AuditFailure("axiom harness name list differs from witness list")
    for spec in QUEUE_SPECS:
        if spec.mode == WITNESS_BY_CITATION:
            local = spec.witnesses[0].rsplit(".", 1)[1]
            pattern = re.compile(
                rf"alias\s+{re.escape(local)}\s*:=\s*"
                rf"{re.escape(spec.candidate)}"
            )
            if not pattern.search(main_code):
                raise AuditFailure(
                    f"citation alias {local} does not name {spec.candidate}"
                )
    model_contracts = check_concrete_model_contracts(main_code)
    return {
        "declarations": len(local_names),
        "queue_witness_declarations": len(QUEUE_WITNESS_NAMES),
        "seeded_witness_declarations": (
            len(LEGACY_SEEDED_PREFIX)
            + len(LEGACY_SEEDED_SUFFIX)
            + len(CURRENT_SEEDED_WITNESSES)
        ),
        "tier_a_witness_declarations": 1,
        "forbidden_tokens": 0,
        "compliance": model_contracts,
        "main_sha256": sha256(WITNESS_REL),
        "harness_sha256": sha256(AXIOM_HARNESS_REL),
    }


def is_ch0_4_path(source_path: str) -> bool:
    if not source_path.startswith("HighDimensionalProbability/"):
        return False
    if source_path.startswith("HighDimensionalProbability/Verification/"):
        return False
    return any(
        source_path.startswith(f"HighDimensionalProbability/Chapter{chapter}_")
        or source_path.startswith(f"HighDimensionalProbability/Chapter{chapter}/")
        or source_path.startswith(
            f"HighDimensionalProbability/Exercise/Chapter{chapter}/"
        )
        for chapter in range(5)
    )


def validate_tier_a_report(report: dict[str, object]) -> dict[str, object]:
    declarations = report.get("declarations")
    if not isinstance(declarations, list):
        raise AuditFailure("Tier-A JSON has no declaration list")
    try:
        v4_join = validate_v4_join_contract(
            report,
            expected_types_tsv=str(V4_TYPES_REL),
            expected_binders_tsv=str(V4_BINDERS_REL),
            expected_declaration_count=EXPECTED_TIER_A_DECLARATION_COUNT,
        )
    except ValueError as error:
        raise AuditFailure(f"Tier-A V4 join contract failed: {error}") from error
    relevant: set[tuple[str, str]] = set()
    shared: set[tuple[str, str]] = set()
    chapter_auto_bound_count = 0
    for raw in declarations:
        if not isinstance(raw, dict):
            continue
        reasons = raw.get("triage_reasons")
        if not isinstance(reasons, list):
            continue
        pair = (str(raw.get("path", "")), str(raw.get("name", "")))
        has_auto_bound = any(
            isinstance(reason, dict)
            and reason.get("reason_id") == AUTO_BOUND_REASON_ID
            for reason in reasons
        )
        legacy_reasons = [
            reason
            for reason in reasons
            if not isinstance(reason, dict)
            or reason.get("reason_id") != AUTO_BOUND_REASON_ID
        ]
        if has_auto_bound and is_ch0_4_path(pair[0]):
            chapter_auto_bound_count += 1
        if not legacy_reasons:
            continue
        if is_ch0_4_path(pair[0]):
            relevant.add(pair)
        if pair[0] == "HighDimensionalProbability/Prelude/Matrix.lean":
            shared.add(pair)
    if relevant:
        raise AuditFailure(
            f"fresh Tier-A scan found uncovered Ch0--4 hits: {sorted(relevant)!r}"
        )
    if shared != EXPECTED_SHARED_TIER_A:
        raise AuditFailure(
            "shared Prelude Tier-A set changed: "
            f"expected={sorted(EXPECTED_SHARED_TIER_A)!r}, "
            f"observed={sorted(shared)!r}"
        )
    return {
        "summary": report.get("summary", {}),
        "v4_join": v4_join,
        "chapter_0_4_auto_bound_flagged_declarations": (
            chapter_auto_bound_count
        ),
        "chapter_0_4_hits": [],
        "shared_prelude_hits": [
            {"path": source_path, "name": name}
            for source_path, name in sorted(shared)
        ],
        "shared_prelude_witness": TIER_A_WITNESS,
    }


def run_tier_a_scan() -> dict[str, object]:
    command = [
        sys.executable,
        str(path(VERIFY / "scripts/scan_v6_vacuity_tier_a.py")),
        "--scope", "library",
        "--v4-types-tsv", str(path(V4_TYPES_REL)),
        "--v4-binders-tsv", str(path(V4_BINDERS_REL)),
        "--format", "json",
        "--output", str(path(SCAN_JSON_REL)),
    ]
    run_logged(command, SCAN_LOG_REL)
    report = json.loads(path(SCAN_JSON_REL).read_text(encoding="utf-8"))
    return validate_tier_a_report(report)


def read_tier_a_scan() -> dict[str, object]:
    if not path(SCAN_JSON_REL).exists():
        raise AuditFailure(f"missing {SCAN_JSON_REL}")
    return validate_tier_a_report(
        json.loads(path(SCAN_JSON_REL).read_text(encoding="utf-8"))
    )


def check_borell_boundary() -> dict[str, str]:
    source_rel = Path(
        "HighDimensionalProbability/Appendix/BorellConvexBody.lean"
    )
    code = masked_source(source_rel)
    present_removed = [
        name for name in REMOVED_BORELL_INTERFACES
        if re.search(rf"\b{re.escape(name)}\b", code)
    ]
    if present_removed:
        raise AuditFailure(
            f"removed Borell interfaces reappeared: {present_removed!r}"
        )
    declarations = set(
        re.findall(
            r"(?m)^[ \t]*(?:theorem|lemma|def|alias)[ \t]+"
            r"([A-Za-z_][A-Za-z0-9_']*)",
            code,
        )
    )
    expected_domain = set(RETAINED_BORELL_DOMAIN_DECLARATIONS)
    if declarations != expected_domain:
        raise AuditFailure(
            "Borell appendix declaration surface changed: "
            f"missing={sorted(expected_domain - declarations)!r}, "
            f"extra={sorted(declarations - expected_domain)!r}"
        )
    missing_domain = [
        name for name in RETAINED_BORELL_DOMAIN_DECLARATIONS
        if not re.search(
            rf"\b(?:theorem|lemma|def|alias)\s+{re.escape(name)}\b",
            code,
        )
    ]
    if missing_domain:
        raise AuditFailure(
            f"Borell domain infrastructure is missing: {missing_domain!r}"
        )
    if any(
        name in path(WITNESS_REL).read_text(encoding="utf-8")
        for name in REMOVED_BORELL_INTERFACES
    ):
        raise AuditFailure("Ch0--4 witnesses must not substitute the Borell conditional")
    return {
        "removed_interfaces": ";".join(REMOVED_BORELL_INTERFACES),
        "retained_domain_declarations": ";".join(
            RETAINED_BORELL_DOMAIN_DECLARATIONS
        ),
        "status": "ABSENT",
        "conditional_substituted": "no",
    }


def build_witness() -> None:
    run_logged(["lake", "build", WITNESS_MODULE], BUILD_LOG_REL)


def run_axiom_harness() -> None:
    raw = path(AXIOM_TSV_REL)
    if raw.exists():
        raw.unlink()
    run_logged(
        [
            "lake", "env", "lean", *LEAN_OPTIONS,
            str(path(AXIOM_HARNESS_REL)),
        ],
        AXIOM_LOG_REL,
    )
    if not raw.exists():
        raise AuditFailure("axiom harness did not create its raw TSV")


def parse_axioms() -> dict[str, frozenset[str]]:
    with path(AXIOM_TSV_REL).open(encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle, delimiter="\t")
        expected_columns = (
            "witness", "axioms", "unexpected", "has_sorryAx"
        )
        if tuple(reader.fieldnames or ()) != expected_columns:
            raise AuditFailure("axiom TSV columns changed")
        rows = list(reader)
    if [row["witness"] for row in rows] != list(WITNESS_NAMES):
        raise AuditFailure("axiom TSV declaration list/order changed")
    parsed: dict[str, frozenset[str]] = {}
    for row in rows:
        axioms = frozenset(filter(None, row["axioms"].split(";")))
        if row["unexpected"] or row["has_sorryAx"] != "false":
            raise AuditFailure(f"axiom harness rejected {row['witness']}")
        extra = axioms - ALLOWED_AXIOMS
        if extra:
            raise AuditFailure(
                f"{row['witness']}: disallowed axioms {sorted(extra)!r}"
            )
        parsed[row["witness"]] = axioms
    return parsed


def parse_axiom_markers(log_text: str) -> dict[str, frozenset[str]]:
    markers: dict[str, frozenset[str]] = {}
    for line in log_text.splitlines():
        fields = line.split("\t")
        if fields and fields[0] == "V6_TIER_C_AXIOM":
            if len(fields) != 3:
                raise AuditFailure(f"malformed calibration marker: {line!r}")
            markers[fields[1]] = frozenset(
                filter(None, fields[2].split(";"))
            )
    return markers


def validate_planted_bad_log() -> dict[str, object]:
    calibration_code = masked_source(PLANTED_BAD_REL)
    static_rejected = bool(FORBIDDEN_PROOF_TOKEN.findall(calibration_code))
    if not static_rejected:
        raise AuditFailure("shared planted witness escaped lexical rejection")
    if not path(PLANTED_BAD_LOG_REL).exists():
        raise AuditFailure(f"missing shared calibration log {PLANTED_BAD_LOG_REL}")
    markers = parse_axiom_markers(
        path(PLANTED_BAD_LOG_REL).read_text(encoding="utf-8")
    )
    bad_name = PREFIX + "plantedBadWitness"
    bad_axioms = markers.get(bad_name)
    if bad_axioms is None or "sorryAx" not in bad_axioms:
        raise AuditFailure("shared planted witness did not expose sorryAx")
    if not (bad_axioms - ALLOWED_AXIOMS):
        raise AuditFailure("shared planted witness escaped axiom rejection")
    return {
        "source": str(PLANTED_BAD_REL),
        "raw_log": str(PLANTED_BAD_LOG_REL),
        "static_checker": "REJECT",
        "axiom_checker": "REJECT",
        "axioms": sorted(bad_axioms),
    }


def ensure_planted_bad_calibration() -> dict[str, object]:
    if not path(PLANTED_BAD_LOG_REL).exists():
        run_logged(
            [
                "lake", "env", "lean", *LEAN_OPTIONS,
                str(path(PLANTED_BAD_REL)),
            ],
            PLANTED_BAD_LOG_REL,
        )
    return validate_planted_bad_log()


def render_axioms(names: Sequence[str],
                  axioms: dict[str, frozenset[str]]) -> str:
    parts = []
    for name in names:
        values = ";".join(sorted(axioms[name])) or "<none>"
        parts.append(f"{name}=[{values}]")
    return " | ".join(parts)


def render_ledger(axioms: dict[str, frozenset[str]]) -> str:
    fields = (
        "row_set", "row_id", "chapter", "sample_rank", "target",
        "witness_mode", "citation_candidate", "witnesses",
        "build", "axiom_audit", "axioms", "status",
    )
    stream = io.StringIO()
    writer = csv.DictWriter(
        stream, fieldnames=fields, delimiter="\t", lineterminator="\n"
    )
    writer.writeheader()
    for spec in QUEUE_SPECS:
        writer.writerow(
            {
                "row_set": "tier_c_queue",
                "row_id": spec.row_id,
                "chapter": spec.chapter,
                "sample_rank": spec.rank,
                "target": spec.target,
                "witness_mode": spec.mode,
                "citation_candidate": spec.candidate,
                "witnesses": ";".join(spec.witnesses),
                "build": "OK",
                "axiom_audit": "OK",
                "axioms": render_axioms(spec.witnesses, axioms),
                "status": "OK",
            }
        )
    writer.writerow(
        {
            "row_set": "fresh_tier_a_shared_prelude",
            "row_id": "",
            "chapter": "Shared Prelude for Chapters 0--4",
            "sample_rank": "",
            "target": "HDP.matrixSingularValue_of_finrank_le",
            "witness_mode": CONCRETE_MODEL,
            "citation_candidate": "",
            "witnesses": TIER_A_WITNESS,
            "build": "OK",
            "axiom_audit": "OK",
            "axioms": render_axioms((TIER_A_WITNESS,), axioms),
            "status": "OK",
        }
    )
    return stream.getvalue()


def render_summary(
    queue: dict[str, object],
    source: dict[str, object],
    citation_edges: dict[str, object],
    tier_a: dict[str, object],
    axioms: dict[str, frozenset[str]],
    calibration: dict[str, object],
    borell: dict[str, str],
) -> str:
    chapter_counts = queue["chapter_counts"]
    assert isinstance(chapter_counts, dict)
    return "\n".join(
        [
            "V6 Tier-C Chapters 0--4 summary",
            "overall: PASS",
            "queue_rows: 25",
            "chapter_buckets: "
            + ", ".join(
                f"{chapter}={chapter_counts[chapter]}"
                for chapter in (
                    "Appetizer", "Chapter 1", "Chapter 2",
                    "Chapter 3", "Chapter 4",
                )
            ),
            "queue_split: WITNESS-BY-CITATION=18, "
            "CONCRETE-NONDEGENERATE-MODEL=7",
            "v4_direct_value_citation_edges: "
            f"{citation_edges['confirmed_direct_value_edges']}/"
            f"{citation_edges['required_edges']} PASS",
            "closed_concrete_model_declarations: "
            f"{source['compliance']['closed_concrete_model_declarations']}",
            "generic_hypothesis_wrappers: 0",
            f"named_queue_witnesses: {len(QUEUE_WITNESS_NAMES)}",
            f"named_witnesses_axiom_audited: {len(axioms)}",
            "fresh_tier_a_actual_ch0_4_hits: "
            f"{len(tier_a['chapter_0_4_hits'])}",
            "fresh_tier_a_shared_prelude_hits: "
            f"{len(tier_a['shared_prelude_hits'])}",
            "v4_join_complete_binder_telescopes: "
            f"{tier_a['v4_join']['complete_binder_telescopes']}",
            "v4_auto_bound_flagged_declarations: "
            f"{tier_a['v4_join']['auto_bound_flagged_declaration_count']}",
            "v4_auto_bound_ch0_4_flagged_declarations: "
            f"{tier_a['chapter_0_4_auto_bound_flagged_declarations']}",
            "source_sorry_admit: 0",
            "allowed_axioms: Classical.choice, Quot.sound, propext",
            "all_witness_axiom_sets_within_allowlist: yes",
            "shared_planted_bad_calibration: REJECT "
            "(lexical checker and sorryAx checker)",
            f"removed_borell_interfaces: {borell['status']}",
            "borell_conditional_substituted: no",
            "broken_rosenthal_pinelis_imported: no",
            f"witness_sha256: {source['main_sha256']}",
            f"axiom_harness_sha256: {source['harness_sha256']}",
            f"calibration_log: {calibration['raw_log']}",
            "",
        ]
    )


def write_final_artifacts(
    queue: dict[str, object],
    source: dict[str, object],
    citation_edges: dict[str, object],
    tier_a: dict[str, object],
    borell: dict[str, str],
    axioms: dict[str, frozenset[str]],
    calibration: dict[str, object],
) -> None:
    ledger = render_ledger(axioms)
    summary = render_summary(
        queue, source, citation_edges, tier_a, axioms, calibration, borell
    )
    write_text(LEDGER_REL, ledger)
    write_text(SUMMARY_REL, summary)
    report = {
        "profile": "V6-Tier-C-Ch0-4",
        "overall": "PASS",
        "queue": queue,
        "source": source,
        "citation_edges": citation_edges,
        "tier_a": tier_a,
        "borell": borell,
        "build": {
            "module": WITNESS_MODULE,
            "raw_log": str(BUILD_LOG_REL),
            "axiom_raw_log": str(AXIOM_LOG_REL),
        },
        "axioms": {
            name: sorted(axioms[name]) for name in WITNESS_NAMES
        },
        "calibration": calibration,
        "artifacts": {
            "ledger": str(LEDGER_REL),
            "summary": str(SUMMARY_REL),
            "raw_axioms": str(AXIOM_TSV_REL),
        },
    }
    write_text(RESULT_JSON_REL, json.dumps(report, indent=2) + "\n")
    write_text(RUNNER_LOG_REL, summary)


def full_run() -> str:
    queue = check_queue()
    source = check_sources()
    citation_edges = check_citation_edges()
    queue["citation_edge_status"] = citation_edges["status"]
    tier_a = run_tier_a_scan()
    borell = check_borell_boundary()
    build_witness()
    run_axiom_harness()
    axioms = parse_axioms()
    calibration = ensure_planted_bad_calibration()
    write_final_artifacts(
        queue, source, citation_edges, tier_a, borell, axioms, calibration
    )
    return path(SUMMARY_REL).read_text(encoding="utf-8")


def static_run() -> str:
    queue = check_queue()
    source = check_sources()
    citation_edges = check_citation_edges()
    tier_a = run_tier_a_scan()
    borell = check_borell_boundary()
    return "\n".join(
        [
            "V6 Tier-C Chapters 0--4 static preflight",
            "overall: PASS",
            f"queue_rows: {queue['row_count']}",
            f"named_witnesses: {source['declarations']}",
            "v4_direct_value_citation_edges: "
            f"{citation_edges['confirmed_direct_value_edges']}/"
            f"{citation_edges['required_edges']} PASS",
            "closed_concrete_model_declarations: "
            f"{source['compliance']['closed_concrete_model_declarations']}",
            "generic_hypothesis_wrappers: 0",
            "fresh_tier_a_actual_ch0_4_hits: "
            f"{len(tier_a['chapter_0_4_hits'])}",
            "fresh_tier_a_shared_prelude_hits: "
            f"{len(tier_a['shared_prelude_hits'])}",
            "v4_join_complete_binder_telescopes: "
            f"{tier_a['v4_join']['complete_binder_telescopes']}",
            "v4_auto_bound_flagged_declarations: "
            f"{tier_a['v4_join']['auto_bound_flagged_declaration_count']}",
            f"removed_borell_interfaces: {borell['status']}",
            "",
        ]
    )


def check_existing() -> str:
    queue = check_queue()
    source = check_sources()
    citation_edges = check_citation_edges()
    queue["citation_edge_status"] = citation_edges["status"]
    tier_a = read_tier_a_scan()
    borell = check_borell_boundary()
    for relative in (BUILD_LOG_REL, AXIOM_LOG_REL):
        if not path(relative).exists():
            raise AuditFailure(f"missing raw build log {relative}")
        if "exit_code: 0" not in path(relative).read_text(encoding="utf-8"):
            raise AuditFailure(f"raw build log is not successful: {relative}")
    axioms = parse_axioms()
    calibration = validate_planted_bad_log()
    if not path(RESULT_JSON_REL).exists():
        raise AuditFailure(f"missing {RESULT_JSON_REL}")
    result = json.loads(path(RESULT_JSON_REL).read_text(encoding="utf-8"))
    if result.get("overall") != "PASS":
        raise AuditFailure("recorded result is not PASS")
    if result.get("queue", {}).get("citation_edge_status") != citation_edges["status"]:
        raise AuditFailure("recorded queue citation-edge status is stale")
    recorded_source = result.get("source", {})
    if (
        recorded_source.get("main_sha256") != source["main_sha256"]
        or recorded_source.get("harness_sha256") != source["harness_sha256"]
    ):
        raise AuditFailure("source hashes differ from the compiled PASS record")
    expected_ledger = render_ledger(axioms)
    expected_summary = render_summary(
        queue, source, citation_edges, tier_a, axioms, calibration, borell
    )
    if path(LEDGER_REL).read_text(encoding="utf-8") != expected_ledger:
        raise AuditFailure("Tier-C ledger is stale or nondeterministic")
    if path(SUMMARY_REL).read_text(encoding="utf-8") != expected_summary:
        raise AuditFailure("Tier-C summary is stale or nondeterministic")
    return expected_summary


def compliance_source_only() -> str:
    queue = check_queue()
    source = check_sources()
    borell = check_borell_boundary()
    return "\n".join(
        [
            "V6 Tier-C Chapters 0--4 compliance source audit",
            "overall: SOURCE-CONTRACTS-PASS-V4-EDGES-PENDING",
            f"queue_rows: {queue['row_count']}",
            f"witness_by_citation_rows: {queue['citation_rows']}",
            f"concrete_model_rows: {queue['concrete_model_rows']}",
            "closed_concrete_model_declarations: "
            f"{source['compliance']['closed_concrete_model_declarations']}",
            "generic_hypothesis_wrappers: 0",
            "v4_direct_value_citation_edges: PENDING-FINAL-V4",
            f"removed_borell_interfaces: {borell['status']}",
            "",
        ]
    )


def compliance_self_test() -> str:
    good = "\n".join(
        [
            "theorem plantedConcrete :",
            "    let x : Fin 2 → ℝ := fun _ ↦ 1",
            "    x 0 = 1 := by",
            "  exact Target.theorem",
            "  have : Fin 2 := 0",
            "  exact rfl",
        ]
    )
    validate_concrete_model_block(
        "Test.plantedConcrete",
        good,
        ("Target.theorem",),
        ("Fin 2", "fun _ ↦ 1"),
    )
    generic_wrapper = "\n".join(
        [
            "theorem plantedConcrete (A : Nat) (hA : A = A) :",
            "    A = A := by",
            "  exact Target.theorem A hA",
            "  have : Fin 2 := 0",
            "  exact hA",
        ]
    )
    try:
        validate_concrete_model_block(
            "Test.plantedConcrete",
            generic_wrapper,
            ("Target.theorem",),
            ("Fin 2",),
        )
    except AuditFailure:
        pass
    else:
        raise AuditFailure("generic-wrapper calibration was not rejected")

    implication_wrapper = "\n".join(
        [
            "theorem plantedConcrete :",
            "    (A : Nat) → A = A := by",
            "  exact Target.theorem",
            "  have : Fin 2 := 0",
        ]
    )
    try:
        validate_concrete_model_block(
            "Test.plantedConcrete",
            implication_wrapper,
            ("Target.theorem",),
            ("Fin 2",),
        )
    except AuditFailure:
        pass
    else:
        raise AuditFailure("implication-wrapper calibration was not rejected")

    hidden_implication_wrapper = "\n".join(
        [
            "theorem plantedConcrete :",
            "    ∃ x : Fin 2 → ℝ,",
            "      (A : Nat) → A = A := by",
            "  exact Target.theorem",
            "  have : Fin 2 := 0",
        ]
    )
    try:
        validate_concrete_model_block(
            "Test.plantedConcrete",
            hidden_implication_wrapper,
            ("Target.theorem",),
            ("Fin 2",),
        )
    except AuditFailure:
        pass
    else:
        raise AuditFailure(
            "data-binder-hidden implication calibration was not rejected"
        )

    validate_required_citation_edges(
        {("Downstream", "Target")},
        {("Downstream", "Target")},
    )
    try:
        validate_required_citation_edges(
            {("Downstream", "Other")},
            {("Downstream", "Target")},
        )
    except AuditFailure:
        pass
    else:
        raise AuditFailure("missing-direct-edge calibration was not rejected")

    clean_row = {
        "module": "HighDimensionalProbability.Chapter1",
        "name": "Downstream",
        "kind": "theorem",
        "axioms": "propext;Classical.choice;Quot.sound",
    }
    target_row = {
        "module": "HighDimensionalProbability.Chapter1",
        "name": "Target",
        "kind": "theorem",
        "axioms": "propext;Classical.choice;Quot.sound",
    }
    environment = {"HighDimensionalProbability.Chapter1"}
    resolved = validate_clean_citation_endpoints(
        {"Downstream": [clean_row], "Target": [target_row]},
        {"Downstream", "Target"},
        environment,
    )
    if set(resolved) != {"Downstream", "Target"}:
        raise AuditFailure("clean-endpoint positive calibration failed")
    sorry_row = dict(target_row)
    sorry_row["axioms"] += ";sorryAx"
    try:
        validate_clean_citation_endpoints(
            {"Downstream": [clean_row], "Target": [sorry_row]},
            {"Downstream", "Target"},
            environment,
        )
    except AuditFailure:
        pass
    else:
        raise AuditFailure("sorryAx endpoint calibration was not rejected")
    try:
        validate_clean_citation_endpoints(
            {"Downstream": [clean_row], "Target": [target_row]},
            {"Downstream", "Target"},
            set(),
        )
    except AuditFailure:
        pass
    else:
        raise AuditFailure("absent-module endpoint calibration was not rejected")
    return (
        "V6 Tier-C Ch0--4 compliance self-test: PASS\n"
        "generic-wrapper calibration: REJECT\n"
        "implication-wrapper calibration: REJECT\n"
        "data-binder-hidden implication calibration: REJECT\n"
        "missing-direct-edge calibration: REJECT\n"
        "sorryAx-endpoint calibration: REJECT\n"
        "absent-module-endpoint calibration: REJECT\n"
    )


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group()
    group.add_argument(
        "--static-only", action="store_true",
        help="run source/queue/fresh Tier-A checks without Lean or Lake",
    )
    group.add_argument(
        "--check", action="store_true",
        help="validate existing compiled evidence without invoking Lean or Lake",
    )
    group.add_argument(
        "--compliance-only", action="store_true",
        help=(
            "check queue/source model contracts without reading unfinished "
            "V4 evidence or invoking Lean/Lake"
        ),
    )
    group.add_argument(
        "--self-test", action="store_true",
        help="run fail-closed compliance calibrations only",
    )
    args = parser.parse_args(argv)
    try:
        if args.self_test:
            output = compliance_self_test()
        elif args.compliance_only:
            output = compliance_source_only()
        elif args.static_only:
            output = static_run()
        elif args.check:
            output = check_existing()
        else:
            output = full_run()
    except (AuditFailure, OSError, ValueError, KeyError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        return 1
    print(output, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
