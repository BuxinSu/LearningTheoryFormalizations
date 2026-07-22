#!/usr/bin/env python3
"""Generate and fail-closed check the Pass 07 row-level evidence artifacts.

This gate closes three deliberately separate evidence obligations:

* the current-state overlay for the five frozen historical core ``PARTIAL`` rows;
* the eleven source-facing obligations replayed against the authoritative PDF
  in correction round 5; and
* exact reverse dependency cones for the corrected load-bearing interfaces.

The generated TSVs are projections of the current frozen inventories, V4
declaration/type/axiom evidence, the full V4 dependency edge relation, V6's
source-level theorem/lemma universe, and the original PDF.  Generation and
checking both require the live Lean source tree to match the stored source
manifest.  A source edit racing the scan is detected by a second manifest
check before any successful result is reported.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import io
import json
import re
import subprocess
import sys
import unicodedata
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Mapping, Sequence

from source_manifest import build_manifest
from verify_exercise_reorganization import require_certificate as require_reorganization_certificate


ROOT = Path(__file__).resolve().parents[3]
VERIFICATION = ROOT / "HighDimensionalProbability" / "Verification"
INVENTORY = VERIFICATION / "inventory"
REVIEW = VERIFICATION / "review"
LOGS = VERIFICATION / "logs"

SOURCE_MANIFEST = LOGS / "source_manifest.txt"
HISTORICAL_ROWS = INVENTORY / "faithful_historical_status_rows.tsv"
CENSUS = INVENTORY / "review_census_838.tsv"
EXERCISE_LEAVES = INVENTORY / "exercise_leaf_declarations.tsv"
DECLARATION_CHANGES = INVENTORY / "pass07_declaration_changes.tsv"
SAME_NAME_CHANGES = INVENTORY / "pass07_same_name_changes.tsv"
DECLARATION_CHANGE_CHECKER = (
    VERIFICATION / "scripts" / "pass07_declaration_change_log.py"
)
REVIEW_BASELINE = REVIEW / "pass07_reviewed_endpoint_baseline.tsv"
AXIOM_AUDIT = LOGS / "axiom_audit.tsv"
TYPE_EVIDENCE = LOGS / "axiom_declaration_types.tsv"
DEPENDENCY_EDGES = LOGS / "axiom_direct_dependencies.tsv"
V4_COMPLETION = LOGS / "pass07_v4_completion.json"
V6_TIER_A = LOGS / "v6_tier_a.tsv"
BERNOULLI_WITNESS = (
    VERIFICATION / "scripts" / "witnesses" / "V6TierCCh8_9.lean"
)
BERNOULLI_BUILD_LOG = LOGS / "v6_tier_c_ch8_9_build.log"
BERNOULLI_AXIOM_LOG = LOGS / "v6_tier_c_ch8_9_axioms.log"
BERNOULLI_RESULTS = LOGS / "v6_tier_c_ch8_9_results.json"
BERNOULLI_RUNNER = VERIFICATION / "scripts" / "run_v6_tier_c_ch8_9.py"
BERNOULLI_LEDGER = REVIEW / "v6_tier_b_ch8_9.tsv"
BERNOULLI_SUPPLEMENT = REVIEW / "v6_tier_b_supplement_ch8_9.tsv"
BERNOULLI_TIER_A_REVIEW = REVIEW / "v6_tier_c_ch8_9_tier_a_review.tsv"
BERNOULLI_FULL_TIER_A_REVIEW = REVIEW / "v6_tier_a_full_review.tsv"
BERNOULLI_AXIOM_HARNESS = (
    ROOT / ".audit_work" / "verification" / "V6TierCCh8_9AxiomAudit.lean"
)
BERNOULLI_PLANTED_BAD = (
    ROOT / ".audit_work" / "verification" / "V6TierCPlantedBad.lean"
)

OVERLAY_OUT = INVENTORY / "pass07_core_partial_resolutions.tsv"
ROUND5_OUT = REVIEW / "pass07_round5_pdf_faithfulness.tsv"
CONES_OUT = INVENTORY / "pass07_dependency_cones.tsv"

PDF = (
    ROOT.parent
    / "High_Dimensional_Probability"
    / "Original_High_Dimensional_Probability.pdf"
)
PDF_LOGICAL_PATH = (
    "High_Dimensional_Probability/Original_High_Dimensional_Probability.pdf"
)
PDF_SHA256 = "a5665ecf5fc833968a6493c6e3a4f6ae2137700ddbaed2fd457b5e1148bc0aac"
PDF_PAGE_COUNT = 341

ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
SORRY_AXIOM = "sorryAx"
REVIEWER = "Codex GPT-5 independent Pass 07 evidence replay"
REVIEW_TIMESTAMP = "2026-07-19"
EXPECTED_V4_MISSING_MODULES = {
    "MatrixConcentration.Appendix_RosenthalPinelis",
    "MatrixConcentration.Chapter1_Introduction",
    "MatrixConcentration.Chapter6_SumOfBoundedRandomMatrices",
    "MatrixConcentration.Chapter7_IntrinsicDimension",
}

HISTORICAL_COLUMNS = (
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
CENSUS_COLUMNS = (
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
AXIOM_COLUMNS = (
    "module",
    "name",
    "kind",
    "is_private",
    "private_user_name",
    "is_internal",
    "axioms",
)
TYPE_COLUMNS = (
    "module",
    "name",
    "kind",
    "is_private",
    "private_user_name",
    "is_internal",
    "level_params",
    "binder_count",
    "type_raw",
    "conclusion_raw",
)
EDGE_COLUMNS = (
    "source_module",
    "source",
    "source_kind",
    "origin",
    "target_module",
    "target",
)
V6_COLUMNS = (
    "path",
    "module",
    "line",
    "end_line",
    "kind",
    "name",
    "parsed",
    "reasons",
    "statement",
    "conclusion",
    "source_theorem_binders",
    "source_variable_binders",
    "v4_match_count",
    "v4_name",
    "v4_type_present",
    "v4_expected_binder_count",
    "v4_binder_match_count",
    "v4_binder_row_count",
    "v4_implicit_single_letter_sort_or_prop",
    "auto_bound_candidates",
)
DECLARATION_CHANGE_COLUMNS = (
    "change_id",
    "change_kind",
    "command_kind",
    "fq_name",
    "source_name",
    "current_file",
    "current_line",
    "baseline_ref",
    "baseline_commit",
    "baseline_tree",
    "baseline_file_sha256",
    "current_file_sha256",
    "new_signature_sha256",
    "new_body_sha256",
    "new_command_sha256",
    "verification_status",
)
SAME_NAME_CHANGE_COLUMNS = (
    "change_id",
    "change_kind",
    "command_kind",
    "fq_name",
    "source_name",
    "baseline_file",
    "baseline_line",
    "current_file",
    "current_line",
    "baseline_ref",
    "baseline_commit",
    "baseline_tree",
    "baseline_file_sha256",
    "current_file_sha256",
    "old_signature_sha256",
    "new_signature_sha256",
    "old_body_sha256",
    "new_body_sha256",
    "old_command_sha256",
    "new_command_sha256",
    "verification_status",
)
REVIEW_BASELINE_COLUMNS = (
    "endpoint",
    "statement_type_sha256",
    "change_class",
    "review_row_ids",
    "reviewer",
    "review_timestamp",
)

OVERLAY_COLUMNS = (
    "overlay_id",
    "historical_flag_id",
    "census_row_id",
    "book_ref",
    "historical_status",
    "historical_detail",
    "finding_id",
    "current_status",
    "current_coverage_bucket",
    "current_endpoint_names",
    "source_locations",
    "round_fixed",
    "round5_review_row_id",
    "dependency_cone_id",
    "axiom_status",
    "historical_inventory_sha256",
    "census_inventory_sha256",
    "axiom_audit_sha256",
    "v4_completion_sha256",
    "review_baseline_sha256",
    "source_manifest_digest",
    "resolution",
)
ROUND5_COLUMNS = (
    "review_row_id",
    "finding_id",
    "finding_component",
    "round",
    "book_ref",
    "pdf_logical_path",
    "pdf_sha256",
    "physical_pages",
    "printed_pages",
    "pdf_anchors",
    "current_endpoint_names",
    "endpoint_review_role_map",
    "endpoint_type_sha256_map",
    "endpoint_axiom_status_map",
    "source_locations",
    "semantic_relation",
    "assumption_delta",
    "verdict",
    "reviewer",
    "review_timestamp",
    "rationale",
    "overlay_ids",
    "dependency_cone_ids",
    "axiom_audit_sha256",
    "type_evidence_sha256",
    "v6_tier_a_sha256",
    "declaration_change_log_sha256",
    "same_name_change_log_sha256",
    "v4_completion_sha256",
    "review_baseline_sha256",
    "source_manifest_digest",
)
CONE_COLUMNS = (
    "cone_id",
    "finding_ids",
    "root_endpoints",
    "required_endpoint_members",
    "member_endpoint",
    "member_module",
    "member_kind",
    "source_path",
    "source_line",
    "closure_universe",
    "member_role",
    "distance",
    "canonical_predecessor",
    "predecessor_in_ledger",
    "edge_origin",
    "statement_type_sha256",
    "axiom_set",
    "proof_status",
    "semantic_review_status",
    "semantic_review_evidence",
    "semantic_witness_sha256_map",
    "dependency_edges_sha256",
    "axiom_audit_sha256",
    "type_evidence_sha256",
    "v6_tier_a_sha256",
    "exercise_inventory_sha256",
    "declaration_change_log_sha256",
    "same_name_change_log_sha256",
    "v4_completion_sha256",
    "review_baseline_sha256",
    "source_manifest_digest",
)


class EvidenceError(RuntimeError):
    """A fail-closed evidence violation."""


@dataclass(frozen=True)
class AxiomRow:
    module: str
    name: str
    kind: str
    is_private: bool
    private_user_name: str
    is_internal: bool
    axioms: frozenset[str]


@dataclass(frozen=True)
class SourceLocation:
    path: str
    line: int

    def render(self) -> str:
        return f"{self.path}:{self.line}"


@dataclass(frozen=True)
class OverlaySpec:
    overlay_id: str
    historical_flag_id: str
    census_row_id: str
    finding_id: str
    endpoints: tuple[str, ...]
    round5_review_row_id: str
    cone_id: str
    resolution: str


@dataclass(frozen=True)
class Round5Spec:
    review_row_id: str
    finding_id: str
    finding_component: str
    book_ref: str
    physical_pages: tuple[int, ...]
    printed_pages: tuple[int, ...]
    anchors: tuple[str, ...]
    endpoints: tuple[str, ...]
    cone_required_endpoints: tuple[str, ...]
    pdf_only_endpoints: tuple[str, ...]
    semantic_relation: str
    verdict: str
    rationale: str
    overlay_ids: tuple[str, ...]
    cone_ids: tuple[str, ...]


@dataclass(frozen=True)
class ConeSpec:
    cone_id: str
    finding_ids: tuple[str, ...]
    roots: tuple[str, ...]
    required_members: tuple[str, ...] = ()


ALL_ENDPOINTS_REQUIRED = ("__ALL_ENDPOINTS_REQUIRED__",)


OVERLAY_SPECS = (
    OverlaySpec(
        "core-partial-exercise-3-18",
        "faithful-history-26073dcd31a7a034",
        "census-87f743633d65fd64",
        "F-06",
        (
            "HDP.Chapter3.ginibreLeftAction",
            "HDP.Chapter3.ginibreRightAction",
            "HDP.Chapter3.ginibre_left_invariant",
            "HDP.Chapter3.ginibre_right_invariant",
            "HDP.Chapter3.exercise_3_18",
        ),
        "R5-F06",
        "C-GOE",
        "Concrete left/right orthogonal actions, their Ginibre law invariance, "
        "and the exact Exercise 3.18 wrapper replace the historical abstract interface.",
    ),
    OverlaySpec(
        "core-partial-exercise-3-19",
        "faithful-history-416d9136352fd3a9",
        "census-2ac4570af46e5e92",
        "F-01",
        (
            "HDP.Chapter3.goeUpperVariance",
            "HDP.Chapter3.independentGOEMatrixMeasure",
            "HDP.Chapter3.independentGOEMatrixMeasure_upper_map",
            "HDP.Chapter3.independentGOEMatrixMeasure_diagonal_map",
            "HDP.Chapter3.independentGOEMatrixMeasure_strictUpper_map",
            "HDP.Chapter3.independentGOEMatrixMeasure_upper_iIndep",
            "HDP.Chapter3.independentGOEMatrixMeasure_symmetric",
            "HDP.Chapter3.ginibreSymmetrize",
            "HDP.Chapter3.gaussianSymmetrizedLaw",
            "HDP.Chapter3.independentGOEMatrixMeasure_eq_gaussianSymmetrizedLaw",
            "HDP.Chapter3.ginibreConjugation",
            "HDP.Chapter3.exercise_3_19a",
            "HDP.Chapter3.exercise_3_19b",
        ),
        "R5-F01",
        "C-GOE",
        "The current interface exposes the actual independent-entry GOE law, "
        "diagonal/off-diagonal laws, upper-coordinate independence, symmetry, "
        "Ginibre symmetrization, and orthogonal-conjugation invariance.",
    ),
    OverlaySpec(
        "core-partial-exercise-3-20",
        "faithful-history-dfed987a32c6417e",
        "census-c963e6d3281f4c67",
        "F-02",
        ("HDP.Chapter3.exercise_3_20",),
        "R5-F02",
        "C-GOE",
        "The current wrapper starts from one standard Gaussian matrix and proves "
        "independence and both standard-Gaussian image laws for Gu and Gv.",
    ),
    OverlaySpec(
        "core-partial-remark-7-2-1",
        "faithful-history-0177acdfa0b84afb",
        "census-8e8fe89097bc9dd2",
        "F-04",
        (
            "HDP.Chapter7.extendedExpectation",
            "HDP.Chapter7.extendedExpectation_eq_integral",
            "HDP.Chapter7.extendedExpectedSupremum",
        ),
        "R5-F04",
        "C-EXTSUP",
        "Extended expectation preserves infinite finite-stage expectations, while "
        "the bridge recovers the ordinary integral on the integrable domain.",
    ),
    OverlaySpec(
        "core-partial-equation-8-37",
        "faithful-history-5de43447ddcd4977",
        "census-72abea10eaf34039",
        "F-05",
        (
            "HDP.Chapter8.populationRisk",
            "HDP.Chapter8.finitePopulationRisk",
            "HDP.Chapter8.populationRisk_eq_ofReal_finitePopulationRisk",
        ),
        "R5-F05",
        "C-RISK",
        "Population risk is extended-valued, and the proof-carrying finite real "
        "interface is connected by an explicit integrability bridge.",
    ),
)

ROUND5_SPECS = (
    Round5Spec(
        "R5-F01",
        "F-01",
        "",
        "Exercise 3.19",
        (100, 101),
        (92, 93),
        (
            "3 19 KK GOE random matrices",
            "diagonal entries are N 0 2",
            "orthogonal conjugation",
        ),
        OVERLAY_SPECS[1].endpoints,
        ALL_ENDPOINTS_REQUIRED,
        (),
        "EXACT_SOURCE_INTERFACE",
        "SOURCE_FAITHFUL",
        "The public GOE object has independent upper-triangular coordinates with "
        "the printed variances, symmetric support, the concrete (G+Gᵀ)/√2 law, "
        "and orthogonal-conjugation invariance.",
        ("core-partial-exercise-3-19",),
        ("C-GOE",),
    ),
    Round5Spec(
        "R5-F02",
        "F-02",
        "",
        "Exercise 3.20",
        (101,),
        (93,),
        (
            "3 20 KK A Gaussian random matrix makes orthogonal vectors independent",
            "Gu and Gv are independent",
        ),
        OVERLAY_SPECS[2].endpoints,
        ALL_ENDPOINTS_REQUIRED,
        (),
        "EXACT_SOURCE_INTERFACE",
        "SOURCE_FAITHFUL",
        "The theorem quantifies over one Gaussian matrix and fixed orthogonal unit "
        "vectors, and concludes independence and both N(0,I_m) image laws.",
        ("core-partial-exercise-3-20",),
        ("C-GOE",),
    ),
    Round5Spec(
        "R5-F04",
        "F-04",
        "",
        "Remark 7.2.1",
        (207,),
        (199,),
        (
            "Remark 7 2 1 Making T finite",
            "where T0 runs over all finite subsets",
        ),
        OVERLAY_SPECS[3].endpoints,
        ALL_ENDPOINTS_REQUIRED,
        (),
        "EXACT_EXTENDED_VALUE_INTERFACE",
        "SOURCE_FAITHFUL",
        "The finite-subfamily supremum uses an extended expectation and therefore "
        "retains +∞; the ordinary expectation is recovered only under integrability.",
        ("core-partial-remark-7-2-1",),
        ("C-EXTSUP",),
    ),
    Round5Spec(
        "R5-F05",
        "F-05",
        "",
        "Equation (8.37)",
        (251,),
        (243,),
        (
            "aim to minimize the risk of misdiagnosing a new patient",
            "8 37",
        ),
        OVERLAY_SPECS[4].endpoints,
        ALL_ENDPOINTS_REQUIRED,
        (),
        "EXACT_EXTENDED_VALUE_INTERFACE",
        "SOURCE_FAITHFUL",
        "The unrestricted nonnegative squared risk is ℝ≥0∞-valued; the real-valued "
        "version requires integrability and is linked by a proved bridge.",
        ("core-partial-equation-8-37",),
        ("C-RISK",),
    ),
    Round5Spec(
        "R5-F06",
        "F-06",
        "",
        "Exercise 3.18",
        (100,),
        (92,),
        (
            "3 18 KK Ginibre random matrices",
            "have the same distribution as G",
        ),
        OVERLAY_SPECS[0].endpoints,
        ALL_ENDPOINTS_REQUIRED,
        (),
        "EXACT_SOURCE_INTERFACE",
        "SOURCE_FAITHFUL",
        "The endpoint specializes to the Ginibre matrix law and the concrete left "
        "and right actions of fixed orthogonal matrices.",
        ("core-partial-exercise-3-18",),
        ("C-GOE",),
    ),
    Round5Spec(
        "R5-F07A",
        "F-07",
        "Definition 2.6.4",
        "Definition 2.6.4",
        (46,),
        (38,),
        (
            "Definition 2 6 4 Subgaussian distributions",
            "Its subgaussian norm",
        ),
        (
            "HDP.IsSubGaussianRandomVariable",
            "HDP.isSubGaussianRandomVariable_iff",
            "HDP.IsSubGaussianRandomVariable.psi2MGF_psi2Norm_le_two",
        ),
        ALL_ENDPOINTS_REQUIRED,
        (),
        "GENERALIZED_RAW_PLUS_SOURCE_BUNDLE",
        "SOURCE_FAITHFUL_ADDITIVE_INTERFACE",
        "The source-facing structure supplies the probability-space and "
        "measurability domain while preserving the generalized raw helper.",
        (),
        ("C-RV",),
    ),
    Round5Spec(
        "R5-F07B",
        "F-07",
        "Definition 2.8.4",
        "Definition 2.8.4",
        (53,),
        (45,),
        (
            "Definition 2 8 4 Subexponential distributions",
            "Its subexponential norm",
        ),
        (
            "HDP.IsSubExponentialRandomVariable",
            "HDP.isSubExponentialRandomVariable_iff",
            "HDP.IsSubExponentialRandomVariable.psi1MGF_psi1Norm_le_two",
        ),
        ALL_ENDPOINTS_REQUIRED,
        (),
        "GENERALIZED_RAW_PLUS_SOURCE_BUNDLE",
        "SOURCE_FAITHFUL_ADDITIVE_INTERFACE",
        "The source-facing structure supplies the probability-space and "
        "measurability domain while preserving the generalized raw helper.",
        (),
        ("C-RV",),
    ),
    Round5Spec(
        "R5-F08",
        "F-08",
        "",
        "Definition 3.2.5",
        (73,),
        (65,),
        (
            "Definition 3 2 5 Isotropic random vectors",
            "E XX T In",
        ),
        (
            "HDP.IsIsotropicRandomVector",
            "HDP.isIsotropicRandomVector_iff",
            "HDP.IsIsotropicRandomVector.integrable_coord_mul",
            "HDP.Chapter3.isIsotropicRandomVector_inner_sq",
        ),
        ALL_ENDPOINTS_REQUIRED,
        (),
        "GENERALIZED_RAW_PLUS_SOURCE_BUNDLE",
        "SOURCE_FAITHFUL_ADDITIVE_INTERFACE",
        "The source-facing isotropy bundle adds probability, measurability, and "
        "finite second moment, and exports the printed directional identity.",
        (),
        ("C-RV",),
    ),
    Round5Spec(
        "R5-F09",
        "F-09",
        "",
        "Definition 3.4.1",
        (81, 82),
        (73, 74),
        (
            "Definition 3 4 1 Subgaussian random vectors",
            "one dimensional marginals",
        ),
        (
            "HDP.IsSubGaussianRandomVector",
            "HDP.isSubGaussianRandomVector_iff",
            "HDP.IsSubGaussianRandomVector.marginal",
            "HDP.IsSubGaussianRandomVector.psi2NormSet_bddAbove",
            "HDP.IsSubGaussianRandomVector.psi2Norm_marginal_le_vector",
        ),
        ALL_ENDPOINTS_REQUIRED,
        (),
        "GENERALIZED_RAW_PLUS_SOURCE_BUNDLE",
        "SOURCE_FAITHFUL_ADDITIVE_INTERFACE",
        "Every marginal is bundled as a subgaussian random variable, and finite "
        "dimensionality proves the real supremum is bounded on the source domain.",
        (),
        ("C-RV",),
    ),
    Round5Spec(
        "R5-F10",
        "F-10",
        "",
        "Definition 3.3.4",
        (75,),
        (67,),
        (
            "Definition 3 3 4 General normal distribution",
            "affine transformation of some standard normal random vector",
        ),
        (
            "HDP.HasGaussianVectorLaw",
            "HDP.Chapter3.hasGaussianVectorLaw_iff_affineRepresentation",
        ),
        ALL_ENDPOINTS_REQUIRED,
        (),
        "CORRECTED_PSD_DOMAIN",
        "SOURCE_FAITHFUL_DOMAIN_REPAIR",
        "The covariance parameter is positive semidefinite, and the source-facing "
        "law is equivalent to an affine representation by a standard Gaussian.",
        (),
        ("C-GAUSSPSD",),
    ),
    Round5Spec(
        "R5-F11",
        "F-11",
        "",
        "Equations (1.10)-(1.13)",
        (19,),
        (11,),
        (
            "moment generating function of X is defined as",
            "1 10",
            "1 11",
            "1 12",
            "1 13",
        ),
        (
            "HDP.Chapter1.lpNormRV_eq_toReal_eLpNorm",
            "HDP.Chapter1.sq_lpNormRV_two_eq_l2InnerRV",
            "HDP.Chapter1.stdDev_eq_lpNormRV",
            "HDP.Chapter1.expectation_vector_apply",
            "HDP.Chapter3.covarianceMatrix_eq_secondMoment_sub_mean",
            "HDP.Chapter1.extendedMGF",
            "HDP.Chapter1.extendedMGF_eq_ofReal_mgf",
        ),
        (
            "HDP.Chapter1.extendedMGF",
            "HDP.Chapter1.extendedMGF_eq_ofReal_mgf",
        ),
        (
            "HDP.Chapter1.lpNormRV_eq_toReal_eLpNorm",
            "HDP.Chapter1.sq_lpNormRV_two_eq_l2InnerRV",
            "HDP.Chapter1.stdDev_eq_lpNormRV",
            "HDP.Chapter1.expectation_vector_apply",
            "HDP.Chapter3.covarianceMatrix_eq_secondMoment_sub_mean",
        ),
        "FINITE_DOMAIN_BRIDGES_PLUS_EXTENDED_MGF",
        "SOURCE_FAITHFUL_ADDITIVE_INTERFACE",
        "The MemLp-restricted Lp/L2/standard-deviation theorems and the "
        "Chapter 3 covariance identity expose the intended finite-moment "
        "regime, while vector expectation is coordinatewise. The unrestricted "
        "MGF preserves +∞ and agrees with the real helper under explicit "
        "integrability.",
        (),
        ("C-MOMENTS",),
    ),
)

CONE_SPECS = (
    ConeSpec(
        "C-GOE",
        ("F-01", "F-02", "F-06"),
        (
            "HDP.Chapter3.ginibreLeftAction",
            "HDP.Chapter3.ginibreRightAction",
            "HDP.Chapter3.ginibreConjugation",
            "HDP.Chapter3.goeUpperVariance",
            "HDP.Chapter3.independentGOEMatrixMeasure",
            "HDP.Chapter3.ginibreSymmetrize",
            "HDP.Chapter3.gaussianSymmetrizedLaw",
            "HDP.Chapter3.exercise_3_20",
        ),
    ),
    ConeSpec(
        "C-EXTSUP",
        ("F-04",),
        (
            "HDP.Chapter7.extendedExpectation",
            "HDP.Chapter7.extendedExpectedSupremum",
        ),
    ),
    ConeSpec(
        "C-RISK",
        ("F-05",),
        (
            "HDP.Chapter8.populationRisk",
            "HDP.Chapter8.finitePopulationRisk",
        ),
    ),
    ConeSpec(
        "C-RV",
        ("F-07", "F-08", "F-09"),
        (
            "HDP.IsSubGaussianRandomVariable",
            "HDP.IsSubExponentialRandomVariable",
            "HDP.IsIsotropicRandomVector",
            "HDP.IsSubGaussianRandomVector",
        ),
    ),
    ConeSpec(
        "C-MOMENTS",
        ("F-11",),
        ("HDP.Chapter1.extendedMGF",),
    ),
    ConeSpec(
        "C-GAUSSPSD",
        ("F-10",),
        ("HDP.HasGaussianVectorLaw",),
    ),
    ConeSpec(
        "C-BERNOULLI",
        ("V6-F2",),
        ("BernoulliLSI.gradient_term_symmetric",),
    ),
)


def round5_endpoint_roles(
    spec: Round5Spec,
) -> tuple[set[str], set[str]]:
    endpoints = list(spec.endpoints)
    if not endpoints or len(endpoints) != len(set(endpoints)):
        raise EvidenceError(
            f"{spec.review_row_id}: endpoints must be nonempty and unique"
        )
    if spec.cone_required_endpoints == ALL_ENDPOINTS_REQUIRED:
        required = set(endpoints)
    else:
        required = set(spec.cone_required_endpoints)
        if len(required) != len(spec.cone_required_endpoints):
            raise EvidenceError(
                f"{spec.review_row_id}: duplicate cone-required endpoint"
            )
    pdf_only = set(spec.pdf_only_endpoints)
    if len(pdf_only) != len(spec.pdf_only_endpoints):
        raise EvidenceError(f"{spec.review_row_id}: duplicate PDF-only endpoint")
    if required & pdf_only or required | pdf_only != set(endpoints):
        raise EvidenceError(
            f"{spec.review_row_id}: endpoint roles do not form an exact partition"
        )
    if not required:
        raise EvidenceError(
            f"{spec.review_row_id}: at least one endpoint must enter a dependency cone"
        )
    return required, pdf_only


def validate_configuration() -> dict[str, tuple[set[str], set[str]]]:
    cone_by_id: dict[str, ConeSpec] = {}
    for cone in CONE_SPECS:
        if not cone.cone_id or cone.cone_id in cone_by_id:
            raise EvidenceError(f"duplicate or blank cone ID {cone.cone_id!r}")
        if (
            not cone.finding_ids
            or len(cone.finding_ids) != len(set(cone.finding_ids))
            or not cone.roots
            or len(cone.roots) != len(set(cone.roots))
            or len(cone.required_members) != len(set(cone.required_members))
        ):
            raise EvidenceError(
                f"{cone.cone_id}: findings/roots must be nonempty and all "
                "configured endpoint lists must be unique"
            )
        cone_by_id[cone.cone_id] = cone

    round5_roles: dict[str, tuple[set[str], set[str]]] = {}
    seen_rows: set[str] = set()
    seen_endpoints: dict[str, str] = {}
    for spec in ROUND5_SPECS:
        if not spec.review_row_id or spec.review_row_id in seen_rows:
            raise EvidenceError(
                f"duplicate or blank Round 5 row ID {spec.review_row_id!r}"
            )
        seen_rows.add(spec.review_row_id)
        if (
            not spec.cone_ids
            or len(spec.cone_ids) != len(set(spec.cone_ids))
            or not spec.finding_id
        ):
            raise EvidenceError(
                f"{spec.review_row_id}: finding/cone IDs must be nonempty and unique"
            )
        for cone_id in spec.cone_ids:
            cone = cone_by_id.get(cone_id)
            if cone is None:
                raise EvidenceError(
                    f"{spec.review_row_id}: unknown dependency cone {cone_id}"
                )
            if spec.finding_id not in cone.finding_ids:
                raise EvidenceError(
                    f"{spec.review_row_id}: {spec.finding_id} is not owned by {cone_id}"
                )
        roles = round5_endpoint_roles(spec)
        round5_roles[spec.review_row_id] = roles
        for endpoint in spec.endpoints:
            previous = seen_endpoints.get(endpoint)
            if previous is not None and previous != spec.review_row_id:
                raise EvidenceError(
                    f"Round 5 endpoint {endpoint} belongs to both "
                    f"{previous} and {spec.review_row_id}"
                )
            seen_endpoints[endpoint] = spec.review_row_id

    seen_overlays: set[str] = set()
    overlay_by_round5: dict[str, set[str]] = {}
    for spec in OVERLAY_SPECS:
        if (
            not spec.overlay_id
            or spec.overlay_id in seen_overlays
            or not spec.endpoints
            or len(spec.endpoints) != len(set(spec.endpoints))
        ):
            raise EvidenceError(
                f"overlay IDs/endpoints must be nonempty and unique: {spec.overlay_id}"
            )
        seen_overlays.add(spec.overlay_id)
        cone = cone_by_id.get(spec.cone_id)
        if cone is None or spec.finding_id not in cone.finding_ids:
            raise EvidenceError(
                f"{spec.overlay_id}: invalid finding/cone linkage "
                f"{spec.finding_id}/{spec.cone_id}"
            )
        if spec.round5_review_row_id not in round5_roles:
            raise EvidenceError(
                f"{spec.overlay_id}: unknown Round 5 row "
                f"{spec.round5_review_row_id}"
            )
        round5_spec = next(
            item
            for item in ROUND5_SPECS
            if item.review_row_id == spec.round5_review_row_id
        )
        if (
            round5_spec.finding_id != spec.finding_id
            or spec.cone_id not in round5_spec.cone_ids
        ):
            raise EvidenceError(
                f"{spec.overlay_id}: Round 5 finding/cone linkage disagrees"
            )
        overlay_by_round5.setdefault(spec.round5_review_row_id, set()).add(
            spec.overlay_id
        )
    for spec in ROUND5_SPECS:
        if set(spec.overlay_ids) != overlay_by_round5.get(spec.review_row_id, set()):
            raise EvidenceError(
                f"{spec.review_row_id}: overlay linkage is not bidirectionally exact"
            )
    return round5_roles


def json_cell(value: object) -> str:
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"))


def sha256_file(path: Path) -> str:
    before = path.stat()
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    after = path.stat()
    if (before.st_size, before.st_mtime_ns) != (after.st_size, after.st_mtime_ns):
        raise EvidenceError(f"input changed while hashing: {path}")
    return digest.hexdigest()


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def parse_bool(value: str, *, field: str, path: Path) -> bool:
    if value == "true":
        return True
    if value == "false":
        return False
    raise EvidenceError(f"{path}: {field} must be true/false, got {value!r}")


def read_tsv(path: Path, expected_columns: Sequence[str]) -> list[dict[str, str]]:
    csv.field_size_limit(sys.maxsize)
    with path.open(encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle, delimiter="\t")
        if tuple(reader.fieldnames or ()) != tuple(expected_columns):
            raise EvidenceError(
                f"{path}: columns {reader.fieldnames!r}, expected {tuple(expected_columns)!r}"
            )
        rows = list(reader)
    if not rows:
        raise EvidenceError(f"{path}: no data rows")
    return rows


def keyed_rows(
    rows: Iterable[dict[str, str]], key: str, *, path: Path
) -> dict[str, dict[str, str]]:
    result: dict[str, dict[str, str]] = {}
    for row in rows:
        value = row[key]
        if not value:
            raise EvidenceError(f"{path}: blank {key}")
        if value in result:
            raise EvidenceError(f"{path}: duplicate {key} {value}")
        result[value] = row
    return result


def assert_manifest_current() -> str:
    if not SOURCE_MANIFEST.is_file():
        raise EvidenceError(f"source manifest missing: {SOURCE_MANIFEST}")
    rendered, digest = build_manifest()
    expected = SOURCE_MANIFEST.read_text(encoding="utf-8")
    if expected != rendered:
        raise EvidenceError(
            "SOURCE MANIFEST DRIFT: regenerate source/V4 evidence before this gate; "
            f"live digest_of_digests={digest}"
        )
    certified_digest = require_reorganization_certificate()
    if certified_digest != digest:
        raise EvidenceError(
            "Exercise-reorganization certificate and source manifest disagree: "
            f"{certified_digest} != {digest}"
        )
    return digest


def load_change_logs() -> tuple[set[str], set[str], str, str]:
    checked = subprocess.run(
        [sys.executable, "-B", str(DECLARATION_CHANGE_CHECKER), "--check"],
        check=False,
        capture_output=True,
        text=True,
    )
    if checked.returncode != 0:
        raise EvidenceError(
            "declaration-change provenance check failed: "
            + (checked.stderr.strip() or checked.stdout.strip())
        )
    added_rows = read_tsv(DECLARATION_CHANGES, DECLARATION_CHANGE_COLUMNS)
    modified_rows = read_tsv(SAME_NAME_CHANGES, SAME_NAME_CHANGE_COLUMNS)
    added = {row["fq_name"] for row in added_rows}
    modified = {row["fq_name"] for row in modified_rows}
    if len(added) != len(added_rows) or len(modified) != len(modified_rows):
        raise EvidenceError("declaration change logs contain duplicate fq_name rows")
    if any(
        row["change_kind"] != "ADDED"
        or row["verification_status"] != "MECHANICALLY_VERIFIED_ADDED"
        for row in added_rows
    ):
        raise EvidenceError("added declaration log has an invalid disposition")
    if any(
        row["verification_status"] != "MECHANICALLY_VERIFIED_SAME_NAME_CHANGE"
        for row in modified_rows
    ):
        raise EvidenceError("same-name declaration log has an invalid disposition")
    if added & modified:
        raise EvidenceError("declaration appears in both added and same-name logs")
    return (
        added,
        modified,
        sha256_file(DECLARATION_CHANGES),
        sha256_file(SAME_NAME_CHANGES),
    )


def load_review_baseline(
    expected_endpoint_rows: Mapping[str, str],
    added_names: set[str],
    modified_names: set[str],
) -> tuple[dict[str, str], str]:
    rows = read_tsv(REVIEW_BASELINE, REVIEW_BASELINE_COLUMNS)
    keyed = keyed_rows(rows, "endpoint", path=REVIEW_BASELINE)
    if set(keyed) != set(expected_endpoint_rows):
        raise EvidenceError(
            f"{REVIEW_BASELINE}: endpoint set differs from reviewed Round 5 set"
        )
    type_hashes: dict[str, str] = {}
    for endpoint, row in keyed.items():
        digest = row["statement_type_sha256"]
        if re.fullmatch(r"[0-9a-f]{64}", digest) is None:
            raise EvidenceError(f"{REVIEW_BASELINE}: invalid type hash for {endpoint}")
        expected_class = (
            "ADDED"
            if endpoint in added_names
            else "SAME_NAME_CHANGED"
            if endpoint in modified_names
            else "UNCHANGED"
        )
        if row["change_class"] != expected_class:
            raise EvidenceError(
                f"{REVIEW_BASELINE}: wrong change class for {endpoint}"
            )
        try:
            reviewed_rows = json.loads(row["review_row_ids"])
        except json.JSONDecodeError as exc:
            raise EvidenceError(
                f"{REVIEW_BASELINE}: invalid review-row JSON for {endpoint}"
            ) from exc
        if reviewed_rows != [expected_endpoint_rows[endpoint]]:
            raise EvidenceError(
                f"{REVIEW_BASELINE}: wrong review row for {endpoint}"
            )
        if (
            row["reviewer"] != REVIEWER
            or row["review_timestamp"] != REVIEW_TIMESTAMP
        ):
            raise EvidenceError(
                f"{REVIEW_BASELINE}: reviewer attestation mismatch for {endpoint}"
            )
        type_hashes[endpoint] = digest
    return type_hashes, sha256_file(REVIEW_BASELINE)


def load_v4_completion(source_digest: str) -> tuple[dict[str, object], str]:
    if not V4_COMPLETION.is_file():
        raise EvidenceError(f"fresh V4 completion manifest missing: {V4_COMPLETION}")
    try:
        data = json.loads(V4_COMPLETION.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise EvidenceError(f"{V4_COMPLETION}: invalid JSON: {exc}") from exc
    if not isinstance(data, dict):
        raise EvidenceError(f"{V4_COMPLETION}: top level is not an object")
    required_scalars = {
        "schema": "pass07-v4-current-v1",
        "completion_status": "COMPLETE_MAXIMAL_BUILDABLE",
        "run_mode": "TWO_SHARD_EXHAUSTIVE_PARTITION",
        "partition_rule": "audited_environment_index_mod_2",
        "source_manifest_digest": source_digest,
        "whole_build_exit_code": 0,
        "build_exit_code": 0,
        "analyzer_exit_code": 2,
        "declarations_audited": 15022,
        "declaration_type_rows": 15022,
        "declaration_binder_rows": 80919,
        "direct_dependency_edges": 1448224,
        "environment_modules": 223,
        "expected_modules": 227,
        "sorryAx_declarations": 228,
        "nonstandard_non_sorry_axiom_declarations": 0,
        "appendix_sorryAx_declarations": 0,
    }
    for field, expected in required_scalars.items():
        if data.get(field) != expected:
            raise EvidenceError(
                f"{V4_COMPLETION}: {field}={data.get(field)!r}, "
                f"expected {expected!r}"
            )
    missing_modules = data.get("missing_modules")
    if (
        not isinstance(missing_modules, list)
        or len(missing_modules) != len(set(missing_modules))
        or set(missing_modules) != EXPECTED_V4_MISSING_MODULES
    ):
        raise EvidenceError(
            f"{V4_COMPLETION}: wrong frozen missing-module set {missing_modules!r}"
        )
    artifacts = data.get("artifacts")
    if not isinstance(artifacts, dict):
        raise EvidenceError(f"{V4_COMPLETION}: artifacts is not an object")
    witnesses = VERIFICATION / "scripts" / "witnesses"
    required_paths = {
        "source_manifest.txt": SOURCE_MANIFEST,
        "pass07_final_whole_build.log": LOGS / "pass07_final_whole_build.log",
        "axiom_audit.tsv": AXIOM_AUDIT,
        "axiom_declaration_types.tsv": TYPE_EVIDENCE,
        "axiom_direct_dependencies.tsv": DEPENDENCY_EDGES,
        "axiom_declaration_binders.tsv": LOGS / "axiom_declaration_binders.tsv",
        "axiom_modules.txt": LOGS / "axiom_modules.txt",
        "axiom_calibration.tsv": LOGS / "axiom_calibration.tsv",
        "axiom_audit_build.log": LOGS / "axiom_audit_build.log",
        "pass07_v4_analyze.log": LOGS / "pass07_v4_analyze.log",
        "axiom_audit_summary.txt": LOGS / "axiom_audit_summary.txt",
        "axiom_module_coverage.txt": LOGS / "axiom_module_coverage.txt",
        "axiom_audit_exceedances.tsv": LOGS / "axiom_audit_exceedances.tsv",
        "axiom_and_opaque_declarations.tsv": (
            LOGS / "axiom_and_opaque_declarations.tsv"
        ),
        "axiom_audit_full_surface_attempt.log": (
            LOGS / "axiom_audit_full_surface_attempt.log"
        ),
        "v3_direct_sorry_declarations.tsv": (
            LOGS / "v3_direct_sorry_declarations.tsv"
        ),
        "definition_constants.tsv": LOGS / "definition_constants.tsv",
        "definition_sanity_build.log": LOGS / "definition_sanity_build.log",
        "pass07_v4_shard0.log": LOGS / "pass07_v4_shard0.log",
        "pass07_v4_shard1.log": LOGS / "pass07_v4_shard1.log",
        "pass07_v4_merge.log": LOGS / "pass07_v4_merge.log",
        "pass07_v4_merge_summary.json": (
            LOGS / "pass07_v4_merge_summary.json"
        ),
        "Pass07FreshV4AxiomAuditShard0.lean": (
            witnesses / "Pass07FreshV4AxiomAuditShard0.lean"
        ),
        "Pass07FreshV4AxiomAuditShard1.lean": (
            witnesses / "Pass07FreshV4AxiomAuditShard1.lean"
        ),
        "scratch_AxiomAuditShard0.lean": (
            ROOT / ".audit_work" / "verification" / "AxiomAuditShard0.lean"
        ),
        "scratch_AxiomAuditShard1.lean": (
            ROOT / ".audit_work" / "verification" / "AxiomAuditShard1.lean"
        ),
        "merge_pass07_v4_shards.py": (
            VERIFICATION / "scripts" / "merge_pass07_v4_shards.py"
        ),
        "pass07_v4_completion.py": (
            VERIFICATION / "scripts" / "pass07_v4_completion.py"
        ),
        "axiom_audit.py": VERIFICATION / "scripts" / "axiom_audit.py",
        "run_all_static_checks.py": (
            VERIFICATION / "scripts" / "run_all_static_checks.py"
        ),
    }
    if set(artifacts) != set(required_paths):
        raise EvidenceError(f"{V4_COMPLETION}: artifact key set is incomplete")
    for name, path in required_paths.items():
        entry = artifacts.get(name)
        if (
            not isinstance(entry, dict)
            or set(entry) != {"sha256", "bytes"}
            or entry.get("sha256") != sha256_file(path)
            or entry.get("bytes") != path.stat().st_size
        ):
            raise EvidenceError(
                f"{V4_COMPLETION}: current hash mismatch for {name}"
            )
    merge_summary = LOGS / "pass07_v4_merge_summary.json"
    if data.get("merge_summary_sha256") != sha256_file(merge_summary):
        raise EvidenceError(f"{V4_COMPLETION}: merge-summary hash mismatch")
    timeline = data.get("timeline")
    if not isinstance(timeline, dict) or set(timeline) != {
        "whole_build",
        "shard0",
        "shard1",
        "merge",
        "analyze",
        "aggregate",
    }:
        raise EvidenceError(f"{V4_COMPLETION}: invalid completion timeline")
    return data, sha256_file(V4_COMPLETION)


def load_axioms() -> tuple[dict[str, AxiomRow], str]:
    rows = read_tsv(AXIOM_AUDIT, AXIOM_COLUMNS)
    result: dict[str, AxiomRow] = {}
    for raw in rows:
        name = raw["name"]
        if name in result:
            raise EvidenceError(f"{AXIOM_AUDIT}: duplicate declaration {name}")
        result[name] = AxiomRow(
            module=raw["module"],
            name=name,
            kind=raw["kind"],
            is_private=parse_bool(raw["is_private"], field="is_private", path=AXIOM_AUDIT),
            private_user_name=raw["private_user_name"],
            is_internal=parse_bool(
                raw["is_internal"], field="is_internal", path=AXIOM_AUDIT
            ),
            axioms=frozenset(filter(None, raw["axioms"].split(";"))),
        )
    return result, sha256_file(AXIOM_AUDIT)


def load_v6_locations() -> tuple[
    dict[str, SourceLocation],
    str,
    dict[str, int],
]:
    rows = read_tsv(V6_TIER_A, V6_COLUMNS)
    locations: dict[str, SourceLocation] = {}
    match_counts: dict[str, int] = {}
    for row in rows:
        if row["parsed"] != "true":
            raise EvidenceError(f"{V6_TIER_A}: unparsed Tier-A row {row['path']}:{row['line']}")
        match_count = row["v4_match_count"]
        match_counts[match_count] = match_counts.get(match_count, 0) + 1
        # Row-level compiled identities are available exactly for the unique
        # V4 matches.  The fixed projection policy excludes the known
        # ambiguous duplicate-statement rows and the frozen unbuildable V4
        # boundary rather than guessing a declaration name.
        if match_count != "1":
            continue
        if not row["v4_name"]:
            raise EvidenceError(
                f"{V6_TIER_A}: unique V4 row has blank identity "
                f"{row['path']}:{row['line']} {row['name']}"
            )
        endpoint = row["v4_name"]
        location = SourceLocation(row["path"], int(row["line"]))
        if endpoint in locations:
            raise EvidenceError(f"{V6_TIER_A}: duplicate V4 endpoint {endpoint}")
        locations[endpoint] = location
    if match_counts != {"0": 319, "1": 7402, "2": 19}:
        raise EvidenceError(
            f"{V6_TIER_A}: unexpected V4 match-count partition {match_counts}"
        )
    return locations, sha256_file(V6_TIER_A), match_counts


def load_exercise_endpoints() -> tuple[set[str], str]:
    rows = read_tsv(
        EXERCISE_LEAVES,
        (
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
        ),
    )
    endpoints = {row["endpoint"] for row in rows}
    if len(endpoints) != len(rows):
        raise EvidenceError(f"{EXERCISE_LEAVES}: duplicate endpoint")
    return endpoints, sha256_file(EXERCISE_LEAVES)


def source_path_for_module(module: str) -> Path:
    if not module.startswith("HighDimensionalProbability"):
        raise EvidenceError(f"cannot resolve non-HDP source module {module}")
    relative = Path(*module.split(".")).with_suffix(".lean")
    path = ROOT / relative
    if not path.is_file():
        raise EvidenceError(f"source module path missing for {module}: {path}")
    return path


def scan_declaration_location(row: AxiomRow) -> SourceLocation:
    path = source_path_for_module(row.module)
    user_name = row.private_user_name or row.name
    short = user_name.rsplit(".", 1)[-1]
    pattern = re.compile(
        rf"^\s*(?:private\s+)?(?:noncomputable\s+)?(?:protected\s+)?"
        rf"(?:def|abbrev|structure|class|inductive|theorem|lemma|opaque)\s+"
        rf"{re.escape(short)}(?:\s|\{{|\(|$)"
    )
    matches = [
        index
        for index, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1)
        if pattern.search(line)
    ]
    if len(matches) != 1:
        raise EvidenceError(
            f"could not resolve unique source location for {row.name} in {path}: {matches}"
        )
    return SourceLocation(path.relative_to(ROOT).as_posix(), matches[0])


def resolve_locations(
    names: Iterable[str],
    axioms: Mapping[str, AxiomRow],
    v6_locations: Mapping[str, SourceLocation],
) -> dict[str, SourceLocation]:
    result: dict[str, SourceLocation] = {}
    for name in sorted(set(names)):
        row = axioms.get(name)
        if row is None:
            raise EvidenceError(f"endpoint absent from V4 axiom audit: {name}")
        result[name] = v6_locations.get(name) or scan_declaration_location(row)
    return result


def proof_status(
    name: str,
    row: AxiomRow,
    exercise_endpoints: set[str],
) -> str:
    unexpected = row.axioms - ALLOWED_AXIOMS - {SORRY_AXIOM}
    if unexpected:
        raise EvidenceError(f"{name}: unexpected axioms {sorted(unexpected)}")
    if SORRY_AXIOM in row.axioms:
        if name not in exercise_endpoints:
            raise EvidenceError(f"{name}: sorryAx outside exercise-leaf inventory")
        if row.module.startswith("HighDimensionalProbability.Appendix"):
            raise EvidenceError(f"{name}: Appendix declaration contains sorryAx")
        return "INTENTIONAL_EXERCISE_SORRY_STATEMENT_ONLY"
    return "KERNEL_PROVED_STANDARD"


def require_standard_endpoints(
    names: Iterable[str],
    axioms: Mapping[str, AxiomRow],
) -> None:
    for name in names:
        row = axioms.get(name)
        if row is None:
            raise EvidenceError(f"required endpoint absent from V4: {name}")
        if SORRY_AXIOM in row.axioms or not row.axioms <= ALLOWED_AXIOMS:
            raise EvidenceError(
                f"required proved endpoint {name} has nonstandard axioms "
                f"{sorted(row.axioms)}"
            )


def load_type_hashes(
    selected: set[str],
    axioms: Mapping[str, AxiomRow],
) -> tuple[dict[str, str], str]:
    before = TYPE_EVIDENCE.stat()
    whole = hashlib.sha256()
    selected_hashes: dict[str, str] = {}
    with TYPE_EVIDENCE.open("rb") as handle:
        header = handle.readline()
        whole.update(header)
        actual_columns = tuple(header.rstrip(b"\r\n").decode("utf-8").split("\t"))
        if actual_columns != TYPE_COLUMNS:
            raise EvidenceError(
                f"{TYPE_EVIDENCE}: columns {actual_columns!r}, expected {TYPE_COLUMNS!r}"
            )
        for line in handle:
            whole.update(line)
            parts = line.rstrip(b"\r\n").split(b"\t", len(TYPE_COLUMNS) - 1)
            if len(parts) != len(TYPE_COLUMNS):
                raise EvidenceError(f"{TYPE_EVIDENCE}: malformed row")
            name = parts[1].decode("utf-8")
            if name not in selected:
                continue
            if name in selected_hashes:
                raise EvidenceError(f"{TYPE_EVIDENCE}: duplicate type row {name}")
            row = axioms.get(name)
            if row is None:
                raise EvidenceError(f"{TYPE_EVIDENCE}: {name} absent from axiom audit")
            if parts[0].decode("utf-8") != row.module:
                raise EvidenceError(f"{TYPE_EVIDENCE}: module mismatch for {name}")
            if parts[2].decode("utf-8") != row.kind:
                raise EvidenceError(f"{TYPE_EVIDENCE}: kind mismatch for {name}")
            type_raw = parts[8]
            if not type_raw:
                raise EvidenceError(f"{TYPE_EVIDENCE}: blank type_raw for {name}")
            selected_hashes[name] = hashlib.sha256(type_raw).hexdigest()
    after = TYPE_EVIDENCE.stat()
    if (before.st_size, before.st_mtime_ns) != (after.st_size, after.st_mtime_ns):
        raise EvidenceError(f"{TYPE_EVIDENCE}: changed during scan")
    missing = sorted(selected - set(selected_hashes))
    if missing:
        raise EvidenceError(f"{TYPE_EVIDENCE}: missing selected endpoints {missing[:20]}")
    return selected_hashes, whole.hexdigest()


def compute_dependency_closures(
    cone_specs: Sequence[ConeSpec],
    axioms: Mapping[str, AxiomRow],
) -> tuple[
    dict[str, dict[str, tuple[int, str, str]]],
    str,
    int,
    int,
]:
    """Return exact reverse closures over all HDP compiled declarations.

    Each state maps an endpoint to ``(distance, predecessor, edge_origin)``.
    Roots have distance zero and blank predecessor/origin.  Iterated streaming
    avoids holding the 1.45M-edge graph in memory while still traversing
    generated/private intermediate declarations.  Projection to V6 source
    theorem/lemma rows happens only after the full closure is known.
    """

    states: dict[str, dict[bytes, tuple[int, bytes, bytes]]] = {
        spec.cone_id: {
            root.encode("utf-8"): (0, b"", b"") for root in spec.roots
        }
        for spec in cone_specs
    }
    root_sets = {
        spec.cone_id: {root.encode("utf-8") for root in spec.roots}
        for spec in cone_specs
    }
    before = DEPENDENCY_EDGES.stat()
    dependency_hash = hashlib.sha256()
    seen_edges: set[bytes] = set()
    edge_row_count = 0
    pass_count = 0
    while True:
        pass_count += 1
        if pass_count > 64:
            raise EvidenceError("dependency closure did not stabilize in 64 passes")
        if pass_count == 2:
            seen_edges.clear()
        distance_updates = 0
        with DEPENDENCY_EDGES.open("rb") as handle:
            header = handle.readline()
            if pass_count == 1:
                dependency_hash.update(header)
            actual_columns = tuple(header.rstrip(b"\r\n").decode("utf-8").split("\t"))
            if actual_columns != EDGE_COLUMNS:
                raise EvidenceError(
                    f"{DEPENDENCY_EDGES}: columns {actual_columns!r}, "
                    f"expected {EDGE_COLUMNS!r}"
                )
            for line in handle:
                if pass_count == 1:
                    dependency_hash.update(line)
                parts = line.rstrip(b"\r\n").split(b"\t")
                if len(parts) != len(EDGE_COLUMNS):
                    raise EvidenceError(f"{DEPENDENCY_EDGES}: malformed edge row")
                source_module, source, _source_kind, origin, target_module, target = parts
                if pass_count == 1:
                    edge_row_count += 1
                    if any(not field for field in parts):
                        raise EvidenceError(
                            f"{DEPENDENCY_EDGES}: blank field in dependency row"
                        )
                    source_name = source.decode("utf-8")
                    source_axiom = axioms.get(source_name)
                    if source_axiom is None:
                        raise EvidenceError(
                            f"{DEPENDENCY_EDGES}: unknown source {source_name}"
                        )
                    if (
                        source_module.decode("utf-8") != source_axiom.module
                        or _source_kind.decode("utf-8") != source_axiom.kind
                    ):
                        raise EvidenceError(
                            f"{DEPENDENCY_EDGES}: source module/kind mismatch "
                            f"for {source_name}"
                        )
                    target_name = target.decode("utf-8")
                    target_axiom = axioms.get(target_name)
                    if target_axiom is not None:
                        if target_module.decode("utf-8") != target_axiom.module:
                            raise EvidenceError(
                                f"{DEPENDENCY_EDGES}: target module mismatch "
                                f"for {target_name}"
                            )
                    elif target_module.startswith(
                        (b"HighDimensionalProbability", b"MatrixConcentration")
                    ):
                        raise EvidenceError(
                            f"{DEPENDENCY_EDGES}: project target absent from "
                            f"axiom audit: {target_name}"
                        )
                    key = b"\0".join((source, origin, target))
                    if key in seen_edges:
                        raise EvidenceError(
                            f"{DEPENDENCY_EDGES}: duplicate dependency edge "
                            f"{source_name} {origin!r} {target!r}"
                        )
                    seen_edges.add(key)
                if origin not in {b"type", b"value"}:
                    raise EvidenceError(
                        f"{DEPENDENCY_EDGES}: unknown edge origin {origin!r}"
                    )
                if not source_module.startswith(b"HighDimensionalProbability"):
                    continue
                for cone_id, state in states.items():
                    target_state = state.get(target)
                    if target_state is None or source in root_sets[cone_id]:
                        continue
                    candidate = (target_state[0] + 1, target, origin)
                    current = state.get(source)
                    if current is None or candidate[0] < current[0]:
                        state[source] = candidate
                        distance_updates += 1
                    elif candidate[0] == current[0] and candidate[1:] < current[1:]:
                        state[source] = candidate
        if distance_updates == 0:
            break
    after = DEPENDENCY_EDGES.stat()
    if (before.st_size, before.st_mtime_ns) != (after.st_size, after.st_mtime_ns):
        raise EvidenceError(f"{DEPENDENCY_EDGES}: changed during closure scan")
    decoded = {
        cone_id: {
            name.decode("utf-8"): (
                value[0],
                value[1].decode("utf-8"),
                value[2].decode("utf-8"),
            )
            for name, value in state.items()
        }
        for cone_id, state in states.items()
    }
    return decoded, dependency_hash.hexdigest(), pass_count, edge_row_count


def normalize_anchor(text: str) -> str:
    normalized = unicodedata.normalize("NFKC", text).casefold()
    normalized = re.sub(r"[^\w]+", " ", normalized, flags=re.UNICODE)
    return " ".join(normalized.split())


def check_pdf() -> tuple[str, dict[str, str]]:
    if not PDF.is_file():
        raise EvidenceError(f"authoritative PDF missing: {PDF}")
    actual_hash = sha256_file(PDF)
    if actual_hash != PDF_SHA256:
        raise EvidenceError(
            f"authoritative PDF SHA-256 mismatch: {actual_hash} != {PDF_SHA256}"
        )
    info = subprocess.run(
        ["pdfinfo", str(PDF)],
        check=False,
        capture_output=True,
        text=True,
    )
    if info.returncode != 0:
        raise EvidenceError(f"pdfinfo failed: {info.stderr.strip()}")
    match = re.search(r"^Pages:\s+(\d+)\s*$", info.stdout, flags=re.MULTILINE)
    if match is None or int(match.group(1)) != PDF_PAGE_COUNT:
        raise EvidenceError(f"PDF page count is not {PDF_PAGE_COUNT}")
    page_text_hashes: dict[str, str] = {}
    for spec in ROUND5_SPECS:
        first = min(spec.physical_pages)
        last = max(spec.physical_pages)
        extracted = subprocess.run(
            [
                "pdftotext",
                "-f",
                str(first),
                "-l",
                str(last),
                "-layout",
                str(PDF),
                "-",
            ],
            check=False,
            capture_output=True,
        )
        if extracted.returncode != 0:
            raise EvidenceError(
                f"pdftotext failed for {spec.review_row_id}: "
                f"{extracted.stderr.decode('utf-8', errors='replace').strip()}"
            )
        text = extracted.stdout.decode("utf-8", errors="replace")
        normalized_text = normalize_anchor(text)
        for anchor in spec.anchors:
            if normalize_anchor(anchor) not in normalized_text:
                raise EvidenceError(
                    f"{spec.review_row_id}: PDF anchor not found on physical "
                    f"pages {first}-{last}: {anchor!r}"
                )
        page_text_hashes[spec.review_row_id] = hashlib.sha256(
            extracted.stdout
        ).hexdigest()
    return actual_hash, page_text_hashes


def validate_bernoulli_witness() -> dict[str, str]:
    paths = (
        BERNOULLI_WITNESS,
        BERNOULLI_BUILD_LOG,
        BERNOULLI_AXIOM_LOG,
        BERNOULLI_RESULTS,
    )
    for path in paths:
        if not path.is_file() or path.is_symlink() or path.stat().st_size == 0:
            raise EvidenceError(f"Bernoulli witness artifact missing/unsafe: {path}")
    names = (
        "HDP.Verification.V6TierC.tierA_gradient_term_fin1_indicator_nonzero",
        "HDP.Verification.V6TierC."
        "tierA_gradient_term_symmetric_fin1_indicator_instance",
    )
    witness_text = BERNOULLI_WITNESS.read_text(encoding="utf-8")
    if any(name.rsplit(".", 1)[-1] not in witness_text for name in names):
        raise EvidenceError("Bernoulli witness source lacks required declarations")
    expected_build_command = (
        "command: lake build "
        "HighDimensionalProbability.Verification.scripts.witnesses."
        "V6TierCCh8_9"
    )
    expected_axiom_command = (
        "command: lake env lean -Dpp.unicode.fun=true "
        "-DrelaxedAutoImplicit=false "
        "-Dweak.linter.mathlibStandardSet=true "
        "-DmaxSynthPendingDepth=3 "
        f"{ROOT / '.audit_work' / 'verification' / 'V6TierCCh8_9AxiomAudit.lean'}"
    )
    build_text = BERNOULLI_BUILD_LOG.read_text(
        encoding="utf-8", errors="replace"
    )
    if (
        not build_text.rstrip().endswith("exit_code: 0")
        or expected_build_command not in build_text.splitlines()
        or "Build completed successfully (8601 jobs)." not in build_text
        or "Built HighDimensionalProbability.Verification.scripts.witnesses."
        "V6TierCCh8_9" not in build_text
    ):
        raise EvidenceError("Bernoulli nonvacuity witness build is not successful")
    axiom_text = BERNOULLI_AXIOM_LOG.read_text(
        encoding="utf-8", errors="replace"
    )
    if (
        not axiom_text.rstrip().endswith("exit_code: 0")
        or expected_axiom_command not in axiom_text.splitlines()
    ):
        raise EvidenceError("Bernoulli witness axiom transcript did not complete")
    axiom_rows: dict[str, set[str]] = {}
    for line in axiom_text.splitlines():
        if not line.startswith("V6_TIER_C_AXIOM\t"):
            continue
        parts = line.split("\t")
        if len(parts) != 3 or parts[1] in axiom_rows:
            raise EvidenceError("malformed/duplicate Bernoulli axiom row")
        axiom_rows[parts[1]] = set(filter(None, parts[2].split(";")))
    for name in names:
        if axiom_rows.get(name) != set(ALLOWED_AXIOMS):
            raise EvidenceError(
                f"Bernoulli witness {name} lacks exact standard-only axioms"
            )
    try:
        results = json.loads(BERNOULLI_RESULTS.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise EvidenceError("invalid Bernoulli witness results JSON") from exc
    expected_gradient = {
        "endpoint": "BernoulliLSI.gradient_term_symmetric",
        "semantic_verdict": "REPAIRED_NONVACUOUS",
        "tier_c_required": False,
        "calibration_witnesses": list(names),
        "current_statement_rehabilitated": True,
    }
    if (
        not isinstance(results, dict)
        or results.get("overall") != "PASS"
        or results.get("gradient_review") != expected_gradient
    ):
        raise EvidenceError("Bernoulli witness semantic result is not exact")
    required_provenance_paths = (
        BERNOULLI_RUNNER,
        BERNOULLI_WITNESS,
        BERNOULLI_LEDGER,
        BERNOULLI_SUPPLEMENT,
        BERNOULLI_TIER_A_REVIEW,
        BERNOULLI_FULL_TIER_A_REVIEW,
        BERNOULLI_AXIOM_HARNESS,
        BERNOULLI_PLANTED_BAD,
        LOGS / "axiom_declaration_types.tsv",
        LOGS / "axiom_declaration_binders.tsv",
        LOGS / "axiom_direct_dependencies.tsv",
        LOGS / "axiom_audit_summary.txt",
        BERNOULLI_BUILD_LOG,
        BERNOULLI_AXIOM_LOG,
        LOGS / "v6_tier_c_ch8_9_planted_bad.log",
    )
    expected_provenance = {
        path.relative_to(ROOT).as_posix(): sha256_file(path)
        for path in required_provenance_paths
    }
    if (
        results.get("source", {}).get("sha256")
        != sha256_file(BERNOULLI_WITNESS)
        or results.get("provenance")
        != {"mode": "full", "sha256": expected_provenance}
    ):
        raise EvidenceError(
            "Bernoulli witness result is not bound to the current source, "
            "V4 evidence, and Lean transcripts"
        )
    result_mtime = BERNOULLI_RESULTS.stat().st_mtime_ns
    if any(
        path.stat().st_mtime_ns > result_mtime
        for path in required_provenance_paths
    ):
        raise EvidenceError(
            "Bernoulli witness result predates a bound source/evidence artifact"
        )
    witness_mtime = BERNOULLI_WITNESS.stat().st_mtime_ns
    if any(
        path.stat().st_mtime_ns < witness_mtime
        for path in (BERNOULLI_BUILD_LOG, BERNOULLI_AXIOM_LOG)
    ):
        raise EvidenceError(
            "Bernoulli Lean transcript predates the current witness source"
        )
    return {
        path.relative_to(ROOT).as_posix(): sha256_file(path) for path in paths
    }


def render_tsv(columns: Sequence[str], rows: Sequence[Mapping[str, object]]) -> str:
    buffer = io.StringIO(newline="")
    writer = csv.DictWriter(
        buffer,
        fieldnames=list(columns),
        delimiter="\t",
        lineterminator="\n",
        extrasaction="raise",
    )
    writer.writeheader()
    for row in rows:
        missing = [column for column in columns if column not in row]
        if missing:
            raise EvidenceError(f"generated row lacks fields {missing}")
        writer.writerow({column: row[column] for column in columns})
    return buffer.getvalue()


def build_artifacts() -> tuple[dict[Path, str], dict[str, object]]:
    source_digest = assert_manifest_current()
    round5_roles = validate_configuration()
    added_names, modified_names, change_hash, same_name_hash = load_change_logs()
    review_row_by_endpoint = {
        endpoint: spec.review_row_id
        for spec in ROUND5_SPECS
        for endpoint in spec.endpoints
    }
    reviewed_type_hashes, review_baseline_hash = load_review_baseline(
        review_row_by_endpoint,
        added_names,
        modified_names,
    )
    v4_completion, v4_completion_hash = load_v4_completion(source_digest)
    historical_hash = sha256_file(HISTORICAL_ROWS)
    census_hash = sha256_file(CENSUS)
    historical = keyed_rows(
        read_tsv(HISTORICAL_ROWS, HISTORICAL_COLUMNS),
        "row_id",
        path=HISTORICAL_ROWS,
    )
    census = keyed_rows(read_tsv(CENSUS, CENSUS_COLUMNS), "row_id", path=CENSUS)
    axioms, axiom_hash = load_axioms()
    v6_locations, v6_hash, v6_match_counts = load_v6_locations()
    exercise_endpoints, exercise_hash = load_exercise_endpoints()
    bernoulli_witness_hashes = validate_bernoulli_witness()

    expected_history_ids = {spec.historical_flag_id for spec in OVERLAY_SPECS}
    actual_partial_ids = {
        row_id
        for row_id, row in historical.items()
        if row["historical_status"] == "HISTORICAL-CORE-PARTIAL"
    }
    if actual_partial_ids != expected_history_ids:
        raise EvidenceError(
            "historical PARTIAL set mismatch: "
            f"expected={sorted(expected_history_ids)} actual={sorted(actual_partial_ids)}"
        )
    if len({spec.census_row_id for spec in OVERLAY_SPECS}) != 5:
        raise EvidenceError("overlay census IDs are not unique")
    if len({spec.overlay_id for spec in OVERLAY_SPECS}) != 5:
        raise EvidenceError("overlay IDs are not unique")

    all_source_endpoints = {
        endpoint
        for spec in ROUND5_SPECS
        for endpoint in spec.endpoints
    }
    all_overlay_endpoints = {
        endpoint
        for spec in OVERLAY_SPECS
        for endpoint in spec.endpoints
    }
    require_standard_endpoints(all_source_endpoints | all_overlay_endpoints, axioms)

    closures, dependency_hash, dependency_passes, dependency_edge_count = (
        compute_dependency_closures(CONE_SPECS, axioms)
    )
    if dependency_edge_count != v4_completion["direct_dependency_edges"]:
        raise EvidenceError(
            "fresh V4 dependency row count disagrees with completion manifest: "
            f"{dependency_edge_count} != "
            f"{v4_completion['direct_dependency_edges']}"
        )
    v6_universe = set(v6_locations)
    projected_members: dict[str, set[str]] = {}
    for spec in CONE_SPECS:
        roots = set(spec.roots)
        missing_roots = sorted(roots - set(closures[spec.cone_id]))
        if missing_roots:
            raise EvidenceError(f"{spec.cone_id}: roots missing from closure {missing_roots}")
        projected_members[spec.cone_id] = (
            set(closures[spec.cone_id]) & v6_universe
        ) | roots
        missing_required_members = (
            set(spec.required_members) - projected_members[spec.cone_id]
        )
        if missing_required_members:
            raise EvidenceError(
                f"{spec.cone_id}: required reviewed members absent from closure: "
                f"{sorted(missing_required_members)}"
            )
        require_standard_endpoints(spec.required_members, axioms)

    for spec in ROUND5_SPECS:
        required, _pdf_only = round5_roles[spec.review_row_id]
        for cone_id in spec.cone_ids:
            missing = required - projected_members[cone_id]
            if missing:
                raise EvidenceError(
                    f"{spec.review_row_id}: cone-required endpoints absent "
                    f"from {cone_id}: {sorted(missing)}"
                )
    for spec in OVERLAY_SPECS:
        missing = set(spec.endpoints) - projected_members[spec.cone_id]
        if missing:
            raise EvidenceError(
                f"{spec.overlay_id}: endpoints absent from {spec.cone_id}: "
                f"{sorted(missing)}"
            )

    f11_required, f11_pdf_only = round5_roles["R5-F11"]
    expected_f11_added = {
        "HDP.Chapter1.extendedMGF",
        "HDP.Chapter1.extendedMGF_eq_ofReal_mgf",
    }
    if f11_required != expected_f11_added or not f11_required <= added_names:
        raise EvidenceError(
            "R5-F11 changed/cone-required endpoints do not match the two "
            "mechanically logged additions"
        )
    if f11_pdf_only & (added_names | modified_names):
        raise EvidenceError(
            "R5-F11 PDF-only endpoint is classified as added or same-name changed"
        )

    selected_endpoints = (
        all_source_endpoints
        | all_overlay_endpoints
        | set().union(*projected_members.values())
    )
    missing_axiom_rows = sorted(selected_endpoints - set(axioms))
    if missing_axiom_rows:
        raise EvidenceError(
            f"selected endpoints missing from axiom audit: {missing_axiom_rows[:20]}"
        )
    type_hashes, type_evidence_hash = load_type_hashes(selected_endpoints, axioms)
    mismatched_reviewed_types = {
        endpoint: (reviewed_type_hashes[endpoint], type_hashes.get(endpoint))
        for endpoint in reviewed_type_hashes
        if type_hashes.get(endpoint) != reviewed_type_hashes[endpoint]
    }
    if mismatched_reviewed_types:
        raise EvidenceError(
            "reviewed Round 5 endpoint type changed; explicit semantic re-review "
            f"is required: {list(mismatched_reviewed_types.items())[:10]}"
        )
    locations = resolve_locations(selected_endpoints, axioms, v6_locations)
    pdf_hash, _page_text_hashes = check_pdf()

    round5_by_id = {spec.review_row_id: spec for spec in ROUND5_SPECS}
    if len(round5_by_id) != 11:
        raise EvidenceError("Round 5 specification is not exactly 11 unique rows")
    expected_round5_multiset = [
        "F-01",
        "F-02",
        "F-04",
        "F-05",
        "F-06",
        "F-07",
        "F-07",
        "F-08",
        "F-09",
        "F-10",
        "F-11",
    ]
    if sorted(spec.finding_id for spec in ROUND5_SPECS) != sorted(
        expected_round5_multiset
    ):
        raise EvidenceError("Round 5 finding multiset is not the required 11 obligations")

    overlay_rows: list[dict[str, object]] = []
    for spec in OVERLAY_SPECS:
        history = historical[spec.historical_flag_id]
        census_row = census.get(spec.census_row_id)
        if census_row is None:
            raise EvidenceError(f"missing census row {spec.census_row_id}")
        candidates = json.loads(history["candidate_census_ids"])
        flags = json.loads(census_row["faithful_historical_flag_ids"])
        if candidates != [spec.census_row_id]:
            raise EvidenceError(
                f"{spec.historical_flag_id}: candidate census IDs {candidates}"
            )
        if flags != [spec.historical_flag_id]:
            raise EvidenceError(
                f"{spec.census_row_id}: historical flag IDs {flags}"
            )
        if census_row["source_status_cell"] != "PARTIAL":
            raise EvidenceError(
                f"{spec.census_row_id}: frozen source status is not PARTIAL"
            )
        if census_row["source_status_class"] != "PARTIAL":
            raise EvidenceError(
                f"{spec.census_row_id}: frozen source class is not PARTIAL"
            )
        if census_row["coverage_bucket"] != "core_formalized":
            raise EvidenceError(
                f"{spec.census_row_id}: coverage bucket is not core_formalized"
            )
        round5_spec = round5_by_id[spec.round5_review_row_id]
        if set(spec.endpoints) - set(round5_spec.endpoints):
            raise EvidenceError(
                f"{spec.overlay_id}: endpoints are not covered by "
                f"{spec.round5_review_row_id}"
            )
        overlay_rows.append(
            {
                "overlay_id": spec.overlay_id,
                "historical_flag_id": spec.historical_flag_id,
                "census_row_id": spec.census_row_id,
                "book_ref": history["book_ref"],
                "historical_status": history["historical_status"],
                "historical_detail": history["historical_detail"],
                "finding_id": spec.finding_id,
                "current_status": "CORE_FORMALIZED_SOURCE_FAITHFUL",
                "current_coverage_bucket": "core_formalized",
                "current_endpoint_names": json_cell(list(spec.endpoints)),
                "source_locations": json_cell(
                    {
                        endpoint: locations[endpoint].render()
                        for endpoint in spec.endpoints
                    }
                ),
                "round_fixed": "1",
                "round5_review_row_id": spec.round5_review_row_id,
                "dependency_cone_id": spec.cone_id,
                "axiom_status": "STANDARD_ONLY",
                "historical_inventory_sha256": historical_hash,
                "census_inventory_sha256": census_hash,
                "axiom_audit_sha256": axiom_hash,
                "v4_completion_sha256": v4_completion_hash,
                "review_baseline_sha256": review_baseline_hash,
                "source_manifest_digest": source_digest,
                "resolution": spec.resolution,
            }
        )

    round5_rows: list[dict[str, object]] = []
    allowed_verdicts = {
        "SOURCE_FAITHFUL",
        "SOURCE_FAITHFUL_ADDITIVE_INTERFACE",
        "SOURCE_FAITHFUL_DOMAIN_REPAIR",
    }
    for spec in ROUND5_SPECS:
        required, pdf_only = round5_roles[spec.review_row_id]
        if spec.verdict not in allowed_verdicts:
            raise EvidenceError(f"{spec.review_row_id}: invalid verdict {spec.verdict}")
        if not spec.rationale or not REVIEWER or not REVIEW_TIMESTAMP:
            raise EvidenceError(f"{spec.review_row_id}: blank review attestation")
        round5_rows.append(
            {
                "review_row_id": spec.review_row_id,
                "finding_id": spec.finding_id,
                "finding_component": spec.finding_component,
                "round": "5",
                "book_ref": spec.book_ref,
                "pdf_logical_path": PDF_LOGICAL_PATH,
                "pdf_sha256": pdf_hash,
                "physical_pages": json_cell(list(spec.physical_pages)),
                "printed_pages": json_cell(list(spec.printed_pages)),
                "pdf_anchors": json_cell(list(spec.anchors)),
                "current_endpoint_names": json_cell(list(spec.endpoints)),
                "endpoint_review_role_map": json_cell(
                    {
                        endpoint: (
                            "PDF_TYPE_AXIOM_AND_DEPENDENCY_CONE"
                            if endpoint in required
                            else "PDF_TYPE_AXIOM_ONLY_UNCHANGED"
                        )
                        for endpoint in spec.endpoints
                    }
                ),
                "endpoint_type_sha256_map": json_cell(
                    {endpoint: type_hashes[endpoint] for endpoint in spec.endpoints}
                ),
                "endpoint_axiom_status_map": json_cell(
                    {endpoint: "STANDARD_ONLY" for endpoint in spec.endpoints}
                ),
                "source_locations": json_cell(
                    {
                        endpoint: locations[endpoint].render()
                        for endpoint in spec.endpoints
                    }
                ),
                "semantic_relation": spec.semantic_relation,
                "assumption_delta": (
                    "LEAN_RAW_COVARIANCE_HELPER_IS_TOTALIZED_OFF_THE_PDF_"
                    "FINITE_SECOND_MOMENT_DOMAIN; MEMLP_RESTRICTED_NEIGHBORING_"
                    "THEOREMS_AND_CHAPTER3_IDENTITY_RECORD_THE_INTENDED_DOMAIN"
                    if spec.review_row_id == "R5-F11"
                    else "NONE_RELATIVE_TO_PDF"
                ),
                "verdict": spec.verdict,
                "reviewer": REVIEWER,
                "review_timestamp": REVIEW_TIMESTAMP,
                "rationale": spec.rationale,
                "overlay_ids": json_cell(list(spec.overlay_ids)),
                "dependency_cone_ids": json_cell(list(spec.cone_ids)),
                "axiom_audit_sha256": axiom_hash,
                "type_evidence_sha256": type_evidence_hash,
                "v6_tier_a_sha256": v6_hash,
                "declaration_change_log_sha256": change_hash,
                "same_name_change_log_sha256": same_name_hash,
                "v4_completion_sha256": v4_completion_hash,
                "review_baseline_sha256": review_baseline_hash,
                "source_manifest_digest": source_digest,
            }
        )

    round5_endpoint_to_row = review_row_by_endpoint

    cone_rows: list[dict[str, object]] = []
    cone_counts: dict[str, int] = {}
    exercise_sorry_count = 0
    for spec in CONE_SPECS:
        members = projected_members[spec.cone_id]
        cone_counts[spec.cone_id] = len(members)
        roots = set(spec.roots)
        for member in sorted(members):
            distance, predecessor, origin = closures[spec.cone_id][member]
            row = axioms[member]
            status = proof_status(member, row, exercise_endpoints)
            if status == "INTENTIONAL_EXERCISE_SORRY_STATEMENT_ONLY":
                exercise_sorry_count += 1
                role = "EXERCISE_STATEMENT"
                semantic_status = "STATEMENT_ONLY_REVIEWED_INTENTIONAL_EXERCISE"
                semantic_evidence = (
                    "exercise_leaf_declarations.tsv;"
                    "Verification/FINAL_CORRECTION_REPORT.md#re-audited-dependency-cones"
                )
            elif member in roots:
                role = "ROOT"
                if spec.cone_id == "C-BERNOULLI":
                    semantic_status = "COMPILED_NONZERO_WITNESS_REPLAYED"
                    semantic_evidence = (
                        "Verification/scripts/witnesses/V6TierCCh8_9.lean:"
                        "tierA_gradient_term_fin1_indicator_nonzero;"
                        "tierA_gradient_term_symmetric_fin1_indicator_instance"
                    )
                elif member in round5_endpoint_to_row:
                    semantic_status = "PDF_SOURCE_OBLIGATION_REPLAYED"
                    semantic_evidence = round5_endpoint_to_row[member]
                else:
                    semantic_status = "DEPENDENCY_TYPE_AXIOM_REPLAYED"
                    semantic_evidence = (
                        "Verification/FINAL_CORRECTION_REPORT.md#re-audited-dependency-cones"
                    )
            else:
                role = "DIRECT_CONSUMER" if distance == 1 else "TRANSITIVE_CONSUMER"
                if member in round5_endpoint_to_row:
                    semantic_status = "PDF_SOURCE_OBLIGATION_REPLAYED"
                    semantic_evidence = round5_endpoint_to_row[member]
                else:
                    semantic_status = "DEPENDENCY_TYPE_AXIOM_REPLAYED"
                    semantic_evidence = (
                        "Verification/FINAL_CORRECTION_REPORT.md#re-audited-dependency-cones"
                    )
            if member in roots:
                if distance != 0 or predecessor or origin:
                    raise EvidenceError(f"{spec.cone_id}: malformed root state {member}")
            else:
                if distance <= 0 or not predecessor or origin not in {"type", "value"}:
                    raise EvidenceError(
                        f"{spec.cone_id}: malformed dependency state {member}"
                    )
            cone_rows.append(
                {
                    "cone_id": spec.cone_id,
                    "finding_ids": json_cell(list(spec.finding_ids)),
                    "root_endpoints": json_cell(list(spec.roots)),
                    "required_endpoint_members": json_cell(
                        list(spec.required_members)
                    ),
                    "member_endpoint": member,
                    "member_module": row.module,
                    "member_kind": row.kind,
                    "source_path": locations[member].path,
                    "source_line": str(locations[member].line),
                    "closure_universe": "V6_TIER_A_UNIQUE_V4_PLUS_ROOTS",
                    "member_role": role,
                    "distance": str(distance),
                    "canonical_predecessor": predecessor,
                    "predecessor_in_ledger": (
                        "" if not predecessor else str(predecessor in members).lower()
                    ),
                    "edge_origin": origin,
                    "statement_type_sha256": type_hashes[member],
                    "axiom_set": ";".join(sorted(row.axioms)),
                    "proof_status": status,
                    "semantic_review_status": semantic_status,
                    "semantic_review_evidence": semantic_evidence,
                    "semantic_witness_sha256_map": json_cell(
                        bernoulli_witness_hashes
                        if spec.cone_id == "C-BERNOULLI"
                        else {}
                    ),
                    "dependency_edges_sha256": dependency_hash,
                    "axiom_audit_sha256": axiom_hash,
                    "type_evidence_sha256": type_evidence_hash,
                    "v6_tier_a_sha256": v6_hash,
                    "exercise_inventory_sha256": exercise_hash,
                    "declaration_change_log_sha256": change_hash,
                    "same_name_change_log_sha256": same_name_hash,
                    "v4_completion_sha256": v4_completion_hash,
                    "review_baseline_sha256": review_baseline_hash,
                    "source_manifest_digest": source_digest,
                }
            )

    # The frozen census arithmetic is independently recomputed rather than
    # inferred from the prose report.
    frozen_core_rows = [
        row for row in census.values() if row["coverage_bucket"] == "core_formalized"
    ]
    frozen_partial_core = [
        row for row in frozen_core_rows if row["source_status_class"] == "PARTIAL"
    ]
    nonpartial_core = [
        row for row in frozen_core_rows if row["source_status_class"] != "PARTIAL"
    ]
    if len(frozen_partial_core) != 5 or len(nonpartial_core) != 763:
        raise EvidenceError(
            "frozen/current core arithmetic mismatch: "
            f"nonpartial={len(nonpartial_core)} partial={len(frozen_partial_core)}"
        )
    if len(nonpartial_core) + len(overlay_rows) != 768:
        raise EvidenceError("current core projection is not 763 + 5 = 768")

    artifacts = {
        OVERLAY_OUT: render_tsv(OVERLAY_COLUMNS, overlay_rows),
        ROUND5_OUT: render_tsv(ROUND5_COLUMNS, round5_rows),
        CONES_OUT: render_tsv(CONE_COLUMNS, cone_rows),
    }
    # Detect a concurrent source edit after the expensive dependency/type/PDF
    # scans and before the caller writes or accepts any artifact.
    ending_digest = assert_manifest_current()
    if ending_digest != source_digest:
        raise EvidenceError(
            f"source manifest changed during gate: {source_digest} -> {ending_digest}"
        )
    summary: dict[str, object] = {
        "source_manifest_digest": source_digest,
        "overlay_rows": len(overlay_rows),
        "round5_rows": len(round5_rows),
        "dependency_rows": len(cone_rows),
        "cone_counts": cone_counts,
        "intentional_exercise_sorry_rows": exercise_sorry_count,
        "dependency_passes": dependency_passes,
        "dependency_edges_sha256": dependency_hash,
        "dependency_edge_rows": dependency_edge_count,
        "axiom_audit_sha256": axiom_hash,
        "type_evidence_sha256": type_evidence_hash,
        "v6_tier_a_sha256": v6_hash,
        "v6_match_counts": v6_match_counts,
        "historical_inventory_sha256": historical_hash,
        "census_inventory_sha256": census_hash,
        "declaration_change_log_sha256": change_hash,
        "same_name_change_log_sha256": same_name_hash,
        "v4_completion_sha256": v4_completion_hash,
        "review_baseline_sha256": review_baseline_hash,
        "bernoulli_witness_sha256": bernoulli_witness_hashes,
        "pdf_sha256": pdf_hash,
        "artifact_sha256": {
            path.relative_to(ROOT).as_posix(): sha256_text(text)
            for path, text in artifacts.items()
        },
    }
    return artifacts, summary


def print_summary(label: str, summary: Mapping[str, object]) -> None:
    print(f"PASS07 EVIDENCE {label}")
    print(f"source_manifest_digest: {summary['source_manifest_digest']}")
    print(f"overlay_rows: {summary['overlay_rows']}")
    print(f"round5_rows: {summary['round5_rows']}")
    print(f"dependency_rows: {summary['dependency_rows']}")
    print(f"cone_counts: {json_cell(summary['cone_counts'])}")
    print(
        "intentional_exercise_sorry_rows: "
        f"{summary['intentional_exercise_sorry_rows']}"
    )
    print(f"dependency_passes: {summary['dependency_passes']}")
    print(f"dependency_edge_rows: {summary['dependency_edge_rows']}")
    for field in (
        "dependency_edges_sha256",
        "axiom_audit_sha256",
        "type_evidence_sha256",
        "v6_tier_a_sha256",
        "historical_inventory_sha256",
        "census_inventory_sha256",
        "declaration_change_log_sha256",
        "same_name_change_log_sha256",
        "v4_completion_sha256",
        "review_baseline_sha256",
        "pdf_sha256",
    ):
        print(f"{field}: {summary[field]}")
    print(f"v6_match_counts: {json_cell(summary['v6_match_counts'])}")
    print(
        "bernoulli_witness_sha256: "
        f"{json_cell(summary['bernoulli_witness_sha256'])}"
    )
    artifact_hashes = summary["artifact_sha256"]
    assert isinstance(artifact_hashes, dict)
    for path, digest in sorted(artifact_hashes.items()):
        print(f"artifact_sha256 {path}: {digest}")


def generate() -> int:
    artifacts, summary = build_artifacts()
    for path, text in artifacts.items():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8", newline="")
    print_summary("GENERATION PASS", summary)
    return 0


def check() -> int:
    artifacts, summary = build_artifacts()
    errors: list[str] = []
    for path, expected in artifacts.items():
        if not path.is_file():
            errors.append(f"artifact missing: {path}")
            continue
        actual_bytes = path.read_bytes()
        expected_bytes = expected.encode("utf-8")
        if actual_bytes != expected_bytes:
            errors.append(
                f"artifact drift: {path} "
                f"expected_sha256={sha256_text(expected)} "
                f"actual_sha256={hashlib.sha256(actual_bytes).hexdigest()}"
            )
    if errors:
        raise EvidenceError("; ".join(errors))
    print_summary("CHECK PASS", summary)
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    action = parser.add_mutually_exclusive_group(required=True)
    action.add_argument("--generate", action="store_true")
    action.add_argument("--check", action="store_true")
    args = parser.parse_args()
    try:
        return generate() if args.generate else check()
    except (EvidenceError, OSError, subprocess.SubprocessError) as exc:
        print(f"PASS07 EVIDENCE GATE FAIL: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
