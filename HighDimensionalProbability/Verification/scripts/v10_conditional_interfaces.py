#!/usr/bin/env python3
"""V10 conditional-interface / undischarged-assumption census.

The check combines four deliberately different views:

* a fresh Lean environment harness over the complete current verified surface;
* an independent textual scan of the complete FILE-WALK UNIVERSE;
* the current V6 Tier-B theorem-endpoint set, validated against the fresh V4
  declaration and module inventories; and
* a fail-closed review table for every environment candidate classified
  ``CONSUMED-ONLY``.

The environment view enumerates Prop-valued definitions and abbreviations,
Prop-valued structure/class fields, and the parent interfaces that carry those
fields.  It also records every binder/conclusion reference and all Prop-valued
theorem binders for the unnamed inline-hypothesis review.  The textual view is
needed independently because an environment cannot expose a never-imported
file.

This tool does not call a conditional theorem a defect merely because it has
mathematical hypotheses.  It asks the narrower soundness question required by
V10: is a published result conditional on a project-owned principle or
certificate that the repository never supplies, and if so is that
conditionality disclosed and ledgered?
"""

from __future__ import annotations

import argparse
import collections
import csv
import dataclasses
import hashlib
import io
import re
import subprocess
import sys
from pathlib import Path
from typing import Iterable, Mapping, Sequence

from file_universe import ROOT, enumerate_universe
from lean_source_scanner import mask_lean_noncode
from v6_tier_a_scanner import extract_declarations


HDP = ROOT / "HighDimensionalProbability"
VERIFICATION = HDP / "Verification"
LOGS = VERIFICATION / "logs"
INVENTORY = VERIFICATION / "inventory"
REVIEW = VERIFICATION / "review"
SCRIPTS = VERIFICATION / "scripts"
HARNESS = ROOT / ".audit_work" / "verification" / "V10ConditionalInterfaces.lean"
PLANTED = ROOT / ".audit_work" / "verification" / "v10_conditional_positive.lean"
PASS07_APPENDIX_WITNESS = (
    SCRIPTS / "witnesses" / "Pass07FinalAppendixAxioms.lean"
)

ENV_MODULES = LOGS / "v10_environment_modules.txt"
ENV_CANDIDATES = LOGS / "v10_environment_candidates.tsv"
ENV_REFERENCES = LOGS / "v10_environment_references.tsv"
ENV_INLINE = LOGS / "v10_environment_inline_binders.tsv"
HARNESS_BUILD_LOG = LOGS / "v10_harness_build.log"
PLANTED_BUILD_LOG = LOGS / "v10_planted_build.log"
PASS07_APPENDIX_WITNESS_LOG = (
    LOGS / "v10_pass07_appendix_axioms_build.log"
)

RECERT_AUDIT = LOGS / "recert_axiom_audit.tsv"
RECERT_MODULES = LOGS / "recert_axiom_modules.txt"
RECERT_COVERAGE = LOGS / "recert_axiom_module_coverage.txt"
V7_CONSTANTS = LOGS / "recert_definition_constants.tsv"
V7_EDGES = LOGS / "recert_definition_dependency_edges.tsv"
V7_REVERSE = LOGS / "recert_definition_reverse_citations.tsv"
V7_DEAD_SWEEP = LOGS / "recert_definition_dead_code_sweep.tsv"
V7_MODULES = LOGS / "recert_definition_modules.txt"
V7_COVERAGE = LOGS / "recert_definition_module_coverage.txt"
V7_SUMMARY = LOGS / "recert_definition_sanity_summary.txt"

TIER_B_ENDPOINTS = LOGS / "recert_v6_tier_b_endpoints.tsv"
TIER_B_EXCLUSIONS = LOGS / "recert_v6_tier_b_endpoint_exclusions.tsv"
TIER_B_SUMMARY = LOGS / "recert_v6_tier_b_endpoint_summary.txt"
SOURCE_MANIFEST = LOGS / "source_manifest.txt"
SOURCE_MANIFEST_CHECK = LOGS / "source_manifest_recertification_check.txt"
DEPENDENCY_SCRIPTS = (
    SCRIPTS / "file_universe.py",
    SCRIPTS / "lean_source_scanner.py",
    SCRIPTS / "v6_tier_a_scanner.py",
    SCRIPTS / "build_v6_tier_b_endpoints.py",
)

OUT_TEXTUAL = INVENTORY / "v10_textual_predicates.tsv"
OUT_ENVIRONMENT = INVENTORY / "v10_environment_predicates.tsv"
OUT_DIFF = INVENTORY / "v10_environment_text_diff.tsv"
OUT_CENSUS = INVENTORY / "v10_predicate_census.tsv"
OUT_CONSUMERS = INVENTORY / "v10_consumers.tsv"
OUT_INLINE = INVENTORY / "v10_inline_hypotheses.tsv"
OUT_REVIEW = REVIEW / "v10_adjudication.tsv"
OUT_PRIMARY_REVIEW = REVIEW / "v10_primary_review_closure.tsv"
OUT_INLINE_REVIEW = REVIEW / "v10_inline_review_closure.tsv"
OUT_V6_RECONCILIATION = REVIEW / "v10_v6_review_reconciliation.tsv"
# Retain the established artifact path for bundle compatibility.  Its current
# contents reconcile removed interfaces and retained finite signatures, not
# historical live conditional-interface expectations.
OUT_RECONCILIATION = REVIEW / "v10_ledger_reconciliation.tsv"
OUT_V7_DEAD = REVIEW / "v10_v7_dead_reconciliation.tsv"
OUT_CALIBRATION = LOGS / "v10_calibration.tsv"
OUT_REVIEW_CLOSURE = LOGS / "v10_review_closure.txt"
OUT_SUMMARY = LOGS / "v10_summary.txt"
OUT_SOURCE_STATE = LOGS / "v10_source_state.txt"
OUT_COMMAND = LOGS / "v10_command.log"
OUT_SELF_TEST = LOGS / "v10_self_test.log"
OUT_SOURCE_PREVIEW = LOGS / "v10_source_preview.log"
OUT_CHECK = LOGS / "v10_check.log"

README_DOCS = (
    ROOT / "README.md",
    HDP / "README.md",
    VERIFICATION / "REVIEW_NOTES.md",
    VERIFICATION / "CORRECTION_LEDGER.md",
    VERIFICATION / "FINAL_CORRECTION_REPORT.md",
    VERIFICATION / "archive" / "FAITHFUL_PROOFREAD_REPORT.md",
    HDP / "APPENDIX_SUMMARY.md",
)

TIER_B_REVIEW_FILES = (
    REVIEW / "v6_tier_b_ch0_4.tsv",
    REVIEW / "v6_tier_b_ch5_7.tsv",
    REVIEW / "v6_tier_b_ch8_9.tsv",
    REVIEW / "v6_tier_b_supplement_ch0_4.tsv",
    REVIEW / "v6_tier_b_supplement_ch5_7.tsv",
    REVIEW / "v6_tier_b_supplement_ch8_9.tsv",
)

REVIEWED_RIEMANNIAN_INFRASTRUCTURE = (
    "HDP.Appendix.RiemannianDiffusionLaw"
)
EXPECTED_RIEMANNIAN_UNPUBLISHED_CONSUMERS = {
    "HDP.Appendix.RiemannianDiffusionLaw.hasExponentialEnergyBound",
    "HDP.Appendix.RiemannianDiffusionLaw.hasLogSobolevInequality",
    "HDP.Appendix.RiemannianDiffusionLaw.hasMeanConcentration",
    "HDP.Chapter5.special_orthogonal_concentration_of_diffusion",
}
KNOWN_SO_HELPER = (
    "HDP.Chapter5.special_orthogonal_concentration_of_diffusion"
)

REMOVED_DECLARATIONS = {
    "HDP.Chapter3.BorellConvexBodyPsiOnePrinciple":
        "BorellConvexBodyPsiOnePrinciple",
    "HDP.Chapter3.convexBodyUniform_marginal_subExponential_of_borell":
        "convexBodyUniform_marginal_subExponential_of_borell",
    "HDP.Chapter5.positive_ricci_concentration":
        "positive_ricci_concentration",
    "HDP.Chapter5.positive_ricci_concentration_psi2":
        "positive_ricci_concentration_psi2",
    "HDP.Chapter5.positive_ricci_concentration_psi2_of_lipschitz":
        "positive_ricci_concentration_psi2_of_lipschitz",
    "HDP.Chapter8.GaussianChevetUpperPrinciple":
        "GaussianChevetUpperPrinciple",
    "HDP.Chapter8.exercise_8_39a_gaussian_chevet_arbitrary_envelope":
        "exercise_8_39a_gaussian_chevet_arbitrary_envelope",
    "HDP.Chapter8.gaussianChevetExpectationEnvelope_ne_top_of_isBounded":
        "gaussianChevetExpectationEnvelope_ne_top_of_isBounded",
    "HDP.Chapter8.remark_8_6_3_gaussian_chevet_arbitrary_envelope":
        "remark_8_6_3_gaussian_chevet_arbitrary_envelope",
    "HDP.Chapter8.exercise_8_39a_gaussian_chevet_arbitrary":
        "exercise_8_39a_gaussian_chevet_arbitrary",
    "HDP.Chapter8.remark_8_6_3_gaussian_chevet_arbitrary":
        "remark_8_6_3_gaussian_chevet_arbitrary",
    "HDP.Chapter8.gaussianChevetUpperPrinciple_external":
        "gaussianChevetUpperPrinciple_external",
}

REMOVED_SOURCE_FILES = (
    "HighDimensionalProbability/Appendix/GaussianChevet.lean",
    "HighDimensionalProbability/Appendix/PositiveRicciConcentration.lean",
)

FINITE_CHEVET_ZERO_DECLARATIONS = {
    "HDP.Chapter8.exercise_8_39a_gaussian_chevet":
        "exercise_8_39a_gaussian_chevet",
    "HDP.Chapter8.remark_8_6_3_gaussian_chevet":
        "remark_8_6_3_gaussian_chevet",
}
EXPECTED_PASS07_CURRENT_AXIOM_REPLAYS = 15


@dataclasses.dataclass(frozen=True)
class SourceCommand:
    path: str
    module: str
    kind: str
    name: str
    line: int
    explicit_type: str
    statement: str


@dataclasses.dataclass(frozen=True)
class Candidate:
    module: str
    name: str
    private_user_name: str
    category: str
    source_kind: str
    parent: str
    prop_fields: tuple[str, ...]

    @property
    def display_name(self) -> str:
        return self.private_user_name or self.name


@dataclasses.dataclass(frozen=True)
class Reference:
    candidate: str
    source_module: str
    source: str
    source_private_user_name: str
    source_kind: str
    relation: str
    binder_index: str
    binder_name: str
    binder_info: str
    type_raw: str


@dataclasses.dataclass(frozen=True)
class InlineBinder:
    module: str
    declaration: str
    private_user_name: str
    binder_index: int
    binder_name: str
    binder_info: str
    head_name: str
    named_candidates: tuple[str, ...]
    type_raw: str


@dataclasses.dataclass(frozen=True)
class ReviewOverride:
    adjudication: str
    disclosure: str
    ledger: str
    rationale: str


# Every CONSUMED-ONLY row must be explicitly classified.  There are no live
# source-facing conditional-interface overrides after the 2026-07-20 removal;
# the analyzer refuses to certify if one is reintroduced without review.
REVIEW_OVERRIDES: dict[str, ReviewOverride] = {}


INLINE_OVERRIDES: dict[tuple[str, str], ReviewOverride] = {
    (
        "HDP.Chapter8.exercise_8_39a_gaussian_chevet",
        "hzero",
    ): ReviewOverride(
        adjudication="RETAINED-FINITE-ZERO-MEMBERSHIP",
        disclosure=(
            "Chapter8_Chaining.lean:24384-24400 exposes hzero : 0 ∈ T "
            "directly in the finite Exercise 8.39(a) theorem"
        ),
        ledger=(
            "the arbitrary-set conditional interface was removed; this "
            "finite zero-containing theorem remains source-visible"
        ),
        rationale=(
            "This is an explicit constructible finite-set membership "
            "hypothesis, not an unpublished universal principle."
        ),
    ),
    (
        "HDP.Chapter8.remark_8_6_3_gaussian_chevet",
        "hzero",
    ): ReviewOverride(
        adjudication="RETAINED-FINITE-ZERO-MEMBERSHIP",
        disclosure=(
            "Chapter8_Chaining.lean:24402-24426 exposes hzero : 0 ∈ T "
            "directly in the finite Remark 8.6.3 theorem"
        ),
        ledger=(
            "the arbitrary-set conditional interface was removed; this "
            "finite zero-containing theorem remains source-visible"
        ),
        rationale=(
            "This is an explicit constructible finite-set membership "
            "hypothesis, not an unpublished universal principle."
        ),
    ),
    (KNOWN_SO_HELPER, "hDiffusion"): ReviewOverride(
        adjudication="INFO-DISCLOSED-UNPUBLISHED-HELPER",
        disclosure=(
            "Appendix/SpecialOrthogonalConcentration.lean:58-69 calls this "
            "an exact reduction and identifies heat-diffusion construction "
            "as the remaining premise"
        ),
        ledger=(
            "not a published completion; the separate "
            "HDP.Chapter5.special_orthogonal_concentration endpoint is "
            "proved unconditionally at lines 127-279"
        ),
        rationale=(
            "This source-disclosed helper takes an inline family of "
            "diffusion certificates, but no published result depends on it; "
            "the headline SO theorem uses the independent ambient LSI route."
        ),
    ),
    (
        "HDP.Appendix.SpecialOrthogonal."
        "hasSubgaussianMGF_centered_of_ambient_logSobolev",
        "hLSI",
    ): ReviewOverride(
        adjudication="PROVED-DISCHARGED-LOCAL-CERTIFICATE",
        disclosure=(
            "Appendix/SpecialOrthogonalConcentration.lean:247-251 supplies "
            "specialOrthogonal_ambient_logSobolev to this helper"
        ),
        ledger=(
            "not an open item: the local ambient log-Sobolev premise is "
            "constructed in the same source proof"
        ),
        rationale=(
            "The expanded principle-name scan conservatively catches hLSI, "
            "but its only use is discharged by the proved "
            "specialOrthogonal_ambient_logSobolev theorem."
        ),
    ),
}

# The current-tree mixed-tier review clusters every direct consumed-only
# premise.  Published rows in this set are ordinary mathematical hypotheses
# (measurability, matrix
# structure, minimizer conditions, and similar constructible predicates), not
# unpublished universal principles.  Keeping the exact names here makes a
# newly introduced direct premise fail closed instead of inheriting a broad
# default.
REVIEWED_DIRECT_PUBLISHED_ORDINARY = frozenset(
    {
        "HDP.Chapter1.IsPoissonRV",
        "HDP.Chapter5.RealLoewnerLE",
        "HDP.Chapter6.IsDiagonalFree",
        "HDP.Chapter8.IsBooleanClassEmpiricalRiskMinimizer",
        "HDP.Chapter8.IsBooleanClassPopulationRiskMinimizer",
        "HDP.Chapter9.CommonSecondMoment",
        "HDP.Chapter9.IsL1RecoveryMinimizer",
        "HDP.Chapter9.IsNoisyConstrainedRecoveryMinimizer",
        "HDP.Chapter9.IsPenalizedRecoveryMinimizer",
        "HDP.Chapter9.IsPenaltyNorm",
        "HDP.Chapter9.IsRandomConstrainedRecoverySolution",
        "HDP.Chapter9.IsRandomNuclearRecoverySolution",
        "HDP.Chapter9.IsRestrictedIsometry",
        "HDP.Chapter9.RelativeRowPsi2Bound",
        "HDP.Chapter9.SetClosedHullBallSandwich",
        "HDP.Chapter9.WithinSetDvoretzkyEffectiveDimension",
        "HDP.HasGaussianVectorLaw",
        "HDP.IsEpsilonNet",
        "HDP.IsSubExponentialRandomVariable",
        "HDP.IsSubGaussianRandomVariable",
        "HDP.IsSubGaussianRandomVector",
        "HDP.RandomMatrix.MeasurableRows",
    }
)

# These exact direct premises occur only in unpublished declarations.  Most
# are ordinary local conditions; the smaller INFO set below identifies the
# genuinely certificate-like infrastructure worth surfacing as a grouped
# observation.  Keeping the full direct-name set exact makes any new direct
# premise fail closed.
REVIEWED_DIRECT_UNPUBLISHED_INFRASTRUCTURE = frozenset(
    {
        "EfronSteinApp.CompactlySupportedSmooth",
        "GaussianLSI.MemW12GaussianPi",
        "HDP.Appendix.BochnerRicciCertificate",
        "HDP.Appendix.HasExponentialEnergyBound",
        "HDP.Appendix.HasGammaTwoLowerBound",
        "HDP.Appendix.HasHerbstEntropyBound",
        "HDP.Appendix.HasUniformPositiveBounds",
        "HDP.Appendix.MarkovSemigroupData",
        "HDP.Appendix.MarkovSemigroupData.GammaTwoFlowCertificate",
        REVIEWED_RIEMANNIAN_INFRASTRUCTURE,
        "HDP.Chapter3.ReverseThinShellLargeEnough",
        "HDP.Chapter4.Exercise.HasTailIntegralRepresentation",
        "HDP.Chapter4.Exercise.IsOrthogonalProjectionMatrix",
        "HDP.Chapter5.BoundedSecondMomentSample",
        "HDP.Chapter6.Exercise.IsIndependentScalarCopy",
        "HDP.Chapter6.Exercise.IsIndependentVectorCopy",
        "HDP.Chapter7.BrownianDiscrete.hitAt",
        "HDP.Chapter8.EmpiricalSymmetrizationExhaustion",
        "HDP.Chapter8.EmpiricalSymmetrizationSignedExhaustion",
        "HDP.Chapter8.Exercise.AdmissibleSequence",
        "HDP.Chapter8.Exercise.IsLabeledEmpiricalRiskMinimizerIn",
        "HDP.Chapter8.Exercise.IsLabeledPopulationRiskMinimizerIn",
        "HDP.Chapter8.Exercise.UnitIntervalLipschitzHypothesis",
        "HDP.Chapter8.IsBooleanEmpiricalRiskMinimizer",
        "HDP.Chapter8.IsBooleanFunctionClass",
        "HDP.Chapter8.IsBooleanPopulationRiskMinimizer",
        "HDP.Chapter8.IsUniformGlivenkoCantelli",
        "HDP.Chapter8.NonemptyFiniteSubset",
        "HDP.Chapter9.HasDiameterBound",
        "HDP.Chapter9.HasExactL1NullspaceProperty",
        "HDP.Chapter9.IsKnownSupportDecoder",
        "HDP.Chapter9.IsRandomNuclearRecoverySolution_finitePrior",
        "HDP.Chapter9.MatrixColumnsInGeneralPosition",
        "HDP.Chapter9.NullspaceProperty",
        "HDP.Chapter9.SparseInjective",
        "HDP.Chapter9.UniformUniqueL1Recovery",
        "HDP.Chapter9.WithinDvoretzkyEffectiveDimension",
        "HDP.Chapter9.finiteKernelHits",
        "MatrixConcentration.IsBernoulli",
        "MatrixConcentration.IsStdGaussian",
        "MatrixConcentration.IsSymmetricRV",
        "RademacherApprox.IndepRademacherSeq",
    }
)

DISCLOSED_UNPUBLISHED_PRIMARY_INFO = frozenset(
    {
        "HDP.Appendix.BochnerRicciCertificate",
        "HDP.Appendix.HasExponentialEnergyBound",
        "HDP.Appendix.HasGammaTwoLowerBound",
        "HDP.Appendix.HasHerbstEntropyBound",
        "HDP.Appendix.HasUniformPositiveBounds",
        "HDP.Appendix.MarkovSemigroupData",
        "HDP.Appendix.MarkovSemigroupData.GammaTwoFlowCertificate",
        "LogSobolev.dualEntropySet",
        "LogSobolev.dualEntropySetT",
    }
)

EXPECTED_V10_F1_INFO_ITEMS = frozenset(
    {
        *DISCLOSED_UNPUBLISHED_PRIMARY_INFO,
        f"{KNOWN_SO_HELPER}[0:hDiffusion]",
    }
)

EXPECTED_PRIMARY_ORDINARY_CLAIMED_ONLY = {
    "HDP.Chapter1.IsPoissonRV": ("HDP.Chapter1.poisson_pmf",),
    "HDP.Chapter8.booleanLpClass": (
        "HDP.Chapter8.theorem_8_3_13_vc_covering",
    ),
    "HDP.Chapter9.measurementFiber": (
        "HDP.Chapter9.IsConstrainedRecoverySolution",
    ),
}

# These digests bind the manual group review to the exact current population,
# consumer keys, publication flags, and raw kernel types.  Any new or changed
# row makes V10 INCOMPLETE until the review and digest are deliberately
# refreshed.
EXPECTED_PRIMARY_REVIEW_COUNT = 250
EXPECTED_PRIMARY_REVIEW_DIGEST = (
    "196bb94c3ebe325d337a19f6523c176fb294c05af9f603000c8ee2ed6797d3cb"
)
EXPECTED_INLINE_HIGHER_ORDER_COUNT = 2911
EXPECTED_INLINE_HIGHER_ORDER_KEY_DIGEST = (
    "17366877da50fa50fe0ead802163a479e2a912cf8583f7ae2b35abd171e4c1c9"
)
EXPECTED_INLINE_HIGHER_ORDER_TYPE_DIGEST = (
    "c376a0c15a2da9f530128dac906b468291c27e5328b24dfbbe7b698600d41176"
)
EXPECTED_PRIMARY_V6_TARGET_COUNT = 84
EXPECTED_PRIMARY_V6_TARGET_DIGEST = (
    "34699a18f300a9c7d47c5a95bfb0b5d1a44ac5482efb5b9fbea244f4a4e6c9a0"
)
EXPECTED_INLINE_V6_TARGET_COUNT = 168
EXPECTED_INLINE_V6_TARGET_DIGEST = (
    "c98ec28e79cd3771ee7afe8769a79dd9a518e6735e4779a0465fe81a02d36c0f"
)
EXPECTED_INLINE_CLAIMED_ONLY_DECL_COUNT = 26
EXPECTED_INLINE_CLAIMED_ONLY_DECL_DIGEST = (
    "c8360d409eba05446125a4a246d8190178a8a73e71e150498370d0942ea53a05"
)
EXPECTED_INLINE_REVIEW_GROUP_COUNTS = {
    "NESTED_PI_OR_NONFORALL": (711, 55),
    "RELATION_LOGIC": (1123, 198),
    "ANALYTIC_REGULARITY": (770, 166),
    "PROBABILITY_LAW": (128, 26),
    "MATRIX_STRUCTURE": (126, 7),
    "SET_GEOMETRIC": (48, 5),
    "LOCAL_PREDICATE": (5, 0),
}

INLINE_RELATION_LOGIC_HEADS = frozenset(
    {"LE.le", "Eq", "Or", "LT.lt", "BddAbove", "Exists", "And", "Ne", "False"}
)
INLINE_ANALYTIC_HEADS = frozenset(
    {
        "Measurable",
        "MeasureTheory.Integrable",
        "AEMeasurable",
        "MeasurableSet",
        "MeasureTheory.MemLp",
        "Continuous",
        "Filter.Tendsto",
        "Filter.Eventually",
        "Filter.EventuallyLE",
        "Differentiable",
        "HasDerivAt",
        "LipschitzWith",
        "DifferentiableAt",
        "Filter.EventuallyEq",
        "IntervalIntegrable",
        "MeasureTheory.AEStronglyMeasurable",
        "Summable",
    }
)
INLINE_PROBABILITY_HEADS = frozenset(
    {
        "ProbabilityTheory.HasLaw",
        "ProbabilityTheory.IdentDistrib",
        "ProbabilityTheory.iIndepFun",
        "ProbabilityTheory.HasSubgaussianMGF",
        "ProbabilityTheory.HasGaussianLaw",
        "MeasureTheory.HasPDF",
        "ProbabilityTheory.IndepFun",
    }
)
INLINE_MATRIX_HEADS = frozenset(
    {"Matrix.IsHermitian", "Matrix.PosSemidef", "Matrix.PosDef", "Matrix.IsSymm"}
)
INLINE_SET_GEOMETRIC_HEADS = frozenset(
    {"Membership.mem", "Finset.Nonempty", "HasSubset.Subset", "ConvexOn"}
)



COMMAND_START = re.compile(
    r"""(?mx)
    ^[ \t]*
    (?:(?:@\[[^\r\n]*\])[ \t]*)*
    (?:(?:private|protected|noncomputable|unsafe|local|scoped)[ \t]+)*
    (?P<kind>def|abbrev|theorem|lemma|class|structure)[ \t]+
    (?P<name>«[^»]+»|[^\s(\[{:="]+)
    """
)

ANY_DECLARATION_START = re.compile(
    r"""(?mx)
    ^[ \t]*
    (?:(?:@\[[^\r\n]*\])[ \t]*)*
    (?:(?:private|protected|noncomputable|unsafe|local|scoped)[ \t]+)*
    (?:def|abbrev|theorem|lemma|class|structure|inductive|instance|
       example|axiom|opaque)[ \t]+
    """
)

OPEN_TO_CLOSE = {
    "(": ")",
    "[": "]",
    "{": "}",
    "⦃": "⦄",
    "⟨": "⟩",
}
CLOSE_TO_OPEN = {value: key for key, value in OPEN_TO_CLOSE.items()}


def module_for_path(relative_path: str) -> str:
    if relative_path == "HighDimensionalProbability.lean":
        return "HighDimensionalProbability"
    if relative_path.startswith("HighDimensionalProbability/"):
        return relative_path[: -len(".lean")].replace("/", ".")
    if relative_path.startswith("MatrixConcentration/"):
        return relative_path[: -len(".lean")].replace("/", ".")
    return ""


def _line_number(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def _normalize(text: str) -> str:
    return re.sub(r"\s+", " ", text).strip()


def _find_command_boundary(
    code: str, start: int, limit: int
) -> tuple[int | None, int | None]:
    stack: list[str] = []
    type_colon: int | None = None
    index = start
    while index < limit:
        character = code[index]
        if character in OPEN_TO_CLOSE:
            stack.append(character)
        elif character in CLOSE_TO_OPEN:
            if stack and stack[-1] == CLOSE_TO_OPEN[character]:
                stack.pop()
        elif not stack:
            if character == ":" and not code.startswith(":=", index):
                if type_colon is None:
                    type_colon = index
            elif code.startswith(":=", index):
                return type_colon, index
            elif (
                code.startswith("where", index)
                and (index == start or not (code[index - 1].isalnum() or code[index - 1] == "_"))
                and (
                    index + 5 == limit
                    or not (code[index + 5].isalnum() or code[index + 5] == "_")
                )
            ):
                return type_colon, index
        index += 1
    return type_colon, None


def parse_source_commands(path: Path) -> list[SourceCommand]:
    if path.is_symlink() or not path.is_file():
        raise ValueError(f"V10 source input is not a physical file: {path}")
    text = path.read_text(encoding="utf-8")
    code, diagnostics = mask_lean_noncode(text)
    if diagnostics:
        rendered = ", ".join(f"{kind}@{offset}" for kind, offset in diagnostics)
        raise ValueError(f"{path}: lexical masking diagnostics: {rendered}")
    relative = path.relative_to(ROOT).as_posix()
    matches = list(COMMAND_START.finditer(code))
    all_starts = [match.start() for match in ANY_DECLARATION_START.finditer(code)]
    commands: list[SourceCommand] = []
    for match in matches:
        later = [offset for offset in all_starts if offset > match.start()]
        limit = min(later) if later else len(code)
        type_colon, assignment = _find_command_boundary(code, match.end(), limit)
        if assignment is None:
            # Equation-compiler theorem clauses are irrelevant to the textual
            # def/abbrev predicate set, but retaining their statement prefix
            # still helps fixture and disclosure diagnostics.
            assignment = limit
        explicit_type = (
            _normalize(code[type_colon + 1 : assignment])
            if type_colon is not None
            else ""
        )
        commands.append(
            SourceCommand(
                path=relative,
                module=module_for_path(relative),
                kind=match.group("kind"),
                name=match.group("name"),
                line=_line_number(text, match.start()),
                explicit_type=explicit_type,
                statement=_normalize(code[match.start() : assignment]),
            )
        )
    return commands


def _is_explicit_prop_type(text: str) -> bool:
    value = text.strip()
    while value.startswith("(") and value.endswith(")"):
        value = value[1:-1].strip()
    return value == "Prop"


def enumerate_textual_predicates(
    universe_paths: Sequence[str],
) -> tuple[list[SourceCommand], list[SourceCommand]]:
    commands: list[SourceCommand] = []
    for relative in universe_paths:
        commands.extend(parse_source_commands(ROOT / relative))
    predicates = [
        command
        for command in commands
        if command.kind in {"def", "abbrev"}
        and _is_explicit_prop_type(command.explicit_type)
    ]
    return sorted(
        predicates,
        key=lambda row: (row.path, row.line, row.name),
    ), commands


def removed_source_references(
    universe_paths: Sequence[str],
) -> dict[str, list[str]]:
    """Find live code references to every removed declaration identifier.

    The scan is intentionally over masked source rather than parsed commands:
    a stale theorem application, type annotation, or import-side alias is as
    important as a stale declaration.  Comments and strings are excluded.
    """

    matches: dict[str, list[str]] = collections.defaultdict(list)
    patterns = {
        environment_name: re.compile(
            rf"(?<![A-Za-z0-9_']){re.escape(source_name)}"
            rf"(?![A-Za-z0-9_'])"
        )
        for environment_name, source_name in REMOVED_DECLARATIONS.items()
    }
    for relative in universe_paths:
        path = ROOT / relative
        text = path.read_text(encoding="utf-8")
        code, diagnostics = mask_lean_noncode(text)
        if diagnostics:
            rendered = ", ".join(
                f"{kind}@{offset}" for kind, offset in diagnostics
            )
            raise ValueError(
                f"{path}: lexical masking diagnostics: {rendered}"
            )
        for environment_name, pattern in patterns.items():
            found = [
                f"{relative}:{_line_number(text, match.start())}"
                for match in pattern.finditer(code)
            ]
            if found:
                matches[environment_name].extend(found)
    return dict(matches)


def _read_tsv(path: Path) -> list[dict[str, str]]:
    csv.field_size_limit(sys.maxsize)
    with path.open(encoding="utf-8", newline="") as handle:
        return list(csv.DictReader(handle, delimiter="\t"))


def read_candidates(path: Path = ENV_CANDIDATES) -> list[Candidate]:
    expected = (
        "module",
        "name",
        "private_user_name",
        "category",
        "source_kind",
        "parent",
        "prop_fields",
    )
    with path.open(encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle, delimiter="\t")
        if tuple(reader.fieldnames or ()) != expected:
            raise ValueError(
                f"{path}: columns {reader.fieldnames!r}, expected {expected!r}"
            )
        rows = [
            Candidate(
                module=row["module"],
                name=row["name"],
                private_user_name=row["private_user_name"],
                category=row["category"],
                source_kind=row["source_kind"],
                parent=(
                    "" if row["parent"] in {"", "_anonymous"} else row["parent"]
                ),
                prop_fields=tuple(filter(None, row["prop_fields"].split(";"))),
            )
            for row in reader
        ]
    names = [row.name for row in rows]
    duplicates = [
        name
        for name, count in collections.Counter(names).items()
        if count > 1
    ]
    if duplicates:
        raise ValueError(f"{path}: duplicate candidates: {duplicates[:20]}")
    return rows


def read_references(path: Path = ENV_REFERENCES) -> list[Reference]:
    rows = _read_tsv(path)
    return [
        Reference(
            candidate=row["candidate"],
            source_module=row["source_module"],
            source=row["source"],
            source_private_user_name=row["source_private_user_name"],
            source_kind=row["source_kind"],
            relation=row["relation"],
            binder_index=row["binder_index"],
            binder_name=row["binder_name"],
            binder_info=row["binder_info"],
            type_raw=row["type_raw"],
        )
        for row in rows
    ]


def read_inline(path: Path = ENV_INLINE) -> list[InlineBinder]:
    rows = _read_tsv(path)
    return [
        InlineBinder(
            module=row["module"],
            declaration=row["declaration"],
            private_user_name=row["private_user_name"],
            binder_index=int(row["binder_index"]),
            binder_name=row["binder_name"],
            binder_info=row["binder_info"],
            head_name=(
                "" if row["head_name"] in {"", "_anonymous"} else row["head_name"]
            ),
            named_candidates=tuple(
                filter(None, row["named_candidates"].split(";"))
            ),
            type_raw=row["type_raw"],
        )
        for row in rows
    ]


def source_locations(
    commands: Sequence[SourceCommand],
) -> dict[tuple[str, str], list[str]]:
    result: dict[tuple[str, str], list[str]] = collections.defaultdict(list)
    for command in commands:
        result[(command.module, command.name)].append(
            f"{command.path}:{command.line}"
        )
    return dict(result)


def match_source_location(
    module: str,
    display_name: str,
    locations: Mapping[tuple[str, str], list[str]],
) -> tuple[str, str]:
    matches = [
        location
        for (source_module, source_name), source_locations_ in locations.items()
        if source_module == module
        and (
            display_name == source_name
            or display_name.endswith("." + source_name)
        )
        for location in source_locations_
    ]
    if len(matches) == 1:
        return matches[0], "MATCHED"
    if not matches:
        return "", "ENVIRONMENT-ONLY"
    return ";".join(matches), "AMBIGUOUS"


def load_modules(path: Path) -> set[str]:
    modules = {
        line.strip()
        for line in path.read_text(encoding="utf-8").splitlines()
        if line.strip()
    }
    if not modules:
        raise ValueError(f"{path}: empty module inventory")
    return modules


def expected_modules(universe: Mapping[str, object]) -> set[str]:
    paths = [
        *list(universe["file_walk_universe"]),
        *list(universe["root_modules_separate"]),
    ]
    return {module_for_path(str(path)) for path in paths}


def load_v4_names(path: Path = RECERT_AUDIT) -> set[str]:
    rows = _read_tsv(path)
    names = {row["name"] for row in rows}
    if not names:
        raise ValueError(f"{path}: no declaration rows")
    return names


def load_tier_b() -> tuple[set[str], dict[str, dict[str, str]]]:
    rows = _read_tsv(TIER_B_ENDPOINTS)
    if not rows:
        raise ValueError(f"{TIER_B_ENDPOINTS}: no current endpoint rows")
    by_name = {row["name"]: row for row in rows}
    if len(by_name) != len(rows):
        raise ValueError(f"{TIER_B_ENDPOINTS}: duplicate endpoint names")
    return set(by_name), by_name


def load_v6_review_statuses() -> dict[str, set[str]]:
    """Index exact reviewed declarations/endpoints across all six V6 shards."""

    statuses: dict[str, set[str]] = collections.defaultdict(set)
    for path in TIER_B_REVIEW_FILES:
        for row in _read_tsv(path):
            status = row.get("verdict") or row.get("status") or ""
            names: set[str] = set()
            for field in (
                "resolved_declarations",
                "endpoint",
                "inventory_endpoint",
            ):
                names.update(
                    name.strip()
                    for name in row.get(field, "").split(";")
                    if name.strip()
                )
            for name in names:
                statuses[name].add(status)
    return dict(statuses)


def live_document_claims() -> str:
    return "\n".join(path.read_text(encoding="utf-8") for path in README_DOCS)


def is_document_claimed(name: str, claims: str) -> bool:
    """Conservatively recognize qualified or backtick-delimited claims.

    Live records often spell a declaration with its full environment name,
    but some tables use only the final Lean identifier.  Counting a
    backtick-delimited unqualified name as claimed errs on the safe side
    without treating ordinary prose words as declarations.
    """

    if name in claims:
        return True
    leaf = name.rsplit(".", 1)[-1]
    return re.search(
        rf"`(?:[^`\s]*\.)?{re.escape(leaf)}`",
        claims,
    ) is not None


def _render_tsv(fields: Sequence[str], rows: Iterable[Mapping[str, object]]) -> str:
    output = io.StringIO()
    writer = csv.DictWriter(
        output,
        fieldnames=list(fields),
        delimiter="\t",
        lineterminator="\n",
        extrasaction="raise",
    )
    writer.writeheader()
    for row in rows:
        writer.writerow({field: row.get(field, "") for field in fields})
    return output.getvalue()


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def _source_state_row(path: Path) -> str:
    digest = _sha256(path) if path.is_file() else "MISSING"
    return f"{digest}  {path.relative_to(ROOT).as_posix()}"


def _logged_command_passed(path: Path) -> bool:
    if not path.is_file():
        return False
    lines = path.read_text(encoding="utf-8").splitlines()
    return bool(lines) and lines[-1] == "exit_status: 0"


def validate_tier_b_freshness(v4_names: set[str]) -> tuple[set[str], list[str]]:
    tier_b, tier_b_rows = load_tier_b()
    errors: list[str] = []
    summary_text = TIER_B_SUMMARY.read_text(encoding="utf-8")
    if "verdict: PASS" not in summary_text:
        errors.append(f"{TIER_B_SUMMARY}: fresh endpoint builder did not PASS")
    expected_count_marker = f"unique_project_theorem_endpoints: {len(tier_b)}"
    if expected_count_marker not in summary_text:
        errors.append(
            f"{TIER_B_SUMMARY}: does not attest live endpoint count "
            f"{len(tier_b)}"
        )
    exclusions = _read_tsv(TIER_B_EXCLUSIONS)
    missing_project = sorted(
        {
            row.get("name", "")
            for row in exclusions
            if row.get("classification") == "MISSING_PROJECT_ENDPOINT"
        }
    )
    if missing_project:
        errors.append(
            "Tier-B endpoint exclusions contain missing project declarations: "
            + ", ".join(missing_project[:20])
        )
    missing = sorted(tier_b - v4_names)
    if missing:
        errors.append(
            "Tier-B endpoints absent from current V4 environment: "
            + ", ".join(missing[:20])
        )
    v4_rows = {row["name"]: row for row in _read_tsv(RECERT_AUDIT)}
    wrong_current_kind = sorted(
        name
        for name in tier_b
        if name in v4_rows and v4_rows[name].get("kind") != "theorem"
    )
    if wrong_current_kind:
        errors.append(
            "Tier-B endpoints not theorem constants in current V4: "
            + ", ".join(wrong_current_kind[:20])
        )
    stale_export_kind = sorted(
        name
        for name, row in tier_b_rows.items()
        if row.get("v4_kind") != "theorem"
    )
    if stale_export_kind:
        errors.append(
            "Tier-B export contains non-theorem endpoint kinds: "
            + ", ".join(stale_export_kind[:20])
        )
    return tier_b, errors


CONSUMER_RELATIONS = frozenset(
    {"binder", "conclusion_contains", "definition_body"}
)
PRODUCER_RELATIONS = frozenset({"conclusion_head", "conclusion_witness"})
PRODUCER_KINDS = frozenset(
    {"theorem", "definition", "abbrev", "opaque"}
)
RAW_EXPR_FIRST_CONST = re.compile(
    r"Lean\.Expr\.const `([^\s\[\)]+)"
)


def _sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def _line_population_digest(lines: Iterable[str]) -> str:
    return _sha256_text("\n".join(sorted(lines)) + "\n")


def _ordered_line_population_digest(lines: Sequence[str]) -> str:
    return _sha256_text("\n".join(lines) + "\n")


def _review_population_errors(
    label: str,
    actual_count: int,
    expected_count: int,
    actual_digests: Mapping[str, str],
    expected_digests: Mapping[str, str],
) -> list[str]:
    """Fail closed on either population cardinality or any bound digest."""

    errors: list[str] = []
    if actual_count != expected_count:
        errors.append(
            f"{label} count drift: expected {expected_count}, "
            f"found {actual_count}"
        )
    for digest_name, expected in expected_digests.items():
        actual = actual_digests.get(digest_name, "")
        if actual != expected:
            errors.append(
                f"{label} {digest_name} digest drift: expected {expected}, "
                f"found {actual}"
            )
    return errors


def _reference_head_name(row: Reference) -> str:
    match = RAW_EXPR_FIRST_CONST.search(row.type_raw)
    return match.group(1) if match is not None else ""


def _directly_assumes_candidate(
    candidate: str, references: Sequence[Reference]
) -> bool:
    return any(
        row.relation == "binder"
        and _reference_head_name(row) == candidate
        for row in references
    )


def _reference_review_key(row: Reference) -> str:
    return "|".join(
        (
            row.source_module,
            row.source,
            row.source_private_user_name,
            row.source_kind,
            row.relation,
            row.binder_index,
            row.binder_name,
            row.binder_info,
            _sha256_text(row.type_raw),
        )
    )


def _primary_review_key(
    candidate: Candidate,
    consumers: Sequence[Reference],
    published_consumers: Sequence[str],
    claimed_consumers: Sequence[str],
) -> str:
    consumer_digest = _sha256_text(
        ";".join(sorted(_reference_review_key(row) for row in consumers))
    )
    return "\t".join(
        (
            candidate.name,
            candidate.module,
            candidate.category,
            candidate.source_kind,
            (
                "direct"
                if _directly_assumes_candidate(candidate.name, consumers)
                else "nested-only"
            ),
            ";".join(published_consumers),
            ";".join(claimed_consumers),
            consumer_digest,
        )
    )


def _inline_review_key(row: InlineBinder, *, include_type: bool) -> str:
    fields = [
        row.module,
        row.declaration,
        row.private_user_name,
        str(row.binder_index),
        row.binder_name,
        row.binder_info,
        row.head_name,
        ";".join(row.named_candidates),
    ]
    if include_type:
        fields.append(row.type_raw)
    return "\t".join(fields)


def _strip_balanced_outer_parens(raw: str) -> str:
    value = raw.strip()
    while value.startswith("(") and value.endswith(")"):
        depth = 0
        closes_at_end = False
        for index, char in enumerate(value):
            if char == "(":
                depth += 1
            elif char == ")":
                depth -= 1
                if depth == 0:
                    closes_at_end = index == len(value) - 1
                    break
        if not closes_at_end:
            break
        value = value[1:-1].strip()
    return value


def _split_raw_expr_terms(raw: str) -> list[str]:
    """Split Lean's raw ``Expr`` pretty-print at top-level whitespace."""

    terms: list[str] = []
    index = 0
    matching = {"(": ")", "[": "]", "{": "}"}
    while index < len(raw):
        while index < len(raw) and raw[index].isspace():
            index += 1
        if index == len(raw):
            break
        start = index
        opening = raw[index]
        if opening in matching:
            stack = [matching[opening]]
            index += 1
            while index < len(raw) and stack:
                char = raw[index]
                if char in matching:
                    stack.append(matching[char])
                elif char == stack[-1]:
                    stack.pop()
                index += 1
            if stack:
                raise ValueError("unbalanced raw Lean Expr term")
            terms.append(raw[start:index])
            continue
        while index < len(raw) and not raw[index].isspace():
            index += 1
        terms.append(raw[start:index])
    return terms


def _expr_constructor_args(raw: str, constructor: str) -> list[str] | None:
    value = _strip_balanced_outer_parens(raw.replace("\\n", "\n"))
    prefix = f"Lean.Expr.{constructor}"
    if value == prefix:
        return []
    if not (
        value.startswith(prefix)
        and len(value) > len(prefix)
        and value[len(prefix)].isspace()
    ):
        return None
    return _split_raw_expr_terms(value[len(prefix) :])


def _inline_terminal_shape(row: InlineBinder) -> tuple[int, str]:
    """Return root-forall depth and terminal head of a reviewed binder type."""

    depth = 0
    expression = row.type_raw
    while True:
        arguments = _expr_constructor_args(expression, "forallE")
        if arguments is None:
            break
        if len(arguments) != 4:
            raise ValueError(
                f"{row.declaration}[{row.binder_index}]: malformed forallE "
                f"with {len(arguments)} arguments"
            )
        depth += 1
        expression = arguments[2]

    while True:
        arguments = _expr_constructor_args(expression, "app")
        if arguments is None:
            break
        if len(arguments) != 2:
            raise ValueError(
                f"{row.declaration}[{row.binder_index}]: malformed app "
                f"with {len(arguments)} arguments"
            )
        expression = arguments[0]

    constant = _expr_constructor_args(expression, "const")
    if constant is not None and constant:
        return depth, constant[0].removeprefix("`")
    if _expr_constructor_args(expression, "fvar") is not None:
        return depth, "[fvar]"
    return depth, "[unparsed]"


def _inline_review_group(row: InlineBinder) -> tuple[str, int, str]:
    depth, head = _inline_terminal_shape(row)
    if depth == 0:
        return "NESTED_PI_OR_NONFORALL", depth, head
    if head in INLINE_RELATION_LOGIC_HEADS:
        return "RELATION_LOGIC", depth, head
    if head in INLINE_ANALYTIC_HEADS:
        return "ANALYTIC_REGULARITY", depth, head
    if head in INLINE_PROBABILITY_HEADS:
        return "PROBABILITY_LAW", depth, head
    if head in INLINE_MATRIX_HEADS:
        return "MATRIX_STRUCTURE", depth, head
    if head in INLINE_SET_GEOMETRIC_HEADS:
        return "SET_GEOMETRIC", depth, head
    if head == "[fvar]":
        return "LOCAL_PREDICATE", depth, head
    return "REVIEW-REQUIRED", depth, head


def _candidate_roles(
    candidate: Candidate,
    references: Sequence[Reference],
) -> tuple[list[Reference], list[Reference]]:
    consumer_rows = [
        row
        for row in references
        if row.candidate == candidate.name
        and row.relation in CONSUMER_RELATIONS
    ]
    producer_rows = [
        row
        for row in references
        if row.candidate == candidate.name
        and row.relation in PRODUCER_RELATIONS
        and row.source != candidate.name
        and row.source_kind in PRODUCER_KINDS
    ]
    return consumer_rows, producer_rows


def _classify_primary_candidates(
    primary: Sequence[Candidate],
    fields: Sequence[Candidate],
    references: Sequence[Reference],
) -> tuple[
    dict[str, str],
    dict[str, list[Reference]],
    dict[str, list[Reference]],
    dict[str, list[Reference]],
    dict[str, set[str]],
    set[str],
]:
    """Compute unconditional producers by a least fixed point.

    A declaration concluding ``P`` is usable only after every project
    predicate/interface named in one of its binders has itself become
    proved.  Thus ``P → P`` and cross-predicate cycles cannot manufacture a
    discharge.  Prop-valued field prerequisites are normalized to their
    parent interface, whose construction supplies the field.
    """

    primary_names = {row.name for row in primary}
    field_parent = {
        row.name: row.parent for row in fields if row.parent
    }
    references_by_candidate: dict[str, list[Reference]] = (
        collections.defaultdict(list)
    )
    for row in references:
        references_by_candidate[row.candidate].append(row)

    source_prerequisites: dict[str, set[str]] = collections.defaultdict(set)
    for row in references:
        if row.relation != "binder":
            continue
        prerequisite = (
            row.candidate
            if row.candidate in primary_names
            else field_parent.get(row.candidate, "")
        )
        if prerequisite:
            source_prerequisites[row.source].add(prerequisite)

    consumers_by_name: dict[str, list[Reference]] = {}
    producer_candidates_by_name: dict[str, list[Reference]] = {}
    for candidate in primary:
        consumers, producers = _candidate_roles(
            candidate,
            references_by_candidate[candidate.name],
        )
        consumers_by_name[candidate.name] = consumers
        producer_candidates_by_name[candidate.name] = producers

    proved: set[str] = set()
    changed = True
    while changed:
        changed = False
        for name, producer_rows in producer_candidates_by_name.items():
            if name in proved:
                continue
            if any(
                source_prerequisites[row.source] <= proved
                for row in producer_rows
            ):
                proved.add(name)
                changed = True

    usable_producers: dict[str, list[Reference]] = {}
    blocked_producers: dict[str, list[Reference]] = {}
    statuses: dict[str, str] = {}
    for candidate in primary:
        name = candidate.name
        usable_producers[name] = [
            row
            for row in producer_candidates_by_name[name]
            if source_prerequisites[row.source] <= proved
        ]
        blocked_producers[name] = [
            row
            for row in producer_candidates_by_name[name]
            if not source_prerequisites[row.source] <= proved
        ]
        statuses[name] = (
            "PROVED"
            if name in proved
            else "CONSUMED-ONLY"
            if consumers_by_name[name]
            else "DEAD"
        )
    return (
        statuses,
        consumers_by_name,
        usable_producers,
        blocked_producers,
        source_prerequisites,
        proved,
    )


def _inline_risk(row: InlineBinder) -> tuple[str, str]:
    override = INLINE_OVERRIDES.get((row.declaration, row.binder_name))
    if override:
        return override.adjudication, override.rationale
    if row.named_candidates:
        return "NAMED-CANDIDATE", "handled by predicate/interface census"
    # Generated hygienic names embed the source module after ``._@.``.
    # Principle-name screening applies to the user-facing binder stem, not
    # that namespace (for example a local ``x`` inside GaussianPoincare).
    name = row.binder_name.split("._@.", 1)[0].lower()
    if (
        row.binder_info == "instImplicit"
        and row.head_name
        and not row.head_name.startswith(("HDP.", "MatrixConcentration."))
    ):
        return (
            "ORDINARY-EXTERNAL-TYPECLASS",
            "Prop-valued typeclass premise owned outside the project "
            "candidate population (for example Nonempty, NeZero, or a "
            "Mathlib measure property)",
        )
    signals: list[str] = []
    if any(
        token in name
        for token in (
            "principle",
            "oracle",
            "certificate",
            "bridge",
            "assumption",
            "external",
            "lsi",
            "logsob",
            "sobolev",
            "poincare",
            "isoper",
            "chevet",
            "borell",
            "ricci",
            "diffusion",
            "herbst",
        )
    ):
        signals.append("principle-like binder name")
    if row.binder_info == "instImplicit":
        signals.append("typeclass-mediated proposition")
    if signals:
        return "REVIEW-REQUIRED", "; ".join(signals)
    return (
        "ORDINARY-LOCAL-HYPOTHESIS",
        "first-order local mathematical side condition; no project-owned "
        "principle/interface dependency",
    )


def _inline_exact_review_population(row: InlineBinder) -> bool:
    """Recover the digest-bound current higher-order review population.

    Exact finite-signature and unpublished-helper overrides are outside this
    population.  The hLSI scan hit remains inside it so its exact row stays
    covered by the current key/type digests while receiving a stronger
    discharged disposition.
    """

    override = INLINE_OVERRIDES.get((row.declaration, row.binder_name))
    if override is not None and override.adjudication != (
        "PROVED-DISCHARGED-LOCAL-CERTIFICATE"
    ):
        return False
    if row.named_candidates:
        return False
    if (
        row.binder_info == "instImplicit"
        and row.head_name
        and not row.head_name.startswith(("HDP.", "MatrixConcentration."))
    ):
        return False
    return "Lean.Expr.forallE" in row.type_raw


def calibration_fixture() -> tuple[bool, bool, str]:
    predicates, _ = enumerate_textual_predicates(
        [PLANTED.relative_to(ROOT).as_posix()]
    )
    found_predicate = any(
        row.name == "FakePrinciple" and row.kind == "def"
        for row in predicates
    )
    declarations = extract_declarations(PLANTED)
    found_consumer = any(
        row.name == "fake_result"
        and "FakePrinciple" in row.statement
        for row in declarations
    )
    found_prover = any(
        row.name != "fake_result"
        and re.search(r":\s*FakePrinciple(?:\s|:=|$)", row.statement)
        for row in declarations
    )
    classification = (
        "PROVED"
        if found_prover
        else "CONSUMED-ONLY"
        if found_consumer
        else "DEAD"
    )
    detail = (
        f"textual_predicates={len(predicates)}; "
        f"theorem_declarations={len(declarations)}; "
        f"classification={classification}"
    )
    return found_predicate, found_consumer, detail


def analyze() -> tuple[dict[Path, str], dict[str, object]]:
    universe = enumerate_universe()
    library_paths = list(universe["file_walk_universe"])
    textual, all_commands = enumerate_textual_predicates(library_paths)
    removed_references = removed_source_references(library_paths)
    locations = source_locations(all_commands)
    harness_compiled = _logged_command_passed(HARNESS_BUILD_LOG)
    pass07_witness_compiled = _logged_command_passed(
        PASS07_APPENDIX_WITNESS_LOG
    )

    candidates = read_candidates()
    references = read_references()
    inline_rows = read_inline()
    raw_schema_errors: list[str] = []
    unexpected_categories = sorted(
        {
            row.category
            for row in candidates
            if row.category
            not in {"predicate", "interface", "structure_field"}
        }
    )
    if unexpected_categories:
        raw_schema_errors.append(
            "unexpected V10 candidate categories: "
            + ", ".join(unexpected_categories)
        )
    unexpected_relations = sorted(
        {
            row.relation
            for row in references
            if row.relation
            not in CONSUMER_RELATIONS | PRODUCER_RELATIONS
        }
    )
    if unexpected_relations:
        raw_schema_errors.append(
            "unexpected V10 reference relations: "
            + ", ".join(unexpected_relations)
        )
    primary = [
        row
        for row in candidates
        if row.category in {"predicate", "interface"}
    ]
    fields = [row for row in candidates if row.category == "structure_field"]
    declared_field_names = {
        name for row in primary for name in row.prop_fields
    }
    actual_field_names = {row.name for row in fields}
    if declared_field_names != actual_field_names:
        raw_schema_errors.append(
            "interface prop-field declaration set differs from field rows: "
            f"parent-only={len(declared_field_names - actual_field_names)}, "
            f"field-only={len(actual_field_names - declared_field_names)}"
        )
    candidate_names = {row.name for row in candidates}
    reference_targets = {row.candidate for row in references}
    unknown_reference_targets = sorted(reference_targets - candidate_names)

    env_modules = load_modules(ENV_MODULES)
    recert_modules = load_modules(RECERT_MODULES)
    v7_modules = load_modules(V7_MODULES)
    expected = expected_modules(universe)
    module_errors: list[str] = []
    for label, actual in (
        ("V10 harness", env_modules),
        ("fresh V4", recert_modules),
        ("fresh V7", v7_modules),
    ):
        missing = sorted(expected - actual)
        extra = sorted(actual - expected)
        if missing or extra:
            module_errors.append(
                f"{label} module mismatch: missing={missing}, extra={extra}"
            )
    if env_modules != recert_modules:
        module_errors.append(
            "V10 and V4 current environment module sets differ"
        )
    if env_modules != v7_modules:
        module_errors.append(
            "V10 and V7 current environment module sets differ"
        )

    v4_names = load_v4_names()
    v7_constant_names = {
        row["name"] for row in _read_tsv(V7_CONSTANTS)
    }
    declaration_set_errors: list[str] = []
    if v4_names != v7_constant_names:
        declaration_set_errors.append(
            "fresh V4/V7 environment declaration sets differ: "
            f"V4-only={len(v4_names - v7_constant_names)}, "
            f"V7-only={len(v7_constant_names - v4_names)}"
        )
    tier_b, tier_b_errors = validate_tier_b_freshness(v4_names)
    v6_review_statuses = load_v6_review_statuses()
    claims = live_document_claims()

    reference_sources = {row.source for row in references}
    inline_sources = {row.declaration for row in inline_rows}
    removal_reconciliation_rows: list[dict[str, object]] = []
    removal_errors: list[str] = []
    for environment_name in sorted(REMOVED_DECLARATIONS):
        present_surfaces: list[str] = []
        for label, names in (
            ("fresh V4 environment", v4_names),
            ("fresh V7 environment", v7_constant_names),
            ("V6 Tier-B endpoints", tier_b),
            ("V10 candidates", candidate_names),
            ("V10 reference targets", reference_targets),
            ("V10 reference sources", reference_sources),
            ("V10 inline theorem sources", inline_sources),
        ):
            family_members = sorted(
                name
                for name in names
                if name == environment_name
                or name.startswith(environment_name + ".")
            )
            if family_members:
                present_surfaces.append(
                    f"{label}[{';'.join(family_members[:5])}]"
                )
        code_locations = removed_references.get(environment_name, [])
        if code_locations:
            present_surfaces[0:0] = [
                "live source code[" + ";".join(code_locations) + "]"
            ]
        result = "CONFIRMED" if not present_surfaces else "STALE/PRESENT"
        if present_surfaces:
            removal_errors.append(
                f"removed declaration {environment_name} remains on "
                + ", ".join(present_surfaces)
            )
        removal_reconciliation_rows.append(
            {
                "ledger_item": "REMOVED-DECLARATION-ABSENCE",
                "semantic_condition": environment_name,
                "detector_evidence": (
                    "source,V4,V7,V6,V10 candidate/reference/inline surfaces"
                ),
                "classification": "ABSENT" if not present_surfaces else "PRESENT",
                "direction": "exact source-and-environment absence",
                "result": result,
            }
        )
    live_library_paths = set(library_paths)
    for relative in REMOVED_SOURCE_FILES:
        path_exists = (ROOT / relative).exists()
        inventoried = relative in live_library_paths
        result = (
            "CONFIRMED"
            if not path_exists and not inventoried
            else "STALE/PRESENT"
        )
        if result != "CONFIRMED":
            removal_errors.append(
                f"removed source file remains: {relative} "
                f"(exists={path_exists}, inventoried={inventoried})"
            )
        removal_reconciliation_rows.append(
            {
                "ledger_item": "REMOVED-SOURCE-FILE-ABSENCE",
                "semantic_condition": relative,
                "detector_evidence": "filesystem and FILE-WALK universe",
                "classification": (
                    "ABSENT" if result == "CONFIRMED" else "PRESENT"
                ),
                "direction": "exact physical-file absence",
                "result": result,
            }
        )

    source_match_by_env: dict[str, tuple[str, str]] = {}
    for candidate in candidates:
        source_match_by_env[candidate.name] = match_source_location(
            candidate.module,
            candidate.display_name,
            locations,
        )

    textual_matches: dict[tuple[str, str], list[Candidate]] = {}
    for row in textual:
        matches = [
            candidate
            for candidate in primary
            if candidate.category == "predicate"
            and candidate.module == row.module
            and (
                candidate.display_name == row.name
                or candidate.display_name.endswith("." + row.name)
            )
        ]
        textual_matches[(row.path, str(row.line))] = matches

    text_rows: list[dict[str, object]] = []
    text_only: list[SourceCommand] = []
    ambiguous_text: list[SourceCommand] = []
    for row in textual:
        matches = textual_matches[(row.path, str(row.line))]
        if not matches:
            text_only.append(row)
        elif len(matches) > 1:
            ambiguous_text.append(row)
        text_rows.append(
            {
                "path": row.path,
                "line": row.line,
                "module": row.module,
                "kind": row.kind,
                "source_name": row.name,
                "environment_matches": ";".join(
                    match.name for match in matches
                ),
                "match_count": len(matches),
            }
        )

    explicit_env_names = {
        match.name
        for matches in textual_matches.values()
        for match in matches
    }
    env_only = [
        candidate
        for candidate in primary
        if candidate.category == "predicate"
        and candidate.name not in explicit_env_names
    ]

    diff_rows: list[dict[str, object]] = []
    for row in textual:
        matches = textual_matches[(row.path, str(row.line))]
        if not matches:
            diff_rows.append(
                {
                    "side": "TEXT-ONLY",
                    "name": row.name,
                    "module": row.module,
                    "source": f"{row.path}:{row.line}",
                    "explanation": (
                        "explicit textual predicate absent from environment; "
                        "would indicate an orphan or enumeration failure"
                    ),
                }
            )
    for candidate in env_only:
        source, match = source_match_by_env[candidate.name]
        diff_rows.append(
            {
                "side": "ENVIRONMENT-ONLY",
                "name": candidate.name,
                "user_name": candidate.private_user_name,
                "module": candidate.module,
                "source": source,
                "explanation": (
                    "return type inferred/reducible, compiler-generated, "
                    "private-mangled, or not written with literal ': Prop'"
                    f" (source match {match})"
                ),
            }
        )

    census_rows: list[dict[str, object]] = []
    consumer_output: list[dict[str, object]] = []
    review_rows: list[dict[str, object]] = []
    status_counts: collections.Counter[str] = collections.Counter()
    consumed_only: list[str] = []
    dead: list[str] = []
    unreviewed: list[str] = []
    primary_review_keys: list[str] = []
    primary_review_closure_rows: list[dict[str, object]] = []
    reviewed_nested_candidates: list[str] = []
    reviewed_direct_published: set[str] = set()
    reviewed_direct_unpublished: set[str] = set()
    reviewed_primary_info: set[str] = set()
    primary_v6_targets: set[str] = set()
    primary_ordinary_claimed_only: dict[str, tuple[str, ...]] = {}

    references_by_candidate: dict[str, list[Reference]] = collections.defaultdict(list)
    for row in references:
        references_by_candidate[row.candidate].append(row)
    (
        primary_statuses,
        primary_consumers,
        primary_provers,
        primary_blocked_producers,
        source_prerequisites,
        proved_primary,
    ) = _classify_primary_candidates(primary, fields, references)

    for candidate in sorted(primary, key=lambda row: row.name):
        status = primary_statuses[candidate.name]
        consumers = primary_consumers[candidate.name]
        provers = primary_provers[candidate.name]
        blocked_producers = primary_blocked_producers[candidate.name]
        status_counts[status] += 1
        if status == "CONSUMED-ONLY":
            consumed_only.append(candidate.name)
        elif status == "DEAD":
            dead.append(candidate.name)
        published_consumers = sorted(
            {row.source for row in consumers if row.source in tier_b}
        )
        claimed_consumers = sorted(
            {
                row.source
                for row in consumers
                if is_document_claimed(row.source, claims)
            }
        )
        primary_review_key = ""
        if status == "CONSUMED-ONLY":
            primary_review_key = _primary_review_key(
                candidate,
                consumers,
                published_consumers,
                claimed_consumers,
            )
            primary_review_keys.append(primary_review_key)
        source, source_match = source_match_by_env[candidate.name]
        override = REVIEW_OVERRIDES.get(candidate.name)
        directly_assumed = _directly_assumes_candidate(
            candidate.name, consumers
        )
        published_or_claimed = bool(
            published_consumers or claimed_consumers
        )
        if status == "CONSUMED-ONLY" and override is not None:
            adjudication = override.adjudication
            disclosure = override.disclosure
            ledger = override.ledger
            rationale = override.rationale
        elif (
            status == "CONSUMED-ONLY"
            and candidate.name in DISCLOSED_UNPUBLISHED_PRIMARY_INFO
        ):
            reviewed_primary_info.add(candidate.name)
            if directly_assumed:
                reviewed_direct_unpublished.add(candidate.name)
            adjudication = "INFO-DISCLOSED-UNPUBLISHED-INFRASTRUCTURE"
            disclosure = (
                f"{source}; every exact consumer is enumerated in "
                "inventory/v10_consumers.tsv"
            )
            ledger = ""
            rationale = (
                "This is source-disclosed, unpublished certificate-bearing "
                "infrastructure.  No Tier-B theorem consumes it; V10 records "
                "it as an informational conditional rather than a defect."
            )
        elif status == "CONSUMED-ONLY" and not directly_assumed:
            reviewed_nested_candidates.append(candidate.name)
            adjudication = "REVIEWED-NESTED-DATA-PREDICATE"
            disclosure = (
                f"{source}; every current occurrence is enumerated in "
                "inventory/v10_consumers.tsv"
            )
            ledger = ""
            rationale = (
                "Exact raw-kernel review found that this constant never heads "
                "a theorem binder: it occurs only inside another proposition "
                "as a set, event, relation, or other data predicate.  It is "
                "therefore not an assumed project principle."
            )
        elif (
            status == "CONSUMED-ONLY"
            and published_or_claimed
            and candidate.name in REVIEWED_DIRECT_PUBLISHED_ORDINARY
        ):
            reviewed_direct_published.add(candidate.name)
            adjudication = "REVIEWED-ORDINARY-DISCLOSED-HYPOTHESIS"
            disclosure = (
                f"{source}; exact published/claimed binders are enumerated "
                "in inventory/v10_consumers.tsv"
            )
            ledger = ""
            rationale = (
                "Manual current-tree group review classifies this direct "
                "premise as an ordinary constructible mathematical condition "
                "or data-bearing interface, not a universal result that the "
                "consumer purports to prove."
            )
        elif (
            status == "CONSUMED-ONLY"
            and not published_or_claimed
            and candidate.name
            in REVIEWED_DIRECT_UNPUBLISHED_INFRASTRUCTURE
        ):
            reviewed_direct_unpublished.add(candidate.name)
            adjudication = "REVIEWED-ORDINARY-UNPUBLISHED-HYPOTHESIS"
            disclosure = (
                f"{source}; exact unpublished binders are enumerated in "
                "inventory/v10_consumers.tsv"
            )
            ledger = ""
            rationale = (
                "Manual current-tree group review classifies this direct "
                "unpublished premise as an ordinary constructible local "
                "condition rather than an unproved universal principle."
            )
        elif status == "CONSUMED-ONLY":
            unreviewed.append(candidate.name)
            adjudication = "UNREVIEWED"
            disclosure = ""
            ledger = ""
            rationale = (
                "fail-closed: direct consumed-only candidate is absent from "
                "the exact reviewed allowlists"
            )
        elif status == "PROVED":
            adjudication = "PROVED"
            disclosure = ""
            ledger = ""
            rationale = (
                "least-fixed-point analysis found a declaration whose exact "
                "conclusion supplies this predicate/interface and whose "
                "project-candidate binder prerequisites are discharged"
            )
        else:
            adjudication = "DEAD-CROSSFILE-V7"
            disclosure = ""
            ledger = ""
            rationale = (
                "neither exact proof/witness nor binder consumer; cross-file "
                "candidate for V7 dead-code review"
            )
        if status == "CONSUMED-ONLY" and override is None:
            primary_v6_targets.update(published_consumers)
            if (
                claimed_consumers
                and not published_consumers
                and adjudication
                not in {"INFO-DISCLOSED-UNPUBLISHED-INFRASTRUCTURE"}
            ):
                primary_ordinary_claimed_only[candidate.name] = tuple(
                    claimed_consumers
                )
        if status == "CONSUMED-ONLY":
            consumer_key_digest = _sha256_text(
                ";".join(
                    sorted(_reference_review_key(row) for row in consumers)
                )
            )
            primary_review_closure_rows.append(
                {
                    "candidate": candidate.name,
                    "module": candidate.module,
                    "category": candidate.category,
                    "source_kind": candidate.source_kind,
                    "dependency_shape": (
                        "direct" if directly_assumed else "nested-only"
                    ),
                    "consumer_reference_count": len(consumers),
                    "consumer_key_digest": consumer_key_digest,
                    "published_consumers": ";".join(published_consumers),
                    "claimed_consumers": ";".join(claimed_consumers),
                    "review_key_sha256": _sha256_text(primary_review_key),
                    "adjudication": adjudication,
                    "review_result": (
                        "CLOSED" if adjudication != "UNREVIEWED" else "OPEN"
                    ),
                    "rationale": rationale,
                }
            )
        census_rows.append(
            {
                "name": candidate.name,
                "module": candidate.module,
                "category": candidate.category,
                "source_kind": candidate.source_kind,
                "parent": "",
                "prop_fields": ";".join(candidate.prop_fields),
                "source_location": source,
                "source_match": source_match,
                "status": status,
                "provers": ";".join(sorted({row.source for row in provers})),
                "blocked_producers": ";".join(
                    sorted({row.source for row in blocked_producers})
                ),
                "blocked_producer_prerequisites": ";".join(
                    sorted(
                        f"{row.source}["
                        + ",".join(sorted(source_prerequisites[row.source]))
                        + "]"
                        for row in blocked_producers
                    )
                ),
                "consumer_count": len({row.source for row in consumers}),
                "published_consumers": ";".join(published_consumers),
                "claimed_consumers": ";".join(claimed_consumers),
                "adjudication": adjudication,
            }
        )
        review_rows.append(
            {
                "name": candidate.name,
                "parent": "",
                "status": status,
                "published": "yes" if published_consumers or claimed_consumers else "no",
                "published_consumers": ";".join(published_consumers),
                "claimed_consumers": ";".join(claimed_consumers),
                "adjudication": adjudication,
                "in_source_disclosure": disclosure,
                "ledger_reference": ledger,
                "rationale": rationale,
            }
        )
        for row in sorted(
            consumers,
            key=lambda item: (
                item.source,
                int(item.binder_index or 0),
            ),
        ):
            consumer_output.append(
                {
                    "candidate": candidate.name,
                    "candidate_status": status,
                    "consumer": row.source,
                    "consumer_user_name": row.source_private_user_name,
                    "consumer_module": row.source_module,
                    "consumer_kind": row.source_kind,
                    "relation": row.relation,
                    "binder_index": row.binder_index,
                    "binder_name": row.binder_name,
                    "binder_info": row.binder_info,
                    "tier_b_published": "yes" if row.source in tier_b else "no",
                    "document_claimed": (
                        "yes"
                        if is_document_claimed(row.source, claims)
                        else "no"
                    ),
                    "adjudication": adjudication,
                }
            )

    primary_review_digest = _line_population_digest(primary_review_keys)
    primary_review_errors = _review_population_errors(
        "primary consumed-only review population",
        len(primary_review_keys),
        EXPECTED_PRIMARY_REVIEW_COUNT,
        {"key/type": primary_review_digest},
        {"key/type": EXPECTED_PRIMARY_REVIEW_DIGEST},
    )
    if reviewed_direct_published != REVIEWED_DIRECT_PUBLISHED_ORDINARY:
        primary_review_errors.append(
            "published ordinary direct-premise allowlist mismatch: "
            f"missing={sorted(REVIEWED_DIRECT_PUBLISHED_ORDINARY - reviewed_direct_published)}, "
            f"extra={sorted(reviewed_direct_published - REVIEWED_DIRECT_PUBLISHED_ORDINARY)}"
        )
    if (
        reviewed_direct_unpublished
        != REVIEWED_DIRECT_UNPUBLISHED_INFRASTRUCTURE
    ):
        primary_review_errors.append(
            "unpublished infrastructure direct-premise allowlist mismatch: "
            f"missing={sorted(REVIEWED_DIRECT_UNPUBLISHED_INFRASTRUCTURE - reviewed_direct_unpublished)}, "
            f"extra={sorted(reviewed_direct_unpublished - REVIEWED_DIRECT_UNPUBLISHED_INFRASTRUCTURE)}"
        )
    if reviewed_primary_info != DISCLOSED_UNPUBLISHED_PRIMARY_INFO:
        primary_review_errors.append(
            "disclosed unpublished primary INFO allowlist mismatch: "
            f"missing={sorted(DISCLOSED_UNPUBLISHED_PRIMARY_INFO - reviewed_primary_info)}, "
            f"extra={sorted(reviewed_primary_info - DISCLOSED_UNPUBLISHED_PRIMARY_INFO)}"
        )
    if (
        primary_ordinary_claimed_only
        != EXPECTED_PRIMARY_ORDINARY_CLAIMED_ONLY
    ):
        primary_review_errors.append(
            "ordinary primary claimed-only manual-review mapping drift: "
            f"expected={EXPECTED_PRIMARY_ORDINARY_CLAIMED_ONLY}, "
            f"found={primary_ordinary_claimed_only}"
        )

    field_rows: list[dict[str, object]] = []
    field_status_counts: collections.Counter[str] = collections.Counter()
    field_parent_errors: list[str] = []
    status_by_name = {row["name"]: row["status"] for row in census_rows}
    adjudication_by_name = {
        row["name"]: row["adjudication"] for row in census_rows
    }
    primary_review_by_name = {
        row["name"]: row for row in review_rows
    }
    for field in sorted(fields, key=lambda row: row.name):
        source, source_match = source_match_by_env[field.name]
        if not source and field.parent:
            source, source_match = source_match_by_env[field.parent]
            source_match = f"PARENT-{source_match}"
        consumers, producer_candidates = _candidate_roles(
            field,
            references_by_candidate[field.name],
        )
        provers = [
            row
            for row in producer_candidates
            if source_prerequisites[row.source] <= proved_primary
        ]
        blocked_producers = [
            row
            for row in producer_candidates
            if not source_prerequisites[row.source] <= proved_primary
        ]
        direct_published_consumers = {
            row.source for row in consumers if row.source in tier_b
        }
        direct_claimed_consumers = {
            row.source
            for row in consumers
            if is_document_claimed(row.source, claims)
        }
        parent_review = primary_review_by_name.get(field.parent, {})
        parent_published_consumers = set(
            filter(
                None,
                str(parent_review.get("published_consumers", "")).split(";"),
            )
        )
        parent_claimed_consumers = set(
            filter(
                None,
                str(parent_review.get("claimed_consumers", "")).split(";"),
            )
        )
        published_consumers = sorted(
            direct_published_consumers | parent_published_consumers
        )
        claimed_consumers = sorted(
            direct_claimed_consumers | parent_claimed_consumers
        )
        inherited_status = status_by_name.get(field.parent, "UNKNOWN")
        inherited_adjudication = adjudication_by_name.get(
            field.parent,
            "UNKNOWN",
        )
        if inherited_status == "UNKNOWN":
            field_parent_errors.append(
                f"Prop-valued field {field.name} has unknown parent "
                f"{field.parent}"
            )
        else:
            field_status_counts[inherited_status] += 1
        field_rows.append(
            {
                "name": field.name,
                "user_name": field.private_user_name,
                "module": field.module,
                "category": field.category,
                "source_kind": field.source_kind,
                "parent": field.parent,
                "prop_fields": "",
                "source_location": source,
                "source_match": source_match,
                "status": inherited_status,
                "provers": ";".join(sorted({row.source for row in provers})),
                "blocked_producers": ";".join(
                    sorted({row.source for row in blocked_producers})
                ),
                "blocked_producer_prerequisites": ";".join(
                    sorted(
                        f"{row.source}["
                        + ",".join(sorted(source_prerequisites[row.source]))
                        + "]"
                        for row in blocked_producers
                    )
                ),
                "consumer_count": len({row.source for row in consumers}),
                "published_consumers": ";".join(published_consumers),
                "claimed_consumers": ";".join(claimed_consumers),
                "adjudication": inherited_adjudication,
            }
        )
        review_rows.append(
            {
                "name": field.name,
                "parent": field.parent,
                "status": inherited_status,
                "published": (
                    "yes"
                    if published_consumers or claimed_consumers
                    else "no"
                ),
                "published_consumers": ";".join(published_consumers),
                "claimed_consumers": ";".join(claimed_consumers),
                "adjudication": inherited_adjudication,
                "in_source_disclosure": parent_review.get(
                    "in_source_disclosure",
                    "",
                ),
                "ledger_reference": parent_review.get(
                    "ledger_reference",
                    "",
                ),
                "rationale": (
                    "Prop-valued projection inherits construction and "
                    f"discharge from parent interface {field.parent}. "
                    + str(parent_review.get("rationale", ""))
                ).strip(),
            }
        )
        for row in sorted(
            consumers,
            key=lambda item: (
                item.source,
                int(item.binder_index or 0),
            ),
        ):
            consumer_output.append(
                {
                    "candidate": field.name,
                    "candidate_status": inherited_status,
                    "consumer": row.source,
                    "consumer_user_name": row.source_private_user_name,
                    "consumer_module": row.source_module,
                    "consumer_kind": row.source_kind,
                    "relation": row.relation,
                    "binder_index": row.binder_index,
                    "binder_name": row.binder_name,
                    "binder_info": row.binder_info,
                    "tier_b_published": (
                        "yes" if row.source in tier_b else "no"
                    ),
                    "document_claimed": (
                        "yes"
                        if is_document_claimed(row.source, claims)
                        else "no"
                    ),
                    "adjudication": inherited_adjudication,
                }
            )

    v7_reverse_sources: dict[str, set[str]] = collections.defaultdict(set)
    for row in _read_tsv(V7_EDGES):
        if row["source"] != row["target"]:
            v7_reverse_sources[row["target"]].add(row["source"])
    v7_dead_by_name = {
        row["name"]: row for row in _read_tsv(V7_DEAD_SWEEP)
    }
    v7_dead_rows: list[dict[str, object]] = []
    v7_dead_errors: list[str] = []
    for name in sorted(dead):
        in_constants = name in v7_constant_names
        reverse_count = len(v7_reverse_sources[name])
        v7_row = v7_dead_by_name.get(name)
        v7_classification = (
            v7_row["classification"] if v7_row is not None else ""
        )
        if not in_constants:
            result = "ERROR-MISSING-FROM-FRESH-V7"
            v7_dead_errors.append(
                f"V10 DEAD candidate absent from fresh V7 constants: {name}"
            )
        elif v7_classification == "DEAD_CODE_CANDIDATE":
            result = "CONFIRMED-V7-DEAD-CODE-CANDIDATE"
        elif v7_classification == "EXCLUDED":
            result = "V7-EXCLUDED-BY-ITS-DOCUMENTED-RULES"
        elif reverse_count > 0:
            result = "V10-INTERFACE-DEAD-BUT-V7-IMPLEMENTATION-LIVE"
        else:
            result = "ERROR-ZERO-V7-REFERENCES-NOT-IN-SWEEP"
            v7_dead_errors.append(
                "V10 DEAD candidate has zero fresh V7 reverse citations but "
                f"no V7 sweep disposition: {name}"
            )
        v7_dead_rows.append(
            {
                "name": name,
                "v10_status": "DEAD",
                "v7_constant_present": "yes" if in_constants else "no",
                "v7_reverse_citation_count": reverse_count,
                "v7_dead_sweep_classification": v7_classification,
                "v7_exclusion_reason": (
                    v7_row["exclusion_reason"] if v7_row is not None else ""
                ),
                "reconciliation": result,
            }
        )

    inline_output: list[dict[str, object]] = []
    inline_review_closure_rows: list[dict[str, object]] = []
    inline_risk_counts: collections.Counter[str] = collections.Counter()
    inline_review_group_counts: collections.Counter[str] = (
        collections.Counter()
    )
    inline_review_group_claimed_counts: collections.Counter[str] = (
        collections.Counter()
    )
    inline_unreviewed: list[str] = []
    inline_review_key_lines: list[str] = []
    inline_review_type_lines: list[str] = []
    inline_v6_targets: set[str] = set()
    inline_claimed_only_declarations: set[str] = set()
    for row in sorted(
        inline_rows,
        key=lambda item: (item.declaration, item.binder_index),
    ):
        published = row.declaration in tier_b
        claimed = is_document_claimed(row.declaration, claims)
        adjudication, rationale = _inline_risk(row)
        override = INLINE_OVERRIDES.get((row.declaration, row.binder_name))
        in_exact_review = _inline_exact_review_population(row)
        review_group = ""
        outer_forall_depth = 0
        terminal_head = ""
        if in_exact_review:
            inline_review_key_lines.append(
                _inline_review_key(row, include_type=False)
            )
            inline_review_type_lines.append(
                _inline_review_key(row, include_type=True)
            )
            try:
                (
                    review_group,
                    outer_forall_depth,
                    terminal_head,
                ) = _inline_review_group(row)
            except ValueError as error:
                review_group = "REVIEW-REQUIRED"
                rationale = str(error)
                adjudication = "REVIEW-REQUIRED"
            if review_group == "REVIEW-REQUIRED":
                adjudication = "REVIEW-REQUIRED"
                rationale = (
                    "fail-closed: exact higher-order review row has an "
                    f"unrecognized outer terminal head {terminal_head}"
                )
            elif override is None and adjudication == (
                "ORDINARY-LOCAL-HYPOTHESIS"
            ):
                adjudication = (
                    "REVIEWED-ORDINARY-INLINE-" + review_group
                )
                rationale = (
                    "Exact row-level mixed-tier review, bound to both key "
                    "and raw-type digests, classifies this binder in the "
                    f"{review_group} ordinary-hypothesis cluster."
                )
            inline_review_group_counts[review_group] += 1
            if published or claimed:
                inline_review_group_claimed_counts[review_group] += 1
            if published:
                inline_v6_targets.add(row.declaration)
            elif claimed:
                inline_claimed_only_declarations.add(row.declaration)
            inline_review_closure_rows.append(
                {
                    "module": row.module,
                    "declaration": row.declaration,
                    "private_user_name": row.private_user_name,
                    "binder_index": row.binder_index,
                    "binder_name": row.binder_name,
                    "binder_info": row.binder_info,
                    "head_name": row.head_name,
                    "named_candidates": ";".join(row.named_candidates),
                    "type_sha256": _sha256_text(row.type_raw),
                    "review_key_sha256": _sha256_text(
                        _inline_review_key(row, include_type=False)
                    ),
                    "outer_forall_depth": outer_forall_depth,
                    "terminal_head": terminal_head,
                    "review_group": review_group,
                    "tier_b_published": "yes" if published else "no",
                    "document_claimed": "yes" if claimed else "no",
                    "adjudication": adjudication,
                    "review_result": (
                        "OPEN"
                        if adjudication == "REVIEW-REQUIRED"
                        else "CLOSED"
                    ),
                    "rationale": rationale,
                }
            )
        if not (
            published
            or claimed
            or override is not None
            or in_exact_review
            or adjudication == "REVIEW-REQUIRED"
        ):
            continue
        inline_risk_counts[adjudication] += 1
        if adjudication == "REVIEW-REQUIRED":
            inline_unreviewed.append(
                f"{row.declaration}[{row.binder_index}:{row.binder_name}]"
            )
        inline_output.append(
            {
                "declaration": row.declaration,
                "declaration_user_name": row.private_user_name,
                "module": row.module,
                "binder_index": row.binder_index,
                "binder_name": row.binder_name,
                "binder_info": row.binder_info,
                "head_name": row.head_name,
                "named_candidates": ";".join(row.named_candidates),
                "higher_order": (
                    "yes"
                    if "Lean.Expr.forallE" in row.type_raw
                    else "no"
                ),
                "tier_b_published": "yes" if published else "no",
                "document_claimed": "yes" if claimed else "no",
                "adjudication": adjudication,
                "disclosure": override.disclosure if override else "",
                "ledger_reference": override.ledger if override else "",
                "rationale": rationale,
            }
        )

    inline_review_key_digest = _ordered_line_population_digest(
        inline_review_key_lines
    )
    inline_review_type_digest = _ordered_line_population_digest(
        inline_review_type_lines
    )
    inline_review_errors = _review_population_errors(
        "inline exact review population",
        len(inline_review_key_lines),
        EXPECTED_INLINE_HIGHER_ORDER_COUNT,
        {
            "key": inline_review_key_digest,
            "raw-type": inline_review_type_digest,
        },
        {
            "key": EXPECTED_INLINE_HIGHER_ORDER_KEY_DIGEST,
            "raw-type": EXPECTED_INLINE_HIGHER_ORDER_TYPE_DIGEST,
        },
    )
    observed_group_counts = {
        group: (
            inline_review_group_counts[group],
            inline_review_group_claimed_counts[group],
        )
        for group in EXPECTED_INLINE_REVIEW_GROUP_COUNTS
    }
    if observed_group_counts != EXPECTED_INLINE_REVIEW_GROUP_COUNTS:
        inline_review_errors.append(
            "inline structural review-cluster count drift: expected "
            f"{EXPECTED_INLINE_REVIEW_GROUP_COUNTS}, "
            f"found {observed_group_counts}"
        )
    unexpected_inline_groups = sorted(
        set(inline_review_group_counts)
        - set(EXPECTED_INLINE_REVIEW_GROUP_COUNTS)
    )
    if unexpected_inline_groups:
        inline_review_errors.append(
            "inline structural review produced unrecognized groups: "
            + ", ".join(unexpected_inline_groups)
        )
    inline_claimed_only_digest = _line_population_digest(
        inline_claimed_only_declarations
    )
    inline_review_errors.extend(
        _review_population_errors(
            "inline document-claimed-only declaration review",
            len(inline_claimed_only_declarations),
            EXPECTED_INLINE_CLAIMED_ONLY_DECL_COUNT,
            {"name": inline_claimed_only_digest},
            {"name": EXPECTED_INLINE_CLAIMED_ONLY_DECL_DIGEST},
        )
    )

    v6_reconciliation_rows: list[dict[str, object]] = []
    v6_reconciliation_errors: list[str] = []
    v6_reconciliation_errors.extend(
        _review_population_errors(
            "primary ordinary Tier-B consumer join",
            len(primary_v6_targets),
            EXPECTED_PRIMARY_V6_TARGET_COUNT,
            {"name": _line_population_digest(primary_v6_targets)},
            {"name": EXPECTED_PRIMARY_V6_TARGET_DIGEST},
        )
    )
    v6_reconciliation_errors.extend(
        _review_population_errors(
            "inline ordinary Tier-B declaration join",
            len(inline_v6_targets),
            EXPECTED_INLINE_V6_TARGET_COUNT,
            {"name": _line_population_digest(inline_v6_targets)},
            {"name": EXPECTED_INLINE_V6_TARGET_DIGEST},
        )
    )
    for review_scope, declarations in (
        ("PRIMARY-ORDINARY-TIER-B", primary_v6_targets),
        ("INLINE-ORDINARY-TIER-B", inline_v6_targets),
    ):
        for declaration in sorted(declarations):
            statuses = v6_review_statuses.get(declaration, set())
            result = "CONFIRMED" if statuses == {"OK"} else "ERROR"
            if result != "CONFIRMED":
                v6_reconciliation_errors.append(
                    f"{review_scope} declaration {declaration} has V6 "
                    f"statuses {sorted(statuses)}, expected ['OK']"
                )
            v6_reconciliation_rows.append(
                {
                    "review_scope": review_scope,
                    "declaration": declaration,
                    "candidate": "",
                    "review_authority": "V6-EXACT-DECLARATION",
                    "expected_status": "OK",
                    "observed_status": ";".join(sorted(statuses))
                    or "MISSING",
                    "result": result,
                }
            )

    for candidate, declarations in sorted(
        primary_ordinary_claimed_only.items()
    ):
        for declaration in declarations:
            v6_reconciliation_rows.append(
                {
                    "review_scope": "PRIMARY-DOCUMENT-CLAIMED-ONLY",
                    "declaration": declaration,
                    "candidate": candidate,
                    "review_authority": (
                        "V10-EXACT-MANUAL-ORDINARY-REVIEW"
                    ),
                    "expected_status": "NOT-IN-TIER-B",
                    "observed_status": "NOT-IN-TIER-B",
                    "result": "CONFIRMED",
                }
            )
    for declaration in sorted(inline_claimed_only_declarations):
        v6_reconciliation_rows.append(
            {
                "review_scope": "INLINE-DOCUMENT-CLAIMED-ONLY",
                "declaration": declaration,
                "candidate": "",
                "review_authority": (
                    "V10-EXACT-MANUAL-ORDINARY-REVIEW"
                ),
                "expected_status": "NOT-IN-TIER-B",
                "observed_status": "NOT-IN-TIER-B",
                "result": "CONFIRMED",
            }
        )

    planted_predicate, planted_consumer, planted_detail = calibration_fixture()
    planted_compiled = _logged_command_passed(PLANTED_BUILD_LOG)
    finite_chevet_errors: list[str] = []
    finite_chevet_reconciled: dict[str, bool] = {}
    for declaration, source_name in sorted(
        FINITE_CHEVET_ZERO_DECLARATIONS.items()
    ):
        source_commands = [
            row
            for row in all_commands
            if row.module
            == "HighDimensionalProbability.Chapter8_Chaining"
            and row.name == source_name
        ]
        source_visible = (
            len(source_commands) == 1
            and re.search(
                r"\bhzero\s*:.*?0\s*:.*?∈\s*T\b",
                source_commands[0].statement,
            )
            is not None
        )
        binders = [
            row
            for row in inline_rows
            if row.declaration == declaration
            and row.binder_name == "hzero"
        ]
        environment_visible = (
            len(binders) == 1
            and binders[0].binder_info == "explicit"
            and binders[0].head_name == "Membership.mem"
            and declaration in v4_names
        )
        override_visible = any(
            row["declaration"] == declaration
            and row["binder_name"] == "hzero"
            and row["adjudication"]
            == "RETAINED-FINITE-ZERO-MEMBERSHIP"
            for row in inline_output
        )
        reconciled = (
            source_visible and environment_visible and override_visible
        )
        finite_chevet_reconciled[declaration] = reconciled
        if not reconciled:
            finite_chevet_errors.append(
                f"retained finite Chevet signature {declaration} lacks an "
                "exact visible explicit hzero : 0 ∈ T source/environment "
                "binder and review override "
                f"(source={source_visible}, environment={environment_visible}, "
                f"override={override_visible})"
            )
        removal_reconciliation_rows.append(
            {
                "ledger_item": "RETAINED-FINITE-CHEVET-HZERO",
                "semantic_condition": declaration + "[hzero]",
                "detector_evidence": (
                    "source signature, fresh theorem binder, V10 override"
                ),
                "classification": (
                    "RETAINED-FINITE-ZERO-MEMBERSHIP"
                    if reconciled
                    else "MISSING"
                ),
                "direction": "source-to-environment signature visibility",
                "result": "CONFIRMED" if reconciled else "STALE/MISSING",
            }
        )

    review_by_name = {str(row["name"]): row for row in review_rows}
    riemannian_review = review_by_name.get(
        REVIEWED_RIEMANNIAN_INFRASTRUCTURE,
        {},
    )
    riemannian_consumers = {
        row.source
        for row in primary_consumers.get(
            REVIEWED_RIEMANNIAN_INFRASTRUCTURE,
            [],
        )
        if row.relation == "binder"
    }
    riemannian_reconciled = bool(
        riemannian_review.get("status") == "CONSUMED-ONLY"
        and riemannian_review.get("adjudication")
        == "REVIEWED-ORDINARY-UNPUBLISHED-HYPOTHESIS"
        and riemannian_review.get("published") == "no"
        and riemannian_consumers
        == EXPECTED_RIEMANNIAN_UNPUBLISHED_CONSUMERS
    )
    removed_absence_passed = not removal_errors
    finite_chevet_passed = all(finite_chevet_reconciled.values())
    calibration_rows = [
        {
            "calibration": "removed_interface_absence",
            "expected": (
                f"{len(REMOVED_DECLARATIONS)} declarations and "
                f"{len(REMOVED_SOURCE_FILES)} source files absent"
            ),
            "observed": (
                f"declaration/source errors={len(removal_errors)}"
            ),
            "pass": "yes" if removed_absence_passed else "no",
        },
        {
            "calibration": "retained_finite_chevet_hzero",
            "expected": (
                "both retained finite Chevet theorem signatures expose an "
                "explicit hzero : 0 ∈ T"
            ),
            "observed": "; ".join(
                f"{name}={'visible' if passed else 'missing'}"
                for name, passed in sorted(
                    finite_chevet_reconciled.items()
                )
            ),
            "pass": "yes" if finite_chevet_passed else "no",
        },
        {
            "calibration": "riemannian_unpublished_infrastructure",
            "expected": (
                f"{REVIEWED_RIEMANNIAN_INFRASTRUCTURE} classified as "
                "reviewed direct unpublished infrastructure"
            ),
            "observed": (
                f"status={riemannian_review.get('status', 'MISSING')}; "
                "adjudication="
                f"{riemannian_review.get('adjudication', 'MISSING')}; "
                f"published={riemannian_review.get('published', 'MISSING')}; "
                f"consumers={';'.join(sorted(riemannian_consumers))}"
            ),
            "pass": "yes" if riemannian_reconciled else "no",
        },
        {
            "calibration": "planted_fake_predicate",
            "expected": "V10Calibration.FakePrinciple found textually",
            "observed": planted_detail,
            "pass": "yes" if planted_predicate else "no",
        },
        {
            "calibration": "planted_fake_consumer",
            "expected": "V10Calibration.fake_result consumes FakePrinciple",
            "observed": planted_detail,
            "pass": "yes" if planted_consumer else "no",
        },
        {
            "calibration": "planted_pair_compiles",
            "expected": (
                "lake env lean accepts the planted conditional theorem with "
                "the library-adjacent option set"
            ),
            "observed": (
                f"{PLANTED_BUILD_LOG.relative_to(ROOT)} exit_status="
                + ("0" if planted_compiled else "missing/nonzero")
            ),
            "pass": "yes" if planted_compiled else "no",
        },
        {
            "calibration": "pass07_current_appendix_witness_compiles",
            "expected": (
                f"{EXPECTED_PASS07_CURRENT_AXIOM_REPLAYS} retained axiom "
                "replays compile against the current Appendix"
            ),
            "observed": (
                f"{PASS07_APPENDIX_WITNESS_LOG.relative_to(ROOT)} "
                "exit_status="
                + ("0" if pass07_witness_compiled else "missing/nonzero")
            ),
            "pass": "yes" if pass07_witness_compiled else "no",
        },
    ]

    so_helper_reconciled = any(
        row["declaration"] == KNOWN_SO_HELPER
        and row["binder_name"] == "hDiffusion"
        and row["adjudication"]
        == "INFO-DISCLOSED-UNPUBLISHED-HELPER"
        for row in inline_output
    )
    reconciliation_rows = removal_reconciliation_rows

    hard_errors = [
        *raw_schema_errors,
        *module_errors,
        *declaration_set_errors,
        *tier_b_errors,
        *v7_dead_errors,
        *field_parent_errors,
        *primary_review_errors,
        *inline_review_errors,
        *v6_reconciliation_errors,
        *removal_errors,
        *finite_chevet_errors,
    ]
    if not harness_compiled:
        hard_errors.append(
            "V10 environment harness lacks a recorded exit_status: 0"
        )
    if not pass07_witness_compiled:
        hard_errors.append(
            "current 15-row Pass07 Appendix witness lacks a recorded "
            "exit_status: 0"
        )
    if unknown_reference_targets:
        hard_errors.append(
            "environment references unknown candidates: "
            + ", ".join(unknown_reference_targets[:20])
        )
    candidate_names_missing_v4 = sorted(candidate_names - v4_names)
    if candidate_names_missing_v4:
        hard_errors.append(
            "V10 candidates absent from fresh V4 declarations: "
            + ", ".join(candidate_names_missing_v4[:20])
        )
    reference_sources_missing_v4 = sorted(
        {row.source for row in references} - v4_names
    )
    if reference_sources_missing_v4:
        hard_errors.append(
            "V10 reference sources absent from fresh V4 declarations: "
            + ", ".join(reference_sources_missing_v4[:20])
        )
    inline_sources_missing_v4 = sorted(
        {row.declaration for row in inline_rows} - v4_names
    )
    if inline_sources_missing_v4:
        hard_errors.append(
            "V10 inline theorem sources absent from fresh V4 declarations: "
            + ", ".join(inline_sources_missing_v4[:20])
        )
    if text_only:
        hard_errors.append(
            f"{len(text_only)} textual Prop definitions absent from environment"
        )
    if ambiguous_text:
        hard_errors.append(
            f"{len(ambiguous_text)} textual Prop definitions have ambiguous "
            "environment matches"
        )
    if unreviewed:
        hard_errors.append(
            f"{len(unreviewed)} consumed-only candidates lack review: "
            + ", ".join(unreviewed[:50])
            + (" ..." if len(unreviewed) > 50 else "")
        )
    if inline_unreviewed:
        hard_errors.append(
            f"{len(inline_unreviewed)} principle-like inline hypotheses lack "
            "review: "
            + ", ".join(inline_unreviewed[:50])
            + (" ..." if len(inline_unreviewed) > 50 else "")
        )
    if not riemannian_reconciled:
        hard_errors.append(
            "RiemannianDiffusionLaw was not recovered as reviewed direct "
            "unpublished infrastructure"
        )
    if not planted_predicate or not planted_consumer or not planted_compiled:
        hard_errors.append("planted FakePrinciple calibration failed")
    stale_reconciliation = [
        row["ledger_item"]
        for row in reconciliation_rows
        if row["result"] != "CONFIRMED"
    ]
    if not so_helper_reconciled:
        hard_errors.append(
            "disclosed unpublished special-orthogonal diffusion helper was "
            "not recovered by the inline-hypothesis detector"
        )

    critical_items = sorted(
        {
            str(row["name"])
            for row in review_rows
            if not row["parent"]
            and str(row["adjudication"]).startswith("CRITICAL")
        }
        | {
            (
                f"{row['declaration']}"
                f"[{row['binder_index']}:{row['binder_name']}]"
            )
            for row in inline_output
            if str(row["adjudication"]).startswith("CRITICAL")
        }
    )
    major_items = sorted(
        {
            str(row["name"])
            for row in review_rows
            if not row["parent"]
            and str(row["adjudication"]).startswith("MAJOR")
        }
        | {
            (
                f"{row['declaration']}"
                f"[{row['binder_index']}:{row['binder_name']}]"
            )
            for row in inline_output
            if str(row["adjudication"]).startswith("MAJOR")
        }
    )
    minor_items = sorted(
        {
            str(row["name"])
            for row in review_rows
            if not row["parent"]
            and str(row["adjudication"]).startswith("MINOR")
        }
        | {
            (
                f"{row['declaration']}"
                f"[{row['binder_index']}:{row['binder_name']}]"
            )
            for row in inline_output
            if str(row["adjudication"]).startswith("MINOR")
        }
    )
    info_items = sorted(
        {
            str(row["name"])
            for row in review_rows
            if not row["parent"]
            and str(row["adjudication"]).startswith("INFO")
        }
        | {
            (
                f"{row['declaration']}"
                f"[{row['binder_index']}:{row['binder_name']}]"
            )
            for row in inline_output
            if str(row["adjudication"]).startswith("INFO")
        }
    )
    if set(info_items) != EXPECTED_V10_F1_INFO_ITEMS:
        hard_errors.append(
            "V10-F1 exact informational infrastructure set mismatch: "
            f"missing={sorted(EXPECTED_V10_F1_INFO_ITEMS - set(info_items))}, "
            f"extra={sorted(set(info_items) - EXPECTED_V10_F1_INFO_ITEMS)}"
        )
    verdict = (
        "INCOMPLETE"
        if hard_errors
        else "ISSUES-FOUND"
        if critical_items or major_items
        else "PASS-WITH-NOTES"
    )

    source_state_paths = [
        Path(__file__),
        *DEPENDENCY_SCRIPTS,
        HARNESS,
        PLANTED,
        ENV_MODULES,
        ENV_CANDIDATES,
        ENV_REFERENCES,
        ENV_INLINE,
        PLANTED_BUILD_LOG,
        HARNESS_BUILD_LOG,
        PASS07_APPENDIX_WITNESS_LOG,
        RECERT_AUDIT,
        RECERT_MODULES,
        RECERT_COVERAGE,
        V7_CONSTANTS,
        V7_EDGES,
        V7_REVERSE,
        V7_DEAD_SWEEP,
        V7_MODULES,
        V7_COVERAGE,
        V7_SUMMARY,
        TIER_B_ENDPOINTS,
        TIER_B_EXCLUSIONS,
        TIER_B_SUMMARY,
        SOURCE_MANIFEST,
        SOURCE_MANIFEST_CHECK,
        PASS07_APPENDIX_WITNESS,
        *README_DOCS,
        *TIER_B_REVIEW_FILES,
    ]
    source_state_rows = [_source_state_row(path) for path in source_state_paths]

    review_closure_errors = [
        *primary_review_errors,
        *inline_review_errors,
        *v6_reconciliation_errors,
    ]
    review_closure_lines = [
        "V10 EXACT REVIEW CLOSURE",
        "========================",
        "verdict: " + ("PASS" if not review_closure_errors else "INCOMPLETE"),
        f"primary_consumed_only_rows: {len(primary_review_keys)}",
        f"primary_expected_rows: {EXPECTED_PRIMARY_REVIEW_COUNT}",
        f"primary_key_type_digest: {primary_review_digest}",
        f"primary_expected_key_type_digest: {EXPECTED_PRIMARY_REVIEW_DIGEST}",
        "primary_dependency_shape_nested_only_rows: "
        + str(
            sum(
                row["dependency_shape"] == "nested-only"
                for row in primary_review_closure_rows
            )
        ),
        "primary_reviewed_nested_ordinary_rows: "
        + str(len(reviewed_nested_candidates)),
        f"primary_direct_published_ordinary_rows: {len(reviewed_direct_published)}",
        "primary_direct_unpublished_reviewed_rows: "
        + str(len(reviewed_direct_unpublished)),
        f"primary_disclosed_info_rows: {len(reviewed_primary_info)}",
        "primary_ordinary_claimed_only_rows: "
        + str(len(primary_ordinary_claimed_only)),
        f"primary_tier_b_join_targets: {len(primary_v6_targets)}",
        f"inline_exact_review_rows: {len(inline_review_key_lines)}",
        f"inline_key_digest: {inline_review_key_digest}",
        f"inline_expected_key_digest: {EXPECTED_INLINE_HIGHER_ORDER_KEY_DIGEST}",
        f"inline_raw_type_digest: {inline_review_type_digest}",
        "inline_expected_raw_type_digest: "
        + EXPECTED_INLINE_HIGHER_ORDER_TYPE_DIGEST,
        "inline_published_or_claimed_rows: "
        + str(
            sum(
                row["tier_b_published"] == "yes"
                or row["document_claimed"] == "yes"
                for row in inline_review_closure_rows
            )
        ),
        "inline_internal_rows: "
        + str(
            sum(
                row["tier_b_published"] == "no"
                and row["document_claimed"] == "no"
                for row in inline_review_closure_rows
            )
        ),
        f"inline_tier_b_join_targets: {len(inline_v6_targets)}",
        "inline_claimed_only_declarations: "
        + str(len(inline_claimed_only_declarations)),
        "",
        "[inline_structural_clusters total / published-or-claimed]",
        *(
            f"{group}: {inline_review_group_counts[group]} / "
            f"{inline_review_group_claimed_counts[group]}"
            for group in EXPECTED_INLINE_REVIEW_GROUP_COUNTS
        ),
        "",
        "[closure_errors]",
        *(review_closure_errors or ["(none)"]),
    ]

    summary_lines = [
        "V10 CONDITIONAL-INTERFACE CENSUS",
        "================================",
        "verdict: " + verdict,
        f"file_walk_universe: {len(library_paths)}",
        f"hdp_source_files: {len(list(universe['hdp']))}",
        f"matrix_concentration_source_files: {len(list(universe['matrix_concentration']))}",
        f"expected_modules: {len(expected)}",
        f"v10_environment_modules: {len(env_modules)}",
        f"recert_v4_modules: {len(recert_modules)}",
        f"recert_v4_declarations: {len(v4_names)}",
        f"tier_b_theorem_endpoints: {len(tier_b)}",
        f"textual_explicit_prop_definitions: {len(textual)}",
        "textual_explicit_prop_definitions_hdp: "
        + str(
            sum(
                row.path.startswith("HighDimensionalProbability/")
                for row in textual
            )
        ),
        "textual_explicit_prop_definitions_matrix_concentration: "
        + str(
            sum(row.path.startswith("MatrixConcentration/") for row in textual)
        ),
        f"environment_primary_candidates: {len(primary)}",
        f"environment_predicates: {sum(row.category == 'predicate' for row in primary)}",
        f"environment_interfaces: {sum(row.category == 'interface' for row in primary)}",
        f"prop_valued_structure_fields: {len(fields)}",
        f"environment_only_predicates: {len(env_only)}",
        f"text_only_predicates: {len(text_only)}",
        f"ambiguous_textual_matches: {len(ambiguous_text)}",
        f"proved_candidates: {status_counts['PROVED']}",
        f"consumed_only_candidates: {status_counts['CONSUMED-ONLY']}",
        f"dead_candidates: {status_counts['DEAD']}",
        f"proved_prop_fields_inherited: {field_status_counts['PROVED']}",
        "consumed_only_prop_fields_inherited: "
        + str(field_status_counts["CONSUMED-ONLY"]),
        f"dead_prop_fields_inherited: {field_status_counts['DEAD']}",
        "dead_candidates_confirmed_v7_dead_code: "
        + str(
            sum(
                row["reconciliation"]
                == "CONFIRMED-V7-DEAD-CODE-CANDIDATE"
                for row in v7_dead_rows
            )
        ),
        "dead_candidates_v7_implementation_live: "
        + str(
            sum(
                row["reconciliation"]
                == "V10-INTERFACE-DEAD-BUT-V7-IMPLEMENTATION-LIVE"
                for row in v7_dead_rows
            )
        ),
        f"consumer_rows: {len(consumer_output)}",
        f"all_theorem_prop_binders: {len(inline_rows)}",
        f"inline_review_rows: {len(inline_output)}",
        f"inline_exact_digest_review_rows: {len(inline_review_key_lines)}",
        "inline_root_universal_review_rows: "
        + str(
            sum(
                int(row["outer_forall_depth"]) > 0
                for row in inline_review_closure_rows
            )
        ),
        "inline_nested_pi_or_nonforall_review_rows: "
        + str(inline_review_group_counts["NESTED_PI_OR_NONFORALL"]),
        "published_or_claimed_inline_prop_binders: "
        + str(
            sum(
                row["tier_b_published"] == "yes"
                or row["document_claimed"] == "yes"
                for row in inline_output
            )
        ),
        "unpublished_principle_risk_or_override_rows: "
        + str(
            sum(
                row["tier_b_published"] == "no"
                and row["document_claimed"] == "no"
                for row in inline_output
            )
        ),
        "removed_interface_absence: "
        + ("PASS" if removed_absence_passed else "FAIL"),
        "retained_finite_chevet_hzero: "
        + ("PASS" if finite_chevet_passed else "FAIL"),
        "riemannian_unpublished_infrastructure: "
        + ("PASS" if riemannian_reconciled else "FAIL"),
        "environment_harness_compile: "
        + ("PASS" if harness_compiled else "FAIL"),
        "pass07_current_appendix_witness_compile: "
        + ("PASS" if pass07_witness_compiled else "FAIL"),
        "planted_calibration: "
        + (
            "PASS"
            if planted_predicate and planted_consumer and planted_compiled
            else "FAIL"
        ),
        "interface_removal_reconciliation: "
        + ("PASS" if not stale_reconciliation else "FAIL"),
        "special_orthogonal_inline_helper: "
        + ("PASS" if so_helper_reconciled else "FAIL"),
        "exact_review_closure: "
        + ("PASS" if not review_closure_errors else "FAIL"),
        f"primary_v6_reconciled_targets: {len(primary_v6_targets)}",
        f"inline_v6_reconciled_targets: {len(inline_v6_targets)}",
        f"critical_new_conditional_items: {len(critical_items)}",
        f"major_new_conditional_items: {len(major_items)}",
        f"minor_new_conditional_items: {len(minor_items)}",
        f"info_conditional_items: {len(info_items)}",
        f"v10_f1_exact_info_items: {len(info_items)}",
        f"removed_declarations_checked_absent: {len(REMOVED_DECLARATIONS)}",
        f"removed_source_files_checked_absent: {len(REMOVED_SOURCE_FILES)}",
        "retained_finite_chevet_hzero_signatures: "
        + str(sum(finite_chevet_reconciled.values()))
        + f"/{len(FINITE_CHEVET_ZERO_DECLARATIONS)}",
        "pass07_current_appendix_axiom_replays: "
        + str(EXPECTED_PASS07_CURRENT_AXIOM_REPLAYS),
        "",
        "[candidate_status_counts]",
        *(
            f"{key}: {value}"
            for key, value in sorted(status_counts.items())
        ),
        "",
        "[inline_adjudication_counts]",
        *(
            f"{key}: {value}"
            for key, value in sorted(inline_risk_counts.items())
        ),
        "",
        "[consumed_only_candidates]",
        *(consumed_only or ["(none)"]),
        "",
        "[dead_candidates_crossfile_v7]",
        *(dead or ["(none)"]),
        "",
        "[hard_errors]",
        *(hard_errors or ["(none)"]),
        "",
        "[critical_new_conditional_items]",
        *(critical_items or ["(none)"]),
        "",
        "[major_new_conditional_items]",
        *(major_items or ["(none)"]),
        "",
        "[minor_new_conditional_items]",
        *(minor_items or ["(none)"]),
        "",
        "[info_conditional_items]",
        *(info_items or ["(none)"]),
    ]

    environment_fields = (
        "name",
        "user_name",
        "module",
        "category",
        "source_kind",
        "parent",
        "prop_fields",
        "source_location",
        "source_match",
        "status",
        "provers",
        "blocked_producers",
        "blocked_producer_prerequisites",
        "consumer_count",
        "published_consumers",
        "claimed_consumers",
        "adjudication",
    )
    outputs = {
        OUT_TEXTUAL: _render_tsv(
            (
                "path",
                "line",
                "module",
                "kind",
                "source_name",
                "environment_matches",
                "match_count",
            ),
            text_rows,
        ),
        OUT_ENVIRONMENT: _render_tsv(
            environment_fields,
            [*census_rows, *field_rows],
        ),
        OUT_DIFF: _render_tsv(
            ("side", "name", "module", "source", "explanation"),
            diff_rows,
        ),
        OUT_CENSUS: _render_tsv(
            environment_fields,
            [*census_rows, *field_rows],
        ),
        OUT_CONSUMERS: _render_tsv(
            (
                "candidate",
                "candidate_status",
                "consumer",
                "consumer_user_name",
                "consumer_module",
                "consumer_kind",
                "relation",
                "binder_index",
                "binder_name",
                "binder_info",
                "tier_b_published",
                "document_claimed",
                "adjudication",
            ),
            consumer_output,
        ),
        OUT_INLINE: _render_tsv(
            (
                "declaration",
                "declaration_user_name",
                "module",
                "binder_index",
                "binder_name",
                "binder_info",
                "head_name",
                "named_candidates",
                "higher_order",
                "tier_b_published",
                "document_claimed",
                "adjudication",
                "disclosure",
                "ledger_reference",
                "rationale",
            ),
            inline_output,
        ),
        OUT_REVIEW: _render_tsv(
            (
                "name",
                "parent",
                "status",
                "published",
                "published_consumers",
                "claimed_consumers",
                "adjudication",
                "in_source_disclosure",
                "ledger_reference",
                "rationale",
            ),
            review_rows,
        ),
        OUT_PRIMARY_REVIEW: _render_tsv(
            (
                "candidate",
                "module",
                "category",
                "source_kind",
                "dependency_shape",
                "consumer_reference_count",
                "consumer_key_digest",
                "published_consumers",
                "claimed_consumers",
                "review_key_sha256",
                "adjudication",
                "review_result",
                "rationale",
            ),
            primary_review_closure_rows,
        ),
        OUT_INLINE_REVIEW: _render_tsv(
            (
                "module",
                "declaration",
                "private_user_name",
                "binder_index",
                "binder_name",
                "binder_info",
                "head_name",
                "named_candidates",
                "type_sha256",
                "review_key_sha256",
                "outer_forall_depth",
                "terminal_head",
                "review_group",
                "tier_b_published",
                "document_claimed",
                "adjudication",
                "review_result",
                "rationale",
            ),
            inline_review_closure_rows,
        ),
        OUT_V6_RECONCILIATION: _render_tsv(
            (
                "review_scope",
                "declaration",
                "candidate",
                "review_authority",
                "expected_status",
                "observed_status",
                "result",
            ),
            v6_reconciliation_rows,
        ),
        OUT_RECONCILIATION: _render_tsv(
            (
                "ledger_item",
                "semantic_condition",
                "detector_evidence",
                "classification",
                "direction",
                "result",
            ),
            reconciliation_rows,
        ),
        OUT_V7_DEAD: _render_tsv(
            (
                "name",
                "v10_status",
                "v7_constant_present",
                "v7_reverse_citation_count",
                "v7_dead_sweep_classification",
                "v7_exclusion_reason",
                "reconciliation",
            ),
            v7_dead_rows,
        ),
        OUT_CALIBRATION: _render_tsv(
            ("calibration", "expected", "observed", "pass"),
            calibration_rows,
        ),
        OUT_REVIEW_CLOSURE: "\n".join(review_closure_lines) + "\n",
        OUT_SUMMARY: "\n".join(summary_lines) + "\n",
        OUT_SOURCE_STATE: "\n".join(source_state_rows) + "\n",
        OUT_COMMAND: command_manifest(),
    }
    metadata: dict[str, object] = {
        "hard_errors": hard_errors,
        "verdict": verdict,
        "critical_items": critical_items,
        "major_items": major_items,
        "issue_items": [*critical_items, *major_items],
        "minor_items": minor_items,
        "info_items": info_items,
        "summary": "\n".join(summary_lines) + "\n",
        "outputs": len(outputs),
    }
    return outputs, metadata


def write_outputs(outputs: Mapping[Path, str]) -> None:
    for path, text in outputs.items():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")


def lean_command(path: Path) -> list[str]:
    return [
        str(Path.home() / ".elan" / "bin" / "lake"),
        "env",
        "lean",
        "-DmaxSynthPendingDepth=3",
        "-DrelaxedAutoImplicit=false",
        str(path.relative_to(ROOT)),
    ]


def harness_command() -> list[str]:
    return lean_command(HARNESS)


def planted_command() -> list[str]:
    return lean_command(PLANTED)


def pass07_appendix_witness_command() -> list[str]:
    return lean_command(PASS07_APPENDIX_WITNESS)


def command_manifest() -> str:
    script = Path(__file__).relative_to(ROOT)
    commands = [
        ["python3", "-B", str(script), "self-test"],
        ["python3", "-B", str(script), "source-preview"],
        ["python3", "-B", str(script), "run"],
        planted_command(),
        harness_command(),
        pass07_appendix_witness_command(),
        ["python3", "-B", str(script), "analyze"],
        ["python3", "-B", str(script), "check"],
    ]
    return (
        "cwd: "
        + str(ROOT)
        + "\n"
        + "\n".join("command: " + " ".join(command) for command in commands)
        + "\n"
    )


def _run_logged_lean(command: Sequence[str], log_path: Path) -> int:
    with log_path.open("w", encoding="utf-8") as handle:
        handle.write("command: " + " ".join(command) + "\n")
        completed = subprocess.run(
            list(command),
            cwd=ROOT,
            stdout=handle,
            stderr=subprocess.STDOUT,
            text=True,
            check=False,
        )
        handle.write(f"\nexit_status: {completed.returncode}\n")
    return completed.returncode


def run_harness() -> int:
    OUT_COMMAND.write_text(
        command_manifest(),
        encoding="utf-8",
    )
    planted_returncode = _run_logged_lean(
        planted_command(),
        PLANTED_BUILD_LOG,
    )
    if planted_returncode != 0:
        return planted_returncode
    harness_returncode = _run_logged_lean(
        harness_command(),
        HARNESS_BUILD_LOG,
    )
    if harness_returncode != 0:
        return harness_returncode
    return _run_logged_lean(
        pass07_appendix_witness_command(),
        PASS07_APPENDIX_WITNESS_LOG,
    )


def self_test() -> list[str]:
    errors: list[str] = []
    predicate, consumer, detail = calibration_fixture()
    if not predicate:
        errors.append("planted FakePrinciple predicate was not detected")
    if not consumer:
        errors.append("planted fake_result consumer was not detected")
    universe = enumerate_universe()
    paths = list(universe["file_walk_universe"])
    if len(REMOVED_DECLARATIONS) != 12:
        errors.append(
            "removed declaration family must contain exactly 12 names, "
            f"found {len(REMOVED_DECLARATIONS)}"
        )
    if len(set(REMOVED_DECLARATIONS.values())) != len(
        REMOVED_DECLARATIONS
    ):
        errors.append("removed declaration source identifiers are not unique")
    if len(FINITE_CHEVET_ZERO_DECLARATIONS) != 2:
        errors.append(
            "retained finite Chevet signature set must contain exactly two "
            f"names, found {len(FINITE_CHEVET_ZERO_DECLARATIONS)}"
        )
    if len(EXPECTED_RIEMANNIAN_UNPUBLISHED_CONSUMERS) != 4:
        errors.append(
            "RiemannianDiffusionLaw must retain exactly four reviewed "
            "unpublished consumers"
        )
    if len(EXPECTED_V10_F1_INFO_ITEMS) != 10:
        errors.append(
            "V10-F1 exact informational infrastructure set must contain "
            f"ten items, found {len(EXPECTED_V10_F1_INFO_ITEMS)}"
        )
    witness_text = PASS07_APPENDIX_WITNESS.read_text(encoding="utf-8")
    witness_prints = re.findall(
        r"(?m)^#print axioms\s+(\S+)\s*$",
        witness_text,
    )
    if len(witness_prints) != EXPECTED_PASS07_CURRENT_AXIOM_REPLAYS:
        errors.append(
            "Pass07 current Appendix witness must contain exactly "
            f"{EXPECTED_PASS07_CURRENT_AXIOM_REPLAYS} axiom replays, "
            f"found {len(witness_prints)}"
        )
    stale_witness_prints = sorted(
        name
        for name in witness_prints
        if any(
            name == removed
            or name.startswith(removed + ".")
            for removed in REMOVED_DECLARATIONS
        )
    )
    if stale_witness_prints:
        errors.append(
            "Pass07 current Appendix witness replays removed declarations: "
            + ", ".join(stale_witness_prints)
        )
    stale_source_references = removed_source_references(paths)
    if stale_source_references:
        errors.append(
            "removed declaration identifiers remain in live source: "
            + ", ".join(
                f"{name}@{';'.join(locations)}"
                for name, locations in sorted(
                    stale_source_references.items()
                )
            )
        )
    stale_removed_files = [
        relative
        for relative in REMOVED_SOURCE_FILES
        if (ROOT / relative).exists() or relative in paths
    ]
    if stale_removed_files:
        errors.append(
            "removed source files remain live: "
            + ", ".join(stale_removed_files)
        )
    if any("Verification/" in str(path) for path in paths):
        errors.append("FILE-WALK universe leaked into Verification")
    if not any(str(path).startswith("MatrixConcentration/") for path in paths):
        errors.append("FILE-WALK universe omitted MatrixConcentration")
    if detail != (
        "textual_predicates=1; theorem_declarations=1; "
        "classification=CONSUMED-ONLY"
    ):
        errors.append(f"unexpected planted fixture shape: {detail}")
    missing_fixture = LOGS / "v10_intentionally_missing_evidence_fixture.log"
    if _logged_command_passed(missing_fixture):
        errors.append("missing evidence was incorrectly accepted as compiled")
    if _source_state_row(missing_fixture) != (
        "MISSING  HighDimensionalProbability/Verification/logs/"
        "v10_intentionally_missing_evidence_fixture.log"
    ):
        errors.append(
            "missing evidence did not render as a controlled source-state "
            "failure"
        )

    def fixture_candidate(name: str) -> Candidate:
        return Candidate(
            module="V10Fixture",
            name=name,
            private_user_name="",
            category="predicate",
            source_kind="definition",
            parent="",
            prop_fields=(),
        )

    def fixture_reference(
        candidate: str,
        source: str,
        relation: str,
    ) -> Reference:
        return Reference(
            candidate=candidate,
            source_module="V10Fixture",
            source=source,
            source_private_user_name="",
            source_kind="theorem",
            relation=relation,
            binder_index="0" if relation == "binder" else "",
            binder_name="h" if relation == "binder" else "",
            binder_info="explicit" if relation == "binder" else "",
            type_raw="",
        )

    cycle_candidates = [fixture_candidate("P"), fixture_candidate("Q")]
    cycle_references = [
        fixture_reference("Q", "p_from_q", "binder"),
        fixture_reference("P", "p_from_q", "conclusion_head"),
        fixture_reference("P", "q_from_p", "binder"),
        fixture_reference("Q", "q_from_p", "conclusion_head"),
    ]
    cycle_statuses = _classify_primary_candidates(
        cycle_candidates,
        [],
        cycle_references,
    )[0]
    if cycle_statuses != {"P": "CONSUMED-ONLY", "Q": "CONSUMED-ONLY"}:
        errors.append(
            "least-fixed-point producer test let a P/Q cycle discharge itself: "
            f"{cycle_statuses}"
        )

    based_candidates = [
        *cycle_candidates,
        fixture_candidate("R"),
    ]
    based_references = [
        *cycle_references,
        fixture_reference("R", "prove_r", "conclusion_head"),
        fixture_reference("R", "p_from_r", "binder"),
        fixture_reference("P", "p_from_r", "conclusion_head"),
    ]
    based_statuses = _classify_primary_candidates(
        based_candidates,
        [],
        based_references,
    )[0]
    if based_statuses != {"P": "PROVED", "Q": "PROVED", "R": "PROVED"}:
        errors.append(
            "least-fixed-point producer test failed to propagate a genuine "
            f"base proof: {based_statuses}"
        )

    fixture_digest = _line_population_digest(["fixture-row"])
    if _review_population_errors(
        "fixture",
        1,
        1,
        {"key": fixture_digest, "raw-type": fixture_digest},
        {"key": fixture_digest, "raw-type": fixture_digest},
    ):
        errors.append("exact review population validator rejected an exact match")
    count_drift = _review_population_errors(
        "fixture",
        2,
        1,
        {"key": fixture_digest},
        {"key": fixture_digest},
    )
    if not any("count drift" in error for error in count_drift):
        errors.append("exact review population validator missed count drift")
    key_drift = _review_population_errors(
        "fixture",
        1,
        1,
        {"key": "changed"},
        {"key": fixture_digest},
    )
    if not any("key digest drift" in error for error in key_drift):
        errors.append("exact review population validator missed key drift")
    type_drift = _review_population_errors(
        "fixture",
        1,
        1,
        {"raw-type": "changed"},
        {"raw-type": fixture_digest},
    )
    if not any("raw-type digest drift" in error for error in type_drift):
        errors.append("exact review population validator missed raw-type drift")

    parser_fixture = InlineBinder(
        module="V10Fixture",
        declaration="V10Fixture.universal",
        private_user_name="",
        binder_index=0,
        binder_name="h",
        binder_info="explicit",
        head_name="[anonymous]",
        named_candidates=(),
        type_raw=(
            "Lean.Expr.forallE\\n"
            "  `x\\n"
            "  (Lean.Expr.const `Nat [])\\n"
            "  (Lean.Expr.app\\n"
            "    (Lean.Expr.const `Eq [])\\n"
            "    (Lean.Expr.fvar (Lean.Name.mkNum `_uniq 1)))\\n"
            "  Lean.BinderInfo.default"
        ),
    )
    if _inline_terminal_shape(parser_fixture) != (1, "Eq"):
        errors.append(
            "raw Lean Expr parser failed root-forall/terminal-head fixture: "
            f"{_inline_terminal_shape(parser_fixture)}"
        )
    return errors


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "mode",
        choices=("self-test", "source-preview", "run", "analyze", "check"),
    )
    args = parser.parse_args()

    if args.mode == "self-test":
        errors = self_test()
        if errors:
            result = "V10 self-test: FAIL\n" + "\n".join(
                f"- {error}" for error in errors
            ) + "\n"
            OUT_SELF_TEST.write_text(result, encoding="utf-8")
            print(result, end="")
            return 1
        result = (
            "V10 self-test: PASS\n"
            "controls: removed-family source and 15-row witness absence; "
            "planted conditional; fixed-point cycles; exact-match acceptance; "
            "count/key/raw-type drift rejection; raw Expr root-forall parser; "
            "controlled missing-evidence rejection\n"
        )
        OUT_SELF_TEST.write_text(result, encoding="utf-8")
        print(result, end="")
        return 0

    if args.mode == "source-preview":
        universe = enumerate_universe()
        paths = list(universe["file_walk_universe"])
        predicates, commands = enumerate_textual_predicates(paths)
        removed_references = removed_source_references(paths)
        removed_files_present = [
            relative
            for relative in REMOVED_SOURCE_FILES
            if (ROOT / relative).exists() or relative in paths
        ]
        finite_source_signatures = {
            declaration: any(
                row.module
                == "HighDimensionalProbability.Chapter8_Chaining"
                and row.name == source_name
                and re.search(
                    r"\bhzero\s*:.*?0\s*:.*?∈\s*T\b",
                    row.statement,
                )
                is not None
                for row in commands
            )
            for declaration, source_name in (
                FINITE_CHEVET_ZERO_DECLARATIONS.items()
            )
        }
        lines = [
            f"file_walk_universe={len(paths)}",
            f"textual_explicit_prop_definitions={len(predicates)}",
            "removed_declaration_source_references="
            + str(sum(map(len, removed_references.values()))),
            "removed_source_files_present="
            + str(len(removed_files_present)),
            "retained_finite_chevet_hzero_source_signatures="
            + str(sum(finite_source_signatures.values()))
            + f"/{len(FINITE_CHEVET_ZERO_DECLARATIONS)}",
            *(
                f"{row.path}:{row.line}\t{row.kind}\t{row.name}"
                for row in predicates
            ),
        ]
        result = "\n".join(lines) + "\n"
        OUT_SOURCE_PREVIEW.write_text(result, encoding="utf-8")
        print(result, end="")
        return (
            0
            if not removed_references
            and not removed_files_present
            and all(finite_source_signatures.values())
            else 1
        )

    if args.mode == "run":
        returncode = run_harness()
        if returncode != 0:
            print(
                f"V10 Lean replay failed with exit {returncode}; see "
                "the planted, environment-harness, and Pass07 witness logs "
                f"under {LOGS.relative_to(ROOT)}",
                file=sys.stderr,
            )
            return returncode

    outputs, metadata = analyze()
    hard_errors = list(metadata["hard_errors"])
    verdict = str(metadata["verdict"])
    if args.mode == "check":
        drift: list[str] = []
        for path, expected in outputs.items():
            if not path.exists():
                drift.append(f"missing {path.relative_to(ROOT)}")
            elif path.read_text(encoding="utf-8") != expected:
                drift.append(f"drift {path.relative_to(ROOT)}")
        if drift:
            result = "V10 evidence check: FAIL\n" + "\n".join(
                f"- {item}" for item in drift
            ) + "\n"
            OUT_CHECK.write_text(result, encoding="utf-8")
            print(result, end="")
            return 1
        if hard_errors:
            result = "V10 evidence check: INCOMPLETE\n" + "\n".join(
                f"- {error}" for error in hard_errors
            ) + "\n"
            OUT_CHECK.write_text(result, encoding="utf-8")
            print(result, end="")
            return 2
        if verdict == "ISSUES-FOUND":
            issue_items = list(metadata["issue_items"])
            result = "V10 evidence check: FAIL\n" + "\n".join(
                f"- critical/major conditional item: {item}"
                for item in issue_items
            ) + "\n"
            OUT_CHECK.write_text(result, encoding="utf-8")
            print(result, end="")
            return 1
        result = "V10 evidence check: PASS\n"
        OUT_CHECK.write_text(result, encoding="utf-8")
        print(result, end="")
        return 0

    write_outputs(outputs)
    print(metadata["summary"], end="")
    if hard_errors:
        return 2
    return 1 if verdict == "ISSUES-FOUND" else 0


if __name__ == "__main__":
    raise SystemExit(main())
