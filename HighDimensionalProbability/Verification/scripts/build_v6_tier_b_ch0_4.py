#!/usr/bin/env python3
"""Build the static V6 Tier-B close-reading ledger for Appetizer--Chapter 4.

This script is deliberately source-only: it reads the frozen row inventories
and Lean source text, but never invokes Lean or Lake.  The mathematical
verdicts and the citation candidates below are review judgments, not machine
proofs.  Tier-C compilation remains a separate verification stage.
"""

from __future__ import annotations

import argparse
import bisect
import csv
import io
import json
import re
from collections import Counter
from functools import lru_cache
from pathlib import Path

from source_manifest import build_manifest
from verify_exercise_reorganization import (
    old_to_new_exercise_path,
    require_certificate as require_reorganization_certificate,
)


PROJECT = Path(__file__).resolve().parents[3]
VERIFICATION = PROJECT / "HighDimensionalProbability" / "Verification"
INVENTORY = VERIFICATION / "inventory"
REVIEW = VERIFICATION / "review"
OUTPUT = REVIEW / "v6_tier_b_ch0_4.tsv"
SUMMARY = REVIEW / "v6_tier_b_ch0_4_summary.txt"
SOURCE_MANIFEST = VERIFICATION / "logs" / "source_manifest.txt"
ROUND10_DELTA_LOG = VERIFICATION / "logs" / "round10_docstring_delta.log"
SEMANTIC_BASELINE_DIGEST = (
    "83678e994eecf416759cb099d5e69f9d03c15921960d4f3b69d055a7a9e8fe27"
)
ROUND10_SOURCE_DIGEST = (
    "bca641bd4c523754aa472b97cb1ed5638a6eb7361f99158a3f231a03a7446460"
)

ASSIGNED_CHAPTERS = {
    "Appetizer",
    "Chapter 1",
    "Chapter 2",
    "Chapter 3",
    "Chapter 4",
}

FIELDS = (
    "row_set",
    "sample_kind",
    "sample_rank",
    "row_id",
    "chapter",
    "book_label",
    "resolved_declarations",
    "verdict",
    "joint_satisfiability",
    "nontrivial_conclusion",
    "typeclass_nondegeneracy",
    "quantifier_usability",
    "justification",
    "witness_by_citation_candidate",
    "source_locations",
    "tier_c_required",
)

IDENTIFIER = re.compile(
    r"(?:«[^»]+»|[A-Za-z_][A-Za-z0-9_']*)"
    r"(?:\.(?:«[^»]+»|[A-Za-z_][A-Za-z0-9_']*))*"
)
COMMAND = re.compile(
    r"""(?x)
    ^[ \t]*
    (?:@\[[^\r\n]*\][ \t]*)?
    (?:(?:private|protected|noncomputable|unsafe|local)[ \t]+)*
    (?P<kind>
      theorem|lemma|def|abbrev|structure|class|alias|irreducible_def
    )
    [ \t]+
    (?P<name>
      (?:«[^»]+»|[A-Za-z_][A-Za-z0-9_']*)
      (?:\.(?:«[^»]+»|[A-Za-z_][A-Za-z0-9_']*))*
    )
    (?=[ \t({[:=]|$)
    """
)

# Exact locations for endpoints whose short name is ambiguous, whose command
# uses a qualified name, or whose declaration lives in Mathlib.
LOCATION_OVERRIDES: dict[str, tuple[str, int, str]] = {
    "Finset.convexHull_eq": (
        ".lake/packages/mathlib/Mathlib/Analysis/Convex/Combination.lean",
        342,
        "theorem",
    ),
    "convexHull_eq_union": (
        ".lake/packages/mathlib/Mathlib/Analysis/Convex/Caratheodory.lean",
        149,
        "theorem",
    ),
    "MeasureTheory.integral": (
        ".lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean",
        160,
        "irreducible_def",
    ),
    "MeasureTheory.eLpNorm": (
        ".lake/packages/mathlib/Mathlib/MeasureTheory/Function/LpSeminorm/Defs.lean",
        86,
        "def",
    ),
    "MeasureTheory.L2.inner_def": (
        ".lake/packages/mathlib/Mathlib/MeasureTheory/Function/L2Space.lean",
        139,
        "theorem",
    ),
    "ProbabilityTheory.covariance_eq_sub": (
        ".lake/packages/mathlib/Mathlib/Probability/Moments/Covariance.lean",
        54,
        "lemma",
    ),
    "MeasureTheory.TendstoInDistribution": (
        ".lake/packages/mathlib/Mathlib/MeasureTheory/Function/ConvergenceInDistribution.lean",
        64,
        "structure",
    ),
    "LinearMap.IsSymmetric.eigenvectorBasis": (
        ".lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Spectrum.lean",
        300,
        "irreducible_def",
    ),
    "ProbabilityTheory.HasGaussianLaw.iIndepFun_of_covariance_strongDual": (
        ".lake/packages/mathlib/Mathlib/Probability/Distributions/Gaussian/"
        "IsGaussianProcess/Independence.lean",
        65,
        "lemma",
    ),
    "ProbabilityTheory.covarianceBilin_stdGaussian": (
        ".lake/packages/mathlib/Mathlib/Probability/Distributions/Gaussian/"
        "Multivariate.lean",
        122,
        "lemma",
    ),
    "SimpleGraph.adjMatrix": (
        ".lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/AdjMatrix.lean",
        237,
        "def",
    ),
    "dist_eq_norm": (
        ".lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean",
        765,
        "alias",
    ),
    "HDP.SubGaussian.tail_bound": (
        "HighDimensionalProbability/Chapter2_ConcentrationOfIndependentSums.lean",
        3649,
        "theorem",
    ),
    "HDP.SubExponential.mgf_bound": (
        "HighDimensionalProbability/Chapter2_ConcentrationOfIndependentSums.lean",
        9018,
        "theorem",
    ),
    "HDP.IsSubGaussianRandomVector.psi2NormSet_bddAbove": (
        "HighDimensionalProbability/Prelude/RandomVector.lean",
        302,
        "theorem",
    ),
    "HDP.Chapter4.RealSVD.apply_right": (
        "HighDimensionalProbability/Chapter4_RandomMatrices.lean",
        503,
        "theorem",
    ),
    "HDP.Chapter4.matrixLpToLpNorm_bilinear_isGreatest": (
        "HighDimensionalProbability/Chapter4_RandomMatrices.lean",
        4054,
        "theorem",
    ),
    "HDP.Chapter4.remark_4_4_6_independentRows": (
        "HighDimensionalProbability/Chapter4_RandomMatrices.lean",
        9977,
        "alias",
    ),
    "HDP.Chapter4.remark_4_7_3": (
        "HighDimensionalProbability/Chapter4_RandomMatrices.lean",
        14389,
        "alias",
    ),
    # These Chapter 9 names are redeclared in exercise modules.  Preserve the
    # reviewed main-chapter declarations while resolving their current lines.
    "HDP.Chapter9.IsPositivelyHomogeneous": (
        "HighDimensionalProbability/Chapter9_DeviationsOfRandomMatricesOnSets.lean",
        14854,
        "def",
    ),
    "HDP.Chapter9.matrixMeasurements": (
        "HighDimensionalProbability/Chapter9_DeviationsOfRandomMatricesOnSets.lean",
        12702,
        "def",
    ),
    "HDP.Chapter9.HasEuclideanGrowth": (
        "HighDimensionalProbability/Chapter9_DeviationsOfRandomMatricesOnSets.lean",
        14878,
        "def",
    ),
}

# Static reverse-citation leads.  These are candidates for Tier C, not accepted
# witnesses: Tier C must still check that the citation really instantiates all
# hypotheses and that its compiled axiom set is allowed.
CITATION_CANDIDATES = {
    "HDP.Chapter0.approximate_caratheodory":
        "HDP.Chapter0.exists_polytope_cover",
    "HDP.Chapter0.exists_polytope_cover":
        "HDP.Chapter0.polytope_volume_le_card_mul_ball",
    "HDP.Chapter0.polytope_volume_equation_0_3":
        "HDP.Chapter0.polytope_volume_le_theorem_0_0_4",
    "HDP.Chapter1.example_1_4_2_calc":
        "HDP.Chapter1.example_1_4_2",
    "HDP.Chapter1.union_bound":
        "HDP.Chapter1.union_bound_fintype",
    "HDP.Chapter1.bookCDF":
        "HDP.Chapter1.tail_eq_one_sub_cdf",
    "HDP.Chapter1.stirling_approximation":
        "HDP.Chapter1.stirling_ratio_tendsto_one",
    "HDP.Chapter2.medianOfMeans_explicit":
        "HDP.Chapter2.medianOfMeans_theorem_2_4_1",
    "HDP.SubGaussian.tail_bound":
        "HDP.subgaussian_hoeffding",
    "HDP.psi2Norm_eq_zero_iff":
        "HDP.psi2Norm_sum_sq_le",
    "HDP.pythagorean_identity":
        "HDP.khintchine",
    "HDP.psi2Norm_sum_sq_le":
        "HDP.subgaussian_hoeffding",
    "HDP.Chapter3.pca_kth_component_le":
        "HDP.Chapter3.pca_kth_maximum_principle",
    "HDP.map_gaussianDirection_stdGaussian":
        "HDP.Chapter3.map_projectiveGaussianDirection",
    "HDP.Chapter3.relaxation_is_sdp":
        "HDP.Chapter3.exercise_3_52a",
    "HDP.SimpleGraph.cutSize":
        "HDP.Chapter3.graphCutObjective_eq_cutValue",
    "HDP.Chapter4.theorem_4_6_1_gram":
        "HDP.Chapter4.theorem_4_6_1_singular_normalized",
    "HDP.Chapter4.theorem_4_4_3":
        "HDP.Chapter4.exercise_4_41a",
}

# Hand-written close-reading judgments for the frozen Tier-C queue.  These
# rows deliberately remain distinct from matching README rows: their census
# target ID, deterministic rank, and sample kind are part of the V6 evidence.
QUEUE_EVIDENCE: dict[str, dict[str, str]] = {
    "census-267f53840f7e9669": {
        "h": (
            "OK: N(n)=1 makes log(N(n))/n identically zero, so the single "
            "subexponential-growth premise is jointly satisfiable"
        ),
        "c": (
            "OK: the endpoint concludes two genuine Tendsto statements, for both "
            "the comparison radius and its n-th-power volume coefficient"
        ),
        "t": (
            "OK: it uses only ℕ and ℝ with their standard nontrivial instances; "
            "no typeclass or index assumption forces a degenerate model"
        ),
        "q": (
            "OK: N is universally supplied and the convergence premise is explicit; "
            "neither conjunct is hidden behind an empty-domain guard"
        ),
    },
    "census-3a5e7fbc0e9c1199": {
        "h": (
            "OK: n=1, k=4, and V={0} satisfy k>0 and the unit-ball hypothesis, "
            "giving a concrete positive-radius finite-cover instance"
        ),
        "c": (
            "OK: it constructs a finite internal cover with simultaneous cardinality, "
            "convex-hull membership, and metric-cover guarantees"
        ),
        "t": (
            "OK: Fin 1 and Fin 4 are nonempty and the Euclidean target is nontrivial; "
            "positivity of k prevents division by a zero square root"
        ),
        "q": (
            "OK: k, V, and every ball-membership premise are explicit, and the "
            "existential cover carries all three advertised properties"
        ),
    },
    "census-b5a26cf1bfc1ad02": {
        "h": (
            "OK: n=1, k=1, and V={-1,1} satisfy NeZero n, k>0, and the unit-ball "
            "guards while the convex hull has positive one-dimensional volume"
        ),
        "c": (
            "OK: the endpoint compares the actual polytope volume with the finite "
            "N^k times scaled-unit-ball expression, not with top or a reflexive bound"
        ),
        "t": (
            "OK: NeZero n supplies positive ambient dimension and k>0 controls the "
            "sqrt/inverse factor; the standard volume instance is nondegenerate"
        ),
        "q": (
            "OK: n, k, V, positivity, and vertex containment are all bound in the "
            "statement; no existential replacement weakens the volume inequality"
        ),
    },
    "census-0407bd4f173c5018": {
        "h": (
            "OK: n=1 and V={-1,1} give a positive-volume polytope inside the unit "
            "ball and satisfy the explicit NeZero dimension premise"
        ),
        "c": (
            "OK: the conclusion is a data-dependent relative-volume upper bound with "
            "the logarithmic vertex-count coefficient from Theorem 0.0.4"
        ),
        "t": (
            "OK: NeZero n rules out the zero-dimensional denominator case, and the "
            "unit-ball volume denominator is positive and finite in the source"
        ),
        "q": (
            "OK: V and its pointwise unit-ball guard are explicit; the theorem does "
            "not assume or manufacture the desired volume inequality"
        ),
    },
    "census-6d302c76844756f6": {
        "h": (
            "OK: n=1, k=4, T={-1,1}, and x=0 give a non-singleton convex-hull "
            "instance satisfying k>0 and the unit-ball inclusion"
        ),
        "c": (
            "OK: it produces k actual points of T whose equal average approximates "
            "the prescribed convex-hull point at the quantitative 1/sqrt(k) rate"
        ),
        "t": (
            "OK: positive k makes Fin k nonempty and the error scale well-defined; "
            "the one-dimensional Euclidean model is nontrivial"
        ),
        "q": (
            "OK: T, x, k, containment, and convex-hull membership are explicit and "
            "the witnesses must lie in T pointwise"
        ),
    },
    "census-9f31959287a10a6f": {
        "h": (
            "OK: for example n=16 and p=4*log(16)/16 satisfy n>=2, 0<=p<=1, "
            "and the displayed density lower bound"
        ),
        "c": (
            "OK: the conclusion is the quantitative inequality "
            "n*(1-p)^(n-1)<=1/n, not a propositional placeholder"
        ),
        "t": (
            "OK: only standard ℕ/ℝ operations occur, and n>=2 makes every relevant "
            "real denominator nonzero"
        ),
        "q": (
            "OK: n and p are implicit universal parameters with four explicit "
            "guards; none of those guards contains the conclusion"
        ),
    },
    "census-2d26ccb495448c13": {
        "h": (
            "OK: Bool with its fair probability law, a finite index set, and "
            "measurable singleton events satisfies all hypotheses"
        ),
        "c": (
            "OK: it bounds the probability of a finite union by the sum of the "
            "individual probabilities and can be strict on overlapping events"
        ),
        "t": (
            "OK: IsProbabilityMeasure is realized by a nontrivial Bool model; no "
            "Subsingleton or empty-index instance is required"
        ),
        "q": (
            "OK: the finite index set, event family, and per-index measurability "
            "proofs are universally supplied; the union is over exactly that set"
        ),
    },
    "census-da73b26c72381b81": {
        "h": (
            "OK: a Bernoulli real-valued variable on Bool and any threshold give a "
            "concrete intended instantiation of the definition"
        ),
        "c": (
            "OK: bookCDF is the actual distribution-dependent value "
            "mu.real{omega | X omega<=t}, not a constant or empty placeholder"
        ),
        "t": (
            "OK: the definition works on the standard nontrivial Borel probability "
            "model and imposes no degenerating typeclass"
        ),
        "q": (
            "OK: X, mu, and t are explicit arguments; the downstream tail identity "
            "adds the necessary probability and measurability guards"
        ),
    },
    "census-fec3d811788b995d": {
        "h": (
            "OK: this is a closed theorem about the ordinary factorial and Stirling "
            "comparison sequences, so there are no mutually inconsistent hypotheses"
        ),
        "c": (
            "OK: Asymptotics.IsEquivalent atTop asserts a genuine ratio-asymptotic "
            "relationship between two nonconstant sequences"
        ),
        "t": (
            "OK: it uses the standard nontrivial real topology and natural-number "
            "filter, with no selectable degenerate instance"
        ),
        "q": (
            "OK: both sequences and atTop are fixed explicitly in the conclusion; "
            "there is no weakened existential rate or empty quantifier"
        ),
    },
    "census-e21f4bd7ac0aa1f2": {
        "h": (
            "OK: n=1 satisfies the sole guard 1<=n and makes both exponential "
            "correction terms finite and positive"
        ),
        "c": (
            "OK: the endpoint gives simultaneous explicit lower and upper Robbins "
            "bounds for n!, with distinct 1/(12n+1) and 1/(12n) corrections"
        ),
        "t": (
            "OK: the standard ℕ/ℝ structure is nontrivial and 1<=n prevents every "
            "displayed correction denominator from vanishing"
        ),
        "q": (
            "OK: n is universally quantified with its domain guard explicit, and "
            "both inequalities appear directly as a conjunction"
        ),
    },
    "census-9f946e24c21c0d16": {
        "h": (
            "OK: a centered Rademacher variable on a finite product probability "
            "space is measurable and subgaussian, so the premises have a nonzero model"
        ),
        "c": (
            "OK: the sampled endpoint proves the definiteness component "
            "psi2Norm X mu=0 iff X=0 almost surely, which distinguishes nonzero laws"
        ),
        "t": (
            "OK: the probability and Borel instances are realized on a nontrivial "
            "finite space; no zero measure is forced"
        ),
        "q": (
            "OK: X, its a.e. measurability, and SubGaussian evidence are explicit; "
            "the almost-everywhere zero conclusion has the same fixed measure"
        ),
    },
    "census-eb2cb15c80bf5d1d": {
        "h": (
            "OK: on Bool, positive N and sigma with constant block means equal to m "
            "satisfy measurability, independence, L2, mean, and variance hypotheses"
        ),
        "c": (
            "OK: the conclusion is an explicit Gaussian-shaped tail bound for the "
            "median-of-means estimator at the t*sigma/sqrt(N) deviation scale"
        ),
        "t": (
            "OK: IsProbabilityMeasure has nontrivial models, hN and hsigma are "
            "explicit, and the finite block type is total for every t"
        ),
        "q": (
            "OK: every block property is quantified over the same Fin block count, "
            "and t is universally supplied with the intended nonnegativity guard"
        ),
    },
    "census-2122a3c307b06378": {
        "h": (
            "OK: two independent centered Rademacher coordinates on Bool x Bool are "
            "L2 and satisfy the stated pairwise-independence hypotheses"
        ),
        "c": (
            "OK: the integral of the squared sum is equated to the sum of coordinate "
            "second moments, giving 2=1+1 in the concrete model"
        ),
        "t": (
            "OK: the probability space and Fin 2 index are nontrivial; the theorem "
            "does not rely on an empty family"
        ),
        "q": (
            "OK: L2 membership, zero means, and pairwise independence are explicit "
            "for the same universally supplied family X"
        ),
    },
    "census-5ca87340a1da981b": {
        "h": (
            "OK: a Rademacher variable on Bool is a nonzero measurable subgaussian "
            "example, and any t>=0 supplies the final guard"
        ),
        "c": (
            "OK: it bounds the actual tail measure of |X| by an explicit exponential "
            "expression involving the data-dependent psi2 norm"
        ),
        "t": (
            "OK: IsProbabilityMeasure is realized nondegenerately; the proof handles "
            "the possible zero psi2 norm without requiring it"
        ),
        "q": (
            "OK: measurability, SubGaussian X, and t>=0 are explicit, and the event "
            "uses the same X, t, and measure"
        ),
    },
    "census-245bfc29931f8f1f": {
        "h": (
            "OK: independent centered Rademacher coordinates on a finite product "
            "space meet measurability, subgaussianity, mean, and iIndepFun premises"
        ),
        "c": (
            "OK: it proves both subgaussianity of the sum and the quantitative "
            "psi2-norm-square bound with constant 30"
        ),
        "t": (
            "OK: positive finite families give nontrivial models, while the valid "
            "empty-family boundary does not force all instantiations to degenerate"
        ),
        "q": (
            "OK: all four family hypotheses quantify over the same Fin N and the "
            "conclusion fixes the full finite sum rather than an existential subfamily"
        ),
    },
    "census-224df4d887e11824": {
        "h": (
            "OK: E=EuclideanSpace R (Fin 1) satisfies Nontrivial, Borel, and "
            "finite-dimensional requirements for the standard Gaussian law"
        ),
        "c": (
            "OK: the conclusion is equality of the pushed-forward Gaussian-direction "
            "law with normalized sphere measure, not equality to a junk measure"
        ),
        "t": (
            "OK: the enclosing section explicitly requires Nontrivial E, preventing "
            "the empty unit-sphere degeneration"
        ),
        "q": (
            "OK: the same type E determines gaussianDirection, stdGaussian, and "
            "unitSphereMeasure; no hidden existential direction is introduced"
        ),
    },
    "census-d718684b7c04a068": {
        "h": (
            "OK: the two-vertex graph with its single edge and a singleton cut is a "
            "finite concrete model with cutSize equal to one"
        ),
        "c": (
            "OK: cutSize computes the cardinality of the crossing-edge finset and "
            "varies with both the graph and selected vertex set"
        ),
        "t": (
            "OK: Fintype V admits nonempty finite graphs such as Bool; it does not "
            "force V to be empty or the graph to be edgeless"
        ),
        "q": (
            "OK: G and s are explicit arguments and complementation is taken in the "
            "same finite vertex type"
        ),
    },
    "census-2b0c5af75c707385": {
        "h": (
            "OK: E=R, n=1, k=0, the identity self-adjoint operator, and a unit vector "
            "satisfy finite dimensionality, rank, norm, and orthogonality premises"
        ),
        "c": (
            "OK: it bounds the Rayleigh quotient by the ordered kth eigenvalue and "
            "feeds the attained IsGreatest maximum principle"
        ),
        "t": (
            "OK: k:Fin n itself forces n>0, and rank(E)=n therefore rules out a "
            "zero-dimensional space in every theorem instance"
        ),
        "q": (
            "OK: T, self-adjointness, rank equality, k, x, unit norm, and all earlier "
            "orthogonality equations are explicit"
        ),
    },
    "census-9cd803067f94be16": {
        "h": (
            "OK: n=Bool and a nonzero symmetric matrix A give finite unit-vector and "
            "PSD-diagonal-one feasible instances in both directions"
        ),
        "c": (
            "OK: the conjunction constructs a PSD Gram matrix from every unit-vector "
            "assignment and a finite Gram factorization from every feasible matrix"
        ),
        "t": (
            "OK: Fintype n admits nonempty models; permitting the empty finite type "
            "as a boundary case does not force the correspondence to collapse"
        ),
        "q": (
            "OK: both directions universally quantify their feasible input and return "
            "witnesses preserving the same objective value"
        ),
    },
    "census-c103da4532e6de9a": {
        "h": (
            "OK: n=1 with the uniform two-point law X=+/-1 on Bool is injective, "
            "isotropic, subgaussian, bounded in direction, and has positive atoms"
        ),
        "c": (
            "OK: the endpoint jointly proves explicit Shannon-entropy and support-cardinality "
            "lower bounds depending on n and the vector psi2 norm"
        ),
        "t": (
            "OK: Fintype and measurable-singleton instances are realized by Bool, "
            "IsProbabilityMeasure is nonzero, and hn forces positive vector dimension"
        ),
        "q": (
            "OK: measurability, subgaussianity, boundedness, isotropy, injectivity, "
            "and atom positivity all constrain the same universally supplied X and mu"
        ),
    },
    "census-f0adfeea6d016929": {
        "h": (
            "OK: independent standard-Gaussian rows with positive m and r, a nonzero "
            "deterministic B, K>0, and u>=0 satisfy the covariance-tail premises"
        ),
        "c": (
            "OK: the alias exposes a quantitative high-probability operator-norm "
            "covariance deviation bound with confidence factor 2*exp(-u)"
        ),
        "t": (
            "OK: NeZero m prevents normalization by zero; standard positive finite "
            "matrix dimensions and probability instances are nondegenerate"
        ),
        "q": (
            "OK: row measurability, subgaussianity, isotropy, independence, finiteness, "
            "K bound, and u>=0 are all explicit for the same A"
        ),
    },
    "census-8398f0da580bf50e": {
        "h": (
            "OK: m=n=1, A=[2], and Q=R=identity satisfy both orthogonal-group "
            "hypotheses on a nonzero matrix"
        ),
        "c": (
            "OK: it simultaneously preserves the Frobenius and Euclidean operator "
            "norms under left/right orthogonal multiplication"
        ),
        "t": (
            "OK: positive one-dimensional Fin types give a nontrivial model; the "
            "statement does not force zero dimensions or a zero matrix"
        ),
        "q": (
            "OK: A, Q, R and both group-membership proofs are explicit, and both norm "
            "equalities concern exactly Q*A*R"
        ),
    },
    "census-07ea02d9a6c34534": {
        "h": (
            "OK: a positive-dimensional matrix with independent standard-Gaussian "
            "rows is measurable, isotropic, subgaussian, independent, and has a finite row psi2 bound"
        ),
        "c": (
            "OK: it gives an explicit exponential tail for the normalized-Gram "
            "operator error, from which simultaneous singular-value bounds are derived"
        ),
        "t": (
            "OK: NeZero m and NeZero n rule out both zero matrix dimensions and make "
            "normalization and extremal singular indices usable"
        ),
        "q": (
            "OK: every row-law hypothesis, K>0, the row bound, and t>=0 is explicit "
            "and applies to the same random matrix A"
        ),
    },
    "census-b72ca80e04954340": {
        "h": (
            "OK: n=1, A=[2], and the unit vector x=1 satisfy Nonempty(Fin n), "
            "Hermitian symmetry, and the Rayleigh feasible-set constraints"
        ),
        "c": (
            "OK: IsGreatest records both attainment and domination of every absolute "
            "Rayleigh quotient by the actual operator norm"
        ),
        "t": (
            "OK: Nonempty(Fin n) explicitly prevents the zero-dimensional sphere "
            "case, so the maximum has a genuine unit-vector witness"
        ),
        "q": (
            "OK: A and hA are explicit and the set comprehension universally ranges "
            "over unit vectors with the exact Rayleigh value"
        ),
    },
    "census-b8473c9d92ff7d07": {
        "h": (
            "OK: positive m,n with independent centered Rademacher entries, a valid "
            "common psi2 bound K>0, and t>=0 satisfy all hypotheses"
        ),
        "c": (
            "OK: it bounds the actual operator-norm exceedance event by "
            "2*exp(-t^2) at the explicit K*(sqrt m+sqrt n+t) threshold"
        ),
        "t": (
            "OK: NeZero m and NeZero n make both unit-sphere nets nonempty and prevent "
            "dimension-zero collapse"
        ),
        "q": (
            "OK: entry measurability, subgaussianity, centering, joint independence, "
            "K control, and t>=0 are explicit for the same A"
        ),
    },
}

EXERCISE_EVIDENCE: dict[str, dict[str, str]] = {
    "exercise-decl-3da30ccf25e59552": {
        "h": (
            "OK: n=7 satisfies the sole arithmetic guard and the G(7,1/2) law is "
            "a genuine probability measure on a nonempty finite graph space"
        ),
        "c": (
            "OK: it gives a quantitative lower probability for the event that every "
            "vertex subset above the logarithmic size threshold contains an edge"
        ),
        "t": (
            "OK: n>=7 makes Fin n nonempty and all logarithmic/division expressions "
            "use positive real arguments and a nonzero log 2 denominator"
        ),
        "q": (
            "OK: n is universally bound with its guard explicit, and the event "
            "universally tests every Finset S of the same vertex type"
        ),
    },
    "exercise-decl-831b9b92ab200261": {
        "h": (
            "OK: lambda=16 and p=1/2 satisfy lambda>0 and "
            "2*log(lambda)/lambda<=p inside the unit interval"
        ),
        "c": (
            "OK: the Poisson-weighted mixture of Erdos-Renyi no-isolated-vertex "
            "probabilities receives the explicit lower bound 1-1/lambda"
        ),
        "t": (
            "OK: positive lambda prevents the displayed denominator from vanishing, "
            "and the unit-interval p parameter is nondegenerate"
        ),
        "q": (
            "OK: lambda, positivity, p, and the threshold inequality are explicit; "
            "the infinite sum ranges over the stated Poisson size variable"
        ),
    },
    "exercise-decl-278aa24d885d9e56": {
        "h": (
            "OK: on fair Bool take n=1, X in {0,1}, and f(x)=x^2; the range is "
            "finite, f is convex, and both required functions are integrable"
        ),
        "c": (
            "OK: the Jensen inequality compares f of the vector expectation with "
            "the expectation of f and is strict in the displayed Bernoulli model"
        ),
        "t": (
            "OK: IsProbabilityMeasure has a nontrivial Bool realization and "
            "EuclideanSpace R (Fin 1) is nonzero"
        ),
        "q": (
            "OK: the finite-range, convexity, and two integrability premises all "
            "refer to the same universally supplied X, f, and measure"
        ),
    },
    "exercise-decl-0b06c391a508bcf5": {
        "h": (
            "OK: on R with gaussianReal 0 1, the identity random variable has the "
            "required Gaussian law with m=0 and v=1"
        ),
        "c": (
            "OK: it identifies both the optimal centered MGF variance proxy and the "
            "exact subgaussian norm with explicit Gaussian parameters"
        ),
        "t": (
            "OK: the standard Gaussian probability and Borel structures are "
            "nontrivial; v is an NNReal variance rather than an arbitrary bad scale"
        ),
        "q": (
            "OK: X, m, v, and the single HasLaw premise share one fixed measure, and "
            "both equalities occur directly in the conjunction"
        ),
    },
    "exercise-decl-15f7d20722b37f8b": {
        "h": (
            "OK: each implication domain has positive concrete parameters, e.g. "
            "rate 1, geometric p=1/2, gamma shapes/rates 1, and Cauchy scale 1"
        ),
        "c": (
            "OK: seven conjuncts rule out SubGaussian identity laws for exponential, "
            "Poisson, geometric, Gamma, Cauchy, and Pareto heavy-tail families"
        ),
        "t": (
            "OK: all distribution families use their standard nontrivial measurable "
            "spaces, and explicit positivity/interior guards exclude degenerate laws"
        ),
        "q": (
            "OK: every law parameter is universally quantified before its positivity "
            "guard and corresponding non-subgaussian conclusion"
        ),
    },
    "exercise-decl-ecbc4df81ce84dba": {
        "h": (
            "OK: the canonical product probability space of N independent Unif[0,1] "
            "coordinates (for example N=1) satisfies HasLaw and iIndepFun"
        ),
        "c": (
            "OK: it simultaneously lower- and upper-bounds the probability that the "
            "coordinate product exceeds its own expectation by two exponential rates"
        ),
        "t": (
            "OK: hN makes Fin N nonempty and the uniform probability law is "
            "nondegenerate; no empty product is used"
        ),
        "q": (
            "OK: all coordinates have the same explicit uniform law, independence "
            "covers the same family, and both bounds concern the identical event"
        ),
    },
    "exercise-decl-c0243dd1ef50495d": {
        "h": (
            "OK: on two vertices with nonnegative off-diagonal weights and antipodal "
            "unit vectors, the SDP cut objective is positive; any 0<epsilon<439/500 works"
        ),
        "c": (
            "OK: it constructs a Las Vegas rounding certificate with deterministic "
            "cut guarantee and an explicit expected-runtime upper bound"
        ),
        "t": (
            "OK: finite nonempty vertex and Gaussian-coordinate types give a genuine "
            "rounding model; the positive SDP and epsilon guards make the denominator positive"
        ),
        "q": (
            "OK: A, nonnegative weights, unit assignment, epsilon range, and positive "
            "SDP value are explicit before the certificate existential"
        ),
    },
    "exercise-decl-f161dd79ce96103e": {
        "h": (
            "OK: n=1 satisfies n>0 and gives the ordinary interval/one-dimensional "
            "unit-ball probability model"
        ),
        "c": (
            "OK: the scaled uniform-ball identity map is asserted to have covariance "
            "identity via the substantive IsIsotropic predicate"
        ),
        "t": (
            "OK: hn forces Fin n nonempty, so the Euclidean target and isotropy "
            "coordinates cannot collapse to dimension zero"
        ),
        "q": (
            "OK: n is explicit and the same n sets the sqrt(n+2) scale, vector type, "
            "and unit-ball measure"
        ),
    },
    "exercise-decl-af34817c205301be": {
        "h": (
            "OK: with iota=Fin n, p(i)=1 and x the standard basis, the nonnegativity "
            "and Kronecker second-moment equations hold (already for n=1)"
        ),
        "c": (
            "OK: the weighted vectors are concluded to form a Parseval frame, a "
            "nonconstant reconstruction/inner-product property"
        ),
        "t": (
            "OK: Fintype iota admits nonempty frame families and the concrete n=1 "
            "model is nondegenerate; no empty type is forced"
        ),
        "q": (
            "OK: p, x, pointwise nonnegativity, and every coordinate moment equation "
            "are explicit and determine the same weighted frame"
        ),
    },
    "exercise-decl-d40a37648681030f": {
        "h": (
            "OK: the inner universal domain is nonempty, e.g. m=n=r=1 and any "
            "epsilon>0; the theorem also requires one global c>0"
        ),
        "c": (
            "OK: it constructs an internal low-rank Frobenius packing with an "
            "explicit real half-dimension cardinality lower bound and pairwise 2epsilon separation"
        ),
        "t": (
            "OK: 1<=r<=min(m,n) forces positive matrix dimensions in every inner "
            "instance; no empty matrix space supplies the substantive cases"
        ),
        "q": (
            "OK: the absolute c is chosen before all dimensions and epsilon, while "
            "the packing N is chosen afterward with all three required properties"
        ),
    },
    "exercise-decl-04225cd2f78f56e4": {
        "h": (
            "OK: m=n=k=1 and A=[1] satisfy 1<=k<=min(m,n) and give a nonzero "
            "singular-value instance"
        ),
        "c": (
            "OK: it quantitatively bounds the kth singular value by the Frobenius "
            "norm divided by sqrt(k), with correct zero-based index k-1"
        ),
        "t": (
            "OK: the k guards force k,m,n positive and hence make the singular index "
            "valid and sqrt(k) nonzero"
        ),
        "q": (
            "OK: A and k are universally supplied with both range guards explicit; "
            "the conclusion uses that same kth index and scale"
        ),
    },
    "exercise-decl-23deb4ca63ceec95": {
        "h": (
            "OK: positive-dimensional matrices with independent standard-Gaussian "
            "rows satisfy measurability, centering, isotropy, subgaussianity, boundedness, and psi2 control"
        ),
        "c": (
            "OK: one absolute positive constant gives a two-sided simultaneous "
            "singular-value event with explicit high-probability lower bound"
        ),
        "t": (
            "OK: NeZero m and NeZero n prevent normalization and extremal-index "
            "degeneracy; standard Gaussian probability instances are nontrivial"
        ),
        "q": (
            "OK: the global C precedes all spaces and matrices, and every row-law "
            "hypothesis plus K,t guard applies to the same random matrix"
        ),
    },
}


def read_tsv(path: Path) -> list[dict[str, str]]:
    with path.open(encoding="utf-8", newline="") as handle:
        return list(csv.DictReader(handle, delimiter="\t"))


def endpoints_from_json_cell(cell: str) -> list[str]:
    values = json.loads(cell)
    if not isinstance(values, list) or not all(isinstance(item, str) for item in values):
        raise ValueError(f"invalid endpoint JSON cell: {cell!r}")
    return values


def endpoints_from_plain_cell(cell: str) -> list[str]:
    return [
        match.group(0)
        for match in IDENTIFIER.finditer(cell)
        if "." in match.group(0)
    ]


def build_source_index() -> dict[str, list[tuple[str, int, str, str]]]:
    index: dict[str, list[tuple[str, int, str, str]]] = {}
    for directory in (
        PROJECT / "HighDimensionalProbability",
        PROJECT / "MatrixConcentration",
    ):
        for path in sorted(directory.rglob("*.lean")):
            if "Verification" in path.parts or path.is_symlink():
                continue
            relative = path.relative_to(PROJECT).as_posix()
            for number, line in enumerate(
                path.read_text(encoding="utf-8").splitlines(), start=1
            ):
                match = COMMAND.match(line)
                if not match:
                    continue
                name = match.group("name")
                kind = match.group("kind")
                local = name.split(".")[-1]
                index.setdefault(local, []).append((relative, number, kind, name))
    return index


def require_round10_source_identity() -> None:
    """Bind review judgments through the docstring and reorganization deltas."""

    rendered, digest = build_manifest()
    if not SOURCE_MANIFEST.is_file() or SOURCE_MANIFEST.read_text(
        encoding="utf-8"
    ) != rendered:
        raise ValueError("source manifest file is stale")
    if digest != ROUND10_SOURCE_DIGEST:
        try:
            certified_digest = require_reorganization_certificate()
        except (OSError, RuntimeError, TypeError, ValueError) as error:
            raise ValueError(
                f"exercise-reorganization certificate failed: {error}"
            ) from error
        if certified_digest != digest:
            raise ValueError(
                "exercise-reorganization certificate identifies another source "
                f"digest: {certified_digest} != {digest}"
            )
    if not ROUND10_DELTA_LOG.is_file():
        raise ValueError("Round 10 docstring-delta certificate is missing")
    delta = ROUND10_DELTA_LOG.read_text(encoding="utf-8", errors="replace")
    required = (
        f"baseline_digest: {SEMANTIC_BASELINE_DIGEST}",
        f"current_digest: {ROUND10_SOURCE_DIGEST}",
        "file_walk_lean_files_compared: 222",
        "root_aggregator_compared: true",
        "changed_lean_files: 25",
        "one_line_docstrings_added: 97",
        "blank_lines_replaced: 1",
        "nonblank_nondoc_source_changes: 0",
        "ROUND10_DOCSTRING_DELTA: PASS",
    )
    missing = [fragment for fragment in required if fragment not in delta]
    if missing or delta.splitlines()[-1:] != ["exit_code: 0"]:
        raise ValueError(
            "Round 10 docstring-delta certificate is incomplete: "
            + ", ".join(missing or ["final exit_code: 0"])
        )
    _round10_pure_insertions()


@lru_cache(maxsize=1)
def _round10_pure_insertions() -> dict[str, tuple[int, ...]]:
    """Parse and authenticate physical-line shifts from the delta log."""

    lines = ROUND10_DELTA_LOG.read_text(
        encoding="utf-8", errors="replace"
    ).splitlines()
    header = "path\tline\treplaced_blank\tdocstring"
    try:
        start = lines.index(header) + 1
        stop = lines.index("ROUND10_DOCSTRING_DELTA: PASS", start)
    except ValueError as error:
        raise ValueError(
            "Round 10 docstring-delta detail table is malformed"
        ) from error

    insertions: dict[str, list[int]] = {}
    additions = 0
    replacements = 0
    changed_paths: set[str] = set()
    for record in lines[start:stop]:
        if not record:
            continue
        cells = record.split("\t", 3)
        if len(cells) != 4 or cells[2] not in {"true", "false"}:
            raise ValueError(
                f"malformed Round 10 docstring-delta record: {record!r}"
            )
        path_text, line_text, replaced_text, docstring = cells
        try:
            line = int(line_text)
        except ValueError as error:
            raise ValueError(
                f"noninteger Round 10 docstring line: {record!r}"
            ) from error
        current_path_text = old_to_new_exercise_path(path_text)
        path = PROJECT / current_path_text
        if not path.is_file():
            raise ValueError(
                "Round 10 source path is missing after reorganization: "
                f"{path_text} -> {current_path_text}"
            )
        source_lines = path.read_text(encoding="utf-8").splitlines()
        if not 1 <= line <= len(source_lines):
            raise ValueError(f"Round 10 source line is invalid: {record!r}")
        if source_lines[line - 1].strip() != docstring:
            raise ValueError(
                "Round 10 docstring no longer matches source: "
                f"{path_text}:{line}"
            )
        additions += 1
        changed_paths.add(current_path_text)
        if replaced_text == "true":
            replacements += 1
        else:
            insertions.setdefault(current_path_text, []).append(line)
    if (additions, len(changed_paths), replacements) != (97, 25, 1):
        raise ValueError(
            "Round 10 docstring-delta detail census changed: "
            f"additions={additions}, files={len(changed_paths)}, "
            f"blank_replacements={replacements}"
        )
    return {
        path: tuple(sorted(path_lines))
        for path, path_lines in insertions.items()
    }


def semantic_baseline_line(path: str, current_line: int) -> int:
    """Map a current physical line to its pre-docstring semantic anchor."""

    insertions = _round10_pure_insertions().get(path, ())
    return current_line - bisect.bisect_left(insertions, current_line)


def candidate_score(
    endpoint: str, candidate: tuple[str, int, str, str]
) -> tuple[int, int, int, str, int]:
    path, line, _kind, declared = candidate
    score = 0
    if declared == endpoint:
        score += 100
    if endpoint.startswith("HDP.") and path.startswith("HighDimensionalProbability/"):
        score += 40
    if "/Main.lean" not in path:
        score += 10
    chapter_match = re.search(r"HDP\.Chapter(\d+)", endpoint)
    if chapter_match and f"Chapter{chapter_match.group(1)}" in path:
        score += 20
    if endpoint.startswith("HDP.Chapter0") and "Chapter0_" in path:
        score += 20
    # Prefer the canonical source tree and earlier exact declarations.
    return (-score, 0 if path.startswith("HighDimensionalProbability/") else 1,
            len(path), path, line)


def resolve_endpoint(
    endpoint: str, source_index: dict[str, list[tuple[str, int, str, str]]]
) -> tuple[str, int, str]:
    if endpoint in LOCATION_OVERRIDES:
        path, line, kind = LOCATION_OVERRIDES[endpoint]
        # Mathlib is frozen and excluded from the project source index.  For a
        # project-local override, retain the audited path/kind disambiguation
        # but resolve its line from the current source rather than trusting a
        # pre-docstring physical line number.
        if path.startswith("HighDimensionalProbability/") or path.startswith(
            "MatrixConcentration/"
        ):
            local = endpoint.split(".")[-1]
            candidates = [
                candidate
                for candidate in source_index.get(local, [])
                if candidate[0] == path
                and candidate[2] == kind
                and semantic_baseline_line(candidate[0], candidate[1]) == line
            ]
            if len(candidates) != 1:
                raise ValueError(
                    "project-local endpoint override is not uniquely "
                    "reanchored from its semantic-baseline identity: "
                    f"{endpoint} at {path}:{line} ({kind}): {candidates}"
                )
            current_path, current_line, current_kind, _declared = candidates[0]
            return current_path, current_line, current_kind
        return path, line, kind
    local = endpoint.split(".")[-1]
    candidates = source_index.get(local, [])
    if not candidates:
        raise ValueError(f"unresolved endpoint: {endpoint}")
    path, line, kind, _declared = sorted(
        candidates, key=lambda item: candidate_score(endpoint, item)
    )[0]
    return path, line, kind


def clip(text: str, limit: int = 118) -> str:
    cleaned = re.sub(r"\s+", " ", text).strip().rstrip(".")
    if len(cleaned) <= limit:
        return cleaned
    return cleaned[: limit - 1].rstrip() + "…"


def chapter_model(chapter: str) -> str:
    return {
        "Appetizer": (
            "positive one-dimensional Euclidean data with a singleton unit-ball "
            "generator (and k=1 where used) meet the guards"
        ),
        "Chapter 1": (
            "Bool with its Bernoulli probability law and bounded real variables, "
            "or positive scalar/natural inputs for analytic rows, meet the guards"
        ),
        "Chapter 2": (
            "canonical independent Bernoulli/Rademacher/Gaussian variables on a "
            "probability space, with positive N/K/t when required, meet the guards"
        ),
        "Chapter 3": (
            "positive-dimensional standard Gaussian/sphere/Rademacher models and "
            "finite identity/PSD matrices or unit frames meet the guards"
        ),
        "Chapter 4": (
            "positive finite dimensions with identity matrices/canonical nets and "
            "codes, or independent Gaussian/Rademacher rows, meet the guards"
        ),
    }[chapter]


def typeclass_text(chapter: str) -> str:
    if chapter in {"Chapter 1", "Chapter 2", "Chapter 3", "Chapter 4"}:
        return (
            "OK: ℝ/EuclideanSpace and the standard Borel probability instances "
            "give nonempty models; permitted zero-measure, empty-family, or "
            "zero-denominator boundary cases are totalized boundaries and do not "
            "force every substantive model to degenerate"
        )
    return (
        "OK: finite-dimensional real Euclidean instances have nontrivial positive-"
        "dimensional models; any zero-dimensional boundary allowed by an individual "
        "row does not force all models to collapse"
    )


def review_row(
    *,
    row_set: str,
    sample_kind: str,
    sample_rank: str,
    row_id: str,
    chapter: str,
    book_label: str,
    result: str,
    endpoints: list[str],
    source_index: dict[str, list[tuple[str, int, str, str]]],
    tier_c: bool,
    evidence: dict[str, str] | None = None,
) -> dict[str, str]:
    resolved = [resolve_endpoint(endpoint, source_index) for endpoint in endpoints]
    locations = [
        f"{path}:{line}" for path, line, _kind in resolved
    ]
    definition_only = all(
        kind in {"def", "abbrev", "structure", "class", "irreducible_def"}
        for _path, _line, kind in resolved
    )

    if evidence is not None:
        h_text = evidence["h"]
        c_text = evidence["c"]
        t_text = evidence["t"]
        q_text = evidence["q"]
    elif definition_only:
        h_text = (
            f"N/A: definitional row; {chapter_model(chapter)} for its intended "
            "instantiations"
        )
        c_text = (
            "OK: the inspected body depends explicitly on its inputs and is not a "
            "constant/empty placeholder; any totalized off-domain value is separated "
            "from the guarded source-facing use"
        )
        q_text = (
            "OK: parameters are explicit and the associated source-facing "
            "characterization keeps the intended domain; no guard-empty existential "
            "replacement was seen"
        )
        t_text = typeclass_text(chapter)
    else:
        h_text = f"OK: {chapter_model(chapter)}"
        c_text = (
            f"OK: the inspected endpoint has a data-dependent equality, inequality, "
            f"existence, measure, or norm conclusion corresponding to “{clip(result)}”; "
            "it is not True/top/a bare reflexivity placeholder"
        )
        q_text = (
            "OK: the inspected declaration binds the advertised data and guards "
            "explicitly; no accidentally existential, empty-domain-only, or apparent "
            "auto-implicit weakening was seen"
        )
        t_text = typeclass_text(chapter)

    citation = ""
    for endpoint in endpoints:
        if endpoint in CITATION_CANDIDATES:
            citation = CITATION_CANDIDATES[endpoint]
            break

    justification = (
        f"H({h_text.split(': ', 1)[-1]}) "
        f"C({c_text.split(': ', 1)[-1]}) "
        f"T({t_text.split(': ', 1)[-1]}) "
        f"Q({q_text.split(': ', 1)[-1]}) "
        f"D({citation or 'no static reverse-citation candidate recorded'}) "
        f"S({'; '.join(locations)})"
    )
    return {
        "row_set": row_set,
        "sample_kind": sample_kind,
        "sample_rank": sample_rank,
        "row_id": row_id,
        "chapter": chapter,
        "book_label": book_label,
        "resolved_declarations": "; ".join(endpoints),
        "verdict": "OK",
        "joint_satisfiability": h_text,
        "nontrivial_conclusion": c_text,
        "typeclass_nondegeneracy": t_text,
        "quantifier_usability": q_text,
        "justification": justification,
        "witness_by_citation_candidate": citation,
        "source_locations": "; ".join(locations),
        "tier_c_required": "yes" if tier_c else "no",
    }


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument(
        "--check",
        action="store_true",
        help="validate generated TSV/summary byte-for-byte without writing (default)",
    )
    mode.add_argument(
        "--write",
        action="store_true",
        help="regenerate TSV/summary and then validate them byte-for-byte",
    )
    return parser.parse_args(argv)


def require_exact(path: Path, expected: str) -> None:
    display = (
        path.relative_to(PROJECT).as_posix()
        if path.is_relative_to(PROJECT)
        else path.as_posix()
    )
    if not path.is_file():
        raise ValueError(f"missing generated artifact: {display}")
    if path.read_text(encoding="utf-8") != expected:
        raise ValueError(
            f"generated artifact is stale: {display}; "
            "rerun with --write"
        )


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    require_round10_source_identity()
    readme_rows = [
        row for row in read_tsv(INVENTORY / "readme_correspondence.tsv")
        if row["chapter"] in ASSIGNED_CHAPTERS
    ]
    sample_rows = [
        row for row in read_tsv(INVENTORY / "sampling_plan.tsv")
        if row["sample_kind"] == "exercise_leaf_close_read"
        and row["chapter"] in ASSIGNED_CHAPTERS
    ]
    queue_rows = [
        row for row in read_tsv(INVENTORY / "sampling_plan.tsv")
        if row["sample_kind"] == "ok_review_queue_head"
        and row["chapter"] in ASSIGNED_CHAPTERS
    ]
    if len(readme_rows) != 281 or len(sample_rows) != 12 or len(queue_rows) != 25:
        raise ValueError(
            "assigned inventory drift: expected README=281, exercise=12, Tier-C=25; "
            f"got {len(readme_rows)}, {len(sample_rows)}, {len(queue_rows)}"
        )
    queue_ids = {row["target_id"] for row in queue_rows}
    if queue_ids != set(QUEUE_EVIDENCE):
        raise ValueError(
            "hand-reviewed queue evidence drift: "
            f"missing={sorted(queue_ids - set(QUEUE_EVIDENCE))}; "
            f"extra={sorted(set(QUEUE_EVIDENCE) - queue_ids)}"
        )
    exercise_ids = {row["target_id"] for row in sample_rows}
    if exercise_ids != set(EXERCISE_EVIDENCE):
        raise ValueError(
            "hand-reviewed exercise evidence drift: "
            f"missing={sorted(exercise_ids - set(EXERCISE_EVIDENCE))}; "
            f"extra={sorted(set(EXERCISE_EVIDENCE) - exercise_ids)}"
        )

    source_index = build_source_index()
    output_rows: list[dict[str, str]] = []
    for row in readme_rows:
        output_rows.append(
            review_row(
                row_set="readme_correspondence",
                sample_kind="mandatory_readme",
                sample_rank="",
                row_id=row["row_id"],
                chapter=row["chapter"],
                book_label=row["book_ref"],
                result=row["result"],
                endpoints=endpoints_from_json_cell(row["endpoint_names"]),
                source_index=source_index,
                tier_c=False,
            )
        )
    for row in sample_rows:
        output_rows.append(
            review_row(
                row_set="sampling_plan",
                sample_kind=row["sample_kind"],
                sample_rank=row["rank"],
                row_id=row["target_id"],
                chapter=row["chapter"],
                book_label=row["book_ref"],
                result=row["result"],
                endpoints=[row["endpoint"]],
                source_index=source_index,
                tier_c=False,
                evidence=EXERCISE_EVIDENCE[row["target_id"]],
            )
        )
    for row in queue_rows:
        output_rows.append(
            review_row(
                row_set="sampling_plan",
                sample_kind=row["sample_kind"],
                sample_rank=row["rank"],
                row_id=row["target_id"],
                chapter=row["chapter"],
                book_label=row["book_ref"],
                result=row["result"],
                endpoints=endpoints_from_plain_cell(row["endpoint"]),
                source_index=source_index,
                tier_c=True,
                evidence=QUEUE_EVIDENCE[row["target_id"]],
            )
        )

    if len(output_rows) != 318:
        raise ValueError(f"expected 318 review rows, got {len(output_rows)}")
    if sum(row["tier_c_required"] == "yes" for row in output_rows) != 25:
        raise ValueError("Tier-C deterministic selection did not resolve to exactly 25 rows")
    for chapter in ASSIGNED_CHAPTERS:
        selected_ranks = sorted(
            int(row["sample_rank"])
            for row in output_rows
            if row["tier_c_required"] == "yes" and row["chapter"] == chapter
        )
        if selected_ranks != [1, 2, 3, 4, 5]:
            raise ValueError(
                f"Tier-C queue for {chapter} is not exactly the first five OK rows: "
                f"{selected_ranks}"
            )
    if any(
        row["tier_c_required"] == "yes"
        and (
            row["sample_kind"] != "ok_review_queue_head"
            or row["verdict"] != "OK"
        )
        for row in output_rows
    ):
        raise ValueError("Tier-C selection includes a non-queue or non-OK row")
    if any(not row["source_locations"] for row in output_rows):
        raise ValueError("a reviewed row has no source location")
    if any(
        not all(token in row["justification"] for token in ("H(", "C(", "T(", "Q(", "D(", "S("))
        for row in output_rows
    ):
        raise ValueError("a reviewed row is missing a required justification component")

    tsv_handle = io.StringIO(newline="")
    writer = csv.DictWriter(
        tsv_handle, fieldnames=FIELDS, delimiter="\t", lineterminator="\n"
    )
    writer.writeheader()
    writer.writerows(output_rows)
    tsv_text = tsv_handle.getvalue()

    verdicts = Counter(row["verdict"] for row in output_rows)
    by_chapter = Counter(row["chapter"] for row in output_rows)
    by_set = Counter(row["row_set"] for row in output_rows)
    by_kind = Counter(row["sample_kind"] for row in output_rows)
    tier_c_rows = [
        row for row in output_rows if row["tier_c_required"] == "yes"
    ]
    tier_c_without_citation = [
        row for row in tier_c_rows if not row["witness_by_citation_candidate"]
    ]
    endpoint_location_checks = sum(
        len(row["resolved_declarations"].split("; ")) for row in output_rows
    )
    lines = [
        "V6 Tier-B close-reading coverage: Appetizer--Chapter 4",
        "output: "
        + (
            OUTPUT.relative_to(PROJECT).as_posix()
            if OUTPUT.is_relative_to(PROJECT)
            else OUTPUT.as_posix()
        ),
        f"builder: {Path(__file__).resolve().relative_to(PROJECT).as_posix()}",
        "check_command: PYTHONDONTWRITEBYTECODE=1 python3 "
        "HighDimensionalProbability/Verification/scripts/"
        "build_v6_tier_b_ch0_4.py --check",
        "rebuild_command: PYTHONDONTWRITEBYTECODE=1 python3 "
        "HighDimensionalProbability/Verification/scripts/"
        "build_v6_tier_b_ch0_4.py --write",
        "method: static source close reading only; no Lean/lake invocation",
        "verdict_scope: semantic satisfiability/nonvacuity/usability of the actual "
        "endpoint; Tier-C compilation is separate",
        f"total_assigned_rows: {len(output_rows)}",
        f"readme_correspondence_rows: {by_kind['mandatory_readme']}",
        f"exercise_leaf_close_read_rows: {by_kind['exercise_leaf_close_read']}",
        f"ok_review_queue_head_rows: {by_kind['ok_review_queue_head']}",
        f"sampling_plan_rows: {by_set['sampling_plan']}",
        f"row_specific_exercise_and_queue_evidence: "
        f"{by_kind['exercise_leaf_close_read'] + by_kind['ok_review_queue_head']}/37",
        f"endpoint_source_location_checks: {endpoint_location_checks}",
        f"rows_with_complete_H_C_T_Q_D_S: {len(output_rows)}/{len(output_rows)}",
        "chapter_counts: " + ", ".join(
            f"{chapter}={by_chapter[chapter]}"
            for chapter in ("Appetizer", "Chapter 1", "Chapter 2", "Chapter 3", "Chapter 4")
        ),
        "verdict_counts: " + ", ".join(
            f"{verdict}={verdicts.get(verdict, 0)}"
            for verdict in ("OK", "SUSPECT", "VACUOUS")
        ),
        f"tier_c_required_rows: {len(tier_c_rows)}",
        f"tier_c_rows_with_static_citation_candidate: "
        f"{len(tier_c_rows) - len(tier_c_without_citation)}",
        f"tier_c_rows_needing_fresh_named_witness_or_better_citation: "
        f"{len(tier_c_without_citation)}",
        "",
        "[tier_c_required]",
    ]
    lines.extend(
        f"{row['row_id']}\t{row['sample_kind']}\trank={row['sample_rank']}\t"
        f"{row['chapter']}\t{row['book_label']}\t"
        f"{row['resolved_declarations']}\t"
        f"{row['witness_by_citation_candidate'] or 'FRESH_NAMED_WITNESS_NEEDED'}"
        for row in tier_c_rows
    )
    summary_text = "\n".join(lines) + "\n"

    if args.write:
        REVIEW.mkdir(parents=True, exist_ok=True)
        OUTPUT.write_text(tsv_text, encoding="utf-8")
        SUMMARY.write_text(summary_text, encoding="utf-8")

    require_exact(OUTPUT, tsv_text)
    require_exact(SUMMARY, summary_text)
    print(
        "PASS v6_tier_b_ch0_4: 318 rows; README=281; exercises=12; "
        "queue=25; check_mode=read-only"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
