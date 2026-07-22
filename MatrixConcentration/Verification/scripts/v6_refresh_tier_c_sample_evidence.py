#!/usr/bin/env python3
"""Refresh the curated Tier-C ledger for the corrected-snapshot sample.

The source-manifest digest is V6's deterministic sampling seed.  When a
record-only correction changes that digest, some of the 40 sampled OK rows can
change even though the 467 Tier-B judgments do not.  This migration preserves
all still-required evidence rows and all 34 boundary rows, removes only
superseded sampled-OK rows, and inserts the explicit evidence choices below.

Nothing here invents a verdict or chooses a citation heuristically: every new
row has a manually reviewed endpoint-to-evidence mapping.  The script verifies
that library sites really contain the endpoint use and that named applications
are declarations in the compiled V6 witness module before writing.
"""

from __future__ import annotations

import argparse
import csv
import re
import sys
from pathlib import Path

from v6_init_tier_c_evidence import FIELDS


SCRIPT = Path(__file__).resolve()
VERIFICATION = SCRIPT.parent.parent
PACKAGE_ROOT = VERIFICATION.parent
LOGS = VERIFICATION / "logs"
CURATION = VERIFICATION / "curation"
MANIFEST = CURATION / "v6_tier_c_evidence.tsv"
SAMPLE = LOGS / "v6_tier_c_sample.tsv"
TIER_B = LOGS / "v6_tier_b_review.tsv"
WITNESSES = VERIFICATION / "scripts" / "witnesses" / "V6Witnesses.lean"


# Each library mapping is a human-selected, direct theorem dependency already
# measured in logs/v6_endpoint_citations.tsv.  The site is independently
# checked below against the current source.
LIBRARY: dict[str, tuple[str, str]] = {
    "covarianceMatrix_apply": (
        "MatrixConcentration.covarianceMatrix_eq_sum_single",
        "MatrixConcentration/Chapter1_Introduction.lean:769",
    ),
    "norm_covarianceMatrix_le": (
        "MatrixConcentration.sampleCov_summand_norm_le",
        "MatrixConcentration/Chapter1_Introduction.lean:924",
    ),
    "sampleCov_summand_centered": (
        "MatrixConcentration.sampleCovariance_expected_error",
        "MatrixConcentration/Chapter1_Introduction.lean:1303",
    ),
    "IsStdGaussian": (
        "MatrixConcentration.gauss_expect_sq_upper",
        "MatrixConcentration/Chapter4_MatrixGaussianAndRademacherSeries.lean:3240",
    ),
    "convex_posDef": (
        "MatrixConcentration.expectation_trace_exp_add_le'",
        "MatrixConcentration/Chapter4_MatrixGaussianAndRademacherSeries.lean:1394",
    ),
    "schattenOneNorm": (
        "MatrixConcentration.schattenOneNorm_eq_zero_iff",
        "MatrixConcentration/Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean:1664",
    ),
    "expectation_conjTranspose": (
        "MatrixConcentration.matrixVar2_sum",
        "MatrixConcentration/Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean:3893",
    ),
    "entrywiseL1Norm_le": (
        "MatrixConcentration.sparsification_relative_error",
        "MatrixConcentration/Chapter6_SumOfBoundedRandomMatrices.lean:4112",
    ),
    "master_tail_upper": (
        "MatrixConcentration.master_tail_upper_inf",
        "MatrixConcentration/Chapter3_MatrixLaplaceTransformMethod.lean:2285",
    ),
    "master_expectation_lower": (
        "MatrixConcentration.master_expectation_lower_sup",
        "MatrixConcentration/Chapter3_MatrixLaplaceTransformMethod.lean:2273",
    ),
    "wigner_variance": (
        "MatrixConcentration.wigner_expected_norm",
        "MatrixConcentration/Chapter4_MatrixGaussianAndRademacherSeries.lean:3679",
    ),
    "gaussian_matrix_mgf": (
        "MatrixConcentration.gaussian_matrix_cgf",
        "MatrixConcentration/Chapter4_MatrixGaussianAndRademacherSeries.lean:324",
    ),
    "rademacher_matrix_mgf": (
        "MatrixConcentration.rademacher_matrix_mgf_le",
        "MatrixConcentration/Chapter4_MatrixGaussianAndRademacherSeries.lean:386",
    ),
    "shiftPow": (
        "MatrixConcentration.shiftPow_apply",
        "MatrixConcentration/Chapter4_MatrixGaussianAndRademacherSeries.lean:4059",
    ),
    "sum_laplCoeff": (
        "MatrixConcentration.expectation_erY_eq",
        "MatrixConcentration/Chapter5_SumOfPSDMatrices.lean:4358",
    ),
    "expectation_matsum_eq": (
        "MatrixConcentration.chernoff_mu_max_eq",
        "MatrixConcentration/Chapter5_SumOfPSDMatrices.lean:814",
    ),
    "chernoff_cgf_trace_bound_lower": (
        "MatrixConcentration.matrix_chernoff_expectation_lower",
        "MatrixConcentration/Chapter5_SumOfPSDMatrices.lean:634",
    ),
    "chernoff_matrix_cgf_le": (
        "MatrixConcentration.chernoff_cgf_trace_bound_lower",
        "MatrixConcentration/Chapter5_SumOfPSDMatrices.lean:461",
    ),
    "matrix_bernstein_herm_expectation_one_sided_ae": (
        "MatrixConcentration.matrix_bernstein_herm_min_expectation_one_sided_ae",
        "MatrixConcentration/Chapter6_SumOfBoundedRandomMatrices.lean:6425",
    ),
    "psiOne": (
        "MatrixConcentration.psiOne_nonneg",
        "MatrixConcentration/Chapter7_IntrinsicDimension.lean:598",
    ),
    "psiOne_nonneg": (
        "MatrixConcentration.convexOn_psiOne",
        "MatrixConcentration/Chapter7_IntrinsicDimension.lean:649",
    ),
    "bernstein_expected_trace_bound_one_sided": (
        "MatrixConcentration.intdim_bernstein_herm_tail_core_one_sided",
        "MatrixConcentration/Chapter7_IntrinsicDimension.lean:5088",
    ),
    "mre_nonneg": (
        "MatrixConcentration.trace_variational_isGreatest",
        "MatrixConcentration/Chapter8_ProofOfLiebsTheorem.lean:4049",
    ),
    "perspective_entropy_eq": (
        "MatrixConcentration.vre_convexOn",
        "MatrixConcentration/Chapter8_ProofOfLiebsTheorem.lean:230",
    ),
    "sortedEig": (
        "MatrixConcentration.sortedEig_antitone",
        "MatrixConcentration/Chapter8_ProofOfLiebsTheorem.lean:4245",
    ),
    "l2_opNorm_vecMulVec_star_self": (
        "MatrixConcentration.l2_opNorm_replicateCol",
        "MatrixConcentration/Prelude.lean:277",
    ),
    "sampleCov_decomposition": (
        "MatrixConcentration.sampleCovariance_expected_error",
        "MatrixConcentration/Chapter1_Introduction.lean:1318",
    ),
    "schattenOneNorm_reindex": (
        "MatrixConcentration.schattenOneNorm_add_le",
        "MatrixConcentration/Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean:2007",
    ),
    "varStatHerm_sum": (
        "MatrixConcentration.varStatHerm_sum_le",
        "MatrixConcentration/Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean:3492",
    ),
    "master_expectation_upper": (
        "MatrixConcentration.master_expectation_upper_inf",
        "MatrixConcentration/Chapter3_MatrixLaplaceTransformMethod.lean:2261",
    ),
    "gaussianRect_coeff_sum_left": (
        "MatrixConcentration.gaussianRect_variance",
        "MatrixConcentration/Chapter4_MatrixGaussianAndRademacherSeries.lean:3734",
    ),
    "expectation_column_gram": (
        "MatrixConcentration.column_submatrix_upper",
        "MatrixConcentration/Chapter5_SumOfPSDMatrices.lean:1979",
    ),
    "entryDiag": (
        "MatrixConcentration.entryDiag_family_bounds",
        "MatrixConcentration/Chapter5_SumOfPSDMatrices.lean:2640",
    ),
    "posSemidef_lapMatrixC": (
        "MatrixConcentration.connected_iff_secondSmallest_pos",
        "MatrixConcentration/Chapter5_SumOfPSDMatrices.lean:3760",
    ),
    "laplCoeff": (
        "MatrixConcentration.laplCoeff_apply",
        "MatrixConcentration/Chapter5_SumOfPSDMatrices.lean:4008",
    ),
    "featureVector": (
        "MatrixConcentration.kernelMatrix_eq_expectation_outer",
        "MatrixConcentration/Chapter6_SumOfBoundedRandomMatrices.lean:4982",
    ),
    "random_feature_error_bound": (
        "MatrixConcentration.random_feature_error_bound_of_abs_le",
        "MatrixConcentration/Chapter6_SumOfBoundedRandomMatrices.lean:5220",
    ),
    "bernstein_matrix_cgf_le_one_sided": (
        "MatrixConcentration.bernstein_cgf_trace_bound_one_sided",
        "MatrixConcentration/Chapter6_SumOfBoundedRandomMatrices.lean:5791",
    ),
    "exp_le_one_add_bernstein_quadratic": (
        "MatrixConcentration.bernstein_matrix_mgf_le",
        "MatrixConcentration/Chapter6_SumOfBoundedRandomMatrices.lean:659",
    ),
    "one_le_intdim": (
        "MatrixConcentration.intdim_chernoff_expectation",
        "MatrixConcentration/Chapter7_IntrinsicDimension.lean:1504",
    ),
    "exp_kronecker_one": (
        "MatrixConcentration.log_kronecker",
        "MatrixConcentration/Chapter8_ProofOfLiebsTheorem.lean:3531",
    ),
    "expectation_sum_mul_conjTranspose_of_centered": (
        "MatrixConcentration.matrixVar1_sum",
        "MatrixConcentration/Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean:3879",
    ),
    "matrix_bernstein_expectation": (
        "MatrixConcentration.sampleCovariance_expected_error",
        "MatrixConcentration/Chapter1_Introduction.lean:1307",
    ),
    "posSemidef_covarianceMatrix": (
        "MatrixConcentration.sampleCov_summand_sq_le",
        "MatrixConcentration/Chapter1_Introduction.lean:1068",
    ),
    "frobeniusNorm": (
        "MatrixConcentration.trace_mul_conjTranspose_self",
        "MatrixConcentration/Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean:110",
    ),
    "l2_opNorm_replicateCol": (
        "MatrixConcentration.l2_opNorm_replicateRow",
        "MatrixConcentration/Prelude.lean:289",
    ),
    "hermDilation": (
        "MatrixConcentration.matrix_bernstein_rect_tail",
        "MatrixConcentration/Chapter6_SumOfBoundedRandomMatrices.lean:1927",
    ),
    "entrywiseL1Norm": (
        "MatrixConcentration.sparsification_error_bound",
        "MatrixConcentration/Chapter6_SumOfBoundedRandomMatrices.lean:4005",
    ),
    "exp_lambdaMax_le_trace_exp": (
        "MatrixConcentration.matrix_laplace_tail_upper",
        "MatrixConcentration/Chapter3_MatrixLaplaceTransformMethod.lean:862",
    ),
    "trace_exp_sum_le_trace_exp_sum_cgf": (
        "MatrixConcentration.bernstein_trace_mgf_bound",
        "MatrixConcentration/Chapter7_IntrinsicDimension.lean:1918",
    ),
    "concaveOn_posDef_expectation_le": (
        "MatrixConcentration.expectation_trace_exp_add_le",
        "MatrixConcentration/Chapter3_MatrixLaplaceTransformMethod.lean:1638",
    ),
    "gaussianRect_variance": (
        "MatrixConcentration.gaussianRect_expected_norm",
        "MatrixConcentration/Chapter4_MatrixGaussianAndRademacherSeries.lean:3753",
    ),
    "signed_coeff_sum_right": (
        "MatrixConcentration.signed_variance",
        "MatrixConcentration/Chapter4_MatrixGaussianAndRademacherSeries.lean:3874",
    ),
    "l2_opNorm_colGram_le": (
        "MatrixConcentration.column_family_bounds",
        "MatrixConcentration/Chapter5_SumOfPSDMatrices.lean:1922",
    ),
    "lapMatrixC": (
        "MatrixConcentration.connected_iff_secondSmallest_pos",
        "MatrixConcentration/Chapter5_SumOfPSDMatrices.lean:3758",
    ),
    "one_add_le_exp_matrix": (
        "MatrixConcentration.chernoff_matrix_mgf_le",
        "MatrixConcentration/Chapter5_SumOfPSDMatrices.lean:318",
    ),
    "psiTwo": (
        "MatrixConcentration.convexOn_psiTwo",
        "MatrixConcentration/Chapter7_IntrinsicDimension.lean:670",
    ),
    "bernstein_threshold_sq": (
        "MatrixConcentration.intdim_bernstein_herm_tail",
        "MatrixConcentration/Chapter7_IntrinsicDimension.lean:2228",
    ),
    "intdim_smul_one": (
        "MatrixConcentration.intdim_eq_card_iff",
        "MatrixConcentration/Chapter7_IntrinsicDimension.lean:287",
    ),
    "trace_exp_eq_at_optimizer": (
        "MatrixConcentration.lieb_theorem",
        "MatrixConcentration/Chapter8_ProofOfLiebsTheorem.lean:4153",
    ),
    "one_le_inv_of_le_one": (
        "MatrixConcentration.inv_shift_loewner_anti",
        "MatrixConcentration/Chapter8_ProofOfLiebsTheorem.lean:1355",
    ),
    "exp_one_kronecker": (
        "MatrixConcentration.log_kronecker",
        "MatrixConcentration/Chapter8_ProofOfLiebsTheorem.lean:3532",
    ),
}


NAMED: dict[str, tuple[str, str, str]] = {
    "sampleCov_varStat_eq": (
        "sampled_sampleCov_varStat_eq",
        "No undischarged Prop premises. The closed theorem uses nn=1, P=2, "
        "and one bounded nonconstant feature vector (1, sign); measurability, "
        "squared-norm bounds, identical distribution, singleton independence, "
        "and squared-integrability are all discharged.",
        "The compiled endpoint application invokes sampleCov_varStat_eq on a "
        "bounded nonconstant sample whose outer product fluctuates.",
    ),
    "matrix_laplace_tail_upper_inf": (
        "sampled_matrix_laplace_tail_upper_inf",
        "No undischarged Prop premises. The closed theorem uses the bounded "
        "nonconstant singleton product-sign Hermitian matrix at threshold one; "
        "measurability, Hermiticity, and its norm bound are discharged.",
        "The compiled endpoint application invokes matrix_laplace_tail_upper_inf "
        "on a genuine finite upper-tail event and its inhabited positive-theta domain.",
    ),
    "matrix_laplace_expectation_lower_sup": (
        "sampled_matrix_laplace_expectation_lower_sup",
        "No undischarged Prop premises. The closed theorem uses the bounded "
        "nonconstant singleton product-sign Hermitian matrix; measurability, "
        "Hermiticity, and the pointwise norm bound are discharged.",
        "The compiled endpoint application invokes "
        "matrix_laplace_expectation_lower_sup on an inhabited negative-theta domain.",
    ),
    "gaussianRect_expected_norm": (
        "sampled_gaussianRect_expected_norm",
        "No undischarged Prop premises. The closed theorem uses product "
        "standard-Gaussian coordinates on Fin 2 x Fin 1; measurability, "
        "Gaussian laws, and independence are all discharged.",
        "The compiled endpoint application invokes gaussianRect_expected_norm "
        "on a genuine nonconstant two-by-one Gaussian column with positive "
        "variance scale and log 3.",
    ),
    "erAdjacency": (
        "sampled_erAdjacency_complete_three",
        "No undischarged Prop premises. The closed theorem evaluates the "
        "three-vertex all-edges adjacency construction as the off-diagonal "
        "all-ones matrix, which is nonzero.",
        "The compiled theorem directly unfolds erAdjacency on a concrete "
        "inhabited graph and identifies its nonzero matrix value.",
    ),
    "matrix_bernstein_uncentered_expectation": (
        "sampled_matrix_bernstein_uncentered_expectation",
        "No undischarged Prop premises. The closed theorem uses shifted "
        "Rademacher matrices S_k=I+epsilon_k I, whose expectation is the "
        "nonzero identity; measurability, affine independence, and the "
        "centered norm bound one are discharged.",
        "The compiled endpoint application invokes "
        "matrix_bernstein_uncentered_expectation and specifically exercises "
        "the nonzero-mean uncentered case.",
    ),
    "matrix_sampling_sample_cost_ae": (
        "sampled_matrix_sampling_sample_cost_ae",
        "No undischarged Prop premises. The closed theorem uses one nonconstant "
        "singleton Rademacher matrix sample with zero mean, positive sample "
        "count and accuracy, and "
        "discharges measurability, norm, mean, law, independence, and cost.",
        "The compiled endpoint application closes the full "
        "matrix_sampling_sample_cost_ae premise package on a fluctuating sample.",
    ),
    "IsPosDefKernel": (
        "sampled_IsPosDefKernel_linear",
        "No undischarged Prop premises. The closed theorem proves that the "
        "linear kernel Phi(a,b)=a*b is positive semidefinite for every finite "
        "observation family via a rank-one Gram representation.",
        "The compiled theorem applies IsPosDefKernel to a nonzero kernel with "
        "arbitrary finite sample size.",
    ),
    "min_intdim_le_intdim_fromBlocks": (
        "sampled_min_intdim_le_intdim_fromBlocks",
        "No undischarged Prop premises. The closed theorem applies the block "
        "intrinsic-dimension lower bound to nonzero identity matrices on Fin 2 "
        "and Fin 1.",
        "The compiled endpoint application uses nonzero positive-semidefinite "
        "blocks and an inhabited block sum.",
    ),
    "convexOn_psiTwo": (
        "sampled_convexOn_psiTwo_midpoint",
        "No undischarged Prop premises. The closed theorem applies global "
        "convexity to psiTwo at the nonzero parameter theta=1 and the distinct "
        "points zero and one with positive midpoint weights.",
        "The compiled endpoint application invokes convexOn_psiTwo and extracts "
        "a concrete nondegenerate midpoint inequality.",
    ),
    "l2_opNorm_replicateRow": (
        "sampled_l2_opNorm_replicateRow",
        "No undischarged Prop premises. The closed theorem applies "
        "l2_opNorm_replicateRow to the constant-one vector on Fin 1, "
        "producing a nonzero one-by-one row whose two norms equal one.",
        "The compiled closed theorem directly applies l2_opNorm_replicateRow "
        "on an inhabited finite dimension.",
    ),
    "schattenOneNorm_eq_zero_iff": (
        "sampled_schattenOneNorm_eq_zero_iff",
        "No undischarged Prop premises. The closed theorem applies "
        "schattenOneNorm_eq_zero_iff to the nonzero identity matrix in "
        "Matrix (Fin 1) (Fin 1) ℂ.",
        "The compiled closed theorem directly checks separation of the "
        "Schatten-one norm on a nontrivial finite matrix space.",
    ),
    "entrywiseL1AddGroupNorm": (
        "sampled_entrywiseL1AddGroupNorm_nonzero",
        "No undischarged Prop premises. The closed theorem evaluates "
        "entrywiseL1AddGroupNorm on the nonzero identity matrix in Matrix "
        "(Fin 1) (Fin 1) ℂ and proves its toFun value is nonzero.",
        "The compiled closed theorem directly references "
        "entrywiseL1AddGroupNorm on a nontrivial finite matrix space.",
    ),
    "matrixMgf_hasSum_moments": (
        "sampled_matrixMgf_hasSum_moments",
        "No undischarged Prop premises. The closed theorem uses hermSeries 0 "
        "under radMu with R=1 and θ=1; measurability, Hermiticity, and the "
        "pointwise bound are discharged, and its even moments are nonzero.",
        "The compiled closed theorem directly applies matrixMgf_hasSum_moments "
        "to the bounded nonconstant product-sign Hermitian model.",
    ),
    "master_tail_upper_inf": (
        "sampled_master_tail_upper_inf",
        "No undischarged Prop premises. The closed theorem uses the singleton "
        "product-sign Hermitian family with Rk=1 and t=1; measurability, "
        "Hermiticity, boundedness, and independence are all discharged.",
        "The compiled closed theorem directly applies master_tail_upper_inf "
        "to a nonconstant finite model whose t=1 upper-tail event is genuine.",
    ),
    "gauss_expect_sq_upper": (
        "sampled_gauss_expect_sq_upper",
        "No undischarged Prop premises. The closed theorem uses the finite "
        "product standard-Gaussian coordinates and nonzero identity matrix "
        "coefficients; measurability, Gaussian laws, and independence are "
        "all discharged.",
        "The compiled endpoint application instantiates gauss_expect_sq_upper "
        "on a nonconstant finite Gaussian matrix series.",
    ),
    "gauss_concentration": (
        "sampled_gauss_concentration",
        "No undischarged Prop premises. The closed theorem uses the same "
        "finite product Gaussian matrix series at t=1, with all law and "
        "independence premises discharged.",
        "The compiled endpoint application instantiates gauss_concentration "
        "at a positive deviation threshold on a nonconstant Gaussian model.",
    ),
    "coupon_collector_lower_instance": (
        "sampled_coupon_collector_lower_instance",
        "No undischarged Prop premises. The closed theorem uses n=ι=Fin 1, "
        "a constant identity-valued family, and θ=1; measurability, spectral "
        "bounds, identity expectation, independence, and positivity close.",
        "The compiled endpoint application closes the complete "
        "coupon_collector_lower_instance premise package on a nonzero model.",
    ),
    "intdim_column_submatrix_upper_totalized": (
        "sampled_intdim_column_submatrix_upper_totalized",
        "No undischarged Prop premises. The closed theorem uses m=n=Fin 1, "
        "B=I, q=1/2, bernMu, and bernCoords; interval, measurability, "
        "Bernoulli-law, and singleton-independence premises all close.",
        "The compiled endpoint application uses the nondegenerate B≠0 and "
        "q>0 branch of intdim_column_submatrix_upper_totalized.",
    ),
    "matrix_sampling_intdim_tail_ae": (
        "sampled_matrix_sampling_intdim_tail_ae",
        "No undischarged Prop premises. The closed theorem uses nn=1, "
        "constant identity samples, B=I, L=1, M₁=M₂=I, and a positive "
        "threshold; all norm, mean, PSD, moment, law, and independence "
        "premises close.",
        "The compiled endpoint application closes the full sampling premise "
        "package with nonzero moment matrices and positive sample count.",
    ),
    "vre_convexOn": (
        "sampled_vre_convexOn",
        "No undischarged Prop premises. The closed theorem uses n=Fin 1, "
        "a₁=1, a₂=3, h₁=2, h₂=1, and τ=1/2; all positivity and interval "
        "premises close on nonidentical input vectors.",
        "The compiled endpoint application evaluates vre_convexOn on "
        "positive unequal vectors at an interior convex weight.",
    ),
    "kronecker_mixed_product": (
        "sampled_kronecker_mixed_product",
        "No undischarged Prop premises. The closed theorem uses n=Fin 2 and "
        "four off-diagonal matrix units whose two products are nonzero.",
        "The compiled endpoint application directly invokes "
        "kronecker_mixed_product on nonidentity matrices.",
    ),
    "scalar_bernstein": (
        "sampled_scalar_bernstein",
        "No undischarged Prop premises. The closed theorem uses the singleton "
        "product-sign model with L=t=1 and discharges independence, "
        "measurability, centering, variance, and almost-sure boundedness.",
        "The compiled endpoint application invokes scalar_bernstein on a "
        "nonconstant Rademacher summand whose threshold event and variance "
        "term are both genuine.",
    ),
    "stableRank_le_rank": (
        "sampled_stableRank_le_rank",
        "No undischarged Prop premises. The closed theorem applies "
        "stableRank_le_rank to the nonzero identity matrix on Fin 2.",
        "The compiled endpoint application stays on the B ≠ 0 domain and "
        "compares stable rank and algebraic rank at the substantive value 2.",
    ),
    "master_expectation_lower_sup": (
        "sampled_master_expectation_lower_sup",
        "No undischarged Prop premises. The closed theorem uses the singleton "
        "product-sign Hermitian family with its measurable, Hermitian, "
        "bounded, and independent hypotheses discharged.",
        "The compiled endpoint application invokes master_expectation_lower_sup "
        "on a nonconstant matrix family and its inhabited negative-theta domain.",
    ),
    "maxqp_rounding_bound_one_of_isRademacher": (
        "sampled_maxqp_rounding_bound_one_of_isRademacher",
        "No undischarged Prop premises. The closed theorem uses singleton "
        "identity coefficients and the nonconstant product-sign law, with "
        "both Gram bounds and all law/independence premises discharged.",
        "The compiled endpoint application exercises the positive "
        "sqrt(2 log 2) rounding scale on a nonzero coefficient.",
    ),
    "rademacher_herm_min_expectation_of_isRademacher": (
        "sampled_rademacher_herm_min_expectation_of_isRademacher",
        "No undischarged Prop premises. The closed theorem uses a Rademacher "
        "multiple of diag(1,-1), with Hermiticity, law, and independence "
        "fully discharged.",
        "The compiled endpoint application has pointwise minimum eigenvalue "
        "-1 and therefore exercises the lower spectral edge nontrivially.",
    ),
    "conditional_column_bound_pointwise_of_isBernoulli": (
        "sampled_conditional_column_bound_pointwise_of_isBernoulli",
        "No undischarged Prop premises. The closed theorem uses a nonzero "
        "one-by-one matrix, a deterministic retained row, and a fair "
        "Bernoulli column selector with all law and independence premises closed.",
        "The compiled endpoint application has a positive conditional Gram "
        "term and a nonconstant column-selection expectation.",
    ),
    "variance_max_eq_of_hermitian": (
        "sampled_variance_max_eq_of_hermitian",
        "No undischarged Prop premises. The closed theorem uses a product-sign "
        "multiple of diag(1,2), with pointwise Hermiticity discharged.",
        "The compiled endpoint application compares the two nonzero "
        "second-moment Gram matrices diag(1,4).",
    ),
    "matrix_sampling_estimator_tail_ae": (
        "sampled_matrix_sampling_estimator_tail_ae",
        "No undischarged Prop premises. The closed theorem uses one "
        "nonconstant centered sign-matrix sample with positive norm bound "
        "and threshold; law and singleton independence are discharged.",
        "The compiled endpoint application invokes the almost-sure sampling "
        "tail bound on a genuine nonzero deviation model.",
    ),
    "trace_control_of_norm_le": (
        "sampled_trace_control_of_norm_le",
        "No undischarged Prop premises. The closed theorem uses A=I, B=0 "
        "and a normalized nonzero Schatten-one dual test matrix.",
        "The compiled endpoint application makes the trace error and "
        "operator-norm error positive and the bound sharp.",
    ),
    "random_feature_relative_error": (
        "sampled_random_feature_relative_error",
        "No undischarged Prop premises. The closed theorem uses a bounded "
        "nonconstant two-coordinate sign feature whose expected outer "
        "product is the identity, with one sampled feature and ε=4.",
        "The compiled endpoint application exercises a nonconstant feature "
        "matrix and a positive relative-error threshold.",
    ),
    "intdim_eq_one_iff_rank_eq_one": (
        "sampled_intdim_eq_one_iff_rank_eq_one",
        "No undischarged Prop premises. The closed theorem applies the "
        "equivalence to the positive identity matrix on Fin 1.",
        "The compiled endpoint application uses a nonzero rank-one PSD "
        "matrix, where both intrinsic dimension and rank equal one.",
    ),
    "chernoff_expected_trace_bound_ae": (
        "sampled_chernoff_expected_trace_bound_ae",
        "No undischarged Prop premises. The closed theorem uses the fair "
        "Bernoulli one-by-one Hermitian family, M=I, L=θ=1, and discharges "
        "all almost-sure spectral, law, and independence assumptions.",
        "The compiled endpoint application invokes the expected-trace "
        "Chernoff estimate on a nonconstant PSD selector.",
    ),
    "generalized_klein": (
        "sampled_generalized_klein",
        "No undischarged Prop premises. The closed theorem uses Fin 1, "
        "positive constant scalar functions, and two identity matrices with "
        "all spectral-set hypotheses discharged.",
        "The compiled endpoint application yields the positive trace "
        "inequality 0 ≤ 1 rather than an empty-index or zero-function case.",
    ),
}


def read(path: Path) -> tuple[list[str], list[dict[str, str]]]:
    with path.open(newline="", encoding="utf-8") as handle:
        reader = csv.DictReader(handle, delimiter="\t")
        return list(reader.fieldnames or []), list(reader)


def write(path: Path, rows: list[dict[str, str]]) -> None:
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(
            handle, fieldnames=FIELDS, delimiter="\t", lineterminator="\n"
        )
        writer.writeheader()
        writer.writerows(rows)


def named_site(name: str) -> str:
    pattern = re.compile(
        r"^\s*theorem\s+" + re.escape(name) + r"(?=$|[\s({:\[])"
    )
    hits = [
        line_number
        for line_number, line in enumerate(
            WITNESSES.read_text(encoding="utf-8").splitlines(), 1
        )
        if pattern.match(line)
    ]
    if len(hits) != 1:
        raise ValueError(
            f"named evidence {name}: expected one declaration, found {hits}"
        )
    return (
        "Verification/scripts/witnesses/V6Witnesses.lean:"
        f"{hits[0]}"
    )


def validate_library_site(
    declaration: str,
    caller: str,
    site: str,
) -> None:
    match = re.fullmatch(
        r"MatrixConcentration/(?P<path>[A-Za-z0-9_./-]+\.lean):"
        r"(?P<line>[0-9]+)",
        site,
    )
    if match is None:
        raise ValueError(f"{declaration}: malformed library site {site!r}")
    path = PACKAGE_ROOT / match.group("path")
    line = int(match.group("line"))
    source = path.read_text(encoding="utf-8").splitlines()
    if not (1 <= line <= len(source)):
        raise ValueError(f"{declaration}: site outside {path.name}")
    if declaration not in source[line - 1]:
        raise ValueError(
            f"{declaration}: site {site} does not contain the endpoint"
        )
    caller_short = caller.rsplit(".", 1)[-1]
    window = "\n".join(
        source[max(0, line - 80) : min(len(source), line + 2)]
    )
    if caller_short not in window:
        raise ValueError(
            f"{declaration}: site is not near caller {caller_short}"
        )


def make_new(
    tier_row: dict[str, str],
    obligation_kind: str,
) -> dict[str, str]:
    global_row = tier_row["global_row"]
    declaration = tier_row["declaration"]
    base = {
        "global_row": global_row,
        "chapter": tier_row["chapter"],
        "chapter_row": tier_row["chapter_row"],
        "declaration": tier_row["declaration"],
        "endpoint_kind": tier_row["endpoint_kind"],
        "tier_b_verdict": tier_row["verdict"],
        "obligation_kind": obligation_kind,
    }
    if declaration in NAMED:
        short, premises, detail = NAMED[declaration]
        full = f"MatrixConcentration.V6Witnesses.{short}"
        return {
            **base,
            "evidence_method": "NAMED_APPLICATION",
            "evidence_names": full,
            "premise_class": "CLOSED_BY_EVIDENCE",
            "substantive_premises": premises,
            "model_names": "",
            "discharge_detail": (
                detail
                + " The environment collector must confirm its direct "
                "endpoint dependency and allowed axiom set."
            ),
            "application_site": named_site(short),
        }
    caller, site = LIBRARY[declaration]
    validate_library_site(tier_row["declaration"], caller, site)
    return {
        **base,
        "evidence_method": "LIBRARY_CITATION",
        "evidence_names": caller,
        "premise_class": "CLOSED_BY_EVIDENCE",
        "substantive_premises": tier_row["check1_model"],
        "model_names": "",
        "discharge_detail": (
            f"At the recorded source line, compiled theorem {caller} "
            f"directly applies {tier_row['declaration']}. The environment "
            "collector independently confirms the direct type/value "
            "dependency and allowed axiom set. Tier-B's jointly satisfiable "
            f"model is: {tier_row['check1_model']}"
        ),
        "application_site": site,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    try:
        fields, current = read(MANIFEST)
        if fields != FIELDS:
            raise ValueError(f"manifest schema drift: {fields!r}")
        _, sample = read(SAMPLE)
        _, tier_b = read(TIER_B)
        tier_by_global = {row["global_row"]: row for row in tier_b}
        current_by_declaration = {row["declaration"]: row for row in current}
        if len(current_by_declaration) != len(current):
            raise ValueError("current manifest contains duplicate declarations")

        ordered: list[tuple[str, str]] = [
            (row["global_row"], "sampled_OK") for row in sample
        ]
        ordered.extend(
            (row["global_row"], f"TierB_{row['verdict']}")
            for row in tier_b
            if row["verdict"] in {"SUSPECT", "VACUOUS"}
        )
        expected = {
            tier_by_global[global_row]["declaration"]
            for global_row, _ in ordered
        }
        existing = set(current_by_declaration)
        missing = expected - existing
        extra = existing - expected
        reviewed = set(LIBRARY) | set(NAMED)

        sampled_expected = {
            tier_by_global[row["global_row"]]["declaration"] for row in sample
        }
        unmapped = sampled_expected - reviewed
        if unmapped:
            raise ValueError(
                "sample obligation set contains rows without a reviewed mapping: "
                f"{sorted(unmapped)}"
            )
        projected_total = len(current) - len(extra) + len(missing)
        if projected_total != 74:
            raise ValueError(
                "reseed would not restore the 74-row obligation set: "
                f"current={len(current)} missing={len(missing)} "
                f"extra={len(extra)} projected={projected_total}"
            )

        rows: list[dict[str, str]] = []
        for global_row, obligation_kind in ordered:
            tier_row = tier_by_global[global_row]
            declaration = tier_row["declaration"]
            if obligation_kind == "sampled_OK":
                row = make_new(tier_row, obligation_kind)
            elif declaration in current_by_declaration:
                row = dict(current_by_declaration[declaration])
            else:
                raise ValueError(
                    "boundary obligation is missing curated evidence: "
                    f"{declaration}"
                )
            immutable = {
                "global_row": global_row,
                "chapter": tier_row["chapter"],
                "chapter_row": tier_row["chapter_row"],
                "declaration": tier_row["declaration"],
                "endpoint_kind": tier_row["endpoint_kind"],
                "tier_b_verdict": tier_row["verdict"],
                "obligation_kind": obligation_kind,
            }
            row.update(immutable)
            rows.append(row)

        if (
            len(rows) != 74
            or len({row["global_row"] for row in rows}) != 74
            or len({row["declaration"] for row in rows}) != 74
        ):
            raise ValueError("refreshed Tier-C ledger is not exactly 74 rows")
        if rows == current:
            print("TIER-C SAMPLE EVIDENCE ALREADY AT FIXED POINT")
            return 0
        refreshed = sum(
            current_by_declaration.get(row["declaration"]) != row for row in rows
        )
        if args.write:
            write(MANIFEST, rows)
            print(
                "WROTE Tier-C evidence: "
                f"retained={len(rows) - len(missing)} "
                f"added={len(missing)} removed={len(extra)} "
                f"refreshed={refreshed} total={len(rows)}"
            )
        else:
            print(
                "DRY-RUN Tier-C evidence: "
                f"retained={len(rows) - len(missing)} "
                f"add={len(missing)} remove={len(extra)} "
                f"refresh={refreshed} total={len(rows)}"
            )
        return 0
    except (KeyError, OSError, ValueError) as error:
        print(f"ERROR: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
