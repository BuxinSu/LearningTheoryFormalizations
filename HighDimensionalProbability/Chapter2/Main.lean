/-
Copyright (c) 2026 Buxin Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Buxin Su
-/

import HighDimensionalProbability.Prelude.Orlicz
import HighDimensionalProbability.Chapter2_ConcentrationOfIndependentSums

/-!
# High-Dimensional Probability, Chapter 2

Core Chapter 2 aggregator. Exercises needed by core or later chapters are
promoted into these topic modules and identified in their docstrings; no core
module imports `Exercise`. The `Exercise.Main` aggregator and book-level
`Appendix` module are intentionally not imported here.
-/

/-!
## Source-facing namespace

The first Chapter 2 modules were originally exported directly from `HDP`.
Book-wide notions retain those public names, while these aliases place the
source-numbered results in `HDP.Chapter2` without breaking existing clients.
-/

namespace HDP.Chapter2

alias subgaussian_iii_to_i := HDP.subgaussian_iii_to_i
alias subgaussian_i_to_iii := HDP.subgaussian_i_to_iii
alias subgaussian_iii_to_ii := HDP.subgaussian_iii_to_ii
alias subgaussian_ii_to_iii := HDP.subgaussian_ii_to_iii
alias subgaussian_iii_to_iv := HDP.subgaussian_iii_to_iv
alias subgaussian_iv_to_i := HDP.subgaussian_iv_to_i
alias remark_2_6_3_iii := HDP.remark_2_6_3_iii
alias remark_2_6_3_i := HDP.remark_2_6_3_i
alias subGaussian_psi2MGF_bound := HDP.SubGaussian.psi2MGF_bound
alias subGaussian_tail_bound := HDP.SubGaussian.tail_bound
alias subGaussian_moment_bound := HDP.SubGaussian.moment_bound
alias subGaussian_mgf_bound := HDP.SubGaussian.mgf_bound
alias psi2Norm_le_of_tail_bound := HDP.psi2Norm_le_of_tail_bound
alias psi2Norm_le_of_moment_bound := HDP.psi2Norm_le_of_moment_bound
alias psi2Norm_le_of_mgf_bound := HDP.psi2Norm_le_of_mgf_bound

alias pythagorean_identity := HDP.pythagorean_identity
alias psi2Norm_sum_sq_le := HDP.psi2Norm_sum_sq_le
alias subgaussian_hoeffding := HDP.subgaussian_hoeffding
alias example_2_7_4 := HDP.example_2_7_4
alias khintchine := HDP.khintchine
alias psi2Norm_max_abs_le := HDP.psi2Norm_max_abs_le
alias psi2Norm_max_abs_le' := HDP.psi2Norm_max_abs_le'
alias psi2Norm_max_le := HDP.psi2Norm_max_le
alias expectation_max_le := HDP.expectation_max_le
alias centering_L2 := HDP.centering_L2
alias psi2Norm_centering := HDP.psi2Norm_centering

alias subExponential_sq_iff := HDP.subExponential_sq_iff
alias psi1Norm_sq := HDP.psi1Norm_sq
alias psi1Norm_mul_le := HDP.psi1Norm_mul_le
alias subexponential_i_to_iii := HDP.subexponential_i_to_iii
alias subexponential_iii_to_i := HDP.subexponential_iii_to_i
alias subexponential_iii_to_ii := HDP.subexponential_iii_to_ii
alias subexponential_ii_to_iii := HDP.subexponential_ii_to_iii
alias subexponential_iii_to_iv := HDP.subexponential_iii_to_iv
alias subexponential_iv_to_i := HDP.subexponential_iv_to_i
alias exponential_mgf_diverges := HDP.exponential_mgf_diverges
alias psi1Norm_centering := HDP.psi1Norm_centering
alias remark_2_8_8 := HDP.remark_2_8_8
alias subExponential_tail_bound := HDP.SubExponential.tail_bound
alias subExponential_mgf_bound := HDP.SubExponential.mgf_bound

alias bernstein_inequality := HDP.bernstein_inequality
alias bernstein_weighted := HDP.bernstein_weighted
alias remark_2_9_4 := HDP.remark_2_9_4

end HDP.Chapter2
