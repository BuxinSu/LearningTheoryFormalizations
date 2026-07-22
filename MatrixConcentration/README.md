# MatrixConcentration

This repository formalizes Joel A. Tropp’s [*An Introduction to Matrix Concentration Inequalities*](https://arxiv.org/abs/1501.01571v1), arXiv:1501.01571v1 [math.PR]. All equation, theorem, proposition, lemma, and definition numbers in this Lean library and in the correspondence table below refer directly to that version.

This Lean 4 project translates the monograph’s mathematical development into kernel-checked Mathlib declarations. It covers the matrix-analysis and probability foundations, the matrix Laplace-transform method, Gaussian and Rademacher series, Chernoff and Bernstein inequalities, intrinsic-dimension refinements, applications, and the proof of Lieb’s theorem. Supporting Appendix modules supply complete proofs for source results that the book states only by citation.

## Summary statistics

| Item | Value |
|---|---|
| arXiv source | Joel A. Tropp, *An Introduction to Matrix Concentration Inequalities*, [arXiv:1501.01571v1](https://arxiv.org/abs/1501.01571v1) |
| Lean / Mathlib version | `leanprover/lean4:v4.31.0`; Mathlib `v4.31.0` |
| Published modules | shared `Prelude`, 8 chapters, and 5 consolidated appendices (14 inner modules total) |
| Public `theorem` / `lemma` / `def` | 469 / 841 / 135 (**1,445 total**) |
| Book → Lean correspondence | **469 kernel-checked declaration counterparts** |
| Verified kernel status | Clean root build; no `sorry`, `admit`, `native_decide`, or custom axioms; `#print axioms` for every audited theorem/lemma endpoint returns exactly `propext`, `Classical.choice`, and `Quot.sound` |
| Verification | [V1–V10 reports and verification scripts](Verification/README.md); raw generated evidence is retained outside this curated GitHub copy |

```bibtex
@article{tropp2015introduction,
  title={An Introduction to Matrix Concentration Inequalities},
  author={Tropp, Joel A},
  journal={arXiv preprint arXiv:1501.01571},
  year={2015}
}
```

The correspondence table is generated from current declaration docstrings and a fresh comparison with the expanded arXiv-v1 TeX source. It lists direct Book counterparts; implementation helpers and recovered prerequisites are intentionally excluded.

## Build

The project is pinned to Lean/Mathlib `v4.31.0`. From the repository root:

```sh
~/.elan/bin/lake build
```

To check one module directly:

```sh
~/.elan/bin/lake env lean MatrixConcentration/Chapter4_MatrixGaussianAndRademacherSeries.lean
```

## Module layout

| Area | Final module | Main topics |
|---|---|---|
| Shared foundations | [`Prelude.lean`](Prelude.lean) | Matrix norms, Hermitian order, eigenvalues, singular values, matrix functions, measurability, expectation, and shared probability infrastructure |
| Chapter 1 | [`Chapter1_Introduction.lean`](Chapter1_Introduction.lean) | Covariance estimation, sample covariance matrices, and introductory scalar and matrix Bernstein inequalities |
| Chapter 2 | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | Matrix analysis, spectral calculus, Hermitian dilation, matrix expectation, variance, and variance statistics |
| Chapter 3 | [`Chapter3_MatrixLaplaceTransformMethod.lean`](Chapter3_MatrixLaplaceTransformMethod.lean) | Matrix moment-generating functions, cumulant bounds, the matrix Laplace-transform method, and master tail and expectation inequalities |
| Chapter 4 | [`Chapter4_MatrixGaussianAndRademacherSeries.lean`](Chapter4_MatrixGaussianAndRademacherSeries.lean) | Gaussian and Rademacher matrix series, noncommutative Khintchine bounds, rectangular series, and Gaussian concentration |
| Chapter 5 | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | Matrix Chernoff inequalities, sums of positive-semidefinite matrices, randomized matrix approximation, and graph applications |
| Chapter 6 | [`Chapter6_SumOfBoundedRandomMatrices.lean`](Chapter6_SumOfBoundedRandomMatrices.lean) | Matrix Bernstein inequalities, bounded random matrices, rectangular dilation arguments, and Rosenthal--Pinelis estimates |
| Chapter 7 | [`Chapter7_IntrinsicDimension.lean`](Chapter7_IntrinsicDimension.lean) | Intrinsic dimension, refined matrix concentration inequalities, covariance estimation, and low-rank approximation |
| Chapter 8 | [`Chapter8_ProofOfLiebsTheorem.lean`](Chapter8_ProofOfLiebsTheorem.lean) | Matrix concavity, Schur complements, tensor-product arguments, and the proof of Lieb's theorem |
| Cited-proof Appendix | [`Appendix_GoldenThompson.lean`](Appendix_GoldenThompson.lean), [`Appendix_GaussianConcentration.lean`](Appendix_GaussianConcentration.lean), [`Appendix_MatrixRosenthal.lean`](Appendix_MatrixRosenthal.lean), [`Appendix_SymmetricLowerBound.lean`](Appendix_SymmetricLowerBound.lean), [`Appendix_RosenthalPinelis.lean`](Appendix_RosenthalPinelis.lean) | Complete formal proofs of external results cited by the monograph, including Golden--Thompson, Gaussian concentration, matrix Rosenthal, symmetric-sum lower bounds, and Rosenthal--Pinelis inequalities |

## Correspondence legend

- `E`: explicit Book theorem, proposition, lemma, definition, equation, or independently stated display.
- `I`: implicit Book assertion or hidden well-definedness/codomain obligation.
- `M`: Mathlib correspondence for a Book object or fact.
- `S`: source-linked declaration whose docstring does not classify it more narrowly.
- `V`: proved variant of a Book display, with the changed hypothesis or constant stated explicitly.
- `thm`, `lem`, `def`, and `abbr` describe the Lean declaration kind.

## Appendix sources and proof pipeline

The Appendix formalizes the external ingredients that Tropp cites rather than proves. The public-module pipeline is:

| Result | External mathematical input | Lean formalization pipeline |
|---|---|---|
| Golden–Thompson, (3.3.3) | J. R. Lee's presentation of the Dyson word argument; the original inequalities of Golden and Thompson | Frobenius trace Cauchy–Schwarz → transition counting for words → Lie product formula → `golden_thompson_trace` |
| Gaussian concentration, (4.1.8) | Prékopa–Leindler / Gaussian infimum-convolution arguments of Bobkov–Ledoux, Maurey, Bobkov–Götze, and Talagrand; Borell–TIS/BLM for the target statement | one-dimensional Prékopa–Leindler → product Gaussian PL → sharp Lipschitz mgf and Chernoff bound → Hermitian dilation and law transfer |
| Matrix Rosenthal, (5.1.9) | CGT Appendix A and the noncommutative Khintchine literature of Buchholz; alternative accounts by Junge–Zheng, Mackey et al., and Tropp | independent-copy symmetrization → coordinate sign reflection → Rademacher expectation estimate → positive-semidefinite square-function bound; Lean obtains the stronger `8 log d` intermediate coefficient |
| Symmetric-sum lower bound, (6.1.7) | Ledoux–Talagrand §6.1 and de la Peña–Giné §1.1 | product-law sign reflection → averaging over all sign choices → the stronger constant-one inequality |
| Rosenthal–Pinelis, (6.1.6) | CGT Theorem A.1(2), whose exact-coefficient statement assumes symmetric self-adjoint summands | Schatten/Khintchine infrastructure → Hermitian dilation → an exact-coefficient distributionally symmetric theorem; independent ghost-copy symmetrization gives the centered theorem with coefficient losses `√2` and `2` |

## Book → Lean correspondence

This table contains **469 verified declaration counterparts**. Chapter counts are **21 / 136 / 35 / 55 / 71 / 64 / 63 / 24** for Chapters 1–8. Implementation helpers and recovered prerequisites remain omitted.

### Chapter 1

| Book source | Lean declaration | Final module | Role | Notes |
|---|---|---|---|---|
| (1.5.1) · p. 6 | `covarianceMatrix` | [`Chapter1_Introduction.lean`](Chapter1_Introduction.lean) | `I/def` | implicit/hidden source assertion |
| (1.5.2) · p. 6 | `sampleCovariance` | [`Chapter1_Introduction.lean`](Chapter1_Introduction.lean) | `I/def` | implicit/hidden source assertion |
| (1.6.4) · p. 8 | `expectation_sum_mul_conjTranspose_of_centered` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `I/thm` | implicit/hidden source assertion |
| (1.6.4) · p. 8 | `matrix_bernstein_variance_eq` | [`Chapter1_Introduction.lean`](Chapter1_Introduction.lean) | `I/thm` | implicit/hidden source assertion |
| (1.6.5) · p. 8 | `matrix_bernstein_tail` | [`Chapter1_Introduction.lean`](Chapter1_Introduction.lean) | `E/thm` | |
| (1.6.6) · p. 8 | `matrix_bernstein_expectation` | [`Chapter1_Introduction.lean`](Chapter1_Introduction.lean) | `E/thm` | |
| (1.6.3) · p. 9 | `l2_opNorm_vecMulVec_star_self` | [`Prelude.lean`](Prelude.lean) | `I/lem` | implicit/hidden source assertion |
| (1.6.3) · p. 9 | `norm_covarianceMatrix_le` | [`Chapter1_Introduction.lean`](Chapter1_Introduction.lean) | `S/thm` | — |
| (1.6.1), §2.8 | `scalar_bernstein` | [`Chapter1_Introduction.lean`](Chapter1_Introduction.lean) | `E/thm` | — |
| (1.5.1), p.6, TeX 795–802 | `covarianceMatrix_apply` | [`Chapter1_Introduction.lean`](Chapter1_Introduction.lean) | `E/lem` | verified explicit source counterpart |
| (1.5.1), p.6, TeX 795–800 | `covarianceMatrix_eq_sum_single` | [`Chapter1_Introduction.lean`](Chapter1_Introduction.lean) | `I/lem` | verified implicit/prose source assertion |
| (1.5.1), p.6, TeX 795–798 | `posSemidef_covarianceMatrix` | [`Chapter1_Introduction.lean`](Chapter1_Introduction.lean) | `I/thm` | verified implicit/prose source assertion |
| §1.5.1, unnumbered prose after (1.5.2), p.6, TeX 804–810 | `expectation_sampleCovariance` | [`Chapter1_Introduction.lean`](Chapter1_Introduction.lean) | `I/thm` | verified implicit/prose source assertion |
| §1.6.3, p.9, TeX 1091–1098 | `sampleCovSummand` | [`Chapter1_Introduction.lean`](Chapter1_Introduction.lean) | `I/def` | verified implicit/prose source assertion |
| §1.6.3, p.9, TeX 1091–1098 | `sampleCov_decomposition` | [`Chapter1_Introduction.lean`](Chapter1_Introduction.lean) | `I/lem` | verified implicit/prose source assertion |
| §1.6.3, p.9, TeX 1091–1098 | `sampleCov_summand_centered` | [`Chapter1_Introduction.lean`](Chapter1_Introduction.lean) | `I/lem` | verified implicit/prose source assertion |
| Theorem 1.6.1, p.7, TeX 877–891 | `bernstein_variance_identity` | [`Chapter1_Introduction.lean`](Chapter1_Introduction.lean) | `I/thm` | verified implicit/prose source assertion |
| §1.6.5, p.11, TeX 1433–1452 | `maxSummandSq` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `I/def` | verified implicit/prose source assertion |
| §1.6.3, p.9, TeX 1091–1098 | `sampleCov_indep_summands` | [`Chapter1_Introduction.lean`](Chapter1_Introduction.lean) | `I/lem` | verified implicit/prose source assertion |
| §1.6.3, pp.10–11, TeX 1143–1149 | `sampleCov_varStat_eq` | [`Chapter1_Introduction.lean`](Chapter1_Introduction.lean) | `I/thm` | verified implicit/prose source assertion |
| §1.6.3, p.11, TeX 1165–1174 | `norm_le_norm_of_loewner_le` | [`Prelude.lean`](Prelude.lean) | `I/thm` | verified implicit/prose source assertion |

### Chapter 2

| Book source | Lean declaration | Final module | Role | Notes |
|---|---|---|---|---|
| SRC:1810–1814 | `inner_toLp_eq_dotProduct` | [`Prelude.lean`](Prelude.lean) | `M/lem` | Mathlib correspondence |
| SRC:1815–1819 | `dotProduct_star_self_eq` | [`Prelude.lean`](Prelude.lean) | `I/lem` | implicit/hidden source assertion |
| SRC:1815–1819 | `l2norm_sq` | [`Prelude.lean`](Prelude.lean) | `M/lem` | Mathlib correspondence |
| SRC:1815–1819 | `l2norm` | [`Prelude.lean`](Prelude.lean) | `I/def` | implicit/hidden source assertion |
| TeX 7610–18, p. 85;SRC:1834–1838 | `frobeniusNorm_eq_norm` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `M/lem` | Mathlib correspondence |
| (2.1.2) · p. 18 | `frobeniusNorm` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `E/def` | — |
| SRC:1839–1854 | `frobeniusNorm_replicateCol` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `I/lem` | implicit/hidden source assertion |
| (2.1.3) · p. 19 | `spectral_decomposition` | [`Prelude.lean`](Prelude.lean) | `M/lem` | Mathlib correspondence |
| SRC:1895 | `eigenvalues_multiset_unique` | [`Prelude.lean`](Prelude.lean) | `I/thm` | implicit/hidden source assertion |
| (2.1.4) · p. 19 | `lambdaMax_smul_nonneg` | [`Prelude.lean`](Prelude.lean) | `E/lem` | — |
| (2.1.4) · p. 19 | `lambdaMin_smul_nonneg` | [`Prelude.lean`](Prelude.lean) | `E/lem` | — |
| SRC:1898 | `lambdaMax` | [`Prelude.lean`](Prelude.lean) | `I/def` | implicit/hidden source assertion |
| SRC:1898 | `lambdaMin` | [`Prelude.lean`](Prelude.lean) | `I/def` | implicit/hidden source assertion |
| SRC:1905–1909 | `lambdaMax_neg` | [`Prelude.lean`](Prelude.lean) | `I/lem` | implicit/hidden source assertion |
| (2.1.5) · p. 19 | `lambdaMin_neg` | [`Prelude.lean`](Prelude.lean) | `E/lem` | — |
| (2.1.7) · p. 20 | `trace_unitary_conj` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `E/thm` | — |
| SRC:1953 | `trace_eq_sum_eigenvalues_complex` | [`Prelude.lean`](Prelude.lean) | `I/thm` | implicit/hidden source assertion |
| SRC:1956–1960 | `trace_conjTranspose_mul_self` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `E/thm` | — |
| (2.1.8) · p. 20 | `trace_mul_conjTranspose_self` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `E/thm` | — |
| SRC:1981–1987 | `posSemidef_iff_exists_eigenvalues_nonneg` | [`Prelude.lean`](Prelude.lean) | `S/thm` | — |
| (2.1.9) · p. 20 | `posSemidef_iff_isHermitian_quadratic` | [`Prelude.lean`](Prelude.lean) | `M/thm` | Mathlib correspondence |
| (2.1.10) · p. 20 | `posDef_iff_exists_eigenvalues_pos` | [`Prelude.lean`](Prelude.lean) | `E/thm` | — |
| SRC:1998–1999; TeX 13928; p. 136 | `posDef_sq_of_det_ne_zero` | [`Prelude.lean`](Prelude.lean) | `I/thm` | implicit/hidden source assertion |
| SRC:1998–1999 | `posSemidef_sq` | [`Prelude.lean`](Prelude.lean) | `I/thm` | implicit/hidden source assertion |
| SRC:2012–2028 | `isClosed_posSemidef` | [`Prelude.lean`](Prelude.lean) | `S/thm` | — |
| SRC:2012–2028 | `posSemidef_smul_nonneg` | [`Prelude.lean`](Prelude.lean) | `S/thm` | — |
| SRC:2029–2031 | `posDef_stable_under_hermitian_perturbation` | [`Prelude.lean`](Prelude.lean) | `I/thm` | implicit/hidden source assertion |
| SRC:2040 | `posSemidef_diagonal_real_iff` | [`Prelude.lean`](Prelude.lean) | `S/thm` | — |
| SRC:2091–2102 | `conjugation_rule` | [`Prelude.lean`](Prelude.lean) | `E/thm` | — |
| (2.1.13) · p. 21 | `lambdaMax_le_trace_re_of_posSemidef` | [`Prelude.lean`](Prelude.lean) | `E/thm` | — |
| SRC:2129–2140 | `cfc_diagonal_real` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `E/thm` | — |
| SRC:2129–2140; TeX 12984–90; p. 127 | `cfc_eq_book_formula` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `M/thm` | Mathlib correspondence |
| SRC:2129–2140 | `cfc_unitary_diagonal` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `I/thm` | implicit/hidden source assertion |
| SRC:2142 | `cfc_pow_eq` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `M/thm` | Mathlib correspondence |
| SRC:2146–2153 | `eigenvalues_cfc_multiset` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `I/thm` | implicit/hidden source assertion |
| SRC:2146–2153 | `spectral_mapping` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `E/thm` | — |
| SRC:2161–2168 | `matrixFun_powerSeries` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `S/thm` | — |
| SRC:2178–2193 | `transfer_rule` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `E/thm` | — |
| (2.1.15) · p. 22 | `matrixExp_eq_cfc` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `M/thm` | Mathlib correspondence |
| SRC:2225–2226;§3.4, TeX 3267–3277, p. 35 | `posDef_exp` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `I/thm` | implicit/hidden source assertion |
| (2.1.16) · p. 22 | `trace_exp_monotone` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `E/thm` | — |
| SRC:2322–2328 | `log_eq_book_formula` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `M/thm` | Mathlib correspondence |
| (2.1.17) · p. 23 | `log_exp_eq` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `M/thm` | Mathlib correspondence |
| (2.1.18) · p. 23 | `log_monotone` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `E/thm` | — |
| (2.1.19) · p. 23 | `exists_svd` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `E/thm` | — |
| SRC:2370–2373 | `singularValues` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `S/def` | — |
| SRC:2370–2373 | `singularValues_sq_multiset_eq` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `S/thm` | — |
| SRC:2375–2383 | `svd_conjTranspose_mul` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `E/thm` | — |
| (2.1.20) · p. 23 | `svd_mul_conjTranspose` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `E/thm` | — |
| (2.1.21) · p. 23 | `frobenius_norm_sq_eq_sum_singularValues_sq` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `E/thm` | — |
| (2.1.22) · p. 24 | `l2_opNorm_eq_max_lambda` | [`Prelude.lean`](Prelude.lean) | `E/thm` | — |
| (2.1.23) · p. 24 | `l2_opNorm_eq_sup_singularValues` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `E/thm` | — |
| SRC:2407–2409 | `l2_opNorm_replicateCol` | [`Prelude.lean`](Prelude.lean) | `I/lem` | implicit/hidden source assertion |
| SRC:2407–2409 | `l2_opNorm_replicateRow` | [`Prelude.lean`](Prelude.lean) | `I/lem` | implicit/hidden source assertion |
| SRC:2407–2409 | `l2_opNorm_herm_consistency` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `I/thm` | implicit/hidden source assertion |
| (2.1.24) · p. 24 | `l2_opNorm_sq_eq` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `E/thm` | — |
| (2.1.24) · p. 24 | `l2_opNorm_sq_mul_conjTranspose_self` | [`Prelude.lean`](Prelude.lean) | `M/lem` | Mathlib correspondence |
| (2.1.25) · p. 24 | `stableRank` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `I/def` | implicit/hidden source assertion |
| SRC:2467–2476 | `continuousAt_stableRank` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `S/thm` | — |
| TeX 7781–86, p. 87;SRC:2467–2476 | `one_le_stableRank` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `S/thm` | — |
| SRC:2467–2476 | `stableRank_le_rank` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `S/thm` | — |
| SRC:2491–2504;§3.6, TeX 3528–3529, p. 37 | `hermDilation_add` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `I/lem` | implicit/hidden source assertion |
| SRC:2491–2504;§3.6, TeX 3528–3529, p. 37 | `hermDilation_smul_real` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `I/lem` | implicit/hidden source assertion |
| SRC:2491–2504 | `hermDilation` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `E/def` | — |
| SRC:2491–2504 | `isHermitian_hermDilation` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `I/lem` | implicit/hidden source assertion |
| (2.1.27) · p. 25 | `hermDilation_sq` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `E/thm` | |
| (2.1.27)–(2.1.28) · p. 25 | `hermDilation_sq_eigenvalues_multiset` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `S/thm` | full squared Hermitian-dilation spectrum with multiplicities |
| (2.1.27)–(2.1.28) · p. 25 | `hermDilation_eigenvalues_multiset` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `S/thm` | full signed dilation spectrum incl. surplus zeros |
| SRC:2512;SRC:2512–2516 | `l2_opNorm_hermDilation` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `I/thm` | implicit/hidden source assertion |
| (2.1.28) · p. 25 | `lambdaMax_hermDilation` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `E/thm` | |
| (2.1.29) · p. 25 | `schattenOneNorm` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `I/def` | implicit/hidden source assertion |
| (2.1.29) · p. 25 | `schattenOneNorm_reindex` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `S/thm` | reindex invariance |
| (2.1.29) · p. 25 | `schattenOneNorm_smul` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `S/thm` | homogeneity |
| (2.1.29) · p. 25 | `schattenOneNorm_eq_zero_iff` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `S/thm` | separation |
| (2.1.29) · p. 25 | `schattenOneNorm_add_le` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `S/thm` | triangle inequality |
| (2.1.29) · p. 25 | `schattenOneAddGroupNorm` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `S/def` | bundled non-global norm structure |
| (2.1.29) · p. 25 | `schattenOneNormedAddCommGroup` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `S/def` | bundled NormedAddCommGroup |
| (2.1.29) · p. 25 | `schattenOneNorm_eq_bundled_norm` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `S/thm` | bundled-norm agreement |
| (2.1.30) · p. 25 | `entrywiseL1Norm` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `I/def` | implicit/hidden source assertion |
| (2.1.30) · p. 25 | `entrywiseL1Norm_add_le` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `S/thm` | triangle inequality |
| (2.1.30) · p. 25 | `entrywiseL1Norm_smul` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `S/thm` | homogeneity |
| (2.1.30) · p. 25 | `entrywiseL1Norm_eq_zero_iff` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `S/thm` | separation |
| (2.1.30) · p. 25 | `entrywiseL1AddGroupNorm` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `S/def` | bundled non-global norm structure |
| (2.1.30) · p. 25 | `entrywiseL1NormedAddCommGroup` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `S/def` | bundled NormedAddCommGroup |
| (2.1.30) · p. 25 | `entrywiseL1Norm_eq_bundled_norm` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `S/thm` | bundled-norm agreement |
| (2.1.31) · p. 25 | `entrywiseL1Norm_le` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `E/thm` | |
| SRC:2633–2645 | `rademacherMeasure` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `I/def` | implicit/hidden source assertion |
| TeX 10670–75, p. 107;SRC:2633–2645 | `IsBernoulli` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `I/def` | implicit/hidden source assertion |
| TeX 3894–3899, p. 41;SRC:2633–2645 | `IsRademacher` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `I/def` | implicit/hidden source assertion |
| SRC:2633–2645 | `IsStdGaussian` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `I/def` | implicit/hidden source assertion |
| SRC:2633–2645 | `bernoulliMeasureReal` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `I/def` | implicit/hidden source assertion |
| SRC:2658–2663 | `iIndepFun_iff_book` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `M/thm` | Mathlib correspondence |
| SRC:2667–2672 | `expectation` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `E/def` | — |
| SRC:2673–2679 | `expectation_add` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `S/thm` | — |
| SRC:2673–2679 | `expectation_const_mul` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `S/thm` | — |
| SRC:2673–2679 | `expectation_mul_const` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `S/thm` | — |
| SRC:2680–2684 | `expectation_mul_of_indepFun` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `S/thm` | — |
| (2.2.1) · p. 27 | `markov_inequality` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `M/thm` | Mathlib correspondence |
| (2.2.2) · p. 27 | `expectation_lambdaMin_le` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `E/thm` | — |
| (2.2.2) · p. 27 | `lambdaMax_expectation_le` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `E/thm` | — |
| (2.2.2) · p. 27 | `norm_expectation_le` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `E/thm` | — |
| SRC:2727–2736 | `expectation_loewner_mono` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `S/thm` | — |
| SRC:2727–2736 | `posSemidef_expectation` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `S/thm` | — |
| (2.2.3) · p. 27 | `matrixVar` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `E/def` | — |
| SRC:2774–2779 | `matrixVar_eq_sub` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `E/thm` | — |
| SRC:2780 | `posSemidef_matrixVar` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `I/thm` | implicit/hidden source assertion |
| SRC:2781–2786 | `matrixVar_apply` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `S/thm` | — |
| (2.2.4) · p. 28 | `varStatHerm` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `E/def` | — |
| SRC:2795–2800 | `rayleigh_matrixVar` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `I/thm` | implicit/hidden source assertion |
| SRC:2795–2800 | `varStatHerm_eq_lambdaMax` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `I/thm` | implicit/hidden source assertion |
| SRC:2795–2800 | `varStatHerm_eq_sup_variance` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `S/thm` | — |
| (2.2.5) · p. 28 | `matrixVar_sum` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `E/thm` | — |
| (2.2.6) · p. 28 | `varStatHerm_sum` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `E/thm` | — |
| SRC:2822–2827 | `sum_varStatHerm_le_card_mul` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `S/thm` | — |
| SRC:2822–2827 | `varStatHerm_sum_le` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `S/thm` | — |
| SRC:2828–2830 | `varStatHerm_sum_of_identDistrib` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `S/thm` | — |
| TeX 3951–3955, p. 42;SRC:2842–2851 | `matrixVar2` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `E/def` | — |
| (2.2.7) · p. 28 | `matrixVar1` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `E/def` | — |
| SRC:2852–2855 | `posSemidef_matrixVar1` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `S/thm` | — |
| SRC:2852–2855 | `posSemidef_matrixVar2` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `S/thm` | — |
| SRC:2855–2859 | `matrixVar1_eq_matrixVar` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `S/thm` | — |
| SRC:2855–2859 | `matrixVar2_eq_matrixVar` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `S/thm` | — |
| (2.2.8) · p. 29 | `varStat` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `E/def` | — |
| SRC:2876–2877 | `varStat_eq_varStatHerm` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `S/thm` | — |
| (2.2.9) · p. 29 | `matrixVar_hermDilation` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `E/thm` | — |
| (2.2.10) · p. 29 | `varStat_hermDilation` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `E/thm` | — |
| TeX 12036–40, p. 117;SRC:2892–2901 | `l2_opNorm_fromBlocks_diagonal` | [`Prelude.lean`](Prelude.lean) | `I/lem` | implicit/hidden source assertion |
| TeX 10810–30, p. 108;SRC:2905–2916 | `matrixVar2_sum` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `S/thm` | — |
| (2.2.11) · p. 29 | `varStat_sum` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `E/thm` | — |
| TeX 5145–5151, p. 55 | `dilation_coeff_sq_norm` | [`Chapter4_MatrixGaussianAndRademacherSeries.lean`](Chapter4_MatrixGaussianAndRademacherSeries.lean) | `I/lem` | implicit/hidden source assertion |
| §2.2.4, p.27, TeX 2673–2679 | `expectation_conjTranspose` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `I/thm` | verified implicit/prose source assertion |
| (2.1.1), p.18, TeX 1815–1819 | `l2norm_eq_sqrt_sum` | [`Prelude.lean`](Prelude.lean) | `M/lem` | Mathlib correspondence |
| (2.1.24), p.24, TeX 2419–2424 | `l2_opNorm_sq_conjTranspose_mul_self` | [`Prelude.lean`](Prelude.lean) | `M/lem` | Mathlib correspondence |
| §2.1.9, p.21, TeX 2029–2031; used in Theorem 3.4.1 | `convex_posDef` | [`Chapter3_MatrixLaplaceTransformMethod.lean`](Chapter3_MatrixLaplaceTransformMethod.lean) | `I/lem` | verified implicit/prose source assertion |
| §2.1.6 unnumbered convention, p.19, TeX 1912–1924 | `sortedEigenvalues` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `I/def` | verified implicit/prose source assertion |
| §2.1.6 unnumbered convention, p.19, TeX 1920–1924; graph use at pp.67–69 | `secondSmallestEigenvalue` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `I/def` | verified implicit/prose source assertion |

### Chapter 3

| Book source | Lean declaration | Final module | Role | Notes |
|---|---|---|---|---|
| §3.1, TeX 2988–2998, p. 32;§3.1, TeX 3018–3024, p. 32 | `matrixCgf` | [`Chapter3_MatrixLaplaceTransformMethod.lean`](Chapter3_MatrixLaplaceTransformMethod.lean) | `E/def` | — |
| §3.1, TeX 2988–3000, p. 32 | `isHermitian_matrixMgf` | [`Chapter3_MatrixLaplaceTransformMethod.lean`](Chapter3_MatrixLaplaceTransformMethod.lean) | `I/lem` | implicit/hidden source assertion |
| §3.1, TeX 2988–3000, p. 32 | `smul_one_le_matrixMgf` | [`Chapter3_MatrixLaplaceTransformMethod.lean`](Chapter3_MatrixLaplaceTransformMethod.lean) | `I/thm` | implicit/hidden source assertion |
| Def. 3.1.1 · `def:matrix-mgf-cgf` · p. 32 | `matrixMgf` | [`Chapter3_MatrixLaplaceTransformMethod.lean`](Chapter3_MatrixLaplaceTransformMethod.lean) | `E/def` | — |
| §3.1, TeX 3009–3015, p. 32;§3.1, TeX 3016, p. 32 | `matrixMgf_hasSum_moments` | [`Chapter3_MatrixLaplaceTransformMethod.lean`](Chapter3_MatrixLaplaceTransformMethod.lean) | `S/thm` | — |
| §3.2, TeX 3037–3043, p. 32 | `matrix_laplace_tail_upper_inf` | [`Chapter3_MatrixLaplaceTransformMethod.lean`](Chapter3_MatrixLaplaceTransformMethod.lean) | `E/thm` | — |
| §3.2, TeX 3037–3049, p. 32 | `matrix_laplace_tail_lower_inf` | [`Chapter3_MatrixLaplaceTransformMethod.lean`](Chapter3_MatrixLaplaceTransformMethod.lean) | `E/thm` | — |
| (3.2.2) · p. 32 | `matrix_laplace_tail_lower` | [`Chapter3_MatrixLaplaceTransformMethod.lean`](Chapter3_MatrixLaplaceTransformMethod.lean) | `E/thm` | — |
| (3.2.3) · p. 33<br>(3.2.1) · p. 32<br>Prop. 3.2.1 · p. 32 | `matrix_laplace_tail_upper` | [`Chapter3_MatrixLaplaceTransformMethod.lean`](Chapter3_MatrixLaplaceTransformMethod.lean) | `E/thm` | — |
| (3.2.3) · p. 33 | `exp_lambdaMax_le_trace_exp` | [`Chapter3_MatrixLaplaceTransformMethod.lean`](Chapter3_MatrixLaplaceTransformMethod.lean) | `S/lem` | — |
| (3.2.3) · p. 33 | `lambdaMax_exp` | [`Chapter3_MatrixLaplaceTransformMethod.lean`](Chapter3_MatrixLaplaceTransformMethod.lean) | `I/lem` | implicit/hidden source assertion |
| TeX 6556–6557, p. 72;§3.2, TeX 3081–3091, p. 33 | `lambdaMax_smul_nonpos` | [`Chapter3_MatrixLaplaceTransformMethod.lean`](Chapter3_MatrixLaplaceTransformMethod.lean) | `I/lem` | implicit/hidden source assertion |
| (3.2.4) · p. 33<br>Prop. 3.2.2 · p. 33 | `matrix_laplace_expectation_upper` | [`Chapter3_MatrixLaplaceTransformMethod.lean`](Chapter3_MatrixLaplaceTransformMethod.lean) | `E/thm` | |
| (3.2.5) · p. 33 | `matrix_laplace_expectation_lower` | [`Chapter3_MatrixLaplaceTransformMethod.lean`](Chapter3_MatrixLaplaceTransformMethod.lean) | `E/thm` | |
| (3.3.1) · p. 34 | `scalar_mgf_sum` | [`Chapter3_MatrixLaplaceTransformMethod.lean`](Chapter3_MatrixLaplaceTransformMethod.lean) | `M/thm` | Mathlib correspondence |
| §3.3, TeX 3148–3152, p. 34 | `matrix_exp_add_of_commute` | [`Chapter3_MatrixLaplaceTransformMethod.lean`](Chapter3_MatrixLaplaceTransformMethod.lean) | `M/thm` | Mathlib correspondence |
| (3.3.3) · p. 34 | `golden_thompson` | [`Chapter3_MatrixLaplaceTransformMethod.lean`](Chapter3_MatrixLaplaceTransformMethod.lean) | `S/thm` | — |
| (3.3.4) · p. 34 | `scalar_cgf_sum` | [`Chapter3_MatrixLaplaceTransformMethod.lean`](Chapter3_MatrixLaplaceTransformMethod.lean) | `S/thm` | — |
| (3.5.1) · p. 35<br>Lemma 3.5.1 · p. 35 | `trace_exp_sum_le_trace_exp_sum_cgf` | [`Chapter3_MatrixLaplaceTransformMethod.lean`](Chapter3_MatrixLaplaceTransformMethod.lean) | `E/thm` | — |
| (3.5.2) · p. 35 | `trace_exp_cgf_sum_le` | [`Chapter3_MatrixLaplaceTransformMethod.lean`](Chapter3_MatrixLaplaceTransformMethod.lean) | `E/thm` | — |
| Thm. 3.4.1 · p. 35 | `lieb_trace_exp_log_concave` | [`Chapter3_MatrixLaplaceTransformMethod.lean`](Chapter3_MatrixLaplaceTransformMethod.lean) | `E/thm` | — |
| §3.4, TeX 3235–3237, p. 35 | `scalar_exp_add_log` | [`Chapter3_MatrixLaplaceTransformMethod.lean`](Chapter3_MatrixLaplaceTransformMethod.lean) | `I/lem` | implicit/hidden source assertion |
| Cor. 3.4.2 · p. 35 | `expectation_trace_exp_add_le` | [`Chapter3_MatrixLaplaceTransformMethod.lean`](Chapter3_MatrixLaplaceTransformMethod.lean) | `E/thm` | — |
| §3.4, TeX 3267–3277, p. 35 | `exp_loewner_bounds` | [`Chapter3_MatrixLaplaceTransformMethod.lean`](Chapter3_MatrixLaplaceTransformMethod.lean) | `I/lem` | implicit/hidden source assertion |
| §3.4, TeX 3270–3277, p. 35 | `concaveOn_posDef_expectation_le` | [`Chapter3_MatrixLaplaceTransformMethod.lean`](Chapter3_MatrixLaplaceTransformMethod.lean) | `S/thm` | — |
| (3.6.1) · p. 36 | `master_expectation_upper` | [`Chapter3_MatrixLaplaceTransformMethod.lean`](Chapter3_MatrixLaplaceTransformMethod.lean) | `E/thm` | — |
| (3.6.2) · p. 36 | `master_expectation_lower` | [`Chapter3_MatrixLaplaceTransformMethod.lean`](Chapter3_MatrixLaplaceTransformMethod.lean) | `E/thm` | — |
| (3.6.3) · p. 36 | `master_tail_upper` | [`Chapter3_MatrixLaplaceTransformMethod.lean`](Chapter3_MatrixLaplaceTransformMethod.lean) | `E/thm` | — |
| (3.6.4) · p. 36 | `master_tail_lower` | [`Chapter3_MatrixLaplaceTransformMethod.lean`](Chapter3_MatrixLaplaceTransformMethod.lean) | `E/thm` | — |
| Proposition 3.2.2; (3.2.4), p.33, TeX 3099–3108 | `matrix_laplace_expectation_upper_inf` | [`Chapter3_MatrixLaplaceTransformMethod.lean`](Chapter3_MatrixLaplaceTransformMethod.lean) | `E/thm` | verified mapping |
| Proposition 3.2.2; (3.2.5), p.33, TeX 3099–3108 | `matrix_laplace_expectation_lower_sup` | [`Chapter3_MatrixLaplaceTransformMethod.lean`](Chapter3_MatrixLaplaceTransformMethod.lean) | `E/thm` | verified mapping |
| Theorem 3.6.1; (3.6.1), p.36, TeX 3489–3520 | `master_expectation_upper_inf` | [`Chapter3_MatrixLaplaceTransformMethod.lean`](Chapter3_MatrixLaplaceTransformMethod.lean) | `E/thm` | verified explicit source counterpart |
| Theorem 3.6.1; (3.6.2), p.36, TeX 3489–3520 | `master_expectation_lower_sup` | [`Chapter3_MatrixLaplaceTransformMethod.lean`](Chapter3_MatrixLaplaceTransformMethod.lean) | `E/thm` | verified explicit source counterpart |
| Theorem 3.6.1; (3.6.3), p.36, TeX 3489–3520 | `master_tail_upper_inf` | [`Chapter3_MatrixLaplaceTransformMethod.lean`](Chapter3_MatrixLaplaceTransformMethod.lean) | `E/thm` | verified explicit source counterpart |
| Theorem 3.6.1; (3.6.4), p.36, TeX 3489–3520 | `master_tail_lower_inf` | [`Chapter3_MatrixLaplaceTransformMethod.lean`](Chapter3_MatrixLaplaceTransformMethod.lean) | `E/thm` | verified explicit source counterpart |

### Chapter 4

| Book source | Lean declaration | Final module | Role | Notes |
|---|---|---|---|---|
| Thm. 4.1.1 · p. 42 | `gaussian_series_rect_expectation` | [`Chapter4_MatrixGaussianAndRademacherSeries.lean`](Chapter4_MatrixGaussianAndRademacherSeries.lean) | `E/thm` | — |
| Thm. 4.1.1 · p. 42 | `rademacher_series_rect_expectation_of_isRademacher` | [`Chapter4_MatrixGaussianAndRademacherSeries.lean`](Chapter4_MatrixGaussianAndRademacherSeries.lean) | `S/thm` | distributional Rademacher law |
| §4.1, TeX 3926–3933, p. 42 | `scalar_gauss_series_variance` | [`Chapter4_MatrixGaussianAndRademacherSeries.lean`](Chapter4_MatrixGaussianAndRademacherSeries.lean) | `E/thm` | — |
| (4.1.1) · p. 42 | `scalar_gauss_series_tail` | [`Chapter4_MatrixGaussianAndRademacherSeries.lean`](Chapter4_MatrixGaussianAndRademacherSeries.lean) | `E/thm` | — |
| TeX 3951–3955, p. 42 | `gaussian_series_second_moment` | [`Chapter4_MatrixGaussianAndRademacherSeries.lean`](Chapter4_MatrixGaussianAndRademacherSeries.lean) | `E/thm` | — |
| TeX 3953–3958, p. 42 | `series_second_moment_right` | [`Chapter4_MatrixGaussianAndRademacherSeries.lean`](Chapter4_MatrixGaussianAndRademacherSeries.lean) | `E/thm` | — |
| TeX 3964–3968, p. 42 | `gaussian_series_rect_tail` | [`Chapter4_MatrixGaussianAndRademacherSeries.lean`](Chapter4_MatrixGaussianAndRademacherSeries.lean) | `E/thm` | — |
| (4.1.7) · p. 43 | `gauss_expect_sq_upper` | [`Chapter4_MatrixGaussianAndRademacherSeries.lean`](Chapter4_MatrixGaussianAndRademacherSeries.lean) | `E/thm` | — |
| (4.1.7) · p. 43 | `gauss_expect_sq_lower` | [`Chapter4_MatrixGaussianAndRademacherSeries.lean`](Chapter4_MatrixGaussianAndRademacherSeries.lean) | `E/thm` | — |
| (4.4.3) · p. 49 | `toeplitz_expected_norm` | [`Chapter4_MatrixGaussianAndRademacherSeries.lean`](Chapter4_MatrixGaussianAndRademacherSeries.lean) | `E/thm` | |
| TeX 4167–4171, p. 44;TeX 4624–4626, p. 49 | `toeplitz_variance` | [`Chapter4_MatrixGaussianAndRademacherSeries.lean`](Chapter4_MatrixGaussianAndRademacherSeries.lean) | `E/thm` | — |
| TeX 4221–4227, p. 44 | `gauss_quadform_second_moment` | [`Chapter4_MatrixGaussianAndRademacherSeries.lean`](Chapter4_MatrixGaussianAndRademacherSeries.lean) | `E/thm` | — |
| TeX 4221–4227, p. 44 | `weakVariance` | [`Chapter4_MatrixGaussianAndRademacherSeries.lean`](Chapter4_MatrixGaussianAndRademacherSeries.lean) | `E/def` | — |
| TeX 4228–4231, p. 45 | `variance_le_max_dim_mul_weakVariance` | [`Chapter4_MatrixGaussianAndRademacherSeries.lean`](Chapter4_MatrixGaussianAndRademacherSeries.lean) | `S/thm` | — |
| TeX 4228–4231, p. 45 | `weakVariance_le_variance` | [`Chapter4_MatrixGaussianAndRademacherSeries.lean`](Chapter4_MatrixGaussianAndRademacherSeries.lean) | `E/thm` | — |
| (4.1.8) · p. 45 | `gauss_concentration` | [`Chapter4_MatrixGaussianAndRademacherSeries.lean`](Chapter4_MatrixGaussianAndRademacherSeries.lean) | `E/thm` | |
| (4.2.3) · p. 46 | `wigner_expected_norm` | [`Chapter4_MatrixGaussianAndRademacherSeries.lean`](Chapter4_MatrixGaussianAndRademacherSeries.lean) | `E/thm` | — |
| TeX 4330–4335, p. 46 | `wigner_coeff_sq_sum` | [`Chapter4_MatrixGaussianAndRademacherSeries.lean`](Chapter4_MatrixGaussianAndRademacherSeries.lean) | `S/thm` | — |
| TeX 4336–4337, p. 46 | `wignerCoeff_sq` | [`Chapter4_MatrixGaussianAndRademacherSeries.lean`](Chapter4_MatrixGaussianAndRademacherSeries.lean) | `I/lem` | implicit/hidden source assertion |
| TeX 4339–4344, p. 46 | `wigner_variance` | [`Chapter4_MatrixGaussianAndRademacherSeries.lean`](Chapter4_MatrixGaussianAndRademacherSeries.lean) | `E/thm` | — |
| (4.2.6) · p. 47 | `gaussianRect_expected_norm` | [`Chapter4_MatrixGaussianAndRademacherSeries.lean`](Chapter4_MatrixGaussianAndRademacherSeries.lean) | `E/thm` | |
| TeX 4424–4437, p. 47 | `gaussianRect_coeff_sum_right` | [`Chapter4_MatrixGaussianAndRademacherSeries.lean`](Chapter4_MatrixGaussianAndRademacherSeries.lean) | `E/thm` | — |
| TeX 4438–4442, p. 47 | `gaussianRect_variance` | [`Chapter4_MatrixGaussianAndRademacherSeries.lean`](Chapter4_MatrixGaussianAndRademacherSeries.lean) | `E/thm` | — |
| TeX 4447–4452, p. 47 | `sqrt_max_comparison` | [`Chapter4_MatrixGaussianAndRademacherSeries.lean`](Chapter4_MatrixGaussianAndRademacherSeries.lean) | `E/thm` | — |
| (4.3.3) · p. 48 | `signed_expected_norm_of_isRademacher` | [`Chapter4_MatrixGaussianAndRademacherSeries.lean`](Chapter4_MatrixGaussianAndRademacherSeries.lean) | `S/thm` | distributional Rademacher law |
| TeX 4494–4497, p. 48;TeX 4498–4499, p. 48;TeX 4517–4529, p. 48;TeX 4531, p. 48 | `signed_variance` | [`Chapter4_MatrixGaussianAndRademacherSeries.lean`](Chapter4_MatrixGaussianAndRademacherSeries.lean) | `E/thm` | — |
| TeX 4502–4509, p. 48;TeX 4517–4529, p. 48 | `signed_coeff_sum_right` | [`Chapter4_MatrixGaussianAndRademacherSeries.lean`](Chapter4_MatrixGaussianAndRademacherSeries.lean) | `E/thm` | — |
| TeX 4510–4516, p. 48 | `signed_coeff_sum_left` | [`Chapter4_MatrixGaussianAndRademacherSeries.lean`](Chapter4_MatrixGaussianAndRademacherSeries.lean) | `E/thm` | — |
| TeX 4564–4577, pp. 48–49;TeX 4583–4587, p. 49 | `shiftPow` | [`Chapter4_MatrixGaussianAndRademacherSeries.lean`](Chapter4_MatrixGaussianAndRademacherSeries.lean) | `E/def` | — |
| TeX 4594–4595, p. 49 | `shiftPow_one_pow` | [`Chapter4_MatrixGaussianAndRademacherSeries.lean`](Chapter4_MatrixGaussianAndRademacherSeries.lean) | `I/lem` | implicit/hidden source assertion |
| TeX 4608–4613, p. 49 | `conjTranspose_mul_shiftPow` | [`Chapter4_MatrixGaussianAndRademacherSeries.lean`](Chapter4_MatrixGaussianAndRademacherSeries.lean) | `E/lem` | — |
| TeX 4608–4613, p. 49 | `shiftPow_mul_conjTranspose` | [`Chapter4_MatrixGaussianAndRademacherSeries.lean`](Chapter4_MatrixGaussianAndRademacherSeries.lean) | `E/lem` | — |
| TeX 4614–4621, p. 49 | `toeplitz_coeff_sum_right` | [`Chapter4_MatrixGaussianAndRademacherSeries.lean`](Chapter4_MatrixGaussianAndRademacherSeries.lean) | `E/thm` | — |
| §4.5, TeX 4709–4719, p. 50 | `maxqp_rounding_bound_of_isRademacher` | [`Chapter4_MatrixGaussianAndRademacherSeries.lean`](Chapter4_MatrixGaussianAndRademacherSeries.lean) | `S/thm` | distributional Rademacher law |
| TeX 4713, p. 50;TeX 4720–4726, p. 51 | `maxqp_variance_le` | [`Chapter4_MatrixGaussianAndRademacherSeries.lean`](Chapter4_MatrixGaussianAndRademacherSeries.lean) | `E/thm` | — |
| §4.5, TeX 4726–4730, p. 51 | `maxqp_rounding_bound_one_of_isRademacher` | [`Chapter4_MatrixGaussianAndRademacherSeries.lean`](Chapter4_MatrixGaussianAndRademacherSeries.lean) | `S/thm` | distributional Rademacher law |
| Thm. 4.6.1 · p. 51 | `gaussian_herm_expectation` | [`Chapter4_MatrixGaussianAndRademacherSeries.lean`](Chapter4_MatrixGaussianAndRademacherSeries.lean) | `E/thm` | — |
| Thm. 4.6.1 · p. 51 | `rademacher_herm_expectation_of_isRademacher` | [`Chapter4_MatrixGaussianAndRademacherSeries.lean`](Chapter4_MatrixGaussianAndRademacherSeries.lean) | `S/thm` | distributional Rademacher law |
| TeX 4819–4828, p. 51 | `gaussian_herm_tail` | [`Chapter4_MatrixGaussianAndRademacherSeries.lean`](Chapter4_MatrixGaussianAndRademacherSeries.lean) | `E/thm` | — |
| (4.6.4) · p. 52 | `gaussian_herm_min_expectation` | [`Chapter4_MatrixGaussianAndRademacherSeries.lean`](Chapter4_MatrixGaussianAndRademacherSeries.lean) | `S/thm` | — |
| (4.6.4) · p. 52 | `rademacher_herm_min_expectation_of_isRademacher` | [`Chapter4_MatrixGaussianAndRademacherSeries.lean`](Chapter4_MatrixGaussianAndRademacherSeries.lean) | `S/thm` | distributional Rademacher law |
| (4.6.5) · p. 52 | `gaussian_herm_min_tail` | [`Chapter4_MatrixGaussianAndRademacherSeries.lean`](Chapter4_MatrixGaussianAndRademacherSeries.lean) | `S/thm` | — |
| (4.6.5) · p. 52 | `rademacher_herm_min_tail_of_isRademacher` | [`Chapter4_MatrixGaussianAndRademacherSeries.lean`](Chapter4_MatrixGaussianAndRademacherSeries.lean) | `S/thm` | distributional Rademacher law |
| TeX 4944–4955, p. 52 | `gaussian_matrix_cgf` | [`Chapter4_MatrixGaussianAndRademacherSeries.lean`](Chapter4_MatrixGaussianAndRademacherSeries.lean) | `E/thm` | — |
| Lemma 4.6.2 · p. 52 | `gaussian_matrix_mgf` | [`Chapter4_MatrixGaussianAndRademacherSeries.lean`](Chapter4_MatrixGaussianAndRademacherSeries.lean) | `E/thm` | — |
| Lemma 4.6.3 · p. 54 | `rademacher_matrix_mgf` | [`Chapter4_MatrixGaussianAndRademacherSeries.lean`](Chapter4_MatrixGaussianAndRademacherSeries.lean) | `E/thm` | — |
| TeX 5064–5072, p. 54;TeX 5180 and 5239–5243, pp. 55–56 | `rademacher_matrix_mgf_le` | [`Chapter4_MatrixGaussianAndRademacherSeries.lean`](Chapter4_MatrixGaussianAndRademacherSeries.lean) | `E/thm` | — |
| TeX 5074–5081, p. 54 | `rademacher_matrix_cgf_le` | [`Chapter4_MatrixGaussianAndRademacherSeries.lean`](Chapter4_MatrixGaussianAndRademacherSeries.lean) | `E/thm` | — |
| TeX 5118–5130, p. 55;TeX 5133, p. 55 | `hermDilation_sum_smul` | [`Chapter4_MatrixGaussianAndRademacherSeries.lean`](Chapter4_MatrixGaussianAndRademacherSeries.lean) | `I/lem` | implicit/hidden source assertion |
| Theorem 4.6.1; (4.6.3), p.51 | `rademacher_herm_tail_of_isRademacher` | [`Chapter4_MatrixGaussianAndRademacherSeries.lean`](Chapter4_MatrixGaussianAndRademacherSeries.lean) | `S/thm` | distributional Rademacher law |
| Theorem 4.1.1; (4.1.6), p.42 | `rademacher_series_rect_tail_of_isRademacher` | [`Chapter4_MatrixGaussianAndRademacherSeries.lean`](Chapter4_MatrixGaussianAndRademacherSeries.lean) | `S/thm` | distributional Rademacher law |
| (4.1.3)–(4.1.4) /, p.42, TeX 3951–3958 | `series_second_moment_left` | [`Chapter4_MatrixGaussianAndRademacherSeries.lean`](Chapter4_MatrixGaussianAndRademacherSeries.lean) | `E/thm` | verified mapping |
| Theorem 4.1.1; (4.1.3)–(4.1.4), p.42, TeX 3944–3969 | `rademacher_series_second_moment` | [`Chapter4_MatrixGaussianAndRademacherSeries.lean`](Chapter4_MatrixGaussianAndRademacherSeries.lean) | `E/thm` | verified mapping |
| §4.2.2 unnumbered display, p.47, TeX 4424–4437 | `gaussianRect_coeff_sum_left` | [`Chapter4_MatrixGaussianAndRademacherSeries.lean`](Chapter4_MatrixGaussianAndRademacherSeries.lean) | `E/thm` | verified explicit source counterpart |
| §4.4 unnumbered displays, p.49, TeX 4608–4621 | `toeplitz_coeff_sum_left` | [`Chapter4_MatrixGaussianAndRademacherSeries.lean`](Chapter4_MatrixGaussianAndRademacherSeries.lean) | `E/thm` | verified explicit source counterpart |

### Chapter 5

| Book source | Lean declaration | Final module | Role | Notes |
|---|---|---|---|---|
| TeX 5292–5299, p. 59 | `posSemidef_of_lambdaMin_nonneg` | [`Appendix_MatrixRosenthal.lean`](Appendix_MatrixRosenthal.lean) | `S/lem` | — |
| (5.1.4) · p. 60<br>Thm. 5.1.1 · p. 60 | `matrix_chernoff_expectation_upper` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `E/thm` | |
| (5.1.1) · p. 60 | `chernoff_mu_min_eq` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `E/lem` | |
| TeX 5419–5429, p. 60;TeX 5430–5433, p. 60 | `expectation_matsum_eq` | [`Appendix_MatrixRosenthal.lean`](Appendix_MatrixRosenthal.lean) | `I/lem` | implicit/hidden source assertion |
| (5.1.2) · p. 60 | `chernoff_mu_max_eq` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `E/lem` | |
| (5.1.3) · p. 60 | `matrix_chernoff_expectation_lower` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `E/thm` | |
| (5.1.5) · p. 60 | `matrix_chernoff_tail_lower` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `E/thm` | |
| (5.1.6) · p. 60 | `matrix_chernoff_tail_upper` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `E/thm` | |
| (5.1.7) · p. 61 | `matrix_chernoff_expectation_lower_simple` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `E/thm` | |
| (5.1.8) · p. 61 | `matrix_chernoff_expectation_upper_simple` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `E/thm` | |
| TeX 5511–5517, p. 61 | `matrix_chernoff_tail_lower_subgaussian` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `E/thm` | — |
| TeX 5518–5522, p. 61 | `matrix_chernoff_tail_upper_exponential` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `E/thm` | — |
| (5.1.9) · p. 61 | `matrix_rosenthal` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `S/thm` | |
| TeX 5559–5560, p. 61 | `expectation_max_lambdaMax_le` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `S/thm` | — |
| (5.1.10) · p. 62 | `rosenthal_lower_two_sided` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `E/thm` | |
| (5.1.10) · p. 62 | `rosenthal_upper_two_sided` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `S/thm` | |
| TeX 5620–5624, p. 62 | `lambdaMax_expectation_ge_mu` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `E/thm` | — |
| TeX 5625–5631, p. 62 | `expectation_max_le_expectation_lambdaMax_of_integrable` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `S/thm` | integrable PSD maximum comparison, a.e.-PSD hypothesis |
| TeX 5632–5634, p. 62 | `lambdaMax_add_posSemidef_ge` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `I/lem` | implicit/hidden source assertion |
| TeX 5638–5647, p. 62;TeX 5648–5651, p. 62 | `bernoulli_diagonal_example` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `E/thm` | — |
| TeX 5685–5691, p. 63 | `expectation_lambdaMin_le_mu` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `E/thm` | — |
| TeX 5696–5703, p. 63;TeX 5704–5707, p. 63;TeX 5708–5711, p. 63 | `coupon_collector_lower_instance` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `E/thm` | — |
| TeX 10670–75, p. 107;TeX 5975–5978, p. 63;TeX 5981–5985, p. 64 | `columnSubmatrix` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `E/def` | — |
| TeX 5985, p. 64;TeX 6068, p. 65 | `integral_id_isBernoulli` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `I/lem` | implicit/hidden source assertion |
| (5.2.1) · p. 64 | `column_submatrix_lower_of_isBernoulli` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `S/thm` | Bernoulli law, no pointwise-support premise |
| (5.2.1) · p. 64 | `column_submatrix_upper_of_isBernoulli` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `S/thm` | Bernoulli law, no pointwise-support premise |
| TeX 10678–82, p. 107;TeX 6008–6013, p. 64;TeX 6087–6098, p. 65 | `columnSubmatrix_gram` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `E/thm` | — |
| TeX 10686–90, p. 107;TeX 6022–6027, p. 64 | `expectation_column_gram` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `E/thm` | — |
| TeX 6034, p. 64 | `l2_opNorm_colGram_le` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `I/lem` | implicit/hidden source assertion |
| TeX 6054–6068, p. 65;TeX 6057–6068, 6096, 6119, pp. 65–66 | `projDiag` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `E/def` | — |
| TeX 6065–6068, p. 65 | `rowColumnSubmatrix` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `E/def` | — |
| TeX 6065–6068, p. 65;TeX 6087–6098, p. 65 | `rowColumnSubmatrix_eq` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `E/lem` | — |
| (5.2.2) · p. 65 | `row_column_submatrix_norm_of_isBernoulli` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `S/thm` | Bernoulli law, no pointwise-support premise |
| (5.2.3) · p. 65 | `conditional_column_bound_of_isBernoulli` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `S/thm` | Bernoulli law, no pointwise-support premise |
| (5.2.3) · p. 65 | `conditional_column_bound_pointwise_of_isBernoulli` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `S/thm` | Bernoulli law, pointwise form |
| (5.2.4) · p. 66 | `row_sampling_gram_bound_of_isBernoulli` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `S/thm` | Bernoulli law, no pointwise-support premise |
| TeX 6135–6140, p. 66 | `colNormSq_rowSubmatrix` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `E/lem` | — |
| TeX 6141–6149, p. 66 | `entryDiag` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `E/def` | — |
| TeX 6141–6149, p. 66 | `sup_colNormSq_eq_lambdaMax` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `E/lem` | — |
| TeX 6151–6158, p. 66 | `entryDiag_family_bounds` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `E/lem` | — |
| TeX 6151–6158, p. 66 | `lambdaMax_diagonal_ofReal` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `I/lem` | implicit/hidden source assertion |
| TeX 6159–6168, p. 66;TeX 6169–6172, p. 66 | `entryDiag_sum_expectation` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `E/lem` | — |
| (5.2.5) · p. 66 | `max_column_norm_bound_of_isBernoulli` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `S/thm` | Bernoulli law, no pointwise-support premise |
| TeX 6234–6241, p. 67 | `lapMatrixC` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `E/def` | — |
| TeX 6234–6241, p. 67;TeX 6234–6243, p. 67;TeX 6243, p. 67 | `normalizedLapMatrix` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `E/def` | — |
| TeX 6241, p. 67 | `lapMatrixC_mulVec_one_eq_zero` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `E/lem` | — |
| TeX 6241, p. 67 | `posSemidef_lapMatrixC` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `E/lem` | — |
| TeX 6243, p. 67 | `connected_iff_secondSmallest_pos` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `S/thm` | — |
| (5.3.2) · p. 68 | `erAdjacency` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `E/def` | |
| TeX 6272–6276, p. 68 | `laplCoeff` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `E/def` | — |
| TeX 6272–6276, p. 68 | `laplCoeff_eq_singles` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `I/lem` | implicit/hidden source assertion |
| (5.3.3) · p. 68 | `erLaplacian` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `E/def` | |
| TeX 6296–6302, p. 69 | `exists_compression_isometry` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `I/thm` | implicit/hidden source assertion |
| (5.3.5) · p. 69 | `compressed_sum_eq` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `E/lem` | |
| TeX 6309–6311, p. 69;TeX 6675–6677, p. 74 | `eigenvalues_multiset_compression` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `I/thm` | implicit/hidden source assertion |
| TeX 6309–6311, p. 69 | `lambdaMin_compression_eq_secondSmallest` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `I/thm` | implicit/hidden source assertion |
| TeX 6313–6321, p. 69 | `compressed_summand_bounds` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `E/lem` | — |
| TeX 6313–6321, p. 69 | `laplCoeff_sq` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `E/lem` | — |
| TeX 6323–6332, p. 69;TeX 6332–6335, p. 69 | `expectation_erY_eq` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `E/thm` | — |
| TeX 6323–6332, p. 69 | `sum_laplCoeff` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `E/thm` | — |
| TeX 6347–6352, p. 69 | `er_compression_tail_of_isBernoulli` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `S/thm` | Bernoulli law, no pointwise-support premise |
| TeX 6347–6352, p. 69 | `er_second_smallest_tail_of_isBernoulli` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `S/thm` | Bernoulli law, no pointwise-support premise |
| Lemma 5.4.1 · p. 70 | `chernoff_matrix_cgf_le` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `E/thm` | — |
| Lemma 5.4.1 · p. 70 | `chernoff_matrix_mgf_le` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `E/thm` | — |
| TeX 6419–6428, p. 70 | `exp_le_one_add_chord` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `S/lem` | — |
| TeX 6433–6438, p. 70;TeX 6439–6441, p. 70 | `one_add_le_exp_matrix` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `I/lem` | implicit/hidden source assertion |
| TeX 6457–6472, p. 71;TeX 6473–6497, p. 71;TeX 6501–6510, p. 71 | `chernoff_cgf_trace_bound_upper` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `I/lem` | implicit/hidden source assertion |
| TeX 6457–6472, p. 71 | `gChernoff` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `I/def` | implicit/hidden source assertion |
| TeX 6517–6534, p. 72;TeX 6536–6558, p. 72 | `chernoff_cgf_trace_bound_lower` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `I/lem` | implicit/hidden source assertion |
| §5.2.2 unnumbered display, pp.65–66, TeX 6054–6068 | `rowSubmatrix` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `E/def` | verified explicit source counterpart |
| §5.3.1 unnumbered prose, p.67, TeX 6234–6243 | `erLaplacian_mulVec_one` | [`Chapter5_SumOfPSDMatrices.lean`](Chapter5_SumOfPSDMatrices.lean) | `I/lem` | verified implicit/prose source assertion |

### Chapter 6

| Book source | Lean declaration | Final module | Role | Notes |
|---|---|---|---|---|
| (6.1.3) · p. 76 | `matrix_bernstein_rect_expectation` | [`Chapter6_SumOfBoundedRandomMatrices.lean`](Chapter6_SumOfBoundedRandomMatrices.lean) | `E/thm` | — |
| (6.1.4) · p. 76 | `matrix_bernstein_rect_tail` | [`Chapter6_SumOfBoundedRandomMatrices.lean`](Chapter6_SumOfBoundedRandomMatrices.lean) | `E/thm` | — |
| TeX 6867, p. 77 | `variance_max_eq_of_hermitian` | [`Chapter6_SumOfBoundedRandomMatrices.lean`](Chapter6_SumOfBoundedRandomMatrices.lean) | `I/lem` | implicit/hidden source assertion |
| (6.1.5) · p. 77 | `matrix_bernstein_split_subgaussian` | [`Chapter6_SumOfBoundedRandomMatrices.lean`](Chapter6_SumOfBoundedRandomMatrices.lean) | `E/thm` | |
| (6.1.5) · p. 77 | `matrix_bernstein_split_subexponential` | [`Chapter6_SumOfBoundedRandomMatrices.lean`](Chapter6_SumOfBoundedRandomMatrices.lean) | `E/thm` | |
| TeX 6906–49, p. 77 | `matrix_bernstein_uncentered_expectation` | [`Chapter6_SumOfBoundedRandomMatrices.lean`](Chapter6_SumOfBoundedRandomMatrices.lean) | `E/thm` | — |
| (6.1.6) · p. 78 | `matrix_rosenthal_pinelis_symmetric_integrable` | [`Chapter6_SumOfBoundedRandomMatrices.lean`](Chapter6_SumOfBoundedRandomMatrices.lean) | `V/thm` | symmetry-in-law, exact coefficients, integrability form |
| (6.1.6) · p. 78 | `matrix_rosenthal_pinelis_centered_with_loss_integrable` | [`Chapter6_SumOfBoundedRandomMatrices.lean`](Chapter6_SumOfBoundedRandomMatrices.lean) | `V/thm` | centered, explicit √2 and 2 losses, integrability form |
| TeX 7007–13, p. 78 | `varStat_le_expectation_norm_sq` | [`Chapter6_SumOfBoundedRandomMatrices.lean`](Chapter6_SumOfBoundedRandomMatrices.lean) | `E/thm` | — |
| TeX 7014–23, p. 78 | `IsSymmetricRV` | [`Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean`](Chapter2_MatrixFunctionsAndProbabilityWithMatrices.lean) | `I/def` | implicit/hidden source assertion |
| (6.1.7) · p. 78 | `symmetric_sum_lower_bound_integrable` | [`Appendix_SymmetricLowerBound.lean`](Appendix_SymmetricLowerBound.lean) | `S/thm` | integrable symmetric lower bound, book 1/4 via stronger coeff-1 estimate |
| TeX 7068–74, p. 79;TeX 7094–101, p. 79 | `l2_opNorm_diagonal_abs` | [`Chapter6_SumOfBoundedRandomMatrices.lean`](Chapter6_SumOfBoundedRandomMatrices.lean) | `I/thm` | implicit/hidden source assertion |
| (6.2.4) · p. 81 | `secondMoment` | [`Chapter6_SumOfBoundedRandomMatrices.lean`](Chapter6_SumOfBoundedRandomMatrices.lean) | `E/def` | |
| (6.2.5) · p. 81 | `matrix_sampling_estimator_expectation_ae` | [`Chapter6_SumOfBoundedRandomMatrices.lean`](Chapter6_SumOfBoundedRandomMatrices.lean) | `S/thm` | a.e. template bound |
| (6.2.6) · p. 81 | `matrix_sampling_estimator_tail_ae` | [`Chapter6_SumOfBoundedRandomMatrices.lean`](Chapter6_SumOfBoundedRandomMatrices.lean) | `S/thm` | a.e. template bound |
| TeX 7404–15, p. 82 | `centered_second_moment_le` | [`Chapter6_SumOfBoundedRandomMatrices.lean`](Chapter6_SumOfBoundedRandomMatrices.lean) | `I/lem` | implicit/hidden source assertion |
| (6.2.7) · p. 82 | `matrix_sampling_sample_cost_ae` | [`Chapter6_SumOfBoundedRandomMatrices.lean`](Chapter6_SumOfBoundedRandomMatrices.lean) | `S/thm` | a.e. template bound |
| TeX 7475–85, p. 83 | `abs_trace_mul_le_schattenOne` | [`Chapter6_SumOfBoundedRandomMatrices.lean`](Chapter6_SumOfBoundedRandomMatrices.lean) | `I/thm` | implicit/hidden source assertion |
| TeX 7475–85, p. 83 | `trace_control_of_norm_le` | [`Chapter6_SumOfBoundedRandomMatrices.lean`](Chapter6_SumOfBoundedRandomMatrices.lean) | `E/thm` | — |
| (6.3.1) · p. 86 | `sparsifyProb` | [`Chapter6_SumOfBoundedRandomMatrices.lean`](Chapter6_SumOfBoundedRandomMatrices.lean) | `E/def` | — |
| TeX 7706–08, p. 86 | `sparsifyProb_sum_eq_one` | [`Chapter6_SumOfBoundedRandomMatrices.lean`](Chapter6_SumOfBoundedRandomMatrices.lean) | `I/thm` | implicit/hidden source assertion |
| TeX 7712–17, p. 86 | `sparsifyValue` | [`Chapter6_SumOfBoundedRandomMatrices.lean`](Chapter6_SumOfBoundedRandomMatrices.lean) | `E/def` | — |
| TeX 7718–23, p. 86 | `expectation_sparsifyEstimator` | [`Chapter6_SumOfBoundedRandomMatrices.lean`](Chapter6_SumOfBoundedRandomMatrices.lean) | `S/thm` | — |
| TeX 7718–23, p. 86 | `sum_sparsifyProb_smul_value` | [`Chapter6_SumOfBoundedRandomMatrices.lean`](Chapter6_SumOfBoundedRandomMatrices.lean) | `I/thm` | implicit/hidden source assertion |
| (6.3.2) · p. 86 | `sparsification_error_bound` | [`Chapter6_SumOfBoundedRandomMatrices.lean`](Chapter6_SumOfBoundedRandomMatrices.lean) | `E/thm` | — |
| TeX 7781–86, p. 87 | `sparsification_relative_error` | [`Chapter6_SumOfBoundedRandomMatrices.lean`](Chapter6_SumOfBoundedRandomMatrices.lean) | `E/thm` | — |
| (6.3.3) · p. 87 | `sparsifyProb_lower₁` | [`Chapter6_SumOfBoundedRandomMatrices.lean`](Chapter6_SumOfBoundedRandomMatrices.lean) | `E/lem` | — |
| TeX 7815–22, p. 87 | `sparsify_norm_le` | [`Chapter6_SumOfBoundedRandomMatrices.lean`](Chapter6_SumOfBoundedRandomMatrices.lean) | `S/thm` | — |
| TeX 7839–44, p. 88 | `sparsify_second_moment_le` | [`Chapter6_SumOfBoundedRandomMatrices.lean`](Chapter6_SumOfBoundedRandomMatrices.lean) | `E/thm` | — |
| (6.4.2) · p. 89 | `mul_eq_sum_outer` | [`Chapter6_SumOfBoundedRandomMatrices.lean`](Chapter6_SumOfBoundedRandomMatrices.lean) | `E/lem` | — |
| (6.4.3) · p. 89 | `matmulProb` | [`Chapter6_SumOfBoundedRandomMatrices.lean`](Chapter6_SumOfBoundedRandomMatrices.lean) | `S/def` | — |
| TeX 8263–66, p. 89 | `matmulProb_sum_eq_one_of_pair_ne_zero` | [`Chapter6_SumOfBoundedRandomMatrices.lean`](Chapter6_SumOfBoundedRandomMatrices.lean) | `S/thm` | normalization allowing B=0, C≠0 |
| TeX 10984–11000, p. 110;TeX 8271–79, 8288–90, p. 89 | `matmulValue` | [`Chapter6_SumOfBoundedRandomMatrices.lean`](Chapter6_SumOfBoundedRandomMatrices.lean) | `E/def` | — |
| TeX 8280–86, p. 89 | `expectation_matmulEstimator_book` | [`Chapter6_SumOfBoundedRandomMatrices.lean`](Chapter6_SumOfBoundedRandomMatrices.lean) | `S/thm` | unbiasedness with no B≠0 premise |
| (6.4.5) · p. 90 | `randomized_matmul_error_bound` | [`Chapter6_SumOfBoundedRandomMatrices.lean`](Chapter6_SumOfBoundedRandomMatrices.lean) | `E/thm` | — |
| TeX 8424–33, p. 90 | `randomized_matmul_relative_error` | [`Chapter6_SumOfBoundedRandomMatrices.lean`](Chapter6_SumOfBoundedRandomMatrices.lean) | `E/thm` | — |
| TeX 11002–10, p. 110;TeX 8459–66, p. 90;TeX 8467–71, p. 90 | `matmul_norm_le` | [`Chapter6_SumOfBoundedRandomMatrices.lean`](Chapter6_SumOfBoundedRandomMatrices.lean) | `E/thm` | — |
| TeX 8494–506, p. 91 | `matmul_second_moment_le` | [`Chapter6_SumOfBoundedRandomMatrices.lean`](Chapter6_SumOfBoundedRandomMatrices.lean) | `E/thm` | — |
| TeX 8879–91, p. 91;TeX 8909–21, p. 92 | `IsPosDefKernel` | [`Chapter6_SumOfBoundedRandomMatrices.lean`](Chapter6_SumOfBoundedRandomMatrices.lean) | `E/def` | — |
| TeX 8879–91, p. 91;TeX 8909–21, p. 92 | `kernelMatrix` | [`Chapter6_SumOfBoundedRandomMatrices.lean`](Chapter6_SumOfBoundedRandomMatrices.lean) | `E/def` | — |
| (6.5.2) · p. 92 | `HasReproducingProperty` | [`Chapter6_SumOfBoundedRandomMatrices.lean`](Chapter6_SumOfBoundedRandomMatrices.lean) | `S/def` | — |
| TeX 8984–9009, p. 93 | `featureOuter` | [`Chapter6_SumOfBoundedRandomMatrices.lean`](Chapter6_SumOfBoundedRandomMatrices.lean) | `S/def` | — |
| TeX 8984–9009, p. 93 | `featureVector` | [`Chapter6_SumOfBoundedRandomMatrices.lean`](Chapter6_SumOfBoundedRandomMatrices.lean) | `E/def` | — |
| TeX 8984–9009, p. 93 | `kernelMatrix_eq_expectation_outer` | [`Chapter6_SumOfBoundedRandomMatrices.lean`](Chapter6_SumOfBoundedRandomMatrices.lean) | `E/thm` | — |
| (6.5.7) · p. 95 | `random_feature_error_bound` | [`Chapter6_SumOfBoundedRandomMatrices.lean`](Chapter6_SumOfBoundedRandomMatrices.lean) | `E/thm` | |
| TeX 9345–61, p. 95 | `trace_kernelMatrix` | [`Chapter6_SumOfBoundedRandomMatrices.lean`](Chapter6_SumOfBoundedRandomMatrices.lean) | `E/thm` | — |
| TeX 9368–80, p. 95 | `random_feature_relative_error` | [`Chapter6_SumOfBoundedRandomMatrices.lean`](Chapter6_SumOfBoundedRandomMatrices.lean) | `E/thm` | — |
| TeX 9389–95, pp. 95–96 | `featureOuter_norm_le` | [`Chapter6_SumOfBoundedRandomMatrices.lean`](Chapter6_SumOfBoundedRandomMatrices.lean) | `E/lem` | — |
| (6.6.2) · p. 96 | `matrix_bernstein_herm_expectation_one_sided_ae` | [`Chapter6_SumOfBoundedRandomMatrices.lean`](Chapter6_SumOfBoundedRandomMatrices.lean) | `S/thm` | one-sided expectation, a.e. edge bound |
| (6.6.3) · p. 96 | `matrix_bernstein_herm_tail_one_sided_ae` | [`Chapter6_SumOfBoundedRandomMatrices.lean`](Chapter6_SumOfBoundedRandomMatrices.lean) | `S/thm` | one-sided tail, a.e. edge bound |
| TeX 9725–35, p. 97 | `matrix_bernstein_herm_min_expectation_one_sided_ae` | [`Chapter6_SumOfBoundedRandomMatrices.lean`](Chapter6_SumOfBoundedRandomMatrices.lean) | `S/thm` | one-sided min-expectation, a.e. edge bound |
| TeX 9736–45, p. 97 | `matrix_bernstein_herm_min_tail_one_sided_ae` | [`Chapter6_SumOfBoundedRandomMatrices.lean`](Chapter6_SumOfBoundedRandomMatrices.lean) | `S/thm` | one-sided min-tail, a.e. edge bound |
| TeX 10093–109, p. 98;TeX 11891–99, p. 116;TeX 9927–47, p. 97 | `gBernstein` | [`Chapter6_SumOfBoundedRandomMatrices.lean`](Chapter6_SumOfBoundedRandomMatrices.lean) | `E/def` | — |
| Lemma 6.6.2 · p. 97 | `bernstein_matrix_cgf_le_one_sided_ae` | [`Chapter6_SumOfBoundedRandomMatrices.lean`](Chapter6_SumOfBoundedRandomMatrices.lean) | `S/thm` | one-sided cgf, a.e. edge bound |
| Lemma 6.6.2 · p. 97 | `bernstein_matrix_mgf_le_one_sided_ae` | [`Chapter6_SumOfBoundedRandomMatrices.lean`](Chapter6_SumOfBoundedRandomMatrices.lean) | `S/thm` | one-sided mgf, a.e. edge bound |
| Lemma 6.6.2 · p. 97 | `bernstein_matrix_cgf_le_one_sided` | [`Chapter6_SumOfBoundedRandomMatrices.lean`](Chapter6_SumOfBoundedRandomMatrices.lean) | `S/thm` | one-sided single-summand cgf |
| Lemma 6.6.2 · p. 97 | `bernstein_matrix_mgf_le_one_sided` | [`Chapter6_SumOfBoundedRandomMatrices.lean`](Chapter6_SumOfBoundedRandomMatrices.lean) | `S/thm` | one-sided single-summand mgf |
| TeX 9949–61, p. 97 | `bernsteinH` | [`Chapter6_SumOfBoundedRandomMatrices.lean`](Chapter6_SumOfBoundedRandomMatrices.lean) | `S/def` | — |
| TeX 10111–29, pp. 98–99 | `bernstein_cgf_trace_bound` | [`Chapter6_SumOfBoundedRandomMatrices.lean`](Chapter6_SumOfBoundedRandomMatrices.lean) | `I/lem` | implicit/hidden source assertion |
| TeX 10225–42, p. 100 | `varAW` | [`Chapter6_SumOfBoundedRandomMatrices.lean`](Chapter6_SumOfBoundedRandomMatrices.lean) | `E/def` | — |
| TeX 10225–42, p. 100 | `varAW_eq_of_identDistrib` | [`Chapter6_SumOfBoundedRandomMatrices.lean`](Chapter6_SumOfBoundedRandomMatrices.lean) | `S/thm` | — |
| TeX 10225–42, p. 100 | `varStat_summand_le_varAW` | [`Chapter6_SumOfBoundedRandomMatrices.lean`](Chapter6_SumOfBoundedRandomMatrices.lean) | `I/thm` | implicit/hidden source assertion |
| Lemma 6.6.2 proof, unnumbered display, pp.97–98, TeX 9927–9990 | `exp_le_one_add_bernstein_quadratic` | [`Chapter6_SumOfBoundedRandomMatrices.lean`](Chapter6_SumOfBoundedRandomMatrices.lean) | `I/thm` | verified implicit/prose source assertion |
| Corollary 6.1.2, unnumbered tail display, p.77, TeX 6901–6949 | `matrix_bernstein_uncentered_tail` | [`Chapter6_SumOfBoundedRandomMatrices.lean`](Chapter6_SumOfBoundedRandomMatrices.lean) | `E/thm` | verified explicit source counterpart |

### Chapter 7

| Book source | Lean declaration | Final module | Role | Notes |
|---|---|---|---|---|
| Def. 7.1.1 · `def:int-dim` · p. 106 | `intdim` | [`Chapter7_IntrinsicDimension.lean`](Chapter7_IntrinsicDimension.lean) | `E/def` | — |
| TeX 10573–78, p. 106 | `intdim_le_rank` | [`Chapter7_IntrinsicDimension.lean`](Chapter7_IntrinsicDimension.lean) | `S/thm` | — |
| TeX 10573–78, p. 106 | `one_le_intdim` | [`Chapter7_IntrinsicDimension.lean`](Chapter7_IntrinsicDimension.lean) | `S/thm` | — |
| TeX 10579–81, p. 106 | `intdim_eq_rank_attained_without_identity` | [`Chapter7_IntrinsicDimension.lean`](Chapter7_IntrinsicDimension.lean) | `S/thm` | — |
| TeX 10579–81, p. 106 | `intdim_eq_card_iff` | [`Chapter7_IntrinsicDimension.lean`](Chapter7_IntrinsicDimension.lean) | `S/thm` | — |
| TeX 10579, p. 106 | `intdim_eq_one_iff_rank_eq_one` | [`Chapter7_IntrinsicDimension.lean`](Chapter7_IntrinsicDimension.lean) | `I/thm` | implicit/hidden source assertion |
| TeX 10584–85, p. 106;TeX 10691–10701, p. 108 | `intdim_smul` | [`Chapter7_IntrinsicDimension.lean`](Chapter7_IntrinsicDimension.lean) | `I/lem` | implicit/hidden source assertion |
| TeX 10586–87, p. 106;TeX 10587–88, p. 106;TeX 10650–55, p. 107 | `intdim_not_monotone` | [`Chapter7_IntrinsicDimension.lean`](Chapter7_IntrinsicDimension.lean) | `I/thm` | implicit/hidden source assertion |
| (7.2.1) · p. 107 | `intdim_chernoff_expectation_ae` | [`Chapter7_IntrinsicDimension.lean`](Chapter7_IntrinsicDimension.lean) | `S/thm` | a.e. spectral support |
| (7.2.2) · p. 107 | `intdim_chernoff_tail_ae` | [`Chapter7_IntrinsicDimension.lean`](Chapter7_IntrinsicDimension.lean) | `S/thm` | a.e. spectral support |
| TeX 10691–10701, p. 108 | `intdim_gram_eq_stableRank` | [`Chapter7_IntrinsicDimension.lean`](Chapter7_IntrinsicDimension.lean) | `E/thm` | — |
| TeX 10702–06, p. 108 | `intdim_column_submatrix_upper_of_isBernoulli` | [`Chapter7_IntrinsicDimension.lean`](Chapter7_IntrinsicDimension.lean) | `S/thm` | book-domain Bernoulli wrapper |
| TeX 10702–06, p. 108 | `intdim_column_submatrix_upper_totalized` | [`Chapter7_IntrinsicDimension.lean`](Chapter7_IntrinsicDimension.lean) | `S/thm` | totalized strengthening for B=0 or q=0 |
| (7.3.2) · p. 108<br>(7.3.1) · p. 108<br>Thm. 7.3.1 · p. 108 | `intdim_bernstein_rect_tail` | [`Chapter7_IntrinsicDimension.lean`](Chapter7_IntrinsicDimension.lean) | `E/thm` | — |
| TeX 10831–37, p. 108;TeX 10904–08, p. 109 | `intdim_fromBlocks_eq` | [`Chapter7_IntrinsicDimension.lean`](Chapter7_IntrinsicDimension.lean) | `S/thm` | — |
| TeX 10859–67, p. 109 | `intdim_fromBlocks_le_card` | [`Chapter7_IntrinsicDimension.lean`](Chapter7_IntrinsicDimension.lean) | `I/thm` | implicit/hidden source assertion |
| Cor. 7.3.2 · p. 109<br>(7.3.3) · p. 109 | `intdim_bernstein_rect_expectation` | [`Chapter7_IntrinsicDimension.lean`](Chapter7_IntrinsicDimension.lean) | `E/thm` | — |
| (7.3.4) · p. 109 | `intdim_fromBlocks_le_add` | [`Chapter7_IntrinsicDimension.lean`](Chapter7_IntrinsicDimension.lean) | `E/thm` | — |
| (7.3.4) · p. 109 | `min_intdim_le_intdim_fromBlocks` | [`Chapter7_IntrinsicDimension.lean`](Chapter7_IntrinsicDimension.lean) | `E/thm` | — |
| §7.3.3, TeX 11039–11044 · p. 111 | `matmul_intdim_error_bound` | [`Chapter7_IntrinsicDimension.lean`](Chapter7_IntrinsicDimension.lean) | `E/thm` | — |
| TeX 10924, p. 109 | `intdim_bernstein_uncentered_tail_ae` | [`Chapter7_IntrinsicDimension.lean`](Chapter7_IntrinsicDimension.lean) | `S/thm` | a.e. uncentered tail |
| Cor. 7.3.2 · p. 109 | `intdim_bernstein_uncentered_expectation` | [`Chapter7_IntrinsicDimension.lean`](Chapter7_IntrinsicDimension.lean) | `S/thm` | uncentered expectation form |
| (7.7.1) · p. 115 | `intdim_bernstein_herm_tail_one_sided` | [`Chapter7_IntrinsicDimension.lean`](Chapter7_IntrinsicDimension.lean) | `S/thm` | one-sided intrinsic Bernstein tail, a.e. upper edge |
| (7.3.5) · p. 110 | `matrix_sampling_intdim_expectation_ae` | [`Chapter7_IntrinsicDimension.lean`](Chapter7_IntrinsicDimension.lean) | `S/thm` | a.e. template bound |
| (7.3.6) · p. 110 | `matrix_sampling_intdim_tail_ae` | [`Chapter7_IntrinsicDimension.lean`](Chapter7_IntrinsicDimension.lean) | `S/thm` | a.e. template bound |
| TeX 11002–10, p. 110 | `matmul_var1_le` | [`Chapter7_IntrinsicDimension.lean`](Chapter7_IntrinsicDimension.lean) | `S/lem` | — |
| TeX 11002–10, p. 110 | `matmul_var2_le` | [`Chapter7_IntrinsicDimension.lean`](Chapter7_IntrinsicDimension.lean) | `S/lem` | — |
| TeX 11045–53, p. 111 | `matmul_intdim_sample_cost` | [`Chapter7_IntrinsicDimension.lean`](Chapter7_IntrinsicDimension.lean) | `E/thm` | — |
| TeX 11346–58, p. 112 | `psiOne` | [`Chapter7_IntrinsicDimension.lean`](Chapter7_IntrinsicDimension.lean) | `S/def` | — |
| TeX 11346–58, p. 112 | `psiTwo` | [`Chapter7_IntrinsicDimension.lean`](Chapter7_IntrinsicDimension.lean) | `S/def` | — |
| Prop. 7.4.1 · p. 112 | `generalized_matrix_laplace_tail` | [`Chapter7_IntrinsicDimension.lean`](Chapter7_IntrinsicDimension.lean) | `E/thm` | — |
| TeX 11374–85, p. 112;TeX 11394–11401, p. 112 | `psi_lambdaMax_le_sum` | [`Chapter7_IntrinsicDimension.lean`](Chapter7_IntrinsicDimension.lean) | `S/lem` | — |
| Lemma 7.5.1 · p. 112 | `intdim_trace_bound` | [`Chapter7_IntrinsicDimension.lean`](Chapter7_IntrinsicDimension.lean) | `E/thm` | — |
| Lemma 7.5.1 · p. 112 | `intdim_trace_bound_of_nonpos` | [`Chapter7_IntrinsicDimension.lean`](Chapter7_IntrinsicDimension.lean) | `V/thm` | Lemma 7.5.1 with the hypothesis relaxed to `φ(0) ≤ 0` (generalizes `intdim_trace_bound`) |
| TeX 11422–27, p. 112 | `convexOn_le_chord` | [`Chapter7_IntrinsicDimension.lean`](Chapter7_IntrinsicDimension.lean) | `I/lem` | implicit/hidden source assertion |
| TeX 11465–77, p. 113 | `intdim_laplace_psd` | [`Chapter7_IntrinsicDimension.lean`](Chapter7_IntrinsicDimension.lean) | `I/thm` | implicit/hidden source assertion |
| TeX 11479–87, p. 113 | `chernoff_trace_mgf_bound_ae` | [`Chapter7_IntrinsicDimension.lean`](Chapter7_IntrinsicDimension.lean) | `S/lem` | a.e. spectral support |
| TeX 11488–96, p. 113 | `chernoff_expected_trace_bound_ae` | [`Chapter7_IntrinsicDimension.lean`](Chapter7_IntrinsicDimension.lean) | `S/lem` | a.e. spectral support |
| TeX 11505–11, p. 113 | `trace_exp_sub_card_le_intdim_exp` | [`Chapter7_IntrinsicDimension.lean`](Chapter7_IntrinsicDimension.lean) | `I/thm` | implicit/hidden source assertion |
| TeX 11522–30, p. 114 | `exp_div_exp_sub_one_le` | [`Chapter7_IntrinsicDimension.lean`](Chapter7_IntrinsicDimension.lean) | `S/lem` | — |
| TeX 11542–49, p. 114 | `self_le_add_one_mul_log` | [`Chapter7_IntrinsicDimension.lean`](Chapter7_IntrinsicDimension.lean) | `E/lem` | — |
| TeX 11877–90, p. 116 | `intdim_laplace_psiTwo_one_sided` | [`Chapter7_IntrinsicDimension.lean`](Chapter7_IntrinsicDimension.lean) | `S/thm` | one-sided intrinsic Laplace step |
| TeX 11891–99, p. 116 | `bernstein_trace_mgf_bound_one_sided` | [`Chapter7_IntrinsicDimension.lean`](Chapter7_IntrinsicDimension.lean) | `S/thm` | one-sided intrinsic Bernstein trace mgf |
| TeX 11900–08, p. 116 | `bernstein_expected_trace_bound_one_sided` | [`Chapter7_IntrinsicDimension.lean`](Chapter7_IntrinsicDimension.lean) | `S/thm` | one-sided intrinsic expected trace |
| TeX 11947–56, p. 116 | `intdim_bernstein_herm_tail_core_one_sided` | [`Chapter7_IntrinsicDimension.lean`](Chapter7_IntrinsicDimension.lean) | `S/thm` | one-sided intrinsic Bernstein core |
| TeX 11957–63, p. 116 | `exp_div_psiTwo_le` | [`Chapter7_IntrinsicDimension.lean`](Chapter7_IntrinsicDimension.lean) | `S/lem` | — |
| TeX 11964–69, p. 116 | `exp_taylor_cubic_bound` | [`Chapter7_IntrinsicDimension.lean`](Chapter7_IntrinsicDimension.lean) | `S/lem` | — |
| TeX 11977–83, p. 117;TeX 11984–94, p. 117 | `bernstein_threshold_sq` | [`Chapter7_IntrinsicDimension.lean`](Chapter7_IntrinsicDimension.lean) | `E/lem` | — |
| TeX 12010–22, p. 117 | `intdim_bernstein_rect_tail_core` | [`Chapter7_IntrinsicDimension.lean`](Chapter7_IntrinsicDimension.lean) | `E/thm` | — |
| TeX 12024–31, p. 117 | `dilation_sum_sq_eq` | [`Chapter7_IntrinsicDimension.lean`](Chapter7_IntrinsicDimension.lean) | `I/lem` | implicit/hidden source assertion |
| TeX 12024–31, p. 117 | `fromBlocks_diag_loewner` | [`Chapter7_IntrinsicDimension.lean`](Chapter7_IntrinsicDimension.lean) | `I/lem` | implicit/hidden source assertion |
| TeX 12050–61, p. 118 | `integral_exp_neg_mul_Ioi` | [`Chapter7_IntrinsicDimension.lean`](Chapter7_IntrinsicDimension.lean) | `I/lem` | implicit/hidden source assertion |
| TeX 12062–68, p. 118 | `tail_exp_split` | [`Chapter7_IntrinsicDimension.lean`](Chapter7_IntrinsicDimension.lean) | `S/lem` | — |
| TeX 12069–75, p. 118 | `integral_gaussian_tail_le` | [`Chapter7_IntrinsicDimension.lean`](Chapter7_IntrinsicDimension.lean) | `E/lem` | — |
| §7.1 unnumbered attainment claim, p.106, TeX 10573–10585 | `intdim_smul_one` | [`Chapter7_IntrinsicDimension.lean`](Chapter7_IntrinsicDimension.lean) | `I/lem` | verified corrected reading of the source attainment claim |
| §7.4 unnumbered prose, p.112, TeX 11346–11358 | `psiOne_nonneg` | [`Chapter7_IntrinsicDimension.lean`](Chapter7_IntrinsicDimension.lean) | `S/lem` | verified source prose |
| §7.4 unnumbered prose, p.112, TeX 11346–11358 | `psiTwo_nonneg` | [`Chapter7_IntrinsicDimension.lean`](Chapter7_IntrinsicDimension.lean) | `S/lem` | verified source prose |
| §7.4 unnumbered prose, p.112, TeX 11346–11358 | `psiOne_zero` | [`Chapter7_IntrinsicDimension.lean`](Chapter7_IntrinsicDimension.lean) | `S/lem` | verified source prose |
| §7.4 unnumbered prose, p.112, TeX 11346–11358 | `psiTwo_zero` | [`Chapter7_IntrinsicDimension.lean`](Chapter7_IntrinsicDimension.lean) | `S/lem` | verified source prose |
| §7.4 unnumbered prose, p.112, TeX 11346–11358 | `psiOne_monotone` | [`Chapter7_IntrinsicDimension.lean`](Chapter7_IntrinsicDimension.lean) | `S/lem` | verified source prose; Lean proves the stronger global monotonicity statement |
| §7.4 unnumbered prose, p.112, TeX 11346–11358 | `psiTwo_monotoneOn` | [`Chapter7_IntrinsicDimension.lean`](Chapter7_IntrinsicDimension.lean) | `S/lem` | verified source prose |
| §7.4 unnumbered prose, p.112, TeX 11346–11358 | `convexOn_psiOne` | [`Chapter7_IntrinsicDimension.lean`](Chapter7_IntrinsicDimension.lean) | `S/lem` | verified source prose |
| §7.4 unnumbered prose, p.112, TeX 11346–11358 | `convexOn_psiTwo` | [`Chapter7_IntrinsicDimension.lean`](Chapter7_IntrinsicDimension.lean) | `S/lem` | verified source prose |

### Chapter 8

| Book source | Lean declaration | Final module | Role | Notes |
|---|---|---|---|---|
| Lemma 8.1.6 · p. 121<br>Thm. 8.1.1 · p. 119<br>(8.1.2) · p. 121 | `trace_exp_eq_at_optimizer` | [`Chapter8_ProofOfLiebsTheorem.lean`](Chapter8_ProofOfLiebsTheorem.lean) | `E/lem` | — |
| TeX 12202–08, p. 120; TeX 14104–07, p. 139 | `mre` | [`Chapter8_ProofOfLiebsTheorem.lean`](Chapter8_ProofOfLiebsTheorem.lean) | `S/def` | — |
| Prop. 8.1.3 · p. 120 | `mre_nonneg` | [`Chapter8_ProofOfLiebsTheorem.lean`](Chapter8_ProofOfLiebsTheorem.lean) | `E/thm` | |
| Fact 8.1.5 · `fact:partial-max` · p. 120 | `partial_maximization` | [`Chapter8_ProofOfLiebsTheorem.lean`](Chapter8_ProofOfLiebsTheorem.lean) | `S/thm` | — |
| TeX 12344–51, p. 122; TeX 12614–21, p. 124; TeX 14147–50, p. 139; TeX 14160–61, p. 140 | `vre` | [`Chapter8_ProofOfLiebsTheorem.lean`](Chapter8_ProofOfLiebsTheorem.lean) | `S/def` | — |
| TeX 12358–66, p. 122 | `vre_eq_mre_diagonal` | [`Chapter8_ProofOfLiebsTheorem.lean`](Chapter8_ProofOfLiebsTheorem.lean) | `I/lem` | implicit/hidden source assertion |
| Prop. 8.2.2 · p. 122 | `vre_nonneg` | [`Chapter8_ProofOfLiebsTheorem.lean`](Chapter8_ProofOfLiebsTheorem.lean) | `E/thm` | — |
| TeX 12422–29, p. 122 | `entropy_tangent_nonneg` | [`Chapter8_ProofOfLiebsTheorem.lean`](Chapter8_ProofOfLiebsTheorem.lean) | `E/lem` | — |
| TeX 12452–60, p. 122; TeX 12463–67, p. 123; TeX 14153–57, pp. 139–140 | `perspectiveFun` | [`Chapter8_ProofOfLiebsTheorem.lean`](Chapter8_ProofOfLiebsTheorem.lean) | `S/def` | — |
| Fact 8.2.4 · `fact:perspective-convex` · p. 123 | `perspectiveFun_convexOn` | [`Chapter8_ProofOfLiebsTheorem.lean`](Chapter8_ProofOfLiebsTheorem.lean) | `E/thm` | — |
| Prop. 8.2.5 · p. 124 | `vre_convexOn` | [`Chapter8_ProofOfLiebsTheorem.lean`](Chapter8_ProofOfLiebsTheorem.lean) | `E/thm` | — |
| TeX 12609–13, pp. 123–124; TeX 12614–21, p. 124 | `perspective_entropy_eq` | [`Chapter8_ProofOfLiebsTheorem.lean`](Chapter8_ProofOfLiebsTheorem.lean) | `E/lem` | — |
| TeX 12675–84, p. 124 | `sortedEig` | [`Chapter8_ProofOfLiebsTheorem.lean`](Chapter8_ProofOfLiebsTheorem.lean) | `E/def` | — |
| TeX 12675–84, p. 124 | `traceFn_eq_sum_sorted` | [`Chapter8_ProofOfLiebsTheorem.lean`](Chapter8_ProofOfLiebsTheorem.lean) | `E/thm` | — |
| Prop. 8.3.5 · p. 126 | `generalized_klein` | [`Chapter8_ProofOfLiebsTheorem.lean`](Chapter8_ProofOfLiebsTheorem.lean) | `E/thm` | |
| TeX 12915–21, p. 126; TeX 12922–28, p. 126 | `klein_inequality` | [`Chapter8_ProofOfLiebsTheorem.lean`](Chapter8_ProofOfLiebsTheorem.lean) | `E/thm` | — |
| TeX 13117–25, p. 128 | `one_le_inv_of_le_one` | [`Chapter8_ProofOfLiebsTheorem.lean`](Chapter8_ProofOfLiebsTheorem.lean) | `I/lem` | implicit/hidden source assertion |
| §8.4.5, TeX 13199–13200, p. 129 | `not_operatorConvexOn_exp` | [`Chapter8_ProofOfLiebsTheorem.lean`](Chapter8_ProofOfLiebsTheorem.lean) | `E/thm` | exact `2 × 2` counterexample; midpoint defect is `-13/20` at `(4,-1)` |
| TeX 13731–34, p. 134 | `matrixPerspective_arg_posDef` | [`Chapter8_ProofOfLiebsTheorem.lean`](Chapter8_ProofOfLiebsTheorem.lean) | `S/lem` | — |
| (8.7.1) · p. 136 | `kronecker_mixed_product` | [`Chapter8_ProofOfLiebsTheorem.lean`](Chapter8_ProofOfLiebsTheorem.lean) | `M/thm` | Mathlib correspondence |
| Fact 8.7.3 · `fact:kron-log` · p. 137 | `exp_kronecker_one` | [`Chapter8_ProofOfLiebsTheorem.lean`](Chapter8_ProofOfLiebsTheorem.lean) | `S/lem` | — |
| Fact 8.7.3 · `fact:kron-log` · p. 137 | `exp_one_kronecker` | [`Chapter8_ProofOfLiebsTheorem.lean`](Chapter8_ProofOfLiebsTheorem.lean) | `S/lem` | — |
| TeX 14015–27, p. 138 | `cfc_entropy_kernel` | [`Chapter8_ProofOfLiebsTheorem.lean`](Chapter8_ProofOfLiebsTheorem.lean) | `S/lem` | — |
| TeX 14015–27, p. 138 | `log_posDef_inv` | [`Chapter8_ProofOfLiebsTheorem.lean`](Chapter8_ProofOfLiebsTheorem.lean) | `S/lem` | — |

## Coverage scope

The table is a declaration correspondence index, not a claim that every sentence, historical attribution, asymptotic comparison, or application in the monograph has been formalized. Numeric and prose-only mappings were checked against the expanded arXiv-v1 TeX; implementation helpers and recovered prerequisites are omitted.

The Appendix section above summarizes the external mathematical inputs and the corresponding Lean proof pipelines.
