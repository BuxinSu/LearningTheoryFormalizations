# HighDimensionalProbability

This repository formalizes Roman Vershynin’s [*High-Dimensional Probability*](https://www.math.uci.edu/~rvershyn/papers/HDP-book/HDP-2.pdf), second edition, in Lean 4 and Mathlib. Equation, theorem, proposition, lemma, corollary, definition, example, and remark numbers in the library refer to the second-edition PDF.

The development covers the main mathematical arc of the book: concentration of independent sums, random vectors and random matrices, concentration without independence, quadratic forms and symmetrization, random processes, chaining, and deviations of random matrices on structured sets. The formalization is organized as a reusable library, with shared foundations for probability, Orlicz norms, random vectors and matrices, metric entropy, Gaussian matrices, random graphs, and matrix concentration.

## Summary

| Item | Value |
|---|---|
| Source | Roman Vershynin, *High-Dimensional Probability*, second-edition PDF |
| Lean / Mathlib version | `leanprover/lean4:v4.31.0`; Mathlib revision `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` |
| Main development | shared `Prelude`, Appetizer, and 9 chapter modules |
| Book → Lean correspondence | **592 verified results** |
| Chapter distribution | Appetizer: 9; Chapters 1–9: 50 / 59 / 61 / 88 / 66 / 39 / 59 / 99 / 61 |
| Core declarations | 2,409 theorems, 1,006 lemmas, and 784 ordinary definitions across the shared foundations and consolidated modules |

```bibtex
@misc{vershynin2026high,
  title={High-Dimensional Probability},
  author={Vershynin, Roman},
  year={2026},
  url={https://www.math.uci.edu/~rvershyn/papers/HDP-book/HDP-2.pdf}
}
```

## Build

The project is pinned to Lean/Mathlib `v4.31.0`. From the project root:

```sh
~/.elan/bin/lake build HighDimensionalProbability
```

To check one chapter directly:

```sh
~/.elan/bin/lake env lean HighDimensionalProbability/Chapter4_RandomMatrices.lean
```

## Module layout

| Area | Final module | Main topics |
|---|---|---|
| Shared foundations | [`Prelude/`](Prelude/) | Probability, Orlicz norms, random vectors and matrices, Gaussian matrices, metric entropy, random graphs, and matrix concentration |
| Appetizer | [`Chapter0_Appetizer.lean`](Chapter0_Appetizer.lean) | Empirical method, approximate Carathéodory, polytope covers, and volume bounds |
| Chapter 1 | [`Chapter1_AnalysisAndProbabilityRefresher.lean`](Chapter1_AnalysisAndProbabilityRefresher.lean) | Convexity, norms, probability, expectation, concentration basics, and classical limit laws |
| Chapter 2 | [`Chapter2_ConcentrationOfIndependentSums.lean`](Chapter2_ConcentrationOfIndependentSums.lean) | Gaussian tails, subgaussian and subexponential variables, Hoeffding and Bernstein inequalities |
| Chapter 3 | [`Chapter3_RandomVectorsInHighDimensions.lean`](Chapter3_RandomVectorsInHighDimensions.lean) | Concentration of random vectors, isotropy, covariance estimation, and high-dimensional geometry |
| Chapter 4 | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) | Singular values, random matrix norms, covariance matrices, and matrix concentration |
| Chapter 5 | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) | Concentration on product spaces, the sphere, and other dependent settings |
| Chapter 6 | [`Chapter6_QuadraticFormsSymmetrizationContraction.lean`](Chapter6_QuadraticFormsSymmetrizationContraction.lean) | Quadratic forms, decoupling, symmetrization, contraction, and comparison principles |
| Chapter 7 | [`Chapter7_RandomProcesses.lean`](Chapter7_RandomProcesses.lean) | Subgaussian processes, Gaussian complexity, widths, and comparison inequalities |
| Chapter 8 | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) | Dudley bounds, generic chaining, entropy integrals, and majorizing-measure methods |
| Chapter 9 | [`Chapter9_DeviationsOfRandomMatricesOnSets.lean`](Chapter9_DeviationsOfRandomMatricesOnSets.lean) | Matrix deviation, Johnson–Lindenstrauss embeddings, covariance estimation, recovery, and restricted isometries |

## Mathematical scope

The library provides formal counterparts for a broad collection of central results, including:

- Jensen, Hölder, Minkowski, Markov, Chebyshev, and classical limit theorems;
- Gaussian tail estimates and concentration inequalities for subgaussian and subexponential random variables;
- Hoeffding-, Bernstein-, and matrix-concentration principles;
- norm and covariance bounds for random vectors and random matrices;
- concentration phenomena on high-dimensional geometric and combinatorial spaces;
- symmetrization, contraction, quadratic-form, and decoupling arguments;
- Gaussian and Rademacher process estimates;
- covering numbers, entropy integrals, Dudley bounds, and generic chaining;
- matrix deviation inequalities and applications to dimension reduction, covariance estimation, sparse recovery, and restricted isometries.

Declarations are placed in the `HDP` namespace, with chapter-specific material under namespaces such as `HDP.Chapter1` through `HDP.Chapter9`. Shared APIs live in `HDP` and are designed to be reused across chapters.

## Shared foundations

| Module | Purpose |
|---|---|
| [`Prelude/Basic.lean`](Prelude/Basic.lean) | Distribution predicates, expectation, moments, moment-generating functions, variance, and elementary exponential estimates |
| [`Prelude/Orlicz.lean`](Prelude/Orlicz.lean) | Luxemburg/Orlicz norms and the common subgaussian/subexponential interface |
| [`Prelude/RandomVector.lean`](Prelude/RandomVector.lean) | Vector expectation, covariance, second moments, isotropy, and Gaussian-vector laws |
| [`Prelude/RandomMatrix.lean`](Prelude/RandomMatrix.lean) | Random-matrix rows, columns, Gram matrices, and sample second moments |
| [`Prelude/GaussianMatrix.lean`](Prelude/GaussianMatrix.lean) | Standard Gaussian matrices and vectorization interfaces |
| [`Prelude/Matrix.lean`](Prelude/Matrix.lean) | Operator norms, singular values, effective rank, and stable rank |
| [`Prelude/MetricEntropy.lean`](Prelude/MetricEntropy.lean) | Metric covers, nets, packing, and covering numbers |
| [`Prelude/MatrixConcentration.lean`](Prelude/MatrixConcentration.lean) | Matrix Bernstein and related concentration interfaces |
| [`Prelude/MatrixConcentrationReal.lean`](Prelude/MatrixConcentrationReal.lean) | Bridges between real matrices and complex/Hermitian concentration results |
| [`Prelude/Sphere.lean`](Prelude/Sphere.lean) | Normalized sphere measure, isometries, and distributional facts |
| [`Prelude/RandomGraph.lean`](Prelude/RandomGraph.lean) | Erdős–Rényi random graphs and probability interfaces |
| [`Prelude/SimpleGraph.lean`](Prelude/SimpleGraph.lean) | Graph cuts, cut sizes, and maximum-cut infrastructure |
| [`Prelude/StochasticBlockModel.lean`](Prelude/StochasticBlockModel.lean) | A loop-aware two-community stochastic block model |

## Citation and source convention

The second-edition PDF is the source of truth for statements and numbering:

> Roman Vershynin, *High-Dimensional Probability*, second edition.

When a result is already available in Mathlib, the development uses or specializes the existing theorem. Otherwise, the corresponding declaration is proved within the project and exposed through the chapter or shared-foundation API.


## Book → Lean correspondence

This table records **592 verified results** from the second-edition PDF. Each row identifies the source statement, its mathematical content, the corresponding Lean declaration, and the module in which it is exposed.

### Appetizer — Using Probability to Cover a Set

| Book source | Result | Lean declaration | Final module |
|---|---|---|---|
| (0.1), convex-hull definition | A point of `conv(T)` is a finite convex combination of points of `T`. | `Finset.convexHull_eq` | `.lake/packages/mathlib/Mathlib/Analysis/Convex/Caratheodory.lean` |
| Theorem 0.0.1 | Caratheodory: in `R^n`, at most `n+1` points suffice in a convex combination. | `convexHull_eq_union` | `.lake/packages/mathlib/Mathlib/Analysis/Convex/Caratheodory.lean` |
| Theorem 0.0.2 | Equal averages of `k` points approximate every point of a convex hull within `1/sqrt(k)`. | `HDP.Chapter0.approximate_caratheodory` | [`Chapter0_Appetizer.lean`](Chapter0_Appetizer.lean) |
| Corollary 0.0.3 | An `N`-vertex polytope in the unit ball has an internal `N^k`-point cover of radius `1/sqrt(k)`. | `HDP.Chapter0.exists_polytope_cover` | [`Chapter0_Appetizer.lean`](Chapter0_Appetizer.lean) |
| (0.3) | The cover yields `Vol(P) <= N^k k^(-n/2) Vol(B)` in division-free form. | `HDP.Chapter0.polytope_volume_equation_0_3` | [`Chapter0_Appetizer.lean`](Chapter0_Appetizer.lean) |
| (0.4) | The positive continuous critical point is `n/(2 log N)`, uniquely. | `HDP.Chapter0.polytope_volume_optimizer_equation_0_4` | [`Chapter0_Appetizer.lean`](Chapter0_Appetizer.lean) |
| Exercise 0.1(a) | Vector bias--variance identity. | `HDP.Chapter0.integral_norm_sub_mean_sq` | [`Chapter0_Appetizer.lean`](Chapter0_Appetizer.lean) |
| Exercise 0.2 | A vector mean minimizes expected squared Euclidean distance. | `HDP.Chapter0.integral_norm_sub_mean_sq_le` | [`Chapter0_Appetizer.lean`](Chapter0_Appetizer.lean) |
| Exercise 0.3 | Independent centered random vectors satisfy the Pythagorean second-moment identity. | `HDP.Chapter0.integral_norm_sum_sq_of_iIndepFun` | [`Chapter0_Appetizer.lean`](Chapter0_Appetizer.lean) |

### Chapter 1 — A Quick Refresher on Analysis and Probability

| Book source | Result | Lean declaration | Final module |
|---|---|---|---|
| Convex-set definition | A set contains every segment joining two of its points. | `HDP.Chapter1.convex_iff_segment` | [`Chapter1_AnalysisAndProbabilityRefresher.lean`](Chapter1_AnalysisAndProbabilityRefresher.lean) |
| (1.1), convex/concave functions | Convex functions lie below secants; `f` is concave iff `-f` is convex. | `HDP.Chapter1.convexOn_iff` | [`Chapter1_AnalysisAndProbabilityRefresher.lean`](Chapter1_AnalysisAndProbabilityRefresher.lean) |
| Maximum principle; norm convexity | A convex function on a convex hull is bounded by generator values; norms and norm balls are convex. | `HDP.Chapter1.convexHull_value_le_generator` | [`Chapter1_AnalysisAndProbabilityRefresher.lean`](Chapter1_AnalysisAndProbabilityRefresher.lean) |
| `ell^p` definitions | Coordinate `ell^p`/`ell^infty` norms and Minkowski's inequality. | `HDP.Chapter1.lpNorm` | [`Chapter1_AnalysisAndProbabilityRefresher.lean`](Chapter1_AnalysisAndProbabilityRefresher.lean) |
| (1.2) | Euclidean norm squared is the dot product with itself. | `HDP.Chapter1.lpNorm_two_eq_euclidean` | [`Chapter1_AnalysisAndProbabilityRefresher.lean`](Chapter1_AnalysisAndProbabilityRefresher.lean) |
| (1.3) | The `ell^infty` unit ball is the cube and the `ell^1` ball is the cross-polytope. | `HDP.Chapter1.linftyUnitBall_eq_cube` | [`Chapter1_AnalysisAndProbabilityRefresher.lean`](Chapter1_AnalysisAndProbabilityRefresher.lean) |
| (1.4) | `ell^p` norms decrease as `p` increases. | `HDP.Chapter1.lpNorm_anti` | [`Chapter1_AnalysisAndProbabilityRefresher.lean`](Chapter1_AnalysisAndProbabilityRefresher.lean) |
| (1.5) | Holder (including Cauchy--Schwarz and endpoint conjugates). | `HDP.Chapter1.holder_inequality` | [`Chapter1_AnalysisAndProbabilityRefresher.lean`](Chapter1_AnalysisAndProbabilityRefresher.lean) |
| (1.6) | Duality: `‖x‖_p` is the maximum/supremum of pairings over the dual unit ball. | `HDP.Chapter1.exercise_1_19` | [`Chapter1_AnalysisAndProbabilityRefresher.lean`](Chapter1_AnalysisAndProbabilityRefresher.lean) |
| (1.7) | Expectation and variance notation. | `MeasureTheory.integral` | `.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean` |
| Expectation linearity | Finite sums have additive expectation without independence. | `HDP.Chapter1.expectation_linear` | [`Chapter1_AnalysisAndProbabilityRefresher.lean`](Chapter1_AnalysisAndProbabilityRefresher.lean) |
| (1.8) | Variance of a weighted sum of independent/uncorrelated variables. | `HDP.Chapter1.variance_weighted_sum` | [`Chapter1_AnalysisAndProbabilityRefresher.lean`](Chapter1_AnalysisAndProbabilityRefresher.lean) |
| (1.9) | The expectation of an event indicator is its probability. | `HDP.Chapter1.expectation_indicator` | [`Chapter1_AnalysisAndProbabilityRefresher.lean`](Chapter1_AnalysisAndProbabilityRefresher.lean) |
| MGF and moments | Moment-generating function definition. | `HDP.Chapter1.mgf_def'` | [`Chapter1_AnalysisAndProbabilityRefresher.lean`](Chapter1_AnalysisAndProbabilityRefresher.lean) |
| (1.10) | Random-variable `L^p` and essential-supremum norms. | `HDP.Chapter1.lpNormRV` | [`Chapter1_AnalysisAndProbabilityRefresher.lean`](Chapter1_AnalysisAndProbabilityRefresher.lean) |
| (1.11) | `L^2` inner product is `E[XY]`. | `HDP.Chapter1.l2InnerRV` | [`Chapter1_AnalysisAndProbabilityRefresher.lean`](Chapter1_AnalysisAndProbabilityRefresher.lean) |
| (1.12) | Standard deviation equals the `L^2` norm of the centered variable. | `HDP.Chapter1.stdDev_eq_lpNormRV` | [`Chapter1_AnalysisAndProbabilityRefresher.lean`](Chapter1_AnalysisAndProbabilityRefresher.lean) |
| (1.13), vector expectation/covariance | Covariance is the centered `L^2` pairing; vector means and covariance matrices are coordinatewise. | `HDP.Chapter1.covariance_def'` | [`Chapter1_AnalysisAndProbabilityRefresher.lean`](Chapter1_AnalysisAndProbabilityRefresher.lean) |
| Finite additivity | Disjoint finite event families have additive probability. | `HDP.Chapter1.probability_additive` | [`Chapter1_AnalysisAndProbabilityRefresher.lean`](Chapter1_AnalysisAndProbabilityRefresher.lean) |
| (1.14) | The indicator of a union is at most the sum of indicators. | `HDP.Chapter1.indicator_biUnion_le_sum` | [`Chapter1_AnalysisAndProbabilityRefresher.lean`](Chapter1_AnalysisAndProbabilityRefresher.lean) |
| Lemma 1.4.1 | Union bound. | `HDP.Chapter1.union_bound` | [`Chapter1_AnalysisAndProbabilityRefresher.lean`](Chapter1_AnalysisAndProbabilityRefresher.lean) |
| Example 1.4.2 | Dense Erdos--Renyi graphs have no isolated vertices with high probability. | `HDP.Chapter1.example_1_4_2_calc` | [`Chapter1_AnalysisAndProbabilityRefresher.lean`](Chapter1_AnalysisAndProbabilityRefresher.lean) |
| Conditional probability | `P(E given F)=P(E intersection F)/P(F)`. | `HDP.Chapter1.cond_real_def` | [`Chapter1_AnalysisAndProbabilityRefresher.lean`](Chapter1_AnalysisAndProbabilityRefresher.lean) |
| (1.15) | Law of total expectation. | `HDP.Chapter1.law_of_total_expectation` | [`Chapter1_AnalysisAndProbabilityRefresher.lean`](Chapter1_AnalysisAndProbabilityRefresher.lean) |
| (1.16) | Total probability conditioned on a random variable. | `HDP.Chapter1.condProbGiven` | [`Chapter1_AnalysisAndProbabilityRefresher.lean`](Chapter1_AnalysisAndProbabilityRefresher.lean) |
| (1.17) | Total probability over a countable measurable partition. | `HDP.Chapter1.law_of_total_probability` | [`Chapter1_AnalysisAndProbabilityRefresher.lean`](Chapter1_AnalysisAndProbabilityRefresher.lean) |
| Example 1.5.1 | A nontrivial Rademacher sum cancels with probability at most `1/2`; the bound is sharp. | `HDP.Chapter1.example_1_5_1` | [`Chapter1_AnalysisAndProbabilityRefresher.lean`](Chapter1_AnalysisAndProbabilityRefresher.lean) |
| (1.18) | Jensen's inequality for scalar/vector variables, and the concave form. | `HDP.Chapter1.jensen_inequality` | [`Chapter1_AnalysisAndProbabilityRefresher.lean`](Chapter1_AnalysisAndProbabilityRefresher.lean) |
| (1.19) | Norm of an expectation is at most expected norm. | `HDP.Chapter1.norm_expectation_le` | [`Chapter1_AnalysisAndProbabilityRefresher.lean`](Chapter1_AnalysisAndProbabilityRefresher.lean) |
| (1.20) | Probability-space `L^p` norms increase with `p`. | `HDP.Chapter1.exercise_1_11a_eLpNorm` | [`Chapter1_AnalysisAndProbabilityRefresher.lean`](Chapter1_AnalysisAndProbabilityRefresher.lean) |
| (1.21) | Minkowski inequality for random variables. | `HDP.Chapter1.minkowski_eLpNorm` | [`Chapter1_AnalysisAndProbabilityRefresher.lean`](Chapter1_AnalysisAndProbabilityRefresher.lean) |
| (1.22) | Holder and Cauchy--Schwarz for random variables. | `HDP.Chapter1.holder_rv` | [`Chapter1_AnalysisAndProbabilityRefresher.lean`](Chapter1_AnalysisAndProbabilityRefresher.lean) |
| CDF/tail identity | `P(X>t)=1-F_X(t)`. | `HDP.Chapter1.bookCDF` | [`Chapter1_AnalysisAndProbabilityRefresher.lean`](Chapter1_AnalysisAndProbabilityRefresher.lean) |
| Lemma 1.6.1 | Integrated-tail formula `E X = integral P(X>t) dt` for nonnegative `X`. | `HDP.Chapter1.integrated_tail_formula_lintegral` | [`Chapter1_AnalysisAndProbabilityRefresher.lean`](Chapter1_AnalysisAndProbabilityRefresher.lean) |
| Proposition 1.6.2 | Markov inequality. | `HDP.Chapter1.markov_inequality` | [`Chapter1_AnalysisAndProbabilityRefresher.lean`](Chapter1_AnalysisAndProbabilityRefresher.lean) |
| §1.6, Markov optimality | The Markov tail bound is attained by a two-point law when only the mean is prescribed. | `HDP.Chapter1.markov_inequality_is_sharp` | [`Chapter1_AnalysisAndProbabilityRefresher.lean`](Chapter1_AnalysisAndProbabilityRefresher.lean) |
| Corollary 1.6.3 | Chebyshev inequality. | `HDP.Chapter1.chebyshev_inequality` | [`Chapter1_AnalysisAndProbabilityRefresher.lean`](Chapter1_AnalysisAndProbabilityRefresher.lean) |
| (1.23) | The variance of an i.i.d. sample mean is `sigma^2/n`. | `HDP.Chapter1.variance_sample_mean` | [`Chapter1_AnalysisAndProbabilityRefresher.lean`](Chapter1_AnalysisAndProbabilityRefresher.lean) |
| Theorem 1.7.1 | Strong law of large numbers. | `HDP.Chapter1.strong_law_of_large_numbers` | [`Chapter1_AnalysisAndProbabilityRefresher.lean`](Chapter1_AnalysisAndProbabilityRefresher.lean) |
| Convergence-in-distribution definition | CDFs converge at continuity points of the limit law. | `MeasureTheory.TendstoInDistribution` | `.lake/packages/mathlib/Mathlib/MeasureTheory/Function/ConvergenceInDistribution.lean` |
| Definition 1.7.2; (1.24) | Standard/general normal laws, densities, means, and variances. | `HDP.Chapter1.stdGaussian_density` | [`Chapter1_AnalysisAndProbabilityRefresher.lean`](Chapter1_AnalysisAndProbabilityRefresher.lean) |
| Theorem 1.7.3 | Lindeberg--Levy CLT. | `HDP.Chapter1.central_limit_theorem` | [`Chapter1_AnalysisAndProbabilityRefresher.lean`](Chapter1_AnalysisAndProbabilityRefresher.lean) |
| Example 1.7.4; (1.25) | Bernoulli/binomial moments and de Moivre--Laplace convergence. | `HDP.IsBernoulli` | [`Chapter1_AnalysisAndProbabilityRefresher.lean`](Chapter1_AnalysisAndProbabilityRefresher.lean) |
| Definition 1.7.5; (1.26) | Poisson distribution and PMF. | `HDP.Chapter1.IsPoissonRV` | [`Chapter1_AnalysisAndProbabilityRefresher.lean`](Chapter1_AnalysisAndProbabilityRefresher.lean) |
| Lemma 1.7.7 | Stirling asymptotic. | `HDP.Chapter1.stirling_approximation` | [`Chapter1_AnalysisAndProbabilityRefresher.lean`](Chapter1_AnalysisAndProbabilityRefresher.lean) |
| (1.27) | Fixed-parameter Poisson PMF asymptotic. | `HDP.Chapter1.poisson_pmf_asymptotic` | [`Chapter1_AnalysisAndProbabilityRefresher.lean`](Chapter1_AnalysisAndProbabilityRefresher.lean) |
| Lemma 1.7.8; (1.28) | Elementary lower/upper factorial bounds. | `HDP.Chapter1.factorial_lower_bound` | [`Chapter1_AnalysisAndProbabilityRefresher.lean`](Chapter1_AnalysisAndProbabilityRefresher.lean) |
| (1.29) | Log-factorial sum and integral upper estimate. | `HDP.Chapter1.log_factorial_eq_sum` | [`Chapter1_AnalysisAndProbabilityRefresher.lean`](Chapter1_AnalysisAndProbabilityRefresher.lean) |
| Remark 1.7.9; (1.30) | Gamma integral and `Gamma(n+1)=n!`, real and complex. | `HDP.Chapter1.gamma_def` | [`Chapter1_AnalysisAndProbabilityRefresher.lean`](Chapter1_AnalysisAndProbabilityRefresher.lean) |
| (1.31) | Stirling asymptotic for Gamma. | `HDP.Chapter1.log_gamma_stirling` | [`Chapter1_AnalysisAndProbabilityRefresher.lean`](Chapter1_AnalysisAndProbabilityRefresher.lean) |

### Chapter 2 — Concentration of Sums of Independent Random Variables

| Book source | Result | Lean declaration | Final module |
|---|---|---|---|
| Question 2.1.1; (2.1) | Chebyshev gives `P(S_N >= 3N/4) <= 4/N` for independent fair coins. | `HDP.Chapter2.fair_coin_chebyshev_equation_2_1` | [`Chapter2_ConcentrationOfIndependentSums.lean`](Chapter2_ConcentrationOfIndependentSums.lean) |
| Proposition 2.1.2; (2.3) | Two-sided Mills-style Gaussian tail bounds, including `P(g>=t) <= phi(t)/t`. | `HDP.Chapter2.gaussian_tail_upper` | [`Chapter2_ConcentrationOfIndependentSums.lean`](Chapter2_ConcentrationOfIndependentSums.lean) |
| (2.4) | Heuristic probability of at least `3N/4` heads is about `exp(-N/8)/sqrt(2pi)`. | `HDP.Chapter2.remark_2_2_4` | [`Chapter2_ConcentrationOfIndependentSums.lean`](Chapter2_ConcentrationOfIndependentSums.lean) |
| Central-binomial paragraph | `P(S_N=N/2)` is asymptotic to `sqrt(2/(pi N))`, showing the `N^-1/2` CLT-error scale is unavoidable. | `HDP.Chapter2.centralBinomialProbability_asymptotic` | [`Chapter2_ConcentrationOfIndependentSums.lean`](Chapter2_ConcentrationOfIndependentSums.lean) |
| Theorem 2.2.1 | Hoeffding inequality for weighted independent Rademachers. | `HDP.Chapter2.hoeffding_rademacher` | [`Chapter2_ConcentrationOfIndependentSums.lean`](Chapter2_ConcentrationOfIndependentSums.lean) |
| (2.5) | Exponential Markov step for a Rademacher sum. | `HDP.Chapter2.hoeffding_rademacher` | [`Chapter2_ConcentrationOfIndependentSums.lean`](Chapter2_ConcentrationOfIndependentSums.lean) |
| (2.6) | Independence factors the MGF of a sum into a product. | `HDP.Chapter2.mgf_rademacher_scaled` | [`Chapter2_ConcentrationOfIndependentSums.lean`](Chapter2_ConcentrationOfIndependentSums.lean) |
| (2.7) | `cosh x <= exp(x^2/2)`. | `HDP.Chapter2.exercise_2_5` | [`Chapter2_ConcentrationOfIndependentSums.lean`](Chapter2_ConcentrationOfIndependentSums.lean) |
| (2.8) | The optimized exponential bound is `exp(-lambda t + lambda^2 ‖a‖_2^2/2)`. | `HDP.Chapter2.hoeffding_rademacher` | [`Chapter2_ConcentrationOfIndependentSums.lean`](Chapter2_ConcentrationOfIndependentSums.lean) |
| Remark 2.2.2 | Hoeffding gives Gaussian-like exponentially light tails. | `HDP.Chapter2.hoeffding_rademacher` | [`Chapter2_ConcentrationOfIndependentSums.lean`](Chapter2_ConcentrationOfIndependentSums.lean) |
| Remark 2.2.4 | A rigorous exponentially small bound for `3N/4` heads. | `HDP.Chapter2.remark_2_2_4` | [`Chapter2_ConcentrationOfIndependentSums.lean`](Chapter2_ConcentrationOfIndependentSums.lean) |
| Theorem 2.2.5 | Two-sided Hoeffding for Rademacher sums. | `HDP.Chapter2.hoeffding_rademacher_two_sided` | [`Chapter2_ConcentrationOfIndependentSums.lean`](Chapter2_ConcentrationOfIndependentSums.lean) |
| Theorem 2.2.6 | Hoeffding for independent centered bounded variables. | `HDP.Chapter2.exercise_2_8` | [`Chapter2_ConcentrationOfIndependentSums.lean`](Chapter2_ConcentrationOfIndependentSums.lean) |
| Theorem 2.3.1 | Chernoff upper-tail inequality for sums of independent Bernoulli variables. | `HDP.Chapter2.chernoff_upper` | [`Chapter2_ConcentrationOfIndependentSums.lean`](Chapter2_ConcentrationOfIndependentSums.lean) |
| (2.9) | Exponential Markov plus Bernoulli-MGF product. | `HDP.Chapter2.mgf_bernoulli_sum_le` | [`Chapter2_ConcentrationOfIndependentSums.lean`](Chapter2_ConcentrationOfIndependentSums.lean) |
| Remark 2.3.2 | Chernoff left-tail inequality. | `HDP.Chapter2.chernoff_lower` | [`Chapter2_ConcentrationOfIndependentSums.lean`](Chapter2_ConcentrationOfIndependentSums.lean) |
| (2.10) | Relative-entropy Chernoff bound before the quadratic simplification. | `HDP.Chapter2.chernoff_relative_entropy_bound` | [`Chapter2_ConcentrationOfIndependentSums.lean`](Chapter2_ConcentrationOfIndependentSums.lean) |
| Corollary 2.3.4 | Two-sided small-deviation Chernoff bound. | `HDP.Chapter2.chernoff_small_deviations` | [`Chapter2_ConcentrationOfIndependentSums.lean`](Chapter2_ConcentrationOfIndependentSums.lean) |
| (2.11) | Definition of the sample mean estimator. | `HDP.Chapter1.variance_sample_mean` | [`Chapter1_AnalysisAndProbabilityRefresher.lean`](Chapter1_AnalysisAndProbabilityRefresher.lean) |
| (2.12) | Sample mean has mean `mu` and variance `sigma^2/N`. | `HDP.Chapter1.expectation_linear` | [`Chapter1_AnalysisAndProbabilityRefresher.lean`](Chapter1_AnalysisAndProbabilityRefresher.lean) |
| (2.13) | Chebyshev tail for the sample mean. | `HDP.Chapter1.chebyshev_inequality` | [`Chapter1_AnalysisAndProbabilityRefresher.lean`](Chapter1_AnalysisAndProbabilityRefresher.lean) |
| Section 2.4 | Replacing one observation can make a median lose at most one lower- and one upper-half rank witness. | `HDP.Chapter2.median_one_coordinate_robust` | [`Chapter2_ConcentrationOfIndependentSums.lean`](Chapter2_ConcentrationOfIndependentSums.lean) |
| Theorem 2.4.1 | Median-of-means achieves a Gaussian tail assuming only finite variance. | `HDP.Chapter2.medianOfMeans_explicit` | [`Chapter2_ConcentrationOfIndependentSums.lean`](Chapter2_ConcentrationOfIndependentSums.lean) |
| Proposition 2.5.1 | If expected degree is at least `C log n`, all Erdos--Renyi degrees lie within 10% of the mean with probability at least `.99`. | `HDP.Chapter2.dense_graphs_almost_regular_explicit` | [`Chapter2_ConcentrationOfIndependentSums.lean`](Chapter2_ConcentrationOfIndependentSums.lean) |
| Remark 2.5.2 | Below `(1-epsilon) log n`, isolated vertices appear, so sparse random graphs are far from regular. | `HDP.Chapter1.exercise_1_9` | [`Chapter1_AnalysisAndProbabilityRefresher.lean`](Chapter1_AnalysisAndProbabilityRefresher.lean) |
| (2.14) | Weighted Hoeffding-type tail for the class motivating subgaussianity. | `HDP.subgaussian_hoeffding` | [`Chapter2_ConcentrationOfIndependentSums.lean`](Chapter2_ConcentrationOfIndependentSums.lean) |
| (2.15) | Subgaussian tail definition `P(abs(X)>t) <= 2 exp(-c t^2)`. | `HDP.SubGaussian` | [`Chapter2_ConcentrationOfIndependentSums.lean`](Chapter2_ConcentrationOfIndependentSums.lean) |
| (2.16) | Standard Gaussian MGF is `exp(lambda^2/2)`. | `HDP.Chapter2.gaussian_mgf` | [`Chapter2_ConcentrationOfIndependentSums.lean`](Chapter2_ConcentrationOfIndependentSums.lean) |
| (2.17) | Gaussian `L^p` norms grow like `sqrt(p)`. | `HDP.Chapter2.gaussian_absolute_moment` | [`Chapter2_ConcentrationOfIndependentSums.lean`](Chapter2_ConcentrationOfIndependentSums.lean) |
| Proposition 2.6.1 | Tail, moment, square-exponential, and centered-MGF definitions of subgaussianity are equivalent. | `HDP.subgaussian_i_to_iii` | [`Chapter2_ConcentrationOfIndependentSums.lean`](Chapter2_ConcentrationOfIndependentSums.lean) |
| Remark 2.6.2 | The all-`lambda` quadratic MGF bound forces mean zero. | `HDP.exercise_2_23` | [`Chapter2_ConcentrationOfIndependentSums.lean`](Chapter2_ConcentrationOfIndependentSums.lean) |
| Remark 2.6.3 | The normalization constant `2` in the equivalent definitions can be replaced by any absolute constant greater than one. | `HDP.remark_2_6_3_i` | [`Chapter2_ConcentrationOfIndependentSums.lean`](Chapter2_ConcentrationOfIndependentSums.lean) |
| Definition 2.6.4; (2.18) | Subgaussian variables and the `psi_2` infimum norm. | `HDP.SubGaussian` | [`Chapter2_ConcentrationOfIndependentSums.lean`](Chapter2_ConcentrationOfIndependentSums.lean) |
| `psi_2` triangle/norm prose | `psi_2` is a norm, including triangle inequality without independence. | `HDP.psi2Norm_eq_zero_iff` | [`Chapter2_ConcentrationOfIndependentSums.lean`](Chapter2_ConcentrationOfIndependentSums.lean) |
| Proposition 2.6.6 | Tail, moment, square-MGF, and centered-MGF bounds in terms of the `psi_2` norm, with converse optimality up to constants. | `HDP.SubGaussian.tail_bound` | [`Chapter2_ConcentrationOfIndependentSums.lean`](Chapter2_ConcentrationOfIndependentSums.lean) |
| (2.19) | Pythagorean identity for independent centered scalar sums. | `HDP.pythagorean_identity` | [`Chapter2_ConcentrationOfIndependentSums.lean`](Chapter2_ConcentrationOfIndependentSums.lean) |
| Proposition 2.7.1 | `psi_2` norm squared of an independent centered sum is bounded by a constant times the sum of squared norms. | `HDP.psi2Norm_sum_sq_le` | [`Chapter2_ConcentrationOfIndependentSums.lean`](Chapter2_ConcentrationOfIndependentSums.lean) |
| Theorem 2.7.3 | Subgaussian Hoeffding inequality. | `HDP.subgaussian_hoeffding` | [`Chapter2_ConcentrationOfIndependentSums.lean`](Chapter2_ConcentrationOfIndependentSums.lean) |
| Example 2.7.4; (2.20) | Applying the subgaussian theorem to weighted Rademachers recovers classical Hoeffding up to constants. | `HDP.example_2_7_4` | [`Chapter2_ConcentrationOfIndependentSums.lean`](Chapter2_ConcentrationOfIndependentSums.lean) |
| Theorem 2.7.5 | Khintchine inequality for independent centered subgaussian variables. | `HDP.khintchine` | [`Chapter2_ConcentrationOfIndependentSums.lean`](Chapter2_ConcentrationOfIndependentSums.lean) |
| Proposition 2.7.6; (2.21) | The `psi_2` norm of a finite maximum grows like `sqrt(log N)` times the largest individual norm. | `HDP.psi2Norm_max_abs_le` | [`Chapter2_ConcentrationOfIndependentSums.lean`](Chapter2_ConcentrationOfIndependentSums.lean) |
| Proposition 2.7.6; (2.22) | Expected maximum has the corresponding `sqrt(log N)` bound. | `HDP.expectation_max_le` | [`Chapter2_ConcentrationOfIndependentSums.lean`](Chapter2_ConcentrationOfIndependentSums.lean) |
| Remark 2.7.7 | Gaussian samples have no outliers; maxima are of order `sqrt(log N)`, sharply so for independent samples. | `HDP.Chapter2.exercise_2_38a_max` | [`Chapter2_ConcentrationOfIndependentSums.lean`](Chapter2_ConcentrationOfIndependentSums.lean) |
| (2.23) | Centering cannot increase the `L^2` norm. | `HDP.centering_L2` | [`Chapter2_ConcentrationOfIndependentSums.lean`](Chapter2_ConcentrationOfIndependentSums.lean) |
| Lemma 2.7.8; (2.24) | Centering a subgaussian variable preserves subgaussianity and controls its `psi_2` norm. | `HDP.psi2Norm_centering` | [`Chapter2_ConcentrationOfIndependentSums.lean`](Chapter2_ConcentrationOfIndependentSums.lean) |
| Proposition 2.8.1 | Tail, moment, exponential-integrability, and local-MGF definitions of subexponentiality are equivalent. | `HDP.subexponential_i_to_iii` | [`Chapter2_ConcentrationOfIndependentSums.lean`](Chapter2_ConcentrationOfIndependentSums.lean) |
| Remark 2.8.3 | The MGF of `Exp(1)` diverges for `lambda>=1`. | `HDP.exponential_mgf_diverges` | [`Chapter2_ConcentrationOfIndependentSums.lean`](Chapter2_ConcentrationOfIndependentSums.lean) |
| Definition 2.8.4; (2.25) | Subexponential variables and the `psi_1` infimum norm. | `HDP.SubExponential` | [`Chapter2_ConcentrationOfIndependentSums.lean`](Chapter2_ConcentrationOfIndependentSums.lean) |
| Lemma 2.8.5 | `X` is subgaussian iff `X^2` is subexponential, with squared norm identity. | `HDP.subExponential_sq_iff` | [`Chapter2_ConcentrationOfIndependentSums.lean`](Chapter2_ConcentrationOfIndependentSums.lean) |
| Lemma 2.8.6 | Product of two subgaussians is subexponential with `psi_1` product bound. | `HDP.psi1Norm_mul_le` | [`Chapter2_ConcentrationOfIndependentSums.lean`](Chapter2_ConcentrationOfIndependentSums.lean) |
| (2.26) | Centering preserves `psi_1` up to an absolute constant. | `HDP.psi1Norm_centering` | [`Chapter2_ConcentrationOfIndependentSums.lean`](Chapter2_ConcentrationOfIndependentSums.lean) |
| Remark 2.8.8 | Bounded => subgaussian => subexponential => all moments => finite variance => finite mean, with norm comparisons. | `HDP.bounded_to_subGaussian` | [`Chapter2_ConcentrationOfIndependentSums.lean`](Chapter2_ConcentrationOfIndependentSums.lean) |
| Remark 2.8.9 | `psi_alpha`/Orlicz norms generalize `psi_1` and `psi_2`. | `HDP.isOrliczNorm` | [`Prelude/Orlicz.lean`](Prelude/Orlicz.lean) |
| Theorem 2.9.1 | Bernstein inequality for independent centered subexponential variables. | `HDP.bernstein_inequality` | [`Chapter2_ConcentrationOfIndependentSums.lean`](Chapter2_ConcentrationOfIndependentSums.lean) |
| (2.27) | Exponential Markov/product step in Bernstein's proof. | `HDP.bernstein_inequality` | [`Chapter2_ConcentrationOfIndependentSums.lean`](Chapter2_ConcentrationOfIndependentSums.lean) |
| (2.28) | The optimization parameter is constrained by the largest `psi_1` norm. | `HDP.SubExponential.mgf_bound` | [`Chapter2_ConcentrationOfIndependentSums.lean`](Chapter2_ConcentrationOfIndependentSums.lean) |
| Corollary 2.9.2 | Weighted/simplified Bernstein inequality. | `HDP.bernstein_weighted` | [`Chapter2_ConcentrationOfIndependentSums.lean`](Chapter2_ConcentrationOfIndependentSums.lean) |
| Remark 2.9.4 | Normalized Bernstein has Gaussian small deviations and exponential large deviations. | `HDP.remark_2_9_4` | [`Chapter2_ConcentrationOfIndependentSums.lean`](Chapter2_ConcentrationOfIndependentSums.lean) |
| Theorem 2.9.5 | Variance-sensitive Bernstein inequality for bounded variables. | `HDP.bernstein_bounded_variance` | [`Chapter2_ConcentrationOfIndependentSums.lean`](Chapter2_ConcentrationOfIndependentSums.lean) |

### Chapter 3 — Random Vectors in High Dimensions

| Book source | Result | Lean declaration | Final module |
|---|---|---|---|
| Theorem 3.1.1; (3.1) | A vector with independent, unit-second-moment, `K`-subgaussian coordinates has `‖X‖_2` concentrated around `sqrt(n)` with `psi_2` scale `C K^2`. | `HDP.Chapter3.concentration_norm` | [`Chapter3_RandomVectorsInHighDimensions.lean`](Chapter3_RandomVectorsInHighDimensions.lean) |
| (3.2) | Equivalent Gaussian tail for `abs(‖X‖_2-sqrt(n))`. | `HDP.Chapter3.concentration_norm` | [`Chapter3_RandomVectorsInHighDimensions.lean`](Chapter3_RandomVectorsInHighDimensions.lean) |
| (3.3) | Bernstein controls the centered squared norm with a mixed quadratic/linear tail. | `HDP.Chapter3.norm_sq_bernstein` | [`Chapter3_RandomVectorsInHighDimensions.lean`](Chapter3_RandomVectorsInHighDimensions.lean) |
| (3.4) | For nonnegative `z`, `abs(z-1)>=delta` implies `abs(z^2-1)>=max(delta,delta^2)`. | `HDP.Chapter3.max_le_abs_sq_sub_one` | [`Chapter3_RandomVectorsInHighDimensions.lean`](Chapter3_RandomVectorsInHighDimensions.lean) |
| Remark 3.1.2 | Thin-shell phenomenon and bounded radial variance follow from norm concentration. | `HDP.Chapter3.thinShellVariance_subGaussian` | [`Chapter3_RandomVectorsInHighDimensions.lean`](Chapter3_RandomVectorsInHighDimensions.lean) |
| (3.5) | Covariance-matrix entries are coordinate covariances. | `HDP.Chapter3.covarianceMatrix_apply` | [`Chapter3_RandomVectorsInHighDimensions.lean`](Chapter3_RandomVectorsInHighDimensions.lean) |
| Section 3.2, covariance prose | `Cov(X)=E[XX^T]-(EX)(EX)^T`, and zero mean reduces covariance to the second moment. | `HDP.Chapter3.covarianceMatrix_eq_secondMoment_sub_mean` | [`Chapter3_RandomVectorsInHighDimensions.lean`](Chapter3_RandomVectorsInHighDimensions.lean) |
| Proposition 3.2.1(a); (3.6) | `E <X,v>^2 = v^T Sigma v` for the second-moment matrix. | `HDP.Chapter3.secondMoment_inner_sq` | [`Chapter3_RandomVectorsInHighDimensions.lean`](Chapter3_RandomVectorsInHighDimensions.lean) |
| Proposition 3.2.1(b) | `E ‖X‖_2^2 = tr(Sigma)`. | `HDP.Chapter3.secondMoment_norm_sq_eq_trace` | [`Chapter3_RandomVectorsInHighDimensions.lean`](Chapter3_RandomVectorsInHighDimensions.lean) |
| Proposition 3.2.1(c) | For independent copies `X,Y`, `E<X,Y>^2` is the squared Frobenius norm of the second-moment matrix. | `HDP.Chapter3.secondMoment_independent_copy_inner_sq` | [`Chapter3_RandomVectorsInHighDimensions.lean`](Chapter3_RandomVectorsInHighDimensions.lean) |
| (3.7) | Spectral decomposition of a symmetric matrix into orthonormal eigenvectors. | `LinearMap.IsSymmetric.eigenvectorBasis` | `.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Spectrum.lean` |
| Proposition 3.2.2; (3.8) | The `k`th eigenvalue is the maximum Rayleigh quotient on the orthogonal complement of earlier eigenvectors. | `HDP.Chapter3.pca_kth_component_le` | [`Chapter3_RandomVectorsInHighDimensions.lean`](Chapter3_RandomVectorsInHighDimensions.lean) |
| Corollary 3.2.3 | The `k`th covariance eigenvalue is the maximum variance of a unit projection orthogonal to preceding principal components, attained by the `k`th eigenvector. | `HDP.Chapter3.covariance_pca_kth_maximum` | [`Chapter3_RandomVectorsInHighDimensions.lean`](Chapter3_RandomVectorsInHighDimensions.lean) |
| Definition 3.2.5; (3.9) | Isotropy means `E[XX^T]=I`, equivalently `E<X,v>^2=‖v‖^2`. | `HDP.IsIsotropic` | [`Prelude/RandomVector.lean`](Prelude/RandomVector.lean) |
| (3.10) | Standard-score/whitening transform and affine reconstruction. | `HDP.Chapter3.exercise_3_10a` | [`Chapter3_RandomVectorsInHighDimensions.lean`](Chapter3_RandomVectorsInHighDimensions.lean) |
| (3.11) | Standard multivariate Gaussian density is proportional to `exp(-‖z‖^2/2)`. | `HDP.Chapter3.exercise_3_15_standardDensity` | [`Chapter3_RandomVectorsInHighDimensions.lean`](Chapter3_RandomVectorsInHighDimensions.lean) |
| Proposition 3.3.1 | Standard Gaussian law is rotation invariant. | `HDP.Chapter3.standardGaussian_rotation_invariant` | [`Chapter3_RandomVectorsInHighDimensions.lean`](Chapter3_RandomVectorsInHighDimensions.lean) |
| Definition 3.3.4 | A general Gaussian vector is exactly an arbitrary rectangular affine image `μ+AZ` of a standard Gaussian, with covariance `AAᵀ`. | `HDP.Chapter3.hasGaussianVectorLaw_iff_affineRepresentation` | [`Chapter3_RandomVectorsInHighDimensions.lean`](Chapter3_RandomVectorsInHighDimensions.lean) |
| Corollary 3.3.2 | Every standard-Gaussian marginal `<Z,v>` is Gaussian with variance `‖v‖^2`. | `HDP.Chapter3.standardGaussian_inner_hasLaw` | [`Chapter3_RandomVectorsInHighDimensions.lean`](Chapter3_RandomVectorsInHighDimensions.lean) |
| Corollary 3.3.3 | A finite sum of independent real Gaussians is Gaussian, with summed mean and summed variance. | `HDP.Chapter3.sum_independent_gaussians_parameters` | [`Chapter3_RandomVectorsInHighDimensions.lean`](Chapter3_RandomVectorsInHighDimensions.lean) |
| Proposition 3.3.5; (3.12) | Gaussian law is uniquely determined by mean and covariance, including singular covariance. | `HDP.Chapter3.gaussianLaw_unique` | [`Chapter3_RandomVectorsInHighDimensions.lean`](Chapter3_RandomVectorsInHighDimensions.lean) |
| Proposition 3.3.6; (3.13) | Invertible-covariance multivariate Gaussian density formula. | `HDP.Chapter3.multivariateGaussianDensity` | [`Chapter3_RandomVectorsInHighDimensions.lean`](Chapter3_RandomVectorsInHighDimensions.lean) |
| Corollary 3.3.7 | Jointly Gaussian variables are independent iff uncorrelated. | `ProbabilityTheory.HasGaussianLaw.iIndepFun_of_covariance_strongDual` | `.lake/packages/mathlib/Mathlib/Probability/Distributions/Gaussian/HasGaussianLaw/Independence.lean` |
| Proposition 3.3.8 | The uniform law on `sqrt(n) S^{n-1}` is isotropic. | `HDP.Chapter3.sphere_isIsotropic` | [`Chapter3_RandomVectorsInHighDimensions.lean`](Chapter3_RandomVectorsInHighDimensions.lean) |
| Eq. (3.14) | Independent uniform unit directions have squared inner-product mean `1/n` and satisfy `P{|⟨X,Y⟩|≥C/√n}≤1/C²`. | `HDP.Chapter3.uniformSphere_inner_sq_expectation`, `HDP.Chapter3.uniformSphere_almost_orthogonal` | [`Chapter3_RandomVectorsInHighDimensions.lean`](Chapter3_RandomVectorsInHighDimensions.lean) |
| (3.15) | A normalized standard Gaussian direction is uniform on the sphere. | `HDP.map_gaussianDirection_stdGaussian` | [`Prelude/Sphere.lean`](Prelude/Sphere.lean) |
| (3.16) | Standard-Gaussian norm concentrates around `sqrt(n)`. | `HDP.Chapter3.stdGaussian_norm_deviation_tail` | [`Chapter3_RandomVectorsInHighDimensions.lean`](Chapter3_RandomVectorsInHighDimensions.lean) |
| Theorem 3.3.9 | Projective CLT: all one-dimensional marginals of the high-dimensional sphere converge to standard normal. | `HDP.Chapter3.projectiveCentralLimitTheorem` | [`Chapter3_RandomVectorsInHighDimensions.lean`](Chapter3_RandomVectorsInHighDimensions.lean) |
| Remark 3.3.10 | Exact one-dimensional marginal densities for uniform sphere/ball laws. | `HDP.sphereMarginalDensity` | [`Chapter3_RandomVectorsInHighDimensions.lean`](Chapter3_RandomVectorsInHighDimensions.lean) |
| Proposition 3.3.11 | Parseval frames are equivalent to isotropic finite-support distributions. | `HDP.IsParsevalFrame` | [`Chapter3_RandomVectorsInHighDimensions.lean`](Chapter3_RandomVectorsInHighDimensions.lean) |
| Example 3.3.12 | Coordinate distribution is a Parseval frame/isotropic law. | `HDP.Chapter3.coordinateParsevalFrame` | [`Chapter3_RandomVectorsInHighDimensions.lean`](Chapter3_RandomVectorsInHighDimensions.lean) |
| Example 3.3.13 | Mercedes--Benz frame is Parseval. | `HDP.Chapter3.mercedesBenzFrame` | [`Chapter3_RandomVectorsInHighDimensions.lean`](Chapter3_RandomVectorsInHighDimensions.lean) |
| Example 3.3.14 | Uniform discrete-cube/Rademacher vector is isotropic. | `HDP.Chapter3.rademacherVector_isIsotropic` | [`Chapter3_RandomVectorsInHighDimensions.lean`](Chapter3_RandomVectorsInHighDimensions.lean) |
| Example 3.3.15 | Independent centered unit-variance coordinates form an isotropic vector. | `HDP.Chapter3.independent_centered_unitVariance_isIsotropic` | [`Chapter3_RandomVectorsInHighDimensions.lean`](Chapter3_RandomVectorsInHighDimensions.lean) |
| Definition 3.4.1 | A vector is subgaussian if every one-dimensional marginal is; its vector `psi_2` norm is the supremum over unit directions. | `HDP.SubGaussianVector` | [`Prelude/RandomVector.lean`](Prelude/RandomVector.lean) |
| Lemma 3.4.2 | Independent subgaussian coordinates give a subgaussian vector; vector norm is comparable to the largest coordinate norm. | `HDP.Chapter3.subGaussianVector_of_independent_coordinates` | [`Chapter3_RandomVectorsInHighDimensions.lean`](Chapter3_RandomVectorsInHighDimensions.lean) |
| Example 3.4.3 | Rademacher vector is subgaussian with bounded vector norm. | `HDP.Chapter3.rademacherVector_subGaussian` | [`Chapter3_RandomVectorsInHighDimensions.lean`](Chapter3_RandomVectorsInHighDimensions.lean) |
| Example 3.4.4 | Standard Gaussian vector has constant vector `psi_2` norm. | `HDP.Chapter3.psi2NormVector_standardGaussian` | [`Chapter3_RandomVectorsInHighDimensions.lean`](Chapter3_RandomVectorsInHighDimensions.lean) |
| Theorem 3.5.1 | Real Grothendieck inequality with an absolute constant at most `1.783`. | `HDP.Chapter3.grothendieck_inequality` | [`Chapter3_RandomVectorsInHighDimensions.lean`](Chapter3_RandomVectorsInHighDimensions.lean) |
| Remark 3.5.2; (3.22)--(3.23) | Homogeneous scalar and Hilbert-vector forms of Grothendieck. | `HDP.Chapter3.grothendieck_homogeneous` | [`Chapter3_RandomVectorsInHighDimensions.lean`](Chapter3_RandomVectorsInHighDimensions.lean) |
| (3.24) | Raw Gaussian correlations satisfy `E[U_i V_j]=<u_i,v_j>`, turning the bilinear sum into an expectation. | `ProbabilityTheory.covarianceBilin_stdGaussian` | `.lake/packages/mathlib/Mathlib/Probability/Distributions/Gaussian/Multivariate.lean` |
| Remark 3.5.3 | Quadratic Grothendieck bounds for PSD and symmetric diagonal-free matrices. | `HDP.Chapter3.quadratic_grothendieck_psd` | [`Chapter3_RandomVectorsInHighDimensions.lean`](Chapter3_RandomVectorsInHighDimensions.lean) |
| Definition 3.5.4; (3.26) | Generic semidefinite-program schema: linear matrix objective, PSD variable, linear constraints. | `HDP.SemidefiniteProgram` | [`Chapter3_RandomVectorsInHighDimensions.lean`](Chapter3_RandomVectorsInHighDimensions.lean) |
| (3.27) | Matrix inner product is `tr(A^T X)=sum A_ij X_ij`. | `HDP.matrixInner` | [`Chapter3_RandomVectorsInHighDimensions.lean`](Chapter3_RandomVectorsInHighDimensions.lean) |
| Remark 3.5.5 | SDP feasible sets are convex. | `HDP.convex_posSemidefiniteMatrices` | [`Chapter3_RandomVectorsInHighDimensions.lean`](Chapter3_RandomVectorsInHighDimensions.lean) |
| (3.28) | Integer quadratic optimization over signs. | `HDP.quadraticObjective` | [`Chapter3_RandomVectorsInHighDimensions.lean`](Chapter3_RandomVectorsInHighDimensions.lean) |
| (3.29) | Vector/Gram SDP relaxation over unit vectors. | `HDP.vectorSDPObjective` | [`Chapter3_RandomVectorsInHighDimensions.lean`](Chapter3_RandomVectorsInHighDimensions.lean) |
| Proposition 3.5.6; (3.30) | The vector relaxation is equivalent to the PSD matrix SDP with diagonal one. | `HDP.Chapter3.relaxation_is_sdp` | [`Chapter3_RandomVectorsInHighDimensions.lean`](Chapter3_RandomVectorsInHighDimensions.lean) |
| Theorem 3.5.7 | For symmetric PSD `A`, attained maxima satisfy `int(A)<=sdp(A)<=2K int(A)`. | `HDP.Chapter3.sdp_relaxation_guarantee` | [`Chapter3_RandomVectorsInHighDimensions.lean`](Chapter3_RandomVectorsInHighDimensions.lean) |
| Definition 3.6.1 | Cut size and maximum cut of a finite graph. | `HDP.SimpleGraph.cutSize` | [`Prelude/SimpleGraph.lean`](Prelude/SimpleGraph.lean) |
| Definition 3.6.2 | Adjacency matrix of a finite graph. | `SimpleGraph.adjMatrix` | `.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/AdjMatrix.lean` |
| (3.34) | Gaussian hyperplane rounding labels each vertex by `sign <X_i,g>`. | `HDP.Chapter3.gaussianRoundingLabel` | [`Chapter3_RandomVectorsInHighDimensions.lean`](Chapter3_RandomVectorsInHighDimensions.lean) |
| Lemma 3.6.5 | Grothendieck sign/arcsine identity for correlated Gaussian signs. | `HDP.Chapter3.grothendieckSignArcsin` | [`Chapter3_RandomVectorsInHighDimensions.lean`](Chapter3_RandomVectorsInHighDimensions.lean) |
| (3.35) | `2 arccos(t)/pi >= .878(1-t)` on `[-1,1]`. | `HDP.Chapter3.goemansWilliamson_pairwise_bound` | [`Chapter3_RandomVectorsInHighDimensions.lean`](Chapter3_RandomVectorsInHighDimensions.lean) |
| Example 3.7.3 | Rank-one tensor power `u^{tensor k}`. | `HDP.tensorPowerFeature` | [`Chapter3_RandomVectorsInHighDimensions.lean`](Chapter3_RandomVectorsInHighDimensions.lean) |
| Lemma 3.7.4 | Inner products of tensor powers satisfy `<u^k,v^k>=<u,v>^k`. | `HDP.inner_tensorPowerFeature` | [`Chapter3_RandomVectorsInHighDimensions.lean`](Chapter3_RandomVectorsInHighDimensions.lean) |
| Example 3.7.5 | A polynomial with nonnegative coefficients has a Hilbert feature map. | `HDP.inner_analyticFeature_of_nonneg` | [`Chapter3_RandomVectorsInHighDimensions.lean`](Chapter3_RandomVectorsInHighDimensions.lean) |
| Example 3.7.6 | General signed coefficients admit two feature maps with the desired cross-inner-product. | `HDP.inner_analyticFeature_signedAnalyticFeature` | [`Chapter3_RandomVectorsInHighDimensions.lean`](Chapter3_RandomVectorsInHighDimensions.lean) |
| Example 3.7.8 | Sine admits signed feature maps; choosing `c=log(1+sqrt(2))` normalizes via `sinh c=1`. | `HDP.sineFeature` | [`Chapter3_RandomVectorsInHighDimensions.lean`](Chapter3_RandomVectorsInHighDimensions.lean) |
| (3.37) | Transformed unit vectors have inner products `sin(c <u_i,v_j>)`. | `HDP.Chapter3.sine_feature_identity` | [`Chapter3_RandomVectorsInHighDimensions.lean`](Chapter3_RandomVectorsInHighDimensions.lean) |
| Gaussian/polynomial kernel prose | Polynomial and Gaussian kernels have explicit feature maps. | `HDP.Chapter3.polynomial_kernel_feature` | [`Chapter3_RandomVectorsInHighDimensions.lean`](Chapter3_RandomVectorsInHighDimensions.lean) |

### Chapter 4 — Random Matrices

| Book source | Result | Lean declaration | Final module |
|---|---|---|---|
| Theorem 4.1.1 | Every real rectangular matrix has an SVD with nonnegative decreasing singular values and orthonormal left/right families. | `HDP.Chapter4.exists_singularValueDecomposition` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Example 4.1.5 | If `U` has orthonormal columns, then `UU^T` is the rank-`k` orthogonal projection onto their span: it is symmetric and idempotent, fixes the column space, and kills its orthogonal complement. | `HDP.Chapter4.orthogonalProjection_eq_mul_transpose` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Remark 4.1.2 | An SVD stretches right singular directions by their singular values and rotates them to left singular directions. | `HDP.Chapter4.RealSVD.apply_right` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Remark 4.1.3; Eq. (4.4) | Singular families extend to square orthogonal matrices and yield the literal factorization `A=UΣVᵀ`, with rectangular diagonal `Σ`. | `HDP.Chapter4.exists_matrixFormSVD` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Remark 4.1.4 | Left/right singular vectors diagonalize `AA^T`/`A^TA`, and singular values are square roots of both Gram spectra. | `HDP.Chapter4.gram_apply_rightSingularVector` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Theorem 4.1.6 | Courant--Fischer max--min and min--max formulas for ordered eigenvalues. | `HDP.Chapter4.courantFischer` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Corollary 4.1.7 | Courant--Fischer formulas for singular values. | `HDP.Chapter4.singularValueMinMax` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Definition 4.1.8 | The Euclidean operator norm is the least uniform stretch factor, equivalently a unit-sphere/nonzero-vector maximum. | `HDP.Chapter4.definition_4_1_8` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Remark 4.1.9 | Every finite-dimensional `p→q` induced norm is attained and equals the maximum of the associated primal/dual bilinear form. | `HDP.Chapter4.matrixLpToLpNorm_attained`, `HDP.Chapter4.matrixLpToLpNorm_bilinear_isGreatest` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Lemma 4.1.10 | Frobenius and operator norms are invariant under orthogonal left/right multiplication. | `HDP.Chapter4.lemma_4_1_10` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Lemma 4.1.11 | Frobenius/operator norms equal the `l2`/maximum aggregates of singular values, with rank comparison. | `HDP.Chapter4.lemma_4_1_11` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Remark 4.1.12 | For symmetric matrices, the operator norm is the maximum absolute eigenvalue/Rayleigh quotient. | `HDP.Chapter4.remark_4_1_12` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Theorem 4.1.13 | Eckart--Young--Mirsky: best rank-`k` operator-norm approximation error is the next singular value. | `HDP.Chapter4.eckartYoungMirsky` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Lemma 4.1.14 | Weyl perturbation bounds for ordered eigenvalues and singular values. | `HDP.Chapter4.weylEigenvalue` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Theorem 4.1.15 | Davis--Kahan controls an eigenvector angle by perturbation norm over a spectral gap. | `HDP.Chapter4.davisKahan` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Lemma 4.1.16 | Davis--Kahan for spectral projections/invariant subspaces. | `HDP.Chapter4.davisKahanSpectralProjections` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Lemma 4.1.17 | Gram error, quadratic distortion, and squared extreme-singular-value bounds are equivalent approximate-isometry conditions. | `HDP.Chapter4.approximateIsometries` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Remark 4.1.18 | A Gram error `max(delta,delta^2)` implies unsquared singular values lie in `[1-delta,1+delta]`. | `HDP.Chapter4.gramError_implies_singularValueBounds` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Definition 4.2.1 | An internal epsilon-net covers every point of a metric-space subset within epsilon. | `HDP.Chapter4.definition_4_2_1` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Definition 4.2.2 | Covering number is the smallest cardinality of an epsilon-net. | `HDP.Chapter4.definition_4_2_2` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Remark 4.2.3 | Compact sets admit finite epsilon-nets. | `HDP.Chapter4.remark_4_2_3` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Definition 4.2.4 | Packing number is the largest cardinality of an epsilon-separated subset. | `HDP.Chapter4.definition_4_2_4` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Remark 4.2.5 | Epsilon-separated centers have disjoint radius-epsilon/2 balls. | `HDP.Chapter4.remark_4_2_5` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Lemma 4.2.6 | A maximal epsilon-separated subset is an epsilon-net. | `HDP.Chapter4.lemma_4_2_6` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Remark 4.2.7 | Greedily adding uncovered points constructs a finite net when the packing number is finite. | `HDP.Chapter4.remark_4_2_7` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Lemma 4.2.8 | Covering and packing numbers satisfy `P(2 epsilon) <= N(epsilon) <= P(epsilon)`. | `HDP.Chapter4.lemma_4_2_8` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Definition 4.2.9 | Minkowski sum of two Euclidean sets. | `HDP.Chapter4.definition_4_2_9` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Proposition 4.2.10 | Volume lower/upper bounds sandwich covering and packing numbers. | `HDP.Chapter4.proposition_4_2_10` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Corollary 4.2.11 | Euclidean ball/sphere covering numbers have `(1/epsilon)^n` lower and `(1+2/epsilon)^n` upper bounds. | `HDP.Chapter4.corollary_4_2_11` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Definition 4.2.14 | Hamming distance counts differing coordinates of binary words. | `HDP.Chapter4.definition_4_2_14` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Proposition 4.2.15 | Hamming-cube covering/packing numbers are bounded by reciprocal Hamming-ball volumes. | `HDP.Chapter4.proposition_4_2_15_exercise_4_32` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Proposition 4.3.1 | Coding a metric set to accuracy epsilon requires/admits about its metric entropy in bits. | `HDP.Chapter4.proposition_4_3_1` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Example 4.3.2 | Repetition coding corrects up to `r` errors with block length `(2r+1)k`. | `HDP.Chapter4.example_4_3_2` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Definition 4.3.3 | An error-correcting code is an encoding/decoding pair correcting every word within Hamming radius `r`. | `HDP.Chapter4.ErrorCorrectingCode` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Lemma 4.3.4 | A sufficiently separated packing yields an error-correcting code. | `HDP.Chapter4.lemma_4_3_4` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Theorem 4.3.5 | There exist efficient binary codes correcting `r` errors with near-linear redundancy. | `HDP.Chapter4.theorem_4_3_5` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Remark 4.3.6 | Required extra bits grow nearly linearly with the number of correctable errors. | `HDP.Chapter4.theorem_4_3_5` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Lemma 4.4.1 | Operator norm can be bounded from its values on an epsilon-net. | `HDP.Chapter4.lemma_4_4_1` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Lemma 4.4.2 | Bilinear/quadratic forms on one or two nets control the full matrix norm. | `HDP.Chapter4.lemma_4_4_2` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Theorem 4.4.3 | Independent centered subgaussian entries give `‖A‖ <= C K(sqrt m+sqrt n+t)` with subgaussian failure probability. | `HDP.Chapter4.theorem_4_4_3` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Remark 4.4.4 | Integrating the tail yields the corresponding expected operator-norm bound. | `HDP.Chapter4.remark_4_4_4_expectation` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Remark 4.4.5 | The order `sqrt m+sqrt n` is optimal because row/column norms lower-bound the operator norm. | `HDP.Chapter4.remark_4_4_5_optimality` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Remark 4.4.6 | Independence can be weakened to independent subgaussian rows or columns. | `HDP.Chapter4.remark_4_4_6_independentRows` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Corollary 4.4.7 | A symmetric matrix with independent centered subgaussian upper-triangular entries has the same norm scale. | `HDP.Chapter4.corollary_4_4_7` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Definition 4.5.1 | Balanced two-community stochastic block model with within/between probabilities and self-loops. | `HDP.Chapter4.definition_4_5_1` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Theorem 4.5.2 | Spectral clustering recovers all but 1% of labels under a signal-to-noise separation. | `HDP.Chapter4.theorem_4_5_2` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Remark 4.5.3 | The guarantee is nontrivial at expected degree of order one and reaches the stated sparse scale. | `HDP.Chapter4.remark_4_5_3_expectedDegree` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Theorem 4.6.1 | Independent isotropic subgaussian rows give simultaneous two-sided singular-value bounds. | `HDP.Chapter4.theorem_4_6_1_gram` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Remark 4.6.2 | The two-sided singular-value deviation also has an expectation form. | `HDP.Chapter4.remark_4_6_2` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Theorem 4.7.1 | Bounded-direction subgaussian vectors admit operator-norm sample second-moment/covariance estimation. | `HDP.Chapter4.theorem_4_7_1_factorized` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Remark 4.7.2 | Sample complexity is of order `K^4 epsilon^-2 n` (constant dependence included). | `HDP.Chapter4.remark_4_7_2` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Remark 4.7.3 | A high-probability version follows with a confidence parameter. | `HDP.Chapter4.remark_4_7_3` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Definition 4.7.4 | Two-component spherical Gaussian-mixture sampling model. | `HDP.Chapter4.gaussianMixtureMeasure` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Theorem 4.7.5 | Leading-eigenvector spectral clustering recovers at least 99% of Gaussian-mixture labels at the stated separation/sample scale. | `HDP.Chapter4.theorem_4_7_5` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Eq. (4.1) | SVD rank-one expansion. | `HDP.Chapter4.exists_singularValueDecomposition` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Eq. (4.2) | Images of distinct right singular vectors are orthogonal. | `HDP.Chapter4.inner_apply_rightSingularVector_ne` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Eq. (4.3) | `A v_i = s_i u_i`. | `HDP.Chapter4.RealSVD.apply_right` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Eq. (4.5) | Singular values are square roots of both Gram spectra. | `HDP.Chapter4.gram_apply_rightSingularVector` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Eq. (4.6) | Courant--Fischer eigenvalue formulas. | `HDP.Chapter4.courantFischer` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Eq. (4.7) | Frobenius inner product equals `tr(A^T B)`. | `HDP.Chapter4.frobeniusInner_eq_trace` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Eq. (4.8) | Squared Frobenius norm equals self-pairing/trace. | `HDP.Chapter4.frobeniusNorm_sq_eq_inner` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Eq. (4.9) | Equivalent unit-sphere/nonzero-vector/operator formulations of `‖A‖`. | `HDP.Chapter4.definition_4_1_8` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Eq. (4.10) | Symmetric operator norm is the maximum absolute Rayleigh quotient. | `HDP.Chapter4.remark_4_1_12` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Eq. (4.11) | First spectral-projection Davis--Kahan norm chain. | `HDP.Chapter4.davisKahanSpectralProjections` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Eq. (4.12) | Lower bound on the separated spectral block. | `HDP.Chapter4.davisKahanSpectralProjections` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Eq. (4.13) | Upper bound on the unperturbed spectral block. | `HDP.Chapter4.davisKahanSpectralProjections` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Eq. (4.14) | Extreme singular values are the maximum/minimum stretch on the unit sphere. | `HDP.Chapter4.extremeSingularValues_bound` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Eq. (4.15) | Gram deviation implies unsquared singular-value deviation. | `HDP.Chapter4.gramError_implies_singularValueBounds` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Eq. (4.16) | Euclidean metric is `d(x,y)=‖x-y‖_2`. | `dist_eq_norm` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Eq. (4.17) | Sharp volumetric covering bounds for the Euclidean unit ball/sphere. | `HDP.Chapter4.corollary_4_2_11` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Eq. (4.18) | Simplified `(1/epsilon)^n <= N <= (3/epsilon)^n` for `0<epsilon<=1`. | `HDP.Chapter4.corollary_4_2_11` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Eq. (4.19) | Repetition-code block length `n=(2r+1)k`. | `HDP.Chapter4.example_4_3_2` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Eq. (4.20) | Quarter-nets of the two unit spheres have sizes at most `9^n` and `9^m`. | `HDP.Chapter4.exists_quarter_unitSphereNet` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Eq. (4.21) | Two quarter-nets control the operator norm by twice the largest sampled bilinear form. | `HDP.Chapter4.lemma_4_4_2` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Eq. (4.22) | Fixed bilinear form of a subgaussian-entry matrix has a subgaussian tail. | `HDP.Chapter4.theorem_4_4_3` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Eq. (4.23) | Union bound over both nets. | `HDP.Chapter4.theorem_4_4_3` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Eq. (4.24) | Choice `u = C K(sqrt n+sqrt m+t)` closing the net proof. | `HDP.Chapter4.theorem_4_4_3` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Eq. (4.25) | SBM centered-noise operator norm is `O(sqrt n)` with exponentially high probability. | `HDP.Chapter4.sbmNoise_norm_tail` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Eq. (4.26) | Two-sided extreme singular-value bounds. | `HDP.Chapter4.theorem_4_6_1_singular` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Eq. (4.27) | Stronger normalized Gram-matrix deviation bound. | `HDP.Chapter4.theorem_4_6_1_gram` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Eq. (4.28) | For fixed unit `x`, `‖Ax‖^2` is the sum of squared row inner products. | `HDP.Chapter4.theorem_4_6_1_gram` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Eq. (4.29) | Directional subgaussian norm is controlled by its `L2` norm. | `HDP.Chapter4.theorem_4_7_1_factorized` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| Eq. (4.30) | Expected relative sample second-moment error. | `HDP.Chapter4.theorem_4_7_1` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| p.108 after (4.14) | Extreme singular values bound Euclidean distortion; exact isometries are equivalent to orthonormal columns, a Gram identity, and all singular values being one. | `HDP.Chapter4.extremeSingularValues_bound` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| pp.119--122, SBM signal calculation | Expected adjacency has two block eigenvectors/eigenvalues, rank at most two, and `A=D+R` separates signal from noise. | `HDP.Chapter4.definition_4_5_1_expectedAdjacency` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| pp.121--123, SBM algorithm | Second-eigenvector signs give a spectral classifier, with misclassification controlled by eigenvector error modulo label swap. | `HDP.Chapter4.sbmSpectralEstimate` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| p.126 before Theorem 4.7.1 | Sample second moment is unbiased and converges entrywise by the strong law. | `HDP.Chapter4.sampleCovarianceMatrix` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |
| pp.129--130, GMM signal calculation | Mixture second moment has spike `I+mu mu^T`; its top eigendirection is the mean direction and drives classification. | `HDP.Chapter4.exercise_4_51_secondMomentMatrix` | [`Chapter4_RandomMatrices.lean`](Chapter4_RandomMatrices.lean) |

### Chapter 5 — Concentration Without Independence

| Book source | Result | Lean declaration | Final module |
|---|---|---|---|
| Definition 5.1.1 | The Lipschitz seminorm is the least valid Lipschitz constant (or `∞` when none exists). | `HDP.Chapter5.lipschitzSeminorm`; `HDP.Chapter5.lipschitzSeminorm_le_iff` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| Example 5.1.2 | Linear functionals, matrices, and the norm map have their advertised sharp Lipschitz constants. | `HDP.Chapter5.example_5_1_2a`; `HDP.Chapter5.example_5_1_2b`; `HDP.Chapter5.example_5_1_2c` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| Theorem 5.1.3 | Every Lipschitz function on the radius-`sqrt n` sphere has dimension-free subgaussian concentration about its mean. | `HDP.Chapter5.sphere_lipschitz_concentration` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| Lemma 5.1.6 | Any set occupying at least half the sphere has exponentially large metric blow-ups. | `HDP.Chapter5.blowUp_of_centered_concentration` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| Remark 5.1.7 | Even exponentially small sets blow up to large measure after a modest enlargement. | `HDP.Chapter5.exercise_5_3a_exponentially_small_blowUp` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| Remark 5.2.1 | Mean, median, and `L^p` centers are interchangeable up to subgaussian-scale constants. | `HDP.Chapter5.IsMedian` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| Theorem 5.2.3 | Lipschitz functions of a standard Gaussian vector concentrate subgaussianly. | `HDP.Chapter5.gaussian_lipschitz_hasSubgaussianMGF` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| Example 5.2.4 | Gaussian linear functionals and the Euclidean norm are special cases of Gaussian concentration. | `HDP.Chapter5.gaussian_norm_concentration` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| Remark 5.2.8 | Gaussian polar decomposition generates Haar orthogonal matrices; determinant correction gives Haar special-orthogonal matrices. | `HDP.Chapter5.orthogonalHaarMeasure` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| Theorem 5.2.10 | Dimension-free concentration on the continuous cube and radius-`sqrt n` Euclidean ball. | `HDP.Chapter5.continuous_cube_lipschitz_concentration` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| Theorem 5.3.1 | Johnson--Lindenstrauss: `N` points embed into `O(epsilon^-2 log N)` dimensions with pairwise distances preserved. | `HDP.Chapter5.theorem_5_3_1` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| Lemma 5.3.2 | A random `m`-dimensional projection has exact second moment and concentrates for each fixed vector. | `HDP.Chapter5.randomProjection_secondMoment` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| Remark 5.3.3 | JL is non-adaptive to the data and independent of ambient dimension. | `HDP.Chapter5.theorem_5_3_1_exponential` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| Remark 5.3.4 | The logarithmic target dimension is optimal in general, even for nonlinear embeddings. | `HDP.Chapter5.exercise_5_15a` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| Theorem 5.4.1 | Matrix Bernstein tail bound for sums of independent centered bounded random matrices. | `HDP.Chapter5.matrixBernsteinTail` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| Definition 5.4.2 | Spectral functional calculus defines `f(X)` by applying `f` to eigenvalues. | `HDP.Chapter5.matrixFunction` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| Definition 5.4.3 | Loewner order compares symmetric matrices by positive semidefiniteness. | `HDP.Chapter5.RealLoewnerLE` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| Proposition 5.4.4 | Loewner order implies eigenvalue/trace monotonicity, norm intervals, and scalar spectral inequalities. | `HDP.Chapter5.loewner_lambdaMax_mono` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| Remark 5.4.5 | `‖X‖<=a` is equivalent to `-aI <= X <= aI`. | `HDP.Chapter5.matrixNorm_gives_loewnerInterval` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| Theorem 5.4.7 | Golden--Thompson trace-exponential inequality. | `HDP.Chapter5.goldenThompsonReal` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| Theorem 5.4.8 | Lieb concavity of `A -> tr exp(H+log A)`. | `HDP.Chapter5.liebConcavityReal` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| Lemma 5.4.9 | Expected/random-matrix form of Lieb's inequality. | `HDP.Chapter5.randomLiebReal` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| Lemma 5.4.10 | Matrix MGF is bounded by the variance term in the Bernstein range. | `HDP.Chapter5.matrixBernsteinMgf` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| Remark 5.4.11 | Integrating matrix Bernstein yields an expected-norm bound. | `HDP.Chapter5.matrixBernsteinExpectation` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| Remark 5.4.12 | The logarithmic dimension factor is a genuine price and can be necessary. | `HDP.Chapter5.missingCoordinate_error_ge_one` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| Theorem 5.4.13 | Matrix Hoeffding tail inequality for a Rademacher matrix series. | `HDP.Chapter5.matrixHoeffding` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| Theorem 5.4.14 | Matrix Khintchine moment bound for a Rademacher matrix series. | `HDP.Chapter5.matrixKhintchineOne` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| Remark 5.4.15 | Hermitian dilation extends matrix concentration to nonsymmetric rectangular matrices. | `HDP.Chapter5.rectangularRademacherExpectation` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| Theorem 5.5.1 | Matrix Bernstein yields spectral recovery in the sparse stochastic block model. | `HDP.Chapter5.theorem_5_5_1` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| Remark 5.5.2 | Expected degree is `(a+b)/2`, and logarithmic degree is enough in the theorem's regime. | `HDP.Chapter5.remark_5_5_2_expectedDegree` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| Theorem 5.6.1 | General bounded-distribution covariance/second-moment estimation via matrix Bernstein. | `HDP.Chapter5.generalCovarianceEstimation` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| Remark 5.6.2 | Sufficient sample size is `C K^2 epsilon^-2 n log n`. | `HDP.Chapter5.remark_5_6_2` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| Remark 5.6.3 | Effective rank refines covariance bounds for low-dimensional distributions. | `HDP.effectiveRank` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| Remark 5.6.4 | Effective/stable rank identities, bounds, continuity, and support-subspace behavior. | `HDP.effectiveRank` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| Remark 5.6.5 | Effective-rank covariance estimation has a high-probability form. | `HDP.Chapter5.covarianceEstimation_effectiveRank_uTail` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| Remark 5.6.6 | Without a boundedness assumption, covariance estimation can fail badly. | `HDP.Chapter5.rareAtomVector_secondMoment` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| Eq. (5.1) | Two-sided subgaussian tail for a Lipschitz sphere observable. | `HDP.Chapter5.sphere_lipschitz_tail` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| Eq. (5.4) | Blow-up lower bound for the median sublevel set. | `HDP.Chapter5.blowUp_of_centered_concentration` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| Eq. (5.5) | Lipschitzness sends the enlarged median sublevel set into `{f<=M+t}`. | `HDP.Chapter5.blowUp_of_centered_concentration` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| Eq. (5.6) | Gaussian Lipschitz tail inequality. | `HDP.Chapter5.gaussian_lipschitz_tail_explicit` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| Eq. (5.9) | JL pairwise approximate-isometry conclusion. | `HDP.Chapter5.theorem_5_3_1` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| Eq. (5.10) | Exact RMS/second-moment norm of a random projection. | `HDP.Chapter5.randomProjection_secondMoment` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| Eq. (5.11) | Fixed-difference random-projection tail before the union bound. | `HDP.Chapter5.randomProjection_fixedVector_tail` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| Eq. (5.12) | Spectral formulas for matrix powers, inverse, and exponential. | `HDP.Chapter5.matrixFunction_power` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| Eq. (5.13) | Operator norm is equivalent to the Loewner interval `-aI <= X <= aI`. | `HDP.Chapter5.matrixNorm_le_iff_loewnerInterval` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| Eq. (5.14) | Matrix inverse reverses order and matrix logarithm preserves order. | `HDP.Chapter5.inverse_loewner_antitone` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| Eq. (5.15) | Symmetric norm reduces to largest eigenvalues of `S` and `-S`. | `HDP.Chapter5.matrixBernsteinSymmetricTail` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| Eq. (5.16) | Exponential Markov/MGF upper-tail step for `lambda_max(S)`. | `HDP.Chapter5.matrixBernsteinTail` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| Eq. (5.17) | Iterated Lieb/log-MGF inequality for a sum. | `HDP.Chapter5.randomLiebReal` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| Eq. (5.18) | Expected matrix-Bernstein norm bound. | `HDP.Chapter5.matrixBernsteinExpectation` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| Eq. (5.19) | Expected sparse-SBM noise norm. | `HDP.Chapter5.sparseSBM_expectedNoise_exact` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| Eq. (5.20) | Simplified sparse-SBM noise bound sufficient for 1% error. | `HDP.Chapter5.sparseSBM_expectedNoise_degree` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| Eq. (5.21) | Almost-sure sample-energy boundedness assumption for covariance estimation. | `HDP.Chapter5.generalCovarianceEstimation` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| Eq. (5.22) | Squared/tracial reformulation of the boundedness assumption. | `HDP.Chapter5.populationSecondMoment_trace_eq_energy` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| Eq. (5.23) | Matrix-Bernstein reduction of expected covariance error. | `HDP.Chapter5.boundedCovarianceEstimation_expected` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| Eq. (5.24) | PSD variance expansion/bound for covariance summands. | `HDP.Chapter5.covarianceBernsteinVariance_le` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| Eq. (5.25) | Target relative covariance error. | `HDP.Chapter5.generalCovarianceEstimation` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| Eq. (5.26) | Sufficient sample-size bound. | `HDP.Chapter5.remark_5_6_2` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| Eq. (5.27) | Effective-rank definition `tr(Sigma)/‖Sigma‖`. | `HDP.effectiveRank` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| Eq. (5.28) | Effective-rank expected covariance bound. | `HDP.Chapter5.boundedCovarianceEstimation_effectiveRank` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| Eq. (5.29) | High-probability effective-rank covariance bound. | `HDP.Chapter5.covarianceEstimation_effectiveRank_uTail` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| p.142 before §5.1.2 | Lipschitz implies uniformly continuous; a uniformly bounded derivative on a convex domain implies Lipschitz. | `HDP.Chapter5.exercise_5_1a_lipschitz_uniformContinuous` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| p.157, Haar discussion | The Gaussian polar factor is Haar on `O(n)`, and a determinant correction gives Haar on `SO(n)`. | `HDP.Chapter5.orthogonalToSpecial_hasLaw` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| p.157, Grassmann discussion | `G_{n,1}` is the antipodal/projective quotient of the sphere, and random subspaces are projection orbits. | `HDP.Chapter5.Grassmannian` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| pp.168--170, sparse SBM proof | `A=D+R`, coordinate-square/variance identities, exact eigengap, and Davis--Kahan-to-misclassification chain. | `HDP.Chapter5.sparseSBM_noise_tail_exact` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| pp.170--172, covariance proof | Population/sample second moments, matrix variance, energy bound, and effective/stable-rank identities. | `HDP.Chapter5.sampleSecondMoment_bernstein_exact` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |

### Chapter 6 — Quadratic Forms, Symmetrization and Contraction

| Book source | Result | Lean declaration | Final module |
|---|---|---|---|
| Theorem 6.1.1 | Decoupling bounds a diagonal-free quadratic chaos by a bilinear form with an independent copy, up to factor four under convex transforms. | `HDP.Chapter6.decoupling` | [`Chapter6_QuadraticFormsSymmetrizationContraction.lean`](Chapter6_QuadraticFormsSymmetrizationContraction.lean) |
| Remark 6.1.2 | For a general matrix, the same bound holds for the off-diagonal part on the left and all entries on the decoupled right. | `HDP.Chapter6.decoupling_offDiagonal` | [`Chapter6_QuadraticFormsSymmetrizationContraction.lean`](Chapter6_QuadraticFormsSymmetrizationContraction.lean) |
| Proposition 6.2.1 | The norm of a subgaussian random vector concentrates around `sqrt n` with a subgaussian tail. | `HDP.Chapter6.subGaussianVector_norm_tail_explicit` | [`Chapter6_QuadraticFormsSymmetrizationContraction.lean`](Chapter6_QuadraticFormsSymmetrizationContraction.lean) |
| Theorem 6.2.2 | Hanson--Wright controls centered quadratic-form deviations in Frobenius and operator-norm regimes. | `HDP.Chapter6.hansonWright` | [`Chapter6_QuadraticFormsSymmetrizationContraction.lean`](Chapter6_QuadraticFormsSymmetrizationContraction.lean) |
| Lemma 6.2.3 | A subgaussian bilinear MGF is bounded by a Gaussian replacement MGF. | `HDP.Chapter6.gaussianReplacement` | [`Chapter6_QuadraticFormsSymmetrizationContraction.lean`](Chapter6_QuadraticFormsSymmetrizationContraction.lean) |
| Lemma 6.2.4 | The MGF of an independent Gaussian bilinear form is bounded by `exp(C lambda^2 ‖A‖_F^2)` in the operator-norm range. | `HDP.Chapter6.gaussianBilinear_mgf` | [`Chapter6_QuadraticFormsSymmetrizationContraction.lean`](Chapter6_QuadraticFormsSymmetrizationContraction.lean) |
| Lemma 6.3.1 | Multiplying by an independent Rademacher sign, applying odd maps, and subtracting an independent copy construct symmetric laws. | `HDP.Chapter6.constructingSymmetricDistributions_part_a` | [`Chapter6_QuadraticFormsSymmetrizationContraction.lean`](Chapter6_QuadraticFormsSymmetrizationContraction.lean) |
| Lemma 6.3.2 | Rademacher symmetrization compares expected norm of a centered sum and its signed version within factors two. | `HDP.Chapter6.symmetrization` | [`Chapter6_QuadraticFormsSymmetrizationContraction.lean`](Chapter6_QuadraticFormsSymmetrizationContraction.lean) |
| Theorem 6.4.1 | A symmetric random matrix with independent centered entries has expected norm controlled by a logarithmic factor times maximal row energy. | `HDP.Chapter6.theorem_6_4_1` | [`Chapter6_QuadraticFormsSymmetrizationContraction.lean`](Chapter6_QuadraticFormsSymmetrizationContraction.lean) |
| Theorem 6.5.1 | Bernoulli matrix completion recovers a rank-`r` matrix in expected normalized Frobenius error at the stated sample scale. | `HDP.Chapter6.matrixCompletion_bernoulli` | [`Chapter6_QuadraticFormsSymmetrizationContraction.lean`](Chapter6_QuadraticFormsSymmetrizationContraction.lean) |
| Theorem 6.6.1 | Rademacher contraction bounds coefficient-weighted random sums by the sup coefficient times the unweighted sum. | `HDP.Chapter6.contractionPrinciple_unit` | [`Chapter6_QuadraticFormsSymmetrizationContraction.lean`](Chapter6_QuadraticFormsSymmetrizationContraction.lean) |
| Lemma 6.6.2 | Gaussian symmetrization compares expected norms of a centered sum with a Gaussian-signed sum, losing `sqrt(log N)`. | `HDP.Chapter6.gaussianSymmetrization_upper` | [`Chapter6_QuadraticFormsSymmetrizationContraction.lean`](Chapter6_QuadraticFormsSymmetrizationContraction.lean) |
| Remark 6.6.3 | The `sqrt(log N)` loss in Gaussian symmetrization is unavoidable in general. | `HDP.Chapter6.exercise_6_37_coordinate_witness` | [`Chapter6_QuadraticFormsSymmetrizationContraction.lean`](Chapter6_QuadraticFormsSymmetrizationContraction.lean) |
| Eq. (6.1) | Finite linear random sum `sum_i a_i X_i`. | `Finset.sum` | [`Chapter6_QuadraticFormsSymmetrizationContraction.lean`](Chapter6_QuadraticFormsSymmetrizationContraction.lean) |
| Eq. (6.2) | Quadratic form equals its double coordinate sum and inner-product form. | `HDP.Chapter6.quadraticForm` | [`Chapter6_QuadraticFormsSymmetrizationContraction.lean`](Chapter6_QuadraticFormsSymmetrizationContraction.lean) |
| Eq. (6.3) | Main decoupling inequality. | `HDP.Chapter6.decoupling` | [`Chapter6_QuadraticFormsSymmetrizationContraction.lean`](Chapter6_QuadraticFormsSymmetrizationContraction.lean) |
| Eq. (6.4) | Partial decoupled chaos is bounded by the full bilinear chaos. | `HDP.Chapter6.integral_decoupledPartialChaos_le_bilinear` | [`Chapter6_QuadraticFormsSymmetrizationContraction.lean`](Chapter6_QuadraticFormsSymmetrizationContraction.lean) |
| Eq. (6.5) | Arbitrary-matrix off-diagonal decoupling. | `HDP.Chapter6.decoupling_offDiagonal` | [`Chapter6_QuadraticFormsSymmetrizationContraction.lean`](Chapter6_QuadraticFormsSymmetrizationContraction.lean) |
| Eq. (6.6) | Exponential Markov step for the random-vector norm. | `HDP.Chapter6.subGaussianVector_norm_tail_explicit` | [`Chapter6_QuadraticFormsSymmetrizationContraction.lean`](Chapter6_QuadraticFormsSymmetrizationContraction.lean) |
| Eq. (6.7) | Gaussian-mixture representation bounds the norm-square exponential. | `HDP.Chapter6.subGaussianVector_norm_tail_explicit` | [`Chapter6_QuadraticFormsSymmetrizationContraction.lean`](Chapter6_QuadraticFormsSymmetrizationContraction.lean) |
| Eq. (6.8) | Exchange of Gaussian/vector expectations by Tonelli/Fubini. | `HDP.Chapter6.subGaussianVector_norm_tail_explicit` | [`Chapter6_QuadraticFormsSymmetrizationContraction.lean`](Chapter6_QuadraticFormsSymmetrizationContraction.lean) |
| Eq. (6.9) | Conditional subgaussian MGF is bounded by a Gaussian MGF. | `HDP.Chapter6.subGaussianVector_lmgf_le_gaussian` | [`Chapter6_QuadraticFormsSymmetrizationContraction.lean`](Chapter6_QuadraticFormsSymmetrizationContraction.lean) |
| Eq. (6.10) | Exact MGF of a standard-Gaussian inner product. | `HDP.Chapter6.standardGaussian_inner_lmgf` | [`Chapter6_QuadraticFormsSymmetrizationContraction.lean`](Chapter6_QuadraticFormsSymmetrizationContraction.lean) |
| Eq. (6.11) | Gaussian bilinear MGF factors over singular values. | `HDP.Chapter6.gaussianDiagonal_mgf` | [`Chapter6_QuadraticFormsSymmetrizationContraction.lean`](Chapter6_QuadraticFormsSymmetrizationContraction.lean) |
| Eq. (6.12) | Off-diagonal Hanson--Wright exponential-Markov bound. | `HDP.Chapter6.hansonWright_offDiagonal_lmgf` | [`Chapter6_QuadraticFormsSymmetrizationContraction.lean`](Chapter6_QuadraticFormsSymmetrizationContraction.lean) |
| Eq. (6.13) | Adding an independent centered perturbation cannot reduce expected norm. | `HDP.Chapter6.integral_norm_le_integral_norm_add_independent_centered` | [`Chapter6_QuadraticFormsSymmetrizationContraction.lean`](Chapter6_QuadraticFormsSymmetrizationContraction.lean) |
| Eq. (6.14) | Entrywise symmetrization of a symmetric random matrix. | `HDP.Chapter6.symmetricRandomMatrix_expectedNorm_upper_of_symmetrization` | [`Chapter6_QuadraticFormsSymmetrizationContraction.lean`](Chapter6_QuadraticFormsSymmetrizationContraction.lean) |
| Eq. (6.15) | Conditional matrix Khintchine for the symmetrized coordinate matrices. | `HDP.Chapter6.conditionalKhintchine_symmetricCoordinates` | [`Chapter6_QuadraticFormsSymmetrizationContraction.lean`](Chapter6_QuadraticFormsSymmetrizationContraction.lean) |
| Eq. (6.16) | Matrix-completion sampling probability `p=m/n^2`. | `HDP.Chapter6.matrixCompletion_bernoulli_normalized` | [`Chapter6_QuadraticFormsSymmetrizationContraction.lean`](Chapter6_QuadraticFormsSymmetrizationContraction.lean) |
| Eq. (6.17) | Best-approximation operator error is at most twice the proxy error. | `HDP.Chapter6.operatorError_le_two_mul_proxyError` | [`Chapter6_QuadraticFormsSymmetrizationContraction.lean`](Chapter6_QuadraticFormsSymmetrizationContraction.lean) |
| Eq. (6.18) | Rectangular independent-entry norm is controlled by expected maximal row/column energy. | `HDP.Chapter6.exercise_6_28_rectangular_expectedNorm` | [`Chapter6_QuadraticFormsSymmetrizationContraction.lean`](Chapter6_QuadraticFormsSymmetrizationContraction.lean) |
| Eq. (6.19) | Expected centered sampling operator norm/error bound. | `HDP.Chapter6.centeredSampling_expectedOperatorNorm_le` | [`Chapter6_QuadraticFormsSymmetrizationContraction.lean`](Chapter6_QuadraticFormsSymmetrizationContraction.lean) |
| Eq. (6.20) | Contraction functional `f(a)=E‖sum a_i epsilon_i x_i‖`. | `HDP.Chapter6.contractionFunctional` | [`Chapter6_QuadraticFormsSymmetrizationContraction.lean`](Chapter6_QuadraticFormsSymmetrizationContraction.lean) |
| p.181 after (6.2) | Independent centered unit-variance coordinates satisfy `E[X^TAX]=tr A`. | `HDP.Chapter6.integral_quadraticForm_eq_diagonal` | [`Chapter6_QuadraticFormsSymmetrizationContraction.lean`](Chapter6_QuadraticFormsSymmetrizationContraction.lean) |
| pp.181--183, decoupling proof | Selector averaging, existence of a favorable split, and independent-copy replacement produce the factor four. | `HDP.Chapter6.decoupling` | [`Chapter6_QuadraticFormsSymmetrizationContraction.lean`](Chapter6_QuadraticFormsSymmetrizationContraction.lean) |
| pp.186--187, Hanson--Wright proof | Centered quadratic form splits into diagonal and off-diagonal pieces; Bernstein handles the first and decoupling/Gaussian replacement the second. | `HDP.Chapter6.quadraticForm_sub_integral_eq_diagonal_add_offDiagonal` | [`Chapter6_QuadraticFormsSymmetrizationContraction.lean`](Chapter6_QuadraticFormsSymmetrizationContraction.lean) |
| p.190, random-matrix proof | Coordinate matrix `Z_ij` need not be diagonal, but `Z_ij^2` is diagonal and sums to row-energy data. | `HDP.Chapter6.symmetricCoordinateMatrix_sq_apply` | [`Chapter6_QuadraticFormsSymmetrizationContraction.lean`](Chapter6_QuadraticFormsSymmetrizationContraction.lean) |
| pp.190--192, completion proof | Bernoulli observation model, proxy error, rank-to-Frobenius transfer, and normalized error algebra. | `HDP.Chapter6.sampledMatrix` | [`Chapter6_QuadraticFormsSymmetrizationContraction.lean`](Chapter6_QuadraticFormsSymmetrizationContraction.lean) |
| p.194 in Lemma 6.6.2 proof | Expected maximum of `N` standard Gaussians is `O(sqrt(log N))`. | `HDP.Chapter6.gaussianSymmetrization_source` | [`Chapter6_QuadraticFormsSymmetrizationContraction.lean`](Chapter6_QuadraticFormsSymmetrizationContraction.lean) |

### Chapter 7 — Random Processes

| Book source | Result | Lean declaration | Final module |
|---|---|---|---|
| Definition 7.1.1 | A random process is a family of random variables on one probability space, indexed by a set. | `HDP.RandomProcess` | [`Chapter7_RandomProcesses.lean`](Chapter7_RandomProcesses.lean) |
| Example 7.1.6 | Brownian motion and an independent centered unit-variance random walk have the square-root canonical increment metrics `d(t,s)=√(t-s)` and `d(n,m)=√(n-m)`. | `HDP.Chapter7.brownian_processIncrement`, `HDP.Chapter7.randomWalk_processIncrement` | [`Chapter7_RandomProcesses.lean`](Chapter7_RandomProcesses.lean) |
| Remark 7.1.7 | `L2` increments obey zero, symmetry, and the triangle inequality. | `HDP.processIncrement_pseudometric_laws` | [`Chapter7_RandomProcesses.lean`](Chapter7_RandomProcesses.lean) |
| Remark 7.1.8 | Squared increments equal `Sigma(t,t)-2 Sigma(t,s)+Sigma(s,s)`; with a zero coordinate, increments recover covariance. | `HDP.processIncrement_sq_eq_covariance` | [`Chapter7_RandomProcesses.lean`](Chapter7_RandomProcesses.lean) |
| Definition 7.1.9 | A Gaussian process has jointly Gaussian restriction to every finite index set; equivalently every finite linear combination is Gaussian. | `HDP.Chapter7.isGaussianProcess_iff_finset` | [`Chapter7_RandomProcesses.lean`](Chapter7_RandomProcesses.lean) |
| Remark 7.1.10 | Mean and covariance determine a Gaussian process in law; with a zero coordinate, increments determine it too. | `HDP.Chapter7.finiteGaussianProcess_identDistrib_of_mean_covariance` | [`Chapter7_RandomProcesses.lean`](Chapter7_RandomProcesses.lean) |
| Lemma 7.1.12 | Every centered Gaussian vector is equal in law to inner products of one standard Gaussian vector with deterministic points. | `HDP.Chapter7.gaussianVector_canonical_representation` | [`Chapter7_RandomProcesses.lean`](Chapter7_RandomProcesses.lean) |
| Remark 7.2.1 | For arbitrary index sets, expected suprema are interpreted as suprema of finite-subset expected maxima. | `HDP.Chapter7.extendedExpectedSupremum` | [`Chapter7_RandomProcesses.lean`](Chapter7_RandomProcesses.lean) |
| Theorem 7.2.2 | Slepian: equal variances plus dominated increments imply stochastic and expected-max domination. | `HDP.Chapter7.slepianInequality` | [`Chapter7_RandomProcesses.lean`](Chapter7_RandomProcesses.lean) |
| Lemma 7.2.3 | Scalar Gaussian integration by parts: `E[X f(X)] = E[f'(X)]`. | `HDP.Chapter7.gaussianIntegrationByParts` | [`Chapter7_RandomProcesses.lean`](Chapter7_RandomProcesses.lean) |
| Lemma 7.2.4 | Multivariate Gaussian integration by parts contracts covariance with the gradient. | `HDP.Chapter7.multivariateGaussianIntegrationByParts` | [`Chapter7_RandomProcesses.lean`](Chapter7_RandomProcesses.lean) |
| Lemma 7.2.5 | The derivative of an interpolated Gaussian expectation is one half the covariance difference contracted with the expected Hessian. | `HDP.Chapter7.gaussianInterpolation` | [`Chapter7_RandomProcesses.lean`](Chapter7_RandomProcesses.lean) |
| Lemma 7.2.6 | A function with nonpositive mixed Hessian entries yields the functional Slepian comparison. | `HDP.Chapter7.gaussianInterpolation` | [`Chapter7_RandomProcesses.lean`](Chapter7_RandomProcesses.lean) |
| Theorem 7.2.7 | Finite-vector Slepian stochastic and expectation comparison. | `HDP.Chapter7.slepianInequality` | [`Chapter7_RandomProcesses.lean`](Chapter7_RandomProcesses.lean) |
| Theorem 7.2.8 | Sudakov--Fernique: increment domination implies expected-supremum domination. | `HDP.Chapter7.sudakovFernique` | [`Chapter7_RandomProcesses.lean`](Chapter7_RandomProcesses.lean) |
| Theorem 7.2.9 | Gordon min-max comparison for Gaussian processes. | `HDP.Chapter7.gordonExpectationInequality` | [`Chapter7_RandomProcesses.lean`](Chapter7_RandomProcesses.lean) |
| Theorem 7.3.1 | An iid standard Gaussian `m x n` matrix has expected operator norm at most `sqrt m + sqrt n`. | `HDP.Chapter7.gaussianMatrix_expected_opNorm` | [`Chapter7_RandomProcesses.lean`](Chapter7_RandomProcesses.lean) |
| Corollary 7.3.2 | The Gaussian matrix norm has Gaussian upper tails around `sqrt m + sqrt n`. | `HDP.Chapter7.gaussianMatrix_opNorm_tail` | [`Chapter7_RandomProcesses.lean`](Chapter7_RandomProcesses.lean) |
| Theorem 7.4.1 | Sudakov lower-bounds a Gaussian expected supremum by `epsilon sqrt(log covering-number)`. | `HDP.Chapter7.sudakovInequality` | [`Chapter7_RandomProcesses.lean`](Chapter7_RandomProcesses.lean) |
| Corollary 7.4.2 | Euclidean Gaussian width dominates every Sudakov covering scale. | `HDP.Chapter7.sudakovInequality` | [`Chapter7_RandomProcesses.lean`](Chapter7_RandomProcesses.lean) |
| Corollary 7.4.3 | A polytope with `N` vertices has logarithmic covering-number bound controlled by its diameter and `log N`. | `HDP.Chapter7.polytopeCovering_log_bound` | [`Chapter7_RandomProcesses.lean`](Chapter7_RandomProcesses.lean) |
| Definition 7.5.1 | Gaussian width is the expected support of a set in a standard Gaussian direction. | `HDP.Chapter7.gaussianWidth` | [`Chapter7_RandomProcesses.lean`](Chapter7_RandomProcesses.lean) |
| Remark 7.5.3 | The width/diameter constants are optimal, witnessed by a symmetric pair and Euclidean balls. | `HDP.Chapter7.exercise_7_16_symmetricPair` | [`Chapter7_RandomProcesses.lean`](Chapter7_RandomProcesses.lean) |
| Definition 7.5.4 | Spherical width is average support over a uniform unit-sphere direction. | `HDP.Chapter7.sphericalWidth` | [`Chapter7_RandomProcesses.lean`](Chapter7_RandomProcesses.lean) |
| Lemma 7.5.5 | Gaussian width equals mean Gaussian radius times spherical width, so the two differ by a `sqrt n` factor. | `HDP.Chapter7.gaussianWidth_eq_radialMean_mul_sphericalWidth` | [`Chapter7_RandomProcesses.lean`](Chapter7_RandomProcesses.lean) |
| Example 7.5.6 | The Euclidean unit ball and sphere have Gaussian width comparable to `sqrt n`. | `HDP.Chapter7.euclideanBallGaussianWidth` | [`Chapter7_RandomProcesses.lean`](Chapter7_RandomProcesses.lean) |
| Example 7.5.7 | The cube has Gaussian width exactly `sqrt(2/pi) n`. | `HDP.Chapter7.cubeGaussianWidth_eq_source` | [`Chapter7_RandomProcesses.lean`](Chapter7_RandomProcesses.lean) |
| Example 7.5.9 | A finite point set has Gaussian width at most a universal constant times diameter times `sqrt(log cardinality)`. | `HDP.Chapter7.gaussianFamilyWidth_unit_upper` | [`Chapter7_RandomProcesses.lean`](Chapter7_RandomProcesses.lean) |
| Lemma 7.5.11 | Gaussian width, Gaussian complexity, and the `L2`-supremum variant are equivalent up to universal constants. | `HDP.Chapter7.almostEquivalentGaussianWidths` | [`Chapter7_RandomProcesses.lean`](Chapter7_RandomProcesses.lean) |
| Definition 7.5.12 | Effective dimension is width-squared divided by diameter-squared and is bounded by affine dimension. | `HDP.Chapter7.effectiveDimension` | [`Chapter7_RandomProcesses.lean`](Chapter7_RandomProcesses.lean) |
| Theorem 7.6.1 | Expected diameter of a random `m`-dimensional projection is comparable to spherical width plus `sqrt(m/n)` times diameter. | `HDP.Chapter7.randomProjection_expectedDiameter` | [`Chapter7_RandomProcesses.lean`](Chapter7_RandomProcesses.lean) |
| Remark 7.6.2 | Random-projection diameter has a width-dominated/diameter-dominated phase transition. | `HDP.Chapter7.phaseTransition_sum_equiv_max` | [`Chapter7_RandomProcesses.lean`](Chapter7_RandomProcesses.lean) |
| Eq. (7.1) | Canonical `L2` increment distance. | `HDP.processIncrement` | [`Chapter7_RandomProcesses.lean`](Chapter7_RandomProcesses.lean) |
| Eq. (7.2) | Canonical Gaussian process `X_t=<g,t>`. | `HDP.Chapter7.canonicalGaussianProcess` | [`Chapter7_RandomProcesses.lean`](Chapter7_RandomProcesses.lean) |
| Eq. (7.3) | Slepian equal-variance and increment-domination assumptions. | `HDP.Chapter7.slepianInequality` | [`Chapter7_RandomProcesses.lean`](Chapter7_RandomProcesses.lean) |
| Eq. (7.4) | Slepian stochastic domination of suprema. | `HDP.Chapter7.slepianInequality` | [`Chapter7_RandomProcesses.lean`](Chapter7_RandomProcesses.lean) |
| Eq. (7.5) | Slepian expected-supremum comparison. | `HDP.Chapter7.slepianInequality` | [`Chapter7_RandomProcesses.lean`](Chapter7_RandomProcesses.lean) |
| Eq. (7.6) | Whole-line scalar Gaussian integration-by-parts calculation. | `HDP.Chapter7.gaussianIntegrationByParts` | [`Chapter7_RandomProcesses.lean`](Chapter7_RandomProcesses.lean) |
| Eq. (7.7) | Multivariate Gaussian integration-by-parts identity. | `HDP.Chapter7.multivariateGaussianIntegrationByParts` | [`Chapter7_RandomProcesses.lean`](Chapter7_RandomProcesses.lean) |
| Eq. (7.8) | Interpolation `sqrt(u)X+sqrt(1-u)Y`. | `HDP.Chapter7.gaussianInterpolationPoint` | [`Chapter7_RandomProcesses.lean`](Chapter7_RandomProcesses.lean) |
| Eq. (7.9) | Derivative of the expected interpolated test function. | `HDP.Chapter7.gaussianInterpolation` | [`Chapter7_RandomProcesses.lean`](Chapter7_RandomProcesses.lean) |
| Eq. (7.10) | First chain-rule expansion in Gaussian interpolation. | `HDP.Chapter7.gaussianInterpolation` | [`Chapter7_RandomProcesses.lean`](Chapter7_RandomProcesses.lean) |
| Eq. (7.11) | Integration-by-parts evaluation of the `X_i` contribution. | `HDP.Chapter7.gaussianInterpolation` | [`Chapter7_RandomProcesses.lean`](Chapter7_RandomProcesses.lean) |
| Eq. (7.12) | Log-sum-exp smooth maximum. | `HDP.Chapter7.sudakovFernique` | [`Chapter7_RandomProcesses.lean`](Chapter7_RandomProcesses.lean) |
| Eq. (7.13) | Canonical metric restated through covariance. | `HDP.processIncrement` | [`Chapter7_RandomProcesses.lean`](Chapter7_RandomProcesses.lean) |
| Eq. (7.14) | Expected supremum of a Gaussian process. | `HDP.Chapter7.expectedFiniteSupremum` | [`Chapter7_RandomProcesses.lean`](Chapter7_RandomProcesses.lean) |
| Eq. (7.15) | Gaussian maximum over polytope vertices controls entropy. | `HDP.Chapter7.polytopeCovering_log_bound` | [`Chapter7_RandomProcesses.lean`](Chapter7_RandomProcesses.lean) |
| Eq. (7.16) | Width is the mean directional width of the difference set. | `HDP.Chapter7.differenceFinset` | [`Chapter7_RandomProcesses.lean`](Chapter7_RandomProcesses.lean) |
| Eq. (7.17) | Ball/sphere width equals `E ‖g‖` and is `sqrt n` up to constants. | `HDP.Chapter7.euclideanBallGaussianWidth` | [`Chapter7_RandomProcesses.lean`](Chapter7_RandomProcesses.lean) |
| Eq. (7.18) | Cube width is `sqrt(2/pi)n`. | `HDP.Chapter7.cubeGaussianWidth_eq_source` | [`Chapter7_RandomProcesses.lean`](Chapter7_RandomProcesses.lean) |
| Eq. (7.20) | Johnson--Lindenstrauss projection scales diameter by `sqrt(m/n)`. | `HDP.Chapter5.randomProjection_rms` | [`Chapter5_ConcentrationWithoutIndependence.lean`](Chapter5_ConcentrationWithoutIndependence.lean) |
| Eq. (7.21) | Orthogonal projection of the unit ball onto a nonzero subspace has diameter two. | `HDP.Chapter7.orthogonalProjection_unitBall_diam` | [`Chapter7_RandomProcesses.lean`](Chapter7_RandomProcesses.lean) |
| Eq. (7.22) | A quarter-net reduces projected diameter to finitely many support values. | `HDP.Chapter7.randomProjection_expectedDiameter_upper` | [`Chapter7_RandomProcesses.lean`](Chapter7_RandomProcesses.lean) |
| Eq. (7.23) | Fixed-direction projected support is a spherical/Gaussian support variable. | `HDP.Chapter7.randomProjection_expectedDiameter_upper` | [`Chapter7_RandomProcesses.lean`](Chapter7_RandomProcesses.lean) |
| Eq. (7.24) | Union-bound tail over the projection net. | `HDP.Chapter7.randomProjection_expectedDiameter_upper` | [`Chapter7_RandomProcesses.lean`](Chapter7_RandomProcesses.lean) |
| Sec. 7.1.1, covariance display | The covariance function is `E[X_t X_s]` for centered processes. | `HDP.processCovariance` | [`Chapter7_RandomProcesses.lean`](Chapter7_RandomProcesses.lean) |
| Sec. 7.1.2 after (7.2) | Canonical Gaussian-process increments equal Euclidean distance. | `HDP.Chapter7.canonicalGaussianProcess_increment` | [`Chapter7_RandomProcesses.lean`](Chapter7_RandomProcesses.lean) |
| Sec. 7.1.2 conclusion | Every finite-dimensional marginal of a Gaussian process admits a canonical Euclidean representation. | `HDP.Chapter7.gaussianVector_canonical_representation` | [`Chapter7_RandomProcesses.lean`](Chapter7_RandomProcesses.lean) |
| Sec. 7.6 proof after (7.24) | The net-union probability can be simplified to a pure exponential tail. | `HDP.Chapter7.randomProjection_expectedDiameter_upper` | [`Chapter7_RandomProcesses.lean`](Chapter7_RandomProcesses.lean) |

### Chapter 8 — Chaining

| Book source | Result | Lean declaration | Final module |
|---|---|---|---|
| Definition 8.1.1 | A process has subgaussian increments when every increment has `psi2` norm at most `K` times the index distance. | `HDP.HasSubGaussianIncrementsWith` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Section 8.1 after Example 8.1.2 | Every process with subgaussian increments is tautologically subgaussian for its `psi2` increment metric. | `HDP.hasSubGaussianIncrementsWith_psi2Metric` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Theorem 8.1.3 | Dudley bounds the expected supremum of a centered subgaussian-increment process by the entropy integral. | `HDP.Chapter8.dudleyIntegralInequality_coveringNumber` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Theorem 8.1.4 | Discrete Dudley bounds the expected supremum by a dyadic entropy sum. | `HDP.Chapter8.discreteDudleyInequality_coveringNumber` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Remark 8.1.5 | Dudley also bounds anchored and pairwise suprema of increments without centering. | `HDP.Chapter8.dudleySupremumOfIncrements` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Remark 8.1.6 | Dudley admits a high-probability bound with an added `u diam(T)` term. | `HDP.Chapter8.dudleyHighProbabilityBound` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Remark 8.1.7 | The entropy integral can be truncated at the diameter because larger balls cover the set singly. | `HDP.Chapter8.coveringEntropy_eq_zero_above_ediam` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Theorem 8.1.8 | Arbitrary bounded Euclidean-set Gaussian width is bounded by its Dudley entropy integral. | `HDP.Chapter8.dudleyInequalityEuclidean_arbitrarySet_ENN` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Example 8.1.9 | Dudley is sharp on the Euclidean ball at scale `sqrt n`. | `HDP.Chapter8.euclideanUnitBall_gaussianWidth_le_sqrt_card` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Remark 8.1.10 | Dudley can overestimate width, but by at most a logarithmic factor; a weighted-basis family exhibits divergence of the entropy integral with bounded width. | `HDP.Chapter8.exercise_8_4a_weightedBasis_actualGaussianWidth` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Remark 8.2.1 | Monte Carlo sample-mean expected absolute error is at most standard deviation divided by `sqrt n`. | `HDP.Chapter8.theorem_8_2_1_monteCarlo_expected_error` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Remark 8.2.2 | The Monte Carlo rate is dimension-free. | `HDP.Chapter8.remark_8_2_2_dimension_free_monteCarlo` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Theorem 8.2.3 | Uniform law of large numbers for all `L`-Lipschitz functions on `[0,1]`, at rate `L/sqrt n`. | `HDP.Chapter8.theorem_8_2_3_lipschitz_uniform_lln_general` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Remark 8.2.4 | One sample realizes the uniform error bound simultaneously for the full class of `L`-Lipschitz functions. | `HDP.Chapter8.remark_8_2_4_exists_good_lipschitz_sample` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Definition 8.2.5 | The empirical process is the centered normalized sample average indexed by a function class. | `HDP.Chapter8.empiricalProcessValue` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Definition 8.3.1 | VC dimension is the largest size of a shattered subset, with an infinite case. | `HDP.BooleanClass.VCDimLE` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Example 8.3.2 | Indicators of real intervals have VC dimension two. | `HDP.Chapter8.example_8_3_2_real_closed_intervals` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Example 8.3.3 | Affine half-planes in `R^2` have VC dimension three. | `HDP.Chapter8.example_8_3_3_euclidean_halfplanes` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Example 8.3.4 | The four strings `001,010,100,111` have VC dimension two. | `HDP.Chapter8.example_8_3_4` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Example 8.3.5 | Affine half-spaces in `R^n` have VC dimension `n+1`. | `HDP.Chapter8.example_8_3_5_euclidean_halfspaces` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Remark 8.3.6 | Affine half-spaces in `R^n` have VC dimension `n+1`, matching their parameter count. | `HDP.Chapter8.remark_8_3_6_simplex_parameter_count` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Lemma 8.3.7 | Pajor: a finite Boolean family has at least as many shattered subsets as functions. | `HDP.Chapter8.lemma_8_3_7_pajor` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Example 8.3.8 | Applying Pajor's splitting to the four-string class yields seven shattered subsets. | `HDP.Chapter8.example_8_3_8_full_family` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Lemma 8.3.9 | Sauer--Shelah bounds a class by the binomial sum up to its VC dimension. | `HDP.Chapter8.lemma_8_3_9_sauer_shelah` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Definition 8.3.10 | The growth function is the largest trace-cardinality on an `n`-point sample. | `HDP.Chapter8.growthFunction` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Proposition 8.3.11 | VC dimension is stable under conjunction and disjunction, with universal-multiple bounds. | `HDP.Chapter8.proposition_8_3_11_and` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Example 8.3.12 | Euclidean strips have controlled VC dimension as intersections of two half-spaces. | `HDP.Chapter8.example_8_3_12_strips` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Theorem 8.3.13 | An arbitrary measurable Boolean class with VC dimension `d` has polynomial `L2` covering numbers. | `HDP.Chapter8.theorem_8_3_13_vc_covering_general` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Lemma 8.3.14 | Empirical `L2` distances preserve a finite separated family with positive probability when sample size is large enough. | `HDP.Chapter8.lemma_8_3_14_dimension_reduction` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Theorem 8.3.15 | A Boolean class of VC dimension `d` has expected uniform empirical deviation `O(sqrt(d/n))`. | `HDP.Chapter8.theorem_8_3_15_vc_expected` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Remark 8.3.16 | Rademacher complexity controls the empirical deviation and has the same VC rate. | `HDP.Chapter8.finiteRademacherComplexity` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Theorem 8.3.17 | Glivenko--Cantelli: the empirical CDF converges uniformly at rate `1/sqrt n`. | `HDP.Chapter8.theorem_8_3_17_glivenko_cantelli_real` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Example 8.3.18 | A random sample gives low discrepancy for a finite range space of small VC dimension. | `HDP.Chapter8.example_8_3_18_discrepancy` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Remark 8.3.19 | Finite VC dimension yields a uniform Glivenko--Cantelli class; infinite VC dimension obstructs uniform convergence. | `HDP.Chapter8.IsUniformGlivenkoCantelli` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Example 8.4.1 | Statistical classification is learning a Boolean target from labeled iid data. | `HDP.Chapter8.booleanSetPopulationRisk` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Example 8.4.2 | Boolean squared loss equals misclassification probability/symmetric-difference loss. | `HDP.Chapter8.example_8_4_2_classification_loss` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Definition 8.4.3 | ERM minimizes empirical squared loss, and population risk has a minimizer only when attainment is supplied/proved. | `HDP.Chapter8.empiricalRisk` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Example 8.4.4 | In classification, empirical risk is the empirical misclassification rate. | `HDP.Chapter8.example_8_4_4_empirical_classification_risk` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Theorem 8.4.5 | VC generalization bound controls expected excess risk by `sqrt(vc/n)`. | `HDP.Chapter8.theorem_8_4_5_vc_generalization_bound_arbitrary` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Example 8.4.6 | The classification loss class has the same VC dimension as the hypothesis class, giving the classification specialization. | `HDP.Chapter8.exercise_8_29_loss_class_vcDimEq_iff` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Remark 8.4.7 | Increasing model complexity reduces approximation bias but increases the VC estimation term. | `HDP.Chapter8.remark_8_4_7_bias_variance_tradeoff` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Definition 8.5.1 | `gamma2` is the infimum, over admissible chains, of the worst weighted multiscale approximation cost. | `HDP.gamma2` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Theorem 8.5.2 | Generic chaining bounds the expected supremum by `C K gamma2`. | `HDP.Chapter8.genericChainingBound` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Remark 8.5.3 | Generic chaining bounds pairwise increment suprema without centering. | `HDP.Chapter8.genericChainingSupremumOfIncrements` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Remark 8.5.4 | Generic chaining has a high-probability `gamma2 + u diam` bound. | `HDP.Chapter8.exercise_8_35_highProbability` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Remark 8.5.7 | For two Gaussian processes, Talagrand comparison reduces to Sudakov--Fernique with constant one. | `HDP.Chapter8.talagrandComparison_gaussian_constant_one` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Eq. (8.1) | `psi2` increment domination by `K d(s,t)`. | `HDP.HasSubGaussianIncrementsWith` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Eq. (8.2) | Discrete dyadic Dudley sum. | `HDP.Chapter8.discreteDudleyInequality_coveringNumber` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Eq. (8.3) | Net approximation makes each process increment `K epsilon`-subgaussian. | `HDP.Chapter8.dudleyIntegralInequality_coveringNumber` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Eq. (8.4) | Dyadic scales `epsilon_k=2^{-k}`. | `HDP.Chapter8.dyadicRadius` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Eq. (8.5) | Each chain level has covering-number cardinality. | `HDP.Chapter8.optimalDyadicLevel` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Eq. (8.6) | Chaining starts at a singleton and terminates at the full finite set. | `HDP.Chapter8.FiniteDudleyChain` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Eq. (8.7) | Chosen projections are within the covering radius. | `HDP.Chapter8.dist_optimalCoverProjection_le` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Eq. (8.8) | Finite telescoping chain expansion. | `HDP.Chapter8.finiteDudleyChain_telescope` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Eq. (8.9) | Infinite-looking telescoping sum truncates at the terminal level. | `HDP.Chapter8.finiteDudleyChain_telescope` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Eq. (8.10) | Expected anchored supremum is bounded by the sum of expected scale suprema. | `HDP.Chapter8.finiteProcessIncrementSup_le_sum_dudleyScaleSup` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Eq. (8.11) | Each scale maximum is bounded by radius times square-root log cardinality. | `HDP.Chapter8.expected_dudleyScaleSup_le_of_subGaussianIncrements` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Eq. (8.12) | Summing scale bounds gives discrete Dudley. | `HDP.Chapter8.discreteDudleyInequality_of_subGaussianIncrements` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Eq. (8.13) | Anchored absolute-increment Dudley bound. | `HDP.Chapter8.dudleySupremumOfIncrements` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Eq. (8.14) | Pairwise-increment Dudley bound. | `HDP.Chapter8.dudleySupremumOfPairwiseIncrements` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Eq. (8.15) | High-probability Dudley bound. | `HDP.Chapter8.exercise_8_1_highProbabilityDudley_finiteMetric` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Eq. (8.16) | Dudley integral truncated at the diameter. | `HDP.Chapter8.coveringEntropy_eq_zero_above_ediam` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Eq. (8.17) | Euclidean-set Gaussian width bounded by the entropy integral. | `HDP.Chapter8.theorem_8_1_8_dudleyInequalityEuclidean_arbitrarySet` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Eq. (8.18) | Monte Carlo sample averages converge almost surely. | `HDP.Chapter8.equation_8_18_monteCarlo_strong_law` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Eq. (8.19) | Monte Carlo integral is approximated by the normalized sample average. | `HDP.Chapter8.monteCarloAverage` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Eq. (8.20) | Expected scalar Monte Carlo error is `O(1/sqrt n)`. | `HDP.Chapter8.theorem_8_2_1_monteCarlo_expected_error` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Eq. (8.21) | Full `L`-Lipschitz function class on `[0,1]`. | `HDP.Chapter8.unitIntervalLipschitzBall` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Eq. (8.22) | Expected uniform Lipschitz empirical error is `O(L/sqrt n)`. | `HDP.Chapter8.theorem_8_2_3_lipschitz_uniform_lln_general` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Eq. (8.23) | Empirical-process coordinate `X_f`. | `HDP.Chapter8.empiricalProcessValue` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Eq. (8.24) | Normalized `[0,1]`-valued one-Lipschitz class. | `HDP.Chapter8.unitIntervalLipschitzClass` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Eq. (8.25) | Dudley entropy bound for the Lipschitz empirical process. | `HDP.Chapter8.theorem_8_2_3_lipschitz_uniform_lln_general` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Eq. (8.26) | Empirical measure is the normalized sum of sample Dirac masses. | `HDP.Chapter8.empiricalMeasure` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Eq. (8.27) | A finite Boolean family lies between `2^vc` and `2^n`. | `HDP.Chapter8.card_family_lower_of_shatters` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Eq. (8.28) | Pajor split families each contribute shattered sets. | `HDP.Chapter8.lemma_8_3_7_pajor` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Eq. (8.29) | Shatterer count is superadditive under the Pajor split. | `HDP.Chapter8.lemma_8_3_7_pajor` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Eq. (8.30) | Growth function lies between `2^d` and the Sauer--Shelah polynomial bound. | `HDP.Chapter8.growthFunction_lower_of_shatters` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Eq. (8.31) | Boolean `L2` distance equals square-root symmetric-difference probability. | `HDP.Chapter8.equation_8_31` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Eq. (8.32) | Empirical Boolean `L2` distance is the sample squared-difference average. | `HDP.Chapter8.equation_8_32` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Eq. (8.33) | Outside the bad event, empirical distance preserves population separation. | `HDP.Chapter8.equation_8_33` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Eq. (8.34) | Union-bound probability for simultaneous empirical distance preservation. | `HDP.Chapter8.equation_8_34_bad_probability_source` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Eq. (8.35) | VC expected deviation is bounded by the empirical entropy integral. | `HDP.Chapter8.theorem_8_3_15_vc_expected` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Eq. (8.36) | Labeled training sample `(X_i,T(X_i))`. | `HDP.Chapter8.empiricalRisk` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Eq. (8.37) | Population squared prediction risk. | `HDP.Chapter8.squaredLoss` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Eq. (8.38) | For Boolean hypotheses, risk is misclassification probability. | `HDP.Chapter8.example_8_4_2_classification_loss` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Eq. (8.39) | Empirical risk and its minimizer. | `HDP.Chapter8.empiricalRisk` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Eq. (8.40) | ERM excess risk is at most twice uniform risk deviation. | `HDP.Chapter8.equation_8_40_excessRisk_arbitrary` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Eq. (8.41) | VC loss-class deviation has `sqrt(vc/n)` rate. | `HDP.Chapter8.theorem_8_4_5_vc_generalization_bound_arbitrary` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Eq. (8.42) | Dudley written as a sum over admissible scales. | `HDP.Chapter8.discreteDudleyInequality_coveringNumber` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Eq. (8.43) | Admissible sequence cardinality bounds. | `HDP.FiniteAdmissibleChain` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Eq. (8.44) | Dudley chain cost has supremum inside the scale sum. | `HDP.Chapter8.realChainCost` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Eq. (8.45) | Definition of `gamma2`. | `HDP.gamma2` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Eq. (8.46) | Choose a chain with cost within factor two of `gamma2`. | `HDP.gamma2_le_chainCost` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Eq. (8.47) | Generic-chain telescoping expansion. | `HDP.Chapter8.admissibleProjection` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Eq. (8.48) | Desired simultaneous weighted increment control. | `HDP.Chapter8.edgeIncrement_le_of_notMem_genericChainBad` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Eq. (8.49) | Single-edge subgaussian tail at scale `2^{k/2}`. | `HDP.Chapter8.edgeIncrement_tail` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Eq. (8.50) | Summed increment control by chain cost. | `HDP.Chapter8.truncatedFineIncrement_le` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Eq. (8.51) | Radius of a Euclidean set. | `HDP.Chapter7.finiteRadius` | [`Chapter7_RandomProcesses.lean`](Chapter7_RandomProcesses.lean) |
| Eq. (8.52) | Chevet bilinear process has increments controlled by opposite radii. | `HDP.Chapter8.equation_8_52_row_increment` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |
| Sec. 8.1 after Theorem 8.1.3 | Metric entropy alone cannot close the Sudakov--Dudley gap. | `HDP.Chapter8.exercise_8_4a_weightedBasis_actualGaussianWidth` | [`Chapter8_Chaining.lean`](Chapter8_Chaining.lean) |

### Chapter 9 — Deviations of Random Matrices on Sets

| Book source | Result | Lean declaration | Final module |
|---|---|---|---|
| Section 9.2.3 | The covariance ellipsoid generated by `B` has outer radius `‖B‖`. | `HDP.Chapter9.covarianceEllipsoid_radius` | [`Chapter9_DeviationsOfRandomMatricesOnSets.lean`](Chapter9_DeviationsOfRandomMatricesOnSets.lean) |
| Theorem 9.1.2 | The matrix norm-deviation process has subgaussian increments. | `HDP.Chapter9.theorem_9_1_2_subGaussianIncrements` | [`Chapter9_DeviationsOfRandomMatricesOnSets.lean`](Chapter9_DeviationsOfRandomMatricesOnSets.lean) |
| Example 9.4.1 | Audio sampling is a high-dimensional linear inverse problem. | `HDP.Chapter9.example_9_4_1_audioSampling` | [`Chapter9_DeviationsOfRandomMatricesOnSets.lean`](Chapter9_DeviationsOfRandomMatricesOnSets.lean) |
| Example 9.4.2 | Linear regression is a noisy linear inverse problem. | `HDP.Chapter9.example_9_4_2_linearRegression` | [`Chapter9_DeviationsOfRandomMatricesOnSets.lean`](Chapter9_DeviationsOfRandomMatricesOnSets.lean) |
| Remark 9.4.3 | When `m<n`, recovery needs a structural prior because the measurement map has a nontrivial kernel. | `HDP.Chapter9.remark_9_4_3_structuralPrior` | [`Chapter9_DeviationsOfRandomMatricesOnSets.lean`](Chapter9_DeviationsOfRandomMatricesOnSets.lean) |
| Remark 9.4.9 | The measurement count scales almost linearly with sparsity. | `HDP.Chapter9.remark_9_4_9_sparseSampleScale` | [`Chapter9_DeviationsOfRandomMatricesOnSets.lean`](Chapter9_DeviationsOfRandomMatricesOnSets.lean) |
| Remark 9.4.12 | Low-rank recovery needs far fewer than `d^2` observations. | `HDP.Chapter9.remark_9_4_12_lowRankSampleScale` | [`Chapter9_DeviationsOfRandomMatricesOnSets.lean`](Chapter9_DeviationsOfRandomMatricesOnSets.lean) |
| Lemma 9.5.2 | An `l1`-minimizer's error is no heavier off the true support than on it. | `HDP.Chapter9.lemma_9_5_2_error_heavier_on_support` | [`Chapter9_DeviationsOfRandomMatricesOnSets.lean`](Chapter9_DeviationsOfRandomMatricesOnSets.lean) |
| Lemma 9.5.3 | The normalized recovery error lies in an approximately sparse set. | `HDP.Chapter9.lemma_9_5_3_error_approximatelySparse` | [`Chapter9_DeviationsOfRandomMatricesOnSets.lean`](Chapter9_DeviationsOfRandomMatricesOnSets.lean) |
| Definition 9.5.5 | RIP uniformly bounds `‖Av‖` on sparse vectors. | `HDP.Chapter9.IsRestrictedIsometry` | [`Chapter9_DeviationsOfRandomMatricesOnSets.lean`](Chapter9_DeviationsOfRandomMatricesOnSets.lean) |
| Theorem 9.5.6 | A sufficiently strong higher-order RIP implies exact `l1` recovery. | `HDP.Chapter9.theorem_9_5_6_rip_implies_exactRecovery` | [`Chapter9_DeviationsOfRandomMatricesOnSets.lean`](Chapter9_DeviationsOfRandomMatricesOnSets.lean) |
| Theorem 9.5.7 | A subgaussian random matrix satisfies RIP above the `s log(en/s)` sample scale. | `HDP.Chapter9.theorem_9_5_7_randomRIP` | [`Chapter9_DeviationsOfRandomMatricesOnSets.lean`](Chapter9_DeviationsOfRandomMatricesOnSets.lean) |
| Definition 9.6.1 | A sublinear functional is positive-homogeneous and subadditive and may take negative values. | `HDP.Chapter9.IsPositivelyHomogeneous` | [`Chapter9_DeviationsOfRandomMatricesOnSets.lean`](Chapter9_DeviationsOfRandomMatricesOnSets.lean) |
| Example 9.6.2 | Norms, linear functionals, inner products, and support functions are sublinear examples. | `HDP.Chapter9.innerSublinearFunctional` | [`Chapter9_DeviationsOfRandomMatricesOnSets.lean`](Chapter9_DeviationsOfRandomMatricesOnSets.lean) |
| Theorem 9.6.4 | The centered sublinear-functional process has subgaussian increments. | `HDP.Chapter9.theorem_9_6_4_subgaussianIncrements` | [`Chapter9_DeviationsOfRandomMatricesOnSets.lean`](Chapter9_DeviationsOfRandomMatricesOnSets.lean) |
| Remark 9.7.5 | Random projections exhibit high- and low-dimensional width/diameter phases. | `HDP.Chapter9.haarProjection_expectedDiameter_set` | [`Chapter9_DeviationsOfRandomMatricesOnSets.lean`](Chapter9_DeviationsOfRandomMatricesOnSets.lean) |
| Eq. (9.1) | A fixed vector is approximately norm-preserved by an isotropic subgaussian matrix. | `HDP.Chapter9.matrixDeviation_unit` | [`Chapter9_DeviationsOfRandomMatricesOnSets.lean`](Chapter9_DeviationsOfRandomMatricesOnSets.lean) |
| Eq. (9.2) | Matrix norm-deviation process `Z_x=‖Ax‖-sqrt(m)‖x‖`. | `HDP.Chapter9.matrixDeviationProcess` | [`Chapter9_DeviationsOfRandomMatricesOnSets.lean`](Chapter9_DeviationsOfRandomMatricesOnSets.lean) |
| Eq. (9.3) | `Z` has `psi2` increments bounded by `CK^2 ‖x-y‖`. | `HDP.Chapter9.theorem_9_1_2_subGaussianIncrements` | [`Chapter9_DeviationsOfRandomMatricesOnSets.lean`](Chapter9_DeviationsOfRandomMatricesOnSets.lean) |
| Eq. (9.4) | Unit-vector deviation from `sqrt m` is subgaussian. | `HDP.Chapter9.matrixDeviation_unit` | [`Chapter9_DeviationsOfRandomMatricesOnSets.lean`](Chapter9_DeviationsOfRandomMatricesOnSets.lean) |
| Eq. (9.5) | Norm increments for two unit vectors are subgaussian. | `HDP.Chapter9.matrixDeviation_unit_pair` | [`Chapter9_DeviationsOfRandomMatricesOnSets.lean`](Chapter9_DeviationsOfRandomMatricesOnSets.lean) |
| Eq. (9.6) | Squared norm differences have the expected `sqrt m ‖x-y‖` scale. | `HDP.Chapter9.squaredMatrixIncrement_tail` | [`Chapter9_DeviationsOfRandomMatricesOnSets.lean`](Chapter9_DeviationsOfRandomMatricesOnSets.lean) |
| Eq. (9.7) | Normalized squared-norm difference is a sum of independent products. | `HDP.Chapter9.squaredIncrementSummand` | [`Chapter9_DeviationsOfRandomMatricesOnSets.lean`](Chapter9_DeviationsOfRandomMatricesOnSets.lean) |
| Eq. (9.8) | Bernstein gives a two-regime tail for the squared increment. | `HDP.Chapter9.squaredMatrixIncrement_tail` | [`Chapter9_DeviationsOfRandomMatricesOnSets.lean`](Chapter9_DeviationsOfRandomMatricesOnSets.lean) |
| Eq. (9.9) | Desired subgaussian tail for normalized norm increments. | `HDP.Chapter9.matrixDeviation_unit_pair` | [`Chapter9_DeviationsOfRandomMatricesOnSets.lean`](Chapter9_DeviationsOfRandomMatricesOnSets.lean) |
| Eq. (9.10) | Radial reduction bounds general increments by unit-sphere increments. | `HDP.Chapter9.theorem_9_1_2_subGaussianIncrements` | [`Chapter9_DeviationsOfRandomMatricesOnSets.lean`](Chapter9_DeviationsOfRandomMatricesOnSets.lean) |
| Eq. (9.12) | A set of `N` points has Gaussian complexity `O(sqrt(log N))` after normalization. | `HDP.Chapter7.gaussianFamilyWidth_unit_upper` | [`Chapter7_RandomProcesses.lean`](Chapter7_RandomProcesses.lean) |
| Eq. (9.16) | Noisy linear observation model `y=Ax+w`. | `HDP.Chapter9.noisyLinearObservation` | [`Chapter9_DeviationsOfRandomMatricesOnSets.lean`](Chapter9_DeviationsOfRandomMatricesOnSets.lean) |
| Eq. (9.17) | Structural prior `x in T`. | `HDP.Chapter9.measurementFiber` | [`Chapter9_DeviationsOfRandomMatricesOnSets.lean`](Chapter9_DeviationsOfRandomMatricesOnSets.lean) |
| Eq. (9.18) | Constrained feasibility program `Ax'=y`, `x' in T`. | `HDP.Chapter9.IsConstrainedRecoverySolution` | [`Chapter9_DeviationsOfRandomMatricesOnSets.lean`](Chapter9_DeviationsOfRandomMatricesOnSets.lean) |
| Eq. (9.20) | Penalized unconstrained recovery objective. | `HDP.Chapter9.penalizedRecoveryObjective` | [`Chapter9_DeviationsOfRandomMatricesOnSets.lean`](Chapter9_DeviationsOfRandomMatricesOnSets.lean) |
| Eq. (9.21) | `ell0` counts nonzero coordinates and defines sparsity. | `HDP.Chapter9.coordinateSupport` | [`Chapter9_DeviationsOfRandomMatricesOnSets.lean`](Chapter9_DeviationsOfRandomMatricesOnSets.lean) |
| Eq. (9.22) | Convex sparse prior `sqrt(s) B_1^n`. | `HDP.Chapter9.sparseRecoveryPrior` | [`Chapter9_DeviationsOfRandomMatricesOnSets.lean`](Chapter9_DeviationsOfRandomMatricesOnSets.lean) |
| Eq. (9.23) | Sparse recovery by feasibility over the `l1` prior. | `HDP.Chapter9.sparseRecoveryPrior` | [`Chapter9_DeviationsOfRandomMatricesOnSets.lean`](Chapter9_DeviationsOfRandomMatricesOnSets.lean) |
| Eq. (9.24) | Sparse recovery becomes nontrivial at `m` of order `s log n`. | `HDP.Chapter9.remark_9_4_9_sparseSampleScale` | [`Chapter9_DeviationsOfRandomMatricesOnSets.lean`](Chapter9_DeviationsOfRandomMatricesOnSets.lean) |
| Eq. (9.25) | Low-rank matrix measurements are Frobenius inner products. | `HDP.Chapter9.matrixMeasurements` | [`Chapter9_DeviationsOfRandomMatricesOnSets.lean`](Chapter9_DeviationsOfRandomMatricesOnSets.lean) |
| Eq. (9.26) | Nuclear-norm constrained recovery program. | `HDP.Chapter9.nuclearPrior` | [`Chapter9_DeviationsOfRandomMatricesOnSets.lean`](Chapter9_DeviationsOfRandomMatricesOnSets.lean) |
| Eq. (9.27) | Basis pursuit minimizes `l1` subject to `Ax'=y`. | `HDP.Chapter9.IsL1RecoveryMinimizer` | [`Chapter9_DeviationsOfRandomMatricesOnSets.lean`](Chapter9_DeviationsOfRandomMatricesOnSets.lean) |
| Eq. (9.28) | Minimality plus triangle inequality yields the support-imbalance bound. | `HDP.Chapter9.lemma_9_5_2_error_heavier_on_support` | [`Chapter9_DeviationsOfRandomMatricesOnSets.lean`](Chapter9_DeviationsOfRandomMatricesOnSets.lean) |
| Eq. (9.29) | A nonzero normalized error lies in the approximate-sparse set and the kernel. | `HDP.Chapter9.normalized_minimizerError_mem_approximatelySparseUnitSet` | [`Chapter9_DeviationsOfRandomMatricesOnSets.lean`](Chapter9_DeviationsOfRandomMatricesOnSets.lean) |
| Eq. (9.30) | The approximate-sparse set has width `O(sqrt(s log n))`. | `HDP.Chapter9.euclideanSetGaussianWidth_approximatelySparseUnitSet_le` | [`Chapter9_DeviationsOfRandomMatricesOnSets.lean`](Chapter9_DeviationsOfRandomMatricesOnSets.lean) |
| Eq. (9.31) | RIP is equivalent to uniform singular-value bounds on sparse coordinate restrictions. | `HDP.Chapter9.IsRestrictedIsometry` | [`Chapter9_DeviationsOfRandomMatricesOnSets.lean`](Chapter9_DeviationsOfRandomMatricesOnSets.lean) |
| Eq. (9.32) | Kernel decomposition relates the leading sparse block to the tail blocks. | `HDP.Chapter9.theorem_9_5_6_rip_implies_exactRecovery` | [`Chapter9_DeviationsOfRandomMatricesOnSets.lean`](Chapter9_DeviationsOfRandomMatricesOnSets.lean) |
| Eq. (9.33) | RIP converts the kernel decomposition into a norm inequality. | `HDP.Chapter9.theorem_9_5_6_rip_implies_exactRecovery` | [`Chapter9_DeviationsOfRandomMatricesOnSets.lean`](Chapter9_DeviationsOfRandomMatricesOnSets.lean) |
| Eq. (9.34) | Each sparse submatrix has near-`sqrt m` singular values with high probability. | `HDP.Chapter9.theorem_9_5_7_randomRIP` | [`Chapter9_DeviationsOfRandomMatricesOnSets.lean`](Chapter9_DeviationsOfRandomMatricesOnSets.lean) |
| Eq. (9.35) | Support functional of a bounded set. | `HDP.Chapter9.setSupportFunctional` | [`Chapter9_DeviationsOfRandomMatricesOnSets.lean`](Chapter9_DeviationsOfRandomMatricesOnSets.lean) |
| Eq. (9.36) | Sublinear functional has Euclidean linear growth `f(x) <= b ‖x‖`. | `HDP.Chapter9.HasEuclideanGrowth` | [`Chapter9_DeviationsOfRandomMatricesOnSets.lean`](Chapter9_DeviationsOfRandomMatricesOnSets.lean) |
| Eq. (9.37) | Centered functional-deviation process `f(Ax)-E f(Ax)`. | `HDP.Chapter9.functionalDeviationProcess` | [`Chapter9_DeviationsOfRandomMatricesOnSets.lean`](Chapter9_DeviationsOfRandomMatricesOnSets.lean) |
| Eq. (9.38) | Functional-deviation process has subgaussian increments. | `HDP.Chapter9.theorem_9_6_4_subgaussianIncrements` | [`Chapter9_DeviationsOfRandomMatricesOnSets.lean`](Chapter9_DeviationsOfRandomMatricesOnSets.lean) |
| Eq. (9.39) | Unit-vector specialization of functional increment control. | `HDP.Chapter9.theorem_9_6_4_subgaussianIncrements` | [`Chapter9_DeviationsOfRandomMatricesOnSets.lean`](Chapter9_DeviationsOfRandomMatricesOnSets.lean) |
| Eq. (9.40) | Orthogonal sum/difference change of variables. | `HDP.Chapter9.theorem_9_6_4_subgaussianIncrements` | [`Chapter9_DeviationsOfRandomMatricesOnSets.lean`](Chapter9_DeviationsOfRandomMatricesOnSets.lean) |
| Eq. (9.41) | First conditionally centered functional has a Gaussian concentration bound. | `HDP.Chapter9.theorem_9_6_4_subgaussianIncrements` | [`Chapter9_DeviationsOfRandomMatricesOnSets.lean`](Chapter9_DeviationsOfRandomMatricesOnSets.lean) |
| Eq. (9.42) | The reflected functional has the same concentration bound. | `HDP.Chapter9.theorem_9_6_4_subgaussianIncrements` | [`Chapter9_DeviationsOfRandomMatricesOnSets.lean`](Chapter9_DeviationsOfRandomMatricesOnSets.lean) |
| Eq. (9.43) | Support functional grows at most as `rad(S) ‖x‖`. | `HDP.Chapter9.setSupportFunctional_growth` | [`Chapter9_DeviationsOfRandomMatricesOnSets.lean`](Chapter9_DeviationsOfRandomMatricesOnSets.lean) |
| Eq. (9.44) | Mean support after Gaussian matrix action equals `‖x‖ w(S)`. | `HDP.Chapter9.functionalDeviationProcess_setSupport_eq` | [`Chapter9_DeviationsOfRandomMatricesOnSets.lean`](Chapter9_DeviationsOfRandomMatricesOnSets.lean) |
| Sec. 9.2.1, before Proposition 9.2.1 | Applying matrix deviation to the unit sphere recovers two-sided singular-value bounds. | `HDP.Chapter9.section_9_2_1_twoSidedSingularValues` | [`Chapter9_DeviationsOfRandomMatricesOnSets.lean`](Chapter9_DeviationsOfRandomMatricesOnSets.lean) |
| Sec. 9.2.2, proof of Proposition 9.2.1 | The difference-set Gaussian complexity satisfies `gamma(T-T)=2w(T)`. | `HDP.Chapter7.gaussianComplexity_difference` | [`Chapter7_RandomProcesses.lean`](Chapter7_RandomProcesses.lean) |
| Sec. 9.3.1, after Theorem 9.3.1 | A random full-row-rank matrix has kernel dimension `n-m`. | `HDP.Chapter9.ae_finrank_kernel_eq_sub_of_ae_fullRowRank` | [`Chapter9_DeviationsOfRandomMatricesOnSets.lean`](Chapter9_DeviationsOfRandomMatricesOnSets.lean) |
| Sec. 9.4.2, before (9.22) | Every `s`-sparse unit vector has `l1` norm at most `sqrt s`. | `HDP.Chapter9.ellOne_le_sqrt_sparse_mul_norm` | [`Chapter9_DeviationsOfRandomMatricesOnSets.lean`](Chapter9_DeviationsOfRandomMatricesOnSets.lean) |
| Sec. 9.4.3, before (9.26) | Rank-`r` matrices have nuclear norm at most `sqrt r` times Frobenius norm. | `HDP.Chapter9.matrixNuclearNorm_le_sqrt_rank_mul_frobenius` | [`Chapter9_DeviationsOfRandomMatricesOnSets.lean`](Chapter9_DeviationsOfRandomMatricesOnSets.lean) |
| Proof of Theorem 9.6.4 | A sublinear functional with Euclidean growth is Lipschitz. | `HDP.Chapter9.SublinearFunctional.lipschitzWith_of_growth` | [`Chapter9_DeviationsOfRandomMatricesOnSets.lean`](Chapter9_DeviationsOfRandomMatricesOnSets.lean) |
