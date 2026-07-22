# Post-correction whole-book review and formalization hand-off

This file records the complete PDF-grounded gap audit, source-faithfulness issues, proof-status boundary, and every compromise made while consolidating the core chapters. The companion master map is `HighDimensionalProbability/README.md`.

## Coverage summary

The frozen audit supplied **873 input rows**. Revalidation against the
second-edition PDF rejects **35** of those rows as non-conclusions, proof-local
steps, bibliographic/algorithmic commentary, open problems, or
non-load-bearing exercise obligations. The resulting mathematical census has
**838 valid conclusions**: **768 formalized**, **0 partial**, **0 missing**, and
**70 appendix-owned or deferred**. The **191** wholly non-load-bearing practice
exercise numbers remain outside the census.

| Chapter | Frozen input rows | Formalized | Appendix-owned / deferred | Rejected after PDF revalidation | Valid conclusions | Practice exercise numbers out of scope |
|---|---:|---:|---:|---:|---:|---:|
| Appetizer | 11 | 11 | 0 | 0 | 11 | 6 |
| Chapter 1 | 63 | 62 | 1 | 0 | 63 | 6 |
| Chapter 2 | 79 | 70 | 1 | 8 | 71 | 29 |
| Chapter 3 | 111 | 96 | 1 | 14 | 97 | 31 |
| Chapter 4 | 120 | 117 | 0 | 3 | 117 | 23 |
| Chapter 5 | 112 | 99 | 13 | 0 | 112 | 5 |
| Chapter 6 | 51 | 47 | 0 | 4 | 47 | 28 |
| Chapter 7 | 87 | 81 | 1 | 5 | 82 | 10 |
| Chapter 8 | 123 | 113 | 10 | 0 | 123 | 27 |
| Chapter 9 | 116 | 72 | 43 | 1 | 115 | 26 |
| **Whole book** | **873** | **768** | **70** | **35** | **838** | **191** |

These figures use three deliberately different denominators:

- The **frozen row census** is the historical snapshot:
  **717 proved / 55 partial / 34 missing / 67 appendix = 873**. Its labels are
  audit inputs, not the final mathematical verdict.
- The **PDF-revalidated census** reclassifies the 89 old gap rows as
  51 formalized, 35 rejected, and 3 appendix-owned/deferred. Together with the
  frozen 717 proved and 67 appendix rows, this gives the final
  **768 / 0 / 0 / 70** valid-conclusion split above.
- The public **README correspondence table is curated for publication** and
  contains only selected formalized book-to-Lean mappings. Its row count is
  **611**; it must not be compared directly
  with either the 873 audit-input rows or the 838 valid conclusions.

This is the final audit. Every accepted core endpoint in the 89-row
disposition table below has been integrated; the remaining dynamic build,
documentation, token, and axiom checks are recorded in the final proof and
repository audit.

## Final proof and repository audit

- **Core build:** the final default `lake build` completed successfully:
  **8,670 / 8,670** jobs.
- **Declaration documentation:** the strict lexical audit checked **5,987**
  theorem/lemma/definition declarations across **101** non-appendix source
  files; all 5,987 have attached docstrings and there are **0** label or
  citation-shape issues.
- **Declaration-preservation regression:** all **5,469** declarations in the
  prior public consolidated core were preserved by file, kind, and name; the
  corrected source adds **75** declarations and removes none.
- **Proof-token scan:** all **25** core files have zero code occurrences of
  `sorry`, `admit`, `axiom`, or `unsafe`. The **228** remaining `sorry`
  occurrences are confined to **46** non-load-bearing exercise-leaf files,
  and all 228 have an `EXERCISE-SORRY` marker; exercise leaves contain no
  `admit`, `axiom`, or `unsafe`.
- **Exhaustive published-row axiom audit:** **526** unique Lean endpoints cover
  all **611** published rows. Of these, 522 depend on exactly
  `[propext, Classical.choice, Quot.sound]`; two on
  `[propext, Quot.sound]`; one on `[Quot.sound]`; and one on no axioms.
  No endpoint has a project-specific or unexpected axiom.
- **README/master-map integrity:** **611** correspondence rows, distributed as
  Appetizer 8 and Chapters 1–9:
  **51 / 59 / 75 / 88 / 68 / 39 / 62 / 100 / 61**. All **603** local
  final-module links (16 unique targets) exist; the other 8 rows explicitly
  point into the pinned Mathlib source tree.
- **Appendix boundary:** `HighDimensionalProbability/Appendix.lean` and
  `HighDimensionalProbability/Appendix/**` were excluded from consolidation, comment-edit, and
  verification scripts. This pass did not add shims or repoint appendix imports; the appendix
  remains separately maintained and may lag the consolidated core module names.

## Citation and Author-note audit

This pass made **884 explicitly countable citation corrections**: 844 mechanically
detected legacy, unbolded, or citation-before-description defects; 35 source-numbered
Tropp references in `Prelude/MatrixConcentration.lean` that were reclassified as
separate implementation infrastructure rather than Vershynin book citations; and five
exercise-part corrections for Exercises 2.44(c) and 2.48(a--d). Additional prose was
rewritten for semantic clarity without inflating this count.

Four declarations carry an informational `**Author note.**`, all in
`HighDimensionalProbability/Prelude/MatrixConcentration.lean`:

- `MatrixConcentration.matrix_bernstein_herm_expectation`
- `MatrixConcentration.matrix_bernstein_herm_tail`
- `MatrixConcentration.matrix_bernstein_rect_expectation_ae`
- `MatrixConcentration.matrix_bernstein_rect_tail_ae`

## Consolidation record and merge compromises

- The numbered core modules imported by each `ChapterN/Main.lean` were consolidated into the nine chapter files listed in the README. Chapter 8's transitively imported numbered `03_EmpiricalProcessesFoundations` module was also absorbed because it contains substantive §8.2 core declarations. Old numbered core files were removed, editable imports were repointed, and exercise/Prelude layouts were retained.
- Chapter 3 required a dependency-safe topological order rather than the literal `Main.lean` order: `01`, `02`, `03`, `04`, `05`, `08`, `07`, `09`, `10`, `11`, `12`, `13`, `06`, `16`, `17`, `20`, `19`, `21`, `18`, `22`, `23`, `24`, `14`, `15`, `25`, `26`, `27`. Declarations remain in source-block order within each module.
- Each former source module is wrapped in an outer section so its local `open`, `variable`, and option state cannot leak into the next merged block.
- Four source-local `private` names collided after physical concatenation and were minimally renamed; public fully-qualified names are unchanged:
  - Chapter 3 source `05_MomentGeometry`: `vectorOfCoordinates` became `vectorOfCoordinates_density` (four code-token occurrences).
  - Chapter 4 source `13_SubGaussianMatrixNorms`: `integral_le_of_quadratic_gaussian_tail` became `integral_le_of_quadratic_gaussian_tail_subgaussian_matrix` (two occurrences).
  - Chapter 6 source `09_SymmetricRandomMatrices`: `rectangularMatrixOpNorm_integrable_of_coordinates` became `rectangularMatrixOpNorm_integrable_of_coordinates_symmetric_matrix` (two occurrences).
  - Chapter 9 source `10_ConstrainedRecovery`: `exists_finset_generator_of_mem_convexHull` became `exists_finset_generator_of_mem_convexHull_constrained_recovery` (two occurrences).
- `HighDimensionalProbability/Appendix.lean` and the entire `HighDimensionalProbability/Appendix/` directory were excluded from the consolidation and comment-edit scripts. No shim was left for deleted core modules, and no appendix import was repointed by this pass.

## Chapter-by-chapter build gates

Each affected consolidated module was rebuilt as corrections landed. The
final Chapter 3 regression completed **8,567 / 8,567** jobs, and the final
root-module regression completed **8,670 / 8,670** jobs.

## Audit interpretation

- `FORMALIZED` means the PDF conclusion has a source-facing, kernel-checked
  endpoint that passed the final aggregate build and axiom gates above.
- `REJECTED` means PDF inspection showed that the input row was not a separate
  in-scope mathematical conclusion. Rejection never means that a genuine
  theorem was silently dropped.
- `IN-APPENDIX` means the valid conclusion naturally depends on an external
  theorem or isolated principle. A conditional core wrapper is not counted as
  an unconditional core proof.
- Non-load-bearing practice exercises and their `EXERCISE-SORRY` leaves are
  intentionally outside the 838-conclusion census.

## Rejected input rows after PDF revalidation

The following list is exhaustive: exactly **35** of the 873 frozen input rows
were audit false positives or deliberately out-of-scope non-conclusions.

| Chapter | Book ref | PDF-grounded rejection reason |
|---|---|---|
| Chapter 2 | (2.2) | The PDF explicitly calls the moving-threshold CLT substitution unjustified; it is a heuristic, not a theorem. |
| Chapter 2 | Remark 2.1.3 | The remark only points to non-load-bearing Exercise 2.3 for sharper Mills-ratio expansions. |
| Chapter 2 | Remark 2.2.3 | “Non-asymptotic” is methodological prose, not a mathematical proposition. |
| Chapter 2 | Remark 2.3.3 | Qualitative Poisson-versus-Gaussian tail interpretation; the fixed mathematical ingredients are already formalized. |
| Chapter 2 | Remark 2.3.5 | Plotting and two-regime PMF intuition, not a separately quantified conclusion. |
| Chapter 2 | Remark 2.7.2 | The reverse-bound tasks are delegated entirely to non-load-bearing Exercises 2.33–2.34. |
| Chapter 2 | Remark 2.8.2 | An explicitly informal Taylor approximation with no quantified remainder statement. |
| Chapter 2 | Remark 2.9.3 | Interpretation of the already-formalized two-regime tail and exponential obstruction, not an additional theorem. |
| Chapter 3 | Remark 3.2.4 | Practical PCA guidance with no error criterion or mathematical assertion. |
| Chapter 3 | (3.17) | Explicitly informal Gaussian/sphere heuristic; the neighboring rigorous results are separate rows. |
| Chapter 3 | (3.18) | A proof decomposition for the projective CLT, not an independent conclusion. |
| Chapter 3 | (3.20) | A proof-local conditioning identity for one route to Theorem 3.4.5. |
| Chapter 3 | (3.21) | A proof-local Laplace/product evaluation for that same route. |
| Chapter 3 | (3.25) | A proof-local truncation estimate superseded by the stronger compiled Krivine proof. |
| Chapter 3 | Example 3.7.2 | Vector/matrix cases are definitional specializations of the formalized tensor type. |
| Chapter 3 | Remark 3.7.9 | Algorithmic interpretation of the compiled randomized-rounding proof, not a new probability conclusion. |
| Chapter 3 | Notes after Theorem 3.1.1 | A literature note on a later optimal constant, outside the theorem proved in the book. |
| Chapter 3 | Notes on Krivine constant | A state-of-knowledge statement rather than a fixed theorem target. |
| Chapter 3 | Notes on Goemans--Williamson | Historical/complexity commentary and a conjecture-conditional hardness claim. |
| Chapter 3 | Notes improving Exercise 3.13 | A notes-only sharpening of a non-load-bearing exercise. |
| Chapter 3 | Notes on PSD Grothendieck | The claimed optimality belongs to non-load-bearing exercise/literature discussion. |
| Chapter 3 | Exercise 3.55 | Non-load-bearing practice exercise; its main-line entire-series bridge is already formalized under Lemma 3.7.7. |
| Chapter 4 | Remark 4.2.13 | The random construction is formalized; the lattice construction is delegated to a non-load-bearing exercise. |
| Chapter 4 | Exercise Eq. (4.31) | A displayed obligation inside non-load-bearing Exercise 4.18. |
| Chapter 4 | Exercise 4.18 | Non-load-bearing practice exercise, outside the publication census. |
| Chapter 6 | Remark 6.5.2 | Qualitative rectangular/noisy/log-free/exact-recovery directions with no uniquely specified theorem. |
| Chapter 6 | Remark 6.5.2 qualitative tail | Duplicate audit row for the same hypothesis-free qualitative improvement prose. |
| Chapter 6 | Exercise 6.31 | “State and prove a version” supplies no unique rectangular target and is non-load-bearing. |
| Chapter 6 | Exercise 6.32 | “Extend” supplies no unique noise model, normalization, or rate and is non-load-bearing. |
| Chapter 7 | Example 7.1.2 | Terminological identification of a finitely indexed process with random-vector data. |
| Chapter 7 | Example 7.1.3 | Explanatory definition of a random walk; no separate asserted estimate. |
| Chapter 7 | Example 7.1.4 | Explanatory Brownian-motion description, not a standalone conclusion in the chapter’s theorem dependency chain. |
| Chapter 7 | Example 7.1.5 | Terminological definition of a random field. |
| Chapter 7 | Remark 7.5.10 | Qualitative synthesis of preceding width/diameter examples, with no single quantified claim. |
| Chapter 9 | Remark 9.6.5 | The PDF explicitly labels extension to subgaussian matrices an open problem; no theorem or axiom should be invented. |

## Newly deferred appendix-owned rows

These **3** valid rows move from the old gap table to the appendix-owned
boundary. They are additional to the 67 rows that were already appendix-owned
in the frozen census.

| Chapter | Book ref | Reason for appendix ownership |
|---|---|---|
| Chapter 3 | Example 3.4.6 | The remaining arbitrary-convex-body `ψ₁` statement is attributed to Borell/Brunn–Minkowski without proof and is unused downstream; the bounded-body part is core-formalized and the isotropic cube requires `√3` scaling. |
| Chapter 5 | Eq. (5.2) | It is a specialization of spherical isoperimetry, whose authoritative theorem is isolated in the off-limits appendix subtree. |
| Chapter 7 | Sec. 7.2.1 Brownian reflection example | The expectation identity uses the external reflection principle, with proof assigned to non-load-bearing Exercise 7.2, and is unused downstream. |

## Disposition of the 89 frozen gap rows

The frozen gap inventory contained **45 `PARTIAL`**, **34 `MISSING`**, and
**10 `UNSURE`** rows. PDF revalidation assigns 51 to `FORMALIZED`, 35 to
`REJECTED`, and 3 to `IN-APPENDIX`. Every accepted core endpoint, including
Examples 3.4.7–3.4.8, is now integrated; no historical gap label remains
unresolved.

| Chapter | Book ref | Validated disposition | Result | Located Lean evidence | Audited file evidence | Validation evidence and disposition |
|---|---|---|---|---|---|---|
| Appetizer | Theorem 0.0.2 | FORMALIZED | Approximate Caratheodory: an equal average of `k` points approximates any point of the convex hull within `1/sqrt(k)`. | `HDP.Chapter0.approximate_caratheodory` | `HighDimensionalProbability/Chapter0_Appetizer.lean` | Exact Hilbert-space empirical-method theorem, supported by the load-bearing vector second-moment identities below. |
| Appetizer | Corollary 0.0.3 | FORMALIZED | An `N`-vertex polytope in the unit ball has an `N^k`-point cover at radius `1/sqrt(k)`. | `HDP.Chapter0.exists_polytope_cover` | `HighDimensionalProbability/Chapter0_Appetizer.lean` | Exact finite internal center set, cover property, and cardinality bound. |
| Appetizer | Theorem 0.0.4; (0.2) | FORMALIZED | The relative volume of an `N`-vertex polytope in the unit ball is at most `(3 sqrt(log N/n))^n`. | `HDP.Chapter0.polytope_volume_theorem_0_0_4` | `HighDimensionalProbability/Chapter0_Appetizer.lean` | Exact rounded-integer proof, including the `N=0,1` and large-`N` branches; the direct multiplication form is also exposed. |
| Appetizer | (0.3) | FORMALIZED | Before optimizing, the covering argument gives `Vol(P)/Vol(B) <= N^k/k^(n/2)`. | `HDP.Chapter0.polytope_volume_equation_0_3` | `HighDimensionalProbability/Chapter0_Appetizer.lean` | Exact division-free equivalent of the displayed relative-volume estimate. |
| Appetizer | (0.4) | FORMALIZED | The continuous optimizer is `k0 = n/(2 log N)`. | `HDP.Chapter0.polytope_volume_optimizer_equation_0_4`; `polytope_volume_optimizer_unique` | `HighDimensionalProbability/Chapter0_Appetizer.lean` | The positive critical-point equation and uniqueness of its positive solution are both explicit. |
| Appetizer | Remark 0.0.5 | FORMALIZED | Polytopes with subexponentially many vertices occupy vanishingly small relative volume. | `HDP.Chapter0.polytope_volume_remark_0_0_5` | `HighDimensionalProbability/Chapter0_Appetizer.lean` | Formalized as `log(N n)/n→0`, proving both the comparison radius and the exact `n`th-power volume coefficient tend to zero. |
| Appetizer | Exercise 0.1(a) | FORMALIZED | Vector bias-variance identity: `E ‖Z-EZ‖^2 = E ‖Z‖^2-‖EZ‖^2`. | `HDP.Chapter0.integral_norm_sub_mean_sq` | `HighDimensionalProbability/Chapter0_Appetizer.lean` | Exact square-integrable real-Hilbert-space identity used by Theorem 0.0.2. |
| Appetizer | Exercise 0.2 | FORMALIZED | The mean minimizes expected squared distance. | `HDP.Chapter0.integral_norm_sub_mean_sq_le` | `HighDimensionalProbability/Chapter0_Appetizer.lean` | Exact vector-valued minimization theorem; it strictly subsumes the earlier scalar infrastructure. |
| Appetizer | Exercise 0.3 | FORMALIZED | Independent mean-zero random vectors satisfy `E ‖sum Z_j‖^2 = sum E ‖Z_j‖^2`. | `HDP.Chapter0.integral_norm_sum_sq_of_iIndepFun` | `HighDimensionalProbability/Chapter0_Appetizer.lean` | Exact finite independent-family identity used in the empirical-method proof. |
| Chapter 1 | Markov optimality prose | FORMALIZED | With only the mean known, Markov's bound is best possible. | `HDP.Chapter1.markov_inequality_is_sharp` | `HighDimensionalProbability/Chapter1_AnalysisAndProbabilityRefresher.lean` | An explicit two-point probability mass function attains Markov's upper bound for every admissible mean/threshold pair. |
| Chapter 1 | Notes: sharp Robbins/Stirling bounds | FORMALIZED | Two-sided `sqrt(2 pi n)(n/e)^n exp(1/(12n+1)) <= n! <= ... exp(1/(12n))`. | `HDP.Chapter1.factorial_robbins_two_sided` | `HighDimensionalProbability/Prelude/RobbinsStirling.lean` | Exact global endpoint, derived from sharp step bounds and the Stirling-sequence limit. |
| Chapter 2 | Question 2.1.1; (2.1) | FORMALIZED | Chebyshev gives only `P(S_N >= 3N/4) <= 4/N` for fair coin flips. | `HDP.Chapter2.fair_coin_chebyshev_equation_2_1` | `HighDimensionalProbability/Chapter2_ConcentrationOfIndependentSums.lean` | Exact fair-coin calculation and printed `4/N` endpoint. |
| Chapter 2 | (2.2) | REJECTED | CLT heuristic replaces the normalized coin sum by a standard Gaussian at a threshold growing with `N`. | `HDP.Chapter1.central_limit_theorem`; `deMoivreLaplace` (rigorous neighboring results) | `HighDimensionalProbability/Chapter1_AnalysisAndProbabilityRefresher.lean` | The PDF explicitly says the moving-threshold substitution is not justified by the ordinary CLT; it is not a theorem obligation. |
| Chapter 2 | Remark 2.1.3 | REJECTED | More precise Mills-ratio expansions are available. | `HDP.Chapter2.gaussian_mills_identity` (supporting main-text identity) | `HighDimensionalProbability/Chapter2_ConcentrationOfIndependentSums.lean` | The remark only directs the reader to non-load-bearing Exercise 2.3. |
| Chapter 2 | Remark 2.2.3 | REJECTED | Concentration inequalities are non-asymptotic. | — | — | Methodological prose, not a mathematical proposition. |
| Chapter 2 | Remark 2.3.3 | REJECTED | Chernoff resembles a Poisson point mass; Poisson tails decay like `exp(-t log t)` and are heavier than Gaussian. | `HDP.Chapter1.poisson_pmf_asymptotic`; `HDP.Chapter2.chernoff_upper` | `HighDimensionalProbability/Chapter1_AnalysisAndProbabilityRefresher.lean`; `HighDimensionalProbability/Chapter2_ConcentrationOfIndependentSums.lean` | Qualitative comparison only; the fixed Poisson asymptotic and Chernoff theorem are already formalized. |
| Chapter 2 | Remark 2.3.5 | REJECTED | Binomial/Poisson behavior is Gaussian near the mean and Poisson-like far away. | `HDP.Chapter2.chernoff_normalized`; `HDP.Chapter1.poisson_limit_theorem` (appendix) | `HighDimensionalProbability/Chapter2_ConcentrationOfIndependentSums.lean`; `HighDimensionalProbability/Appendix/PoissonLimitTheorem.lean` | Plotting/two-regime intuition, not a separately quantified conclusion. |
| Chapter 2 | Median robustness prose | FORMALIZED | A single extreme outlier moves a median only to a neighboring order statistic. | `HDP.Chapter2.median_one_coordinate_robust` | `HighDimensionalProbability/Chapter2_ConcentrationOfIndependentSums.lean` | Exact cardinal/rank-witness formulation of one-coordinate contamination robustness. |
| Chapter 2 | Example 2.6.5 | FORMALIZED | Standard Gaussian, Rademacher, Bernoulli, binomial, and bounded laws provide the main-text subgaussian examples. | `HDP.psi2Norm_standardGaussian`; `psi2Norm_rademacher`; `psi2Norm_bernoulli`; `psi2Norm_le_of_bounded`; sum closure | `HighDimensionalProbability/Chapter2_ConcentrationOfIndependentSums.lean` | All main-text positive examples are covered. The longer negative named-law checklist belongs to non-load-bearing Exercise 2.25 and is excluded from this row's validated scope. |
| Chapter 2 | Remark 2.7.2 | REJECTED | A reverse bound holds for identically distributed summands but fails in general. | — | — | The claimed checks are delegated entirely to non-load-bearing Exercises 2.33–2.34. |
| Chapter 2 | Remark 2.8.2 | REJECTED | A centered unit-variance MGF is approximately Gaussian near zero by Taylor expansion. | — | — | Explicit intuition without a quantified remainder theorem. |
| Chapter 2 | Example 2.8.7 | FORMALIZED | Main-text subexponential examples follow from the generic implications and the exponential-law calculation. | `HDP.subGaussian_to_subExponential`; `HDP.subExponential_sq_iff`; `HDP.exponential_mgf_diverges` | `HighDimensionalProbability/Chapter2_ConcentrationOfIndependentSums.lean` | The general implications and canonical exponential example are exact. The remaining named-law classification checklist is delegated to non-load-bearing Exercise 2.39 and excluded from the validated row scope. |
| Chapter 2 | Remark 2.9.3 | REJECTED | Both Gaussian and exponential tails are necessary; one subexponential term may have an exponential tail. | `HDP.exponential_mgf_diverges`; `HDP.SubExponential.tail_bound` | `HighDimensionalProbability/Chapter2_ConcentrationOfIndependentSums.lean` | Interpretation of the already-formalized two-regime bound and exponential obstruction, not a new theorem. |
| Chapter 3 | Covariance prose | FORMALIZED | `cov(X)=E[XX^T]-mu mu^T`; covariance is symmetric positive semidefinite; for mean zero it equals the second moment. | `HDP.Chapter3.covarianceMatrix_eq_secondMoment_sub_mean`; `covarianceMatrix_eq_secondMoment_of_mean_zero`; covariance symmetry/PSD API | `HighDimensionalProbability/Chapter3_RandomVectorsInHighDimensions.lean`; `HighDimensionalProbability/Prelude/RandomVector.lean` | Exact finite-matrix identity and zero-mean specialization, together with the existing symmetry and positive-semidefiniteness results. |
| Chapter 3 | Corollary 3.2.3 | FORMALIZED | PCA directions successively maximize variance of centered one-dimensional projections. | `HDP.Chapter3.covarianceOperator_reApplyInnerSelf`; `covariance_pca_kth_maximum` | `HighDimensionalProbability/Chapter3_RandomVectorsInHighDimensions.lean` | Exact covariance quadratic-form/variance identity and ordered covariance-PCA maximum principle for square-integrable random vectors. |
| Chapter 3 | Remark 3.2.4 | REJECTED | Keeping the leading principal components gives a practical dimension-reduction method. | — | — | Practical guidance with no asserted error criterion or mathematical endpoint. |
| Chapter 3 | Corollary 3.3.3 | FORMALIZED | A sum of independent normals is normal, with means and variances adding. | `HDP.Chapter3.sum_independent_gaussians_hasGaussianLaw`; `sum_independent_gaussians_parameters` | `HighDimensionalProbability/Chapter3_RandomVectorsInHighDimensions.lean` | Gaussian closure and the printed scalar summed-mean/summed-variance parameters are both exposed. |
| Chapter 3 | Definition 3.3.4 | FORMALIZED | A general Gaussian vector is an affine image `mu+A Z` of a standard Gaussian. | `HDP.Chapter3.affineGaussianMeasure`; `affineGaussianMeasure_eq_multivariateGaussian`; `hasGaussianVectorLaw_iff_affineRepresentation` | `HighDimensionalProbability/Chapter3_RandomVectorsInHighDimensions.lean` | Arbitrary rectangular affine Gaussian measures, covariance `AAᵀ`, and equivalence with `HasGaussianVectorLaw` for positive-semidefinite covariance. |
| Chapter 3 | (3.14) | FORMALIZED | Two independent isotropic directions are almost orthogonal at scale `1/sqrt(n)`. | `HDP.Chapter3.uniformSphere_inner_sq_expectation`; `uniformSphere_almost_orthogonal` | `HighDimensionalProbability/Chapter3_RandomVectorsInHighDimensions.lean` | Exact `1/n` squared-inner-product expectation and normalized Markov tail `≤ 1/C²`. |
| Chapter 3 | (3.17) | REJECTED | Informal heuristic `N(0,I_n) approximately Unif(sqrt(n) S^{n-1})`. | rigorous neighboring sphere/Gaussian results | `HighDimensionalProbability/Chapter3_RandomVectorsInHighDimensions.lean` | The PDF explicitly labels this informal; (3.15), (3.16), and Theorem 3.3.9 are the rigorous conclusions. |
| Chapter 3 | (3.18) | REJECTED | Quantitative CDF error decomposition used in the projective-CLT proof. | `HDP.Chapter3.projectiveRatio_uniform_cdf`; `standardGaussian_cdf_increment_le` | `HighDimensionalProbability/Chapter3_RandomVectorsInHighDimensions.lean` | Proof decomposition rather than an independent conclusion; the compiled endpoint is the stronger uniform projective CLT. |
| Chapter 3 | Theorem 3.4.5; (3.19) | FORMALIZED | Sphere marginal tail `P(<X,v>≥t) ≤ 2 exp(-n t²/2)` and hence the sphere is subgaussian at scale `1/sqrt(n)`. | `HDP.Chapter3.sphere_tail`; `unitSphere_marginal_tail`; `unitSphere_subGaussian`; `psi2NormVector_unitSphere_le` | `HighDimensionalProbability/Chapter3_RandomVectorsInHighDimensions.lean` | The source exponent `-n t²/2` is now exact, including the `t<1` ratio argument, the endpoint, rotation transport, and the stated subgaussian consequences. |
| Chapter 3 | (3.20) | REJECTED | Conditioning identity for the Gaussian-ratio proof of the sphere tail. | `HDP.Chapter3.projectiveRatio_ge_subset_rest_tail`; `projectiveRatio_oneSided_tail_lt_one` | `HighDimensionalProbability/Chapter3_RandomVectorsInHighDimensions.lean` | Proof-local identity, not a separate census conclusion. Faithful event-conditioning helpers now implement its role in the exact proof of Theorem 3.4.5. |
| Chapter 3 | (3.21) | REJECTED | Product/Laplace-transform evaluation for the conditioned Gaussian norm. | `HDP.Chapter3.lintegral_exp_neg_sq_standardGaussian`; `projectiveGaussianCoordinate_rest_tail` | `HighDimensionalProbability/Chapter3_RandomVectorsInHighDimensions.lean` | Proof-local calculation, not a separate census conclusion. The exact one-coordinate Laplace transform and independent-product tail calculation are now compiled as helpers for Theorem 3.4.5. |
| Chapter 3 | Example 3.4.6 | IN-APPENDIX | Uniform convex-body marginals: bounded bodies are subgaussian; Borell gives subexponential marginals for arbitrary convex bodies. | `HDP.bounded_to_subGaussian`; unit-ball/sphere infrastructure | `HighDimensionalProbability/Chapter2_ConcentrationOfIndependentSums.lean`; `HighDimensionalProbability/Chapter3_RandomVectorsInHighDimensions.lean` | The bounded conclusion is covered. The remaining Borell/Brunn–Minkowski statement is an externally cited, unproved, unused ingredient whose natural home is the off-limits appendix; the isotropic cube requires `sqrt(3)` scaling. |
| Chapter 3 | Example 3.4.7 | FORMALIZED | The coordinate distribution has exact vector `psi_2` norm `sqrt(n/log(n+1))`; the unscaled basis law has norm `1/sqrt(log(n+1))`. | `HDP.Chapter3.example_3_4_7_coordinate_distribution`; `standardBasisDistribution_psi2NormVector` | `HighDimensionalProbability/Chapter3_RandomVectorsInHighDimensions.lean` | Exact equalities are proved in the consolidated core, and the former exercise-only placeholder was removed. |
| Chapter 3 | Example 3.4.8 | FORMALIZED | A finite isotropic subgaussian law has entropy at least `n/K^2-log 2` and support cardinality at least `(1/2)exp(n/K^2)`. | `HDP.Chapter3.isotropic_subgaussian_finite_support_entropy_and_card`; `isotropic_finiteShannonEntropy_and_support_lower_bounds` | `HighDimensionalProbability/Chapter3_RandomVectorsInHighDimensions.lean` | The atom-mass estimate, entropy bound, and support bound are kernel-checked in the consolidated core, and the former exercise-only placeholders were removed. |
| Chapter 3 | (3.25) | REJECTED | Explicit `L^2` bound for a truncated Gaussian used in the first Grothendieck proof. | compiled Krivine proof | `HighDimensionalProbability/Chapter3_RandomVectorsInHighDimensions.lean` | Proof-local estimate for an alternate route, superseded by the stronger compiled Krivine proof. |
| Chapter 3 | (3.31) | FORMALIZED | Graph cut cardinality equals the adjacency-matrix sign objective. | `HDP.Chapter3.graphCutObjective_eq_cutValue` | `HighDimensionalProbability/Chapter3_RandomVectorsInHighDimensions.lean` | Exact graph-level equality, proved using the degree-sum formula for the crossing graph. |
| Chapter 3 | (3.32) | FORMALIZED | `maxcut(G)` is the maximum of the sign-matrix objective. | `HDP.Chapter3.graphMaxCut_eq_max_cutMatrixObjective` | `HighDimensionalProbability/Chapter3_RandomVectorsInHighDimensions.lean` | Exact attained maximum characterization. |
| Chapter 3 | Proposition 3.6.3 | FORMALIZED | A uniformly random cut has expected size at least half of maximum cut. | `HDP.Chapter3.randomGraphCut_halfApproximation` | `HighDimensionalProbability/Chapter3_RandomVectorsInHighDimensions.lean` | The integral is the actual graph cut cardinality. |
| Chapter 3 | (3.33) | FORMALIZED | Max-cut SDP objective/maximization. | `HDP.Chapter3.graphSDPValue`; `graphMaxCut_le_graphSDPValue` | `HighDimensionalProbability/Chapter3_RandomVectorsInHighDimensions.lean` | The compact feasible set attains the graph-named SDP optimum, which dominates max-cut. |
| Chapter 3 | Theorem 3.6.4 | FORMALIZED | Goemans--Williamson rounding achieves at least `.878 sdp(G)` and hence `.878 maxcut(G)` in expectation. | `HDP.Chapter3.goemans_williamson_graph_guarantee` | `HighDimensionalProbability/Chapter3_RandomVectorsInHighDimensions.lean` | Exact `439/500` guarantee for the actual rounded graph cut against both graph optima. |
| Chapter 3 | Definition 3.7.1; (3.36) | FORMALIZED | General order-`k` tensors and their coordinate inner product. | `HDP.TensorSpace`; `tensorInner`; `tensorInner_eq_inner`; `tensorPowerSpace_eq_tensorSpace` | `HighDimensionalProbability/Chapter3_RandomVectorsInHighDimensions.lean` | Independently sized dependent finite axes, exact coordinate inner product, and the equal-axis tensor-power specialization. |
| Chapter 3 | Example 3.7.2 | REJECTED | Vectors and matrices are order-one and order-two tensors. | `HDP.TensorSpace`; `HDP.TensorPowerSpace` | `HighDimensionalProbability/Chapter3_RandomVectorsInHighDimensions.lean` | Definitional specializations, not separate mathematical conclusions requiring naming-only wrappers. |
| Chapter 3 | Lemma 3.7.7 | FORMALIZED | Entire real power series has a Hilbert feature-map realization. | `HDP.absolutePowerSummable_of_entire`; `HDP.Chapter3.realAnalytic_featureMap_of_entire` | `HighDimensionalProbability/Chapter3_RandomVectorsInHighDimensions.lean` | Absolute convergence at every radius is derived from pointwise convergence by geometric domination, then fed into the literal-hypothesis feature-map theorem. |
| Chapter 3 | Remark 3.7.9 | REJECTED | Krivine's proof gives a randomized rounding algorithm with an expected bilinear guarantee. | `HDP.Chapter3.grothendieck_inequality`; compiled rounding proof | `HighDimensionalProbability/Chapter3_RandomVectorsInHighDimensions.lean` | Algorithmic interpretation of an already-compiled probabilistic proof, not an additional mathematical endpoint. |
| Chapter 3 | (3.38); Moore--Aronszajn prose | FORMALIZED | A kernel has a Hilbert feature map iff it is positive semidefinite. | `HDP.Chapter3.scalarKernel_featureMap_iff_posSemidef` | `HighDimensionalProbability/Chapter3_RandomVectorsInHighDimensions.lean` | Exact scalar-kernel iff: RKHS construction gives sufficiency, while arbitrary feature Gram kernels give necessity. |
| Chapter 3 | Notes after Theorem 3.1.1 | REJECTED | Dependence on `K` improves from `K^2` to the optimal `K sqrt(log K)`. | — | — | Bibliographic note about a later optimal constant, not the book theorem's fixed conclusion. |
| Chapter 3 | Notes on Krivine constant | REJECTED | The true real Grothendieck constant is strictly below the explicit Krivine value, but no explicit expression is known. | — | — | External state-of-knowledge statement, not a fixed formalization target. |
| Chapter 3 | Notes on Goemans--Williamson | REJECTED | `.878...` is the best known approximation ratio; conditional UGC hardness rules out improvement. | — | — | Historical/complexity commentary with a conjecture-conditional hardness claim. |
| Chapter 3 | Notes improving Exercise 3.13 | REJECTED | For standard Gaussians, `E max_i ‖X_i‖ <= sqrt(n)+sqrt(2 log N)` (the PDF prints `n` in one extraction location, but context is number of samples). | `HDP.Chapter3.exercise_3_13a` | `HighDimensionalProbability/Chapter3_RandomVectorsInHighDimensions.lean` | Notes-only sharpening of a non-load-bearing exercise; sharp-constant completion is outside the exercise policy. |
| Chapter 3 | Notes on PSD Grothendieck | REJECTED | The constant `pi/2` is optimal for PSD Grothendieck. | — | — | Literature/exercise discussion: Exercise 3.57 is non-load-bearing, and its upper bound would not itself establish optimality. |
| Chapter 3 | Exercise 3.55 | REJECTED | Analytic-kernel feature-map construction. | `HDP.absolutePowerSummable_of_entire`; `HDP.Chapter3.realAnalytic_featureMap_of_entire` | `HighDimensionalProbability/Chapter3_RandomVectorsInHighDimensions.lean` | Non-load-bearing practice exercise. Its main-line entire-series bridge is now covered by the formalized Lemma 3.7.7 row. |
| Chapter 4 | Remark 4.1.3 | FORMALIZED | Zero-pad/order singular values and write `A = U Sigma V^T` using square orthogonal matrices. | `HDP.Chapter4.singularValue_eq_zero_of_domain_le`; `rectangularSingularValueMatrix`; `exists_matrixFormSVD` | `HighDimensionalProbability/Chapter4_RandomMatrices.lean` | Orthonormal-family extensions, orthogonal coordinate matrices, the rectangular singular-value diagonal, and the literal matrix factorization are explicit. |
| Chapter 4 | Example 4.1.5 | FORMALIZED | A rank-`k` orthogonal projection is `UU^T`, symmetric, with `k` eigenvalues one and the rest zero. | `HDP.Chapter4.orthogonalProjection_eq_mul_transpose` | `HighDimensionalProbability/Chapter4_RandomMatrices.lean` | One theorem proves symmetry, idempotence, exact rank, identity on the column space, and vanishing on its orthogonal complement. |
| Chapter 4 | Remark 4.1.9 | FORMALIZED | General `p -> q` induced matrix norms and the bilinear dual formula. | `HDP.Chapter4.matrixLpToLpNorm_attained`; `matrixLpToLpNorm_bilinear_isGreatest`; `remark_4_1_9` | `HighDimensionalProbability/Chapter4_RandomMatrices.lean` | Finite-dimensional attainment and an exact `IsGreatest` theorem for primal and conjugate-dual bilinear values, including endpoint exponents. |
| Chapter 4 | Remark 4.2.13 | REJECTED | Euclidean nets can be built by a scaled lattice or by random points. | `HDP.Chapter4.exercise_4_39` (random construction) | `HighDimensionalProbability/Chapter4_RandomMatrices.lean` | The mathematical random construction is formalized; the separate lattice construction is delegated to a non-load-bearing exercise. |
| Chapter 4 | Eq. (4.4) | FORMALIZED | Square matrix form `A = U Sigma V^T`. | `HDP.Chapter4.exists_matrixFormSVD` | `HighDimensionalProbability/Chapter4_RandomMatrices.lean` | Literal square-orthogonal-factor matrix SVD, with the rectangular form proved simultaneously. |
| Chapter 4 | Exercise Eq. (4.31) | REJECTED | General `p -> q` norm equals both a maximum ratio and a bilinear maximum. | `HDP.Chapter4.matrixLpToLpNorm_attained`; `matrixLpToLpNorm_bilinear_isGreatest` (main-text infrastructure) | `HighDimensionalProbability/Chapter4_RandomMatrices.lean` | Displayed obligation inside non-load-bearing Exercise 4.18; the substantive general attainment/duality content is already recorded under Remark 4.1.9. |
| Chapter 4 | Exercise 4.18 | REJECTED | General `p -> q` induced matrix norm, its norm axioms, and transpose duality. | `HDP.Chapter4.matrixLpToLpNorm`; `exercise_4_18b_matrixLpToLpNorm`; `exercise_4_18c_duality` | `HighDimensionalProbability/Chapter4_RandomMatrices.lean` | Non-load-bearing practice exercise, outside the publication census. |
| Chapter 5 | Definition 5.1.1 | FORMALIZED | A map is Lipschitz if distances expand by at most a constant; `‖f‖_Lip` is the least such constant. | `HDP.Chapter5.lipschitzSeminorm`; `lipschitzSeminorm_le_iff`; `LipschitzWith` | `HighDimensionalProbability/Chapter5_ConcentrationWithoutIndependence.lean` | The extended least constant is explicit and exactly characterized; the PDF's false unrestricted differentiable-implies-Lipschitz sentence remains corrected to the bounded-derivative theorem. |
| Chapter 5 | Example 5.1.2 | FORMALIZED | Linear functionals, matrices, and norm maps have the advertised exact Lipschitz constants. | `HDP.Chapter5.example_5_1_2a`; `example_5_1_2b`; `example_5_1_2c` | `HighDimensionalProbability/Chapter5_ConcentrationWithoutIndependence.lean` | All three substantive numbered examples are proved in core, with the PDF's matrix domain/codomain reversal corrected. |
| Chapter 5 | Remark 5.4.6 | FORMALIZED | Matrix monotonicity: inverse is antitone and logarithm monotone on positive definite matrices; scalar monotonicity does not suffice generally. | `HDP.Chapter5.square_not_matrixMonotone_counterexample`<br>`exercise_5_17a_commutingMatrixFunction_monotone`<br>`inverse_loewner_antitone`<br>`logarithm_loewner_monotone` | `HighDimensionalProbability/Chapter5_ConcentrationWithoutIndependence.lean` | The positive results and an explicit `2×2` square-function counterexample are proved. |
| Chapter 5 | Eq. (5.2) | IN-APPENDIX | Spherical isoperimetry implies `sigma(A_t) >= sigma(H_t)` for a half-measure set and hemisphere. | `HDP.Chapter5.spherical_isoperimetric` | `HighDimensionalProbability/Appendix/SphericalIsoperimetric.lean` | Valid specialization of an authoritative external theorem isolated in the appendix; it is not claimed as an unconditional core proof. |
| Chapter 5 | Eq. (5.3) | FORMALIZED | The hemisphere neighborhood contains the cap `{x_1 <= t/sqrt 2}`. | `HDP.Chapter5.sphericalCapBand_subset_neighborhood` | `HighDimensionalProbability/Prelude/SphericalCapGeometry.lean` | Exact full-dimensional containment, including the degenerate polar projection case. |
| Chapter 5 | pp.145--146, sphere proof | FORMALIZED | A real random variable has a median satisfying both half-probability inequalities. | `HDP.Chapter5.exists_measureMedian`; `exists_isMedian` | `HighDimensionalProbability/Chapter5_ConcentrationWithoutIndependence.lean` | Exact lower-quantile construction for probability measures and pushforward wrapper for arbitrary a.e.-measurable real random variables, including atomic laws. |
| Chapter 5 | p.163 before Golden--Thompson | FORMALIZED | In general `exp(X+Y) != exp(X)exp(Y)` for noncommuting symmetric matrices. | `HDP.Chapter5.matrixExponential_add_ne_mul_counterexample` | `HighDimensionalProbability/Chapter5_ConcentrationWithoutIndependence.lean` | Explicit symmetric `2×2` witness with fully computed exponentials. |
| Chapter 6 | Remark 6.5.2 | REJECTED | Matrix completion extends to rectangular/noisy data and can be improved to remove the log or achieve exact noiseless recovery. | `HDP.Chapter6.exercise_6_31_rectangular_matrix_completion`; `exercise_6_32_noisy_matrix_completion` (chosen exercise variants) | `HighDimensionalProbability/Chapter6_QuadraticFormsSymmetrizationContraction.lean` | Qualitative research directions with no uniquely specified hypotheses, rate, normalization, or target theorem. |
| Chapter 6 | Remark 6.5.2 qualitative tail | REJECTED | The logarithmic factor can be removed and noiseless observations can achieve exactly zero error. | — | — | Duplicate audit row for the same hypothesis-free qualitative improvement prose. |
| Chapter 6 | Exercise 6.31 | REJECTED | A rectangular extension of matrix completion. | `HDP.Chapter6.exercise_6_31_rectangular_matrix_completion` (one chosen version) | `HighDimensionalProbability/Chapter6_QuadraticFormsSymmetrizationContraction.lean` | Non-load-bearing “state and prove a version” prompt with no unique source target. |
| Chapter 6 | Exercise 6.32 | REJECTED | A noisy-observation extension of matrix completion. | `HDP.Chapter6.exercise_6_32_noisy_matrix_completion` (one chosen version) | `HighDimensionalProbability/Chapter6_QuadraticFormsSymmetrizationContraction.lean` | Non-load-bearing “extend” prompt without a specified noise model, rate, or normalization. |
| Chapter 7 | Example 7.1.2 | REJECTED | A process indexed by `{1,...,n}` is the same data as a random vector. | `HDP.RandomProcess` | `HighDimensionalProbability/Prelude/RandomProcess.lean` | Terminological identification of equivalent data, not a separate theorem. |
| Chapter 7 | Example 7.1.3 | REJECTED | A random walk is the partial-sum process of independent mean-zero increments. | `HDP.RandomProcess` | `HighDimensionalProbability/Prelude/RandomProcess.lean` | Explanatory construction, with no separate asserted estimate. |
| Chapter 7 | Example 7.1.4 | REJECTED | Standard Brownian motion has continuous paths and independent Gaussian increments. | `HDP.RandomProcess` | `HighDimensionalProbability/Prelude/RandomProcess.lean` | Explanatory model description rather than a standalone conclusion in the chapter's theorem dependency chain. |
| Chapter 7 | Example 7.1.5 | REJECTED | A process indexed by a subset of Euclidean space is a random field. | `HDP.RandomProcess` | `HighDimensionalProbability/Prelude/RandomProcess.lean` | Terminological example, not a mathematical proposition. |
| Chapter 7 | Example 7.1.6 | FORMALIZED | Brownian-motion and unit-variance random-walk increments have square-root distance. | `HDP.Chapter7.brownian_processIncrement`; `randomWalk_processIncrement` | `HighDimensionalProbability/Chapter7_RandomProcesses.lean` | Exact Brownian and independent centered unit-variance random-walk increment identities. |
| Chapter 7 | Theorem 7.1.11 | FORMALIZED | The centered maximum of a finite Gaussian process has `psi2` norm bounded by a universal constant times the largest marginal standard deviation. | `HDP.Chapter7.finiteGaussianProcess_concentration`; `finiteGaussianProcess_affine_representation` | `HighDimensionalProbability/Chapter7_RandomProcesses.lean` | The arbitrary finite process is represented affinely in law, with coefficient norms identified with marginal standard deviations; both sub-Gaussianity and the `psi2` bound are transported to the original probability space. |
| Chapter 7 | Proposition 7.5.2 | FORMALIZED | Gaussian width is finite for bounded sets and obeys scaling, Minkowski, convex-hull, symmetry, diameter, and linear-image laws. | `HDP.Chapter8.euclideanSetGaussianWidthENN_eq_top_iff_not_isBounded`; `euclideanSetGaussianWidthENN_translate`; `euclideanSetGaussianWidthENN_orthogonalImage`; `euclideanSetGaussianWidthENN_convexHull`; `euclideanSetGaussianWidthENN_minkowskiSum`; `euclideanSetGaussianWidthENN_scale`; `euclideanSetGaussianWidthENN_eq_half_difference`; `euclideanSetGaussianWidthENN_diameter_bounds`; `euclideanSetGaussianWidthENN_continuousLinearImage` | `HighDimensionalProbability/Chapter8_Chaining.lean` | Complete actual-set extended-valued interface with bounded safe-real wrappers; all 24 public endpoints depend only on the three standard Lean axioms. |
| Chapter 7 | Example 7.5.8 | FORMALIZED | The cross-polytope has Gaussian width of order `sqrt(log n)`. | `HDP.Chapter7.crossPolytopeGaussianWidth_twoSided` | `HighDimensionalProbability/Chapter7_RandomProcesses.lean` | Direct finite two-sided comparison for every dimension `n ≥ 2`. |
| Chapter 7 | Remark 7.5.10 | REJECTED | In high dimensions a set can have huge diameter but small width, and width can behave unexpectedly across examples. | preceding width/diameter examples | `HighDimensionalProbability/Chapter7_RandomProcesses.lean` | Qualitative synthesis of the preceding examples, with no single quantified comparison to formalize. |
| Chapter 7 | Eq. (7.19) | FORMALIZED | Cross-polytope width is comparable to `sqrt(log n)`. | `HDP.Chapter7.crossPolytopeGaussianWidth_twoSided`; `crossPolytopeGaussianWidth_asymptotic_actual` | `HighDimensionalProbability/Chapter7_RandomProcesses.lean` | Exact canonical finite comparison and sharp asymptotic on the corrected range `n ≥ 2`. |
| Chapter 7 | Eq. (7.21) | FORMALIZED | Projecting the Euclidean ball to a nonzero subspace does not shrink its diameter. | `HDP.Chapter7.orthogonalProjection_unitBall_diam` | `HighDimensionalProbability/Chapter7_RandomProcesses.lean` | The image is exactly the subspace unit ball and has diameter two. |
| Chapter 7 | Sec. 7.2.1 Brownian reflection example | IN-APPENDIX | `E sup_{t<=t0} B_t = sqrt(2t0/pi)`. | — | — | The source invokes the external reflection principle and assigns its proof to non-load-bearing Exercise 7.2; this unused result is deferred to the off-limits appendix. |
| Chapter 8 | Example 8.1.2 | FORMALIZED | Every Gaussian process is subgaussian for its canonical `L2` pseudometric; any process is trivially so for its `psi2` increment metric. | `HDP.gaussianProcess_hasSubGaussianIncrementsWith`; `HDP.gaussianProcess_hasSubGaussianIncrements`; `HDP.hasSubGaussianIncrementsWith_psi2Metric`; `HDP.hasSubGaussianIncrements_psi2Metric` | `HighDimensionalProbability/Chapter8_Chaining.lean` | The arbitrary, possibly noncentered Gaussian process receives an explicit universal increment constant; the tautological `psi2`-metric half is also exposed. |
| Chapter 8 | Remark 8.2.4 | FORMALIZED | One sample realizes the uniform Lipschitz error bound simultaneously for every function. | `HDP.Chapter8.remark_8_2_4_exists_good_lipschitz_sample` | `HighDimensionalProbability/Chapter8_Chaining.lean` | The arbitrary full Lipschitz class follows from the measurable expected-supremum bound by a Markov existence argument; the earlier finite-grid endpoint remains available. |
| Chapter 8 | Sec. 8.1 after Example 8.1.2 | FORMALIZED | Any process becomes subgaussian-increment if distance is defined by its increment `psi2` norm. | `HDP.hasSubGaussianIncrementsWith_psi2Metric`; `HDP.hasSubGaussianIncrements_psi2Metric` | `HighDimensionalProbability/Chapter8_Chaining.lean` | Exact constant-one and existential tautological wrappers. |
| Chapter 9 | Remark 9.6.5 | REJECTED | Extending the general matrix-deviation theorem to subgaussian matrices is open. | — | — | The PDF explicitly identifies an open problem; documenting it is faithful, while asserting a theorem or axiom would not be. |
| Chapter 9 | Sec. 9.2.3, proof of Theorem 9.2.2 | FORMALIZED | For the covariance ellipsoid, radius is the square root of operator norm and Gaussian complexity is at most the square root of trace. | `HDP.Chapter9.covarianceEllipsoid_radius`; `covarianceEllipsoid_gaussianComplexityEnvelope_le` | `HighDimensionalProbability/Chapter9_DeviationsOfRandomMatricesOnSets.lean` | The radius is exact, and the Gaussian-complexity statement uses the authoritative arbitrary-set finite-subfamily envelope, bounded by `‖B‖_F = √tr(BᵀB)`. |

## Appendix-owned coverage: not a core proof claim

The following table preserves all **67 original appendix rows** from the frozen
census. Together with the 3 newly deferred rows listed above, the final
appendix-owned/deferred count is **70**. These rows may name checked core
wrappers, but those wrappers can be conditional on an appendix-owned principle.
Nothing in this section asserts that an `EXTERNAL-SORRY`, custom assumption, or
its transitive dependents are kernel-proved.

In particular, the Chapter 9 rows depending on 
`HDP.Chapter8.majorizingMeasureLowerPrinciple_external` remain `in appendix`; a 
proved conditional wrapper is not an unconditional proof of the advertised theorem.

| Chapter | Book ref | Result | Appendix/conditional evidence | File evidence | Why it is not marked proved |
|---|---|---|---|---|---|
| Chapter 1 | Theorem 1.7.6 | Poisson limit theorem for rare Bernoulli triangular arrays. | `HDP.Chapter1.poisson_limit_theorem` | `HighDimensionalProbability/Appendix/PoissonLimitTheorem.lean` | Exact external theorem; intentionally isolated, and no core theorem depends on the placeholder. |
| Chapter 2 | Theorem 2.1.4 | Berry--Esseen quantitative CLT. | `HDP.Chapter2.berryEsseen` | `HighDimensionalProbability/Appendix/BerryEsseen.lean` | Exact externally cited theorem, isolated and not imported into core. |
| Chapter 5 | Theorem 5.1.4 | Euclidean balls minimize boundary area and every epsilon-neighborhood volume at fixed volume. | `HDP.Chapter5.euclidean_isoperimetric` | `HighDimensionalProbability/Appendix/EuclideanIsoperimetric.lean` | Appendix states the measurable outer-neighborhood comparison. The separate minimal-boundary-area clause is not represented directly; the PDF itself says it follows by a limit. |
| Chapter 5 | Theorem 5.1.5 | Spherical caps minimize epsilon-neighborhood area at fixed spherical area. | `HDP.Chapter5.spherical_isoperimetric` | `HighDimensionalProbability/Appendix/SphericalIsoperimetric.lean` | Corrected measurable chordal-neighborhood form; isolated `EXTERNAL-SORRY`. |
| Chapter 5 | Theorem 5.2.2 | Half-spaces minimize Gaussian epsilon-neighborhood measure at fixed Gaussian measure. | `HDP.Chapter5.gaussian_isoperimetric` | `HighDimensionalProbability/Appendix/GaussianIsoperimetric.lean` | Corrected Borel/measurable-set statement; isolated `EXTERNAL-SORRY`. |
| Chapter 5 | Theorem 5.2.5 | Lipschitz functions on the normalized Hamming cube concentrate at scale `1/sqrt n`. | `HDP.Chapter5.hamming_cube_concentration` | `HighDimensionalProbability/Appendix/HammingCubeConcentration.lean` | Corrected `n>0` and normalized-distance statement; isolated `EXTERNAL-SORRY`. |
| Chapter 5 | Theorem 5.2.6 | Lipschitz functions on a uniform random permutation concentrate at scale `1/sqrt n`. | `HDP.Chapter5.symmetric_group_concentration` | `HighDimensionalProbability/Appendix/SymmetricGroupConcentration.lean` | Corrected `n>0`; isolated `EXTERNAL-SORRY`. |
| Chapter 5 | Theorem 5.2.7 | Positive-Ricci concentration, specialized to Haar measure on `SO(n)`. | `HDP.Chapter5.positive_ricci_concentration`<br>`HDP.Chapter5.special_orthogonal_concentration` | `HighDimensionalProbability/Appendix/PositiveRicciConcentration.lean`<br>`HighDimensionalProbability/Appendix/SpecialOrthogonalConcentration.lean` | PDF omits Lipschitz/measurability and infimizes Ricci over unnormalized vectors; appendix uses a normalized Ricci lower bound. Equation (5.8) is a separate row below. |
| Chapter 5 | Theorem 5.2.9 | Lipschitz functions on a random Grassmannian subspace concentrate at scale `1/sqrt n`. | `HDP.Chapter5.Grassmannian`<br>`grassmannHaarMeasure`<br>`grassmannDistance`<br>`HDP.Chapter5.grassmannian_concentration` | `HighDimensionalProbability/Chapter5_ConcentrationWithoutIndependence.lean`<br>`HighDimensionalProbability/Appendix/GrassmannianConcentration.lean` | PDF quotient/stabilizer and `G_{n,1}=S^{n-1}` claims are inaccurate and its Lipschitz hypothesis is omitted; Lean uses the projection orbit model. |
| Chapter 5 | Theorem 5.2.11 | Strongly convex exponential densities yield dimension-free concentration. | `HDP.Chapter5.strongly_convex_density_concentration` | `HighDimensionalProbability/Appendix/StronglyConvexDensity.lean` | Appendix separates potential/observable, normalizes the density, and restores the Gaussian potential `‖x‖^2/2+c`; isolated `EXTERNAL-SORRY`. |
| Chapter 5 | Theorem 5.2.12 | Talagrand convex concentration for product measures with bounded independent coordinates. | `HDP.Chapter5.talagrand_convex_concentration` | `HighDimensionalProbability/Appendix/TalagrandConvexConcentration.lean` | Product law, coordinate supports, convexity, measurability, and Lipschitzness are explicit; isolated `EXTERNAL-SORRY`. |
| Chapter 5 | Theorem 5.7.1 | McDiarmid/bounded differences inequality for independent coordinates. | `HDP.Chapter5.bounded_differences` | `HighDimensionalProbability/Appendix/BoundedDifferences.lean` | PDF inconsistently uses `N` and `n` and gives the wrong abstract domain; appendix uses a genuine dependent product over `Fin N`; isolated `EXTERNAL-SORRY`. |
| Chapter 5 | Eq. (5.7) | Hamming-cube concentration inequality. | `HDP.Chapter5.hamming_cube_concentration` | `HighDimensionalProbability/Appendix/HammingCubeConcentration.lean` | Corrected `n>0`; isolated `EXTERNAL-SORRY`. |
| Chapter 5 | Eq. (5.8) | Positive-Ricci manifolds have Gaussian concentration at scale `1/sqrt kappa`. | `HDP.Chapter5.positive_ricci_concentration` | `HighDimensionalProbability/Appendix/PositiveRicciConcentration.lean` | PDF's Ricci infimum is ill-normalized; appendix states `Ric(v,v)>=kappa‖v‖^2`. |
| Chapter 8 | Theorem 8.5.5 | Gaussian expected suprema are equivalent, up to universal constants, to `gamma2`. | core upper `HDP.Chapter8.genericChainingBound`; conditional lower `majorizingMeasure_lower`; witness `HDP.Chapter8.majorizingMeasureLowerPrinciple_external` | `HighDimensionalProbability/Chapter8_Chaining.lean`; `HighDimensionalProbability/Chapter8_Chaining.lean`; `HighDimensionalProbability/Appendix/MajorizingMeasureLower.lean` | The difficult lower bound is explicitly omitted by the book and isolated as an external Appendix principle. |
| Chapter 8 | Corollary 8.5.6 | Talagrand comparison: a subgaussian process is controlled by a Gaussian process with dominating canonical increments. | `HDP.Chapter8.talagrandComparison`; `HDP.Chapter8.majorizingMeasureLowerPrinciple_external` | `HighDimensionalProbability/Chapter8_Chaining.lean`; `HighDimensionalProbability/Appendix/MajorizingMeasureLower.lean` | Core theorem visibly requires `[MajorizingMeasureLowerPrinciple]`; no hidden root instance. |
| Chapter 8 | Corollary 8.5.8 | Geometric Talagrand comparison bounds a subgaussian process by Gaussian width. | `HDP.Chapter8.corollary_8_5_8_geometric`; `HDP.Chapter8.majorizingMeasureLowerPrinciple_external` | `HighDimensionalProbability/Chapter8_Chaining.lean`; `HighDimensionalProbability/Appendix/MajorizingMeasureLower.lean` | Explicit external lower-majorizing-measure dependency. |
| Chapter 8 | Remark 8.5.9 | Subgaussian width is at most a universal multiple of Gaussian width. | `HDP.Chapter8.remark_8_5_9_subgaussian_width`; `HDP.Chapter8.majorizingMeasureLowerPrinciple_external` | `HighDimensionalProbability/Chapter8_Chaining.lean`; `HighDimensionalProbability/Appendix/MajorizingMeasureLower.lean` | Explicit principle parameter. |
| Chapter 8 | Theorem 8.6.1 | Subgaussian Chevet bounds a bilinear supremum by opposite radius-width products. | `HDP.Chapter8.theorem_8_6_1_subgaussian_chevet_arbitrary_bounded_real`; `HDP.Chapter8.majorizingMeasureLowerPrinciple_external` | `HighDimensionalProbability/Chapter8_Chaining.lean`; `HighDimensionalProbability/Appendix/MajorizingMeasureLower.lean` | Core theorem is checked conditional on `[MajorizingMeasureLowerPrinciple]`. |
| Chapter 8 | Remark 8.6.2 | The Chevet bound specializes to an expected operator-norm estimate. | `HDP.Chapter8.remark_8_6_2_finite_unit_sphere_bound`; `HDP.Chapter8.majorizingMeasureLowerPrinciple_external` | `HighDimensionalProbability/Chapter8_Chaining.lean`; `HighDimensionalProbability/Appendix/MajorizingMeasureLower.lean` | Same explicit lower-principle dependency. |
| Chapter 8 | Remark 8.6.3 | For Gaussian matrices, the Chevet control is two-sided with the sharp constant-one upper comparison. | `HDP.Chapter8.remark_8_6_3_gaussian_chevet_arbitrary`; witness `HDP.Chapter8.gaussianChevetUpperPrinciple_external` | `HighDimensionalProbability/Chapter8_Chaining.lean`; `HighDimensionalProbability/Appendix/GaussianChevet.lean` | The PDF hint's fixed-radius comparison is false in general; sharp arbitrary-set upper principle is isolated in Appendix. Reverse inequality is proved unconditionally. |
| Chapter 8 | Exercise 8.37 | Expectation, high-probability, and moment consequences of Talagrand comparison. | `HDP.Chapter8.exercise_8_37a_expectation`; `exercise_8_37b_highProbability`; `exercise_8_37c_moments`; `HDP.Chapter8.majorizingMeasureLowerPrinciple_external` | `HighDimensionalProbability/Chapter8_Chaining.lean`; `HighDimensionalProbability/Appendix/MajorizingMeasureLower.lean` | Checked conditional wrappers; external lower-majorizing-measure existence is isolated. |
| Chapter 8 | Exercise 8.39(a--b) | Sharp Gaussian Chevet upper and reverse inequalities. | `HDP.Chapter8.exercise_8_39a_gaussian_chevet_arbitrary`; `exercise_8_39b_gaussian_chevet_reverse_arbitrary`; `HDP.Chapter8.gaussianChevetUpperPrinciple_external` | `HighDimensionalProbability/Chapter8_Chaining.lean`; `HighDimensionalProbability/Appendix/GaussianChevet.lean` | Reverse half is core-proved; arbitrary sharp upper half uses isolated `GaussianChevetUpperPrinciple`. |
| Chapter 8 | Sec. 8.5.3 after Theorem 8.5.5 | The lower majorizing-measure bound is not proved in the book. | `HDP.Chapter8.majorizingMeasureLowerPrinciple_external` | `HighDimensionalProbability/Appendix/MajorizingMeasureLower.lean` | Correctly isolated, never hidden in core. |
| Chapter 9 | Theorem 9.1.1 | Matrix deviations on a set are controlled in expectation by its Gaussian complexity. | `HDP.Chapter9.theorem_9_1_1_matrixDeviation`; arbitrary-set `theorem_9_1_1_matrixDeviation_envelope`; `HDP.Chapter8.majorizingMeasureLowerPrinciple_external` | `HighDimensionalProbability/Chapter9_DeviationsOfRandomMatricesOnSets.lean`; `HighDimensionalProbability/Appendix/MajorizingMeasureLower.lean` | The core wrappers are conditional on `MajorizingMeasureLowerPrinciple`; its only witness is external. The real theorem is finite and the `ENNReal` envelope safely represents the PDF's arbitrary-set convention. |
| Chapter 9 | Remark 9.1.3 | Centering converts the matrix-deviation theorem into deviation around `E ‖Ax‖`. | `HDP.Chapter9.exercise_9_2_centeredMatrixDeviation_envelope`; `HDP.Chapter8.majorizingMeasureLowerPrinciple_external` | `HighDimensionalProbability/Chapter9_DeviationsOfRandomMatricesOnSets.lean`; `HighDimensionalProbability/Appendix/MajorizingMeasureLower.lean` | Promoted Exercise 9.2 is a proved conditional wrapper; the unconditional advertised result needs the external lower principle. |
| Chapter 9 | Remark 9.1.4 | Matrix deviations obey the corresponding high-probability bound. | `HDP.Chapter9.remark_9_1_4_matrixDeviation_highProbability_set`; `HDP.Chapter8.majorizingMeasureLowerPrinciple_external` | `HighDimensionalProbability/Chapter9_DeviationsOfRandomMatricesOnSets.lean`; `HighDimensionalProbability/Appendix/MajorizingMeasureLower.lean` | The actual-set event is rigorous, but its bound is conditional on the external lower principle. |
| Chapter 9 | Remark 9.1.5 | Deviations of squared norms follow from deviations of norms. | `HDP.Chapter9.exercise_9_3_quadraticMatrixDeviation_envelope`; `HDP.Chapter8.majorizingMeasureLowerPrinciple_external` | `HighDimensionalProbability/Chapter9_DeviationsOfRandomMatricesOnSets.lean`; `HighDimensionalProbability/Appendix/MajorizingMeasureLower.lean` | Promoted Exercise 9.3 is proved conditionally; the unconditional theorem inherits Theorem 9.1.1's external dependency. |
| Chapter 9 | Proposition 9.2.1 | A subgaussian projection approximately preserves all pairwise distances in a bounded set, with width-dependent additive error. | `HDP.Chapter9.theorem_9_2_1_randomProjectionSizes`; `HDP.Chapter8.majorizingMeasureLowerPrinciple_external` | `HighDimensionalProbability/Chapter9_DeviationsOfRandomMatricesOnSets.lean`; `HighDimensionalProbability/Appendix/MajorizingMeasureLower.lean` | Canonical endpoint has the printed bounded-set scope but depends on the external lower principle. |
| Chapter 9 | Theorem 9.2.2 | Empirical covariance has an effective-rank operator-norm error bound. | `HDP.Chapter9.theorem_9_2_2_lowRankCovariance_direct`; `HDP.Chapter8.majorizingMeasureLowerPrinciple_external` | `HighDimensionalProbability/Chapter9_DeviationsOfRandomMatricesOnSets.lean`; `HighDimensionalProbability/Appendix/MajorizingMeasureLower.lean` | Conditional wrapper. Lean correctly calls the uncentered matrix a second moment and handles singular covariance without invalid whitening. |
| Chapter 9 | Remark 9.2.3 | The covariance-estimation error has a high-probability version. | `HDP.Chapter9.exercise_9_9_lowRankCovariance_highProbability_direct`; `HDP.Chapter8.majorizingMeasureLowerPrinciple_external` | `HighDimensionalProbability/Chapter9_DeviationsOfRandomMatricesOnSets.lean`; `HighDimensionalProbability/Appendix/MajorizingMeasureLower.lean` | Promoted Exercise 9.9 is proved conditionally on the external lower principle. |
| Chapter 9 | Lemma 9.2.4 | Additive Johnson--Lindenstrauss embeds any bounded set with an error governed by Gaussian complexity. | `HDP.Chapter9.theorem_9_2_4_additiveJohnsonLindenstrauss`; `HDP.Chapter8.majorizingMeasureLowerPrinciple_external` | `HighDimensionalProbability/Chapter9_DeviationsOfRandomMatricesOnSets.lean`; `HighDimensionalProbability/Appendix/MajorizingMeasureLower.lean` | Actual-set conditional wrapper; it also corrects the printed difference-set typo `X-Y` to `X-X`. |
| Chapter 9 | Remark 9.2.5 | The additive JL error is small once the target dimension dominates effective dimension. | `HDP.Chapter9.remark_9_2_5_setAdditiveJLError_le`; `remark_9_2_5_effectiveDimension_set`; external lower-principle witness | `HighDimensionalProbability/Chapter9_DeviationsOfRandomMatricesOnSets.lean`; `HighDimensionalProbability/Appendix/MajorizingMeasureLower.lean` | The numerical conclusion is packaged through the same external-principle constant; PDF's `T`/`X` inconsistency is corrected. |
| Chapter 9 | Theorem 9.3.1 | The expected diameter of a random kernel section is bounded by width divided by `sqrt m`. | `HDP.Chapter9.theorem_9_3_1_mStar_set`; `HDP.Chapter8.majorizingMeasureLowerPrinciple_external` | `HighDimensionalProbability/Chapter9_DeviationsOfRandomMatricesOnSets.lean`; `HighDimensionalProbability/Appendix/MajorizingMeasureLower.lean` | Actual-set conditional wrapper; no attainment or finite-fiber assumption is hidden. |
| Chapter 9 | Example 9.3.2 | A random high-dimensional section of the cross-polytope has diameter `O(sqrt(log n/n))`. | `HDP.Chapter9.example_9_3_2_crossPolytopeBody_mStar`; external lower-principle witness | `HighDimensionalProbability/Chapter9_DeviationsOfRandomMatricesOnSets.lean`; `HighDimensionalProbability/Appendix/MajorizingMeasureLower.lean` | Conditional consequence. PDF's unrelated `T` in (9.13) is corrected to the cross-polytope body. |
| Chapter 9 | Remark 9.3.3 | The M-star bound is nontrivial once codimension dominates effective dimension. | `HDP.Chapter9.remark_9_3_3_effectiveDimension_set`; external lower-principle witness | `HighDimensionalProbability/Chapter9_DeviationsOfRandomMatricesOnSets.lean`; `HighDimensionalProbability/Appendix/MajorizingMeasureLower.lean` | Actual-set conditional endpoint. |
| Chapter 9 | Theorem 9.3.4 | A random kernel avoids a spherical set once `m` dominates its squared width. | `HDP.Chapter9.theorem_9_3_4_escape`; `HDP.Chapter8.majorizingMeasureLowerPrinciple_external` | `HighDimensionalProbability/Chapter9_DeviationsOfRandomMatricesOnSets.lean`; `HighDimensionalProbability/Appendix/MajorizingMeasureLower.lean` | Arbitrary spherical-set scope, but the unconditional bound inherits the external lower principle. |
| Chapter 9 | Theorem 9.4.4 | Constrained recovery over a bounded prior has expected error `O(K^2 w(T)/sqrt m)`. | `HDP.Chapter9.theorem_9_4_4_constrainedRecovery`; external lower-principle witness | `HighDimensionalProbability/Chapter9_DeviationsOfRandomMatricesOnSets.lean`; `HighDimensionalProbability/Appendix/MajorizingMeasureLower.lean` | Uses the actual uncountable prior and rigorous selectors, but is conditional on the external lower principle. |
| Chapter 9 | Remark 9.4.5 | Constrained recovery becomes accurate above the prior's effective dimension. | `HDP.Chapter9.remark_9_4_5_effectiveDimension`; external lower-principle witness | `HighDimensionalProbability/Chapter9_DeviationsOfRandomMatricesOnSets.lean`; `HighDimensionalProbability/Appendix/MajorizingMeasureLower.lean` | Conditional consequence, with safe zero-diameter handling. |
| Chapter 9 | Remark 9.4.6 | Convexifying the prior does not change Gaussian width or the recovery guarantee. | `HDP.Chapter9.remark_9_4_6_convexRelaxation`; external lower-principle witness | `HighDimensionalProbability/Chapter9_DeviationsOfRandomMatricesOnSets.lean`; `HighDimensionalProbability/Appendix/MajorizingMeasureLower.lean` | Convexification identity is core, but the advertised recovery guarantee remains conditional. |
| Chapter 9 | Remark 9.4.7 | Penalized unconstrained optimization gives a robust alternative to exact feasibility. | `HDP.Chapter9.remark_9_4_7_unconstrainedOptimization`; `exercise_9_20`; external lower-principle witness | `HighDimensionalProbability/Chapter9_DeviationsOfRandomMatricesOnSets.lean`; `HighDimensionalProbability/Appendix/MajorizingMeasureLower.lean` | Corrected tuning/zero branches are proved conditionally on the external lower principle. |
| Chapter 9 | Corollary 9.4.8 | Sparse vectors can be recovered from roughly `s log n` subgaussian measurements. | `HDP.Chapter9.theorem_9_4_8_sparseRecovery`; external lower-principle witness | `HighDimensionalProbability/Chapter9_DeviationsOfRandomMatricesOnSets.lean`; `HighDimensionalProbability/Appendix/MajorizingMeasureLower.lean` | Actual `sqrt s` `l1` prior, but the recovery theorem depends on the external lower principle. |
| Chapter 9 | Remark 9.4.10 | Truncating the `l1` ball improves `log n` to `log(en/s)`. | `HDP.Chapter9.remark_9_4_10_logImprovement`; `exercise_9_26`; `exercise_9_26_improvedSparseRecovery`; external lower-principle witness | `HighDimensionalProbability/Chapter9_DeviationsOfRandomMatricesOnSets.lean`; `HighDimensionalProbability/Appendix/MajorizingMeasureLower.lean` | Convexification and width are core; the advertised improved recovery conclusion is conditional. |
| Chapter 9 | Corollary 9.4.11 | Low-rank matrices can be recovered from roughly `rd` Gaussian measurements via nuclear norm. | `HDP.Chapter9.theorem_9_4_11_lowRankRecovery`; external lower-principle witness | `HighDimensionalProbability/Chapter9_DeviationsOfRandomMatricesOnSets.lean`; `HighDimensionalProbability/Appendix/MajorizingMeasureLower.lean` | Actual nuclear-norm prior, but conditional on the external lower principle. |
| Chapter 9 | Theorem 9.5.1 | `l1` minimization exactly recovers every sparse vector with high probability. | `HDP.Chapter9.theorem_9_5_1_exactSparseRecovery`; external lower-principle witness | `HighDimensionalProbability/Chapter9_DeviationsOfRandomMatricesOnSets.lean`; `HighDimensionalProbability/Appendix/MajorizingMeasureLower.lean` | Uniform actual descent-set theorem, but its escape input is conditional on the external lower principle. |
| Chapter 9 | Remark 9.5.4 | A sharper width bound improves exact recovery to `s log(en/s)` measurements. | `HDP.Chapter9.remark_9_5_4_improvedExactRecoveryWidth`; `remark_9_5_4_improvedExactRecovery`; external lower-principle witness | `HighDimensionalProbability/Chapter9_DeviationsOfRandomMatricesOnSets.lean`; `HighDimensionalProbability/Appendix/MajorizingMeasureLower.lean` | Width theorem is core; the recovery conclusion over the actual set is conditional. |
| Chapter 9 | Theorem 9.6.3 | A Gaussian matrix obeys a general deviation inequality for sublinear functionals with linear growth. | `HDP.Chapter9.theorem_9_6_3_generalMatrixDeviation`; `theorem_9_6_3_generalMatrixDeviation_envelope`; external lower-principle witness | `HighDimensionalProbability/Chapter9_DeviationsOfRandomMatricesOnSets.lean`; `HighDimensionalProbability/Appendix/MajorizingMeasureLower.lean` | Conditional core wrapper. It correctly replaces the PDF's impossible global boundedness by Euclidean linear growth and fixes the output dimension. |
| Chapter 9 | Theorem 9.7.1 | Two-sided Chevet controls the deviation of support suprema under a Gaussian matrix. | `HDP.Chapter9.theorem_9_7_1_twoSidedChevet_set_ENN`; `theorem_9_7_1_twoSidedChevet_set`; external lower-principle witness | `HighDimensionalProbability/Chapter9_DeviationsOfRandomMatricesOnSets.lean`; `HighDimensionalProbability/Appendix/MajorizingMeasureLower.lean` | Conditional wrapper; it correctly uses `rad(S)` where the PDF explanatory clause says `rad(T)`. |
| Chapter 9 | Theorem 9.7.2 | A Gaussian image of a convex body is sandwiched between nearly concentric Euclidean balls. | `HDP.Chapter9.theorem_9_7_2_dvoretzkyMilman`; `DvoretzkyMilmanSetConclusion`; external lower-principle witness | `HighDimensionalProbability/Chapter9_DeviationsOfRandomMatricesOnSets.lean`; `HighDimensionalProbability/Appendix/MajorizingMeasureLower.lean` | Actual-set/closed-hull conditional theorem; closure safety is explicit. |
| Chapter 9 | Remark 9.7.3 | The Dvoretzky--Milman sandwich is nearly round above effective dimension. | `HDP.Chapter9.remark_9_7_3_effectiveDimension_set`; `remark_9_7_3_effectiveDimension_set_radii`; external lower-principle witness | `HighDimensionalProbability/Chapter9_DeviationsOfRandomMatricesOnSets.lean`; `HighDimensionalProbability/Appendix/MajorizingMeasureLower.lean` | Conditional consequence; comparison ball correctly lies in `R^m`, not the PDF's `R^n`. |
| Chapter 9 | Example 9.7.4 | A random proportional-dimensional image of the cube is almost round. | `HDP.Chapter9.example_9_7_4_cubeNearlyRound_set`; external lower-principle witness | `HighDimensionalProbability/Chapter9_DeviationsOfRandomMatricesOnSets.lean`; `HighDimensionalProbability/Appendix/MajorizingMeasureLower.lean` | Actual cube body and image bridges are core; the almost-round probability conclusion is conditional. |
| Chapter 9 | Eq. (9.11) | Uniform matrix deviations satisfy a width-plus-radius high-probability bound. | `HDP.Chapter9.remark_9_1_4_matrixDeviation_highProbability_set`; external lower-principle witness | `HighDimensionalProbability/Chapter9_DeviationsOfRandomMatricesOnSets.lean`; `HighDimensionalProbability/Appendix/MajorizingMeasureLower.lean` | Actual-set conditional wrapper; only the lower-principle witness is external. |
| Chapter 9 | Eq. (9.13) | Expected cross-polytope section diameter is `O(sqrt(log n/n))`. | `HDP.Chapter9.example_9_3_2_crossPolytopeBody_mStar`; external lower-principle witness | `HighDimensionalProbability/Chapter9_DeviationsOfRandomMatricesOnSets.lean`; `HighDimensionalProbability/Appendix/MajorizingMeasureLower.lean` | Conditional M-star consequence; Lean corrects the display's stray `T`. |
| Chapter 9 | Eq. (9.14) | Escape occurs when `m >= C K^4 w(T)^2`. | hypothesis/conclusion of `HDP.Chapter9.theorem_9_3_4_escape`; external lower-principle witness | `HighDimensionalProbability/Chapter9_DeviationsOfRandomMatricesOnSets.lean`; `HighDimensionalProbability/Appendix/MajorizingMeasureLower.lean` | Conditional on the external lower principle. |
| Chapter 9 | Eq. (9.15) | The unit-sphere matrix-deviation event used in the escape proof. | proof of `HDP.Chapter9.theorem_9_3_4_escape`; `remark_9_1_4_matrixDeviation_highProbability_set`; `HDP.Chapter8.majorizingMeasureLowerPrinciple_external` | `HighDimensionalProbability/Chapter9_DeviationsOfRandomMatricesOnSets.lean`; `HighDimensionalProbability/Chapter9_DeviationsOfRandomMatricesOnSets.lean`; `HighDimensionalProbability/Appendix/MajorizingMeasureLower.lean` | Event logic is core; its quantitative probability bound is conditional. |
| Chapter 9 | Eq. (9.19) | Expected constrained-recovery error is `O(K^2 w(T)/sqrt m)`. | `HDP.Chapter9.theorem_9_4_4_constrainedRecovery`; external lower-principle witness | `HighDimensionalProbability/Chapter9_DeviationsOfRandomMatricesOnSets.lean`; `HighDimensionalProbability/Appendix/MajorizingMeasureLower.lean` | Actual-prior conditional result. |
| Chapter 9 | Eq. (9.45) | Gaussian image is sandwiched between inner and outer Euclidean balls. | `HDP.Chapter9.DvoretzkyMilmanSetConclusion`; `theorem_9_7_2_dvoretzkyMilman`; external lower-principle witness | `HighDimensionalProbability/Chapter9_DeviationsOfRandomMatricesOnSets.lean`; `HighDimensionalProbability/Appendix/MajorizingMeasureLower.lean` | Predicate is core; the `0.99` theorem is conditional. Output balls correctly live in `R^m`. |
| Chapter 9 | Exercise 9.2 | Center matrix deviations around `E ‖Ax‖`. | `HDP.Chapter9.exercise_9_2_centeredMatrixDeviation_envelope`; external lower-principle witness | `HighDimensionalProbability/Chapter9_DeviationsOfRandomMatricesOnSets.lean`; `HighDimensionalProbability/Appendix/MajorizingMeasureLower.lean` | Promoted proof is conditional because Theorem 9.1.1 is. |
| Chapter 9 | Exercise 9.3 | Convert norm deviations into quadratic norm deviations. | `HDP.Chapter9.exercise_9_3_quadraticMatrixDeviation_envelope`; external lower-principle witness | `HighDimensionalProbability/Chapter9_DeviationsOfRandomMatricesOnSets.lean`; `HighDimensionalProbability/Appendix/MajorizingMeasureLower.lean` | Correct arbitrary-set envelope, conditional on the external lower principle. |
| Chapter 9 | Exercise 9.9 | High-probability low-rank covariance estimation. | `HDP.Chapter9.exercise_9_9_lowRankCovariance_highProbability_direct`; external lower-principle witness | `HighDimensionalProbability/Chapter9_DeviationsOfRandomMatricesOnSets.lean`; `HighDimensionalProbability/Appendix/MajorizingMeasureLower.lean` | Direct-row corrected theorem, but externally conditional. |
| Chapter 9 | Exercise 9.12 | M-star bound for every affine kernel section. | `HDP.Chapter9.exercise_9_12_affineMStar_set`; external lower-principle witness | `HighDimensionalProbability/Chapter9_DeviationsOfRandomMatricesOnSets.lean`; `HighDimensionalProbability/Appendix/MajorizingMeasureLower.lean` | Uses an extended supremum over actual fibers, fixing the source's unjustified maximum, but remains conditional. |
| Chapter 9 | Exercise 9.19 | Constrained recovery in the noisy linear model. | `HDP.Chapter9.exercise_9_19`; external lower-principle witness | `HighDimensionalProbability/Chapter9_DeviationsOfRandomMatricesOnSets.lean`; `HighDimensionalProbability/Appendix/MajorizingMeasureLower.lean` | Corrects the PDF's random noise norm left outside expectation and makes integrability explicit. |
| Chapter 9 | Exercise 9.20 | Penalized unconstrained recovery with a rigorously tuned parameter. | `HDP.Chapter9.exercise_9_20`; external lower-principle witness | `HighDimensionalProbability/Chapter9_DeviationsOfRandomMatricesOnSets.lean`; `HighDimensionalProbability/Appendix/MajorizingMeasureLower.lean` | Fixes undefined tuning at `x=0`, attainment, and the meaning of asymptotic comparison. |
| Chapter 9 | Exercise 9.26 | Bound the truncated sparse width and derive the `s log(en/s)` recovery improvement. | `HDP.Chapter9.exercise_9_26`; `exercise_9_26_sparse_width`; `exercise_9_26_improvedSparseRecovery`; external lower-principle witness | `HighDimensionalProbability/Chapter9_DeviationsOfRandomMatricesOnSets.lean`; `HighDimensionalProbability/Appendix/MajorizingMeasureLower.lean` | Width/convexification half is core; advertised recovery half is conditional. |
| Chapter 9 | Exercise 9.37 | General-norm Johnson--Lindenstrauss from general matrix deviation. | `HDP.Chapter9.exercise_9_37_generalNormJL`; external lower-principle witness | `HighDimensionalProbability/Chapter9_DeviationsOfRandomMatricesOnSets.lean`; `HighDimensionalProbability/Appendix/MajorizingMeasureLower.lean` | Precise quantitative theorem, conditional with Theorem 9.6.3. |
| Chapter 9 | Sec. 9.7 opening | General-norm JL follows from the general matrix-deviation theorem. | `HDP.Chapter9.exercise_9_37_generalNormJL`; external lower-principle witness | `HighDimensionalProbability/Chapter9_DeviationsOfRandomMatricesOnSets.lean`; `HighDimensionalProbability/Appendix/MajorizingMeasureLower.lean` | PDF cites Theorem 9.1.1 here, but the intended source is Theorem 9.6.3; Lean fixes the citation and exposes its external dependency. |
| Chapter 9 | After Theorem 9.7.1 | The two-sided Chevet deviation bound implies the ordinary one-sided Chevet inequality by triangle inequality. | `HDP.Chapter9.theorem_9_7_1_twoSidedChevet_set` | `HighDimensionalProbability/Chapter9_DeviationsOfRandomMatricesOnSets.lean`; `HighDimensionalProbability/Appendix/MajorizingMeasureLower.lean` | Logical consequence of the conditional two-sided theorem; no separate redundant wrapper is needed. |

## Row-level faithfulness, source, and citation notes on frozen proved/stronger rows

The following exhaustive table retains every one of the **717 frozen
proved/stronger rows** without deletion. It also contains 7 consolidated
post-correction entries (six Appetizer entries and Proposition 7.5.2), for 724
displayed rows in this section. The remaining newly formalized gap rows are
documented in the 89-row disposition table rather than duplicated here.
Exact/faithful rows remain visible so no source repair, strengthened form, extra
hypothesis, boundary convention, dimension/range correction, or citation nuance
is lost to a heuristic filter. These notes do not downgrade a row.

| Chapter | Book ref | Audit class | Result | Faithfulness / source / citation note |
|---|---|---|---|---|
| Appetizer | (0.1), convex-hull definition | STRONGER | A point of `conv(T)` is a finite convex combination of points of `T`. | Mathlib works over real ordered fields and gives a positive, affinely independent representation; no Chapter-0 wrapper exists. |
| Appetizer | Theorem 0.0.1 | STRONGER | Caratheodory: in `R^n`, at most `n+1` points suffice in a convex combination. | The result is split into a more general affine-independent representation and the dimension/cardinality theorem; there is no single source-facing `n+1` wrapper. |
| Appetizer | Theorem 0.0.2 | FORMALIZED | Equal averages of `k` points approximate every point of a convex hull within `1/√k`. | Exact Hilbert-space empirical-method statement, including the load-bearing second-moment identities. |
| Appetizer | Corollary 0.0.3 | FORMALIZED | An `N`-vertex polytope in the unit ball has an internal `N^k`-point cover of radius `1/√k`. | Exact finite center set and cardinality bound. |
| Appetizer | Theorem 0.0.4; (0.2) | FORMALIZED | The relative volume of an `N`-vertex polytope is at most `(3√(log N/n))^n`. | The integer ceiling optimization and every degenerate/large-`N` branch are explicit. |
| Appetizer | (0.3)–(0.4) | FORMALIZED | The pre-optimization volume coefficient is `N^k/k^(n/2)` and the continuous critical point is `n/(2 log N)`. | The volume inequality is stated safely in ENNReal multiplication form; the critical point and uniqueness are proved over the positive domain. |
| Appetizer | Remark 0.0.5 | FORMALIZED | Subexponential vertex growth forces the comparison radius and relative-volume coefficient to vanish. | “Subexponential” is made precise as `log(N n)/n→0`; both limits are proved. |
| Appetizer | Exercises 0.1(a), 0.2, 0.3 | FORMALIZED | Vector bias–variance, mean minimization, and the independent centered-vector Pythagorean identity. | These are the load-bearing exercise inputs explicitly consumed by the Appetizer proof. |
| Chapter 1 | Convex-set definition | FORMALIZED | A set contains every segment joining two of its points. | Faithful, generalized to real modules. |
| Chapter 1 | (1.1), convex/concave functions | FORMALIZED | Convex functions lie below secants; `f` is concave iff `-f` is convex. | Exact. |
| Chapter 1 | Maximum principle; norm convexity | STRONGER | A convex function on a convex hull is bounded by generator values; norms and norm balls are convex. | Lean includes safe arbitrary-set and finite-attainment forms. |
| Chapter 1 | `ell^p` definitions | FORMALIZED | Coordinate `ell^p`/`ell^infty` norms and Minkowski's inequality. | Finite `p` formulas state the necessary positivity/range hypotheses. |
| Chapter 1 | (1.2) | FORMALIZED | Euclidean norm squared is the dot product with itself. | Exact finite-coordinate identities. |
| Chapter 1 | (1.3) | FORMALIZED | The `ell^infty` unit ball is the cube and the `ell^1` ball is the cross-polytope. | Cross-polytope wrapper makes the nonempty-coordinate requirement explicit. |
| Chapter 1 | (1.4) | FORMALIZED | `ell^p` norms decrease as `p` increases. | Includes finite and `q=infinity` endpoints. |
| Chapter 1 | (1.5) | FORMALIZED | Holder (including Cauchy--Schwarz and endpoint conjugates). | Exact and endpoint-complete. |
| Chapter 1 | (1.6) | FORMALIZED | Duality: `‖x‖_p` is the maximum/supremum of pairings over the dual unit ball. | Uses `IsGreatest` so the maximum claim is safe. |
| Chapter 1 | (1.7) | FORMALIZED | Expectation and variance notation. | Direct Mathlib representation. |
| Chapter 1 | Expectation linearity | STRONGER | Finite sums have additive expectation without independence. | General finite family with explicit integrability. |
| Chapter 1 | (1.8) | STRONGER | Variance of a weighted sum of independent/uncorrelated variables. | Includes the genuinely uncorrelated form. |
| Chapter 1 | (1.9) | FORMALIZED | The expectation of an event indicator is its probability. | Measurability is explicit. |
| Chapter 1 | MGF and moments | FORMALIZED | The moment-generating function is `E exp(lambda X)`. | Definition is exact; the prose derivative interpretation is not packaged separately. |
| Chapter 1 | (1.10) | FORMALIZED | Random-variable `L^p` and essential-supremum norms. | `eLpNorm` is authoritative; a real conversion needs `MemLp`. |
| Chapter 1 | (1.11) | FORMALIZED | `L^2` inner product is `E[XY]`. | Exact under `MemLp 2`. |
| Chapter 1 | (1.12) | FORMALIZED | Standard deviation equals the `L^2` norm of the centered variable. | Exact. |
| Chapter 1 | (1.13), vector expectation/covariance | FORMALIZED | Covariance is the centered `L^2` pairing; vector means and covariance matrices are coordinatewise. | Exact finite-dimensional API. |
| Chapter 1 | Finite additivity | FORMALIZED | Disjoint finite event families have additive probability. | Pairwise-disjoint measurable family. |
| Chapter 1 | (1.14) | FORMALIZED | The indicator of a union is at most the sum of indicators. | Pointwise exact. |
| Chapter 1 | Lemma 1.4.1 | FORMALIZED | Union bound. | Exact finite and indexed forms. |
| Chapter 1 | Example 1.4.2 | FORMALIZED | Dense Erdos--Renyi graphs have no isolated vertices with high probability. | Includes the actual shared graph model, not only an abstract event estimate. |
| Chapter 1 | Conditional probability | FORMALIZED | `P(E given F)=P(E intersection F)/P(F)`. | Mathlib's zero-denominator convention is documented. |
| Chapter 1 | (1.15) | STRONGER | Law of total expectation. | Includes Banach-valued variables. |
| Chapter 1 | (1.16) | FORMALIZED | Total probability conditioned on a random variable. | Exact. |
| Chapter 1 | (1.17) | STRONGER | Total probability over a countable measurable partition. | Countable version; null conditioning cells vanish. |
| Chapter 1 | Example 1.5.1 | FORMALIZED | A nontrivial Rademacher sum cancels with probability at most `1/2`; the bound is sharp. | Exact, including the two-term equality example. |
| Chapter 1 | (1.18) | STRONGER | Jensen's inequality for scalar/vector variables, and the concave form. | General integrable forms. |
| Chapter 1 | (1.19) | STRONGER | Norm of an expectation is at most expected norm. | General real normed spaces. |
| Chapter 1 | (1.20) | FORMALIZED | Probability-space `L^p` norms increase with `p`. | Extended-valued master statement plus finite real wrappers. |
| Chapter 1 | (1.21) | FORMALIZED | Minkowski inequality for random variables. | Exact. |
| Chapter 1 | (1.22) | FORMALIZED | Holder and Cauchy--Schwarz for random variables. | Both endpoints are explicit. |
| Chapter 1 | CDF/tail identity | FORMALIZED | `P(X>t)=1-F_X(t)`. | Uses a measurable formulation. |
| Chapter 1 | Lemma 1.6.1 | STRONGER | Integrated-tail formula `E X = integral P(X>t) dt` for nonnegative `X`. | Infinite-valued and finite Bochner versions. |
| Chapter 1 | Proposition 1.6.2 | FORMALIZED | Markov inequality. | Correct `t>0`, nonnegativity, and integrability hypotheses are explicit. |
| Chapter 1 | Corollary 1.6.3 | FORMALIZED | Chebyshev inequality. | Exact under `MemLp 2` and `t>0`. |
| Chapter 1 | (1.23) | FORMALIZED | The variance of an i.i.d. sample mean is `sigma^2/n`. | Exact finite-variance form. |
| Chapter 1 | Theorem 1.7.1 | FORMALIZED | Strong law of large numbers. | Reconstructed from Mathlib's SLLN. |
| Chapter 1 | Convergence-in-distribution definition | FORMALIZED | CDFs converge at continuity points of the limit law. | Represented by Mathlib's measure-theoretic notion and Portmanteau consequences. |
| Chapter 1 | Definition 1.7.2; (1.24) | FORMALIZED | Standard/general normal laws, densities, means, and variances. | Density requires positive scale; the law identity also handles the degenerate scale. |
| Chapter 1 | Theorem 1.7.3 | FORMALIZED | Lindeberg--Levy CLT. | Positive `sigma`; pointwise CDF convergence follows via Portmanteau. |
| Chapter 1 | Example 1.7.4; (1.25) | FORMALIZED | Bernoulli/binomial moments and de Moivre--Laplace convergence. | Exact for `0<p<1`. |
| Chapter 1 | Definition 1.7.5; (1.26) | FORMALIZED | Poisson distribution and PMF. | Exact law-based interface. |
| Chapter 1 | Lemma 1.7.7 | FORMALIZED | Stirling asymptotic. | Exact asymptotic equivalence/ratio. |
| Chapter 1 | (1.27) | FORMALIZED | Fixed-parameter Poisson PMF asymptotic. | Exact. |
| Chapter 1 | Lemma 1.7.8; (1.28) | FORMALIZED | Elementary lower/upper factorial bounds. | Upper bound correctly assumes `1<=n`; the printed all-natural wording fails at Lean's `0^0` convention. |
| Chapter 1 | (1.29) | FORMALIZED | Log-factorial sum and integral upper estimate. | Exact content of the area comparison. |
| Chapter 1 | Remark 1.7.9; (1.30) | STRONGER | Gamma integral and `Gamma(n+1)=n!`, real and complex. | Includes the complex half-plane extension mentioned in prose. |
| Chapter 1 | (1.31) | FORMALIZED | Stirling asymptotic for Gamma. | Exact real asymptotic. |
| Chapter 1 | Exercise 1.3 | FORMALIZED | Finite Jensen and its converse. | Exact finite form supporting the Jensen discussion. |
| Chapter 1 | Exercise 1.4 | STRONGER | Maximum principle for convex functions on convex hulls. | Arbitrary-set supremum and finite-attainment versions. |
| Chapter 1 | Exercises 1.5--1.6 | FORMALIZED | Cube/cross-polytope convex-hull identities. | Explicit coefficient-witness subparts are construction-only and excluded. |
| Chapter 1 | Exercises 1.9--1.10 | FORMALIZED | Sharp isolated-vertex threshold in `G(n,p)`. | Eventual/asymptotic formulation; used by Remark 2.5.2. |
| Chapter 1 | Exercise 1.11(a) | STRONGER | Monotonicity of probability-space `L^p`. | Part (b) is a witness construction and out of scope. |
| Chapter 1 | Exercise 1.12 | FORMALIZED | Interpolation/moment inequality used later. | Necessary `MemLp` hypotheses are explicit. |
| Chapter 1 | Exercise 1.14 | FORMALIZED | Two-sided moment comparison used by later hints. | Exact. |
| Chapter 1 | Exercise 1.15(a--c) | FORMALIZED | Layer-cake/FTC moment identities. | (a) needs integrability; the PDF's differentiability-only (b) is repaired to a valid FTC/absolute-continuity form. |
| Chapter 1 | Exercise 1.16 | FORMALIZED | Paley--Zygmund inequality. | Exact and used in Chapter 3. |
| Chapter 1 | Exercise 1.17 | FORMALIZED | Finite-dimensional norm comparison. | Extremizer construction is out of scope. |
| Chapter 1 | Exercise 1.19 | FORMALIZED | `ell^p` duality formula. | The separate nonzero witness task is out of scope. |
| Chapter 2 | Proposition 2.1.2; (2.3) | FORMALIZED | Two-sided Mills-style Gaussian tail bounds, including `P(g>=t) <= phi(t)/t`. | Exact for `t>0`. |
| Chapter 2 | (2.4) | STRONGER | Heuristic probability of at least `3N/4` heads is about `exp(-N/8)/sqrt(2pi)`. | The PDF labels (2.4) heuristic; Lean rigorously proves a comparable exponential upper bound, without the heuristic prefactor. |
| Chapter 2 | Central-binomial paragraph | FORMALIZED | `P(S_N=N/2)` is asymptotic to `sqrt(2/(pi N))`, showing the `N^-1/2` CLT-error scale is unavoidable. | Exact asymptotic endpoint. |
| Chapter 2 | Theorem 2.2.1 | FORMALIZED | Hoeffding inequality for weighted independent Rademachers. | Exact constant `1/2` in the exponent. |
| Chapter 2 | (2.5) | FORMALIZED | Exponential Markov step for a Rademacher sum. | Proof-internal rather than a separately exported equation theorem. |
| Chapter 2 | (2.6) | FORMALIZED | Independence factors the MGF of a sum into a product. | The exact product step is used in the compiled proof. |
| Chapter 2 | (2.7) | FORMALIZED | `cosh x <= exp(x^2/2)`. | Promoted because it is load-bearing for Hoeffding. |
| Chapter 2 | (2.8) | FORMALIZED | The optimized exponential bound is `exp(-lambda t + lambda^2 ‖a‖_2^2/2)`. | Exact calculation is present in the theorem proof. |
| Chapter 2 | Remark 2.2.2 | FORMALIZED | Hoeffding gives Gaussian-like exponentially light tails. | The qualitative conclusion follows immediately from the exact bounds. |
| Chapter 2 | Remark 2.2.4 | FORMALIZED | A rigorous exponentially small bound for `3N/4` heads. | Exact source-facing wrapper. |
| Chapter 2 | Theorem 2.2.5 | FORMALIZED | Two-sided Hoeffding for Rademacher sums. | Lean also handles `t=0`. |
| Chapter 2 | Theorem 2.2.6 | FORMALIZED | Hoeffding for independent centered bounded variables. | Exact; proof prerequisites from Exercises 2.8--2.10 are promoted. |
| Chapter 2 | Theorem 2.3.1 | FORMALIZED | Chernoff upper-tail inequality for sums of independent Bernoulli variables. | Makes `mu>0` explicit and handles the optimizer safely. |
| Chapter 2 | (2.9) | FORMALIZED | Exponential Markov plus Bernoulli-MGF product. | Exact proof step. |
| Chapter 2 | Remark 2.3.2 | FORMALIZED | Chernoff left-tail inequality. | Exact for `0<t<=mu`. |
| Chapter 2 | (2.10) | FORMALIZED | Relative-entropy Chernoff bound before the quadratic simplification. | Supported by `entropy_ge_sq_third` and `entropy_lower_ge_sq_half`. |
| Chapter 2 | Corollary 2.3.4 | FORMALIZED | Two-sided small-deviation Chernoff bound. | The boundary `delta=1` is handled explicitly. |
| Chapter 2 | (2.11) | FORMALIZED | Definition of the sample mean estimator. | No standalone notation declaration, but the exact estimator is used. |
| Chapter 2 | (2.12) | FORMALIZED | Sample mean has mean `mu` and variance `sigma^2/N`. | Exact. |
| Chapter 2 | (2.13) | FORMALIZED | Chebyshev tail for the sample mean. | Composition of exact source results; no separate Chapter-2 wrapper. |
| Chapter 2 | Theorem 2.4.1 | FORMALIZED | Median-of-means achieves a Gaussian tail assuming only finite variance. | The divisibility/integer-block inaccuracy is rigorously repaired. |
| Chapter 2 | Proposition 2.5.1 | FORMALIZED | If expected degree is at least `C log n`, all Erdos--Renyi degrees lie within 10% of the mean with probability at least `.99`. | Includes an explicit constant and shared finite graph model. |
| Chapter 2 | Remark 2.5.2 | FORMALIZED | Below `(1-epsilon) log n`, isolated vertices appear, so sparse random graphs are far from regular. | Exact eventual threshold result supports the main-text remark. |
| Chapter 2 | (2.14) | FORMALIZED | Weighted Hoeffding-type tail for the class motivating subgaussianity. | General subgaussian theorem strictly contains the motivating examples up to constants. |
| Chapter 2 | (2.15) | FORMALIZED | Subgaussian tail definition `P(abs(X)>t) <= 2 exp(-c t^2)`. | Implemented through equivalent integrability properties with explicit constants. |
| Chapter 2 | (2.16) | FORMALIZED | Standard Gaussian MGF is `exp(lambda^2/2)`. | Exact law-based form. |
| Chapter 2 | (2.17) | STRONGER | Gaussian `L^p` norms grow like `sqrt(p)`. | Exact moment formula plus sharp asymptotic, stronger than the displayed upper bound. |
| Chapter 2 | Proposition 2.6.1 | FORMALIZED | Tail, moment, square-exponential, and centered-MGF definitions of subgaussianity are equivalent. | Constants are explicit rather than hidden. |
| Chapter 2 | Remark 2.6.2 | FORMALIZED | The all-`lambda` quadratic MGF bound forces mean zero. | Promoted load-bearing exercise endpoint. |
| Chapter 2 | Remark 2.6.3 | FORMALIZED | The normalization constant `2` in the equivalent definitions can be replaced by any absolute constant greater than one. | Exact quantitative rescaling. |
| Chapter 2 | Definition 2.6.4; (2.18) | FORMALIZED | Subgaussian variables and the `psi_2` infimum norm. | Infimum attainment is proved with required measurability/probability hypotheses. |
| Chapter 2 | `psi_2` triangle/norm prose | FORMALIZED | `psi_2` is a norm, including triangle inequality without independence. | Faithful; equality is a.e.-aware. |
| Chapter 2 | Proposition 2.6.6 | FORMALIZED | Tail, moment, square-MGF, and centered-MGF bounds in terms of the `psi_2` norm, with converse optimality up to constants. | Exact up to explicit absolute constants, as printed. |
| Chapter 2 | (2.19) | FORMALIZED | Pythagorean identity for independent centered scalar sums. | Exact. |
| Chapter 2 | Proposition 2.7.1 | FORMALIZED | `psi_2` norm squared of an independent centered sum is bounded by a constant times the sum of squared norms. | Exact up to the book's absolute constant. |
| Chapter 2 | Theorem 2.7.3 | FORMALIZED | Subgaussian Hoeffding inequality. | Exact up to an explicit absolute constant. |
| Chapter 2 | Example 2.7.4; (2.20) | FORMALIZED | Applying the subgaussian theorem to weighted Rademachers recovers classical Hoeffding up to constants. | Exact source-facing specialization. |
| Chapter 2 | Theorem 2.7.5 | FORMALIZED | Khintchine inequality for independent centered subgaussian variables. | Exact moment-growth form. |
| Chapter 2 | Proposition 2.7.6; (2.21) | FORMALIZED | The `psi_2` norm of a finite maximum grows like `sqrt(log N)` times the largest individual norm. | Safe nonempty/index hypotheses are explicit. |
| Chapter 2 | Proposition 2.7.6; (2.22) | FORMALIZED | Expected maximum has the corresponding `sqrt(log N)` bound. | Exact up to the absolute constant. |
| Chapter 2 | Remark 2.7.7 | STRONGER | Gaussian samples have no outliers; maxima are of order `sqrt(log N)`, sharply so for independent samples. | Proves both finite upper bounds and asymptotically sharp independent-Gaussian limits. |
| Chapter 2 | (2.23) | FORMALIZED | Centering cannot increase the `L^2` norm. | This is the explicit downstream use of Exercise 0.2. |
| Chapter 2 | Lemma 2.7.8; (2.24) | FORMALIZED | Centering a subgaussian variable preserves subgaussianity and controls its `psi_2` norm. | Equation (2.24) is the triangle-inequality proof step; the final constant-factor bound is proved. |
| Chapter 2 | Proposition 2.8.1 | FORMALIZED | Tail, moment, exponential-integrability, and local-MGF definitions of subexponentiality are equivalent. | Explicit local-MGF constants replace hidden constants. |
| Chapter 2 | Remark 2.8.3 | FORMALIZED | The MGF of `Exp(1)` diverges for `lambda>=1`. | Exact. |
| Chapter 2 | Definition 2.8.4; (2.25) | FORMALIZED | Subexponential variables and the `psi_1` infimum norm. | Exact. |
| Chapter 2 | Lemma 2.8.5 | FORMALIZED | `X` is subgaussian iff `X^2` is subexponential, with squared norm identity. | Exact. |
| Chapter 2 | Lemma 2.8.6 | FORMALIZED | Product of two subgaussians is subexponential with `psi_1` product bound. | Corrects the PDF proof's accidental `psi_2` label to `psi_1`. |
| Chapter 2 | (2.26) | FORMALIZED | Centering preserves `psi_1` up to an absolute constant. | Exact up to an explicit constant. |
| Chapter 2 | Remark 2.8.8 | FORMALIZED | Bounded => subgaussian => subexponential => all moments => finite variance => finite mean, with norm comparisons. | The PDF's displayed `‖g‖_2` wording in nearby proof context is correctly treated as a squared norm where required. |
| Chapter 2 | Remark 2.8.9 | FORMALIZED | `psi_alpha`/Orlicz norms generalize `psi_1` and `psi_2`. | Strict convexity and a.e.-separation hypotheses are made explicit. |
| Chapter 2 | Theorem 2.9.1 | FORMALIZED | Bernstein inequality for independent centered subexponential variables. | Exact Gaussian/exponential minimum form. |
| Chapter 2 | (2.27) | FORMALIZED | Exponential Markov/product step in Bernstein's proof. | Exact proof step. |
| Chapter 2 | (2.28) | FORMALIZED | The optimization parameter is constrained by the largest `psi_1` norm. | Exact local-MGF domain is encoded. |
| Chapter 2 | Corollary 2.9.2 | FORMALIZED | Weighted/simplified Bernstein inequality. | Exact. |
| Chapter 2 | Remark 2.9.4 | FORMALIZED | Normalized Bernstein has Gaussian small deviations and exponential large deviations. | Exact two-regime wrapper. |
| Chapter 2 | Theorem 2.9.5 | FORMALIZED | Variance-sensitive Bernstein inequality for bounded variables. | Promoted Exercise 2.47 prerequisites prove the MGF estimate. |
| Chapter 2 | Exercises 2.2, 2.4(b), 2.6 | FORMALIZED | Gaussian lower tail, truncated second moment, and exponential-moment tail. | Exercise 2.4(b) needs `t>0`; the printed all-real form contains `1/t`. |
| Chapter 2 | Exercises 2.5, 2.8--2.10 | FORMALIZED | `cosh` bound, symmetrization, Hoeffding lemma, and bounded Hoeffding. | All promoted because the core proof consumes them. |
| Chapter 2 | Exercise 2.11 | FORMALIZED | Chernoff left tail. | Exact. |
| Chapter 2 | Exercise 2.16 | FORMALIZED | Repairs median-of-means block integrality/divisibility. | Exact rigorous repair. |
| Chapter 2 | Exercises 2.22--2.24 | FORMALIZED | Gaussian moments, zero-mean MGF implication, and exact/basic `psi_2` examples. | Exercise 2.24(a) is corrected to use `abs(c)`. |
| Chapter 2 | Exercises 2.35, 2.37--2.38 | FORMALIZED | Interpolation/maximal bounds and sharp Gaussian maxima used later. | These are promoted/core endpoints rather than imported exercise leaves. |
| Chapter 2 | Exercises 2.41--2.42 | FORMALIZED | Subexponential equivalences and Orlicz/norm structure. | Corrected strictness/a.e. hypotheses are explicit. |
| Chapter 2 | Exercise 2.44(a) | FORMALIZED | `psi_1` centering. | Parts (b,c) are non-load-bearing practice leaves. |
| Chapter 2 | Exercise 2.47(a,b) | FORMALIZED | Variance-sensitive bounded MGF and Bernstein. | Exact promoted prerequisites for Theorem 2.9.5. |
| Chapter 3 | Theorem 3.1.1; (3.1) | FORMALIZED | A vector with independent, unit-second-moment, `K`-subgaussian coordinates has `‖X‖_2` concentrated around `sqrt(n)` with `psi_2` scale `C K^2`. | Exact with an explicit absolute constant. |
| Chapter 3 | (3.2) | FORMALIZED | Equivalent Gaussian tail for `abs(‖X‖_2-sqrt(n))`. | Exact up to the theorem's explicit constant. |
| Chapter 3 | (3.3) | FORMALIZED | Bernstein controls the centered squared norm with a mixed quadratic/linear tail. | Exact. |
| Chapter 3 | (3.4) | FORMALIZED | For nonnegative `z`, `abs(z-1)>=delta` implies `abs(z^2-1)>=max(delta,delta^2)`. | Exact deterministic transfer. |
| Chapter 3 | Remark 3.1.2 | FORMALIZED | Thin-shell phenomenon and bounded radial variance follow from norm concentration. | The main tail and its variance consequence are both proved; this replaces the frozen inventory's obsolete expository label. |
| Chapter 3 | (3.5) | FORMALIZED | Covariance-matrix entries are coordinate covariances. | Exact centered covariance, kept distinct from the uncentered second moment. |
| Chapter 3 | Proposition 3.2.1(a); (3.6) | FORMALIZED | `E <X,v>^2 = v^T Sigma v` for the second-moment matrix. | Exact. |
| Chapter 3 | Proposition 3.2.1(b) | FORMALIZED | `E ‖X‖_2^2 = tr(Sigma)`. | Exact. |
| Chapter 3 | Proposition 3.2.1(c) | FORMALIZED | For independent copies `X,Y`, `E<X,Y>^2` is the squared Frobenius norm of the second-moment matrix. | Exact product-space/independent-copy theorem; this part was absent in the stale inventory but is now implemented. |
| Chapter 3 | (3.7) | STRONGER | Spectral decomposition of a symmetric matrix into orthonormal eigenvectors. | General finite-dimensional spectral theorem; no Chapter-3 reconstruction wrapper is needed by the subsequent proof. |
| Chapter 3 | Proposition 3.2.2; (3.8) | FORMALIZED | The `k`th eigenvalue is the maximum Rayleigh quotient on the orthogonal complement of earlier eigenvectors. | The full ordered-`k` statement is now present; the old top-eigenvalue-only inventory is stale. |
| Chapter 3 | Definition 3.2.5; (3.9) | FORMALIZED | Isotropy means `E[XX^T]=I`, equivalently `E<X,v>^2=‖v‖^2`. | Correctly uncentered: isotropy does not silently impose zero mean. |
| Chapter 3 | (3.10) | FORMALIZED | Standard-score/whitening transform and affine reconstruction. | Lean treats the singular-covariance case correctly rather than writing an unconditional inverse square root. |
| Chapter 3 | (3.11) | FORMALIZED | Standard multivariate Gaussian density is proportional to `exp(-‖z‖^2/2)`. | Exact. |
| Chapter 3 | Proposition 3.3.1 | STRONGER | Standard Gaussian law is rotation invariant. | Stated for finite-dimensional real inner-product spaces/isometries, not only coordinate matrices. |
| Chapter 3 | Corollary 3.3.2 | FORMALIZED | Every standard-Gaussian marginal `<Z,v>` is Gaussian with variance `‖v‖^2`. | Exact. |
| Chapter 3 | Proposition 3.3.5; (3.12) | STRONGER | Gaussian law is uniquely determined by mean and covariance, including singular covariance. | General inner-product-space uniqueness, including degenerate laws. |
| Chapter 3 | Proposition 3.3.6; (3.13) | FORMALIZED | Invertible-covariance multivariate Gaussian density formula. | Uses positive-definite covariance, matching the PDF's invertibility requirement. |
| Chapter 3 | Corollary 3.3.7 | STRONGER | Jointly Gaussian variables are independent iff uncorrelated. | Mathlib supplies the general finite-family direction; local wrappers expose the pair case. |
| Chapter 3 | Proposition 3.3.8 | FORMALIZED | The uniform law on `sqrt(n) S^{n-1}` is isotropic. | Exact normalized-surface probability measure. |
| Chapter 3 | (3.15) | FORMALIZED | A normalized standard Gaussian direction is uniform on the sphere. | Exact pushforward identity. |
| Chapter 3 | (3.16) | FORMALIZED | Standard-Gaussian norm concentrates around `sqrt(n)`. | Exact concentration up to explicit constants. |
| Chapter 3 | Theorem 3.3.9 | STRONGER | Projective CLT: all one-dimensional marginals of the high-dimensional sphere converge to standard normal. | Uniform over every unit direction and every CDF threshold; the varying-dimension quantifiers are corrected explicitly. |
| Chapter 3 | Remark 3.3.10 | FORMALIZED | Exact one-dimensional marginal densities for uniform sphere/ball laws. | Exact normalized density laws, with dimension corrections from Exercise 3.27. |
| Chapter 3 | Proposition 3.3.11 | FORMALIZED | Parseval frames are equivalent to isotropic finite-support distributions. | Includes the exact finite uniform law. |
| Chapter 3 | Example 3.3.12 | FORMALIZED | Coordinate distribution is a Parseval frame/isotropic law. | Exact. |
| Chapter 3 | Example 3.3.13 | FORMALIZED | Mercedes--Benz frame is Parseval. | Exact. |
| Chapter 3 | Example 3.3.14 | FORMALIZED | Uniform discrete-cube/Rademacher vector is isotropic. | Exact. |
| Chapter 3 | Example 3.3.15 | FORMALIZED | Independent centered unit-variance coordinates form an isotropic vector. | Exact. |
| Chapter 3 | Definition 3.4.1 | FORMALIZED | A vector is subgaussian if every one-dimensional marginal is; its vector `psi_2` norm is the supremum over unit directions. | The real `sSup` API exposes the boundedness premise needed to avoid treating infinity as a real number. |
| Chapter 3 | Lemma 3.4.2 | FORMALIZED | Independent subgaussian coordinates give a subgaussian vector; vector norm is comparable to the largest coordinate norm. | Exact up to the book's absolute constants. |
| Chapter 3 | Example 3.4.3 | FORMALIZED | Rademacher vector is subgaussian with bounded vector norm. | Exact qualitative claim. |
| Chapter 3 | Example 3.4.4 | FORMALIZED | Standard Gaussian vector has constant vector `psi_2` norm. | Exact dimension-free conclusion with explicit value/bound. |
| Chapter 3 | Theorem 3.5.1 | STRONGER | Real Grothendieck inequality with an absolute constant at most `1.783`. | Full finite-dimensional theorem with Krivine's explicit constant and absolute-value strengthening. |
| Chapter 3 | Remark 3.5.2; (3.22)--(3.23) | FORMALIZED | Homogeneous scalar and Hilbert-vector forms of Grothendieck. | Correct nonempty ambient-coordinate hypothesis is explicit. |
| Chapter 3 | (3.24) | FORMALIZED | Raw Gaussian correlations satisfy `E[U_i V_j]=<u_i,v_j>`, turning the bilinear sum into an expectation. | Mathematical identity is present in a more general covariance API, though the current Grothendieck proof uses Krivine rounding instead of this first proof. |
| Chapter 3 | Remark 3.5.3 | FORMALIZED | Quadratic Grothendieck bounds for PSD and symmetric diagonal-free matrices. | Lean supplies the symmetry condition omitted from the printed diagonal-free shorthand. |
| Chapter 3 | Definition 3.5.4; (3.26) | FORMALIZED | Generic semidefinite-program schema: linear matrix objective, PSD variable, linear constraints. | The exact schema is present; the frozen inventory's contrary note is obsolete. |
| Chapter 3 | (3.27) | FORMALIZED | Matrix inner product is `tr(A^T X)=sum A_ij X_ij`. | Exact real matrix sum convention. |
| Chapter 3 | Remark 3.5.5 | FORMALIZED | SDP feasible sets are convex. | Exact. |
| Chapter 3 | (3.28) | FORMALIZED | Integer quadratic optimization over signs. | Objective and finite attainment are both formalized. |
| Chapter 3 | (3.29) | FORMALIZED | Vector/Gram SDP relaxation over unit vectors. | Exact and attainment-safe. |
| Chapter 3 | Proposition 3.5.6; (3.30) | FORMALIZED | The vector relaxation is equivalent to the PSD matrix SDP with diagonal one. | Both Gram directions and objective preservation are proved. |
| Chapter 3 | Theorem 3.5.7 | FORMALIZED | For symmetric PSD `A`, attained maxima satisfy `int(A)<=sdp(A)<=2K int(A)`. | Exact, with existence of maximizers included rather than an unsafe supremum. |
| Chapter 3 | Definition 3.6.1 | FORMALIZED | Cut size and maximum cut of a finite graph. | Exact graph-cardinality definitions. |
| Chapter 3 | Definition 3.6.2 | FORMALIZED | Adjacency matrix of a finite graph. | Direct upstream definition. |
| Chapter 3 | (3.34) | FORMALIZED | Gaussian hyperplane rounding labels each vertex by `sign <X_i,g>`. | Exact. |
| Chapter 3 | Lemma 3.6.5 | STRONGER | Grothendieck sign/arcsine identity for correlated Gaussian signs. | General unit-vector/finite-dimensional form. |
| Chapter 3 | (3.35) | FORMALIZED | `2 arccos(t)/pi >= .878(1-t)` on `[-1,1]`. | Uses exact rational `439/500`. |
| Chapter 3 | Example 3.7.3 | FORMALIZED | Rank-one tensor power `u^{tensor k}`. | Exact homogeneous rank-one construction. |
| Chapter 3 | Lemma 3.7.4 | FORMALIZED | Inner products of tensor powers satisfy `<u^k,v^k>=<u,v>^k`. | Exact. |
| Chapter 3 | Example 3.7.5 | FORMALIZED | A polynomial with nonnegative coefficients has a Hilbert feature map. | Exact, with convergence/summability explicit. |
| Chapter 3 | Example 3.7.6 | FORMALIZED | General signed coefficients admit two feature maps with the desired cross-inner-product. | Corrects the PDF's map typo: `Psi` must be evaluated at `v`, not `u`. |
| Chapter 3 | Example 3.7.8 | FORMALIZED | Sine admits signed feature maps; choosing `c=log(1+sqrt(2))` normalizes via `sinh c=1`. | Corrects a printed `cosh`/`sinh` slip in the norm computation. |
| Chapter 3 | (3.37) | FORMALIZED | Transformed unit vectors have inner products `sin(c <u_i,v_j>)`. | Exact Gram-realization step. |
| Chapter 3 | Gaussian/polynomial kernel prose | STRONGER | Polynomial and Gaussian kernels have explicit feature maps. | Exact explicit maps, stronger than mere existence. |
| Chapter 3 | Exercise 3.2 | FORMALIZED | Generalized thin-shell variance consequence. | Promoted and consumed in core. |
| Chapter 3 | Exercise 3.5 | FORMALIZED | Expected `ell^p` norm of an isotropic vector. | Covers finite and infinity ranges with explicit hypotheses. |
| Chapter 3 | Exercise 3.6 | FORMALIZED | Matching expected Gaussian `ell^p` norm estimates. | Exact scale, including the large-`p` regime. |
| Chapter 3 | Exercise 3.7 | FORMALIZED | Small-ball bounds for isotropic vectors. | Correct dimension/nonzero hypotheses are explicit. |
| Chapter 3 | Exercise 3.9 | FORMALIZED | Isotropic one-dimensional marginal identity. | Supplies the directional form (3.9). |
| Chapter 3 | Exercise 3.10 | FORMALIZED | Whitening/standard-score facts. | Correct singular-covariance formulation. |
| Chapter 3 | Exercise 3.13 | FORMALIZED | Expected maximum norm of subgaussian/Gaussian vectors. | Correct scale; the separate notes-only sharp-constant request is rejected under the non-load-bearing exercise policy. |
| Chapter 3 | Exercise 3.15 | FORMALIZED | General multivariate normal density. | Promoted input to the Gaussian-vector density development. |
| Chapter 3 | Exercise 3.16 | FORMALIZED | Characterizations of joint Gaussianity. | Exact promoted endpoints. |
| Chapter 3 | Exercise 3.18 | FORMALIZED | Ginibre/standard Gaussian matrix invariance. | Promoted proof-chain input. |
| Chapter 3 | Exercise 3.19 | FORMALIZED | GOE representation and invariance. | Exact promoted endpoints. |
| Chapter 3 | Exercise 3.20 | FORMALIZED | A Gaussian matrix sends orthogonal vectors to independent Gaussian images. | Later consumed by Chapter 9. |
| Chapter 3 | Exercise 3.22 | FORMALIZED | Gaussian radius and direction are independent; direction is uniform. | Strong measure-theoretic form, later consumed. |
| Chapter 3 | Exercise 3.23 | STRONGER | Random Gaussian points are in convex position with quantitative/exponential probability. | Includes a concrete standard-Gaussian cloud model and explicit failure bound. |
| Chapter 3 | Exercise 3.27 | FORMALIZED | Exact sphere/ball coordinate densities. | Corrected dimension exponents; supports Remark 3.3.10. |
| Chapter 3 | Exercise 3.32 | FORMALIZED | A marginal `psi_2` norm is at most vector norm times direction norm. | Promoted descriptive endpoint. |
| Chapter 3 | Exercise 3.34 | FORMALIZED | Subgaussian quadratic-form control used in later matrix chapters. | Later consumed by Chapter 8. |
| Chapter 3 | Exercise 3.37 | STRONGER | Isotropic subgaussian coordinates need not imply norm concentration without independence. | Complete explicit counterexample, later consumed by Chapter 6. |
| Chapter 3 | Exercises 3.47--3.48 | FORMALIZED | Equivalent Grothendieck assumptions and optimized numerical truncation. | Exercise 3.47 uses corrected rectangular indexing. |
| Chapter 3 | Exercise 3.49 | FORMALIZED | PSD quadratic Grothendieck consequences. | All parts promoted. |
| Chapter 3 | Exercise 3.50 | FORMALIZED | Diagonal-free quadratic Grothendieck consequences. | Lean adds the needed symmetry assumption. |
| Chapter 3 | Exercise 3.51 | FORMALIZED | Gram matrices are PSD and every finite PSD matrix is a Gram matrix. | Exact finite-dimensional equivalence. |
| Chapter 3 | Exercise 3.52; (3.40)--(3.41) | FORMALIZED | Bilinear sign optimization and its vector relaxation can be expressed as an SDP and approximated within a constant factor. | Both numbered exercise displays are in scope because this exercise is promoted and feeds the main SDP development; indices are corrected. |
| Chapter 3 | Exercise 3.53 | STRONGER | Grothendieck sign/arcsine identity. | Unique promoted endpoint, generalized beyond the exercise's coordinate presentation. |
| Chapter 4 | Theorem 4.1.1 | FORMALIZED | Every real rectangular matrix has an SVD with nonnegative decreasing singular values and orthonormal left/right families. | PDF proof's final summand has the typo `u_i v_j^T`; Lean correctly uses matching index `i`. |
| Chapter 4 | Remark 4.1.2 | FORMALIZED | An SVD stretches right singular directions by their singular values and rotates them to left singular directions. | Exact mathematical content; zero singular values are handled explicitly. |
| Chapter 4 | Remark 4.1.4 | FORMALIZED | Left/right singular vectors diagonalize `AA^T`/`A^TA`, and singular values are square roots of both Gram spectra. | The two singular equations give the stated Gram eigenpairs; the left equation is physically located in the later perturbation module. |
| Chapter 4 | Theorem 4.1.6 | FORMALIZED | Courant--Fischer max--min and min--max formulas for ordered eigenvalues. | Both arbitrary-subspace directions and attainment are present. |
| Chapter 4 | Corollary 4.1.7 | STRONGER | Courant--Fischer formulas for singular values. | Lean gives safe zero-indexed/zero-padded rectangular semantics and explicit attainment; the PDF informally speaks of `n` singular values. |
| Chapter 4 | Definition 4.1.8 | FORMALIZED | The Euclidean operator norm is the least uniform stretch factor, equivalently a unit-sphere/nonzero-vector maximum. | Empty dimensions are excluded where maxima require nonempty spheres. |
| Chapter 4 | Lemma 4.1.10 | FORMALIZED | Frobenius and operator norms are invariant under orthogonal left/right multiplication. | Faithful. |
| Chapter 4 | Lemma 4.1.11 | FORMALIZED | Frobenius/operator norms equal the `l2`/maximum aggregates of singular values, with rank comparison. | Lean includes nonempty-index guards. |
| Chapter 4 | Remark 4.1.12 | FORMALIZED | For symmetric matrices, the operator norm is the maximum absolute eigenvalue/Rayleigh quotient. | This is equation (4.10). |
| Chapter 4 | Theorem 4.1.13 | FORMALIZED | Eckart--Young--Mirsky: best rank-`k` operator-norm approximation error is the next singular value. | The PDF says `rank B = k`, which is false when `rank A < k`; Lean correctly minimizes over `rank B <= k` and guards the endpoint. Record as a source correction. |
| Chapter 4 | Lemma 4.1.14 | FORMALIZED | Weyl perturbation bounds for ordered eigenvalues and singular values. | Faithful with explicit index ranges. |
| Chapter 4 | Theorem 4.1.15 | FORMALIZED | Davis--Kahan controls an eigenvector angle by perturbation norm over a spectral gap. | Lean states valid gap/index hypotheses that the surrounding PDF prose leaves contextual. |
| Chapter 4 | Lemma 4.1.16 | FORMALIZED | Davis--Kahan for spectral projections/invariant subspaces. | Faithful; equations (4.11)--(4.13) are in its proof chain. |
| Chapter 4 | Lemma 4.1.17 | FORMALIZED | Gram error, quadratic distortion, and squared extreme-singular-value bounds are equivalent approximate-isometry conditions. | Faithful. |
| Chapter 4 | Remark 4.1.18 | FORMALIZED | A Gram error `max(delta,delta^2)` implies unsquared singular values lie in `[1-delta,1+delta]`. | PDF labels this a **Remark**, not a lemma; older inventory wording “Lemma 4.1.18” is a citation-kind mismatch. |
| Chapter 4 | Definition 4.2.1 | FORMALIZED | An internal epsilon-net covers every point of a metric-space subset within epsilon. | Faithful through Mathlib's `IsNet`. |
| Chapter 4 | Definition 4.2.2 | FORMALIZED | Covering number is the smallest cardinality of an epsilon-net. | Lean uses `ENat` so infinite covering numbers are meaningful. |
| Chapter 4 | Remark 4.2.3 | FORMALIZED | Compact sets admit finite epsilon-nets. | Lean makes completeness/positive-radius assumptions explicit. |
| Chapter 4 | Definition 4.2.4 | FORMALIZED | Packing number is the largest cardinality of an epsilon-separated subset. | Lean uses extended cardinality. |
| Chapter 4 | Remark 4.2.5 | FORMALIZED | Epsilon-separated centers have disjoint radius-epsilon/2 balls. | PDF proof prose uses the wrong radius in one sentence; Lean has the correct epsilon/2. |
| Chapter 4 | Lemma 4.2.6 | FORMALIZED | A maximal epsilon-separated subset is an epsilon-net. | Faithful. |
| Chapter 4 | Remark 4.2.7 | FORMALIZED | Greedily adding uncovered points constructs a finite net when the packing number is finite. | The finite-existence form captures the algorithmic conclusion, not an executable algorithm. |
| Chapter 4 | Lemma 4.2.8 | FORMALIZED | Covering and packing numbers satisfy `P(2 epsilon) <= N(epsilon) <= P(epsilon)`. | Faithful. |
| Chapter 4 | Definition 4.2.9 | FORMALIZED | Minkowski sum of two Euclidean sets. | Faithful. |
| Chapter 4 | Proposition 4.2.10 | STRONGER | Volume lower/upper bounds sandwich covering and packing numbers. | Cross-multiplied `ENNReal` form handles infinite/unbounded cases without illegal division; it implies the finite PDF display. |
| Chapter 4 | Corollary 4.2.11 | FORMALIZED | Euclidean ball/sphere covering numbers have `(1/epsilon)^n` lower and `(1+2/epsilon)^n` upper bounds. | Includes the simplified small-scale form (4.18). |
| Chapter 4 | Definition 4.2.14 | FORMALIZED | Hamming distance counts differing coordinates of binary words. | Faithful. |
| Chapter 4 | Proposition 4.2.15 | FORMALIZED | Hamming-cube covering/packing numbers are bounded by reciprocal Hamming-ball volumes. | Rational form avoids truncating natural division. |
| Chapter 4 | Proposition 4.3.1 | FORMALIZED | Coding a metric set to accuracy epsilon requires/admits about its metric entropy in bits. | Lean makes “accuracy” precise as encoding fibres of diameter at most epsilon; this matches the PDF proof but resolves its factor-two ambiguity. |
| Chapter 4 | Example 4.3.2 | FORMALIZED | Repetition coding corrects up to `r` errors with block length `(2r+1)k`. | Faithful and includes equation (4.19). |
| Chapter 4 | Definition 4.3.3 | FORMALIZED | An error-correcting code is an encoding/decoding pair correcting every word within Hamming radius `r`. | Faithful. |
| Chapter 4 | Lemma 4.3.4 | FORMALIZED | A sufficiently separated packing yields an error-correcting code. | Faithful with finite/feasibility assumptions explicit. |
| Chapter 4 | Theorem 4.3.5 | FORMALIZED | There exist efficient binary codes correcting `r` errors with near-linear redundancy. | PDF omits feasibility such as `2r <= n`; Lean adds it. Record this source-side omission. |
| Chapter 4 | Remark 4.3.6 | FORMALIZED | Required extra bits grow nearly linearly with the number of correctable errors. | A direct asymptotic corollary of the quantified theorem; no separate declaration. |
| Chapter 4 | Lemma 4.4.1 | FORMALIZED | Operator norm can be bounded from its values on an epsilon-net. | Faithful with denominator range explicit. |
| Chapter 4 | Lemma 4.4.2 | FORMALIZED | Bilinear/quadratic forms on one or two nets control the full matrix norm. | Includes symmetric and rectangular forms. |
| Chapter 4 | Theorem 4.4.3 | FORMALIZED | Independent centered subgaussian entries give `‖A‖ <= C K(sqrt m+sqrt n+t)` with subgaussian failure probability. | PDF proof interchanges two indices in one sum; Lean uses the corrected double sum. |
| Chapter 4 | Remark 4.4.4 | FORMALIZED | Integrating the tail yields the corresponding expected operator-norm bound. | Faithful. |
| Chapter 4 | Remark 4.4.5 | FORMALIZED | The order `sqrt m+sqrt n` is optimal because row/column norms lower-bound the operator norm. | Faithful. |
| Chapter 4 | Remark 4.4.6 | FORMALIZED | Independence can be weakened to independent subgaussian rows or columns. | Faithful. |
| Chapter 4 | Corollary 4.4.7 | FORMALIZED | A symmetric matrix with independent centered subgaussian upper-triangular entries has the same norm scale. | Faithful. |
| Chapter 4 | Definition 4.5.1 | FORMALIZED | Balanced two-community stochastic block model with within/between probabilities and self-loops. | Lean uses `Fin (2*k)` and `Sym2`, making even size and parameter ranges explicit while retaining the PDF's self-loops. |
| Chapter 4 | Theorem 4.5.2 | FORMALIZED | Spectral clustering recovers all but 1% of labels under a signal-to-noise separation. | Tie handling and global label swap are explicit. The PDF's intermediate eigengap notation has a factor-two inconsistency; Lean uses the exact gap. |
| Chapter 4 | Remark 4.5.3 | FORMALIZED | The guarantee is nontrivial at expected degree of order one and reaches the stated sparse scale. | Faithful after keeping the loop-aware expected degree. |
| Chapter 4 | Theorem 4.6.1 | FORMALIZED | Independent isotropic subgaussian rows give simultaneous two-sided singular-value bounds. | Safe dimension/measurability hypotheses are explicit. |
| Chapter 4 | Remark 4.6.2 | FORMALIZED | The two-sided singular-value deviation also has an expectation form. | Faithful. |
| Chapter 4 | Theorem 4.7.1 | STRONGER | Bounded-direction subgaussian vectors admit operator-norm sample second-moment/covariance estimation. | Lean covers singular population second moments without assuming invertible whitening and binds iid/measurability hypotheses explicitly. The PDF calls an uncentered second moment “covariance” in places. |
| Chapter 4 | Remark 4.7.2 | FORMALIZED | Sample complexity is of order `K^4 epsilon^-2 n` (constant dependence included). | PDF prose suppresses dependence on the subgaussian constant; Lean retains it. |
| Chapter 4 | Remark 4.7.3 | FORMALIZED | A high-probability version follows with a confidence parameter. | Faithful. |
| Chapter 4 | Definition 4.7.4 | FORMALIZED | Two-component spherical Gaussian-mixture sampling model. | Current declarations lack a source-numbered doc citation, but their model matches the PDF. |
| Chapter 4 | Theorem 4.7.5 | FORMALIZED | Leading-eigenvector spectral clustering recovers at least 99% of Gaussian-mixture labels at the stated separation/sample scale. | Lean gives an outer-measure failure bound because measurability of the ordered-eigenbasis selector is unavailable; operational probability guarantee is retained. PDF has an incorrect cross-reference to a Chapter 3 network section. |
| Chapter 4 | Eq. (4.1) | FORMALIZED | SVD rank-one expansion. | Corrects the PDF proof typo `v_j` to `v_i`. |
| Chapter 4 | Eq. (4.2) | FORMALIZED | Images of distinct right singular vectors are orthogonal. | Faithful. |
| Chapter 4 | Eq. (4.3) | FORMALIZED | `A v_i = s_i u_i`. | Includes the zero-singular-value case. |
| Chapter 4 | Eq. (4.5) | FORMALIZED | Singular values are square roots of both Gram spectra. | Expressed through eigenpair equations rather than a single square-root equality. |
| Chapter 4 | Eq. (4.6) | FORMALIZED | Courant--Fischer eigenvalue formulas. | Faithful. |
| Chapter 4 | Eq. (4.7) | FORMALIZED | Frobenius inner product equals `tr(A^T B)`. | Faithful. |
| Chapter 4 | Eq. (4.8) | FORMALIZED | Squared Frobenius norm equals self-pairing/trace. | Faithful. |
| Chapter 4 | Eq. (4.9) | FORMALIZED | Equivalent unit-sphere/nonzero-vector/operator formulations of `‖A‖`. | Nonempty dimensions explicit. |
| Chapter 4 | Eq. (4.10) | FORMALIZED | Symmetric operator norm is the maximum absolute Rayleigh quotient. | Faithful. |
| Chapter 4 | Eq. (4.11) | FORMALIZED | First spectral-projection Davis--Kahan norm chain. | Proof-local but Lean-checked. |
| Chapter 4 | Eq. (4.12) | FORMALIZED | Lower bound on the separated spectral block. | Proof-local. |
| Chapter 4 | Eq. (4.13) | FORMALIZED | Upper bound on the unperturbed spectral block. | Proof-local. |
| Chapter 4 | Eq. (4.14) | FORMALIZED | Extreme singular values are the maximum/minimum stretch on the unit sphere. | Faithful. |
| Chapter 4 | Eq. (4.15) | FORMALIZED | Gram deviation implies unsquared singular-value deviation. | PDF item is Remark 4.1.18. |
| Chapter 4 | Eq. (4.16) | STRONGER | Euclidean metric is `d(x,y)=‖x-y‖_2`. | No project wrapper is needed; the ambient instance is more general than `R^n`. |
| Chapter 4 | Eq. (4.17) | FORMALIZED | Sharp volumetric covering bounds for the Euclidean unit ball/sphere. | Faithful. |
| Chapter 4 | Eq. (4.18) | FORMALIZED | Simplified `(1/epsilon)^n <= N <= (3/epsilon)^n` for `0<epsilon<=1`. | Faithful. |
| Chapter 4 | Eq. (4.19) | FORMALIZED | Repetition-code block length `n=(2r+1)k`. | Faithful. |
| Chapter 4 | Eq. (4.20) | FORMALIZED | Quarter-nets of the two unit spheres have sizes at most `9^n` and `9^m`. | Faithful. |
| Chapter 4 | Eq. (4.21) | FORMALIZED | Two quarter-nets control the operator norm by twice the largest sampled bilinear form. | Faithful. |
| Chapter 4 | Eq. (4.22) | FORMALIZED | Fixed bilinear form of a subgaussian-entry matrix has a subgaussian tail. | PDF proof has an index typo; Lean uses the correct row/column coordinates. |
| Chapter 4 | Eq. (4.23) | FORMALIZED | Union bound over both nets. | Proof-local. |
| Chapter 4 | Eq. (4.24) | FORMALIZED | Choice `u = C K(sqrt n+sqrt m+t)` closing the net proof. | Proof-local. |
| Chapter 4 | Eq. (4.25) | FORMALIZED | SBM centered-noise operator norm is `O(sqrt n)` with exponentially high probability. | Source eigengap constants later have a factor-two inconsistency; the noise bound itself is captured. |
| Chapter 4 | Eq. (4.26) | FORMALIZED | Two-sided extreme singular-value bounds. | Faithful. |
| Chapter 4 | Eq. (4.27) | FORMALIZED | Stronger normalized Gram-matrix deviation bound. | Stronger intermediate endpoint explicitly exposed. |
| Chapter 4 | Eq. (4.28) | FORMALIZED | For fixed unit `x`, `‖Ax‖^2` is the sum of squared row inner products. | Proof-local finite-sum identity. |
| Chapter 4 | Eq. (4.29) | FORMALIZED | Directional subgaussian norm is controlled by its `L2` norm. | PDF uses this as a standing assumption; Lean binds it locally. |
| Chapter 4 | Eq. (4.30) | FORMALIZED | Expected relative sample second-moment error. | Faithful with `K^4` dependence visible. |
| Chapter 4 | Exercise Eq. (4.32) | FORMALIZED | `infinity -> 1` norm is attained on sign vectors. | Faithful. |
| Chapter 4 | p.108 after (4.14) | FORMALIZED | Extreme singular values bound Euclidean distortion; exact isometries are equivalent to orthonormal columns, a Gram identity, and all singular values being one. | Condition-number notation itself is not separately defined, but the mathematical inequalities/equivalences are. |
| Chapter 4 | pp.119--122, SBM signal calculation | FORMALIZED | Expected adjacency has two block eigenvectors/eigenvalues, rank at most two, and `A=D+R` separates signal from noise. | PDF says rank two without nondegeneracy and prints wrong eigenvalues for the displayed `2x2` matrix; Lean correctly states rank `<=2` and eigenvalues `p+q,p-q`. |
| Chapter 4 | pp.121--123, SBM algorithm | FORMALIZED | Second-eigenvector signs give a spectral classifier, with misclassification controlled by eigenvector error modulo label swap. | Lean supplies deterministic tie handling and normalized vectors missing from the prose. |
| Chapter 4 | p.126 before Theorem 4.7.1 | FORMALIZED | Sample second moment is unbiased and converges entrywise by the strong law. | “Covariance” is only correct under centering; Lean names the uncentered object as a second moment. |
| Chapter 4 | pp.129--130, GMM signal calculation | FORMALIZED | Mixture second moment has spike `I+mu mu^T`; its top eigendirection is the mean direction and drives classification. | Faithful with deterministic eigenvector choice. |
| Chapter 4 | Exercise 4.2 | FORMALIZED | Operator-norm axioms, transpose invariance, submultiplicativity, and submatrix monotonicity. | Faithful. |
| Chapter 4 | Exercise 4.3 | FORMALIZED | Operator/Frobenius norms of rank-one and diagonal matrices. | Faithful. |
| Chapter 4 | Exercise 4.4 | FORMALIZED | Rank/Frobenius/operator inequalities and sharpness witnesses. | PDF's exact-rank lower-sharpness clause is false for `r>1`; Lean proves the valid `rank<=r` statement and separate endpoint witnesses. |
| Chapter 4 | Exercise 4.7 | FORMALIZED | Operator norm versus row/column Euclidean norms, with equality for orthogonal families. | Faithful. |
| Chapter 4 | Exercise 4.9 | FORMALIZED | Walsh/Hadamard matrices are orthogonal after normalization. | PDF omits that the dimension must be `2^k`; Lean adds it. |
| Chapter 4 | Exercise 4.12 | FORMALIZED | Norm of a difference of orthogonal projections. | Faithful with rank cases explicit. |
| Chapter 4 | Exercise 4.13 | FORMALIZED | Davis--Kahan bound for leading eigenspace projections. | Valid index/gap hypotheses are explicit. |
| Chapter 4 | Exercise 4.14 | FORMALIZED | Hermitian dilation converts singular triples into positive/negative eigenpairs. | PDF calls displayed vectors “eigenvalues”; Lean correctly treats them as eigenvectors/eigenpairs. |
| Chapter 4 | Exercise 4.16 | FORMALIZED | Small acute angle implies closeness up to a global sign. | Faithful. |
| Chapter 4 | Exercise 4.19 | FORMALIZED | Exact formulas for `1->infinity`, `1->2`, and `2->infinity` norms. | Faithful with nonempty dimensions. |
| Chapter 4 | Exercise 4.20 | FORMALIZED | `infinity->1` sign formula, rank-one duality, and failure of a quadratic analogue. | Faithful. |
| Chapter 4 | Exercise 4.21 | FORMALIZED | Cut norm is equivalent to the corresponding sign/operator formulation. | PDF hint has an index typo; Lean uses the corrected indices. |
| Chapter 4 | Exercise 4.25 | FORMALIZED | Covering and packing numbers are invariant under closure. | Faithful. |
| Chapter 4 | Exercise 4.32 | FORMALIZED | Hamming-cube volume bounds prove Proposition 4.2.15. | Faithful. |
| Chapter 4 | Exercise 4.33 | FORMALIZED | Packing yields an error-correcting code with the stated bit budget. | Lean adds `1<=r` and `2r<=n` feasibility. |
| Chapter 4 | Exercise 4.34 | FORMALIZED | One-/two-net operator-norm bounds. | Requires the necessary net-radius range below one. |
| Chapter 4 | Exercise 4.35 | FORMALIZED | Symmetric quadratic-form net bound. | Requires radius below one-half for `1-2epsilon`. |
| Chapter 4 | Exercise 4.36 | FORMALIZED | General bilinear/quadratic net lemma used as Lemma 4.4.2. | Exercise provenance is promoted into the numbered lemma endpoint. |
| Chapter 4 | Exercise 4.37 | FORMALIZED | Net argument for uniform norm deviations. | Lean keeps the printed norm-deviation conclusion; the hint's squared version is only auxiliary. |
| Chapter 4 | Exercise 4.38 | FORMALIZED | Tail-to-expectation conversion for the net bound. | Faithful. |
| Chapter 4 | Exercise 4.39 | FORMALIZED | Random Gaussian points construct a Euclidean net with high probability. | Supports the random half of Remark 4.2.13. |
| Chapter 4 | Exercise 4.41 | FORMALIZED | Tail/expectation variants of two-sided subgaussian singular-value bounds. | Faithful. |
| Chapter 4 | Exercise 4.43 | FORMALIZED | Independent-row/column variants of subgaussian matrix norm estimates. | Faithful. |
| Chapter 4 | Exercise 4.44 | FORMALIZED | Expected norms for matrices with independent rows/columns. | PDF formulas omit expectation signs; Lean follows the hints and supplies the mathematically intended expectations. |
| Chapter 4 | Exercise 4.47 | FORMALIZED | Two-sided subgaussian matrix bounds in the unnormalized/source form. | Faithful. |
| Chapter 4 | Exercise 4.49 | FORMALIZED | High-probability covariance/second-moment estimation. | Faithful. |
| Chapter 4 | Exercise 4.51 | FORMALIZED | Gaussian-mixture spectral clustering theorem. | Lean fixes eigenvector ties/global sign and gives an outer-measure failure bound. |
| Chapter 5 | Theorem 5.1.3 | FORMALIZED | Every Lipschitz function on the radius-`sqrt n` sphere has dimension-free subgaussian concentration about its mean. | Lean binds positive dimension, measurability/integrability, and the zero-Lipschitz branch. |
| Chapter 5 | Lemma 5.1.6 | FORMALIZED | Any set occupying at least half the sphere has exponentially large metric blow-ups. | Lean proves it independently of Appendix isoperimetry and requires measurability/nonemptiness. |
| Chapter 5 | Remark 5.1.7 | FORMALIZED | Even exponentially small sets blow up to large measure after a modest enlargement. | Faithful corrected range `s>=0`, `t>=s`. |
| Chapter 5 | Remark 5.2.1 | FORMALIZED | Mean, median, and `L^p` centers are interchangeable up to subgaussian-scale constants. | Lean makes integrability/`MemLp` assumptions explicit. |
| Chapter 5 | Theorem 5.2.3 | FORMALIZED | Lipschitz functions of a standard Gaussian vector concentrate subgaussianly. | Proved from the verified Gaussian MGF theorem, not Appendix isoperimetry; handles `K=0`. |
| Chapter 5 | Example 5.2.4 | FORMALIZED | Gaussian linear functionals and the Euclidean norm are special cases of Gaussian concentration. | Faithful, including degenerate marginals. |
| Chapter 5 | Remark 5.2.8 | FORMALIZED | Gaussian polar decomposition generates Haar orthogonal matrices; determinant correction gives Haar special-orthogonal matrices. | PDF falsely claims the raw Gaussian polar factor is Haar on `SO(n)`; it is Haar on `O(n)`. Lean records the necessary determinant/sign correction. |
| Chapter 5 | Theorem 5.2.10 | FORMALIZED | Dimension-free concentration on the continuous cube and radius-`sqrt n` Euclidean ball. | The radial map is corrected at zero and targets `sqrt n B_2^n`. |
| Chapter 5 | Theorem 5.3.1 | FORMALIZED | Johnson--Lindenstrauss: `N` points embed into `O(epsilon^-2 log N)` dimensions with pairwise distances preserved. | PDF omits the cardinality hypothesis `card X = N`, `m<=n`, and `0<epsilon<1`; Lean binds them. |
| Chapter 5 | Lemma 5.3.2 | FORMALIZED | A random `m`-dimensional projection has exact second moment and concentrates for each fixed vector. | Faithful. |
| Chapter 5 | Remark 5.3.3 | FORMALIZED | JL is non-adaptive to the data and independent of ambient dimension. | PDF calls the map `P` in prose although the theorem uses `Q`; use the theorem's notation in comments. |
| Chapter 5 | Remark 5.3.4 | FORMALIZED | The logarithmic target dimension is optimal in general, even for nonlinear embeddings. | PDF misnames the target dimension `n`; Lean uses `m`. |
| Chapter 5 | Theorem 5.4.1 | FORMALIZED | Matrix Bernstein tail bound for sums of independent centered bounded random matrices. | Lean handles positive dimensions, measurability, and degenerate `K,sigma` branches. |
| Chapter 5 | Definition 5.4.2 | FORMALIZED | Spectral functional calculus defines `f(X)` by applying `f` to eigenvalues. | Inverse/log identities are separately guarded by their legal domains. |
| Chapter 5 | Definition 5.4.3 | FORMALIZED | Loewner order compares symmetric matrices by positive semidefiniteness. | Faithful. |
| Chapter 5 | Proposition 5.4.4 | FORMALIZED | Loewner order implies eigenvalue/trace monotonicity, norm intervals, and scalar spectral inequalities. | Nonempty dimensions explicit. |
| Chapter 5 | Remark 5.4.5 | FORMALIZED | `‖X‖<=a` is equivalent to `-aI <= X <= aI`. | Faithful. |
| Chapter 5 | Theorem 5.4.7 | FORMALIZED | Golden--Thompson trace-exponential inequality. | Verified wrapper over the proved vendored Matrix Concentration theorem; this is not HDP Appendix content. |
| Chapter 5 | Theorem 5.4.8 | FORMALIZED | Lieb concavity of `A -> tr exp(H+log A)`. | Proved vendored dependency, not an external `sorry`. |
| Chapter 5 | Lemma 5.4.9 | FORMALIZED | Expected/random-matrix form of Lieb's inequality. | Lean adds exponential integrability and positivity needed to define the expectation/log. |
| Chapter 5 | Lemma 5.4.10 | FORMALIZED | Matrix MGF is bounded by the variance term in the Bernstein range. | Denominator-free `theta*K<3` handles `K=0`. |
| Chapter 5 | Remark 5.4.11 | FORMALIZED | Integrating matrix Bernstein yields an expected-norm bound. | This is equation (5.18), promoted from Exercise 5.20. |
| Chapter 5 | Remark 5.4.12 | FORMALIZED | The logarithmic dimension factor is a genuine price and can be necessary. | PDF mistakenly compares equation (5.18) with itself; comments should describe the intended scalar-vs-matrix comparison. |
| Chapter 5 | Theorem 5.4.13 | FORMALIZED | Matrix Hoeffding tail inequality for a Rademacher matrix series. | Faithful. |
| Chapter 5 | Theorem 5.4.14 | FORMALIZED | Matrix Khintchine moment bound for a Rademacher matrix series. | Includes every `p>=1`, especially later-used `p=1`. |
| Chapter 5 | Remark 5.4.15 | FORMALIZED | Hermitian dilation extends matrix concentration to nonsymmetric rectangular matrices. | Correct rectangular dimensions and sharper max-variance form are explicit. |
| Chapter 5 | Theorem 5.5.1 | FORMALIZED | Matrix Bernstein yields spectral recovery in the sparse stochastic block model. | Even size, probability ranges, loops, signs/ties, and an explicit recovery constant are bound locally. |
| Chapter 5 | Remark 5.5.2 | FORMALIZED | Expected degree is `(a+b)/2`, and logarithmic degree is enough in the theorem's regime. | Faithful in the loop-aware model. |
| Chapter 5 | Theorem 5.6.1 | FORMALIZED | General bounded-distribution covariance/second-moment estimation via matrix Bernstein. | PDF leaves iid samples contextual and calls an uncentered moment covariance; Lean binds the sample and uses precise terminology. |
| Chapter 5 | Remark 5.6.2 | FORMALIZED | Sufficient sample size is `C K^2 epsilon^-2 n log n`. | PDF suppresses `K^2`; Lean retains it and states only sufficiency. |
| Chapter 5 | Remark 5.6.3 | FORMALIZED | Effective rank refines covariance bounds for low-dimensional distributions. | Zero-safe. |
| Chapter 5 | Remark 5.6.4 | FORMALIZED | Effective/stable rank identities, bounds, continuity, and support-subspace behavior. | PDF expressions are undefined at zero and one rectangular sum is misindexed; Lean gives zero-safe definitions and continuity only off zero. |
| Chapter 5 | Remark 5.6.5 | FORMALIZED | Effective-rank covariance estimation has a high-probability form. | Requires nonzero population second moment explicitly. |
| Chapter 5 | Remark 5.6.6 | FORMALIZED | Without a boundedness assumption, covariance estimation can fail badly. | Precise quantified rare-atom witness replaces qualitative prose. |
| Chapter 5 | Eq. (5.1) | FORMALIZED | Two-sided subgaussian tail for a Lipschitz sphere observable. | Zero-Lipschitz case is handled safely. |
| Chapter 5 | Eq. (5.4) | FORMALIZED | Blow-up lower bound for the median sublevel set. | Alternate proof, same endpoint. |
| Chapter 5 | Eq. (5.5) | FORMALIZED | Lipschitzness sends the enlarged median sublevel set into `{f<=M+t}`. | Proof-local. |
| Chapter 5 | Eq. (5.6) | FORMALIZED | Gaussian Lipschitz tail inequality. | Faithful. |
| Chapter 5 | Eq. (5.9) | FORMALIZED | JL pairwise approximate-isometry conclusion. | Faithful with missing source hypotheses supplied. |
| Chapter 5 | Eq. (5.10) | FORMALIZED | Exact RMS/second-moment norm of a random projection. | Faithful. |
| Chapter 5 | Eq. (5.11) | FORMALIZED | Fixed-difference random-projection tail before the union bound. | Faithful. |
| Chapter 5 | Eq. (5.12) | FORMALIZED | Spectral formulas for matrix powers, inverse, and exponential. | PDF writes `X^-1` without invertibility; Lean guards inverse/log domains. |
| Chapter 5 | Eq. (5.13) | FORMALIZED | Operator norm is equivalent to the Loewner interval `-aI <= X <= aI`. | Faithful. |
| Chapter 5 | Eq. (5.14) | FORMALIZED | Matrix inverse reverses order and matrix logarithm preserves order. | Corrects the PDF's inverse direction and works on the positive-definite domain. |
| Chapter 5 | Eq. (5.15) | FORMALIZED | Symmetric norm reduces to largest eigenvalues of `S` and `-S`. | Proof-local. |
| Chapter 5 | Eq. (5.16) | FORMALIZED | Exponential Markov/MGF upper-tail step for `lambda_max(S)`. | Proof-local. |
| Chapter 5 | Eq. (5.17) | FORMALIZED | Iterated Lieb/log-MGF inequality for a sum. | Integrability hypotheses explicit. |
| Chapter 5 | Eq. (5.18) | FORMALIZED | Expected matrix-Bernstein norm bound. | Promoted Exercise 5.20; later load-bearing. |
| Chapter 5 | Eq. (5.19) | FORMALIZED | Expected sparse-SBM noise norm. | Faithful. |
| Chapter 5 | Eq. (5.20) | FORMALIZED | Simplified sparse-SBM noise bound sufficient for 1% error. | Lean keeps an explicit adequate constant. |
| Chapter 5 | Eq. (5.21) | FORMALIZED | Almost-sure sample-energy boundedness assumption for covariance estimation. | Bound locally quantified. |
| Chapter 5 | Eq. (5.22) | FORMALIZED | Squared/tracial reformulation of the boundedness assumption. | Faithful. |
| Chapter 5 | Eq. (5.23) | FORMALIZED | Matrix-Bernstein reduction of expected covariance error. | Faithful. |
| Chapter 5 | Eq. (5.24) | FORMALIZED | PSD variance expansion/bound for covariance summands. | Faithful. |
| Chapter 5 | Eq. (5.25) | FORMALIZED | Target relative covariance error. | Faithful. |
| Chapter 5 | Eq. (5.26) | FORMALIZED | Sufficient sample-size bound. | Retains the PDF-suppressed `K^2`. |
| Chapter 5 | Eq. (5.27) | STRONGER | Effective-rank definition `tr(Sigma)/‖Sigma‖`. | Lean is zero-safe; PDF is undefined at `Sigma=0`. |
| Chapter 5 | Eq. (5.28) | FORMALIZED | Effective-rank expected covariance bound. | Faithful with nonzero/zero branch handled. |
| Chapter 5 | Eq. (5.29) | FORMALIZED | High-probability effective-rank covariance bound. | Requires `Sigma != 0`. |
| Chapter 5 | Exercise Eq. (5.30) | FORMALIZED | Unit-sphere Lipschitz observable has bounded psi2 norm. | Load-bearing Exercise 5.5. |
| Chapter 5 | Exercise Eq. (5.31) | FORMALIZED | Unit-sphere Lipschitz observable has a subgaussian tail. | Load-bearing Exercise 5.5. |
| Chapter 5 | p.142 before §5.1.2 | FORMALIZED | Lipschitz implies uniformly continuous; a uniformly bounded derivative on a convex domain implies Lipschitz. | PDF's unconditional global “differentiable implies Lipschitz” is false; Lean formalizes the valid corrected statement. |
| Chapter 5 | p.157, Haar discussion | FORMALIZED | The Gaussian polar factor is Haar on `O(n)`, and a determinant correction gives Haar on `SO(n)`. | Corrects a false PDF claim. |
| Chapter 5 | p.157, Grassmann discussion | FORMALIZED | `G_{n,1}` is the antipodal/projective quotient of the sphere, and random subspaces are projection orbits. | Corrects the PDF's literal identification `G_{n,1}=S^{n-1}` and incomplete stabilizer. |
| Chapter 5 | pp.168--170, sparse SBM proof | FORMALIZED | `A=D+R`, coordinate-square/variance identities, exact eigengap, and Davis--Kahan-to-misclassification chain. | Lean fixes hidden constants, ties, and sign invariance. |
| Chapter 5 | pp.170--172, covariance proof | FORMALIZED | Population/sample second moments, matrix variance, energy bound, and effective/stable-rank identities. | Zero matrix and rectangular indexing corrected. |
| Chapter 5 | Exercise 5.1 | FORMALIZED | Lipschitz maps are uniformly continuous; bounded derivatives imply Lipschitzness. | Corrects the false global differentiability claim; construction-only subparts are out of scope. |
| Chapter 5 | Exercise 5.3 | FORMALIZED | Exponentially small spherical sets have dramatic blow-up. | Faithful corrected ranges. |
| Chapter 5 | Exercise 5.4 | FORMALIZED | Sphere concentration also holds for geodesic distance. | Faithful. |
| Chapter 5 | Exercise 5.5 | FORMALIZED | Unit-sphere psi2/tail concentration, used in random projections and Chapter 7. | Equations (5.30)--(5.31). |
| Chapter 5 | Exercise 5.6 | FORMALIZED | Mean- and median-centered psi2 norms control each other. | Requires a supplied `IsMedian`; existence is independently formalized by `exists_measureMedian` and `exists_isMedian`. |
| Chapter 5 | Exercise 5.7 | FORMALIZED | Distance-to-set is Lipschitz, turning function concentration into set blow-up. | Provides the appendix-free proof route. |
| Chapter 5 | Exercise 5.8 | FORMALIZED | Gaussian Lipschitz concentration. | Promoted source proof of Theorem 5.2.3. |
| Chapter 5 | Exercise 5.9 | FORMALIZED | Expected maximum of finitely many Gaussian coordinates/variables. | Part (b) is later Theorem 7.1.11. |
| Chapter 5 | Exercise 5.10 | FORMALIZED | `L^p` deviations follow from subgaussian concentration. | `p>=1`/`MemLp` explicit. |
| Chapter 5 | Exercise 5.11 | FORMALIZED | Gaussian CDF sends Gaussian coordinates to uniform cube coordinates. | Faithful. |
| Chapter 5 | Exercise 5.12 | FORMALIZED | Transport from Gaussian space proves continuous-cube concentration. | Faithful. |
| Chapter 5 | Exercise 5.13 | FORMALIZED | Radial transport proves concentration on `sqrt n B_2^n`. | PDF scale/value-at-zero ambiguity corrected. |
| Chapter 5 | Exercise 5.14 | FORMALIZED | Subgaussian/Rademacher random matrices give a JL embedding. | Isotropy, independence, and `K^4` dependence explicit. |
| Chapter 5 | Exercise 5.15 | FORMALIZED | Volumetric packing proves the nonlinear JL dimension lower bound. | Target dimension notation corrected. |
| Chapter 5 | Exercise 5.16 | FORMALIZED | Polynomial/power-series matrix functional calculus. | Adds the missing constant term and convergence/spectral radius hypotheses. |
| Chapter 5 | Exercise 5.17 | FORMALIZED | Commuting symmetric matrices preserve scalar functional-calculus order. | The main-text noncommuting negative claim is independently formalized by an explicit positive-semidefinite `2×2` square-function counterexample. |
| Chapter 5 | Exercise 5.18 | FORMALIZED | Inverse antitonicity and logarithm monotonicity. | Works on positive definite matrices/`x>0`. |
| Chapter 5 | Exercise 5.19 | FORMALIZED | Commuting matrix exponentials multiply. | The main-text noncommuting witness is independently formalized with explicit symmetric `2×2` matrices and computed exponentials. |
| Chapter 5 | Exercise 5.20 | FORMALIZED | Expected matrix-Bernstein norm bound. | Equation (5.18), used by Chapters 5--6. |
| Chapter 5 | Exercise 5.21 | FORMALIZED | Matrix Hoeffding. | Numbered as Theorem 5.4.13. |
| Chapter 5 | Exercise 5.22 | FORMALIZED | Matrix Khintchine for all moments `p>=1`. | Numbered as Theorem 5.4.14; used in Chapter 6. |
| Chapter 5 | Exercise 5.23 | FORMALIZED | Rectangular matrix Bernstein via Hermitian dilation. | Faithful corrected dimensions. |
| Chapter 5 | Exercise 5.24 | FORMALIZED | Rectangular matrix Khintchine via Hermitian dilation. | Faithful corrected dimensions. |
| Chapter 5 | Exercise 5.26 | FORMALIZED | High-probability effective-rank covariance estimation. | Used in Chapter 9. |
| Chapter 5 | Exercise 5.27 | FORMALIZED | Rare-atom distributions show boundedness cannot simply be dropped. | Precise quantified impossibility theorem. |
| Chapter 5 | Exercise 5.28 | FORMALIZED | Coupon-collector examples force logarithmic sample complexity. | Hint's sample index corrected from `n` to `m`. |
| Chapter 5 | Exercise 5.29 | FORMALIZED | Effective/stable-rank algebra, examples, continuity, and support rank. | Zero/rectangular issues corrected. |
| Chapter 6 | Theorem 6.1.1 | FORMALIZED | Decoupling bounds a diagonal-free quadratic chaos by a bilinear form with an independent copy, up to factor four under convex transforms. | PDF writes ordinary expectations for arbitrary convex `F`; Lean adds measurability/integrability or uses an extended nonnegative integral. |
| Chapter 6 | Remark 6.1.2 | FORMALIZED | For a general matrix, the same bound holds for the off-diagonal part on the left and all entries on the decoupled right. | Faithful corrected analytic hypotheses. |
| Chapter 6 | Proposition 6.2.1 | FORMALIZED | The norm of a subgaussian random vector concentrates around `sqrt n` with a subgaussian tail. | PDF permits `K=0` with a non-strict event, yielding a false edge case; Lean requires `K>0` and positive dimension. |
| Chapter 6 | Theorem 6.2.2 | FORMALIZED | Hanson--Wright controls centered quadratic-form deviations in Frobenius and operator-norm regimes. | Explicit absolute constant, nonempty dimension, `K>0`, and zero-matrix branches. |
| Chapter 6 | Lemma 6.2.3 | FORMALIZED | A subgaussian bilinear MGF is bounded by a Gaussian replacement MGF. | Separate probability spaces/extended MGFs make independence and finiteness legal. |
| Chapter 6 | Lemma 6.2.4 | FORMALIZED | The MGF of an independent Gaussian bilinear form is bounded by `exp(C lambda^2 ‖A‖_F^2)` in the operator-norm range. | PDF calls it a quadratic form and divides by `‖A‖`; Lean states the bilinear object and a denominator-free range, with a guarded printed wrapper. |
| Chapter 6 | Lemma 6.3.1 | FORMALIZED | Multiplying by an independent Rademacher sign, applying odd maps, and subtracting an independent copy construct symmetric laws. | Exercise 6.16 payload is promoted and fully proved. |
| Chapter 6 | Lemma 6.3.2 | FORMALIZED | Rademacher symmetrization compares expected norm of a centered sum and its signed version within factors two. | Bochner integrability and sign/vector independence explicit. |
| Chapter 6 | Theorem 6.4.1 | FORMALIZED | A symmetric random matrix with independent centered entries has expected norm controlled by a logarithmic factor times maximal row energy. | PDF's `sqrt(log n)` is false at `n=1`; Lean uses the safe `sqrt(2 log(2n))` scale. Its proof also corrects the false prose claim that `Z_ij` itself is diagonal. |
| Chapter 6 | Theorem 6.5.1 | FORMALIZED | Bernoulli matrix completion recovers a rank-`r` matrix in expected normalized Frobenius error at the stated sample scale. | PDF inherits the observation model, `p=m/n^2`, rank range, and “best” norm from prior prose; Lean binds a complete model/certificate and `n>=2`. |
| Chapter 6 | Theorem 6.6.1 | FORMALIZED | Rademacher contraction bounds coefficient-weighted random sums by the sup coefficient times the unweighted sum. | Faithful. |
| Chapter 6 | Lemma 6.6.2 | FORMALIZED | Gaussian symmetrization compares expected norms of a centered sum with a Gaussian-signed sum, losing `sqrt(log N)`. | Safe API uses `log(2N)`; source-shaped wrapper assumes `N>=2`, since the PDF formula is false/undefined at `N=1`. |
| Chapter 6 | Remark 6.6.3 | FORMALIZED | The `sqrt(log N)` loss in Gaussian symmetrization is unavoidable in general. | Precise coordinate witness formalizes the otherwise vague Exercise 6.37 prompt. |
| Chapter 6 | Eq. (6.1) | STRONGER | Finite linear random sum `sum_i a_i X_i`. | No chapter-specific wrapper is needed; Lean's finite-sum API is more general. |
| Chapter 6 | Eq. (6.2) | FORMALIZED | Quadratic form equals its double coordinate sum and inner-product form. | Faithful. |
| Chapter 6 | Eq. (6.3) | FORMALIZED | Main decoupling inequality. | Analytic hypotheses explicit. |
| Chapter 6 | Eq. (6.4) | FORMALIZED | Partial decoupled chaos is bounded by the full bilinear chaos. | Faithful. |
| Chapter 6 | Eq. (6.5) | FORMALIZED | Arbitrary-matrix off-diagonal decoupling. | Faithful. |
| Chapter 6 | Eq. (6.6) | FORMALIZED | Exponential Markov step for the random-vector norm. | Proof-local. |
| Chapter 6 | Eq. (6.7) | FORMALIZED | Gaussian-mixture representation bounds the norm-square exponential. | Proof-local. |
| Chapter 6 | Eq. (6.8) | FORMALIZED | Exchange of Gaussian/vector expectations by Tonelli/Fubini. | Integrability/nonnegative integral legality explicit. |
| Chapter 6 | Eq. (6.9) | FORMALIZED | Conditional subgaussian MGF is bounded by a Gaussian MGF. | Faithful. |
| Chapter 6 | Eq. (6.10) | FORMALIZED | Exact MGF of a standard-Gaussian inner product. | Faithful. |
| Chapter 6 | Eq. (6.11) | FORMALIZED | Gaussian bilinear MGF factors over singular values. | Faithful with denominator-free range. |
| Chapter 6 | Eq. (6.12) | FORMALIZED | Off-diagonal Hanson--Wright exponential-Markov bound. | Faithful. |
| Chapter 6 | Eq. (6.13) | FORMALIZED | Adding an independent centered perturbation cannot reduce expected norm. | Faithful. |
| Chapter 6 | Eq. (6.14) | FORMALIZED | Entrywise symmetrization of a symmetric random matrix. | Proof-local chain checked. |
| Chapter 6 | Eq. (6.15) | FORMALIZED | Conditional matrix Khintchine for the symmetrized coordinate matrices. | Faithful. |
| Chapter 6 | Eq. (6.16) | FORMALIZED | Matrix-completion sampling probability `p=m/n^2`. | Lean also guards `0<p<1`/dimensions. |
| Chapter 6 | Eq. (6.17) | FORMALIZED | Best-approximation operator error is at most twice the proxy error. | Faithful. |
| Chapter 6 | Eq. (6.18) | FORMALIZED | Rectangular independent-entry norm is controlled by expected maximal row/column energy. | The main-text equation is correct; Exercise 6.28's restatement omits an expectation and is corrected in Lean. |
| Chapter 6 | Eq. (6.19) | FORMALIZED | Expected centered sampling operator norm/error bound. | Faithful. |
| Chapter 6 | Eq. (6.20) | FORMALIZED | Contraction functional `f(a)=E‖sum a_i epsilon_i x_i‖`. | Faithful. |
| Chapter 6 | p.181 after (6.2) | FORMALIZED | Independent centered unit-variance coordinates satisfy `E[X^TAX]=tr A`. | Hidden square-integrability assumptions explicit. |
| Chapter 6 | pp.181--183, decoupling proof | FORMALIZED | Selector averaging, existence of a favorable split, and independent-copy replacement produce the factor four. | Ordinary-integral and `lintegral` variants distinguish finiteness. |
| Chapter 6 | pp.186--187, Hanson--Wright proof | FORMALIZED | Centered quadratic form splits into diagonal and off-diagonal pieces; Bernstein handles the first and decoupling/Gaussian replacement the second. | Faithful. |
| Chapter 6 | p.190, random-matrix proof | FORMALIZED | Coordinate matrix `Z_ij` need not be diagonal, but `Z_ij^2` is diagonal and sums to row-energy data. | Direct correction of a false PDF prose sentence (“each `Z_ij` is diagonal”). |
| Chapter 6 | pp.190--192, completion proof | FORMALIZED | Bernoulli observation model, proxy error, rank-to-Frobenius transfer, and normalized error algebra. | Lean binds all inherited hypotheses. |
| Chapter 6 | p.194 in Lemma 6.6.2 proof | FORMALIZED | Expected maximum of `N` standard Gaussians is `O(sqrt(log N))`. | Literal `sqrt(log N)` is false at `N=1`; source wrapper requires `N>=2` and safe API uses `log(2N)`. |
| Chapter 6 | Exercise 6.1 | FORMALIZED | Off-diagonal version of decoupling for an arbitrary matrix. | Proves Remark 6.1.2 / equation (6.5). |
| Chapter 6 | Exercise 6.16 | FORMALIZED | Three constructions of symmetric distributions. | Promoted proof of Lemma 6.3.1. |
| Chapter 6 | Exercise 6.28 | FORMALIZED | Rectangular random-matrix norm via maximal row/column norms. | PDF exercise omits expectation on the random RHS and conflates row/column indices; Lean proves the corrected theorem used in matrix completion. |
| Chapter 6 | Exercise 6.30 | FORMALIZED | Expected maximum Bernoulli row energy. | Uses safe logarithmic/dimension assumptions. |
| Chapter 6 | Exercise 6.33 | FORMALIZED | Matrix Bernstein extension for independent unbounded random matrices. | Uses safe `log(2n)`/nonempty guards. |
| Chapter 6 | Exercise 6.34 | FORMALIZED | Covariance estimation for unbounded distributions under a maximal-sample-energy condition. | PDF writes `max_i ‖X‖^2` before introducing copies and has zero-rank/log edge cases; Lean quantifies iid copies and uses zero-safe effective rank. |
| Chapter 6 | Exercise 6.35 | FORMALIZED | The Rademacher-series coefficient functional is convex. | Used directly in Theorem 6.6.1. |
| Chapter 6 | Exercise 6.37 | FORMALIZED | Coordinate-vector witness shows Gaussian-symmetrization's logarithmic loss is optimal. | PDF prompt is vague; the precise witness proves its claimed optimality and supports Remark 6.6.3. |
| Chapter 7 | Definition 7.1.1 | FORMALIZED | A random process is a family of random variables on one probability space, indexed by a set. | Exact typed definition. |
| Chapter 7 | Remark 7.1.7 | FORMALIZED | `L2` increments obey zero, symmetry, and the triangle inequality. | Lean correctly says pseudometric. The PDF main sentence says metric, while its footnote supplies the necessary correction. |
| Chapter 7 | Remark 7.1.8 | FORMALIZED | Squared increments equal `Sigma(t,t)-2 Sigma(t,s)+Sigma(s,s)`; with a zero coordinate, increments recover covariance. | Explicit `L2`/centering hypotheses make the informal moments well-defined. |
| Chapter 7 | Definition 7.1.9 | FORMALIZED | A Gaussian process has jointly Gaussian restriction to every finite index set; equivalently every finite linear combination is Gaussian. | Exact finite-dimensional characterization. |
| Chapter 7 | Remark 7.1.10 | FORMALIZED | Mean and covariance determine a Gaussian process in law; with a zero coordinate, increments determine it too. | Finite-dimensional equality-in-law is the rigorous content of process-law equality. |
| Chapter 7 | Lemma 7.1.12 | FORMALIZED | Every centered Gaussian vector is equal in law to inner products of one standard Gaussian vector with deterministic points. | Singular covariance is allowed. |
| Chapter 7 | Remark 7.2.1 | FORMALIZED | For arbitrary index sets, expected suprema are interpreted as suprema of finite-subset expected maxima. | Lean uses an extended-real arbitrary-index interface, avoiding hidden finiteness. |
| Chapter 7 | Theorem 7.2.2 | FORMALIZED | Slepian: equal variances plus dominated increments imply stochastic and expected-max domination. | Lean correctly quantifies the tail threshold over all real numbers; the later finite-vector restatement's `tau>=0` is a PDF inconsistency. |
| Chapter 7 | Lemma 7.2.3 | FORMALIZED | Scalar Gaussian integration by parts: `E[X f(X)] = E[f'(X)]`. | Lean adds the analytic regularity and integrability actually needed by the identity. |
| Chapter 7 | Lemma 7.2.4 | FORMALIZED | Multivariate Gaussian integration by parts contracts covariance with the gradient. | Correct compact-support/regularity form, including singular covariance. |
| Chapter 7 | Lemma 7.2.5 | FORMALIZED | The derivative of an interpolated Gaussian expectation is one half the covariance difference contracted with the expected Hessian. | Lean restricts differentiation to `0<u<1` and exposes domination; the PDF statement includes endpoints despite dividing by square roots. |
| Chapter 7 | Lemma 7.2.6 | FORMALIZED | A function with nonpositive mixed Hessian entries yields the functional Slepian comparison. | Smoothing and dominated convergence are explicit in the verified proof. |
| Chapter 7 | Theorem 7.2.7 | FORMALIZED | Finite-vector Slepian stochastic and expectation comparison. | Lean uses the correct all-real threshold, strengthening the PDF's internally inconsistent `tau>=0` restatement. |
| Chapter 7 | Theorem 7.2.8 | FORMALIZED | Sudakov--Fernique: increment domination implies expected-supremum domination. | Finite-index proof matches the chapter's stated finite-subset convention. |
| Chapter 7 | Theorem 7.2.9 | FORMALIZED | Gordon min-max comparison for Gaussian processes. | The PDF tail statement is false without equal coordinate variances. Lean splits the valid expectation theorem from the tail theorem with the missing equal-variance assumption. |
| Chapter 7 | Theorem 7.3.1 | FORMALIZED | An iid standard Gaussian `m x n` matrix has expected operator norm at most `sqrt m + sqrt n`. | Exact sharp-constant conclusion, with positive/nonempty dimension guards. |
| Chapter 7 | Corollary 7.3.2 | FORMALIZED | The Gaussian matrix norm has Gaussian upper tails around `sqrt m + sqrt n`. | Exact typed tail event. |
| Chapter 7 | Theorem 7.4.1 | FORMALIZED | Sudakov lower-bounds a Gaussian expected supremum by `epsilon sqrt(log covering-number)`. | Lean correctly requires `epsilon>0`; the PDF's `epsilon>=0` creates an unsafe `0 sqrt(log infinity)` corner. |
| Chapter 7 | Corollary 7.4.2 | FORMALIZED | Euclidean Gaussian width dominates every Sudakov covering scale. | Canonical-process specialization. |
| Chapter 7 | Corollary 7.4.3 | FORMALIZED | A polytope with `N` vertices has logarithmic covering-number bound controlled by its diameter and `log N`. | Safe cardinal/log casts are explicit. |
| Chapter 7 | Definition 7.5.1 | FORMALIZED | Gaussian width is the expected support of a set in a standard Gaussian direction. | Chapter 7's real API is finite; the later extended arbitrary-set API supplies the printed scope safely. |
| Chapter 7 | Proposition 7.5.2 | FORMALIZED | Gaussian width is finite exactly on bounded sets and satisfies translation, orthogonal, convex-hull, Minkowski-sum, scaling, symmetrization, two-sided diameter, and linear-image laws. | The authoritative finite-subfamily envelope gives genuine arbitrary-set ENNReal statements and bounded safe-real wrappers; 24 public endpoints were axiom-audited. |
| Chapter 7 | Remark 7.5.3 | FORMALIZED | The width/diameter constants are optimal, witnessed by a symmetric pair and Euclidean balls. | Both witness families requested by the source are proved. |
| Chapter 7 | Definition 7.5.4 | FORMALIZED | Spherical width is average support over a uniform unit-sphere direction. | Positive ambient dimension is explicit; later set API supplies arbitrary bounded-set scope. |
| Chapter 7 | Lemma 7.5.5 | FORMALIZED | Gaussian width equals mean Gaussian radius times spherical width, so the two differ by a `sqrt n` factor. | Exact finite polar factorization with explicit dimension guard. |
| Chapter 7 | Example 7.5.6 | FORMALIZED | The Euclidean unit ball and sphere have Gaussian width comparable to `sqrt n`. | The actual support integral is encoded by a safe proxy; constants are explicit. |
| Chapter 7 | Example 7.5.7 | FORMALIZED | The cube has Gaussian width exactly `sqrt(2/pi) n`. | Exact source normalization. |
| Chapter 7 | Example 7.5.9 | FORMALIZED | A finite point set has Gaussian width at most a universal constant times diameter times `sqrt(log cardinality)`. | The normalized theorem plus proved algebraic laws yields the printed form. |
| Chapter 7 | Lemma 7.5.11 | FORMALIZED | Gaussian width, Gaussian complexity, and the `L2`-supremum variant are equivalent up to universal constants. | Translation/concentration proof is explicit. |
| Chapter 7 | Definition 7.5.12 | FORMALIZED | Effective dimension is width-squared divided by diameter-squared and is bounded by affine dimension. | Lean uses a documented zero-diameter value; the printed quotient is undefined there. |
| Chapter 7 | Theorem 7.6.1 | FORMALIZED | Expected diameter of a random `m`-dimensional projection is comparable to spherical width plus `sqrt(m/n)` times diameter. | Lean fixes the PDF's row/column dimension mistake and requires `0<n`, `1<=m<=n`; expectation remains present. |
| Chapter 7 | Remark 7.6.2 | FORMALIZED | Random-projection diameter has a width-dominated/diameter-dominated phase transition. | Lean keeps the expectation that the PDF's final display accidentally drops. |
| Chapter 7 | Eq. (7.1) | FORMALIZED | Canonical `L2` increment distance. | It is a pseudometric unless indices are separated. |
| Chapter 7 | Eq. (7.2) | FORMALIZED | Canonical Gaussian process `X_t=<g,t>`. | Exact. |
| Chapter 7 | Eq. (7.3) | FORMALIZED | Slepian equal-variance and increment-domination assumptions. | Exact. |
| Chapter 7 | Eq. (7.4) | FORMALIZED | Slepian stochastic domination of suprema. | Lean correctly handles all real thresholds. |
| Chapter 7 | Eq. (7.5) | FORMALIZED | Slepian expected-supremum comparison. | Exact with integrability. |
| Chapter 7 | Eq. (7.6) | FORMALIZED | Whole-line scalar Gaussian integration-by-parts calculation. | Proof-local; analytic boundary conditions are explicit. |
| Chapter 7 | Eq. (7.7) | FORMALIZED | Multivariate Gaussian integration-by-parts identity. | Exact corrected analytic form. |
| Chapter 7 | Eq. (7.8) | FORMALIZED | Interpolation `sqrt(u)X+sqrt(1-u)Y`. | Exact. |
| Chapter 7 | Eq. (7.9) | FORMALIZED | Derivative of the expected interpolated test function. | Valid on the interior; endpoint passage is separate. |
| Chapter 7 | Eq. (7.10) | FORMALIZED | First chain-rule expansion in Gaussian interpolation. | Proof-local. |
| Chapter 7 | Eq. (7.11) | FORMALIZED | Integration-by-parts evaluation of the `X_i` contribution. | Proof-local. |
| Chapter 7 | Eq. (7.12) | FORMALIZED | Log-sum-exp smooth maximum. | No redundant public definition; verified inside the theorem. |
| Chapter 7 | Eq. (7.13) | FORMALIZED | Canonical metric restated through covariance. | Exact under `L2`/centering. |
| Chapter 7 | Eq. (7.14) | FORMALIZED | Expected supremum of a Gaussian process. | Extended form handles arbitrary indices. |
| Chapter 7 | Eq. (7.15) | FORMALIZED | Gaussian maximum over polytope vertices controls entropy. | Encoded in the corollary proof. |
| Chapter 7 | Eq. (7.16) | FORMALIZED | Width is the mean directional width of the difference set. | Finite-set safe form. |
| Chapter 7 | Eq. (7.17) | FORMALIZED | Ball/sphere width equals `E ‖g‖` and is `sqrt n` up to constants. | Explicit dimension guard. |
| Chapter 7 | Eq. (7.18) | FORMALIZED | Cube width is `sqrt(2/pi)n`. | Exact. |
| Chapter 7 | Eq. (7.20) | FORMALIZED | Johnson--Lindenstrauss projection scales diameter by `sqrt(m/n)`. | Contextual citation to an earlier proved theorem. |
| Chapter 7 | Eq. (7.22) | FORMALIZED | A quarter-net reduces projected diameter to finitely many support values. | Proof-local. |
| Chapter 7 | Eq. (7.23) | FORMALIZED | Fixed-direction projected support is a spherical/Gaussian support variable. | Proof-local. |
| Chapter 7 | Eq. (7.24) | FORMALIZED | Union-bound tail over the projection net. | Lean retains the leading factor `2`; the PDF's following unnumbered simplification drops it without justification. |
| Chapter 7 | Eq. (7.25), Exercise 7.3 | FORMALIZED | Talagrand contraction for Rademacher processes. | Load-bearing exercise equation, finite nonempty form. |
| Chapter 7 | Exercise 7.1(a) | FORMALIZED | A zero coordinate lets one recover covariance from increments. | Used by Remark 7.1.8. |
| Chapter 7 | Exercise 7.3 | FORMALIZED | Talagrand contraction for finite random processes. | Eq. (7.25) captured. |
| Chapter 7 | Exercise 7.6 | FORMALIZED | Prove multivariate Gaussian integration by parts. | Promoted proof of Lemma 7.2.4. |
| Chapter 7 | Exercise 7.7 | FORMALIZED | Differentiate log-sum-exp under interpolation to prove Sudakov--Fernique. | Promoted proof step. |
| Chapter 7 | Exercise 7.9 | FORMALIZED | Gordon comparison with equal variances. | Equal variance is essential for the tail half; the PDF's suggestion it can be dropped is false. |
| Chapter 7 | Exercise 7.10 | FORMALIZED | Frobenius distance identity for rank-one tensors used in the Gaussian matrix comparison. | PDF ambient dimensions are mistyped; Lean uses the dimensionally correct spaces. |
| Chapter 7 | Exercise 7.12 | FORMALIZED | The Gaussian radial-mean correction is eventually monotone in natural dimension. | PDF malformed a dimension-indexed sequence as a real-variable function. |
| Chapter 7 | Exercise 7.14 | FORMALIZED | A non-relatively-compact index set has divergent finite-subset Gaussian maxima. | Extended-real formulation fixes the PDF's ordinary-real infinity. |
| Chapter 7 | Exercise 7.15 | FORMALIZED | Prove all algebraic properties of Gaussian width. | Finite-safe forms. |
| Chapter 7 | Exercise 7.16 | FORMALIZED | Exhibit sharpness witnesses for the width/diameter bounds. | Supports numbered Remark 7.5.3. |
| Chapter 7 | Exercise 7.17 | FORMALIZED | Width of `ell_p` balls. | Lean correctly assumes `n>=2` for logarithmic endpoints. |
| Chapter 7 | Exercise 7.18 | FORMALIZED | Nuclear/operator duality and the nuclear norm laws. | Exact promoted core result. |
| Chapter 7 | Exercise 7.20 | FORMALIZED | Compare Gaussian width with Gaussian complexity. | Used by Lemma 7.5.11. |
| Chapter 7 | Exercise 7.21 | FORMALIZED | Effective dimension is at most affine dimension and equals dimension for Euclidean balls. | Zero-diameter convention is explicit. |
| Chapter 7 | Exercise 7.24 | FORMALIZED | Haar orbit of a fixed unit vector is uniform on the sphere. | Corrects the main proof's row/column mismatch. |
| Chapter 7 | Exercise 7.25 | FORMALIZED | Gaussian projection analogue of the projection-diameter theorem. | Positive projection dimension is explicit. |
| Chapter 7 | Exercise 7.26 | FORMALIZED | Matching lower bound for expected random-projection diameter. | Combined with the core upper bound in Theorem 7.6.1. |
| Chapter 7 | Sec. 7.1.1, covariance display | FORMALIZED | The covariance function is `E[X_t X_s]` for centered processes. | Typed definition with moment assumptions downstream. |
| Chapter 7 | Sec. 7.1.2 after (7.2) | FORMALIZED | Canonical Gaussian-process increments equal Euclidean distance. | Exact. |
| Chapter 7 | Sec. 7.1.2 conclusion | FORMALIZED | Every finite-dimensional marginal of a Gaussian process admits a canonical Euclidean representation. | Equality in law, including singular covariance. |
| Chapter 7 | Sec. 7.6 proof after (7.24) | FORMALIZED | The net-union probability can be simplified to a pure exponential tail. | PDF drops a leading factor `2`; Lean keeps a valid constant/exponent form. |
| Chapter 8 | Definition 8.1.1 | FORMALIZED | A process has subgaussian increments when every increment has `psi2` norm at most `K` times the index distance. | Exact explicit-constant and existential forms. |
| Chapter 8 | Theorem 8.1.3 | FORMALIZED | Dudley bounds the expected supremum of a centered subgaussian-increment process by the entropy integral. | Finite proof engine matches the chapter's explicit finite-set convention; Theorem 8.1.8 supplies the arbitrary Euclidean-set wrapper. |
| Chapter 8 | Theorem 8.1.4 | FORMALIZED | Discrete Dudley bounds the expected supremum by a dyadic entropy sum. | Exact finite source form. |
| Chapter 8 | Remark 8.1.5 | FORMALIZED | Dudley also bounds anchored and pairwise suprema of increments without centering. | Both printed variants are explicit. |
| Chapter 8 | Remark 8.1.6 | FORMALIZED | Dudley admits a high-probability bound with an added `u diam(T)` term. | Fully quantified finite form. |
| Chapter 8 | Remark 8.1.7 | FORMALIZED | The entropy integral can be truncated at the diameter because larger balls cover the set singly. | Exact. |
| Chapter 8 | Theorem 8.1.8 | FORMALIZED | Arbitrary bounded Euclidean-set Gaussian width is bounded by its Dudley entropy integral. | Extended-real interface precedes safe real conversion; no finite-cloud weakening. |
| Chapter 8 | Example 8.1.9 | STRONGER | Dudley is sharp on the Euclidean ball at scale `sqrt n`. | Lean supplies an explicit upper constant and the sharp radial lower scale. |
| Chapter 8 | Remark 8.1.10 | FORMALIZED | Dudley can overestimate width, but by at most a logarithmic factor; a weighted-basis family exhibits divergence of the entropy integral with bounded width. | The logarithmic comparison correctly assumes `n>=2`. |
| Chapter 8 | Remark 8.2.1 | STRONGER | Monte Carlo sample-mean expected absolute error is at most standard deviation divided by `sqrt n`. | Constant one; pairwise independence suffices. |
| Chapter 8 | Remark 8.2.2 | FORMALIZED | The Monte Carlo rate is dimension-free. | Arbitrary observation space makes the dimension independence literal. |
| Chapter 8 | Theorem 8.2.3 | FORMALIZED | Uniform law of large numbers for all `L`-Lipschitz functions on `[0,1]`, at rate `L/sqrt n`. | Source-general arbitrary class; normalization/anchoring is proved, not assumed. |
| Chapter 8 | Definition 8.2.5 | FORMALIZED | The empirical process is the centered normalized sample average indexed by a function class. | Exact typed definition. |
| Chapter 8 | Definition 8.3.1 | FORMALIZED | VC dimension is the largest size of a shattered subset, with an infinite case. | Arbitrary-class bound avoids silently coercing infinite VC dimension to a natural. |
| Chapter 8 | Example 8.3.2 | FORMALIZED | Indicators of real intervals have VC dimension two. | Full interval class, not just one witness. |
| Chapter 8 | Example 8.3.3 | FORMALIZED | Affine half-planes in `R^2` have VC dimension three. | Includes degenerate configurations through the general theorem. |
| Chapter 8 | Example 8.3.4 | FORMALIZED | The four strings `001,010,100,111` have VC dimension two. | Exact finite example. |
| Chapter 8 | Example 8.3.5 | FORMALIZED | Affine half-spaces in `R^n` have VC dimension `n+1`. | Full infinite Euclidean class. |
| Chapter 8 | Remark 8.3.6 | FORMALIZED | Affine half-spaces in `R^n` have VC dimension `n+1`, matching their parameter count. | The general claim is explicitly only a heuristic; Lean proves the stated half-space evidence. |
| Chapter 8 | Lemma 8.3.7 | FORMALIZED | Pajor: a finite Boolean family has at least as many shattered subsets as functions. | Exact. |
| Chapter 8 | Example 8.3.8 | FORMALIZED | Applying Pajor's splitting to the four-string class yields seven shattered subsets. | PDF says six after listing empty set, three singletons, and three pairs; Lean correctly proves seven. |
| Chapter 8 | Lemma 8.3.9 | FORMALIZED | Sauer--Shelah bounds a class by the binomial sum up to its VC dimension. | Zero-VC case is split safely. |
| Chapter 8 | Definition 8.3.10 | FORMALIZED | The growth function is the largest trace-cardinality on an `n`-point sample. | Exact finite and arbitrary-class interfaces. |
| Chapter 8 | Proposition 8.3.11 | FORMALIZED | VC dimension is stable under conjunction and disjunction, with universal-multiple bounds. | Exact up to the source's absolute-constant notation. |
| Chapter 8 | Example 8.3.12 | FORMALIZED | Euclidean strips have controlled VC dimension as intersections of two half-spaces. | Full strip class plus finite stability bridge. |
| Chapter 8 | Theorem 8.3.13 | FORMALIZED | An arbitrary measurable Boolean class with VC dimension `d` has polynomial `L2` covering numbers. | Positivity, measurability, probability measure, and `ENNReal` casts are explicit. |
| Chapter 8 | Lemma 8.3.14 | FORMALIZED | Empirical `L2` distances preserve a finite separated family with positive probability when sample size is large enough. | Exact finite-class probability statement. |
| Chapter 8 | Theorem 8.3.15 | FORMALIZED | A Boolean class of VC dimension `d` has expected uniform empirical deviation `O(sqrt(d/n))`. | Arbitrary measurable class via explicit exhaustion. |
| Chapter 8 | Remark 8.3.16 | FORMALIZED | Rademacher complexity controls the empirical deviation and has the same VC rate. | Measurability is finite/exhaustion-based. |
| Chapter 8 | Theorem 8.3.17 | FORMALIZED | Glivenko--Cantelli: the empirical CDF converges uniformly at rate `1/sqrt n`. | Exact real-line arbitrary-law endpoint. |
| Chapter 8 | Example 8.3.18 | FORMALIZED | A random sample gives low discrepancy for a finite range space of small VC dimension. | Finite range-space source form. |
| Chapter 8 | Remark 8.3.19 | STRONGER | Finite VC dimension yields a uniform Glivenko--Cantelli class; infinite VC dimension obstructs uniform convergence. | Lean proves both directions, including the converse delegated to Exercise 8.28. |
| Chapter 8 | Example 8.4.1 | FORMALIZED | Statistical classification is learning a Boolean target from labeled iid data. | Typed setup rather than a vacuous proposition. |
| Chapter 8 | Example 8.4.2 | FORMALIZED | Boolean squared loss equals misclassification probability/symmetric-difference loss. | Exact. |
| Chapter 8 | Definition 8.4.3 | FORMALIZED | ERM minimizes empirical squared loss, and population risk has a minimizer only when attainment is supplied/proved. | Fixes the PDF's unguarded arbitrary-class `argmin`. |
| Chapter 8 | Example 8.4.4 | FORMALIZED | In classification, empirical risk is the empirical misclassification rate. | Exact. |
| Chapter 8 | Theorem 8.4.5 | FORMALIZED | VC generalization bound controls expected excess risk by `sqrt(vc/n)`. | Arbitrary measurable loss class with explicit minimizers/exhaustion. |
| Chapter 8 | Example 8.4.6 | FORMALIZED | The classification loss class has the same VC dimension as the hypothesis class, giving the classification specialization. | Exact source specialization. |
| Chapter 8 | Remark 8.4.7 | FORMALIZED | Increasing model complexity reduces approximation bias but increases the VC estimation term. | Formal finite nested-class risk inequality captures the mathematical content. |
| Chapter 8 | Definition 8.5.1 | FORMALIZED | `gamma2` is the infimum, over admissible chains, of the worst weighted multiscale approximation cost. | `ENNReal` codomain handles divergence; finite proof setting matches the proof's explicit reduction. |
| Chapter 8 | Theorem 8.5.2 | FORMALIZED | Generic chaining bounds the expected supremum by `C K gamma2`. | Finite source form; zero-`gamma2` and pseudometric terminal-level cases are repaired. |
| Chapter 8 | Remark 8.5.3 | FORMALIZED | Generic chaining bounds pairwise increment suprema without centering. | Exact finite form. |
| Chapter 8 | Remark 8.5.4 | FORMALIZED | Generic chaining has a high-probability `gamma2 + u diam` bound. | The PDF delegates the proof to load-bearing Exercise 8.35. |
| Chapter 8 | Remark 8.5.7 | FORMALIZED | For two Gaussian processes, Talagrand comparison reduces to Sudakov--Fernique with constant one. | Unconditional core proof. |
| Chapter 8 | Eq. (8.1) | FORMALIZED | `psi2` increment domination by `K d(s,t)`. | Exact. |
| Chapter 8 | Eq. (8.2) | FORMALIZED | Discrete dyadic Dudley sum. | Exact finite form. |
| Chapter 8 | Eq. (8.3) | FORMALIZED | Net approximation makes each process increment `K epsilon`-subgaussian. | Proof-local. |
| Chapter 8 | Eq. (8.4) | FORMALIZED | Dyadic scales `epsilon_k=2^{-k}`. | Equivalent radius-parametrized definition. |
| Chapter 8 | Eq. (8.5) | FORMALIZED | Each chain level has covering-number cardinality. | Uses actual Mathlib covering numbers. |
| Chapter 8 | Eq. (8.6) | FORMALIZED | Chaining starts at a singleton and terminates at the full finite set. | Pseudometric terminal branch is explicit. |
| Chapter 8 | Eq. (8.7) | FORMALIZED | Chosen projections are within the covering radius. | Exact. |
| Chapter 8 | Eq. (8.8) | FORMALIZED | Finite telescoping chain expansion. | Exact. |
| Chapter 8 | Eq. (8.9) | FORMALIZED | Infinite-looking telescoping sum truncates at the terminal level. | Safe finite realization. |
| Chapter 8 | Eq. (8.10) | FORMALIZED | Expected anchored supremum is bounded by the sum of expected scale suprema. | Exact. |
| Chapter 8 | Eq. (8.11) | FORMALIZED | Each scale maximum is bounded by radius times square-root log cardinality. | Exact. |
| Chapter 8 | Eq. (8.12) | FORMALIZED | Summing scale bounds gives discrete Dudley. | Exact. |
| Chapter 8 | Eq. (8.13) | FORMALIZED | Anchored absolute-increment Dudley bound. | Exact. |
| Chapter 8 | Eq. (8.14) | FORMALIZED | Pairwise-increment Dudley bound. | Exact. |
| Chapter 8 | Eq. (8.15) | FORMALIZED | High-probability Dudley bound. | Load-bearing Exercise 8.1 supplies the proof. |
| Chapter 8 | Eq. (8.16) | FORMALIZED | Dudley integral truncated at the diameter. | Exact. |
| Chapter 8 | Eq. (8.17) | FORMALIZED | Euclidean-set Gaussian width bounded by the entropy integral. | Actual bounded-set scope. |
| Chapter 8 | Eq. (8.18) | FORMALIZED | Monte Carlo sample averages converge almost surely. | Reuses the proved Chapter 1 strong law. |
| Chapter 8 | Eq. (8.19) | FORMALIZED | Monte Carlo integral is approximated by the normalized sample average. | Exact definition. |
| Chapter 8 | Eq. (8.20) | STRONGER | Expected scalar Monte Carlo error is `O(1/sqrt n)`. | Explicit constant one. |
| Chapter 8 | Eq. (8.21) | FORMALIZED | Full `L`-Lipschitz function class on `[0,1]`. | Exact typed class. |
| Chapter 8 | Eq. (8.22) | FORMALIZED | Expected uniform Lipschitz empirical error is `O(L/sqrt n)`. | Source-general endpoint. |
| Chapter 8 | Eq. (8.23) | FORMALIZED | Empirical-process coordinate `X_f`. | Exact. |
| Chapter 8 | Eq. (8.24) | FORMALIZED | Normalized `[0,1]`-valued one-Lipschitz class. | Exact. |
| Chapter 8 | Eq. (8.25) | FORMALIZED | Dudley entropy bound for the Lipschitz empirical process. | Proof-local chaining step. |
| Chapter 8 | Eq. (8.26) | FORMALIZED | Empirical measure is the normalized sum of sample Dirac masses. | Exact. |
| Chapter 8 | Eq. (8.27) | FORMALIZED | A finite Boolean family lies between `2^vc` and `2^n`. | Exact. |
| Chapter 8 | Eq. (8.28) | FORMALIZED | Pajor split families each contribute shattered sets. | Proof-local. |
| Chapter 8 | Eq. (8.29) | FORMALIZED | Shatterer count is superadditive under the Pajor split. | Proof-local. |
| Chapter 8 | Eq. (8.30) | FORMALIZED | Growth function lies between `2^d` and the Sauer--Shelah polynomial bound. | `d=0` handled separately. |
| Chapter 8 | Eq. (8.31) | FORMALIZED | Boolean `L2` distance equals square-root symmetric-difference probability. | Exact. |
| Chapter 8 | Eq. (8.32) | FORMALIZED | Empirical Boolean `L2` distance is the sample squared-difference average. | Exact. |
| Chapter 8 | Eq. (8.33) | FORMALIZED | Outside the bad event, empirical distance preserves population separation. | Exact. |
| Chapter 8 | Eq. (8.34) | FORMALIZED | Union-bound probability for simultaneous empirical distance preservation. | Exact source factor. |
| Chapter 8 | Eq. (8.35) | FORMALIZED | VC expected deviation is bounded by the empirical entropy integral. | Proof-local. |
| Chapter 8 | Eq. (8.36) | FORMALIZED | Labeled training sample `(X_i,T(X_i))`. | Typed through sample and target arguments. |
| Chapter 8 | Eq. (8.37) | FORMALIZED | Population squared prediction risk. | Exact. |
| Chapter 8 | Eq. (8.38) | FORMALIZED | For Boolean hypotheses, risk is misclassification probability. | Exact. |
| Chapter 8 | Eq. (8.39) | FORMALIZED | Empirical risk and its minimizer. | Avoids unproved arbitrary-class argmin attainment. |
| Chapter 8 | Eq. (8.40) | FORMALIZED | ERM excess risk is at most twice uniform risk deviation. | Actual arbitrary Boolean class. |
| Chapter 8 | Eq. (8.41) | FORMALIZED | VC loss-class deviation has `sqrt(vc/n)` rate. | Exact. |
| Chapter 8 | Eq. (8.42) | FORMALIZED | Dudley written as a sum over admissible scales. | Contextual restatement. |
| Chapter 8 | Eq. (8.43) | FORMALIZED | Admissible sequence cardinality bounds. | Exact finite certificate. |
| Chapter 8 | Eq. (8.44) | FORMALIZED | Dudley chain cost has supremum inside the scale sum. | Exact structural comparison. |
| Chapter 8 | Eq. (8.45) | FORMALIZED | Definition of `gamma2`. | Extended-real codomain is safer than the PDF's real notation. |
| Chapter 8 | Eq. (8.46) | FORMALIZED | Choose a chain with cost within factor two of `gamma2`. | PDF says "supremum" where it means infimum; Lean uses the infimum. |
| Chapter 8 | Eq. (8.47) | FORMALIZED | Generic-chain telescoping expansion. | Finite terminal level. |
| Chapter 8 | Eq. (8.48) | FORMALIZED | Desired simultaneous weighted increment control. | Exact event-level form. |
| Chapter 8 | Eq. (8.49) | FORMALIZED | Single-edge subgaussian tail at scale `2^{k/2}`. | Exact with explicit constants. |
| Chapter 8 | Eq. (8.50) | FORMALIZED | Summed increment control by chain cost. | Proof-local decomposition exposed by named lemmas. |
| Chapter 8 | Eq. (8.51) | FORMALIZED | Radius of a Euclidean set. | Finite and bounded arbitrary-set forms. |
| Chapter 8 | Eq. (8.52) | FORMALIZED | Chevet bilinear process has increments controlled by opposite radii. | The displayed increment estimate itself is core-proved. Theorem 8.6.1's later Talagrand-comparison step is separately classified `IN-APPENDIX`. |
| Chapter 8 | Eq. (8.53), Exercise 8.1 | FORMALIZED | Scale-by-scale high-probability Dudley bound. | Load-bearing exercise equation. |
| Chapter 8 | Exercise 8.1 | FORMALIZED | Prove the high-probability Dudley inequality. | Builds its chain automatically and handles the zero-step case. |
| Chapter 8 | Exercise 8.3 | FORMALIZED | Discrete Dudley entropy sum is equivalent to the entropy integral. | Uses actual covering numbers. |
| Chapter 8 | Exercise 8.4 | FORMALIZED | Weighted-basis set has bounded width but divergent entropy integral. | Exact two-part example. |
| Chapter 8 | Exercise 8.5 | FORMALIZED | Dudley and Sudakov functionals differ by at most `C log n`. | Corrected to `n>=2`; universal constant is chosen before the set. |
| Chapter 8 | Exercise 8.9 | FORMALIZED | Construct a small covering net for the Lipschitz class. | Supplies Theorem 8.2.3's entropy input. |
| Chapter 8 | Exercise 8.11 | FORMALIZED | Empirical symmetrization over an arbitrary Boolean class. | Absolute suprema, factor two, and exhaustion/measurability certificate are explicit. |
| Chapter 8 | Exercise 8.13 | FORMALIZED | Planar closed disks have the stated VC dimension. | Promoted source-numbered example. |
| Chapter 8 | Exercise 8.17 | FORMALIZED | Affine half-spaces in `R^n` have VC dimension `n+1`. | PDF says "half-planes" in `R^n`; Lean uses half-spaces. |
| Chapter 8 | Exercise 8.28 | FORMALIZED | Infinite VC obstructs uniform GC, and uniform GC implies finite VC. | Both directions. |
| Chapter 8 | Exercise 8.29 | FORMALIZED | Classification loss class has the same VC dimension as the hypothesis class. | Exact arbitrary-class equivalence. |
| Chapter 8 | Exercise 8.35 | FORMALIZED | High-probability generic chaining. | PDF hint's `1-exp(u^2)` sign is corrected to a decaying tail. |
| Chapter 8 | Exercise 8.36 | FORMALIZED | Generic-chaining bound for centered empirical processes. | Necessary zero-function anchor is explicit; the PDF statement is false for a nonconstant singleton class without it. |
| Chapter 8 | Sec. 8.1 after Theorem 8.1.3 | FORMALIZED | Metric entropy alone cannot close the Sudakov--Dudley gap. | Concrete counterexample formalizes the negative claim. |
| Chapter 9 | Theorem 9.1.2 | FORMALIZED | The matrix norm-deviation process has subgaussian increments. | Exact, including the degenerate and radial cases suppressed in the prose proof. |
| Chapter 9 | Example 9.4.1 | FORMALIZED | Audio sampling is a high-dimensional linear inverse problem. | Encodes the mathematical linear-observation content of the example. |
| Chapter 9 | Example 9.4.2 | FORMALIZED | Linear regression is a noisy linear inverse problem. | Exact model-level statement. |
| Chapter 9 | Remark 9.4.3 | FORMALIZED | When `m<n`, recovery needs a structural prior because the measurement map has a nontrivial kernel. | Makes the rank-nullity assumptions explicit. |
| Chapter 9 | Remark 9.4.9 | FORMALIZED | The measurement count scales almost linearly with sparsity. | Exact numerical implication. |
| Chapter 9 | Remark 9.4.12 | FORMALIZED | Low-rank recovery needs far fewer than `d^2` observations. | PDF incorrectly cites Corollary 9.4.8; Lean documentation points to 9.4.11. |
| Chapter 9 | Lemma 9.5.2 | FORMALIZED | An `l1`-minimizer's error is no heavier off the true support than on it. | Exact. |
| Chapter 9 | Lemma 9.5.3 | FORMALIZED | The normalized recovery error lies in an approximately sparse set. | Exact, with the nonzero normalization branch explicit. |
| Chapter 9 | Definition 9.5.5 | FORMALIZED | RIP uniformly bounds `‖Av‖` on sparse vectors. | Avoids unsafe singular-value indexing for rectangular matrices. |
| Chapter 9 | Theorem 9.5.6 | FORMALIZED | A sufficiently strong higher-order RIP implies exact `l1` recovery. | The PDF uses a real `lambda` as a block cardinality; Lean correctly uses a natural block multiplier. |
| Chapter 9 | Theorem 9.5.7 | FORMALIZED | A subgaussian random matrix satisfies RIP above the `s log(en/s)` sample scale. | Positivity and `1<=s<=n` are explicit. |
| Chapter 9 | Definition 9.6.1 | FORMALIZED | A sublinear functional is positive-homogeneous and subadditive and may take negative values. | Exact algebraic interface. |
| Chapter 9 | Example 9.6.2 | FORMALIZED | Norms, linear functionals, inner products, and support functions are sublinear examples. | Support set and argument now live in the same space, fixing (9.35)'s dimension mismatch. |
| Chapter 9 | Theorem 9.6.4 | FORMALIZED | The centered sublinear-functional process has subgaussian increments. | Corrects the PDF's reference from process (9.2) to (9.37) and rigorously replaces informal conditional expectations. |
| Chapter 9 | Remark 9.7.5 | FORMALIZED | Random projections exhibit high- and low-dimensional width/diameter phases. | Genuine Haar-projection expectation and scale, not a finite-family envelope presented as the actual random set. |
| Chapter 9 | Eq. (9.1) | FORMALIZED | A fixed vector is approximately norm-preserved by an isotropic subgaussian matrix. | Fixed-vector concentration is independent of the external chaining principle. |
| Chapter 9 | Eq. (9.2) | FORMALIZED | Matrix norm-deviation process `Z_x=‖Ax‖-sqrt(m)‖x‖`. | Exact definition. |
| Chapter 9 | Eq. (9.3) | FORMALIZED | `Z` has `psi2` increments bounded by `CK^2 ‖x-y‖`. | Exact. |
| Chapter 9 | Eq. (9.4) | FORMALIZED | Unit-vector deviation from `sqrt m` is subgaussian. | Exact with positivity hypotheses. |
| Chapter 9 | Eq. (9.5) | FORMALIZED | Norm increments for two unit vectors are subgaussian. | Exact. |
| Chapter 9 | Eq. (9.6) | FORMALIZED | Squared norm differences have the expected `sqrt m ‖x-y‖` scale. | Proof-local heuristic made quantitative by the named tail theorem. |
| Chapter 9 | Eq. (9.7) | FORMALIZED | Normalized squared-norm difference is a sum of independent products. | Exact algebraic expansion. |
| Chapter 9 | Eq. (9.8) | FORMALIZED | Bernstein gives a two-regime tail for the squared increment. | Exact quantitative tail with safe parameter ranges. |
| Chapter 9 | Eq. (9.9) | FORMALIZED | Desired subgaussian tail for normalized norm increments. | Proof-local two-regime argument. |
| Chapter 9 | Eq. (9.10) | FORMALIZED | Radial reduction bounds general increments by unit-sphere increments. | The load-bearing geometric inequality is separately proved. |
| Chapter 9 | Eq. (9.12) | FORMALIZED | A set of `N` points has Gaussian complexity `O(sqrt(log N))` after normalization. | Core geometric estimate; no Appendix dependency. |
| Chapter 9 | Eq. (9.16) | FORMALIZED | Noisy linear observation model `y=Ax+w`. | Exact definition. |
| Chapter 9 | Eq. (9.17) | FORMALIZED | Structural prior `x in T`. | Typed prior/fiber formulation. |
| Chapter 9 | Eq. (9.18) | FORMALIZED | Constrained feasibility program `Ax'=y`, `x' in T`. | Avoids claiming arbitrary optimizer attainment. |
| Chapter 9 | Eq. (9.20) | FORMALIZED | Penalized unconstrained recovery objective. | Exact definition; corrected performance theorem is load-bearing Exercise 9.20. |
| Chapter 9 | Eq. (9.21) | FORMALIZED | `ell0` counts nonzero coordinates and defines sparsity. | Exact finite support count. |
| Chapter 9 | Eq. (9.22) | FORMALIZED | Convex sparse prior `sqrt(s) B_1^n`. | Actual uncountable prior. |
| Chapter 9 | Eq. (9.23) | FORMALIZED | Sparse recovery by feasibility over the `l1` prior. | Program is formalized; its probabilistic guarantee is separately `IN-APPENDIX`. |
| Chapter 9 | Eq. (9.24) | FORMALIZED | Sparse recovery becomes nontrivial at `m` of order `s log n`. | Arithmetic scale implication is core; the underlying Corollary 9.4.8 remains Appendix-dependent. |
| Chapter 9 | Eq. (9.25) | FORMALIZED | Low-rank matrix measurements are Frobenius inner products. | Exact typed measurement map. |
| Chapter 9 | Eq. (9.26) | FORMALIZED | Nuclear-norm constrained recovery program. | Program is core; its recovery guarantee is Appendix-dependent. |
| Chapter 9 | Eq. (9.27) | FORMALIZED | Basis pursuit minimizes `l1` subject to `Ax'=y`. | Exact optimizer predicate. |
| Chapter 9 | Eq. (9.28) | FORMALIZED | Minimality plus triangle inequality yields the support-imbalance bound. | Proof-local exact inequality. |
| Chapter 9 | Eq. (9.29) | FORMALIZED | A nonzero normalized error lies in the approximate-sparse set and the kernel. | Normalization's nonzero case is explicit. |
| Chapter 9 | Eq. (9.30) | FORMALIZED | The approximate-sparse set has width `O(sqrt(s log n))`. | Actual-set width, not only a finite proxy. |
| Chapter 9 | Eq. (9.31) | FORMALIZED | RIP is equivalent to uniform singular-value bounds on sparse coordinate restrictions. | Correct rectangular-matrix formulation. |
| Chapter 9 | Eq. (9.32) | FORMALIZED | Kernel decomposition relates the leading sparse block to the tail blocks. | Proof-local with natural block sizes. |
| Chapter 9 | Eq. (9.33) | FORMALIZED | RIP converts the kernel decomposition into a norm inequality. | Proof-local. |
| Chapter 9 | Eq. (9.34) | FORMALIZED | Each sparse submatrix has near-`sqrt m` singular values with high probability. | Union bound and safe support formulation are explicit. |
| Chapter 9 | Eq. (9.35) | FORMALIZED | Support functional of a bounded set. | Set and argument live in the same inner-product space, correcting the PDF's `R^n`/`R^m` mismatch. |
| Chapter 9 | Eq. (9.36) | FORMALIZED | Sublinear functional has Euclidean linear growth `f(x) <= b ‖x‖`. | Argument is correctly in `R^m`, the domain of `f`, not the printed `R^n`. |
| Chapter 9 | Eq. (9.37) | FORMALIZED | Centered functional-deviation process `f(Ax)-E f(Ax)`. | Exact. |
| Chapter 9 | Eq. (9.38) | FORMALIZED | Functional-deviation process has subgaussian increments. | PDF miscites (9.2); Lean uses (9.37). |
| Chapter 9 | Eq. (9.39) | FORMALIZED | Unit-vector specialization of functional increment control. | Proof-local. |
| Chapter 9 | Eq. (9.40) | FORMALIZED | Orthogonal sum/difference change of variables. | Exact Gaussian product representation, including degenerate directions. |
| Chapter 9 | Eq. (9.41) | FORMALIZED | First conditionally centered functional has a Gaussian concentration bound. | Lean replaces informal conditioning by measurable product integration. |
| Chapter 9 | Eq. (9.42) | FORMALIZED | The reflected functional has the same concentration bound. | Same rigorous product-space argument. |
| Chapter 9 | Eq. (9.43) | FORMALIZED | Support functional grows at most as `rad(S) ‖x‖`. | Argument correctly lies in output space `R^m`, not printed `R^n`. |
| Chapter 9 | Eq. (9.44) | FORMALIZED | Mean support after Gaussian matrix action equals `‖x‖ w(S)`. | Actual support-set identity. |
| Chapter 9 | Eq. (9.46), Exercise 9.25 | FORMALIZED | Unit `s`-sparse set. | Load-bearing exercise definition. |
| Chapter 9 | Eq. (9.47), Exercise 9.25 | FORMALIZED | Truncated `l1` ball. | Load-bearing exercise definition. |
| Chapter 9 | Exercise 9.1 | FORMALIZED | Reverse-triangle geometry needed for the radial increment reduction. | Exact, including normalization hypotheses. |
| Chapter 9 | Exercise 9.11 | FORMALIZED | Additive JL error cannot in general be replaced by a uniform relative error. | Explicit bounded infinite counterexample; no lower-principle dependency. |
| Chapter 9 | Exercise 9.22(a) | FORMALIZED | A full-spark matrix gives uniqueness among sparse candidates. | The PDF's unrestricted uniqueness is false for `m<n`; Lean states the valid sparse-candidate result. |
| Chapter 9 | Exercise 9.23(a--c) | FORMALIZED | `ell0` and `ellp` for `p<1` fail norm axioms, and `ellp^p` tends to support size. | Part (b) correctly assumes ambient dimension at least two. |
| Chapter 9 | Exercise 9.25 | FORMALIZED | Sparse unit set and truncated `l1` ball approximate one another through convex hulls. | Uses ambient zero-padded coordinate restrictions; handles the final short block. |
| Chapter 9 | Exercise 9.32(a) | FORMALIZED | Nullspace property is equivalent to unique `l1` recovery of every sparse vector. | Exact deterministic equivalence. |
| Chapter 9 | Exercise 9.34 | FORMALIZED | Subadditivity implies `f(x)-f(y)<=f(x-y)`. | Exact. |
| Chapter 9 | Exercise 9.40 | FORMALIZED | Support-function bounds are equivalent to a closed-convex-hull ball sandwich. | Adds nonemptiness/closedness and proves the compactness step suppressed by the source. |
| Chapter 9 | Exercise 9.43 | FORMALIZED | True Haar random projections satisfy the almost-round sandwich. | Actual arbitrary bounded set and an `R^m` coordinate image; fixes the PDF's unspecified ambient ball. |
| Chapter 9 | Sec. 9.2.1, before Proposition 9.2.1 | FORMALIZED | Applying matrix deviation to the unit sphere recovers two-sided singular-value bounds. | This fixed-sphere corollary is proved directly and does not need the external lower-majorizing-measure witness. |
| Chapter 9 | Sec. 9.2.2, proof of Proposition 9.2.1 | FORMALIZED | The difference-set Gaussian complexity satisfies `gamma(T-T)=2w(T)`. | Exact finite-set identity used to pass from radius to diameter. |
| Chapter 9 | Sec. 9.3.1, after Theorem 9.3.1 | FORMALIZED | A random full-row-rank matrix has kernel dimension `n-m`. | PDF informally treats full rank as automatic; Lean states the precise almost-sure premise and unconditional rank-nullity lower bound. |
| Chapter 9 | Sec. 9.4.2, before (9.22) | FORMALIZED | Every `s`-sparse unit vector has `l1` norm at most `sqrt s`. | Exact prior-containment inequality. |
| Chapter 9 | Sec. 9.4.3, before (9.26) | FORMALIZED | Rank-`r` matrices have nuclear norm at most `sqrt r` times Frobenius norm. | Exact singular-value Cauchy--Schwarz step. |
| Chapter 9 | Proof of Theorem 9.6.4 | FORMALIZED | A sublinear functional with Euclidean growth is Lipschitz. | Makes the proof's implicit concentration hypothesis explicit. |

## Cross-row and source-level faithfulness issues

These issues were stated outside individual obligation rows in the source audits 
or are important enough to retain explicitly even where a row-level note overlaps.

- The Chapter 3 TranslationReport inventory retains an obsolete baseline count and must not be copied into the README.
- The Chapter 1--2 inventories over-credit omissions in the sharp Stirling note and the negative halves of Examples 2.6.5 and 2.8.7.
- The unscaled-cube isotropy claim is false; the isotropic cube needs the `sqrt(3)` scaling.
- The printed diagonal-free quadratic Grothendieck shorthand omits symmetry.
- Example 3.7.8 has a `cosh`/`sinh` source typo.
- The Chapter 4 SVD proof's last displayed summand prints `u_i v_j^T`; the checked development uses matching index `i`.
- Theorem 4.1.13's literal `rank B = k` minimization fails when `rank A < k`; Lean uses `rank B <= k`.
- Book item 4.1.18 is a Remark, not a Lemma.
- Remark 4.2.5's prose uses the wrong disjoint-ball radius; `epsilon/2` is correct.
- Proposition 4.3.1's phrase 'accuracy epsilon' is ambiguous by a factor of two; Lean uses fibre diameter.
- Theorem 4.3.5 omits coding-feasibility assumptions such as `2r <= n`.
- Theorem 4.4.3's proof interchanges row and column summation indices.
- The stochastic-block-model `2 x 2` eigenvalues and a later eigengap carry factor-two inconsistencies; expected rank is only at most two without nondegeneracy.
- Section 4.7 sometimes calls an uncentered second moment a covariance and suppresses `K^4` sample-complexity dependence.
- The Gaussian-mixture discussion points to the wrong chapter/section; the spectral-clustering development is Chapter 4, Section 4.5.
- Exercise source repairs include 4.4 exact rank, 4.9 power-of-two dimension, 4.14 vectors versus eigenvalues, 4.37 norm versus squared-norm hint, and 4.44 missing expectation signs.
- Definition 5.1.1 permits an arbitrary real Lipschitz constant, and the global 'differentiable implies Lipschitz' prose is false without a bounded derivative on a suitable domain.
- Example 5.1.2 reverses the domain and codomain of an `m x n` matrix.
- A raw Gaussian polar factor is Haar on `O(n)`, not `SO(n)`; `G_{n,1}` is projective/antipodal rather than literally the sphere; the printed Grassmann stabilizer is incomplete.
- Theorem 5.2.7 and the Grassmann theorem omit Lipschitz/measurability assumptions; the Ricci expression behind (5.8) is not normalized over unit tangent vectors.
- The standard-Gaussian potential in Theorem 5.2.11 needs `norm(x)^2/2 + c`; normalization and regularity are missing in the PDF.
- The Johnson--Lindenstrauss statement omits cardinality/range/dimension hypotheses, and Remark 5.3.4 uses the wrong target-dimension symbol.
- Equation (5.12) writes an inverse without invertibility; Remark 5.4.6 reverses inverse monotonicity and includes zero in inverse/log domains.
- Remark 5.4.12 mistakenly compares equation (5.18) with itself.
- Sparse-SBM and covariance statements omit model/sample hypotheses; covariance sample-complexity prose suppresses `K^2`.
- Effective/stable rank is undefined at zero in the PDF, and one rectangular singular-value sum is misindexed.
- Theorem 5.7.1 alternates between `N` and `n` and writes the wrong product domain.
- Section 5.7 cites Theorem 5.1.3 for spherical isoperimetry; the correct reference is Theorem 5.1.5.
- Theorem 6.1.1's ordinary expectations need measurability/integrability qualifications.
- Proposition 6.2.1's non-strict event fails at `K = 0`; Lemma 6.2.4's reciprocal range is undefined at the zero matrix.
- Theorem 6.4.1 and the Gaussian-symmetrization maximum use `sqrt(log n)`/`sqrt(log N)`, which fail at one; safe forms use `log(2n)` or at least two indices.
- Theorem 6.4.1's proof says `Z_ij` is diagonal although only `Z_ij^2` is diagonal.
- Theorem 6.5.1 inherits model, probability/rank range, scaling, and approximation-norm assumptions only from surrounding prose; Lean states them locally.
- Exercise 6.28 omits an expectation, Exercise 6.34 uses an unindexed maximum, and Exercise 6.36 mismatches `n` and `N`.
- Exercise 6.23(b)'s constant-one type-`p` inequality is false; the deferred leaf uses `2^p`. Exercise 6.27 omits coordinate independence.
- Exercise 6.15 should cite Proposition 3.6.3, and the hint for 6.34 should cite Exercise 6.33.
- Exercises 6.31--6.32 are intrinsically under-specified and require author notes for any selected Lean formulation.

## Intentional out-of-scope rows retained for review

These are not comprehensiveness gaps and are not master rows. The last item is still 
a citation issue worth carrying into final review notes.

- **Chapter 4, Remark 4.2.12:** The exact Euclidean-ball volume can be computed geometrically, probabilistically, and analytically. This is a practice prompt, not a mathematical endpoint. Equation (4.33) is treated below as practice.
- **Chapter 4, Exercise Eq. (4.33):** Two-sided asymptotic bounds for Euclidean-ball volume. Do not count as a comprehensive-coverage gap under the exercise policy.
- **Chapter 5, Remark 5.1.8:** The blow-up effect is analogous to a high-dimensional zero-one law. Expository analogy only.
- **Chapter 5, §5.7 notes, p.173:** The spherical isoperimetric result is cited as Theorem 5.1.3. Citation error in the PDF: spherical isoperimetry is Theorem **5.1.5**; 5.1.3 is Lipschitz concentration. Carry this into citation notes.
