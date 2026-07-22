import HighDimensionalProbability.Chapter0_Appetizer
import HighDimensionalProbability.Chapter1_AnalysisAndProbabilityRefresher
import HighDimensionalProbability.Chapter2_ConcentrationOfIndependentSums
import HighDimensionalProbability.Chapter3_RandomVectorsInHighDimensions
import HighDimensionalProbability.Chapter4_RandomMatrices
import HighDimensionalProbability.Exercise.Chapter1.Sec01
import HighDimensionalProbability.Exercise.Chapter2.Sec07
import HighDimensionalProbability.Exercise.Chapter4.Sec07
import HighDimensionalProbability.Prelude.Matrix
import Mathlib.Probability.Distributions.Uniform

/-!
# V6 Tier-C witnesses for Chapters 0--4

The twenty-five `queue_*` declarations below cover every Tier-C row selected
from `v6_tier_b_ch0_4.tsv`.  Eighteen rows are
`WITNESS-BY-CITATION`: the runner requires a final V4 direct value-dependency
edge from the named downstream theorem to the target.  The other seven rows
use closed, concrete, nondegenerate models; arbitrary parameters followed by
copies of the target hypotheses are forbidden.  The final theorem covers the
only shared-Prelude hit relevant to these chapters in a fresh Tier-A scan.
-/

set_option autoImplicit false
set_option maxHeartbeats 0

open Filter MeasureTheory ProbabilityTheory Matrix Set
open scoped BigOperators ENNReal NNReal MatrixOrder RealInnerProductSpace
  Topology

namespace HDP.Verification.V6TierC

/-! ## Appetizer queue -/

/-- Mathlib's finite convex-hull representation on the genuinely non-singleton
set `{0,1}`. -/
theorem seeded_app_finset_convexHull_two_point :
    convexHull ℝ (↑({0, 1} : Finset ℝ) : Set ℝ) =
      {x : ℝ |
        ∃ w : ℝ → ℝ,
          (∀ y ∈ ({0, 1} : Finset ℝ), 0 ≤ w y) ∧
            ∑ y ∈ ({0, 1} : Finset ℝ), w y = 1 ∧
              ({0, 1} : Finset ℝ).centerMass w id = x} := by
  exact Finset.convexHull_eq ({0, 1} : Finset ℝ)

/-- Carathéodory's convex-hull union on the genuinely non-singleton set
`{0,1}` in one dimension. -/
theorem seeded_app_convexHull_eq_union_two_point :
    convexHull ℝ ({0, 1} : Set ℝ) =
      ⋃ (t : Finset ℝ) (_ : ↑t ⊆ ({0, 1} : Set ℝ))
        (_ : AffineIndependent ℝ ((↑) : t → ℝ)),
          convexHull ℝ ↑t := by
  exact convexHull_eq_union

/-- Remark 0.0.5 for the explicit nontrivial constant sequence `N n = 2`.
Unlike `N n = 1`, its logarithmic numerator is positive rather than
identically zero. -/
theorem queue_ch0_polytope_volume_remark_constant_two :
    Filter.Tendsto
        (fun n : ℕ ↦
          3 * Real.sqrt (Real.log (((fun _ : ℕ ↦ 2) n : ℕ) : ℝ) / n))
        Filter.atTop (nhds 0) ∧
      Filter.Tendsto
        (fun n : ℕ ↦
          (3 * Real.sqrt
            (Real.log (((fun _ : ℕ ↦ 2) n : ℕ) : ℝ) / n)) ^ n)
        Filter.atTop (nhds 0) := by
  apply HDP.Chapter0.polytope_volume_remark_0_0_5 (fun _ : ℕ ↦ 2)
  simpa using
    (tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop :
        Filter.Tendsto (fun n : ℕ ↦ (n : ℝ))
          Filter.atTop Filter.atTop) :
      Filter.Tendsto (fun n : ℕ ↦ Real.log (2 : ℝ) / (n : ℝ))
        Filter.atTop (nhds 0))

/-- Compiled downstream use of Corollary 0.0.3. -/
alias queue_ch0_polytope_cover_downstream :=
  HDP.Chapter0.polytope_volume_le_card_mul_ball

/-- Compiled downstream use of Equation (0.3). -/
alias queue_ch0_polytope_equation_downstream :=
  HDP.Chapter0.polytope_volume_le_theorem_0_0_4

/-- Theorem 0.0.4 on the genuine one-dimensional two-vertex polytope. -/
theorem queue_ch0_polytope_volume_fin1_two_vertices :
    let e := EuclideanSpace.basisFun (Fin 1) ℝ (0 : Fin 1)
    ∃ V : Finset (EuclideanSpace ℝ (Fin 1)),
      e ∈ V ∧ -e ∈ V ∧
        volume
              (convexHull ℝ
                (V : Set (EuclideanSpace ℝ (Fin 1)))) /
            volume
              (Metric.closedBall
                (0 : EuclideanSpace ℝ (Fin 1)) 1) ≤
          ENNReal.ofReal
            ((3 * Real.sqrt
              (Real.log (V.card : ℝ) / (1 : ℕ))) ^ (1 : ℕ)) := by
  classical
  let e := EuclideanSpace.basisFun (Fin 1) ℝ (0 : Fin 1)
  change ∃ V : Finset (EuclideanSpace ℝ (Fin 1)),
    e ∈ V ∧ -e ∈ V ∧
      volume (convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin 1)))) /
          volume
            (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1) ≤
        ENNReal.ofReal
          ((3 * Real.sqrt
            (Real.log (V.card : ℝ) / (1 : ℕ))) ^ (1 : ℕ))
  let V : Finset (EuclideanSpace ℝ (Fin 1)) := {e, -e}
  refine ⟨V, by simp [V], by simp [V], ?_⟩
  apply HDP.Chapter0.polytope_volume_theorem_0_0_4 V
  intro v hv
  simp only [V, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl
  · simp [Metric.mem_closedBall, e]
  · simp [Metric.mem_closedBall, e]

/-- Compiled downstream use of Theorem 0.0.2. -/
alias queue_ch0_approximate_caratheodory_downstream :=
  HDP.Chapter0.exists_polytope_cover

/-! ## Chapter 1 queue -/

/-- Compiled downstream use of the calculation in Example 1.4.2. -/
alias queue_ch1_example_1_4_2_calc_downstream :=
  HDP.Chapter1.example_1_4_2

/-- Compiled downstream use of the union bound in Example 1.4.2. -/
alias queue_ch1_union_bound_downstream :=
  HDP.Chapter1.union_bound_fintype

/-- Compiled downstream use of the book CDF definition. -/
alias queue_ch1_bookCDF_downstream :=
  HDP.Chapter1.tail_eq_one_sub_cdf

/-- Compiled downstream use of the Stirling asymptotic theorem. -/
alias queue_ch1_stirling_downstream :=
  HDP.Chapter1.stirling_ratio_tendsto_one

/-- Robbins' two-sided bounds at the concrete interior integer `n = 2`. -/
theorem queue_ch1_robbins_stirling_n_two :
    Real.sqrt (2 * Real.pi * (2 : ℕ)) *
          (((2 : ℕ) : ℝ) / Real.exp 1) ^ (2 : ℕ) *
          Real.exp (1 / (12 * (((2 : ℕ) : ℝ)) + 1)) ≤
        (((2 : ℕ).factorial : ℕ) : ℝ) ∧
      (((2 : ℕ).factorial : ℕ) : ℝ) ≤
        Real.sqrt (2 * Real.pi * (2 : ℕ)) *
          (((2 : ℕ) : ℝ) / Real.exp 1) ^ (2 : ℕ) *
          Real.exp (1 / (12 * (((2 : ℕ) : ℝ)))) := by
  exact HDP.Chapter1.factorial_robbins_two_sided
    (n := 2) (by norm_num)

/-! ## Chapter 2 queue -/

/-- Compiled downstream use of definiteness of the `ψ₂` norm. -/
alias queue_ch2_psi2_zero_downstream :=
  HDP.psi2Norm_sum_sq_le

/-- Compiled downstream use of the explicit median-of-means theorem. -/
alias queue_ch2_median_of_means_downstream :=
  HDP.Chapter2.medianOfMeans_theorem_2_4_1

/-- Compiled downstream use of the Pythagorean identity. -/
alias queue_ch2_pythagorean_downstream :=
  HDP.khintchine

/-- Compiled downstream use of the scalar subgaussian tail bound. -/
alias queue_ch2_tail_bound_downstream :=
  HDP.subgaussian_hoeffding

/-- Compiled downstream use of the `ψ₂` sum-of-squares bound. -/
alias queue_ch2_psi2_sum_downstream :=
  HDP.subgaussian_hoeffding

/-! ## Chapter 3 queue -/

/-- Compiled downstream use of the Gaussian-direction pushforward identity. -/
alias queue_ch3_gaussian_direction_downstream :=
  HDP.Chapter3.map_projectiveGaussianDirection

/-- Compiled downstream use of the graph cut-size definition. -/
alias queue_ch3_cut_size_downstream :=
  HDP.Chapter3.graphCutObjective_eq_cutValue

/-- Compiled downstream use of the `k`th PCA component bound. -/
alias queue_ch3_pca_kth_downstream :=
  HDP.Chapter3.pca_kth_maximum_principle

/-- Compiled downstream use of the SDP-relaxation correspondence. -/
alias queue_ch3_relaxation_downstream :=
  HDP.Chapter3.exercise_3_52a

/-- A genuine two-atom, positive-dimensional isotropic model for the raw
entropy and support theorem.  Both atoms have mass `1/2`, their values are
the distinct vectors `e` and `-e`, and `K = 2`. -/
theorem queue_ch3_isotropic_entropy_fin2_model :
    ∃ p : Fin 2 → ℝ,
      ∃ x : Fin 2 → EuclideanSpace ℝ (Fin 1),
        Function.Injective x ∧
          (∀ i, 0 < p i) ∧
          (∑ i, p i = 1) ∧
          (∀ j k, ∑ i, p i * (x i j * x i k) =
            if j = k then 1 else 0) ∧
          (∀ i, p i ≤
            2 * Real.exp (-‖x i‖ ^ 2 / (2 : ℝ) ^ 2)) ∧
          ((1 : ℝ) / (2 : ℝ) ^ 2 - Real.log 2 ≤
              HDP.Chapter3.finiteShannonEntropy p ∧
            (1 / 2 : ℝ) * Real.exp ((1 : ℝ) / (2 : ℝ) ^ 2) ≤
              (Fintype.card (Fin 2) : ℝ)) := by
  let e := EuclideanSpace.basisFun (Fin 1) ℝ (0 : Fin 1)
  let p : Fin 2 → ℝ := fun _ ↦ (1 / 2 : ℝ)
  let x : Fin 2 → EuclideanSpace ℝ (Fin 1) := ![e, -e]
  have hxinj : Function.Injective x := by
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals try rfl
    all_goals
      exfalso
      have hcoord := congrArg
        (fun v : EuclideanSpace ℝ (Fin 1) ↦ v (0 : Fin 1)) hij
      norm_num [x, e] at hcoord
  have hp : ∀ i, 0 < p i := by
    intro i
    simp [p]
  have hpsum : ∑ i, p i = 1 := by norm_num [p]
  have hiso : ∀ j k, ∑ i, p i * (x i j * x i k) =
      if j = k then 1 else 0 := by
    intro j k
    fin_cases j
    fin_cases k
    norm_num [p, x, e]
  have hexp : (3 / 4 : ℝ) ≤ Real.exp (-(1 / 4 : ℝ)) := by
    have h := Real.add_one_le_exp (-(1 / 4 : ℝ))
    nlinarith
  have hatom : ∀ i, p i ≤
      2 * Real.exp (-‖x i‖ ^ 2 / (2 : ℝ) ^ 2) := by
    intro i
    fin_cases i <;> simp only [p, x] <;> simp [e] <;> nlinarith
  have hresult :=
    HDP.Chapter3.isotropic_finiteShannonEntropy_and_support_lower_bounds
      p (fun _ ↦ by simp [p]) hpsum x hiso
      (K := 2) (by norm_num) hatom
  refine ⟨p, x, hxinj, hp, hpsum, hiso, hatom, ?_⟩
  simpa using hresult

/-- The higher-level finite-support endpoint on the concrete uniform
two-point coordinate law in dimension two.  The support consists of the
distinct nonzero vectors `√2 e₀` and `√2 e₁`. -/
theorem queue_ch3_isotropic_finite_support_fin2_model :
    let μ : Measure (Fin 2) := uniformOn (Set.univ : Set (Fin 2))
    let X : Fin 2 → EuclideanSpace ℝ (Fin 2) :=
      HDP.frameRandomVector (HDP.Chapter3.coordinateParsevalFrame 2)
    let p : Fin 2 → ℝ := fun ω ↦ μ.real {ω}
    let K := HDP.psi2NormVector X μ
    (2 : ℝ) / K ^ 2 - Real.log 2 ≤
        HDP.Chapter3.finiteShannonEntropy p ∧
      (1 / 2 : ℝ) * Real.exp ((2 : ℝ) / K ^ 2) ≤
        Fintype.card (Fin 2) := by
  letI : NeZero 2 := ⟨by norm_num⟩
  let μ : Measure (Fin 2) := uniformOn (Set.univ : Set (Fin 2))
  let X : Fin 2 → EuclideanSpace ℝ (Fin 2) :=
    HDP.frameRandomVector (HDP.Chapter3.coordinateParsevalFrame 2)
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  have hXinj : Function.Injective X := by
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals try rfl
    all_goals
      exfalso
      have hcoord := congrArg
        (fun v : EuclideanSpace ℝ (Fin 2) ↦ v (0 : Fin 2)) hij
      have hsqrt : 0 < Real.sqrt (2 : ℝ) := by positivity
      simp [X, HDP.frameRandomVector,
        HDP.Chapter3.coordinateParsevalFrame] at hcoord <;> nlinarith
  have hpositive : ∀ ω, 0 < μ.real {ω} := by
    intro ω
    simp [μ, Measure.real, uniformOn_univ]
  apply
    HDP.Chapter3.isotropic_subgaussian_finite_support_entropy_and_card
      (μ := μ) (n := 2) (X := X) (by norm_num)
  · exact (measurable_of_finite X).aemeasurable
  · intro u
    apply (HDP.psi2Norm_le_of_bounded
      (M := 2 * ‖u‖ + 1) (by positivity) ?_).1
    filter_upwards [] with i
    have hXnorm : ‖X i‖ = Real.sqrt 2 := by
      simp [X, HDP.frameRandomVector,
        HDP.Chapter3.coordinateParsevalFrame, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2)]
    have hsqrt : Real.sqrt 2 ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
        Real.sqrt_nonneg 2]
    calc
      |inner ℝ (X i) u| ≤ ‖X i‖ * ‖u‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ 2 * ‖u‖ := by
        rw [hXnorm]
        exact mul_le_mul_of_nonneg_right hsqrt (norm_nonneg u)
      _ ≤ 2 * ‖u‖ + 1 := by norm_num
  · refine ⟨3 / Real.sqrt (Real.log 2), ?_⟩
    rintro r ⟨u, hu, rfl⟩
    apply (HDP.psi2Norm_le_of_bounded
      (M := 3) (by norm_num) ?_).2
    filter_upwards [] with i
    have hXnorm : ‖X i‖ = Real.sqrt 2 := by
      simp [X, HDP.frameRandomVector,
        HDP.Chapter3.coordinateParsevalFrame, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2)]
    have hsqrt : Real.sqrt 2 ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
        Real.sqrt_nonneg 2]
    calc
      |inner ℝ (X i) u| ≤ ‖X i‖ * ‖u‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ 2 := by rw [hXnorm, hu, mul_one]; exact hsqrt
      _ ≤ 3 := by norm_num
  · simpa [X, μ] using
      HDP.Chapter3.coordinateDistribution_isIsotropic 2
  · exact hXinj
  · exact hpositive

/-! ## Chapter 4 queue -/

/-- Remark 4.7.3 on the canonical one-sample, one-dimensional labelled
Gaussian-mixture model.  The augmented row has two coordinates, its row
law and every structural hypothesis are supplied by proved model lemmas,
`K = 4`, `u = 16`, and the deterministic factor is nonzero. -/
theorem queue_ch4_covariance_tail_gaussian_mixture_fin1 :
    let muvec := EuclideanSpace.basisFun (Fin 1) ℝ (0 : Fin 1)
    let A : HDP.Chapter4.GaussianMixtureSample 1 1 →
        Matrix (Fin 1) (Fin 2) ℝ :=
      fun w ↦ HDP.Chapter4.gaussianMixtureAugmentedMatrix w
    let B : Matrix (Fin 1) (Fin 2) ℝ :=
      HDP.Chapter4.gaussianMixtureFactorMatrix muvec
    HDP.Chapter4.gaussianMixtureSampleMeasure 1 1
        {w | HDP.Chapter4.covarianceTailConstant * (4 : ℝ) ^ 2 *
            (Real.sqrt ((((2 : ℕ) : ℝ) + 16) / (1 : ℕ)) +
              (((2 : ℕ) : ℝ) + 16) / (1 : ℕ)) *
              HDP.matrixOpNorm (B * B.transpose) <
          HDP.matrixOpNorm
            (HDP.normalizedGram 1 (A w * B.transpose) -
              B * B.transpose)} ≤
      ENNReal.ofReal (2 * Real.exp (-(16 : ℝ))) := by
  dsimp only
  exact HDP.Chapter4.remark_4_7_3
    (μ := HDP.Chapter4.gaussianMixtureSampleMeasure 1 1)
    (m := 1) (n := 1) (r := 2)
    (fun w : HDP.Chapter4.GaussianMixtureSample 1 1 ↦
      HDP.Chapter4.gaussianMixtureAugmentedMatrix w)
    (HDP.Chapter4.gaussianMixtureFactorMatrix
      (EuclideanSpace.basisFun (Fin 1) ℝ (0 : Fin 1)))
    HDP.Chapter4.gaussianMixtureAugmentedMatrix_aemeasurableRows
    HDP.Chapter4.gaussianMixtureAugmentedMatrix_subGaussianRows
    HDP.Chapter4.gaussianMixtureAugmentedMatrix_isotropicRows
    HDP.Chapter4.gaussianMixtureAugmentedMatrix_independentRows
    HDP.Chapter4.gaussianMixtureAugmentedMatrix_rowPsi2Finite
    (K := (4 : ℝ)) (by norm_num)
    HDP.Chapter4.gaussianMixtureAugmentedMatrix_rowPsi2Bound
    (u := (16 : ℝ)) (by norm_num)

/-- Lemma 4.1.10 on the nonzero `1 × 1` matrix `2I`. -/
theorem queue_ch4_orthogonal_invariance_fin1_nonzero :
    let A : Matrix (Fin 1) (Fin 1) ℝ :=
      (2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)
    HDP.matrixFrobeniusNorm
          ((1 : Matrix (Fin 1) (Fin 1) ℝ) * A *
            (1 : Matrix (Fin 1) (Fin 1) ℝ)) =
        HDP.matrixFrobeniusNorm A ∧
      HDP.matrixOpNorm
          ((1 : Matrix (Fin 1) (Fin 1) ℝ) * A *
            (1 : Matrix (Fin 1) (Fin 1) ℝ)) =
        HDP.matrixOpNorm A := by
  dsimp only
  exact HDP.Chapter4.lemma_4_1_10
    ((2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ))
    (1 : Matrix (Fin 1) (Fin 1) ℝ)
    (1 : Matrix (Fin 1) (Fin 1) ℝ)
    (by exact (Matrix.orthogonalGroup (Fin 1) ℝ).one_mem)
    (by exact (Matrix.orthogonalGroup (Fin 1) ℝ).one_mem)

/-- Compiled downstream use of the Gram-matrix tail theorem. -/
alias queue_ch4_gram_tail_downstream :=
  HDP.Chapter4.theorem_4_6_1_singular_normalized

/-- Equation (4.10) for the nonzero Hermitian matrix `I` in dimension one. -/
theorem queue_ch4_rayleigh_fin1_identity :
    IsGreatest
      {z : ℝ | ∃ x : EuclideanSpace ℝ (Fin 1),
        ‖x‖ = 1 ∧
          z = |inner ℝ x
            ((1 : Matrix (Fin 1) (Fin 1) ℝ).toEuclideanLin x)|}
      (HDP.matrixOpNorm (1 : Matrix (Fin 1) (Fin 1) ℝ)) := by
  exact HDP.Chapter4.remark_4_1_12
    (1 : Matrix (Fin 1) (Fin 1) ℝ) Matrix.isHermitian_one

/-- Compiled downstream use of Theorem 4.4.3. -/
alias queue_ch4_operator_norm_tail_downstream :=
  HDP.Chapter4.exercise_4_41a

/-! ## Shared Prelude Tier-A coverage -/

/-- The zero-padded singular-value theorem at the first out-of-range index of
a genuine `1 × 1` identity matrix. -/
theorem tierA_prelude_matrixSingularValue_fin1_index_one :
    HDP.matrixSingularValue
      (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 = 0 := by
  exact HDP.matrixSingularValue_of_finrank_le
    (1 : Matrix (Fin 1) (Fin 1) ℝ) (by norm_num)

/-! ## Manifest-seeded random-control witnesses -/

/-- The two optimizer statements on the interior data
`n = 2`, `N = exp 1`, `k = 1`.  The logarithm and both denominators are
strictly positive, so this is not a boundary instance. -/
theorem seeded_ch0_polytope_optimizer_exp_one :
    (0 < (2 : ℝ) / (2 * Real.log (Real.exp 1)) ∧
      Real.log (Real.exp 1) -
          (2 : ℝ) /
            (2 * ((2 : ℝ) / (2 * Real.log (Real.exp 1)))) = 0) ∧
      (1 : ℝ) = (2 : ℝ) / (2 * Real.log (Real.exp 1)) := by
  have hlog : 0 < Real.log (Real.exp (1 : ℝ)) := by
    rw [Real.log_exp]
    norm_num
  constructor
  · exact HDP.Chapter0.polytope_volume_optimizer_equation_0_4
      (n := 2) (N := Real.exp 1) (by norm_num) hlog
  · apply HDP.Chapter0.polytope_volume_optimizer_unique
      (n := 2) (N := Real.exp 1) (k := 1) (by norm_num) hlog
    rw [Real.log_exp]
    norm_num

/-- The fair two-point probability law used by the seeded Appetizer,
Chapter 1, and Chapter 2 controls. -/
noncomputable def seededBoolMeasure : Measure Bool :=
  (PMF.uniformOfFintype Bool).toMeasure

instance : IsProbabilityMeasure seededBoolMeasure := by
  unfold seededBoolMeasure
  infer_instance

/-- A nonconstant bounded random variable on the fair two-point space. -/
def seededRademacher (b : Bool) : ℝ :=
  if b then 1 else -1

/-- A nonnegative, nonconstant Bernoulli variable on the same space. -/
def seededBernoulli (b : Bool) : ℝ :=
  if b then 1 else 0

private lemma seededRademacher_memLp_two :
    MemLp seededRademacher 2 seededBoolMeasure := by
  apply MemLp.of_bound
    (measurable_of_finite seededRademacher).aestronglyMeasurable 1
  filter_upwards with b
  cases b <;> simp [seededRademacher]

/-- Exercise 0.2 on a genuinely nonconstant random variable and a center
different from either value. -/
theorem seeded_ch0_mean_minimizes_rademacher :
    seededRademacher true ≠ seededRademacher false ∧
      (∫ b, ‖seededRademacher b -
            ∫ b, seededRademacher b ∂seededBoolMeasure‖ ^ 2
          ∂seededBoolMeasure) ≤
        ∫ b, ‖seededRademacher b - (2 : ℝ)‖ ^ 2
          ∂seededBoolMeasure := by
  constructor
  · norm_num [seededRademacher]
  · exact HDP.Chapter0.integral_norm_sub_mean_sq_le
      (μ := seededBoolMeasure) seededRademacher_memLp_two 2

/-- Lemma 1.6.1 on a nonnegative, nonconstant two-point random variable. -/
theorem seeded_ch1_integrated_tail_bernoulli :
    seededBernoulli true ≠ seededBernoulli false ∧
      (∫⁻ b, ENNReal.ofReal (seededBernoulli b) ∂seededBoolMeasure) =
        ∫⁻ t in Set.Ioi (0 : ℝ),
          seededBoolMeasure {b | t < seededBernoulli b} := by
  have hmeas : AEMeasurable seededBernoulli seededBoolMeasure :=
    (measurable_of_finite seededBernoulli).aemeasurable
  have hnonneg : 0 ≤ᵐ[seededBoolMeasure] seededBernoulli :=
    Filter.Eventually.of_forall fun b => by
      cases b <;> simp [seededBernoulli]
  exact ⟨by norm_num [seededBernoulli],
    HDP.Chapter1.integrated_tail_formula_lintegral hnonneg hmeas⟩

/-- Minkowski's inequality at `p = 2` for two distinct nonconstant
observables on the fair two-point law. -/
theorem seeded_ch1_minkowski_two_point :
    seededRademacher true ≠ seededRademacher false ∧
      eLpNorm (fun b => seededRademacher b + seededBernoulli b)
          (2 : ℝ≥0∞) seededBoolMeasure ≤
        eLpNorm seededRademacher (2 : ℝ≥0∞) seededBoolMeasure +
          eLpNorm seededBernoulli (2 : ℝ≥0∞) seededBoolMeasure := by
  have hR : AEStronglyMeasurable seededRademacher seededBoolMeasure :=
    (measurable_of_finite seededRademacher).aestronglyMeasurable
  have hB : AEStronglyMeasurable seededBernoulli seededBoolMeasure :=
    (measurable_of_finite seededBernoulli).aestronglyMeasurable
  exact ⟨by norm_num [seededRademacher],
    HDP.Chapter1.minkowski_eLpNorm (μ := seededBoolMeasure)
      (p := (2 : ℝ≥0∞)) (by norm_num) hR hB⟩

/-- Equation (1.13)'s vector expectation and both covariance expansions on a
nonconstant one-dimensional Rademacher vector. -/
theorem seeded_ch1_expectation_covariance_rademacher :
    let X : Bool → EuclideanSpace ℝ (Fin 1) :=
      fun b ↦ seededRademacher b •
        EuclideanSpace.basisFun (Fin 1) ℝ (0 : Fin 1)
    X true ≠ X false ∧
      (∫ b, X b ∂seededBoolMeasure) 0 =
        ∫ b, X b 0 ∂seededBoolMeasure ∧
      HDP.covarianceMatrix X seededBoolMeasure =
        HDP.secondMomentMatrix X seededBoolMeasure -
          Matrix.vecMulVec
            (∫ b, X b ∂seededBoolMeasure).ofLp
            (∫ b, X b ∂seededBoolMeasure).ofLp ∧
      cov[(fun b ↦ X b 0), (fun b ↦ X b 0); seededBoolMeasure] =
        (∫ b, X b 0 * X b 0 ∂seededBoolMeasure) -
          (∫ b, X b 0 ∂seededBoolMeasure) *
            (∫ b, X b 0 ∂seededBoolMeasure) := by
  dsimp
  let X : Bool → EuclideanSpace ℝ (Fin 1) :=
    fun b ↦ seededRademacher b •
      EuclideanSpace.basisFun (Fin 1) ℝ (0 : Fin 1)
  have hX : MemLp X 2 seededBoolMeasure := by
    apply MemLp.of_bound (measurable_of_finite X).aestronglyMeasurable 1
    filter_upwards with b
    cases b <;> simp [X, seededRademacher]
  have hcoord : MemLp (fun b ↦ X b 0) 2 seededBoolMeasure := by
    simpa only [Function.comp_apply, EuclideanSpace.coe_proj] using
      hX.continuousLinearMap_comp (EuclideanSpace.proj (𝕜 := ℝ) 0)
  change X true ≠ X false ∧ _ ∧ _ ∧ _
  refine ⟨?_, HDP.Chapter1.expectation_vector_apply
      (hX.integrable one_le_two) 0,
    HDP.Chapter3.covarianceMatrix_eq_secondMoment_sub_mean hX,
    ProbabilityTheory.covariance_eq_sub hcoord hcoord⟩
  intro h
  have hcoordEq := congrArg
    (fun v : EuclideanSpace ℝ (Fin 1) => v 0) h
  norm_num [X, seededRademacher] at hcoordEq

/-- Definition 2.6.4 and its attained-`ψ₂` bound on a nonconstant bounded
Rademacher variable. -/
theorem seeded_ch2_rademacher_psi2_attainment :
    seededRademacher true ≠ seededRademacher false ∧
      HDP.psi2MGF seededRademacher seededBoolMeasure
          (HDP.psi2Norm seededRademacher seededBoolMeasure) ≤ 2 := by
  have hmeas : AEMeasurable seededRademacher seededBoolMeasure :=
    (measurable_of_finite seededRademacher).aemeasurable
  have hbound : ∀ᵐ b ∂seededBoolMeasure,
      |seededRademacher b| ≤ (2 : ℝ) :=
    Filter.Eventually.of_forall fun b => by
      cases b <;> norm_num [seededRademacher]
  have hsub : HDP.SubGaussian seededRademacher seededBoolMeasure :=
    (HDP.psi2Norm_le_of_bounded (μ := seededBoolMeasure)
      (M := 2) (by norm_num) hbound).1
  have hsource : HDP.IsSubGaussianRandomVariable
      seededRademacher seededBoolMeasure :=
    ⟨inferInstance, hmeas, hsub⟩
  exact ⟨by norm_num [seededRademacher],
    hsource.psi2MGF_psi2Norm_le_two⟩

/-- Example 3.7.8 on nonzero one-dimensional inputs and positive scale. -/
theorem seeded_ch3_sine_feature_fin1 :
    let e := EuclideanSpace.basisFun (Fin 1) ℝ (0 : Fin 1)
    e ≠ 0 ∧
      inner ℝ (HDP.sineFeature 1 (by norm_num) e)
          (HDP.signedSineFeature 1 (by norm_num) e) =
        Real.sin (inner ℝ e e) := by
  dsimp
  constructor
  · intro he
    have hcoord := congrArg
      (fun v : EuclideanSpace ℝ (Fin 1) => v (0 : Fin 1)) he
    norm_num at hcoord
  · simpa using HDP.Chapter3.sine_feature_identity
      (c := 1) (by norm_num)
      (EuclideanSpace.basisFun (Fin 1) ℝ (0 : Fin 1))
      (EuclideanSpace.basisFun (Fin 1) ℝ (0 : Fin 1))

/-- Definition 3.7.1 on a genuinely two-axis, two-coordinate tensor space. -/
theorem seeded_ch3_tensor_power_fin2_two :
    HDP.TensorPowerSpace (Fin 2) 2 =
      HDP.TensorSpace (fun _ : Fin 2 => Fin 2) := by
  exact HDP.tensorPowerSpace_eq_tensorSpace (ι := Fin 2) 2

/-- The Gaussian-rounding label on two explicit nonzero real vectors has the
advertised sign-valued square. -/
theorem seeded_ch3_gaussianRoundingLabel_real :
    (1 : ℝ) ≠ 0 ∧
      HDP.Chapter3.gaussianRoundingLabel (1 : ℝ) (-1 : ℝ) ^ 2 = 1 := by
  constructor
  · norm_num
  · exact HDP.hyperplaneLabel_sq (1 : ℝ) (-1 : ℝ)

/-- All three endpoints in the unit-sphere row at positive dimension one,
using the explicit first basis direction and the positive threshold `1/2`. -/
theorem seeded_ch3_unitSphere_fin1_all_endpoints :
    let v : Metric.sphere
        (0 : EuclideanSpace ℝ (Fin 1)) 1 :=
      ⟨EuclideanSpace.basisFun (Fin 1) ℝ (0 : Fin 1), by
        simp [Metric.mem_sphere]⟩
    (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin 1)))
        {x | (1 / 2 : ℝ) ≤
          inner ℝ (x : EuclideanSpace ℝ (Fin 1))
            (v : EuclideanSpace ℝ (Fin 1))} ≤
      ENNReal.ofReal
        (2 * Real.exp (-((1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ 2 / 2)) ∧
      HDP.SubGaussianVector
        (HDP.uniformSphereVector (EuclideanSpace ℝ (Fin 1)))
        (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin 1))) ∧
      HDP.psi2NormVector
        (HDP.uniformSphereVector (EuclideanSpace ℝ (Fin 1)))
        (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin 1))) ≤
          Real.sqrt 5 * HDP.Chapter3.sphereProjectionTailScale /
            Real.sqrt 1 := by
  dsimp
  constructor
  · exact HDP.Chapter3.sphere_tail 1 (by norm_num)
      ⟨EuclideanSpace.basisFun (Fin 1) ℝ (0 : Fin 1), by
        simp [Metric.mem_sphere]⟩
      (by norm_num)
  · simpa using HDP.Chapter3.unitSphere_subGaussian 1 (by norm_num)

/-- Remark 4.2.3 for the non-singleton compact set `{0,1}` in the complete
real line. -/
theorem seeded_ch4_relative_compactness_two_point :
    (0 : ℝ) ≠ 1 ∧
      (IsCompact (closure ({0, 1} : Set ℝ)) ↔
        ∀ ε : ℝ≥0, ε ≠ 0 →
          ∃ N ⊆ ({0, 1} : Set ℝ), N.Finite ∧
            Metric.IsCover ε ({0, 1} : Set ℝ) N) := by
  constructor
  · norm_num
  · exact HDP.Chapter4.remark_4_2_3 ({0, 1} : Set ℝ)

/-- Matrix-form SVD existence on the nonzero `1 × 1` identity. -/
theorem seeded_ch4_matrix_form_svd_fin1 :
    ∃ s : HDP.Chapter4.RealSVD
        (1 : Matrix (Fin 1) (Fin 1) ℝ), True := by
  obtain ⟨s, _bU, _bV, _⟩ :=
    HDP.Chapter4.exists_matrixFormSVD
      (1 : Matrix (Fin 1) (Fin 1) ℝ)
  exact ⟨s, True.intro⟩

/-- Definition 4.5.1's coordinate expectation on a nonempty two-vertex SBM
with interior within/between probabilities. -/
theorem seeded_ch4_sbm_expected_adjacency_interior :
    let p : Set.Icc (0 : ℝ) 1 := ⟨1 / 2, by norm_num⟩
    let q : Set.Icc (0 : ℝ) 1 := ⟨1 / 3, by norm_num⟩
    ∫ G, HDP.sbmAdjacencyMatrix G (0 : HDP.SBMVertex 1)
          (1 : HDP.SBMVertex 1)
        ∂(HDP.Chapter4.definition_4_5_1 1 p q) =
      HDP.sbmExpectedAdjacency 1 p q
        (0 : HDP.SBMVertex 1) (1 : HDP.SBMVertex 1) := by
  dsimp
  exact HDP.Chapter4.definition_4_5_1_expectedAdjacency
    1 ⟨1 / 2, by norm_num⟩ ⟨1 / 3, by norm_num⟩ 0 1

/-! ## Final-manifest seeded endpoint witnesses -/

/-- The final Appetizer sample retains the unique interior optimizer. -/
alias seeded_final_app_polytope_optimizer_unique :=
  HDP.Chapter0.polytope_volume_optimizer_unique

/-- The final Appetizer sample retains the exact optimizer identity. -/
alias seeded_current_ch0_polytope_optimizer_equation :=
  HDP.Chapter0.polytope_volume_optimizer_equation_0_4

alias seeded_final_app_integral_norm_sub_mean_sq :=
  HDP.Chapter0.integral_norm_sub_mean_sq

alias seeded_final_ch1_indicator_biUnion_le_sum :=
  HDP.Chapter1.indicator_biUnion_le_sum

alias seeded_final_ch1_exercise_1_11a_eLpNorm :=
  HDP.Chapter1.exercise_1_11a_eLpNorm

alias seeded_final_ch1_holder_rv :=
  HDP.Chapter1.holder_rv

alias seeded_final_ch1_log_gamma_stirling :=
  HDP.Chapter1.log_gamma_stirling

alias seeded_final_ch1_convex_iff_segment :=
  HDP.Chapter1.convex_iff_segment

alias seeded_final_ch2_gaussian_mgf :=
  HDP.Chapter2.gaussian_mgf

alias seeded_final_ch2_expectation_linear :=
  HDP.Chapter1.expectation_linear

alias seeded_final_ch2_remark_2_2_4 :=
  HDP.Chapter2.remark_2_2_4

alias seeded_final_ch2_median_one_coordinate_robust :=
  HDP.Chapter2.median_one_coordinate_robust

alias seeded_final_ch2_centering_L2 :=
  HDP.centering_L2

alias seeded_final_ch3_sphere_isIsotropic :=
  HDP.Chapter3.sphere_isIsotropic

alias seeded_final_ch3_secondMoment_inner_sq :=
  HDP.Chapter3.secondMoment_inner_sq

alias seeded_final_ch3_thinShellVariance_subGaussian :=
  HDP.Chapter3.thinShellVariance_subGaussian

/-- The sampled definition is exercised by its exact bilinear identification. -/
alias seeded_final_ch3_quadraticObjective_eq_bilinear :=
  HDP.Chapter3.quadraticObjective_eq_bilinear

alias seeded_final_ch4_theorem_4_6_1_singular :=
  HDP.Chapter4.theorem_4_6_1_singular

alias seeded_final_ch4_courantFischer :=
  HDP.Chapter4.courantFischer

alias seeded_final_ch4_definition_4_5_1_expectedAdjacency :=
  HDP.Chapter4.definition_4_5_1_expectedAdjacency

alias seeded_final_ch4_remark_4_7_2 :=
  HDP.Chapter4.remark_4_7_2

/-- The directly sorry-backed global Exercise 4.50(c) is not imported as
evidence.  Instead, this proves its packing conclusion on the admissible
`m = n = r = 1`, `c = ε = 1` instance.  The singleton zero matrix lies in the
rank-one Frobenius ball, has the required cardinal lower bound, and is
pairwise separated vacuously. -/
theorem seeded_final_ch4_exercise_4_50c_fin1 :
    (0 : ℝ) < 1 ∧ (1 : ℕ) ≤ 1 ∧ (1 : ℕ) ≤ min 1 1 ∧
      ∃ N : Finset (Matrix (Fin 1) (Fin 1) ℝ),
        Real.rpow ((1 : ℝ) / 1)
            ((((1 + 1 : ℕ) : ℝ) * (1 : ℕ)) / 2) ≤ (N.card : ℝ) ∧
          (N : Set (Matrix (Fin 1) (Fin 1) ℝ)) ⊆
            HDP.Chapter4.Exercise.lowRankFrobeniusBall 1 1 1 ∧
          Set.Pairwise (N : Set (Matrix (Fin 1) (Fin 1) ℝ))
            (fun A B =>
              2 * (1 : ℝ) < HDP.matrixFrobeniusNorm (A - B)) := by
  classical
  refine ⟨by norm_num, by norm_num, by norm_num, {0}, ?_, ?_, ?_⟩
  · norm_num
  · intro A hA
    simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hA
    subst A
    simp [HDP.Chapter4.Exercise.lowRankFrobeniusBall]
  · simp

end HDP.Verification.V6TierC
