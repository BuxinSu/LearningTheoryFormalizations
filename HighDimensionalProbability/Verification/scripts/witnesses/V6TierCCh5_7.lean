import HighDimensionalProbability.Appendix.GrassmannianConcentration
import HighDimensionalProbability.Appendix.EuclideanIsoperimetric
import HighDimensionalProbability.Appendix.BrownianReflection
import HighDimensionalProbability.Appendix.Infra.SLT.GaussianSobolevDense.Defs
import HighDimensionalProbability.Appendix.Infra.SLT.GaussianPoincare.EfronSteinApp
import HighDimensionalProbability.Exercise.Chapter6.Sec01
import HighDimensionalProbability.Exercise.Chapter6.Sec03
import HighDimensionalProbability.Chapter7_RandomProcesses
import HighDimensionalProbability.Exercise.Chapter5.Sec01
import HighDimensionalProbability.Exercise.Chapter7.Sec01
import HighDimensionalProbability.Exercise.Chapter7.Sec06

/-!
# V6 Tier-C compiled witnesses for Chapters 5--7

The five `queue_*` theorems are exactly the queue rows whose Tier-C evidence
cannot be discharged by an existing library citation.  The other ten fixed
queue rows are checked separately as declaration-exact V4 dependency edges.
The two `tierA_*` theorems cover the additional Chapter 5--7 hits from a fresh
Tier-A library scan.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Matrix Set
open scoped BigOperators ENNReal NNReal MatrixOrder ComplexOrder
  RealInnerProductSpace Matrix.Norms.L2Operator

namespace HDP.Verification.V6TierC

/-! ## Seeded random-control witnesses -/

/-- Gaussian norm concentration in the genuinely positive dimension two. -/
theorem seeded_ch5_gaussian_norm_concentration_fin2 :
    (0 : Fin 2) ≠ 1 ∧
      HDP.SubGaussian
          (HDP.Chapter5.gaussianCentered
            (fun x : EuclideanSpace ℝ (Fin 2) ↦ ‖x‖))
          (HDP.Chapter5.gaussianPiMeasure 2) ∧
        HDP.psi2Norm
            (HDP.Chapter5.gaussianCentered
              (fun x : EuclideanSpace ℝ (Fin 2) ↦ ‖x‖))
            (HDP.Chapter5.gaussianPiMeasure 2) ≤
          2 * Real.sqrt 5 := by
  exact ⟨by decide, HDP.Chapter5.gaussian_norm_concentration 2⟩

/-- The Lipschitz seminorm characterization for the nonconstant identity map
on the real line. -/
theorem seeded_ch5_lipschitzSeminorm_real_identity :
    (id (0 : ℝ) ≠ id 1) ∧
      (HDP.Chapter5.lipschitzSeminorm (id : ℝ → ℝ) ≤ (1 : ℝ≥0∞) ↔
        LipschitzWith (1 : ℝ≥0) (id : ℝ → ℝ)) := by
  constructor
  · norm_num
  · exact HDP.Chapter5.lipschitzSeminorm_le_iff (id : ℝ → ℝ) 1

/-- An independent, sorry-free realization of Exercise 6.2(a)'s hypotheses:
two distinct Rademacher coordinates supply the scalar copy, while the nonzero
`1 × 1` matrix makes the off-diagonal chaos identically zero. -/
theorem seeded_ch6_exercise_6_2a_independent_rademacher :
    let μ := EfronSteinApp.rademacherProductMeasure 2
    let X : Fin 1 → EfronSteinApp.RademacherSpace 2 → ℝ :=
      fun _ ω ↦ ω 0
    let X' : Fin 1 → EfronSteinApp.RademacherSpace 2 → ℝ :=
      fun _ ω ↦ ω 1
    HDP.Chapter6.Exercise.IsIndependentScalarCopy X X' μ ∧
      (∀ i, ∫ ω, X i ω ∂μ = 0) ∧
      eLpNorm
          (HDP.Chapter6.Exercise.offDiagonalChaos
            (1 : Matrix (Fin 1) (Fin 1) ℝ) X)
          2 μ ≤
        4 * eLpNorm
          (HDP.Chapter6.Exercise.decoupledChaos
            (1 : Matrix (Fin 1) (Fin 1) ℝ) X X')
          2 μ := by
  dsimp
  have hcoords := EfronSteinApp.coord_indep 2
  have h0law :
      HasLaw
        (fun ω : EfronSteinApp.RademacherSpace 2 => ω 0)
        RademacherApprox.rademacherMeasure
        (EfronSteinApp.rademacherProductMeasure 2) :=
    (MeasureTheory.measurePreserving_eval
      (fun _ : Fin 2 => RademacherApprox.rademacherMeasure) 0).hasLaw
  have h1law :
      HasLaw
        (fun ω : EfronSteinApp.RademacherSpace 2 => ω 1)
        RademacherApprox.rademacherMeasure
        (EfronSteinApp.rademacherProductMeasure 2) :=
    (MeasureTheory.measurePreserving_eval
      (fun _ : Fin 2 => RademacherApprox.rademacherMeasure) 1).hasLaw
  have hcopy : HDP.Chapter6.Exercise.IsIndependentScalarCopy
      (fun _ : Fin 1 => fun ω : EfronSteinApp.RademacherSpace 2 => ω 0)
      (fun _ : Fin 1 => fun ω : EfronSteinApp.RademacherSpace 2 => ω 1)
      (EfronSteinApp.rademacherProductMeasure 2) := by
    refine ⟨ProbabilityTheory.iIndepFun.of_subsingleton,
      ProbabilityTheory.iIndepFun.of_subsingleton, ?_, ?_⟩
    · have h01 := hcoords.indepFun (by decide : (0 : Fin 2) ≠ 1)
      have hcomp := h01.comp
        (by fun_prop :
          Measurable (fun z : ℝ => fun _ : Fin 1 => z))
        (by fun_prop :
          Measurable (fun z : ℝ => fun _ : Fin 1 => z))
      simpa [Function.comp_def] using hcomp
    · intro i
      fin_cases i
      exact h1law.identDistrib h0law
  refine ⟨hcopy, ?_, ?_⟩
  · intro i
    fin_cases i
    rw [h0law.integral_eq]
    have hneg : Integrable (fun x : ℝ => x)
        ((1 / 2 : ℝ≥0∞) • Measure.dirac (-1 : ℝ)) :=
      (integrable_dirac (by simp)).smul_measure (by norm_num)
    have hpos : Integrable (fun x : ℝ => x)
        ((1 / 2 : ℝ≥0∞) • Measure.dirac (1 : ℝ)) :=
      (integrable_dirac (by simp)).smul_measure (by norm_num)
    rw [RademacherApprox.rademacherMeasure,
      integral_add_measure hneg hpos, integral_smul_measure,
      integral_smul_measure, integral_dirac, integral_dirac]
    norm_num
  · rw [show
        HDP.Chapter6.Exercise.offDiagonalChaos
            (1 : Matrix (Fin 1) (Fin 1) ℝ)
            (fun _ : Fin 1 =>
              fun ω : EfronSteinApp.RademacherSpace 2 => ω 0) =
          (0 : EfronSteinApp.RademacherSpace 2 → ℝ) by
        funext ω
        simp [HDP.Chapter6.Exercise.offDiagonalChaos]]
    rw [eLpNorm_zero]
    exact bot_le

/-- Mean and covariance identify the law of the explicit one-coordinate
standard Gaussian vector. -/
theorem seeded_ch7_finiteGaussianProcess_identical_fin1 :
    let X : Fin 1 → EuclideanSpace ℝ (Fin 1) → ℝ := fun i g ↦ g i
    IdentDistrib
        (fun g => WithLp.toLp 2 (X · g))
        (fun g => WithLp.toLp 2 (X · g))
        (stdGaussian (EuclideanSpace ℝ (Fin 1)))
        (stdGaussian (EuclideanSpace ℝ (Fin 1))) := by
  dsimp
  have hGaussian :
      HasGaussianLaw
        (fun g : EuclideanSpace ℝ (Fin 1) =>
          WithLp.toLp 2 (fun i : Fin 1 => g i))
        (stdGaussian (EuclideanSpace ℝ (Fin 1))) := by
    change HasGaussianLaw
      (id : EuclideanSpace ℝ (Fin 1) →
        EuclideanSpace ℝ (Fin 1))
      (stdGaussian (EuclideanSpace ℝ (Fin 1)))
    exact
      (ProbabilityTheory.IsGaussian.hasGaussianLaw_id :
        HasGaussianLaw (id : EuclideanSpace ℝ (Fin 1) →
          EuclideanSpace ℝ (Fin 1))
          (stdGaussian (EuclideanSpace ℝ (Fin 1))))
  exact HDP.Chapter7.finiteGaussianProcess_identDistrib_of_mean_covariance
    hGaussian hGaussian (fun _ ↦ rfl) (fun _ _ ↦ rfl)

/-- The logarithmic polytope-cover bound on the non-singleton segment with
vertices zero and the first Euclidean basis vector. -/
theorem seeded_ch7_polytopeCovering_fin1_segment :
    let e := EuclideanSpace.basisFun (Fin 1) ℝ (0 : Fin 1)
    let V : Finset (EuclideanSpace ℝ (Fin 1)) := {0, e}
    Real.log (HDP.finiteCoveringNumber 1
        (convexHull ℝ (V : Set (EuclideanSpace ℝ (Fin 1))))
        (by
          have hcompact :
              IsCompact
                (convexHull ℝ
                  (V : Set (EuclideanSpace ℝ (Fin 1)))) :=
            V.finite_toSet.isCompact_convexHull ℝ
          have hclosure :
              IsCompact
                (closure
                  (convexHull ℝ
                    (V : Set (EuclideanSpace ℝ (Fin 1))))) := by
            rw [hcompact.isClosed.closure_eq]
            exact hcompact
          obtain ⟨N, hNsub, hNfinite, hNcover⟩ :=
            Metric.exists_finite_isCover_of_isCompact_closure
              (by norm_num : (1 : ℝ≥0) ≠ 0) hclosure
          exact ne_top_of_le_ne_top hNfinite.encard_lt_top.ne
            (hNcover.coveringNumber_le_encard hNsub))) ≤
      10000 * Real.log V.card / ((1 : ℝ≥0) : ℝ) ^ 2 := by
  dsimp
  apply HDP.Chapter7.polytopeCovering_log_bound
  · simp
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · simp
    · simp
  · norm_num

/-! ## Chapter 5 fresh-witness queue rows -/

/-- The Grassmannian endpoint at the genuine line-in-a-plane case `G(2,1)`. -/
theorem queue_ch5_grassmannian_fin2_line :
    ∃ C : ℝ, 0 < C ∧
      HDP.Chapter5.HasMeanConcentration
        (HDP.Chapter5.grassmannHaarMeasure 2 1)
        HDP.Chapter5.grassmannDistance (C / Real.sqrt 2) := by
  obtain ⟨C, hC, hconc⟩ := HDP.Chapter5.grassmannian_concentration
  exact ⟨C, hC, hconc 2 1 (by norm_num) (by norm_num)⟩

/-- The norm/Loewner equivalence on the nonzero Hermitian matrix `diag(1,-1)`. -/
theorem queue_ch5_matrixNorm_loewner_diagonal_fin2 :
    ‖(!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ)‖ ≤ (1 : ℝ) ↔
      (-(1 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) ≤
          HDP.complexifyMatrix
            (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ) ∧
        HDP.complexifyMatrix
            (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ) ≤
          (1 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  apply HDP.Chapter5.matrixNorm_le_iff_loewnerInterval
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

/-! ## Chapter 7 fresh-witness queue rows -/

/-- Gaussian interpolation in dimension one at the interior point `u=1/2`,
with the distinct positive-definite covariance matrices `1` and `2 • 1` and
the concrete nonzero smooth cutoff. -/
theorem queue_ch7_gaussianInterpolation_fin1_half :
    HasDerivAt
      (HDP.Chapter7.gaussianInterpolationExpectation
        (1 : Matrix (Fin 1) (Fin 1) ℝ)
        ((2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ))
        (GaussianSobolev.smoothCutoffR 1))
      ((1 / 2 : ℝ) * ∑ i, ∑ j,
        ((1 : Matrix (Fin 1) (Fin 1) ℝ) i j -
          ((2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) i j) *
          ∫ p, HDP.Chapter7.gaussianHessianEntry
              (GaussianSobolev.smoothCutoffR 1) i j
              (HDP.Chapter7.gaussianInterpolationPoint (1 / 2) p)
            ∂((multivariateGaussian 0
                (1 : Matrix (Fin 1) (Fin 1) ℝ)).prod
              (multivariateGaussian 0
                ((2 : ℝ) •
                  (1 : Matrix (Fin 1) (Fin 1) ℝ))))) (1 / 2) ∧
      GaussianSobolev.smoothCutoffR 1
          (0 : EuclideanSpace ℝ (Fin 1)) = 1 ∧
      (1 : Matrix (Fin 1) (Fin 1) ℝ) ≠
        (2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  constructor
  · exact HDP.Chapter7.gaussianInterpolation
      (1 : Matrix (Fin 1) (Fin 1) ℝ)
      ((2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ))
      Matrix.PosSemidef.one
      (Matrix.PosSemidef.one.smul (by norm_num))
      (GaussianSobolev.smoothCutoffR 1)
      ((GaussianSobolev.smoothCutoffR_contDiff
        (n := 1) (by norm_num)).of_le
          (WithTop.coe_le_coe.2 (OrderTop.le_top _)))
      (GaussianSobolev.smoothCutoffR_hasCompactSupport
        (n := 1) (by norm_num))
      (by norm_num)
  · constructor
    · exact GaussianSobolev.smoothCutoffR_eq_one_of_norm_le
        (n := 1) (by norm_num) (by simp)
    · intro h
      have h00 := congrFun (congrFun h (0 : Fin 1)) (0 : Fin 1)
      norm_num at h00

/-- The global two-sided constants specialized to the genuine two-dimensional cross-polytope. -/
theorem queue_ch7_crossPolytope_dimension_two :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      c * HDP.Chapter2.gaussianMaxScale 0 ≤
          HDP.Chapter7.crossPolytopeGaussianWidth 2 ∧
        HDP.Chapter7.crossPolytopeGaussianWidth 2 ≤
          C * HDP.Chapter2.gaussianMaxScale 0 := by
  obtain ⟨c, C, hc, hC, htwo⟩ :=
    HDP.Chapter7.crossPolytopeGaussianWidth_twoSided
  exact ⟨c, C, hc, hC, by simpa using htwo 0⟩

/-- Multivariate Gaussian integration by parts for standard covariance in
dimension one and the concrete nonzero smooth cutoff observable. -/
theorem queue_ch7_multivariateGaussianIBP_fin1 :
    (∫ x, x (0 : Fin 1) * GaussianSobolev.smoothCutoffR 1 x
        ∂multivariateGaussian 0
          (1 : Matrix (Fin 1) (Fin 1) ℝ) =
      ∑ j, (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 j *
        ∫ x, fderiv ℝ (GaussianSobolev.smoothCutoffR 1) x
            (EuclideanSpace.basisFun (Fin 1) ℝ j)
          ∂multivariateGaussian 0
            (1 : Matrix (Fin 1) (Fin 1) ℝ)) ∧
      GaussianSobolev.smoothCutoffR 1
          (0 : EuclideanSpace ℝ (Fin 1)) = 1 := by
  have hsmooth := GaussianSobolev.smoothCutoffR_contDiff
    (n := 1) (R := 1) (by norm_num)
  have hdiff : ContDiff ℝ 1
      (GaussianSobolev.smoothCutoffR 1 :
        EuclideanSpace ℝ (Fin 1) → ℝ) :=
    hsmooth.of_le (WithTop.coe_le_coe.2 (OrderTop.le_top _))
  have hcompact : HasCompactSupport
      (GaussianSobolev.smoothCutoffR 1 :
        EuclideanSpace ℝ (Fin 1) → ℝ) :=
    GaussianSobolev.smoothCutoffR_hasCompactSupport
      (n := 1) (by norm_num)
  have hintLeft : ∀ i : Fin 1, Integrable
      (fun x : EuclideanSpace ℝ (Fin 1) ↦
        x i * GaussianSobolev.smoothCutoffR 1 x)
      (multivariateGaussian 0
        (1 : Matrix (Fin 1) (Fin 1) ℝ)) := by
    intro i
    have hcoord : Continuous
        (fun x : EuclideanSpace ℝ (Fin 1) ↦ x i) :=
      PiLp.continuous_apply 2 (fun _ : Fin 1 ↦ ℝ) i
    exact (hcoord.mul hdiff.continuous)
      |>.integrable_of_hasCompactSupport hcompact.mul_left
  have hintRight : ∀ j : Fin 1, Integrable
      (fun x : EuclideanSpace ℝ (Fin 1) ↦
        fderiv ℝ (GaussianSobolev.smoothCutoffR 1) x
          (EuclideanSpace.basisFun (Fin 1) ℝ j))
      (multivariateGaussian 0
        (1 : Matrix (Fin 1) (Fin 1) ℝ)) := by
    intro j
    exact ((hsmooth.continuous_fderiv (by simp)).clm_apply continuous_const)
      |>.integrable_of_hasCompactSupport
        (hcompact.fderiv_apply ℝ
          (EuclideanSpace.basisFun (Fin 1) ℝ j))
  constructor
  · exact HDP.Chapter7.multivariateGaussianIntegrationByParts
      (1 : Matrix (Fin 1) (Fin 1) ℝ) Matrix.PosSemidef.one
      (GaussianSobolev.smoothCutoffR 1)
      (fun j x ↦ fderiv ℝ (GaussianSobolev.smoothCutoffR 1) x
        (EuclideanSpace.basisFun (Fin 1) ℝ j))
      hdiff hcompact (fun _ _ ↦ rfl) hintLeft hintRight 0
  · exact GaussianSobolev.smoothCutoffR_eq_one_of_norm_le
      (n := 1) (by norm_num) (by simp)

/-! ## Additional fresh Tier-A hits -/

/-- `exercise_6_25` binds `p` separately in its two conjuncts.  This concrete
`M=N=n=1` instance proves both branches (at `p=3/2` and `p=2`) without using
the exercise's still-unproved global declaration. -/
theorem tierA_ch6_exercise625_two_branches_nonvacuous :
    let a : Fin 1 → ℝ := fun _ ↦ 1
    let x : Fin 1 → Fin 1 → ℝ := fun _ _ ↦ 1
    (0 < (1 : ℕ)) ∧
      (1 < (3 / 2 : ℝ) ∧ (3 / 2 : ℝ) ≤ 2) ∧
      (2 : ℝ) ≤ 2 ∧
      (∀ i, 0 ≤ a i) ∧
      (∑ i, a i = 1) ∧
      (∀ i, HDP.Chapter1.lpNorm (3 / 2 : ℝ)
        (x i - HDP.Chapter6.Exercise.weightedBarycenter a x) ≤ 1) ∧
      (∃ I : Fin 1 → Fin 1,
        HDP.Chapter1.lpNorm (3 / 2 : ℝ)
          (HDP.Chapter6.Exercise.sampledAverage I x -
            HDP.Chapter6.Exercise.weightedBarycenter a x) ≤
          (1 : ℝ) / Real.rpow 1 (((3 / 2 : ℝ) - 1) / (3 / 2 : ℝ))) ∧
      (∀ i, HDP.Chapter1.lpNorm 2
        (x i - HDP.Chapter6.Exercise.weightedBarycenter a x) ≤ 1) ∧
      (∃ I : Fin 1 → Fin 1,
        HDP.Chapter1.lpNorm 2
          (HDP.Chapter6.Exercise.sampledAverage I x -
            HDP.Chapter6.Exercise.weightedBarycenter a x) ≤
          Real.sqrt 2 / Real.sqrt 1) := by
  dsimp
  have hcentered :
      ∀ i : Fin 1,
        (fun _ : Fin 1 ↦ (1 : ℝ)) -
            HDP.Chapter6.Exercise.weightedBarycenter
              (fun _ : Fin 1 ↦ (1 : ℝ))
              (fun _ : Fin 1 ↦ fun _ : Fin 1 ↦ (1 : ℝ)) = 0 := by
    intro i
    fin_cases i
    funext j
    fin_cases j
    simp [HDP.Chapter6.Exercise.weightedBarycenter]
  have hsampled :
      HDP.Chapter6.Exercise.sampledAverage
          (fun _ : Fin 1 ↦ (0 : Fin 1))
          (fun _ : Fin 1 ↦ fun _ : Fin 1 ↦ (1 : ℝ)) -
        HDP.Chapter6.Exercise.weightedBarycenter
          (fun _ : Fin 1 ↦ (1 : ℝ))
          (fun _ : Fin 1 ↦ fun _ : Fin 1 ↦ (1 : ℝ)) = 0 := by
    funext j
    fin_cases j
    simp [HDP.Chapter6.Exercise.sampledAverage,
      HDP.Chapter6.Exercise.weightedBarycenter]
  have hlpzero32 :
      HDP.Chapter1.lpNorm (3 / 2 : ℝ) (0 : Fin 1 → ℝ) = 0 :=
    (HDP.Chapter1.lpNorm_eq_zero_iff (by norm_num)).2 rfl
  have hlpzero2 :
      HDP.Chapter1.lpNorm 2 (0 : Fin 1 → ℝ) = 0 :=
    (HDP.Chapter1.lpNorm_eq_zero_iff (by norm_num)).2 rfl
  refine ⟨by norm_num, ⟨by norm_num, by norm_num⟩, by norm_num,
    fun _ ↦ by norm_num, by simp, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [hcentered i, hlpzero32]
    norm_num
  · refine ⟨fun _ ↦ 0, ?_⟩
    rw [hsampled, hlpzero32]
    norm_num
  · intro i
    rw [hcentered i, hlpzero2]
    norm_num
  · refine ⟨fun _ ↦ 0, ?_⟩
    rw [hsampled, hlpzero2]
    positivity

/-- The Chapter 7 Tier-A hit at `β≥0` has a concrete positive-`β`, two-index
instance; every off-diagonal increment gap is `-1` and every weight is `1`. -/
theorem tierA_ch7_logPartition_positiveBeta_fin2 :
    HDP.Chapter7.logPartitionDerivativeExpression
      (I := Fin 2) 1
      (fun _ _ ↦ 0) (fun _ _ ↦ 1) (fun _ _ ↦ 1) ≤ 0 := by
  exact HDP.Chapter7.exercise_7_7_logPartitionDerivativeExpression_nonpos
    (I := Fin 2) 1 (by norm_num)
    (fun _ _ ↦ 0) (fun _ _ ↦ 1) (fun _ _ ↦ 1)
    (fun _ _ ↦ by norm_num) (fun _ _ ↦ by norm_num)

/-! ## Final-manifest seeded endpoint witnesses -/

alias seeded_final_ch5_euclidean_isoperimetric :=
  HDP.Chapter5.euclidean_isoperimetric

alias seeded_final_ch5_sparseSBM_expectedNoise_degree :=
  HDP.Chapter5.sparseSBM_expectedNoise_degree

/-- The sampled Haar-measure definition is exercised by its fixed-rotation
invariance theorem. -/
alias seeded_final_ch5_orthogonalHaarMeasure_left_invariant :=
  HDP.Chapter5.orthogonalHaarMeasure_left_invariant

alias seeded_final_ch5_sphere_lipschitz_tail :=
  HDP.Chapter5.sphere_lipschitz_tail

alias seeded_final_ch6_hansonWright :=
  HDP.Chapter6.hansonWright

/-- The sampled quadratic-form definition is exercised by its exact finite
double-sum expansion. -/
alias seeded_final_ch6_quadraticForm_eq_doubleSum :=
  HDP.Chapter6.quadraticForm_eq_doubleSum

/-- The sampled matrix-sampling definition is exercised entrywise. -/
alias seeded_final_ch6_sampledMatrix_apply :=
  HDP.Chapter6.sampledMatrix_apply

alias seeded_final_ch6_centeredSampling_expectedOperatorNorm_le :=
  HDP.Chapter6.centeredSampling_expectedOperatorNorm_le

alias seeded_final_ch6_integral_decoupledPartialChaos_le_bilinear :=
  HDP.Chapter6.integral_decoupledPartialChaos_le_bilinear

/-- The sampled interpolation-point definition is exercised by the complete
bounded-derivative interpolation identity. -/
alias seeded_final_ch7_gaussianInterpolation_of_boundedDerivative :=
  HDP.Chapter7.gaussianInterpolation_of_boundedDerivative

alias seeded_final_ch7_finiteGaussianProcess_identDistrib :=
  HDP.Chapter7.finiteGaussianProcess_identDistrib_of_mean_covariance

/-- The first endpoint in the two-definition row is exercised by its
agreement with ordinary expectation on integrable functions. -/
alias seeded_final_ch7_extendedExpectation_eq_integral :=
  HDP.Chapter7.extendedExpectation_eq_integral

/-- The second endpoint in the two-definition row is exercised by the
noncompact-index divergence theorem. -/
alias seeded_final_ch7_extendedExpectedSupremum_noncompact :=
  HDP.Chapter7.exercise_7_14_noncompact_expectedSupremum

alias seeded_final_ch7_slepianInequality :=
  HDP.Chapter7.slepianInequality

alias seeded_final_ch7_brownianReflectionPrinciple_external :=
  HDP.Chapter7.brownianReflectionPrinciple_external

end HDP.Verification.V6TierC
