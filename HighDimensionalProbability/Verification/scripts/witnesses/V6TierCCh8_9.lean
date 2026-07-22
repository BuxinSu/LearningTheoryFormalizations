import HighDimensionalProbability.Chapter8_Chaining
import HighDimensionalProbability.Chapter9_DeviationsOfRandomMatricesOnSets
import HighDimensionalProbability.Appendix.MajorizingMeasureLower
import HighDimensionalProbability.Appendix.Infra.SLT.GaussianLSI.BernoulliLSI
import HighDimensionalProbability.Exercise.Chapter9.Sec04
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Distributions.Uniform

/-!
# V6 Tier-C witnesses for Chapters 8--9

The ten `queue_*` declarations correspond, in order, to the fixed rank-one
through rank-five Tier-B queue rows for Chapters 8 and 9.  Eight are
`WITNESS-BY-CITATION` aliases whose consumers have a direct value dependency
on the selected endpoint.  The two endpoints with no downstream consumer use
explicit nondegenerate models.  The additional
`equation_8_46_*` theorem supplies the near-minimizing admissible chain that the
source wording of Equation (8.46) requires but `HDP.gamma2_le_chainCost` alone
does not construct.  Two further `tierA_gradient_*` declarations pair a
genuinely nonzero Boolean-gradient computation with an instantiation of the
repaired flip-invariance helper.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal RealInnerProductSpace

namespace HDP.Verification.V6TierC

/-! ## Seeded random-control witnesses -/

/-- Example 8.3.18 for an explicit two-range class and one-point sample.  The
bound is the actual uniform deviation, so every member of the nonempty class
is checked simultaneously. -/
theorem seeded_ch8_discrepancy_fin1_two_ranges :
    let F : HDP.Chapter8.BooleanFamily (Fin 1) := {∅, {0}}
    let sample : Fin 1 → Fin 1 := id
    ∀ u ∈ F,
      |HDP.Chapter8.empiricalAverage sample
          (HDP.Chapter8.booleanIndicator u) -
        ∫ x, HDP.Chapter8.booleanIndicator u x
          ∂(Measure.dirac (0 : Fin 1))| ≤
        HDP.Chapter8.booleanUniformDeviation F
          (Measure.dirac (0 : Fin 1)) sample := by
  dsimp
  exact HDP.Chapter8.example_8_3_18_discrepancy
    {∅, {0}} id le_rfl

/-- Constant-one Gaussian comparison for the nonconstant canonical process
indexed by the two distinct real points zero and one. -/
theorem seeded_ch8_talagrandComparison_canonical_fin2 :
    let a : Fin 2 → ℝ := fun i ↦ (i : ℝ)
    let X := HDP.Chapter7.canonicalGaussianProcess a
    a 0 ≠ a 1 ∧
      HDP.Chapter7.expectedFiniteSupremum (stdGaussian ℝ) X ≤
        HDP.Chapter7.expectedFiniteSupremum (stdGaussian ℝ) X := by
  dsimp
  constructor
  · norm_num
  · exact HDP.Chapter8.talagrandComparison_gaussian_constant_one
      (stdGaussian ℝ) (stdGaussian ℝ)
      (HDP.Chapter7.canonicalGaussianProcess
        (fun i : Fin 2 ↦ (i : ℝ)))
      (HDP.Chapter7.canonicalGaussianProcess
        (fun i : Fin 2 ↦ (i : ℝ)))
      (HDP.Chapter7.canonicalGaussianProcess_isGaussian
        (fun i : Fin 2 ↦ (i : ℝ)))
      (HDP.Chapter7.canonicalGaussianProcess_isGaussian
        (fun i : Fin 2 ↦ (i : ℝ)))
      (HDP.Chapter7.canonicalGaussianProcess_centered
        (fun i : Fin 2 ↦ (i : ℝ)))
      (HDP.Chapter7.canonicalGaussianProcess_centered
        (fun i : Fin 2 ↦ (i : ℝ)))
      (fun _ _ ↦ le_rfl)

/-- The closed four-string Pajor example is recompiled as a named seeded
control. -/
alias seeded_ch8_example_8_3_8_full_family :=
  HDP.Chapter8.example_8_3_8_full_family

/-- The growth lower bound on the concrete pair shattered by the four-string
family, inside the full three-coordinate ground set. -/
theorem seeded_ch8_growthFunction_binary_strings :
    2 ^ ({0, 2} : Finset (Fin 3)).card ≤
      HDP.Chapter8.growthFunction HDP.Chapter8.binaryStringFamily 3 := by
  apply HDP.Chapter8.growthFunction_lower_of_shatters
    (F := HDP.Chapter8.binaryStringFamily)
    (q := {0, 2})
    (s := Finset.univ)
  · exact HDP.Chapter8.example_8_3_4_shatters_pair
  · simp
  · simp

/-- A canonical product of two independent book-level Rademacher laws. -/
noncomputable def seededRademacherPlaneMeasure :
    Measure (Fin 2 → ℝ) :=
  Measure.pi (fun _ : Fin 2 => HDP.Chapter4.rademacherMeasure)

instance : IsProbabilityMeasure seededRademacherPlaneMeasure := by
  unfold seededRademacherPlaneMeasure
  infer_instance

/-- One nonconstant two-coordinate Rademacher row. -/
def seededRademacherPlaneMatrix :
    HDP.RandomMatrix (Fin 1) (Fin 2) (Fin 2 → ℝ) :=
  fun omega _ j => omega j

private theorem seededRademacherPlane_coordinate
    (j : Fin 2) :
    HDP.IsRademacher (fun omega : Fin 2 → ℝ => omega j)
      seededRademacherPlaneMeasure := by
  refine ⟨(measurable_pi_apply j).aemeasurable, ?_⟩
  unfold seededRademacherPlaneMeasure
  have hmap := MeasureTheory.Measure.pi_map_eval
    (fun _ : Fin 2 => HDP.Chapter4.rademacherMeasure) j
  simpa [HDP.Chapter4.rademacherMeasure,
    Finset.prod_eq_one (fun i _ => measure_univ)] using hmap

private theorem seededRademacherPlane_independent :
    iIndepFun
      (fun j : Fin 2 => fun omega : Fin 2 → ℝ => omega j)
      seededRademacherPlaneMeasure := by
  unfold seededRademacherPlaneMeasure
  have h := ProbabilityTheory.iIndepFun_pi
    (𝓧 := fun _ : Fin 2 => ℝ) (Ω := fun _ : Fin 2 => ℝ)
    (μ := fun _ : Fin 2 => HDP.Chapter4.rademacherMeasure)
    (X := fun _ => id) (fun _ => aemeasurable_id)
  simpa only [id_eq] using h

/-- A concrete, nonconstant Rademacher measurement row, zero-sparse signal,
and feasible zero selector instantiate the full sparse-recovery endpoint.
The external class is installed from the axiom-clean appendix witness rather
than retained as a hypothesis. -/
theorem seeded_ch9_sparseRecovery_conditional :
    seededRademacherPlaneMatrix (fun _ => 1) 0 0 ≠
        seededRademacherPlaneMatrix (fun _ => -1) 0 0 ∧
      ∃ C : ℝ, 0 < C ∧
        (∫ omega : Fin 2 → ℝ,
            ‖(0 : EuclideanSpace ℝ (Fin 2)) - 0‖
              ∂seededRademacherPlaneMeasure) ≤
          C * HDP.Chapter5.rademacherJLRowConstant ^ 2 *
            (Real.sqrt ((1 : ℕ) : ℝ) *
              Real.sqrt (2 * Real.log (2 * ((0 + 2 : ℕ) : ℝ)))) /
                Real.sqrt ((1 : ℕ) : ℝ) := by
  have hrad : ∀ i j,
      HDP.IsRademacher
        (fun omega => seededRademacherPlaneMatrix omega i j)
        seededRademacherPlaneMeasure := by
    intro i j
    simpa [seededRademacherPlaneMatrix] using
      seededRademacherPlane_coordinate j
  have hwithin : ∀ i,
      iIndepFun
        (fun j omega => seededRademacherPlaneMatrix omega i j)
        seededRademacherPlaneMeasure := by
    intro i
    simpa [seededRademacherPlaneMatrix] using
      seededRademacherPlane_independent
  have hrow (i : Fin 1) :
      HDP.randomMatrixRow seededRademacherPlaneMatrix i =
        HDP.Chapter3.vectorOfCoordinates
          (fun j : Fin 2 => fun omega : Fin 2 → ℝ => omega j) := by
    rfl
  have hrowsm :
      seededRademacherPlaneMatrix.MeasurableRows := by
    apply HDP.RandomMatrix.MeasurableEntries.measurable_rows
    intro i j
    exact measurable_pi_apply j
  have hsub :
      seededRademacherPlaneMatrix.SubGaussianRows
        seededRademacherPlaneMeasure := by
    intro i
    rw [hrow i]
    exact (HDP.Chapter3.rademacherVector_subGaussian
      (fun j => seededRademacherPlane_coordinate j)
      seededRademacherPlane_independent).1
  have hiso :
      seededRademacherPlaneMatrix.IsotropicRows
        seededRademacherPlaneMeasure := by
    intro i
    rw [hrow i]
    exact HDP.Chapter3.rademacherVector_isIsotropic
      (fun j => seededRademacherPlane_coordinate j)
      seededRademacherPlane_independent
  have hindep :
      seededRademacherPlaneMatrix.IndependentRows
        seededRademacherPlaneMeasure :=
    ProbabilityTheory.iIndepFun.of_subsingleton
  have hfinite :
      seededRademacherPlaneMatrix.RowPsi2Finite
        seededRademacherPlaneMeasure := by
    intro i
    refine ⟨HDP.Chapter5.rademacherJLRowConstant, ?_⟩
    intro r hr
    rcases hr with ⟨u, hu, rfl⟩
    exact HDP.Chapter5.rademacher_row_direction_psi2_le
      seededRademacherPlaneMatrix hrad hwithin i u hu
  have hpsi :
      seededRademacherPlaneMatrix.RowPsi2Bound
        seededRademacherPlaneMeasure
        HDP.Chapter5.rademacherJLRowConstant := by
    intro i
    rw [HDP.psi2NormVector]
    apply csSup_le
    · let e : EuclideanSpace ℝ (Fin 2) :=
        EuclideanSpace.single (0 : Fin 2) 1
      exact ⟨HDP.psi2Norm
        (fun omega => inner ℝ
          (HDP.randomMatrixRow seededRademacherPlaneMatrix i omega) e)
          seededRademacherPlaneMeasure,
        e, by simp [e], rfl⟩
    · intro r hr
      rcases hr with ⟨u, hu, rfl⟩
      exact HDP.Chapter5.rademacher_row_direction_psi2_le
        seededRademacherPlaneMatrix hrad hwithin i u hu
  constructor
  · norm_num [seededRademacherPlaneMatrix]
  · letI : HDP.Chapter8.MajorizingMeasureLowerPrinciple :=
      Classical.choice HDP.Chapter8.majorizingMeasureLowerPrinciple_external
    refine ⟨HDP.Chapter9.mStarConstant,
      HDP.Chapter9.mStarConstant_pos, ?_⟩
    simpa using HDP.Chapter9.theorem_9_4_8_sparseRecovery
      (μ := seededRademacherPlaneMeasure)
      (m := 1) (k := 0) (s := 1)
      (by norm_num) seededRademacherPlaneMatrix
      hrowsm hsub hiso hindep hfinite
      HDP.Chapter5.rademacherJLRowConstant_pos hpsi
      (0 : EuclideanSpace ℝ (Fin 2))
      (by simp [HDP.Chapter9.IsSparse, HDP.Chapter9.ellZero,
        HDP.Chapter9.coordinateSupport])
      (by simp)
      (fun _ => (0 : EuclideanSpace ℝ (Fin 2)))
      measurable_const
      (by
        intro omega
        exact HDP.Chapter9.trueSignal_mem_measurementFiber
          (seededRademacherPlaneMatrix omega)
          (HDP.Chapter9.sparseRecoveryPrior 2 1)
          (by simp [HDP.Chapter9.sparseRecoveryPrior]))

/-- Two-sided Chevet on two nonzero one-dimensional segments. -/
theorem seeded_ch9_twoSidedChevet_two_point_sets :
    let e := EuclideanSpace.basisFun (Fin 1) ℝ (0 : Fin 1)
    let F : Finset (EuclideanSpace ℝ (Fin 1)) := {0, e}
    e ≠ 0 ∧
      ∃ C : ℝ, 0 < C ∧
        (HDP.Chapter9.setTwoSidedChevetExpectationEnvelope
          (F : Set (EuclideanSpace ℝ (Fin 1)))
          (F : Set (EuclideanSpace ℝ (Fin 1)))).toReal ≤
          C * HDP.Chapter9.setSupportRadius
              (F : Set (EuclideanSpace ℝ (Fin 1))) *
            (HDP.Chapter9.gaussianComplexityEnvelope
              (F : Set (EuclideanSpace ℝ (Fin 1)))).toReal := by
  dsimp
  constructor
  · intro h
    have hcoord := congrArg
      (fun v : EuclideanSpace ℝ (Fin 1) => v (0 : Fin 1)) h
    norm_num at hcoord
  · letI : HDP.Chapter8.MajorizingMeasureLowerPrinciple :=
      Classical.choice HDP.Chapter8.majorizingMeasureLowerPrinciple_external
    refine ⟨HDP.Chapter9.generalMatrixDeviationConstant,
      HDP.Chapter9.generalMatrixDeviationConstant_pos, ?_⟩
    apply HDP.Chapter9.theorem_9_7_1_twoSidedChevet_set
    · simp
    · simp
    · exact ({0,
        EuclideanSpace.basisFun (Fin 1) ℝ (0 : Fin 1)} :
          Finset (EuclideanSpace ℝ (Fin 1))).finite_toSet.isBounded
    · exact ({0,
        EuclideanSpace.basisFun (Fin 1) ℝ (0 : Fin 1)} :
          Finset (EuclideanSpace ℝ (Fin 1))).finite_toSet.isBounded

/-- The inner-product sublinear functional is nonzero on the real unit
vector and vanishes at zero. -/
theorem seeded_ch9_innerSublinearFunctional_real :
    (HDP.Chapter9.innerSublinearFunctional (1 : ℝ)).toFun 1 = 1 ∧
      (HDP.Chapter9.innerSublinearFunctional (1 : ℝ)).toFun 0 = 0 := by
  norm_num [HDP.Chapter9.innerSublinearFunctional]

/-! ## Chapter 8 queue -/

/-- Remark 8.1.10 in the genuine two-coordinate member of the weighted-basis
family.  Cardinality two certifies that this is not a collapsed singleton
model. -/
theorem queue_ch8_weightedBasis_actualWidth_dimension_two :
    (HDP.Chapter8.exercise84WeightedSet 0).card = 2 ∧
      HDP.Chapter7.gaussianWidth
          (HDP.Chapter8.exercise84WeightedSet 0) ≤
        Real.sqrt 5 * (4 / Real.sqrt (Real.log 2)) := by
  constructor
  · rw [HDP.Chapter8.exercise84WeightedSet,
      Finset.card_image_of_injective _
        (HDP.Chapter8.exercise84Point_injective 0)]
    norm_num
  · exact HDP.Chapter8.exercise_8_4a_weightedBasis_actualGaussianWidth 0

/-- Compiled downstream use of the chain-cost upper bound.  The V4 edge
checker separately requires
`gamma2_ofReal_ne_top -> HDP.gamma2_le_chainCost`. -/
alias queue_ch8_gamma2_finiteness_downstream :=
  HDP.Chapter8.gamma2_ofReal_ne_top

/-! ### A concrete two-sample Monte Carlo model -/

/-- One unbiased bit used by the concrete Monte Carlo witness. -/
noncomputable def monteCarloBitPMF : PMF Bool :=
  PMF.uniformOfFintype Bool

/-- The product law of two independent unbiased bits. -/
noncomputable def monteCarloTwoBitMeasure : Measure (Fin 2 → Bool) :=
  Measure.pi (fun _ : Fin 2 ↦ monteCarloBitPMF.toMeasure)

instance : IsProbabilityMeasure monteCarloTwoBitMeasure := by
  unfold monteCarloTwoBitMeasure
  infer_instance

/-- Coordinate observations on the two-bit product space. -/
def monteCarloBitObservation (i : Fin 2) (ω : Fin 2 → Bool) : Bool :=
  ω i

/-- The nonconstant Rademacher observable on one bit. -/
def monteCarloRademacher (b : Bool) : ℝ :=
  if b then 1 else -1

/-- Remark 8.2.2 on two genuinely independent Rademacher observations.
Every displayed assumption of the endpoint is certified: finite second
moment, mean zero, variance one, and pairwise independence. -/
theorem queue_ch8_dimensionFreeMonteCarlo_two_sample_model :
    (∀ i, MemLp
        (fun ω ↦ monteCarloRademacher (monteCarloBitObservation i ω))
        2 monteCarloTwoBitMeasure) ∧
      (∀ i, ∫ ω, monteCarloRademacher
          (monteCarloBitObservation i ω) ∂monteCarloTwoBitMeasure = 0) ∧
      (∀ i, Var[
          fun ω ↦ monteCarloRademacher (monteCarloBitObservation i ω);
          monteCarloTwoBitMeasure] = 1) ∧
      Set.Pairwise Set.univ (fun i j ↦
        IndepFun
          (fun ω ↦ monteCarloRademacher (monteCarloBitObservation i ω))
          (fun ω ↦ monteCarloRademacher (monteCarloBitObservation j ω))
          monteCarloTwoBitMeasure) ∧
      (∫ ω, |HDP.Chapter8.monteCarloAverage
          monteCarloBitObservation monteCarloRademacher ω|
          ∂monteCarloTwoBitMeasure) ≤
        Real.sqrt ((1 : ℝ) / 2) := by
  have hfmeas : Measurable monteCarloRademacher :=
    measurable_of_finite _
  have hcoordMeas : ∀ i, Measurable
      (fun ω ↦ monteCarloRademacher (monteCarloBitObservation i ω)) := by
    intro i
    change Measurable
      (monteCarloRademacher ∘ fun ω : Fin 2 → Bool ↦ ω i)
    exact hfmeas.comp (measurable_pi_apply i)
  have hmem : ∀ i, MemLp
      (fun ω ↦ monteCarloRademacher (monteCarloBitObservation i ω))
      2 monteCarloTwoBitMeasure := by
    intro i
    apply MemLp.of_bound (hcoordMeas i).aestronglyMeasurable 1
    filter_upwards with ω
    unfold monteCarloRademacher
    split <;> simp
  have hfmean :
      (∫ b, monteCarloRademacher b ∂monteCarloBitPMF.toMeasure) = 0 := by
    rw [PMF.integral_eq_sum]
    norm_num [monteCarloBitPMF, monteCarloRademacher,
      Fintype.sum_bool]
  have hmean : ∀ i,
      (∫ ω, monteCarloRademacher (monteCarloBitObservation i ω)
        ∂monteCarloTwoBitMeasure) = 0 := by
    intro i
    calc
      (∫ ω, monteCarloRademacher (monteCarloBitObservation i ω)
          ∂monteCarloTwoBitMeasure) =
          ∫ b, monteCarloRademacher b ∂monteCarloBitPMF.toMeasure := by
            simpa [monteCarloTwoBitMeasure, monteCarloBitObservation] using
              (MeasureTheory.integral_comp_eval
                (μ := fun _ : Fin 2 ↦ monteCarloBitPMF.toMeasure)
                (i := i) (f := monteCarloRademacher)
                hfmeas.aestronglyMeasurable)
      _ = 0 := hfmean
  have hfsecond :
      (∫ b, monteCarloRademacher b ^ 2
        ∂monteCarloBitPMF.toMeasure) = 1 := by
    rw [PMF.integral_eq_sum]
    norm_num [monteCarloBitPMF, monteCarloRademacher,
      Fintype.sum_bool]
  have hvar : ∀ i, Var[
      fun ω ↦ monteCarloRademacher (monteCarloBitObservation i ω);
      monteCarloTwoBitMeasure] = 1 := by
    intro i
    rw [variance_of_integral_eq_zero (hcoordMeas i).aemeasurable (hmean i)]
    calc
      (∫ ω, monteCarloRademacher
          (monteCarloBitObservation i ω) ^ 2
          ∂monteCarloTwoBitMeasure) =
          ∫ b, monteCarloRademacher b ^ 2
            ∂monteCarloBitPMF.toMeasure := by
              simpa [monteCarloTwoBitMeasure, monteCarloBitObservation] using
                (MeasureTheory.integral_comp_eval
                  (μ := fun _ : Fin 2 ↦ monteCarloBitPMF.toMeasure)
                  (i := i) (f := fun b ↦ monteCarloRademacher b ^ 2)
                  (hfmeas.pow_const 2).aestronglyMeasurable)
      _ = 1 := hfsecond
  have hiIndep : iIndepFun
      (fun i ω ↦ monteCarloRademacher (monteCarloBitObservation i ω))
      monteCarloTwoBitMeasure := by
    unfold monteCarloTwoBitMeasure monteCarloBitObservation
    exact iIndepFun_pi
      (μ := fun _ : Fin 2 ↦ monteCarloBitPMF.toMeasure)
      (X := fun _ ↦ monteCarloRademacher)
      (fun _ ↦ hfmeas.aemeasurable)
  have hpair : Set.Pairwise Set.univ (fun i j ↦
      IndepFun
        (fun ω ↦ monteCarloRademacher (monteCarloBitObservation i ω))
        (fun ω ↦ monteCarloRademacher (monteCarloBitObservation j ω))
        monteCarloTwoBitMeasure) := by
    intro i _ j _ hij
    exact hiIndep.indepFun hij
  refine ⟨hmem, hmean, hvar, hpair, ?_⟩
  simpa using
    (HDP.Chapter8.remark_8_2_2_dimension_free_monteCarlo
      (P := monteCarloTwoBitMeasure) (n := 2) (by norm_num)
      monteCarloBitObservation monteCarloRademacher
      hmem hmean hvar hpair)

/-- Compiled downstream use of the empirical-risk definition.  The V4 edge
checker requires
`exists_empiricalRiskMinimizer -> HDP.Chapter8.empiricalRisk`. -/
alias queue_ch8_empiricalRisk_minimizer_downstream :=
  HDP.Chapter8.exists_empiricalRiskMinimizer

/-- Compiled downstream use of Pajor's inequality in the zero-VC branch of
Sauer--Shelah. -/
alias queue_ch8_pajor_zero_vc_downstream :=
  HDP.Chapter8.lemma_8_3_9_zero_vc

/-! ## Exact-correspondence repair for Equation (8.46) -/

/-- If `gamma2 d` is nonzero, an admissible chain has cost at most twice
`gamma2 d`.  The nonzero assumption is necessary for this pure-infimum
argument: at value zero, a factor-two bound asks for exact attainment.

The `gamma2 d = ∞` branch is immediate.  Otherwise strict monotonicity of
multiplication gives `gamma2 d < 2 * gamma2 d`, and `iInf_lt_iff` extracts a
chain below that threshold. -/
theorem equation_8_46_exists_chainCost_le_two_mul_gamma2
    {T : Type*} [Fintype T] [Nonempty T]
    (d : T → T → ℝ≥0∞) (hγ0 : HDP.gamma2 d ≠ 0) :
    ∃ A : HDP.FiniteAdmissibleChain T,
      HDP.chainCost d A ≤ 2 * HDP.gamma2 d := by
  by_cases hγtop : HDP.gamma2 d = ∞
  · refine ⟨HDP.canonicalFiniteAdmissibleChain T, ?_⟩
    simp [hγtop]
  · have hlt : HDP.gamma2 d < 2 * HDP.gamma2 d := by
      calc
        HDP.gamma2 d = 1 * HDP.gamma2 d := by simp
        _ < 2 * HDP.gamma2 d :=
          (ENNReal.mul_lt_mul_iff_left hγ0 hγtop).2 (by norm_num)
    rw [HDP.gamma2] at hlt
    obtain ⟨A, hA⟩ := iInf_lt_iff.mp hlt
    exact ⟨A, hA.le⟩

/-! ## Full-library Tier-A calibration -/

/-- The Boolean-coordinate gradient term is genuinely nonzero on the
one-coordinate indicator model: its Bernoulli-uniform integral is exactly
one.  This calibrates the nondegenerate model proposed by the full Tier-A
review and supplies the nonzero half of the repaired helper's semantic
certificate. -/
theorem tierA_gradient_term_fin1_indicator_nonzero :
    let h : (Fin 1 → Bool) → ℝ :=
      fun ε ↦ if ε 0 then 1 else 0
    (∫ ε, (h ε - h (BernoulliLSI.flipCoord 0 ε)) ^ 2
        ∂(BernoulliLSI.bernoulliUniform 1)) = 1 ∧
      (∫ ε, (h ε - h (BernoulliLSI.flipCoord 0 ε)) ^ 2
        ∂(BernoulliLSI.bernoulliUniform 1)) ≠ 0 := by
  dsimp
  have hpoint :
      (fun ε : Fin 1 → Bool ↦
        ((if ε 0 then (1 : ℝ) else 0) -
          (if (BernoulliLSI.flipCoord 0 ε) 0 then 1 else 0)) ^ 2) =
        fun _ ↦ (1 : ℝ) := by
    funext ε
    cases hε : ε 0 <;>
      simp [BernoulliLSI.flipCoord, hε]
  rw [hpoint]
  simp

/-- The repaired `gradient_term_symmetric` declaration can be instantiated on
the same nondegenerate one-coordinate model.  Its left side evaluates the
gradient after flipping the base point; its right side evaluates it before
the flip. -/
theorem tierA_gradient_term_symmetric_fin1_indicator_instance :
    let h : (Fin 1 → Bool) → ℝ :=
      fun ε ↦ if ε 0 then 1 else 0
    let ε : Fin 1 → Bool := fun _ ↦ true
    (h (BernoulliLSI.flipCoord 0 ε) -
        h (BernoulliLSI.flipCoord 0 (BernoulliLSI.flipCoord 0 ε))) ^ 2 =
      (h ε - h (BernoulliLSI.flipCoord 0 ε)) ^ 2 := by
  exact BernoulliLSI.gradient_term_symmetric
    (0 : Fin 1) (fun ε ↦ if ε 0 then 1 else 0) (fun _ ↦ true)

/-! ## Chapter 9 queue -/

/-- Compiled source-facing use of Theorem 9.1.2 by Theorem 9.1.1. -/
alias queue_ch9_subGaussianIncrements_matrixDeviation_downstream :=
  HDP.Chapter9.theorem_9_1_1_matrixDeviation

/-- Compiled downstream use of the sublinear-functional Lipschitz lemma in
Theorem 9.6.4. -/
alias queue_ch9_sublinear_lipschitz_subgaussian_downstream :=
  HDP.Chapter9.theorem_9_6_4_subgaussianIncrements

/-- Compiled downstream use of the Gaussian-complexity difference identity in
the expected-diameter form of Proposition 9.2.1. -/
alias queue_ch9_gaussianComplexity_projectionDiameter_downstream :=
  HDP.Chapter9.randomMatrixImageDiameter_expectation

/-- Compiled downstream interpretation of the approximately-sparse width
bound in Remark 9.5.4. -/
alias queue_ch9_approximatelySparseWidth_remark_downstream :=
  HDP.Chapter9.remark_9_5_4_improvedExactRecoveryWidth

/-- A second source-facing consumer of Theorem 9.1.2, here the quadratic
matrix-deviation exercise. -/
alias queue_ch9_subGaussianIncrements_quadraticDeviation_downstream :=
  HDP.Chapter9.exercise_9_3_quadraticMatrixDeviation

/-! ## Final-manifest seeded endpoint witnesses -/

alias seeded_final_ch8_corollary_8_5_8_geometric :=
  HDP.Chapter8.corollary_8_5_8_geometric

alias seeded_final_ch8_example_8_3_5_euclidean_halfspaces :=
  HDP.Chapter8.example_8_3_5_euclidean_halfspaces

alias seeded_final_ch8_discreteDudleyInequality_coveringNumber :=
  HDP.Chapter8.discreteDudleyInequality_coveringNumber

alias seeded_final_ch8_majorizingMeasureLowerPrinciple_external :=
  HDP.Chapter8.majorizingMeasureLowerPrinciple_external

alias seeded_final_ch8_theorem_8_3_17_glivenko_cantelli_real :=
  HDP.Chapter8.theorem_8_3_17_glivenko_cantelli_real

alias seeded_final_ch9_theorem_9_4_8_sparseRecovery :=
  HDP.Chapter9.theorem_9_4_8_sparseRecovery

alias seeded_final_ch9_remark_9_4_6_convexRelaxation :=
  HDP.Chapter9.remark_9_4_6_convexRelaxation

alias seeded_final_ch9_ae_finrank_kernel_eq_sub :=
  HDP.Chapter9.ae_finrank_kernel_eq_sub_of_ae_fullRowRank

alias seeded_final_ch9_theorem_9_1_1_matrixDeviation_envelope :=
  HDP.Chapter9.theorem_9_1_1_matrixDeviation_envelope

alias seeded_final_ch9_functionalDeviationProcess_setSupport_eq :=
  HDP.Chapter9.functionalDeviationProcess_setSupport_eq

end HDP.Verification.V6TierC
