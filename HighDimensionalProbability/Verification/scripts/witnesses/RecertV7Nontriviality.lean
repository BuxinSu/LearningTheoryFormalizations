import HighDimensionalProbability
import MatrixConcentration.Chapter2_MatrixFunctionsAndProbabilityWithMatrices

/-!
# Current-tree V7 nontriviality witnesses

These verification-only theorems close tractable definition-sanity rows with
concrete nonempty models or exact data-preservation laws.  Every theorem is
named so the separate collector can verify its direct type dependencies and
axiom set.
-/

set_option autoImplicit false
set_option maxHeartbeats 0

open MeasureTheory
open scoped BigOperators ENNReal NNReal RealInnerProductSpace
open scoped Matrix.Norms.L2Operator

namespace HDP.Verification.V7

/-! ## Boolean classes and VC predicates -/

theorem booleanClass_has_distinct_values :
    (∅ : HDP.BooleanClass Bool) ≠ ({∅} : HDP.BooleanClass Bool) := by
  simp

theorem booleanFamily_has_distinct_values :
    (∅ : HDP.Chapter8.BooleanFamily Bool) ≠
      ({∅} : HDP.Chapter8.BooleanFamily Bool) := by
  simp

theorem booleanClass_vc_predicates_nonconstant :
    HDP.Chapter8.realClosedIntervals.Shatters ({0, 1} : Finset ℝ) ∧
      ¬ HDP.Chapter8.realClosedIntervals.Shatters
        ({0, 1, 2} : Finset ℝ) ∧
      HDP.Chapter8.realClosedIntervals.VCDimLE 2 ∧
      ¬ HDP.Chapter8.realClosedIntervals.VCDimLE 1 ∧
      HDP.Chapter8.realClosedIntervals.VCDimEq 2 ∧
      ¬ HDP.Chapter8.realClosedIntervals.VCDimEq 1 := by
  have hpair := HDP.Chapter8.realClosedIntervals_shatter_pair
  have hle := HDP.Chapter8.realClosedIntervals_vcDimLE
  have heq := HDP.Chapter8.example_8_3_2_real_closed_intervals
  refine ⟨hpair, ?_, hle, ?_, heq, ?_⟩
  · intro hthree
    have hcard := hle ({0, 1, 2} : Finset ℝ) hthree
    norm_num at hcard
  · intro hone
    have hcard := hone ({0, 1} : Finset ℝ) hpair
    norm_num at hcard
  · intro hone
    exact (by
      have hcard := hone.1 ({0, 1} : Finset ℝ) hpair
      norm_num at hcard)

/-! ## Finite chaining structures and process helpers -/

theorem finiteDudleyChain_bool_inhabited_and_anchor_faithful :
    ∃ C : HDP.Chapter8.FiniteDudleyChain Bool 1,
      C.anchor = false ∧
        C.projection 0 true = false ∧
        C.projection 1 true = true := by
  let C : HDP.Chapter8.FiniteDudleyChain Bool 1 :=
    { anchor := false
      projection := fun k t => if k = 0 then false else t
      coarse := by simp
      exact := by simp }
  exact ⟨C, rfl, by simp [C], by simp [C]⟩

theorem finiteProcessOscillation_bool_is_nonzero :
    let X : HDP.RandomProcess Bool Unit :=
      fun t _ => if t then 1 else 0
    1 ≤ HDP.Chapter8.finiteProcessOscillation X () := by
  dsimp
  unfold HDP.Chapter8.finiteProcessOscillation
  have h :=
    Finset.le_sup'
      (fun p : Bool × Bool =>
        |(if p.1 then (1 : ℝ) else 0) -
          (if p.2 then (1 : ℝ) else 0)|)
      (show (true, false) ∈
        (Finset.univ.product (Finset.univ : Finset Bool)) by simp)
  norm_num at h ⊢

theorem edgeIncrement_bool_is_nonzero :
    let X : HDP.RandomProcess Bool Unit :=
      fun t _ => if t then 1 else 0
    HDP.Chapter8.edgeIncrement X (true, false) () = 1 := by
  norm_num [HDP.Chapter8.edgeIncrement]

theorem finiteEuclideanProcess_preserves_indexed_values
    {n : ℕ} {Ω : Type*}
    (T : Finset (EuclideanSpace ℝ (Fin n)))
    (X : EuclideanSpace ℝ (Fin n) → Ω → ℝ)
    (t : ↥T) (ω : Ω) :
    HDP.Chapter8.finiteEuclideanProcess T X t ω = X t.1 ω := by
  rfl

theorem canonicalFiniteAdmissibleChain_bool_has_required_levels :
    ∃ A : HDP.FiniteAdmissibleChain Bool,
      A = HDP.canonicalFiniteAdmissibleChain Bool ∧
        A.level ⟨A.terminal, Nat.lt_succ_self A.terminal⟩ =
          Finset.univ ∧
        (A.level ⟨0, Nat.zero_lt_succ A.terminal⟩).card = 1 := by
  let A := HDP.canonicalFiniteAdmissibleChain Bool
  exact ⟨A, rfl, A.level_terminal, A.level_zero_card⟩

/-! ## Stochastic-block-model helpers -/

theorem sbmEdge_one_has_distinct_edges :
    @HDP.SBMEdge = @HDP.SBMEdge ∧
      (s((0 : HDP.SBMVertex 1), (0 : HDP.SBMVertex 1)) :
          HDP.SBMEdge 1) ≠
        s((0 : HDP.SBMVertex 1), (1 : HDP.SBMVertex 1)) := by
  exact ⟨rfl, by decide⟩

theorem sbmCommunity_has_both_values :
    HDP.sbmCommunity (0 : HDP.SBMVertex 1) = false ∧
      HDP.sbmCommunity (1 : HDP.SBMVertex 1) = true := by
  decide

theorem sbmCommunityLabel_has_both_signs :
    HDP.sbmCommunityLabel (0 : HDP.SBMVertex 1) = 1 ∧
      HDP.sbmCommunityLabel (1 : HDP.SBMVertex 1) = -1 := by
  norm_num [HDP.sbmCommunityLabel, HDP.sbmCommunity]

theorem spectralSignLabel_has_both_signs :
    HDP.spectralSignLabel (fun _ : Unit => (1 : ℝ)) () = 1 ∧
      HDP.spectralSignLabel (fun _ : Unit => (-1 : ℝ)) () = -1 := by
  norm_num [HDP.spectralSignLabel]

theorem misclassifiedUpToSign_bool_detects_one_error :
    HDP.misclassifiedUpToSign
        (fun b : Bool => if b then (-1 : ℝ) else 1)
        (fun _ => (1 : ℝ)) = 1 := by
  norm_num [HDP.misclassifiedUpToSign, HDP.spectralSignLabel] <;> decide

/-! ## Matrix data preservation and centering -/

theorem gaussianMatrixFlatten_preserves_entry :
    HDP.gaussianMatrixFlatten (m := 1) (n := 1)
        (fun _ _ => (1 : ℝ)) ((0 : Fin 1), (0 : Fin 1)) = 1 := by
  rfl

theorem gaussianMatrixActionLinearMap_nonzero :
    let x : EuclideanSpace ℝ (Fin 1) :=
      WithLp.toLp 2 (fun _ => (1 : ℝ))
    let g : EuclideanSpace ℝ (Fin 1 × Fin 1) :=
      WithLp.toLp 2 (fun _ => (1 : ℝ))
    HDP.gaussianMatrixActionLinearMap x g (0 : Fin 1) = 1 := by
  norm_num [HDP.gaussianMatrixActionLinearMap, HDP.gaussianMatrixAction,
    HDP.gaussianMatrixUnvectorize]

theorem matrixConcentration_measurableSpace_coordinate_nonconstant :
    Measurable
        (fun A : Matrix (Fin 1) (Fin 1) ℂ =>
          A (0 : Fin 1) (0 : Fin 1)) ∧
      (fun A : Matrix (Fin 1) (Fin 1) ℂ =>
          A (0 : Fin 1) (0 : Fin 1)) (fun _ _ => 0) ≠
        (fun A : Matrix (Fin 1) (Fin 1) ℂ =>
          A (0 : Fin 1) (0 : Fin 1)) (fun _ _ => 1) := by
  constructor
  · fun_prop
  · norm_num

theorem gaussianCentered_preserves_differences
    {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (z w : Fin n → ℝ) :
    HDP.Chapter5.gaussianCentered F z -
        HDP.Chapter5.gaussianCentered F w =
      F (WithLp.toLp 2 z) - F (WithLp.toLp 2 w) := by
  simp only [HDP.Chapter5.gaussianCentered]
  ring

theorem matrixDeviationProcess_preserves_sample_norm_differences
    {Ω : Type*} {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (x : EuclideanSpace ℝ (Fin n)) (ω ξ : Ω) :
    HDP.Chapter9.matrixDeviationProcess A x ω -
        HDP.Chapter9.matrixDeviationProcess A x ξ =
      ‖HDP.Chapter9.matrixAction A x ω‖ -
        ‖HDP.Chapter9.matrixAction A x ξ‖ := by
  simp only [HDP.Chapter9.matrixDeviationProcess]
  ring

theorem centeredEntry_preserves_sample_differences
    {Ω m n : Type*} [MeasurableSpace Ω]
    (A : HDP.RandomMatrix m n Ω) (i : m) (j : n)
    (μ : Measure Ω) (ω ξ : Ω) :
    HDP.centeredEntry A i j μ ω - HDP.centeredEntry A i j μ ξ =
      A ω i j - A ξ i j := by
  simp only [HDP.centeredEntry]
  ring

theorem randomMatrixColumn_preserves_entries
    {Ω m n : Type*} [Fintype m]
    (A : HDP.RandomMatrix m n Ω) (j : n) (ω : Ω) (i : m) :
    HDP.randomMatrixColumn A j ω i = A ω i j := by
  rfl

theorem randomMatrixEntryPsi2Bound_unit_separates_thresholds :
    let A : HDP.RandomMatrix Unit Unit Unit := fun _ _ _ => 0
    A.EntryPsi2Bound (Measure.dirac ()) 0 ∧
      ¬ A.EntryPsi2Bound (Measure.dirac ()) (-1) := by
  dsimp
  constructor
  · intro _ _
    rw [HDP.psi2Norm_const]
    norm_num
  · intro h
    have hle := h () ()
    have hnonneg :=
      HDP.psi2Norm_nonneg (fun _ : Unit => (0 : ℝ))
        (Measure.dirac ())
    linarith

theorem realMatrix_has_nonzero_member :
    ∃ A : HDP.RealMatrix Unit Unit, A () () = 1 := by
  exact ⟨fun _ _ => 1, rfl⟩

theorem orthogonalProjectionOperator_fixes_members
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (K : Submodule ℝ E)
    (x : E) (hx : x ∈ K) :
    HDP.orthogonalProjectionOperator K x = x := by
  exact K.starProjection_eq_self_iff.mpr hx

/-! ## Remaining concrete structure/value witnesses -/

theorem defaultUnitDirection_is_nonzero :
    ‖((HDP.defaultUnitDirection (E := ℝ) :
        Metric.sphere (0 : ℝ) 1) : ℝ)‖ = 1 ∧
      ((HDP.defaultUnitDirection (E := ℝ) :
        Metric.sphere (0 : ℝ) 1) : ℝ) ≠ 0 := by
  have hnorm :
      ‖((HDP.defaultUnitDirection (E := ℝ) :
          Metric.sphere (0 : ℝ) 1) : ℝ)‖ = 1 := by
    simpa [Metric.mem_sphere, Real.dist_eq] using
      (HDP.defaultUnitDirection (E := ℝ)).property
  exact ⟨hnorm, by
    intro hzero
    rw [hzero, norm_zero] at hnorm
    norm_num at hnorm⟩

theorem minimalFiniteNet_retains_cover_fields
    {X : Type*} [PseudoMetricSpace X]
    (ε : NNReal) (K : Set X)
    (hfinite : Metric.coveringNumber ε K ≠ ⊤) :
    (HDP.minimalFiniteNet ε K hfinite).points ⊆ K ∧
      Metric.IsCover ε
        K (HDP.minimalFiniteNet ε K hfinite).points := by
  exact ⟨(HDP.minimalFiniteNet ε K hfinite).subset,
    (HDP.minimalFiniteNet ε K hfinite).isCover⟩

theorem truncateNorm_is_identity_at_its_norm
    (B : Matrix (Fin 1) (Fin 1) ℂ) :
    MatrixConcentration.truncateNorm ‖B‖ B = B := by
  rw [MatrixConcentration.truncateNorm, if_pos le_rfl]

theorem sublinearFunctional_toFun_has_nonzero_model :
    (HDP.Chapter9.innerSublinearFunctional (1 : ℝ)).toFun 1 = 1 ∧
      (HDP.Chapter9.innerSublinearFunctional (1 : ℝ)).toFun 0 = 0 := by
  norm_num [HDP.Chapter9.innerSublinearFunctional]

theorem pair_distance_le_setKernelSectionDiameterENN
    {Ω : Type} {m n : ℕ}
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
    (T : Set (EuclideanSpace ℝ (Fin n))) (ω : Ω)
    {x y : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ T) (hy : y ∈ T)
    (hx0 : HDP.Chapter9.matrixAction A x ω = 0)
    (hy0 : HDP.Chapter9.matrixAction A y ω = 0) :
    ENNReal.ofReal ‖x - y‖ ≤
      HDP.Chapter9.setKernelSectionDiameterENN A T ω := by
  unfold HDP.Chapter9.setKernelSectionDiameterENN
  exact le_iSup_of_le x (le_iSup_of_le hx
    (le_iSup_of_le y (le_iSup_of_le hy
      (le_iSup_of_le hx0 (le_iSup_of_le hy0 le_rfl)))))

/-! ## Residual-closure witnesses -/

theorem booleanClassUniformDeviation_singleton_bool_is_one :
    let F : HDP.BooleanClass Bool := {{true}}
    HDP.Chapter8.booleanClassUniformDeviation
      (Measure.dirac false) (fun _ : Fin 1 => true) F = 1 := by
  dsimp
  unfold HDP.Chapter8.booleanClassUniformDeviation
  rw [show Set.range
      (fun u : ({{true}} : HDP.BooleanClass Bool) =>
        |HDP.Chapter8.booleanSetDeviation (Measure.dirac false)
          (fun _ : Fin 1 => true) u.1|) = {1} by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      have hu : u.1 = ({true} : Set Bool) := by
        exact Set.mem_singleton_iff.mp u.2
      simp [hu, HDP.Chapter8.booleanSetDeviation,
        HDP.Chapter8.empiricalAverage,
        HDP.Chapter8.booleanSetIndicator, measureReal_def]
    · intro hx
      have hx1 : x = 1 := by simpa using hx
      subst x
      refine ⟨⟨{true}, by simp⟩, ?_⟩
      simp [HDP.Chapter8.booleanSetDeviation,
        HDP.Chapter8.empiricalAverage,
        HDP.Chapter8.booleanSetIndicator, measureReal_def]]
  simp

theorem canonicalProcessEDistance_bool_gaussian_is_one :
    let a : Bool → ℝ := fun b => if b then 1 else 0
    HDP.Chapter8.canonicalProcessEDistance
      (HDP.Chapter7.canonicalGaussianProcess a)
      (ProbabilityTheory.stdGaussian ℝ)
      false true = 1 := by
  dsimp
  unfold HDP.Chapter8.canonicalProcessEDistance
  rw [HDP.Chapter7.canonicalGaussianProcess_increment]
  norm_num

theorem hasSubGaussianIncrementsWith_gaussian_positive_and_zero_fails :
    let a : Bool → ℝ := fun b => if b then 1 else 0
    let X := HDP.Chapter7.canonicalGaussianProcess a
    let d := HDP.processIncrement X (ProbabilityTheory.stdGaussian ℝ)
    HDP.HasSubGaussianIncrementsWith X
        (ProbabilityTheory.stdGaussian ℝ) d
        (Real.sqrt (8 / 3)) ∧
      ¬ HDP.HasSubGaussianIncrementsWith X
        (ProbabilityTheory.stdGaussian ℝ) d 0 := by
  dsimp
  constructor
  · exact
      HDP.Chapter7.canonicalGaussianProcess_hasSubGaussianIncrementsWith
        (fun b : Bool => if b then (1 : ℝ) else 0)
  · intro hzero
    have hbound := (hzero.2 false true).2
    let v : ℝ := (if true then 1 else 0) - (if false then 1 else 0)
    have hv := HDP.standardGaussian_inner_subGaussian v
    have hfun :
        (fun g : ℝ =>
          HDP.Chapter7.canonicalGaussianProcess
              (fun b : Bool => if b then (1 : ℝ) else 0) true g -
            HDP.Chapter7.canonicalGaussianProcess
              (fun b : Bool => if b then (1 : ℝ) else 0) false g) =
          (fun g : ℝ => inner ℝ v g) := by
      funext g
      simp [HDP.Chapter7.canonicalGaussianProcess, v]
    rw [hfun, hv.2] at hbound
    norm_num [v] at hbound
    exact (not_le_of_gt (by positivity)) hbound

theorem randomMatrix_subGaussianEntries_standardGaussian_nonconstant :
    let A : HDP.RandomMatrix Unit Unit ℝ := fun ω _ _ => ω
    A.SubGaussianEntries (ProbabilityTheory.stdGaussian ℝ) ∧
      A 0 () () ≠ A 1 () () := by
  dsimp
  constructor
  · intro _ _
    simpa using
      (HDP.standardGaussian_inner_subGaussian (1 : ℝ)).1
  · norm_num

theorem randomMatrix_independentEntries_product_and_dependent_contrast :
    let μbit : Measure Bool := HDP.Chapter3.bernoulliMaskMeasure
    let A : HDP.RandomMatrix Unit Bool ((Unit × Bool) → Bool) :=
      fun ω i j => if ω (i, j) then 1 else 0
    let B : HDP.RandomMatrix Unit Bool Bool :=
      fun ω _ _ => if ω then 1 else 0
    A.IndependentEntries (Measure.pi fun _ : Unit × Bool => μbit) ∧
      ¬ B.IndependentEntries μbit := by
  dsimp
  constructor
  · unfold HDP.RandomMatrix.IndependentEntries
    have hcoord :=
      ProbabilityTheory.iIndepFun_pi
        (μ := fun _ : Unit × Bool =>
          HDP.Chapter3.bernoulliMaskMeasure)
        (X := fun _ : Unit × Bool => id)
        (fun _ => aemeasurable_id)
    have hreal :
        ProbabilityTheory.iIndepFun
          (fun i : Unit × Bool =>
            fun ω : (Unit × Bool) → Bool =>
              if ω i then (1 : ℝ) else 0)
          (Measure.pi fun _ : Unit × Bool =>
            HDP.Chapter3.bernoulliMaskMeasure) :=
      hcoord.comp
        (fun _ : Unit × Bool => fun b : Bool =>
          if b then (1 : ℝ) else 0)
        (fun _ => by fun_prop)
    simpa [Function.comp_def] using hreal
  · intro hdep
    unfold HDP.RandomMatrix.IndependentEntries at hdep
    have hpair := hdep.indepFun
      (i := ((), false)) (j := ((), true)) (by decide)
    have heq := hpair.measure_inter_preimage_eq_mul
      ({0} : Set ℝ) ({0} : Set ℝ)
      (by measurability) (by measurability)
    have hpre :
        (fun ω : Bool => if ω then (1 : ℝ) else 0) ⁻¹'
            ({0} : Set ℝ) = {false} := by
      ext b
      cases b <;> simp
    rw [hpre, Set.inter_self] at heq
    rw [HDP.Chapter3.bernoulliMaskMeasure_false] at heq
    have heqReal := congrArg ENNReal.toReal heq
    norm_num at heqReal

theorem subGaussianVector_identity_standardGaussian_nonconstant :
    let E := EuclideanSpace ℝ (Fin 1)
    let X : E → E := id
    HDP.SubGaussianVector X (ProbabilityTheory.stdGaussian E) ∧
      X 0 ≠ X (EuclideanSpace.single (0 : Fin 1) 1) := by
  dsimp
  constructor
  · intro u
    simpa [real_inner_comm] using
      (HDP.standardGaussian_inner_subGaussian u).1
  · intro h
    have happ := congrArg
      (fun x : EuclideanSpace ℝ (Fin 1) => x (0 : Fin 1)) h
    norm_num at happ

theorem dvoretzkyMilmanSetConclusion_closedBall_nontrivial :
    let E := EuclideanSpace ℝ (Fin 1)
    let S : Set E := Metric.closedBall 0 1
    HDP.Chapter9.DvoretzkyMilmanSetConclusion S 1 1 ∧
      ¬ HDP.Chapter9.DvoretzkyMilmanSetConclusion S 1 0 := by
  dsimp
  have hhull :
      HDP.Chapter9.closedConvexHullSet
          (Metric.closedBall
            (0 : EuclideanSpace ℝ (Fin 1)) 1) =
        Metric.closedBall 0 1 := by
    apply Set.Subset.antisymm
    · exact closedConvexHull_min Set.Subset.rfl
        (convex_closedBall 0 1) Metric.isClosed_closedBall
    · exact subset_closedConvexHull
  constructor
  · unfold HDP.Chapter9.DvoretzkyMilmanSetConclusion
    rw [hhull]
    exact ⟨Set.Subset.rfl, fun _ => Set.Subset.rfl⟩
  · intro hbad
    unfold HDP.Chapter9.DvoretzkyMilmanSetConclusion at hbad
    rw [hhull] at hbad
    let e : EuclideanSpace ℝ (Fin 1) :=
      EuclideanSpace.single (0 : Fin 1) 1
    have he : e ∈
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1 := by
      simp [e]
    have hezero := hbad.1 he
    simp [Metric.mem_closedBall, dist_eq_norm, e] at hezero

theorem setWidthEffectiveDimension_pair_positive_and_singleton_zero :
    let E := EuclideanSpace ℝ (Fin 1)
    let e : E := EuclideanSpace.single (0 : Fin 1) 1
    let X : Set E := {0, e}
    0 < HDP.Chapter9.setWidthEffectiveDimension X ∧
      HDP.Chapter9.setWidthEffectiveDimension ({0} : Set E) = 0 := by
  dsimp
  let e : EuclideanSpace ℝ (Fin 1) :=
    EuclideanSpace.single (0 : Fin 1) 1
  let X : Set (EuclideanSpace ℝ (Fin 1)) := {0, e}
  have heNorm : ‖e‖ = 1 := by simp [e]
  have hdiam : Metric.diam X = 1 := by
    rw [show X = ({0, e} :
      Set (EuclideanSpace ℝ (Fin 1))) by rfl, Metric.diam_pair]
    simpa [dist_eq_norm, heNorm]
  have hbounded : Bornology.IsBounded X :=
    ((Set.finite_singleton e).insert 0).isBounded
  have hwne :
      HDP.Chapter8.euclideanSetGaussianWidthENN X ≠ ⊤ :=
    HDP.Chapter8.euclideanSetGaussianWidthENN_ne_top
      (by exact ⟨0, by simp [X]⟩) hbounded
  have hlower :=
    HDP.Chapter8.euclideanSetGaussianWidthENN_lower_diameter hbounded
  have hlowerReal := ENNReal.toReal_mono hwne hlower
  rw [ENNReal.toReal_ofReal (by
    rw [hdiam]
    positivity)] at hlowerReal
  have hwpos :
      0 < HDP.Chapter8.euclideanSetGaussianWidth X := by
    change 0 <
      (HDP.Chapter8.euclideanSetGaussianWidthENN X).toReal
    rw [hdiam] at hlowerReal
    exact lt_of_lt_of_le (by positivity) hlowerReal
  constructor
  · rw [HDP.Chapter9.setWidthEffectiveDimension, if_neg (by
      rw [hdiam]
      norm_num)]
    exact div_pos (sq_pos_of_pos hwpos) (sq_pos_of_pos (by
      rw [hdiam]
      norm_num))
  · simp [HDP.Chapter9.setWidthEffectiveDimension, Metric.diam_singleton]

theorem raw_subGaussian_subExponential_measure_mass_contrast :
    let X : Unit → ℝ := fun _ => 0
    let μ1 : Measure Unit := Measure.dirac ()
    let μ3 : Measure Unit := (3 : ℝ≥0∞) • Measure.dirac ()
    (HDP.SubGaussian X μ1 ∧ HDP.SubExponential X μ1) ∧
      (¬ HDP.SubGaussian X μ3 ∧ ¬ HDP.SubExponential X μ3) := by
  dsimp
  constructor
  · constructor
    · refine ⟨1, one_pos, ?_⟩
      simp [HDP.psi2MGF]
    · refine ⟨1, one_pos, ?_⟩
      simp [HDP.psi1MGF]
  · constructor
    · rintro ⟨K, hK, hle⟩
      have hmass :
          HDP.psi2MGF (fun _ : Unit => (0 : ℝ))
              ((3 : ℝ≥0∞) • Measure.dirac ()) K = 3 := by
        simp [HDP.psi2MGF]
      rw [hmass] at hle
      norm_num at hle
    · rintro ⟨K, hK, hle⟩
      have hmass :
          HDP.psi1MGF (fun _ : Unit => (0 : ℝ))
              ((3 : ℝ≥0∞) • Measure.dirac ()) K = 3 := by
        simp [HDP.psi1MGF]
      rw [hmass] at hle
      norm_num at hle

end HDP.Verification.V7
