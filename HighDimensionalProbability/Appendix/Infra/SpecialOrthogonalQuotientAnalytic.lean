import HighDimensionalProbability.Appendix.Infra.SpecialOrthogonalQuotientGeometry
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Analytic descent from the special orthogonal group to a coordinate quotient

This module constructs a differentiable regularized representative of the
conditional Haar square average, proves its tangent-energy bound by
conditional Cauchy--Schwarz, integrates the bound using Haar invariance, and
removes the positive regularization by continuity of Boltzmann entropy.
-/

open Matrix MeasureTheory
open scoped BigOperators RealInnerProductSpace Topology

namespace HDP.Appendix.SpecialOrthogonal

noncomputable section

local instance matrixSecondCountableTopologyAnalytic (n : ℕ) :
    SecondCountableTopology
      (Matrix (Fin n) (Fin n) ℝ) :=
  inferInstanceAs
    (SecondCountableTopology (Fin n → Fin n → ℝ))

local instance specialOrthogonalSecondCountableTopologyAnalytic (n : ℕ) :
    SecondCountableTopology
      (Matrix.specialOrthogonalGroup (Fin n) ℝ) :=
  TopologicalSpace.secondCountableTopology_induced
    (Matrix.specialOrthogonalGroup (Fin n) ℝ)
    (Matrix (Fin n) (Fin n) ℝ) Subtype.val

theorem contDiff_one_parametricIntegral_of_compact
    {E α : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [TopologicalSpace α] [T2Space α] [CompactSpace α]
    [SecondCountableTopology α]
    [MeasurableSpace α] [BorelSpace α]
    (μ : Measure α) [IsFiniteMeasure μ]
    (F : E → α → ℝ)
    (hF : Continuous (Function.uncurry F))
    (hFderiv :
      Continuous
        (Function.uncurry
          (fun x a => fderiv ℝ (fun y => F y a) x)))
    (hFdiff : ∀ a, Differentiable ℝ (fun x => F x a)) :
    ContDiff ℝ 1 (fun x => ∫ a, F x a ∂μ) := by
  rw [contDiff_one_iff_hasFDerivAt]
  let D : E → E →L[ℝ] ℝ :=
    fun x => ∫ a, fderiv ℝ (fun y => F y a) x ∂μ
  refine ⟨D, ?_, ?_⟩
  · unfold D
    simpa only [Measure.restrict_univ] using
      (continuous_parametric_integral_of_continuous
        (μ := μ) hFderiv (s := Set.univ) isCompact_univ)
  · intro x₀
    have hcompact :
        IsCompact
          (Metric.closedBall x₀ 1 ×ˢ (Set.univ : Set α)) :=
      (isCompact_closedBall x₀ 1).prod isCompact_univ
    have hbdd :
        BddAbove
          ((fun p : E × α =>
              ‖fderiv ℝ (fun y => F y p.2) p.1‖) ''
            (Metric.closedBall x₀ 1 ×ˢ
              (Set.univ : Set α))) :=
      IsCompact.bddAbove_image hcompact
        hFderiv.norm.continuousOn
    rcases bddAbove_def.mp hbdd with ⟨B, hB⟩
    have hF_meas :
        ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) μ := by
      filter_upwards []
      intro x
      exact
        (hF.comp
          (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    have hF_int : Integrable (F x₀) μ := by
      simpa [Function.uncurry_def, Function.comp_def] using
        (hF.comp
          (continuous_const.prodMk continuous_id)).continuousOn
          |>.integrableOn_compact (μ := μ) isCompact_univ
    have hF'_meas :
        AEStronglyMeasurable
          (fun a => fderiv ℝ (fun y => F y a) x₀) μ :=
      (hFderiv.comp
        (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    have h_bound :
        ∀ᵐ a ∂μ, ∀ x ∈ Metric.closedBall x₀ 1,
          ‖fderiv ℝ (fun y => F y a) x‖ ≤ B := by
      filter_upwards []
      intro a x hx
      exact hB _ ⟨(x, a), ⟨hx, Set.mem_univ a⟩, rfl⟩
    have hB_int : Integrable (fun _ : α => B) μ :=
      integrable_const B
    have h_diff :
        ∀ᵐ a ∂μ, ∀ x ∈ Metric.closedBall x₀ 1,
          HasFDerivAt (fun y => F y a)
            (fderiv ℝ (fun y => F y a) x) x := by
      filter_upwards []
      intro a x _
      exact (hFdiff a x).hasFDerivAt
    exact
      (hasFDerivAt_integral_of_dominated_of_fderiv_le
        (Metric.closedBall_mem_nhds x₀ (by norm_num))
        hF_meas hF_int hF'_meas h_bound hB_int h_diff)

theorem hasDerivAt_parametricIntegral_of_compact
    {α : Type*}
    [TopologicalSpace α] [T2Space α] [CompactSpace α]
    [SecondCountableTopology α]
    [MeasurableSpace α] [BorelSpace α]
    (μ : Measure α) [IsFiniteMeasure μ]
    (F F' : ℝ → α → ℝ)
    (hF : Continuous (Function.uncurry F))
    (hF' : Continuous (Function.uncurry F'))
    (hdiff : ∀ a t, HasDerivAt (fun s => F s a) (F' t a) t)
    (t₀ : ℝ) :
    HasDerivAt (fun t => ∫ a, F t a ∂μ)
      (∫ a, F' t₀ a ∂μ) t₀ := by
  have hcompact :
      IsCompact
        (Metric.closedBall t₀ 1 ×ˢ (Set.univ : Set α)) :=
    (isCompact_closedBall t₀ 1).prod isCompact_univ
  have hbdd :
      BddAbove
        ((fun p : ℝ × α => ‖F' p.1 p.2‖) ''
          (Metric.closedBall t₀ 1 ×ˢ
            (Set.univ : Set α))) :=
    IsCompact.bddAbove_image hcompact
      hF'.norm.continuousOn
  rcases bddAbove_def.mp hbdd with ⟨B, hB⟩
  have hF_meas :
      ∀ᶠ t in 𝓝 t₀, AEStronglyMeasurable (F t) μ := by
    filter_upwards []
    intro t
    exact
      (hF.comp
        (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hF_int : Integrable (F t₀) μ := by
    simpa [Function.uncurry_def, Function.comp_def] using
      (hF.comp
        (continuous_const.prodMk continuous_id)).continuousOn
        |>.integrableOn_compact (μ := μ) isCompact_univ
  have hF'_meas :
      AEStronglyMeasurable (F' t₀) μ :=
    (hF'.comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hbound :
      ∀ᵐ a ∂μ, ∀ t ∈ Metric.closedBall t₀ 1,
        ‖F' t a‖ ≤ B := by
    filter_upwards []
    intro a t ht
    exact hB _ ⟨(t, a), ⟨ht, Set.mem_univ a⟩, rfl⟩
  have hB_int : Integrable (fun _ : α => B) μ :=
    integrable_const B
  exact
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (Metric.closedBall_mem_nhds t₀ (by norm_num))
      hF_meas hF_int hF'_meas hbound hB_int
      (Filter.Eventually.of_forall fun a t _ => hdiff a t)).2

/-- Cauchy--Schwarz for continuous real functions on a compact probability
space, in the squared form used for conditional Haar averages. -/
theorem integral_mul_sq_le_integral_sq_mul_integral_sq
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
    [CompactSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (f g : α → ℝ) (hf : Continuous f) (hg : Continuous g) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤
      (∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 ∂μ) := by
  let F : C(α, ℝ) := ⟨f, hf⟩
  let G : C(α, ℝ) := ⟨g, hg⟩
  let F₂ : α →₂[μ] ℝ := ContinuousMap.toLp 2 μ ℝ F
  let G₂ : α →₂[μ] ℝ := ContinuousMap.toLp 2 μ ℝ G
  have h := real_inner_mul_inner_self_le F₂ G₂
  rw [MeasureTheory.ContinuousMap.inner_toLp μ F G,
    MeasureTheory.ContinuousMap.inner_toLp μ F F,
    MeasureTheory.ContinuousMap.inner_toLp μ G G] at h
  simpa only [F, G, F₂, G₂, RCLike.conj_to_real,
    ContinuousMap.coe_mk, pow_two, mul_comm] using h

/-- Vectorized right multiplication by a fixed square matrix. -/
noncomputable def vectorizedRightMulCLM {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℝ) :
    FrobeniusEuclidean n →L[ℝ] FrobeniusEuclidean n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y =>
        HDP.gaussianMatrixVectorize
          (HDP.gaussianMatrixUnvectorize y * B)
      map_add' := by
        intro y z
        apply WithLp.ofLp_injective
        ext p
        simp [HDP.gaussianMatrixVectorize,
          HDP.gaussianMatrixFlatten, WithLp.ofLp_toLp,
          HDP.gaussianMatrixUnvectorize, Matrix.mul_apply,
          Pi.add_apply, Finset.sum_add_distrib]
        simp_rw [add_mul]
        rw [Finset.sum_add_distrib]
      map_smul' := by
        intro c y
        apply WithLp.ofLp_injective
        ext p
        simp [HDP.gaussianMatrixVectorize,
          HDP.gaussianMatrixFlatten, WithLp.ofLp_toLp,
          HDP.gaussianMatrixUnvectorize, Matrix.mul_apply,
          Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        ring }

@[simp] lemma vectorizedRightMulCLM_apply {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℝ)
    (y : FrobeniusEuclidean n) :
    vectorizedRightMulCLM B y =
      HDP.gaussianMatrixVectorize
        (HDP.gaussianMatrixUnvectorize y * B) := rfl

lemma continuous_vectorizedRightMulCLM (n : ℕ) :
    Continuous
      (vectorizedRightMulCLM :
        Matrix (Fin n) (Fin n) ℝ →
          FrobeniusEuclidean n →L[ℝ] FrobeniusEuclidean n) := by
  rw [continuous_clm_apply]
  intro y
  apply (PiLp.continuous_toLp 2
    (fun _ : Fin n × Fin n => ℝ)).comp
  apply continuous_pi
  intro p
  simp only [vectorizedRightMulCLM_apply,
    HDP.gaussianMatrixVectorize, HDP.gaussianMatrixFlatten,
    Function.comp_apply, Matrix.mul_apply]
  fun_prop

/-- Ambient stabilizer average before descent to the quotient sphere. -/
noncomputable def quotientAmbientAverage
    (k : ℕ) (H : FrobeniusEuclidean (k + 3) → ℝ)
    (y : FrobeniusEuclidean (k + 3)) : ℝ :=
  ∫ V : Matrix.specialOrthogonalGroup (Fin (k + 2)) ℝ,
    H (vectorizedRightMulCLM
      (coordinateStabilizerMatrix
        (secondCoordinateIndex k) V.1) y) ^ 2
    ∂HDP.Chapter5.specialOrthogonalHaarMeasure (k + 2)

lemma contDiff_one_quotientAmbientAverage
    (k : ℕ) (H : FrobeniusEuclidean (k + 3) → ℝ)
    (hHdiff : Differentiable ℝ H)
    (hHderiv : Continuous (fderiv ℝ H)) :
    ContDiff ℝ 1 (quotientAmbientAverage k H) := by
  let μ :=
    HDP.Chapter5.specialOrthogonalHaarMeasure (k + 2)
  let K :
      Matrix.specialOrthogonalGroup (Fin (k + 2)) ℝ →
        Matrix (Fin (k + 3)) (Fin (k + 3)) ℝ :=
    fun V =>
      coordinateStabilizerMatrix
        (secondCoordinateIndex k) V.1
  let L :
      Matrix.specialOrthogonalGroup (Fin (k + 2)) ℝ →
        FrobeniusEuclidean (k + 3) →L[ℝ]
          FrobeniusEuclidean (k + 3) :=
    fun V => vectorizedRightMulCLM (K V)
  let F :
      FrobeniusEuclidean (k + 3) →
        Matrix.specialOrthogonalGroup (Fin (k + 2)) ℝ → ℝ :=
    fun y V => H (L V y) ^ 2
  have hK : Continuous K := by
    dsimp [K]
    exact continuous_subtype_val.comp
      (continuous_coordinateStabilizerHom
        (secondCoordinateIndex k))
  have hL : Continuous L := by
    exact
      (continuous_vectorizedRightMulCLM (k + 3)).comp hK
  have hpoint :
      Continuous (Function.uncurry (fun y V => L V y)) := by
    exact (hL.comp continuous_snd).clm_apply continuous_fst
  have hF : Continuous (Function.uncurry F) := by
    dsimp [F]
    exact (hHdiff.continuous.comp hpoint).pow 2
  have hFdiff :
      ∀ V, Differentiable ℝ (fun y => F y V) := by
    intro V
    dsimp [F]
    exact (hHdiff.comp (L V).differentiable).pow 2
  have hfderiv :
      ∀ y V,
        fderiv ℝ (fun z => F z V) y =
          (2 * H (L V y)) •
            ((fderiv ℝ H (L V y)).comp (L V)) := by
    intro y V
    dsimp [F]
    simpa [Function.comp_def, mul_comm] using
      ((hHdiff (L V y)).hasFDerivAt.comp y
        (L V).hasFDerivAt).pow 2 |>.fderiv
  have hFderiv :
      Continuous
        (Function.uncurry
          (fun y V => fderiv ℝ (fun z => F z V) y)) := by
    simp_rw [hfderiv]
    have hleft :
        Continuous
          (fun p :
              FrobeniusEuclidean (k + 3) ×
                Matrix.specialOrthogonalGroup (Fin (k + 2)) ℝ =>
            2 * H (L p.2 p.1)) := by
      exact continuous_const.mul
        (hHdiff.continuous.comp hpoint)
    have hright :
        Continuous
          (fun p :
              FrobeniusEuclidean (k + 3) ×
                Matrix.specialOrthogonalGroup (Fin (k + 2)) ℝ =>
            (fderiv ℝ H (L p.2 p.1)).comp (L p.2)) := by
      exact
        (hHderiv.comp hpoint).clm_comp
          (hL.comp continuous_snd)
    exact hleft.smul hright
  unfold quotientAmbientAverage
  simpa only [μ, K, L, F] using
    contDiff_one_parametricIntegral_of_compact
      μ F hF hFderiv hFdiff

lemma quotientAmbientAverage_vectorize_specialOrthogonal
    (k : ℕ) (H : FrobeniusEuclidean (k + 3) → ℝ)
    (hH : Continuous H)
    (U : Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ) :
    quotientAmbientAverage k H
        (HDP.gaussianMatrixVectorize U.1) =
      rightAverage
        (coordinateStabilizerMeasure (secondCoordinateIndex k))
        (fun W => H (HDP.gaussianMatrixVectorize W.1) ^ 2) U := by
  unfold quotientAmbientAverage rightAverage
  rw [integral_coordinateStabilizerMeasure_of_continuous]
  · congr 1
  · have hmul :
        Continuous
          (fun W :
              Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ =>
            (U * W).1) :=
        continuous_subtype_val.comp (by fun_prop)
    exact
      (hH.comp
        (continuous_gaussianMatrixVectorize.comp hmul)).pow 2

lemma quotientAmbientAverage_nonneg
    (k : ℕ) (H : FrobeniusEuclidean (k + 3) → ℝ)
    (y : FrobeniusEuclidean (k + 3)) :
    0 ≤ quotientAmbientAverage k H y := by
  unfold quotientAmbientAverage
  exact integral_nonneg (fun _ => sq_nonneg _)

lemma contDiffAt_vectorize_quotientPlusSectionMatrix
    (k : ℕ) (y : EuclideanSpace ℝ (Fin (k + 3)))
    (hy : quotientReference k + y ≠ 0) :
    ContDiffAt ℝ ⊤
      (fun z =>
        HDP.gaussianMatrixVectorize
          (quotientPlusSectionMatrix k z)) y := by
  have hdot :
      euclideanDot
          (quotientReference k + y)
          (quotientReference k + y) ≠ 0 :=
    ne_of_gt (euclideanDot_self_pos hy)
  unfold quotientPlusSectionMatrix
    HDP.gaussianMatrixVectorize HDP.gaussianMatrixFlatten
  apply
    (PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Fin (k + 3) × Fin (k + 3) => ℝ)).symm.contDiff.contDiffAt.comp
      y
  rw [contDiffAt_pi]
  intro p
  simp only [Matrix.mul_apply, householderMatrix,
    Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, smul_eq_mul, euclideanDot]
  exact ContDiffAt.sum fun c _ => by
    fun_prop (disch := aesop)

lemma contDiffAt_vectorize_quotientMinusSectionMatrix
    (k : ℕ) (y : EuclideanSpace ℝ (Fin (k + 3)))
    (hy : quotientReference k - y ≠ 0) :
    ContDiffAt ℝ ⊤
      (fun z =>
        HDP.gaussianMatrixVectorize
          (quotientMinusSectionMatrix k z)) y := by
  have hdot :
      euclideanDot
          (quotientReference k - y)
          (quotientReference k - y) ≠ 0 :=
    ne_of_gt (euclideanDot_self_pos hy)
  unfold quotientMinusSectionMatrix
    HDP.gaussianMatrixVectorize HDP.gaussianMatrixFlatten
  apply
    (PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Fin (k + 3) × Fin (k + 3) => ℝ)).symm.contDiff.contDiffAt.comp
      y
  rw [contDiffAt_pi]
  intro p
  simp only [Matrix.mul_apply, householderMatrix,
    Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, smul_eq_mul, euclideanDot]
  exact ContDiffAt.sum fun c _ => by
    fun_prop (disch := aesop)

/-- The two local quotient representatives obtained from the Householder
sections. -/
noncomputable def quotientPlusAverage
    (k : ℕ) (H : FrobeniusEuclidean (k + 3) → ℝ)
    (y : EuclideanSpace ℝ (Fin (k + 3))) : ℝ :=
  quotientAmbientAverage k H
    (HDP.gaussianMatrixVectorize
      (quotientPlusSectionMatrix k y))

/-- The ambient quotient average evaluated through the negative Householder section. -/
noncomputable def quotientMinusAverage
    (k : ℕ) (H : FrobeniusEuclidean (k + 3) → ℝ)
    (y : EuclideanSpace ℝ (Fin (k + 3))) : ℝ :=
  quotientAmbientAverage k H
    (HDP.gaussianMatrixVectorize
      (quotientMinusSectionMatrix k y))

lemma contDiffAt_one_quotientPlusAverage
    (k : ℕ) (H : FrobeniusEuclidean (k + 3) → ℝ)
    (hHdiff : Differentiable ℝ H)
    (hHderiv : Continuous (fderiv ℝ H))
    (y : EuclideanSpace ℝ (Fin (k + 3)))
    (hy : quotientReference k + y ≠ 0) :
    ContDiffAt ℝ 1 (quotientPlusAverage k H) y := by
  unfold quotientPlusAverage
  exact
    (contDiff_one_quotientAmbientAverage k H hHdiff hHderiv).contDiffAt.comp
      y
      ((contDiffAt_vectorize_quotientPlusSectionMatrix k y hy).of_le
        (by simp))

lemma contDiffAt_one_quotientMinusAverage
    (k : ℕ) (H : FrobeniusEuclidean (k + 3) → ℝ)
    (hHdiff : Differentiable ℝ H)
    (hHderiv : Continuous (fderiv ℝ H))
    (y : EuclideanSpace ℝ (Fin (k + 3)))
    (hy : quotientReference k - y ≠ 0) :
    ContDiffAt ℝ 1 (quotientMinusAverage k H) y := by
  unfold quotientMinusAverage
  exact
    (contDiff_one_quotientAmbientAverage k H hHdiff hHderiv).contDiffAt.comp
      y
      ((contDiffAt_vectorize_quotientMinusSectionMatrix k y hy).of_le
        (by simp))

/-- Householder sections bundled as special-orthogonal matrices on their
respective sphere charts. -/
noncomputable def quotientPlusSection
    (k : ℕ)
    (y : Metric.sphere
      (0 : EuclideanSpace ℝ (Fin (k + 3))) 1)
    (hy : quotientReference k + (y : EuclideanSpace ℝ _) ≠ 0) :
    Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ :=
  ⟨quotientPlusSectionMatrix k y,
    quotientPlusSectionMatrix_mem_specialOrthogonal k y hy⟩

/-- The negative Householder section bundled as a special-orthogonal matrix. -/
noncomputable def quotientMinusSection
    (k : ℕ)
    (y : Metric.sphere
      (0 : EuclideanSpace ℝ (Fin (k + 3))) 1)
    (hy : quotientReference k - (y : EuclideanSpace ℝ _) ≠ 0) :
    Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ :=
  ⟨quotientMinusSectionMatrix k y,
    quotientMinusSectionMatrix_mem_specialOrthogonal k y hy⟩

lemma quotientPlusAverage_eq_rightAverage
    (k : ℕ) (H : FrobeniusEuclidean (k + 3) → ℝ)
    (hH : Continuous H)
    (y : Metric.sphere
      (0 : EuclideanSpace ℝ (Fin (k + 3))) 1)
    (hy : quotientReference k + (y : EuclideanSpace ℝ _) ≠ 0) :
    quotientPlusAverage k H y =
      rightAverage
        (coordinateStabilizerMeasure (secondCoordinateIndex k))
        (fun W => H (HDP.gaussianMatrixVectorize W.1) ^ 2)
        (quotientPlusSection k y hy) := by
  exact quotientAmbientAverage_vectorize_specialOrthogonal
    k H hH (quotientPlusSection k y hy)

lemma quotientMinusAverage_eq_rightAverage
    (k : ℕ) (H : FrobeniusEuclidean (k + 3) → ℝ)
    (hH : Continuous H)
    (y : Metric.sphere
      (0 : EuclideanSpace ℝ (Fin (k + 3))) 1)
    (hy : quotientReference k - (y : EuclideanSpace ℝ _) ≠ 0) :
    quotientMinusAverage k H y =
      rightAverage
        (coordinateStabilizerMeasure (secondCoordinateIndex k))
        (fun W => H (HDP.gaussianMatrixVectorize W.1) ^ 2)
        (quotientMinusSection k y hy) := by
  exact quotientAmbientAverage_vectorize_specialOrthogonal
    k H hH (quotientMinusSection k y hy)

lemma quotientPlusAverage_eq_quotientMinusAverage
    (k : ℕ) (H : FrobeniusEuclidean (k + 3) → ℝ)
    (hH : Continuous H)
    (y : Metric.sphere
      (0 : EuclideanSpace ℝ (Fin (k + 3))) 1)
    (hplus :
      quotientReference k + (y : EuclideanSpace ℝ _) ≠ 0)
    (hminus :
      quotientReference k - (y : EuclideanSpace ℝ _) ≠ 0) :
    quotientPlusAverage k H y =
      quotientMinusAverage k H y := by
  rw [quotientPlusAverage_eq_rightAverage k H hH y hplus,
    quotientMinusAverage_eq_rightAverage k H hH y hminus]
  apply rightAverage_coordinateStabilizer_eq_of_mulVec_eq
    (secondCoordinateIndex k)
    (fun W => H (HDP.gaussianMatrixVectorize W.1) ^ 2)
  · exact (hH.comp
      (continuous_gaussianMatrixVectorize.comp
        continuous_subtype_val)).pow 2
  · change
      quotientPlusSectionMatrix k y *ᵥ
          (fun a => quotientReference k a) =
        quotientMinusSectionMatrix k y *ᵥ
          (fun a => quotientReference k a)
    rw [quotientPlusSectionMatrix_mulVec_reference
        k y hplus,
      quotientMinusSectionMatrix_mulVec_reference
        k y hminus]

lemma euclideanDot_quotientReference_self (k : ℕ) :
    euclideanDot (quotientReference k)
      (quotientReference k) = 1 := by
  rw [euclideanDot_self_eq_norm_sq,
    norm_quotientReference]
  norm_num

lemma euclideanDot_quotientReference_neg_self (k : ℕ) :
    euclideanDot (quotientReference k)
      (-quotientReference k) = -1 := by
  unfold euclideanDot
  calc
    (∑ a : Fin (k + 3),
        quotientReference k a * (-quotientReference k) a) =
        -(∑ a : Fin (k + 3),
          quotientReference k a * quotientReference k a) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro a _
      change
        quotientReference k a * (-quotientReference k a) =
          -(quotientReference k a * quotientReference k a)
      ring
    _ = -1 := by
      rw [show
          (∑ a : Fin (k + 3),
            quotientReference k a * quotientReference k a) =
            euclideanDot (quotientReference k)
              (quotientReference k) by rfl,
        euclideanDot_quotientReference_self]

/-- Smooth partition coordinate separating the two antipodal chart
singularities.  It is negative near `-r` and greater than one near `r`. -/
noncomputable def quotientPartitionArgument
    (k : ℕ) (y : EuclideanSpace ℝ (Fin (k + 3))) : ℝ :=
  2 * euclideanDot (quotientReference k) y + 3 / 2

/-- The smooth transition weight used to combine the two quotient charts. -/
noncomputable def quotientPartitionWeight
    (k : ℕ) (y : EuclideanSpace ℝ (Fin (k + 3))) : ℝ :=
  Real.smoothTransition (quotientPartitionArgument k y)

lemma contDiff_quotientPartitionArgument (k : ℕ) :
    ContDiff ℝ ⊤ (quotientPartitionArgument k) := by
  unfold quotientPartitionArgument euclideanDot
  fun_prop

lemma contDiff_quotientPartitionWeight (k : ℕ) :
    ContDiff ℝ 1 (quotientPartitionWeight k) := by
  unfold quotientPartitionWeight
  exact (Real.smoothTransition.contDiff (n := 1)).comp
    ((contDiff_quotientPartitionArgument k).of_le (by simp))

@[simp] lemma quotientPartitionArgument_neg_reference (k : ℕ) :
    quotientPartitionArgument k (-quotientReference k) = -1 / 2 := by
  rw [quotientPartitionArgument,
    euclideanDot_quotientReference_neg_self]
  ring

@[simp] lemma quotientPartitionArgument_reference (k : ℕ) :
    quotientPartitionArgument k (quotientReference k) = 7 / 2 := by
  rw [quotientPartitionArgument,
    euclideanDot_quotientReference_self]
  ring

/-- The positive-chart quotient average multiplied by its partition weight. -/
noncomputable def quotientPlusWeighted
    (k : ℕ) (H : FrobeniusEuclidean (k + 3) → ℝ)
    (y : EuclideanSpace ℝ (Fin (k + 3))) : ℝ :=
  quotientPartitionWeight k y * quotientPlusAverage k H y

/-- The negative-chart quotient average multiplied by the complementary partition weight. -/
noncomputable def quotientMinusWeighted
    (k : ℕ) (H : FrobeniusEuclidean (k + 3) → ℝ)
    (y : EuclideanSpace ℝ (Fin (k + 3))) : ℝ :=
  (1 - quotientPartitionWeight k y) *
    quotientMinusAverage k H y

lemma contDiffAt_one_quotientPlusWeighted
    (k : ℕ) (H : FrobeniusEuclidean (k + 3) → ℝ)
    (hHdiff : Differentiable ℝ H)
    (hHderiv : Continuous (fderiv ℝ H))
    (y : EuclideanSpace ℝ (Fin (k + 3))) :
    ContDiffAt ℝ 1 (quotientPlusWeighted k H) y := by
  by_cases hy :
      quotientReference k + y ≠ 0
  · exact
      (contDiff_quotientPartitionWeight k).contDiffAt.mul
        (contDiffAt_one_quotientPlusAverage
          k H hHdiff hHderiv y hy)
  · have hy' : y = -quotientReference k :=
      eq_neg_of_add_eq_zero_left (by
        simpa [add_comm] using (not_ne_iff.mp hy))
    have harg :
        quotientPartitionArgument k y < 0 := by
      rw [hy', quotientPartitionArgument_neg_reference]
      norm_num
    have hevent :
        ∀ᶠ z in 𝓝 y,
          quotientPartitionArgument k z < 0 :=
      (contDiff_quotientPartitionArgument k).continuous.continuousAt
        |>.preimage_mem_nhds (Iio_mem_nhds harg)
    refine
      (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hevent] with z hz
    simp only [quotientPlusWeighted,
      quotientPartitionWeight]
    rw [Real.smoothTransition.zero_of_nonpos hz.le,
      zero_mul]

lemma contDiffAt_one_quotientMinusWeighted
    (k : ℕ) (H : FrobeniusEuclidean (k + 3) → ℝ)
    (hHdiff : Differentiable ℝ H)
    (hHderiv : Continuous (fderiv ℝ H))
    (y : EuclideanSpace ℝ (Fin (k + 3))) :
    ContDiffAt ℝ 1 (quotientMinusWeighted k H) y := by
  by_cases hy :
      quotientReference k - y ≠ 0
  · exact
      (contDiffAt_const.sub
        (contDiff_quotientPartitionWeight k).contDiffAt).mul
        (contDiffAt_one_quotientMinusAverage
          k H hHdiff hHderiv y hy)
  · have hy' : y = quotientReference k := by
      exact (sub_eq_zero.mp (not_ne_iff.mp hy)).symm
    have harg :
        1 < quotientPartitionArgument k y := by
      rw [hy', quotientPartitionArgument_reference]
      norm_num
    have hevent :
        ∀ᶠ z in 𝓝 y,
          1 < quotientPartitionArgument k z :=
      (contDiff_quotientPartitionArgument k).continuous.continuousAt
        |>.preimage_mem_nhds (Ioi_mem_nhds harg)
    refine
      (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hevent] with z hz
    simp only [quotientMinusWeighted,
      quotientPartitionWeight]
    rw [Real.smoothTransition.one_of_one_le hz.le,
      sub_self, zero_mul]

/-- A global `C¹` ambient representative of the descended squared
stabilizer average. -/
noncomputable def quotientPatchedAverage
    (k : ℕ) (H : FrobeniusEuclidean (k + 3) → ℝ)
    (y : EuclideanSpace ℝ (Fin (k + 3))) : ℝ :=
  quotientPlusWeighted k H y + quotientMinusWeighted k H y

lemma contDiff_one_quotientPatchedAverage
    (k : ℕ) (H : FrobeniusEuclidean (k + 3) → ℝ)
    (hHdiff : Differentiable ℝ H)
    (hHderiv : Continuous (fderiv ℝ H)) :
    ContDiff ℝ 1 (quotientPatchedAverage k H) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  exact
    (contDiffAt_one_quotientPlusWeighted
      k H hHdiff hHderiv y).add
      (contDiffAt_one_quotientMinusWeighted
        k H hHdiff hHderiv y)

lemma quotientPlusAverage_eq_rightAverage_of_mulVec
    (k : ℕ) (H : FrobeniusEuclidean (k + 3) → ℝ)
    (hH : Continuous H)
    (y : Metric.sphere
      (0 : EuclideanSpace ℝ (Fin (k + 3))) 1)
    (hy : quotientReference k + (y : EuclideanSpace ℝ _) ≠ 0)
    (U : Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ)
    (hUy :
      U.1 *ᵥ (fun a => quotientReference k a) =
        fun a => (y : EuclideanSpace ℝ _) a) :
    quotientPlusAverage k H y =
      rightAverage
        (coordinateStabilizerMeasure (secondCoordinateIndex k))
        (fun W => H (HDP.gaussianMatrixVectorize W.1) ^ 2) U := by
  rw [quotientPlusAverage_eq_rightAverage k H hH y hy]
  apply rightAverage_coordinateStabilizer_eq_of_mulVec_eq
    (secondCoordinateIndex k)
    (fun W => H (HDP.gaussianMatrixVectorize W.1) ^ 2)
  · exact (hH.comp
      (continuous_gaussianMatrixVectorize.comp
        continuous_subtype_val)).pow 2
  · change
      quotientPlusSectionMatrix k y *ᵥ
          (fun a => quotientReference k a) =
        U.1 *ᵥ (fun a => quotientReference k a)
    rw [quotientPlusSectionMatrix_mulVec_reference
      k y hy, hUy]

lemma quotientMinusAverage_eq_rightAverage_of_mulVec
    (k : ℕ) (H : FrobeniusEuclidean (k + 3) → ℝ)
    (hH : Continuous H)
    (y : Metric.sphere
      (0 : EuclideanSpace ℝ (Fin (k + 3))) 1)
    (hy : quotientReference k - (y : EuclideanSpace ℝ _) ≠ 0)
    (U : Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ)
    (hUy :
      U.1 *ᵥ (fun a => quotientReference k a) =
        fun a => (y : EuclideanSpace ℝ _) a) :
    quotientMinusAverage k H y =
      rightAverage
        (coordinateStabilizerMeasure (secondCoordinateIndex k))
        (fun W => H (HDP.gaussianMatrixVectorize W.1) ^ 2) U := by
  rw [quotientMinusAverage_eq_rightAverage k H hH y hy]
  apply rightAverage_coordinateStabilizer_eq_of_mulVec_eq
    (secondCoordinateIndex k)
    (fun W => H (HDP.gaussianMatrixVectorize W.1) ^ 2)
  · exact (hH.comp
      (continuous_gaussianMatrixVectorize.comp
        continuous_subtype_val)).pow 2
  · change
      quotientMinusSectionMatrix k y *ᵥ
          (fun a => quotientReference k a) =
        U.1 *ᵥ (fun a => quotientReference k a)
    rw [quotientMinusSectionMatrix_mulVec_reference
      k y hy, hUy]

lemma quotientPatchedAverage_eq_rightAverage_of_mulVec
    (k : ℕ) (H : FrobeniusEuclidean (k + 3) → ℝ)
    (hH : Continuous H)
    (y : Metric.sphere
      (0 : EuclideanSpace ℝ (Fin (k + 3))) 1)
    (U : Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ)
    (hUy :
      U.1 *ᵥ (fun a => quotientReference k a) =
        fun a => (y : EuclideanSpace ℝ _) a) :
    quotientPatchedAverage k H y =
      rightAverage
        (coordinateStabilizerMeasure (secondCoordinateIndex k))
        (fun W => H (HDP.gaussianMatrixVectorize W.1) ^ 2) U := by
  let q :=
    rightAverage
      (coordinateStabilizerMeasure (secondCoordinateIndex k))
      (fun W => H (HDP.gaussianMatrixVectorize W.1) ^ 2) U
  by_cases hp :
      quotientReference k + (y : EuclideanSpace ℝ _) ≠ 0
  · have hplus :
        quotientPlusAverage k H y = q := by
      exact quotientPlusAverage_eq_rightAverage_of_mulVec
        k H hH y hp U hUy
    by_cases hm :
        quotientReference k - (y : EuclideanSpace ℝ _) ≠ 0
    · have hminus :
          quotientMinusAverage k H y = q := by
        exact quotientMinusAverage_eq_rightAverage_of_mulVec
          k H hH y hm U hUy
      unfold quotientPatchedAverage quotientPlusWeighted
        quotientMinusWeighted
      rw [hplus, hminus]
      ring
    · have hy :
          (y : EuclideanSpace ℝ (Fin (k + 3))) =
            quotientReference k := by
        exact (sub_eq_zero.mp (not_ne_iff.mp hm)).symm
      have hw : quotientPartitionWeight k y = 1 := by
        unfold quotientPartitionWeight
        rw [hy, quotientPartitionArgument_reference]
        exact Real.smoothTransition.one_of_one_le (by norm_num)
      unfold quotientPatchedAverage quotientPlusWeighted
        quotientMinusWeighted
      rw [hplus, hw]
      ring
  · have hyneg :
        (y : EuclideanSpace ℝ (Fin (k + 3))) =
          -quotientReference k :=
      eq_neg_of_add_eq_zero_left (by
        simpa [add_comm] using (not_ne_iff.mp hp))
    have hm :
        quotientReference k - (y : EuclideanSpace ℝ _) ≠ 0 := by
      intro hm
      have hypos :
          (y : EuclideanSpace ℝ (Fin (k + 3))) =
            quotientReference k :=
        (sub_eq_zero.mp hm).symm
      have hrneg :
          quotientReference k = -quotientReference k := by
        exact hypos.symm.trans hyneg
      have htwo :
          (2 : ℝ) • quotientReference k = 0 := by
        calc
          (2 : ℝ) • quotientReference k =
              quotientReference k + quotientReference k := by
                rw [two_smul]
          _ = -quotientReference k + quotientReference k :=
            congrArg
              (fun z => z + quotientReference k) hrneg
          _ = 0 := neg_add_cancel _
      have hrzero : quotientReference k = 0 :=
        (smul_eq_zero.mp htwo).resolve_left (by norm_num)
      exact quotientReference_ne_zero k hrzero
    have hminus :
        quotientMinusAverage k H y = q :=
      quotientMinusAverage_eq_rightAverage_of_mulVec
        k H hH y hm U hUy
    have hw : quotientPartitionWeight k y = 0 := by
      unfold quotientPartitionWeight
      rw [hyneg, quotientPartitionArgument_neg_reference]
      exact Real.smoothTransition.zero_of_nonpos (by norm_num)
    unfold quotientPatchedAverage quotientPlusWeighted
      quotientMinusWeighted
    rw [hminus, hw]
    ring

lemma quotientPatchedAverage_eq_rightAverage_orbit
    (k : ℕ) (H : FrobeniusEuclidean (k + 3) → ℝ)
    (hH : Continuous H)
    (U : Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ) :
    quotientPatchedAverage k H
        (specialOrthogonalSphereOrbit
          (coordinateSpherePoint (secondCoordinateIndex k)) U) =
      rightAverage
        (coordinateStabilizerMeasure (secondCoordinateIndex k))
        (fun W => H (HDP.gaussianMatrixVectorize W.1) ^ 2) U := by
  exact quotientPatchedAverage_eq_rightAverage_of_mulVec
    k H hH
    (specialOrthogonalSphereOrbit
      (coordinateSpherePoint (secondCoordinateIndex k)) U)
    U (by rfl)

lemma quotientPlusAverage_nonneg
    (k : ℕ) (H : FrobeniusEuclidean (k + 3) → ℝ)
    (y : EuclideanSpace ℝ (Fin (k + 3))) :
    0 ≤ quotientPlusAverage k H y := by
  exact quotientAmbientAverage_nonneg k H _

lemma quotientMinusAverage_nonneg
    (k : ℕ) (H : FrobeniusEuclidean (k + 3) → ℝ)
    (y : EuclideanSpace ℝ (Fin (k + 3))) :
    0 ≤ quotientMinusAverage k H y := by
  exact quotientAmbientAverage_nonneg k H _

lemma quotientPatchedAverage_nonneg
    (k : ℕ) (H : FrobeniusEuclidean (k + 3) → ℝ)
    (y : EuclideanSpace ℝ (Fin (k + 3))) :
    0 ≤ quotientPatchedAverage k H y := by
  unfold quotientPatchedAverage quotientPlusWeighted
    quotientMinusWeighted quotientPartitionWeight
  exact add_nonneg
    (mul_nonneg
      (Real.smoothTransition.nonneg _)
      (quotientPlusAverage_nonneg k H y))
    (mul_nonneg
      (sub_nonneg.mpr (Real.smoothTransition.le_one _))
      (quotientMinusAverage_nonneg k H y))

/-- A fixed outer cutoff which is identically one on the unit ball and
has compact support. -/
noncomputable def quotientOuterBump (k : ℕ) :
    ContDiffBump
      (0 : EuclideanSpace ℝ (Fin (k + 3))) where
  rIn := 2
  rOut := 3
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

@[simp] lemma quotientOuterBump_rIn (k : ℕ) :
    (quotientOuterBump k).rIn = 2 := rfl

@[simp] lemma quotientOuterBump_rOut (k : ℕ) :
    (quotientOuterBump k).rOut = 3 := rfl

lemma quotientOuterBump_eq_one_of_norm_le_one
    (k : ℕ) (y : EuclideanSpace ℝ (Fin (k + 3)))
    (hy : ‖y‖ ≤ 1) :
    quotientOuterBump k y = 1 := by
  apply (quotientOuterBump k).one_of_mem_closedBall
  simpa [Metric.mem_closedBall, dist_zero_right] using hy.trans (by norm_num)

@[simp] lemma quotientOuterBump_eq_one_on_sphere
    (k : ℕ)
    (y : Metric.sphere
      (0 : EuclideanSpace ℝ (Fin (k + 3))) 1) :
    quotientOuterBump k y = 1 := by
  apply quotientOuterBump_eq_one_of_norm_le_one
  simpa [Metric.mem_sphere, dist_zero_right] using y.2

/-- A compactly supported `C¹` representative of the positive
regularization `quotientPatchedAverage + ε`. -/
noncomputable def quotientRegularizedRepresentative
    (k : ℕ) (H : FrobeniusEuclidean (k + 3) → ℝ)
    (ε : ℝ) (y : EuclideanSpace ℝ (Fin (k + 3))) : ℝ :=
  quotientOuterBump k y *
    Real.sqrt (quotientPatchedAverage k H y + ε)

lemma contDiff_one_quotientRegularizedRepresentative
    (k : ℕ) (H : FrobeniusEuclidean (k + 3) → ℝ)
    (hHdiff : Differentiable ℝ H)
    (hHderiv : Continuous (fderiv ℝ H))
    {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ 1 (quotientRegularizedRepresentative k H ε) := by
  unfold quotientRegularizedRepresentative
  apply (quotientOuterBump k).contDiff.mul
  apply
    ((contDiff_one_quotientPatchedAverage k H hHdiff hHderiv).add
      contDiff_const).sqrt
  intro y
  exact ne_of_gt
    (lt_of_lt_of_le hε
      (le_add_of_nonneg_left
        (quotientPatchedAverage_nonneg k H y)))

lemma quotientRegularizedRepresentative_hasCompactSupport
    (k : ℕ) (H : FrobeniusEuclidean (k + 3) → ℝ)
    (ε : ℝ) :
    HasCompactSupport
      (quotientRegularizedRepresentative k H ε) := by
  unfold quotientRegularizedRepresentative
  exact (quotientOuterBump k).hasCompactSupport.mul_right

lemma quotientRegularizedRepresentative_sq_on_sphere
    (k : ℕ) (H : FrobeniusEuclidean (k + 3) → ℝ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (y : Metric.sphere
      (0 : EuclideanSpace ℝ (Fin (k + 3))) 1) :
    quotientRegularizedRepresentative k H ε y ^ 2 =
      quotientPatchedAverage k H y + ε := by
  rw [quotientRegularizedRepresentative,
    quotientOuterBump_eq_one_on_sphere]
  simp only [one_mul]
  exact Real.sq_sqrt
    (add_nonneg (quotientPatchedAverage_nonneg k H y) hε)

lemma quotientRegularizedRepresentative_exists_bounds
    (k : ℕ) (H : FrobeniusEuclidean (k + 3) → ℝ)
    (hHdiff : Differentiable ℝ H)
    (hHderiv : Continuous (fderiv ℝ H))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
      (∀ y, ‖quotientRegularizedRepresentative k H ε y‖ ≤ C) ∧
      (∀ y,
        ‖fderiv ℝ
          (quotientRegularizedRepresentative k H ε) y‖ ≤ D) := by
  let R := quotientRegularizedRepresentative k H ε
  have hRdiff :
      ContDiff ℝ 1 R :=
    contDiff_one_quotientRegularizedRepresentative
      k H hHdiff hHderiv hε
  have hRcompact : HasCompactSupport R :=
    quotientRegularizedRepresentative_hasCompactSupport k H ε
  obtain ⟨C₀, hC₀⟩ :=
    hRdiff.continuous.bounded_above_of_compact_support hRcompact
  obtain ⟨D₀, hD₀⟩ :=
    hRdiff.continuous_fderiv (by norm_num)
      |>.bounded_above_of_compact_support
        (HasCompactSupport.fderiv (𝕜 := ℝ) hRcompact)
  refine ⟨max C₀ 0, max D₀ 0, le_max_right _ _, le_max_right _ _,
    fun y => (hC₀ y).trans (le_max_left _ _),
    fun y => (hD₀ y).trans (le_max_left _ _)⟩

lemma euclideanDot_smul_left {n : ℕ}
    (c : ℝ) (x y : EuclideanSpace ℝ (Fin n)) :
    euclideanDot (c • x) y = c * euclideanDot x y := by
  unfold euclideanDot
  simp only [PiLp.smul_apply, smul_eq_mul, mul_assoc,
    Finset.mul_sum]

lemma euclideanDot_smul_right {n : ℕ}
    (c : ℝ) (x y : EuclideanSpace ℝ (Fin n)) :
    euclideanDot x (c • y) = c * euclideanDot x y := by
  rw [euclideanDot_comm, euclideanDot_smul_left,
    euclideanDot_comm]

/-- Radial normalization.  We use a local Fréchet derivative at unit
vectors to compare derivatives of functions agreeing on the sphere. -/
noncomputable def radialDirection
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x : E) : E :=
  NormedSpace.normalize x

lemma radialDirection_norm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {x : E} (hx : x ≠ 0) :
    ‖radialDirection x‖ = 1 := by
  exact NormedSpace.norm_normalize hx

lemma hasFDerivAt_radialDirection_of_norm_one
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x : E) (hx : ‖x‖ = 1) :
    HasFDerivAt radialDirection
      (HDP.Appendix.sphereTangentProjection x) x := by
  let q : E → ℝ :=
    fun y => ‖y‖ ^ 2
  let r : E → ℝ :=
    fun y => Real.sqrt (q y)
  let a : E → ℝ :=
    fun y => (r y)⁻¹
  have hq :
      HasFDerivAt q (2 • innerSL ℝ x) x := by
    simpa [q] using
      (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hq0 : q x ≠ 0 := by
    simp [q, hx]
  have hr :
      HasFDerivAt r
        ((1 / (2 * Real.sqrt (q x))) •
          (2 • innerSL ℝ x)) x := by
    simpa [r] using hq.sqrt hq0
  have hr0 : r x ≠ 0 := by
    simp [r, q, hx]
  have ha := (hasFDerivAt_inv' hr0).comp x hr
  have hsmul := ha.smul (hasFDerivAt_id x)
  have hfun : (radialDirection : E → E) = Inv.inv ∘ r • id := by
    funext y
    simp [radialDirection, NormedSpace.normalize, a, r, q,
      Real.sqrt_sq (norm_nonneg y)]
  rw [← hfun] at hsmul
  apply hsmul.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  simp [a, r, q, hx,
    HDP.Appendix.sphereTangentProjection, smul_smul,
    sub_eq_add_neg]

lemma inner_euclidean_eq_euclideanDot {n : ℕ}
    (x y : EuclideanSpace ℝ (Fin n)) :
    inner ℝ x y = euclideanDot x y := by
  rw [PiLp.inner_apply]
  simp [euclideanDot, RCLike.inner_apply, mul_comm]

/-- Two differentiable ambient functions which agree on the unit sphere
have equal derivatives in every tangent direction. -/
lemma fderiv_eq_of_eq_on_unitSphere_of_tangent {n : ℕ}
    (F G : EuclideanSpace ℝ (Fin n) → ℝ)
    (y z : EuclideanSpace ℝ (Fin n))
    (hF : DifferentiableAt ℝ F y)
    (hG : DifferentiableAt ℝ G y)
    (hy : ‖y‖ = 1)
    (hyz : euclideanDot y z = 0)
    (hEq : ∀ x, ‖x‖ = 1 → F x = G x) :
    fderiv ℝ F y z = fderiv ℝ G y z := by
  have hy0 : y ≠ 0 := by
    intro h
    simpa [h] using hy
  have hrad :
      HasFDerivAt radialDirection
        (HDP.Appendix.sphereTangentProjection y) y :=
    hasFDerivAt_radialDirection_of_norm_one y hy
  have htangent :
      HDP.Appendix.sphereTangentProjection y z = z := by
    unfold HDP.Appendix.sphereTangentProjection
    simp [inner_euclidean_eq_euclideanDot, hyz]
  have hry : radialDirection y = y := by
    exact NormedSpace.normalize_eq_self_of_norm_eq_one hy
  have hFc :
      HasFDerivAt (F ∘ radialDirection)
        ((fderiv ℝ F y).comp
          (HDP.Appendix.sphereTangentProjection y)) y := by
    have hFbase :
        HasFDerivAt F (fderiv ℝ F y) (radialDirection y) := by
      simpa [hry] using hF.hasFDerivAt
    exact hFbase.comp y hrad
  have hGc :
      HasFDerivAt (G ∘ radialDirection)
        ((fderiv ℝ G y).comp
          (HDP.Appendix.sphereTangentProjection y)) y := by
    have hGbase :
        HasFDerivAt G (fderiv ℝ G y) (radialDirection y) := by
      simpa [hry] using hG.hasFDerivAt
    exact hGbase.comp y hrad
  have hevent :
      (F ∘ radialDirection) =ᶠ[𝓝 y]
        (G ∘ radialDirection) := by
    filter_upwards [eventually_ne_nhds hy0] with x hx
    exact hEq _ (radialDirection_norm hx)
  have hsame :
      (fderiv ℝ F y).comp
          (HDP.Appendix.sphereTangentProjection y) =
        (fderiv ℝ G y).comp
          (HDP.Appendix.sphereTangentProjection y) :=
    hFc.unique (hGc.congr_of_eventuallyEq hevent)
  have happ := congrArg
    (fun L :
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => L z) hsame
  simpa [htangent] using happ

/-- A local version of tangent agreement.  It is enough that the two
functions agree on a spherical neighborhood of the base point. -/
lemma fderiv_eq_of_eventuallyEq_on_unitSphere_of_tangent {n : ℕ}
    (F G : EuclideanSpace ℝ (Fin n) → ℝ)
    (y z : EuclideanSpace ℝ (Fin n))
    (hF : DifferentiableAt ℝ F y)
    (hG : DifferentiableAt ℝ G y)
    (hy : ‖y‖ = 1)
    (hyz : euclideanDot y z = 0)
    (hEq :
      ∀ᶠ x in 𝓝 y, ‖x‖ = 1 → F x = G x) :
    fderiv ℝ F y z = fderiv ℝ G y z := by
  have hy0 : y ≠ 0 := by
    intro h
    simpa [h] using hy
  have hrad :
      HasFDerivAt radialDirection
        (HDP.Appendix.sphereTangentProjection y) y :=
    hasFDerivAt_radialDirection_of_norm_one y hy
  have htangent :
      HDP.Appendix.sphereTangentProjection y z = z := by
    unfold HDP.Appendix.sphereTangentProjection
    simp [inner_euclidean_eq_euclideanDot, hyz]
  have hry : radialDirection y = y :=
    NormedSpace.normalize_eq_self_of_norm_eq_one hy
  have hFc :
      HasFDerivAt (F ∘ radialDirection)
        ((fderiv ℝ F y).comp
          (HDP.Appendix.sphereTangentProjection y)) y := by
    have hFbase :
        HasFDerivAt F (fderiv ℝ F y) (radialDirection y) := by
      simpa [hry] using hF.hasFDerivAt
    exact hFbase.comp y hrad
  have hGc :
      HasFDerivAt (G ∘ radialDirection)
        ((fderiv ℝ G y).comp
          (HDP.Appendix.sphereTangentProjection y)) y := by
    have hGbase :
        HasFDerivAt G (fderiv ℝ G y) (radialDirection y) := by
      simpa [hry] using hG.hasFDerivAt
    exact hGbase.comp y hrad
  have hEq' :
      ∀ᶠ x in 𝓝 (radialDirection y),
        ‖x‖ = 1 → F x = G x := by
    simpa [hry] using hEq
  have hevent :
      (F ∘ radialDirection) =ᶠ[𝓝 y]
        (G ∘ radialDirection) := by
    filter_upwards
      [hrad.continuousAt hEq', eventually_ne_nhds hy0] with x hx hx0
    exact hx (radialDirection_norm hx0)
  have hsame :
      (fderiv ℝ F y).comp
          (HDP.Appendix.sphereTangentProjection y) =
        (fderiv ℝ G y).comp
          (HDP.Appendix.sphereTangentProjection y) :=
    hFc.unique (hGc.congr_of_eventuallyEq hevent)
  have happ := congrArg
    (fun L :
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => L z) hsame
  simpa [htangent] using happ

lemma hasDerivAt_householderMatrix_two_smul_line
    {n : ℕ}
    (r a : EuclideanSpace ℝ (Fin n))
    (hrr : euclideanDot r r = 1)
    (hra : euclideanDot r a = 0) :
    HasDerivAt
      (fun t : ℝ =>
        householderMatrix ((2 : ℝ) • r + t • a))
      (-(Matrix.vecMulVec (fun i => a i) (fun j => r j)) -
        Matrix.vecMulVec (fun i => r i) (fun j => a j)) 0 := by
  let v : ℝ → EuclideanSpace ℝ (Fin n) :=
    fun t => (2 : ℝ) • r + t • a
  have hv (i : Fin n) :
      HasDerivAt (fun t => v t i) (a i) 0 := by
    change
      HasDerivAt
        (fun t : ℝ => (2 : ℝ) * r i + t * a i) (a i) 0
    simpa only [id_eq, one_mul] using
      ((hasDerivAt_id (𝕜 := ℝ) (x := (0 : ℝ))).mul_const
        (a i)).const_add (2 * r i)
  have hqraw :
      HasDerivAt
        (fun t => ∑ i : Fin n, v t i * v t i)
        (∑ i : Fin n,
          (a i * (2 * r i) + (2 * r i) * a i)) 0 := by
    have hsum :=
      HasDerivAt.sum (u := Finset.univ)
        (fun i _ => (hv i).mul (hv i))
    have hsum' :
        HasDerivAt
          (∑ i : Fin n,
            (fun t => v t i) * fun t => v t i)
          (∑ i : Fin n,
            (a i * (2 * r i) + (2 * r i) * a i)) 0 :=
      hsum.congr_deriv (by simp [v])
    apply hsum'.congr_of_eventuallyEq
    filter_upwards []
    intro t
    simp only [Finset.sum_apply, Pi.mul_apply]
  have hqderiv :
      (∑ i : Fin n,
        (a i * (2 * r i) + (2 * r i) * a i)) = 0 := by
    calc
      (∑ i : Fin n,
          (a i * (2 * r i) + (2 * r i) * a i)) =
          4 * euclideanDot r a := by
            unfold euclideanDot
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ = 0 := by rw [hra, mul_zero]
  rw [hqderiv] at hqraw
  have hq :
      HasDerivAt
        (fun t => euclideanDot (v t) (v t)) 0 0 := by
    simpa [euclideanDot] using hqraw
  have hqzero :
      euclideanDot (v 0) (v 0) = 4 := by
    rw [show v 0 = (2 : ℝ) • r by simp [v]]
    rw [euclideanDot_smul_left,
      euclideanDot_smul_right, hrr]
    norm_num
  have hc :
      HasDerivAt
        (fun t => (2 : ℝ) *
          (euclideanDot (v t) (v t))⁻¹) 0 0 := by
    have hinv := hq.inv (by rw [hqzero]; norm_num)
    exact (HasDerivAt.const_mul (2 : ℝ) hinv).congr_deriv (by simp)
  apply hasDerivAt_pi.2
  intro i
  apply hasDerivAt_pi.2
  intro j
  have hprod :=
    ((hc.mul (hv i)).mul (hv j))
  have hentry :=
    (hasDerivAt_const (x := (0 : ℝ))
      (c := if i = j then (1 : ℝ) else 0)).sub hprod
  let d : ℝ :=
    -((2 : ℝ) * (euclideanDot (v 0) (v 0))⁻¹ *
        v 0 i * a j) -
      ((2 : ℝ) * (euclideanDot (v 0) (v 0))⁻¹ *
        a i * v 0 j)
  have hentryD :
      HasDerivAt
        ((fun _t : ℝ => if i = j then (1 : ℝ) else 0) -
          (((fun t => (2 : ℝ) *
              (euclideanDot (v t) (v t))⁻¹) *
            fun t => v t i) *
            fun t => v t j))
        d 0 := by
    apply hentry.congr_deriv
    dsimp [d]
    ring
  have hentryFun :
      HasDerivAt
        (fun t =>
          householderMatrix (v t) i j) d 0 := by
    apply hentryD.congr_of_eventuallyEq
    filter_upwards []
    intro t
    simp only [Pi.sub_apply, Pi.mul_apply]
    simp [householderMatrix, Matrix.vecMulVec_apply,
      div_eq_mul_inv, Matrix.one_apply]
    ring
  apply hentryFun.congr_deriv
  dsimp [d]
  rw [hqzero]
  simp [v, Matrix.vecMulVec_apply]
  ring

lemma householderDerivative_mul_householder
    {n : ℕ}
    (r a : EuclideanSpace ℝ (Fin n))
    (hrr : euclideanDot r r = 1)
    (hra : euclideanDot r a = 0) :
    (-(Matrix.vecMulVec (fun i => a i) (fun j => r j)) -
        Matrix.vecMulVec (fun i => r i) (fun j => a j)) *
        householderMatrix r =
      Matrix.vecMulVec (fun i => a i) (fun j => r j) -
        Matrix.vecMulVec (fun i => r i) (fun j => a j) := by
  have hr0 : r ≠ 0 := by
    intro hr
    subst r
    norm_num [euclideanDot] at hrr
  have hrH (j : Fin n) :
      (∑ c : Fin n, r c * householderMatrix r c j) =
        -r j := by
    have h :
        (∑ c : Fin n,
          householderMatrix r j c * r c) = -r j := by
      simpa [Matrix.mulVec, dotProduct] using
        congrFun (householderMatrix_mulVec_self r hr0) j
    rw [← h]
    apply Finset.sum_congr rfl
    intro c _
    have hsym :
        householderMatrix r c j =
          householderMatrix r j c := by
      have ht := congrArg
        (fun M : Matrix (Fin n) (Fin n) ℝ => M j c)
        (householderMatrix_transpose r)
      simpa using ht
    rw [hsym]
    ring
  have haH (j : Fin n) :
      (∑ c : Fin n, a c * householderMatrix r c j) =
        a j := by
    have h :
        (∑ c : Fin n,
          householderMatrix r j c * a c) = a j := by
      simpa [Matrix.mulVec, dotProduct] using
        congrFun
          (householderMatrix_mulVec_of_dot_eq_zero r a hra) j
    rw [← h]
    apply Finset.sum_congr rfl
    intro c _
    have hsym :
        householderMatrix r c j =
          householderMatrix r j c := by
      have ht := congrArg
        (fun M : Matrix (Fin n) (Fin n) ℝ => M j c)
        (householderMatrix_transpose r)
      simpa using ht
    rw [hsym]
    ring
  ext i j
  simp only [Matrix.mul_apply, Matrix.sub_apply,
    Matrix.neg_apply, Matrix.vecMulVec_apply]
  calc
    (∑ c : Fin n,
        (-(a i * r c) - r i * a c) *
          householderMatrix r c j) =
        -(a i) * (∑ c : Fin n,
          r c * householderMatrix r c j) -
          r i * (∑ c : Fin n,
            a c * householderMatrix r c j) := by
            rw [Finset.mul_sum, Finset.mul_sum,
              ← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro c _
            ring
    _ = a i * r j - r i * a j := by
      rw [hrH, haH]
      ring

/-- Householder section centered at the identity over the reference
direction `r`. -/
noncomputable def centeredHouseholderSection {n : ℕ}
    (r y : EuclideanSpace ℝ (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ :=
  householderMatrix (r + y) * householderMatrix r

lemma hasDerivAt_centeredHouseholderSection_line
    {n : ℕ}
    (r a : EuclideanSpace ℝ (Fin n))
    (hrr : euclideanDot r r = 1)
    (hra : euclideanDot r a = 0) :
    HasDerivAt
      (fun t : ℝ =>
        centeredHouseholderSection r (r + t • a))
      (Matrix.vecMulVec (fun i => a i) (fun j => r j) -
        Matrix.vecMulVec (fun i => r i) (fun j => a j)) 0 := by
  let D :=
    -(Matrix.vecMulVec (fun i => a i) (fun j => r j)) -
      Matrix.vecMulVec (fun i => r i) (fun j => a j)
  have hh :
      HasDerivAt
        (fun t : ℝ =>
          householderMatrix ((2 : ℝ) • r + t • a))
        D 0 :=
    hasDerivAt_householderMatrix_two_smul_line
      r a hrr hra
  have hderiv :=
    householderDerivative_mul_householder r a hrr hra
  apply hasDerivAt_pi.2
  intro i
  apply hasDerivAt_pi.2
  intro j
  have hhij (c : Fin n) :
      HasDerivAt
        (fun t : ℝ =>
          householderMatrix ((2 : ℝ) • r + t • a) i c)
        (D i c) 0 :=
    hasDerivAt_pi.1 (hasDerivAt_pi.1 hh i) c
  have hsum :=
    HasDerivAt.sum (u := Finset.univ)
      (fun c _ => (hhij c).mul_const
        (householderMatrix r c j))
  have hentry :
      HasDerivAt
        (fun t : ℝ =>
          centeredHouseholderSection r (r + t • a) i j)
        ((Matrix.vecMulVec (fun i => a i) (fun j => r j) -
          Matrix.vecMulVec (fun i => r i) (fun j => a j)) i j) 0 := by
    have hsum' := hsum.congr_deriv (by
      have hij := congrArg
        (fun M : Matrix (Fin n) (Fin n) ℝ => M i j)
        hderiv
      simpa [D, Matrix.mul_apply] using hij)
    apply hsum'.congr_of_eventuallyEq
    filter_upwards []
    intro t
    simp only [Finset.sum_apply, Pi.mul_apply]
    simp only [centeredHouseholderSection, Matrix.mul_apply]
    rw [← add_assoc, ← two_smul ℝ r]
  exact hentry

/-- A Householder reflection is unchanged when its defining vector is
multiplied by two. -/
lemma householderMatrix_two_smul {n : ℕ}
    (r : EuclideanSpace ℝ (Fin n))
    (hrr : euclideanDot r r = 1) :
    householderMatrix ((2 : ℝ) • r) =
      householderMatrix r := by
  have hdot :
      euclideanDot ((2 : ℝ) • r) ((2 : ℝ) • r) = 4 := by
    rw [euclideanDot_smul_left, euclideanDot_smul_right, hrr]
    norm_num
  ext i j
  simp only [householderMatrix, Matrix.sub_apply, Matrix.one_apply,
    Matrix.smul_apply, Matrix.vecMulVec_apply, PiLp.smul_apply,
    smul_eq_mul]
  rw [hdot, hrr]
  ring

lemma centeredHouseholderSection_self {n : ℕ}
    (r : EuclideanSpace ℝ (Fin n))
    (hrr : euclideanDot r r = 1) :
    centeredHouseholderSection r r = 1 := by
  have hr0 : r ≠ 0 := by
    intro hr
    subst r
    norm_num [euclideanDot] at hrr
  unfold centeredHouseholderSection
  rw [← two_smul ℝ r, householderMatrix_two_smul r hrr,
    householderMatrix_mul_self r hr0]

/-- Vectorization as a continuous linear map. -/
noncomputable def matrixVectorizeCLM {m n : ℕ} :
    Matrix (Fin m) (Fin n) ℝ →L[ℝ]
      EuclideanSpace ℝ (Fin m × Fin n) :=
  LinearMap.toContinuousLinearMap
    { toFun := HDP.gaussianMatrixVectorize
      map_add' := by
        intro A B
        apply WithLp.ofLp_injective
        ext p
        simp [HDP.gaussianMatrixVectorize,
          HDP.gaussianMatrixFlatten]
      map_smul' := by
        intro c A
        apply WithLp.ofLp_injective
        ext p
        simp [HDP.gaussianMatrixVectorize,
          HDP.gaussianMatrixFlatten] }

@[simp] lemma matrixVectorizeCLM_apply {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    matrixVectorizeCLM A = HDP.gaussianMatrixVectorize A := rfl

/-- Euclidean action of a fixed real matrix. -/
noncomputable def matrixMulVecCLM {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)

@[simp] lemma matrixMulVecCLM_apply {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    matrixMulVecCLM A x =
      WithLp.toLp 2 (A *ᵥ (fun i => x i)) :=
  rfl

/-- Vectorized left multiplication by a fixed square matrix. -/
noncomputable def vectorizedLeftMulCLM {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    FrobeniusEuclidean n →L[ℝ] FrobeniusEuclidean n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y =>
        HDP.gaussianMatrixVectorize
          (A * HDP.gaussianMatrixUnvectorize y)
      map_add' := by
        intro y z
        apply WithLp.ofLp_injective
        ext p
        simp [HDP.gaussianMatrixVectorize,
          HDP.gaussianMatrixFlatten, WithLp.ofLp_toLp,
          HDP.gaussianMatrixUnvectorize, Matrix.mul_apply]
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib]
      map_smul' := by
        intro c y
        apply WithLp.ofLp_injective
        ext p
        simp [HDP.gaussianMatrixVectorize,
          HDP.gaussianMatrixFlatten, WithLp.ofLp_toLp,
          HDP.gaussianMatrixUnvectorize, Matrix.mul_apply,
          smul_eq_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring }

@[simp] lemma vectorizedLeftMulCLM_apply {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (y : FrobeniusEuclidean n) :
    vectorizedLeftMulCLM A y =
      HDP.gaussianMatrixVectorize
        (A * HDP.gaussianMatrixUnvectorize y) := rfl

lemma euclideanDot_mulVec_transpose {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) :
    euclideanDot
        (WithLp.toLp 2 (A *ᵥ (fun i => x i))) y =
      euclideanDot x
        (WithLp.toLp 2 (Aᵀ *ᵥ (fun i => y i))) := by
  unfold euclideanDot Matrix.mulVec dotProduct
  simp only [WithLp.ofLp_toLp, Matrix.transpose_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Centered quotient lift based at `U`.  At the orbit point `U r` it is
equal to `U`, and its differential in a tangent direction is the horizontal
matrix `U (a rᵀ - r aᵀ)`. -/
noncomputable def quotientCenteredLiftVector
    (k : ℕ)
    (U : Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ)
    (x : EuclideanSpace ℝ (Fin (k + 3))) :
    FrobeniusEuclidean (k + 3) :=
  vectorizedLeftMulCLM U.1
    (HDP.gaussianMatrixVectorize
      (centeredHouseholderSection (quotientReference k)
        (matrixMulVecCLM U.1ᵀ x)))

/-- The quotient ambient average evaluated on the centered lift based at `U`. -/
noncomputable def quotientCenteredAverage
    (k : ℕ)
    (H : FrobeniusEuclidean (k + 3) → ℝ)
    (U : Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ)
    (x : EuclideanSpace ℝ (Fin (k + 3))) : ℝ :=
  quotientAmbientAverage k H
    (quotientCenteredLiftVector k U x)

lemma matrixMulVecCLM_transpose_orbit
    (k : ℕ)
    (U : Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ) :
    matrixMulVecCLM U.1ᵀ
        (specialOrthogonalSphereOrbit
          (coordinateSpherePoint (secondCoordinateIndex k)) U) =
      quotientReference k := by
  apply WithLp.ofLp_injective
  change
    U.1ᵀ *ᵥ
        (U.1 *ᵥ
          (fun i => quotientReference k i)) =
      fun i => quotientReference k i
  rw [Matrix.mulVec_mulVec,
    (Matrix.mem_orthogonalGroup_iff' (Fin (k + 3)) ℝ).mp U.2.1]
  exact Matrix.one_mulVec _

lemma norm_matrixMulVecCLM_transpose_special
    {n : ℕ}
    (U : Matrix.specialOrthogonalGroup (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖matrixMulVecCLM U.1ᵀ x‖ = ‖x‖ := by
  let Ut : Matrix.orthogonalGroup (Fin n) ℝ :=
    ⟨U.1ᵀ, by
      rw [Matrix.mem_orthogonalGroup_iff (Fin n) ℝ,
        Matrix.transpose_transpose]
      exact
        (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).mp U.2.1⟩
  change ‖HDP.Chapter5.orthogonalAction Ut x‖ = ‖x‖
  exact HDP.Chapter5.norm_orthogonalAction Ut x

lemma quotientCenteredLiftVector_orbit
    (k : ℕ)
    (U : Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ) :
    quotientCenteredLiftVector k U
        (specialOrthogonalSphereOrbit
          (coordinateSpherePoint (secondCoordinateIndex k)) U) =
      HDP.gaussianMatrixVectorize U.1 := by
  unfold quotientCenteredLiftVector
  rw [matrixMulVecCLM_transpose_orbit,
    centeredHouseholderSection_self
      (quotientReference k)
      (euclideanDot_quotientReference_self k)]
  simp

lemma quotientCenteredAverage_eq_patched_of_norm_one
    (k : ℕ) (H : FrobeniusEuclidean (k + 3) → ℝ)
    (hH : Continuous H)
    (U : Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ)
    (x : EuclideanSpace ℝ (Fin (k + 3)))
    (hx : ‖x‖ = 1)
    (hplus :
      quotientReference k + matrixMulVecCLM U.1ᵀ x ≠ 0) :
    quotientCenteredAverage k H U x =
      quotientPatchedAverage k H x := by
  let xs : Metric.sphere
      (0 : EuclideanSpace ℝ (Fin (k + 3))) 1 :=
    ⟨x, by simpa [Metric.mem_sphere, dist_zero_right] using hx⟩
  let x' : Metric.sphere
      (0 : EuclideanSpace ℝ (Fin (k + 3))) 1 :=
    ⟨matrixMulVecCLM U.1ᵀ x, by
      simpa [Metric.mem_sphere, dist_zero_right] using
        (calc
          ‖matrixMulVecCLM U.1ᵀ x‖ = ‖x‖ :=
            norm_matrixMulVecCLM_transpose_special U x
          _ = 1 := hx)⟩
  have hplus' :
      quotientReference k +
          (x' : EuclideanSpace ℝ (Fin (k + 3))) ≠ 0 :=
    hplus
  let S : Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ :=
    ⟨quotientPlusSectionMatrix k x',
      quotientPlusSectionMatrix_mem_specialOrthogonal
        k x' hplus'⟩
  let W : Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ := U * S
  have hlift :
      quotientCenteredLiftVector k U x =
        HDP.gaussianMatrixVectorize W.1 := by
    unfold quotientCenteredLiftVector
    simp only [vectorizedLeftMulCLM_apply]
    rw [HDP.gaussianMatrixUnvectorize_vectorize]
    rfl
  have hWx :
      W.1 *ᵥ (fun a => quotientReference k a) =
        fun a => x a := by
    change
      (U.1 * quotientPlusSectionMatrix k x') *ᵥ
          (fun a => quotientReference k a) =
        fun a => x a
    rw [← Matrix.mulVec_mulVec,
      quotientPlusSectionMatrix_mulVec_reference k x' hplus']
    change
      U.1 *ᵥ (U.1ᵀ *ᵥ (fun a => x a)) =
        fun a => x a
    rw [Matrix.mulVec_mulVec,
      (Matrix.mem_orthogonalGroup_iff (Fin (k + 3)) ℝ).mp U.2.1]
    exact Matrix.one_mulVec _
  unfold quotientCenteredAverage
  rw [hlift,
    quotientAmbientAverage_vectorize_specialOrthogonal k H hH W]
  exact
    (quotientPatchedAverage_eq_rightAverage_of_mulVec
      k H hH xs W (by simpa [xs] using hWx)).symm

lemma hasDerivAt_vectorized_centeredHouseholderSection_line
    {n : ℕ}
    (r a : EuclideanSpace ℝ (Fin n))
    (hrr : euclideanDot r r = 1)
    (hra : euclideanDot r a = 0) :
    HasDerivAt
      (fun t : ℝ =>
        HDP.gaussianMatrixVectorize
          (centeredHouseholderSection r (r + t • a)))
      (HDP.gaussianMatrixVectorize
        (Matrix.vecMulVec (fun i => a i) (fun j => r j) -
          Matrix.vecMulVec (fun i => r i) (fun j => a j))) 0 := by
  let A :=
    Matrix.vecMulVec (fun i => a i) (fun j => r j) -
      Matrix.vecMulVec (fun i => r i) (fun j => a j)
  have hmatrix :=
    hasDerivAt_centeredHouseholderSection_line r a hrr hra
  have hraw :
      HasDerivAt
        (fun t : ℝ =>
          HDP.gaussianMatrixFlatten
            (centeredHouseholderSection r (r + t • a)))
        (HDP.gaussianMatrixFlatten A) 0 := by
    apply hasDerivAt_pi.2
    intro p
    exact hasDerivAt_pi.1
      (hasDerivAt_pi.1 hmatrix p.1) p.2
  have h :=
    (PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2
      (HDP.gaussianMatrixFlatten
        (centeredHouseholderSection r (r + (0 : ℝ) • a)))).comp_hasDerivAt
        (0 : ℝ) hraw
  simpa [HDP.gaussianMatrixVectorize, Function.comp_def, A] using h

lemma hasDerivAt_quotientCenteredLiftVector_line
    (k : ℕ)
    (U : Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ)
    (y z : EuclideanSpace ℝ (Fin (k + 3)))
    (hbase :
      matrixMulVecCLM U.1ᵀ y = quotientReference k)
    (htangent :
      euclideanDot (quotientReference k)
        (matrixMulVecCLM U.1ᵀ z) = 0) :
    HasDerivAt
      (fun t : ℝ =>
        quotientCenteredLiftVector k U (y + t • z))
      (HDP.gaussianMatrixVectorize
        (U.1 *
          (Matrix.vecMulVec
              (fun i => matrixMulVecCLM U.1ᵀ z i)
              (fun j => quotientReference k j) -
            Matrix.vecMulVec
              (fun i => quotientReference k i)
              (fun j => matrixMulVecCLM U.1ᵀ z j)))) 0 := by
  let r := quotientReference k
  let a := matrixMulVecCLM U.1ᵀ z
  let A : Matrix (Fin (k + 3)) (Fin (k + 3)) ℝ :=
    Matrix.vecMulVec (fun i => a i) (fun j => r j) -
      Matrix.vecMulVec (fun i => r i) (fun j => a j)
  have hrr : euclideanDot r r = 1 :=
    euclideanDot_quotientReference_self k
  have hcore :
      HasDerivAt
        (fun t : ℝ =>
          HDP.gaussianMatrixVectorize
            (centeredHouseholderSection r (r + t • a)))
        (HDP.gaussianMatrixVectorize A) 0 := by
    exact hasDerivAt_vectorized_centeredHouseholderSection_line
      r a hrr htangent
  have hleft :=
    (vectorizedLeftMulCLM U.1).hasFDerivAt.comp_hasDerivAt
      (0 : ℝ) hcore
  have hline (t : ℝ) :
      matrixMulVecCLM U.1ᵀ (y + t • z) = r + t • a := by
    simp [map_add, map_smul, hbase, r, a]
  apply hleft.congr_of_eventuallyEq
  filter_upwards []
  intro t
  simp only [Function.comp_apply]
  rw [← hline t]
  rfl

/-- Directional derivative obtained by differentiating the compact
stabilizer integral. -/
noncomputable def quotientAmbientDirectionalDerivative
    (k : ℕ) (H : FrobeniusEuclidean (k + 3) → ℝ)
    (y v : FrobeniusEuclidean (k + 3)) : ℝ :=
  ∫ V : Matrix.specialOrthogonalGroup (Fin (k + 2)) ℝ,
    2 *
      H (vectorizedRightMulCLM
        (coordinateStabilizerMatrix
          (secondCoordinateIndex k) V.1) y) *
      fderiv ℝ H
        (vectorizedRightMulCLM
          (coordinateStabilizerMatrix
            (secondCoordinateIndex k) V.1) y)
        (vectorizedRightMulCLM
          (coordinateStabilizerMatrix
            (secondCoordinateIndex k) V.1) v)
    ∂HDP.Chapter5.specialOrthogonalHaarMeasure (k + 2)

lemma hasDerivAt_quotientAmbientAverage_line
    (k : ℕ) (H : FrobeniusEuclidean (k + 3) → ℝ)
    (hHdiff : Differentiable ℝ H)
    (hHderiv : Continuous (fderiv ℝ H))
    (y v : FrobeniusEuclidean (k + 3)) :
    HasDerivAt
      (fun t : ℝ => quotientAmbientAverage k H (y + t • v))
      (quotientAmbientDirectionalDerivative k H y v) 0 := by
  let μ :=
    HDP.Chapter5.specialOrthogonalHaarMeasure (k + 2)
  let K :
      Matrix.specialOrthogonalGroup (Fin (k + 2)) ℝ →
        Matrix (Fin (k + 3)) (Fin (k + 3)) ℝ :=
    fun V =>
      coordinateStabilizerMatrix
        (secondCoordinateIndex k) V.1
  let L :
      Matrix.specialOrthogonalGroup (Fin (k + 2)) ℝ →
        FrobeniusEuclidean (k + 3) →L[ℝ]
          FrobeniusEuclidean (k + 3) :=
    fun V => vectorizedRightMulCLM (K V)
  let F :
      ℝ → Matrix.specialOrthogonalGroup (Fin (k + 2)) ℝ → ℝ :=
    fun t V => H (L V (y + t • v)) ^ 2
  let F' :
      ℝ → Matrix.specialOrthogonalGroup (Fin (k + 2)) ℝ → ℝ :=
    fun t V =>
      2 * H (L V (y + t • v)) *
        fderiv ℝ H (L V (y + t • v)) (L V v)
  have hK : Continuous K := by
    dsimp [K]
    exact continuous_subtype_val.comp
      (continuous_coordinateStabilizerHom
        (secondCoordinateIndex k))
  have hL : Continuous L :=
    (continuous_vectorizedRightMulCLM (k + 3)).comp hK
  have hline :
      Continuous
        (fun p :
            ℝ × Matrix.specialOrthogonalGroup (Fin (k + 2)) ℝ =>
          y + p.1 • v) :=
    continuous_const.add (continuous_fst.smul continuous_const)
  have hpoint :
      Continuous
        (fun p :
            ℝ × Matrix.specialOrthogonalGroup (Fin (k + 2)) ℝ =>
          L p.2 (y + p.1 • v)) :=
    (hL.comp continuous_snd).clm_apply hline
  have hvel :
      Continuous
        (fun p :
            ℝ × Matrix.specialOrthogonalGroup (Fin (k + 2)) ℝ =>
          L p.2 v) :=
    (hL.comp continuous_snd).clm_apply continuous_const
  have hF : Continuous (Function.uncurry F) := by
    dsimp [F]
    exact (hHdiff.continuous.comp hpoint).pow 2
  have hF' : Continuous (Function.uncurry F') := by
    dsimp [F']
    exact
      (continuous_const.mul (hHdiff.continuous.comp hpoint)).mul
        ((hHderiv.comp hpoint).clm_apply hvel)
  have hdiff :
      ∀ V t, HasDerivAt (fun s => F s V) (F' t V) t := by
    intro V t
    have htv :
        HasDerivAt (fun s : ℝ => y + s • v) v t := by
      simpa only [id_eq, one_smul] using
        ((hasDerivAt_id (𝕜 := ℝ) (x := t)).smul_const v).const_add y
    have hLV :=
      (L V).hasFDerivAt.comp_hasDerivAt t htv
    have hcomp :=
      (hHdiff (L V (y + t • v))).hasFDerivAt
        |>.comp_hasDerivAt t hLV
    have hcomp' :
        HasDerivAt
          (fun s : ℝ => H (L V (y + s • v)))
          (fderiv ℝ H (L V (y + t • v)) (L V v)) t := by
      simpa only [Function.comp_def] using hcomp
    have hmul :
        HasDerivAt
          (fun s : ℝ =>
            H (L V (y + s • v)) * H (L V (y + s • v)))
          (F' t V) t :=
      (hcomp'.mul hcomp').congr_deriv (by
        dsimp [F']
        ring)
    simpa only [F, pow_two] using hmul
  unfold quotientAmbientAverage quotientAmbientDirectionalDerivative
  simpa only [μ, K, L, F, F', zero_smul, add_zero] using
    hasDerivAt_parametricIntegral_of_compact μ F F'
      hF hF' hdiff 0

lemma hasDerivAt_quotientCenteredAverage_orbit_line
    (k : ℕ) (H : FrobeniusEuclidean (k + 3) → ℝ)
    (hHdiff : Differentiable ℝ H)
    (hHderiv : Continuous (fderiv ℝ H))
    (U : Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ)
    (z : EuclideanSpace ℝ (Fin (k + 3)))
    (htangent :
      euclideanDot
        (specialOrthogonalSphereOrbit
          (coordinateSpherePoint (secondCoordinateIndex k)) U) z = 0) :
    let y :=
      (specialOrthogonalSphereOrbit
        (coordinateSpherePoint (secondCoordinateIndex k)) U :
          EuclideanSpace ℝ (Fin (k + 3)))
    let a := matrixMulVecCLM U.1ᵀ z
    let A : Matrix (Fin (k + 3)) (Fin (k + 3)) ℝ :=
      Matrix.vecMulVec (fun i => a i)
          (fun j => quotientReference k j) -
        Matrix.vecMulVec (fun i => quotientReference k i)
          (fun j => a j)
    let v := HDP.gaussianMatrixVectorize (U.1 * A)
    HasDerivAt
      (fun t : ℝ => quotientCenteredAverage k H U (y + t • z))
      (quotientAmbientDirectionalDerivative k H
        (HDP.gaussianMatrixVectorize U.1) v) 0 := by
  dsimp only
  let y :=
    (specialOrthogonalSphereOrbit
      (coordinateSpherePoint (secondCoordinateIndex k)) U :
        EuclideanSpace ℝ (Fin (k + 3)))
  let a := matrixMulVecCLM U.1ᵀ z
  let A : Matrix (Fin (k + 3)) (Fin (k + 3)) ℝ :=
    Matrix.vecMulVec (fun i => a i)
        (fun j => quotientReference k j) -
      Matrix.vecMulVec (fun i => quotientReference k i)
        (fun j => a j)
  let v := HDP.gaussianMatrixVectorize (U.1 * A)
  have hbase :
      matrixMulVecCLM U.1ᵀ y = quotientReference k :=
    matrixMulVecCLM_transpose_orbit k U
  have htan :
      euclideanDot (quotientReference k) a = 0 := by
    have hdot :=
      euclideanDot_mulVec_transpose U.1
        (quotientReference k) z
    rw [show
      WithLp.toLp 2
          (U.1 *ᵥ (fun i => quotientReference k i)) = y by
        rfl] at hdot
    change
      euclideanDot (quotientReference k)
        (WithLp.toLp 2
          (U.1ᵀ *ᵥ (fun i => z i))) = 0
    rw [← hdot]
    exact htangent
  have hlift :
      HasDerivAt
        (fun t : ℝ =>
          quotientCenteredLiftVector k U (y + t • z)) v 0 := by
    simpa only [a, A, v] using
      hasDerivAt_quotientCenteredLiftVector_line
        k U y z hbase htan
  have hlift0 :
      quotientCenteredLiftVector k U y =
        HDP.gaussianMatrixVectorize U.1 :=
    quotientCenteredLiftVector_orbit k U
  have houter :
      HasFDerivAt (quotientAmbientAverage k H)
        (fderiv ℝ (quotientAmbientAverage k H)
          (HDP.gaussianMatrixVectorize U.1))
        (HDP.gaussianMatrixVectorize U.1) :=
    (contDiff_one_quotientAmbientAverage
      k H hHdiff hHderiv).differentiable
        (by norm_num) (HDP.gaussianMatrixVectorize U.1)
      |>.hasFDerivAt
  have hcomp :=
    houter.comp_hasDerivAt_of_eq (0 : ℝ) hlift
      (by simpa [y] using hlift0.symm)
  have haffine :
      HasDerivAt
        (fun t : ℝ =>
          HDP.gaussianMatrixVectorize U.1 + t • v) v 0 := by
    simpa only [id_eq, one_smul] using
      ((hasDerivAt_id (𝕜 := ℝ) (x := (0 : ℝ))).smul_const v).const_add
        (HDP.gaussianMatrixVectorize U.1)
  have houterLine :=
    houter.comp_hasDerivAt_of_eq (0 : ℝ) haffine (by simp)
  have hline :=
    hasDerivAt_quotientAmbientAverage_line
      k H hHdiff hHderiv
        (HDP.gaussianMatrixVectorize U.1) v
  have hderiv :
      fderiv ℝ (quotientAmbientAverage k H)
          (HDP.gaussianMatrixVectorize U.1) v =
        quotientAmbientDirectionalDerivative k H
          (HDP.gaussianMatrixVectorize U.1) v :=
    houterLine.unique hline
  unfold quotientCenteredAverage
  exact hcomp.congr_deriv hderiv

/-- The horizontal skew matrix associated to a coordinate vector is the
corresponding linear combination of elementary skew generators. -/
lemma coordinateHorizontalMatrix_eq_neg_sum_skewGenerator
    {n : ℕ} (i : Fin n)
    (b : EuclideanSpace ℝ (Fin n)) :
    Matrix.vecMulVec (fun p => b p)
          (fun q => (coordinateSpherePoint i :
            EuclideanSpace ℝ (Fin n)) q) -
        Matrix.vecMulVec
          (fun p => (coordinateSpherePoint i :
            EuclideanSpace ℝ (Fin n)) p)
          (fun q => b q) =
      ∑ j : Fin n, (-b j) • skewGenerator i j := by
  classical
  ext p q
  by_cases hp : p = i
  · subst p
    by_cases hq : q = i
    · subst q
      simp [coordinateSpherePoint, skewGenerator,
        Matrix.vecMulVec_apply, Matrix.sum_apply,
        Matrix.smul_apply, Matrix.single_apply]
    · simp [coordinateSpherePoint, skewGenerator, hq,
        Matrix.vecMulVec_apply, Matrix.sum_apply,
        Matrix.smul_apply, Matrix.single_apply]
      simp [hq, Ne.symm hq, mul_ite]
  · by_cases hq : q = i
    · subst q
      simp [coordinateSpherePoint, skewGenerator, hp,
        Matrix.vecMulVec_apply, Matrix.sum_apply,
        Matrix.smul_apply, Matrix.single_apply]
      simp [hp, Ne.symm hp, mul_ite]
    · simp [coordinateSpherePoint, skewGenerator, hp, hq,
        Matrix.vecMulVec_apply, Matrix.sum_apply,
        Matrix.smul_apply, Matrix.single_apply]
      simp [hp, hq, Ne.symm hp, Ne.symm hq]

lemma fderiv_coordinateHorizontalMatrix
    {n : ℕ}
    (H : FrobeniusEuclidean n → ℝ)
    (W : Matrix.specialOrthogonalGroup (Fin n) ℝ)
    (i : Fin n)
    (b : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ H (HDP.gaussianMatrixVectorize W.1)
        (HDP.gaussianMatrixVectorize
          (W.1 *
            (Matrix.vecMulVec (fun p => b p)
                  (fun q => (coordinateSpherePoint i :
                    EuclideanSpace ℝ (Fin n)) q) -
              Matrix.vecMulVec
                (fun p => (coordinateSpherePoint i :
                  EuclideanSpace ℝ (Fin n)) p)
                (fun q => b q)))) =
      -2 * ∑ j : Fin n, tangentGradient H W i j * b j := by
  let A :=
    Matrix.vecMulVec (fun p => b p)
          (fun q => (coordinateSpherePoint i :
            EuclideanSpace ℝ (Fin n)) q) -
      Matrix.vecMulVec
        (fun p => (coordinateSpherePoint i :
          EuclideanSpace ℝ (Fin n)) p)
        (fun q => b q)
  have hA :
      A = ∑ j : Fin n, (-b j) • skewGenerator i j :=
    coordinateHorizontalMatrix_eq_neg_sum_skewGenerator i b
  have hdir :
      HDP.gaussianMatrixVectorize (W.1 * A) =
        ∑ j : Fin n, (-b j) •
          HDP.gaussianMatrixVectorize
            (W.1 * skewGenerator i j) := by
    change
      matrixVectorizeCLM (W.1 * A) =
        ∑ j : Fin n, (-b j) •
          matrixVectorizeCLM (W.1 * skewGenerator i j)
    rw [hA, Matrix.mul_sum, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    change
      matrixVectorizeCLM (W.1 * ((-b j) • skewGenerator i j)) =
        (-b j) • matrixVectorizeCLM
          (W.1 * skewGenerator i j)
    rw [Matrix.mul_smul, map_smul]
  change
    fderiv ℝ H (HDP.gaussianMatrixVectorize W.1)
        (HDP.gaussianMatrixVectorize (W.1 * A)) =
      -2 * ∑ j : Fin n, tangentGradient H W i j * b j
  rw [hdir, map_sum]
  simp_rw [map_smul,
    fderiv_skewGenerator_eq_tangentGradient H W i]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma fderiv_coordinateHorizontalMatrix_sq_le
    {n : ℕ}
    (H : FrobeniusEuclidean n → ℝ)
    (W : Matrix.specialOrthogonalGroup (Fin n) ℝ)
    (i : Fin n)
    (b : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ H (HDP.gaussianMatrixVectorize W.1)
        (HDP.gaussianMatrixVectorize
          (W.1 *
            (Matrix.vecMulVec (fun p => b p)
                  (fun q => (coordinateSpherePoint i :
                    EuclideanSpace ℝ (Fin n)) q) -
              Matrix.vecMulVec
                (fun p => (coordinateSpherePoint i :
                  EuclideanSpace ℝ (Fin n)) p)
                (fun q => b q)))) ^ 2 ≤
      2 * horizontalSquareEnergy (tangentGradient H W) i *
        ‖b‖ ^ 2 := by
  rw [fderiv_coordinateHorizontalMatrix H W i b]
  have hcs :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun j : Fin n => tangentGradient H W i j)
      (fun j : Fin n => b j)
  have hb :
      (∑ j : Fin n, b j ^ 2) = ‖b‖ ^ 2 := by
    rw [← euclideanDot_self_eq_norm_sq]
    unfold euclideanDot
    apply Finset.sum_congr rfl
    intro j _
    ring
  unfold horizontalSquareEnergy rowSquareEnergy
  rw [hb] at hcs
  nlinarith

lemma transpose_mul_vecMulVec_mul {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) :
    Sᵀ * Matrix.vecMulVec (fun p => x p) (fun q => y q) * S =
      Matrix.vecMulVec
        (Sᵀ *ᵥ (fun p => x p))
        (Sᵀ *ᵥ (fun q => y q)) := by
  ext p q
  simp only [Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct]
  calc
    (∑ z : Fin n,
        (∑ w : Fin n, S w p * (x w * y z)) * S z q) =
        ∑ z : Fin n,
          ((∑ w : Fin n, S w p * x w) * y z) * S z q := by
            apply Finset.sum_congr rfl
            intro z _
            congr 1
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro w _
            ring
    _ =
        (∑ w : Fin n, S w p * x w) *
          ∑ z : Fin n, S z q * y z := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro z _
            ring

lemma coordinateStabilizerMatrix_mulVec_reference
    {n : ℕ} (i : Fin (n + 1))
    (A : Matrix (Fin n) (Fin n) ℝ) :
    coordinateStabilizerMatrix i A *ᵥ
        (fun p => (coordinateSpherePoint i :
          EuclideanSpace ℝ (Fin (n + 1))) p) =
      fun p => (coordinateSpherePoint i :
        EuclideanSpace ℝ (Fin (n + 1))) p := by
  ext p
  refine Fin.succAboveCases i ?_ (fun j => ?_) p
  · simp [coordinateSpherePoint, Matrix.mulVec, dotProduct]
  · simp [coordinateSpherePoint, Matrix.mulVec, dotProduct]

lemma coordinateStabilizerMatrix_transpose_mulVec_reference
    {n : ℕ} (i : Fin (n + 1))
    (A : Matrix (Fin n) (Fin n) ℝ) :
    (coordinateStabilizerMatrix i A)ᵀ *ᵥ
        (fun p => (coordinateSpherePoint i :
          EuclideanSpace ℝ (Fin (n + 1))) p) =
      fun p => (coordinateSpherePoint i :
        EuclideanSpace ℝ (Fin (n + 1))) p := by
  rw [← coordinateStabilizerMatrix_transpose]
  exact coordinateStabilizerMatrix_mulVec_reference i Aᵀ

lemma conjugate_coordinateHorizontalMatrix_stabilizer
    {n : ℕ} (i : Fin (n + 1))
    (S : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (a : EuclideanSpace ℝ (Fin (n + 1)))
    (hSr :
      Sᵀ *ᵥ
          (fun p => (coordinateSpherePoint i :
            EuclideanSpace ℝ (Fin (n + 1))) p) =
        fun p => (coordinateSpherePoint i :
          EuclideanSpace ℝ (Fin (n + 1))) p) :
    Sᵀ *
        (Matrix.vecMulVec (fun p => a p)
              (fun q => (coordinateSpherePoint i :
                EuclideanSpace ℝ (Fin (n + 1))) q) -
          Matrix.vecMulVec
            (fun p => (coordinateSpherePoint i :
              EuclideanSpace ℝ (Fin (n + 1))) p)
            (fun q => a q)) * S =
      Matrix.vecMulVec
          (Sᵀ *ᵥ (fun p => a p))
          (fun q => (coordinateSpherePoint i :
            EuclideanSpace ℝ (Fin (n + 1))) q) -
        Matrix.vecMulVec
          (fun p => (coordinateSpherePoint i :
            EuclideanSpace ℝ (Fin (n + 1))) p)
          (Sᵀ *ᵥ (fun q => a q)) := by
  rw [Matrix.mul_sub, Matrix.sub_mul,
    transpose_mul_vecMulVec_mul,
    transpose_mul_vecMulVec_mul, hSr]

/-- The value of `H` along the stabilizer fiber through `U`. -/
noncomputable def quotientFiberValue
    (k : ℕ) (H : FrobeniusEuclidean (k + 3) → ℝ)
    (U : Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ)
    (V : Matrix.specialOrthogonalGroup (Fin (k + 2)) ℝ) : ℝ :=
  H (HDP.gaussianMatrixVectorize
    (U.1 * coordinateStabilizerMatrix
      (secondCoordinateIndex k) V.1))

/-- The derivative of `H` along the horizontal infinitesimal direction on a quotient fiber. -/
noncomputable def quotientFiberHorizontalDerivative
    (k : ℕ) (H : FrobeniusEuclidean (k + 3) → ℝ)
    (U : Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ)
    (a : EuclideanSpace ℝ (Fin (k + 3)))
    (V : Matrix.specialOrthogonalGroup (Fin (k + 2)) ℝ) : ℝ :=
  let A :=
    Matrix.vecMulVec (fun p => a p)
          (fun q => quotientReference k q) -
      Matrix.vecMulVec (fun p => quotientReference k p)
        (fun q => a q)
  let S :=
    coordinateStabilizerMatrix (secondCoordinateIndex k) V.1
  fderiv ℝ H (HDP.gaussianMatrixVectorize (U.1 * S))
    (HDP.gaussianMatrixVectorize (U.1 * A * S))

lemma continuous_quotientFiberValue
    (k : ℕ) {H : FrobeniusEuclidean (k + 3) → ℝ}
    (hH : Continuous H)
    (U : Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ) :
    Continuous (quotientFiberValue k H U) := by
  unfold quotientFiberValue
  have hS :
      Continuous
        (fun V : Matrix.specialOrthogonalGroup (Fin (k + 2)) ℝ =>
          coordinateStabilizerMatrix
            (secondCoordinateIndex k) V.1) :=
    continuous_subtype_val.comp
      (continuous_coordinateStabilizerHom
        (secondCoordinateIndex k))
  exact hH.comp
    (continuous_gaussianMatrixVectorize.comp
      (continuous_const.mul hS))

lemma continuous_quotientFiberHorizontalDerivative
    (k : ℕ) {H : FrobeniusEuclidean (k + 3) → ℝ}
    (hHderiv : Continuous (fderiv ℝ H))
    (U : Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ)
    (a : EuclideanSpace ℝ (Fin (k + 3))) :
    Continuous (quotientFiberHorizontalDerivative k H U a) := by
  unfold quotientFiberHorizontalDerivative
  let A :=
    Matrix.vecMulVec (fun p => a p)
          (fun q => quotientReference k q) -
      Matrix.vecMulVec (fun p => quotientReference k p)
        (fun q => a q)
  have hS :
      Continuous
        (fun V : Matrix.specialOrthogonalGroup (Fin (k + 2)) ℝ =>
          coordinateStabilizerMatrix
            (secondCoordinateIndex k) V.1) :=
    continuous_subtype_val.comp
      (continuous_coordinateStabilizerHom
        (secondCoordinateIndex k))
  have hpoint :
      Continuous
        (fun V : Matrix.specialOrthogonalGroup (Fin (k + 2)) ℝ =>
          HDP.gaussianMatrixVectorize
            (U.1 * coordinateStabilizerMatrix
              (secondCoordinateIndex k) V.1)) :=
    continuous_gaussianMatrixVectorize.comp
      (continuous_const.mul hS)
  have hdir :
      Continuous
        (fun V : Matrix.specialOrthogonalGroup (Fin (k + 2)) ℝ =>
          HDP.gaussianMatrixVectorize
            (U.1 * A * coordinateStabilizerMatrix
              (secondCoordinateIndex k) V.1)) :=
    continuous_gaussianMatrixVectorize.comp
      ((continuous_const.mul continuous_const).mul hS)
  exact (hHderiv.comp hpoint).clm_apply hdir

lemma quotientAmbientDirectionalDerivative_eq_fiber
    (k : ℕ) (H : FrobeniusEuclidean (k + 3) → ℝ)
    (U : Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ)
    (a : EuclideanSpace ℝ (Fin (k + 3))) :
    let A :=
      Matrix.vecMulVec (fun p => a p)
            (fun q => quotientReference k q) -
        Matrix.vecMulVec (fun p => quotientReference k p)
          (fun q => a q)
    quotientAmbientDirectionalDerivative k H
        (HDP.gaussianMatrixVectorize U.1)
        (HDP.gaussianMatrixVectorize (U.1 * A)) =
      ∫ V : Matrix.specialOrthogonalGroup (Fin (k + 2)) ℝ,
        2 * quotientFiberValue k H U V *
          quotientFiberHorizontalDerivative k H U a V
        ∂HDP.Chapter5.specialOrthogonalHaarMeasure (k + 2) := by
  dsimp only
  unfold quotientAmbientDirectionalDerivative quotientFiberValue
    quotientFiberHorizontalDerivative
  apply integral_congr_ae
  filter_upwards []
  intro V
  simp only [vectorizedRightMulCLM_apply,
    HDP.gaussianMatrixUnvectorize_vectorize]

lemma quotientAmbientAverage_vectorize_eq_fiberValue_sq
    (k : ℕ) (H : FrobeniusEuclidean (k + 3) → ℝ)
    (U : Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ) :
    quotientAmbientAverage k H
        (HDP.gaussianMatrixVectorize U.1) =
      ∫ V : Matrix.specialOrthogonalGroup (Fin (k + 2)) ℝ,
        quotientFiberValue k H U V ^ 2
        ∂HDP.Chapter5.specialOrthogonalHaarMeasure (k + 2) := by
  unfold quotientAmbientAverage quotientFiberValue
  apply integral_congr_ae
  filter_upwards []
  intro V
  simp only [vectorizedRightMulCLM_apply,
    HDP.gaussianMatrixUnvectorize_vectorize]

lemma quotientAmbientDirectionalDerivative_sq_le
    (k : ℕ) (H : FrobeniusEuclidean (k + 3) → ℝ)
    (hH : Continuous H)
    (hHderiv : Continuous (fderiv ℝ H))
    (U : Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ)
    (a : EuclideanSpace ℝ (Fin (k + 3))) :
    let A :=
      Matrix.vecMulVec (fun p => a p)
            (fun q => quotientReference k q) -
        Matrix.vecMulVec (fun p => quotientReference k p)
          (fun q => a q)
    quotientAmbientDirectionalDerivative k H
          (HDP.gaussianMatrixVectorize U.1)
          (HDP.gaussianMatrixVectorize (U.1 * A)) ^ 2 ≤
      quotientAmbientAverage k H
          (HDP.gaussianMatrixVectorize U.1) *
        (4 *
          ∫ V : Matrix.specialOrthogonalGroup (Fin (k + 2)) ℝ,
            quotientFiberHorizontalDerivative k H U a V ^ 2
            ∂HDP.Chapter5.specialOrthogonalHaarMeasure (k + 2)) := by
  dsimp only
  let μ :=
    HDP.Chapter5.specialOrthogonalHaarMeasure (k + 2)
  have hcs :=
    integral_mul_sq_le_integral_sq_mul_integral_sq μ
      (quotientFiberValue k H U)
      (fun V => 2 * quotientFiberHorizontalDerivative k H U a V)
      (continuous_quotientFiberValue k hH U)
      (continuous_const.mul
        (continuous_quotientFiberHorizontalDerivative
          k hHderiv U a))
  rw [quotientAmbientDirectionalDerivative_eq_fiber,
    quotientAmbientAverage_vectorize_eq_fiberValue_sq]
  calc
    (∫ V, 2 * quotientFiberValue k H U V *
          quotientFiberHorizontalDerivative k H U a V ∂μ) ^ 2 =
        (∫ V, quotientFiberValue k H U V *
          (2 * quotientFiberHorizontalDerivative k H U a V) ∂μ) ^ 2 := by
            congr 2
            funext V
            ring
    _ ≤
        (∫ V, quotientFiberValue k H U V ^ 2 ∂μ) *
          ∫ V, (2 *
            quotientFiberHorizontalDerivative k H U a V) ^ 2 ∂μ :=
      hcs
    _ =
        (∫ V, quotientFiberValue k H U V ^ 2 ∂μ) *
          (4 * ∫ V,
            quotientFiberHorizontalDerivative k H U a V ^ 2 ∂μ) := by
      congr 1
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards []
      intro V
      ring

lemma quotientFiberHorizontalDerivative_sq_le
    (k : ℕ) (H : FrobeniusEuclidean (k + 3) → ℝ)
    (U : Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ)
    (a : EuclideanSpace ℝ (Fin (k + 3)))
    (V : Matrix.specialOrthogonalGroup (Fin (k + 2)) ℝ) :
    quotientFiberHorizontalDerivative k H U a V ^ 2 ≤
      2 *
        horizontalSquareEnergy
          (tangentGradient H
            (U * coordinateStabilizerHom
              (secondCoordinateIndex k) V))
          (secondCoordinateIndex k) *
        ‖a‖ ^ 2 := by
  let i := secondCoordinateIndex k
  let Sg := coordinateStabilizerHom i V
  let S := Sg.1
  let W := U * Sg
  let b := matrixMulVecCLM Sᵀ a
  let A :=
    Matrix.vecMulVec (fun p => a p)
          (fun q => (coordinateSpherePoint i :
            EuclideanSpace ℝ (Fin (k + 3))) q) -
      Matrix.vecMulVec
        (fun p => (coordinateSpherePoint i :
          EuclideanSpace ℝ (Fin (k + 3))) p)
        (fun q => a q)
  let B :=
    Matrix.vecMulVec (fun p => b p)
          (fun q => (coordinateSpherePoint i :
            EuclideanSpace ℝ (Fin (k + 3))) q) -
      Matrix.vecMulVec
        (fun p => (coordinateSpherePoint i :
          EuclideanSpace ℝ (Fin (k + 3))) p)
        (fun q => b q)
  have hconj : Sᵀ * A * S = B := by
    exact conjugate_coordinateHorizontalMatrix_stabilizer
      i S a
        (coordinateStabilizerMatrix_transpose_mulVec_reference
          i V.1)
  have horth : S * Sᵀ = 1 :=
    (Matrix.mem_orthogonalGroup_iff (Fin (k + 3)) ℝ).mp Sg.2.1
  have hdir : U.1 * A * S = W.1 * B := by
    rw [← hconj]
    change U.1 * A * S = (U.1 * S) * (Sᵀ * A * S)
    calc
      U.1 * A * S = U.1 * (S * Sᵀ) * A * S := by
        rw [horth]
        simp
      _ = (U.1 * S) * (Sᵀ * A * S) := by
        noncomm_ring
  have hbound :=
    fderiv_coordinateHorizontalMatrix_sq_le
      H W i b
  have hbnorm : ‖b‖ = ‖a‖ := by
    exact norm_matrixMulVecCLM_transpose_special Sg a
  unfold quotientFiberHorizontalDerivative
  change
    fderiv ℝ H (HDP.gaussianMatrixVectorize W.1)
        (HDP.gaussianMatrixVectorize (U.1 * A * S)) ^ 2 ≤
      2 * horizontalSquareEnergy
        (tangentGradient H W) i * ‖a‖ ^ 2
  rw [hdir]
  calc
    _ ≤ 2 * horizontalSquareEnergy
        (tangentGradient H W) i * ‖b‖ ^ 2 := hbound
    _ = 2 * horizontalSquareEnergy
        (tangentGradient H W) i * ‖a‖ ^ 2 := by rw [hbnorm]

lemma integral_quotientFiberHorizontalDerivative_sq_le
    (k : ℕ) (H : FrobeniusEuclidean (k + 3) → ℝ)
    (hHderiv : Continuous (fderiv ℝ H))
    (U : Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ)
    (a : EuclideanSpace ℝ (Fin (k + 3))) :
    (∫ V : Matrix.specialOrthogonalGroup (Fin (k + 2)) ℝ,
        quotientFiberHorizontalDerivative k H U a V ^ 2
        ∂HDP.Chapter5.specialOrthogonalHaarMeasure (k + 2)) ≤
      ∫ V : Matrix.specialOrthogonalGroup (Fin (k + 2)) ℝ,
        2 *
          horizontalSquareEnergy
            (tangentGradient H
              (U * coordinateStabilizerHom
                (secondCoordinateIndex k) V))
            (secondCoordinateIndex k) *
          ‖a‖ ^ 2
        ∂HDP.Chapter5.specialOrthogonalHaarMeasure (k + 2) := by
  apply integral_mono
  · simpa only [IntegrableOn, Measure.restrict_univ] using
      ((continuous_quotientFiberHorizontalDerivative
        k hHderiv U a).pow 2).continuousOn.integrableOn_compact
          (μ := HDP.Chapter5.specialOrthogonalHaarMeasure (k + 2))
          isCompact_univ
  · have htg : Continuous
        (fun V : Matrix.specialOrthogonalGroup (Fin (k + 2)) ℝ =>
          tangentGradient H
            (U * coordinateStabilizerHom
              (secondCoordinateIndex k) V)) :=
      (continuous_tangentGradient hHderiv).comp
        (continuous_const.mul
          (continuous_coordinateStabilizerHom
            (secondCoordinateIndex k)))
    have hh : Continuous
        (fun V : Matrix.specialOrthogonalGroup (Fin (k + 2)) ℝ =>
          2 *
            horizontalSquareEnergy
              (tangentGradient H
                (U * coordinateStabilizerHom
                  (secondCoordinateIndex k) V))
              (secondCoordinateIndex k) *
            ‖a‖ ^ 2) := by
      unfold horizontalSquareEnergy rowSquareEnergy
      fun_prop
    simpa only [IntegrableOn, Measure.restrict_univ] using
      hh.continuousOn.integrableOn_compact
        (μ := HDP.Chapter5.specialOrthogonalHaarMeasure (k + 2))
        isCompact_univ
  · intro V
    exact quotientFiberHorizontalDerivative_sq_le k H U a V

lemma fderiv_quotientPatchedAverage_orbit_tangent
    (k : ℕ) (H : FrobeniusEuclidean (k + 3) → ℝ)
    (hHdiff : Differentiable ℝ H)
    (hHderiv : Continuous (fderiv ℝ H))
    (U : Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ)
    (z : EuclideanSpace ℝ (Fin (k + 3)))
    (htangent :
      euclideanDot
        (specialOrthogonalSphereOrbit
          (coordinateSpherePoint (secondCoordinateIndex k)) U) z = 0) :
    let y :=
      (specialOrthogonalSphereOrbit
        (coordinateSpherePoint (secondCoordinateIndex k)) U :
          EuclideanSpace ℝ (Fin (k + 3)))
    let a := matrixMulVecCLM U.1ᵀ z
    let A : Matrix (Fin (k + 3)) (Fin (k + 3)) ℝ :=
      Matrix.vecMulVec (fun i => a i)
          (fun j => quotientReference k j) -
        Matrix.vecMulVec (fun i => quotientReference k i)
          (fun j => a j)
    fderiv ℝ (quotientPatchedAverage k H) y z =
      quotientAmbientDirectionalDerivative k H
        (HDP.gaussianMatrixVectorize U.1)
        (HDP.gaussianMatrixVectorize (U.1 * A)) := by
  dsimp only
  let y :=
    (specialOrthogonalSphereOrbit
      (coordinateSpherePoint (secondCoordinateIndex k)) U :
        EuclideanSpace ℝ (Fin (k + 3)))
  let a := matrixMulVecCLM U.1ᵀ z
  let A : Matrix (Fin (k + 3)) (Fin (k + 3)) ℝ :=
    Matrix.vecMulVec (fun i => a i)
        (fun j => quotientReference k j) -
      Matrix.vecMulVec (fun i => quotientReference k i)
        (fun j => a j)
  have hy : ‖y‖ = 1 := by
    exact norm_coe_mem_unitSphere
      (specialOrthogonalSphereOrbit
        (coordinateSpherePoint (secondCoordinateIndex k)) U)
  have hplus_base :
      quotientReference k + matrixMulVecCLM U.1ᵀ y ≠ 0 := by
    rw [show matrixMulVecCLM U.1ᵀ y = quotientReference k by
      exact matrixMulVecCLM_transpose_orbit k U]
    rw [← two_smul ℝ]
    exact smul_ne_zero (by norm_num) (quotientReference_ne_zero k)
  have hplus_event :
      ∀ᶠ x in 𝓝 y,
        quotientReference k + matrixMulVecCLM U.1ᵀ x ≠ 0 := by
    exact
      (continuous_const.add
        (matrixMulVecCLM U.1ᵀ).continuous).continuousAt.eventually_ne
          hplus_base
  have hlocal :
      ∀ᶠ x in 𝓝 y, ‖x‖ = 1 →
        quotientPatchedAverage k H x =
          quotientCenteredAverage k H U x := by
    filter_upwards [hplus_event] with x hxplus hxnorm
    exact
      (quotientCenteredAverage_eq_patched_of_norm_one
        k H hHdiff.continuous U x hxnorm hxplus).symm
  have hpatched_diff :
      DifferentiableAt ℝ (quotientPatchedAverage k H) y :=
    (contDiff_one_quotientPatchedAverage
      k H hHdiff hHderiv).differentiable
        (by norm_num) y
  have hcentered_diff :
      DifferentiableAt ℝ (quotientCenteredAverage k H U) y := by
    change DifferentiableAt ℝ
      (fun x =>
        quotientAmbientAverage k H
          (vectorizedLeftMulCLM U.1
            (HDP.gaussianMatrixVectorize
              (quotientPlusSectionMatrix k
                (matrixMulVecCLM U.1ᵀ x))))) y
    apply
      ((contDiff_one_quotientAmbientAverage
        k H hHdiff hHderiv).differentiable
          (by norm_num) _).fun_comp'
    apply (vectorizedLeftMulCLM U.1).differentiableAt.fun_comp'
    have hsection :
        DifferentiableAt ℝ
          (fun x =>
            HDP.gaussianMatrixVectorize
              (quotientPlusSectionMatrix k x))
          (matrixMulVecCLM U.1ᵀ y) :=
      (contDiffAt_vectorize_quotientPlusSectionMatrix
        k (matrixMulVecCLM U.1ᵀ y) hplus_base).differentiableAt
          (by simp)
    exact hsection.fun_comp' y
      (matrixMulVecCLM U.1ᵀ).differentiableAt
  have hderiv_agree :
      fderiv ℝ (quotientPatchedAverage k H) y z =
        fderiv ℝ (quotientCenteredAverage k H U) y z :=
    fderiv_eq_of_eventuallyEq_on_unitSphere_of_tangent
      (quotientPatchedAverage k H)
      (quotientCenteredAverage k H U)
      y z hpatched_diff hcentered_diff hy htangent hlocal
  have hline_fderiv :
      HasDerivAt
        (fun t : ℝ =>
          quotientCenteredAverage k H U (y + t • z))
        (fderiv ℝ (quotientCenteredAverage k H U) y z) 0 := by
    have haffine :
        HasDerivAt (fun t : ℝ => y + t • z) z 0 := by
      simpa only [id_eq, one_smul] using
        ((hasDerivAt_id (𝕜 := ℝ) (x := (0 : ℝ))).smul_const z).const_add y
    exact hcentered_diff.hasFDerivAt.comp_hasDerivAt_of_eq
      0 haffine (by simp)
  have hline_explicit :
      HasDerivAt
        (fun t : ℝ =>
          quotientCenteredAverage k H U (y + t • z))
        (quotientAmbientDirectionalDerivative k H
          (HDP.gaussianMatrixVectorize U.1)
          (HDP.gaussianMatrixVectorize (U.1 * A))) 0 := by
    simpa only [y, a, A] using
      hasDerivAt_quotientCenteredAverage_orbit_line
        k H hHdiff hHderiv U z htangent
  rw [hderiv_agree]
  exact hline_fderiv.unique hline_explicit

lemma norm_sphereTangentProjection_apply_le
    {n : ℕ} (y v : EuclideanSpace ℝ (Fin n))
    (hy : ‖y‖ = 1) :
    ‖HDP.Appendix.sphereTangentProjection y v‖ ≤ ‖v‖ := by
  let c : ℝ := inner ℝ y v
  have hformula :
      ‖HDP.Appendix.sphereTangentProjection y v‖ ^ 2 =
        ‖v‖ ^ 2 - c ^ 2 := by
    unfold HDP.Appendix.sphereTangentProjection
    change ‖v - c • y‖ ^ 2 = ‖v‖ ^ 2 - c ^ 2
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul,
      Real.norm_eq_abs, hy]
    have hc : inner ℝ v y = c := by
      simpa only [c] using (real_inner_comm v y).symm
    rw [hc]
    simp only [mul_one, sq_abs]
    ring
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [hformula]
  exact sub_le_self _ (sq_nonneg c)

lemma euclideanDot_sphereTangentProjection
    {n : ℕ} (y v : EuclideanSpace ℝ (Fin n))
    (hy : ‖y‖ = 1) :
    euclideanDot y (HDP.Appendix.sphereTangentProjection y v) = 0 := by
  unfold HDP.Appendix.sphereTangentProjection
  change
    euclideanDot y
      (v - (inner ℝ y v) • y) = 0
  have hinner :
      inner ℝ y v = euclideanDot y v :=
    inner_euclidean_eq_euclideanDot y v
  rw [hinner]
  unfold euclideanDot
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  have hyy :
      ∑ i : Fin n, y i * y i = 1 := by
    change euclideanDot y y = 1
    rw [euclideanDot_self_eq_norm_sq, hy]
    norm_num
  have hsecond :
      (∑ x : Fin n,
          y x * ((∑ j : Fin n, y j * v j) * y x)) =
        (∑ j : Fin n, y j * v j) *
          ∑ x : Fin n, y x * y x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, hsecond, hyy]
  ring

lemma fderiv_quotientRegularizedRepresentative_tangent_sq_le_fiber
    (k : ℕ) (H : FrobeniusEuclidean (k + 3) → ℝ)
    (hHdiff : Differentiable ℝ H)
    (hHderiv : Continuous (fderiv ℝ H))
    {ε : ℝ} (hε : 0 < ε)
    (U : Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ)
    (z : EuclideanSpace ℝ (Fin (k + 3)))
    (htangent :
      euclideanDot
        (specialOrthogonalSphereOrbit
          (coordinateSpherePoint (secondCoordinateIndex k)) U) z = 0) :
    let y :=
      (specialOrthogonalSphereOrbit
        (coordinateSpherePoint (secondCoordinateIndex k)) U :
          EuclideanSpace ℝ (Fin (k + 3)))
    let a := matrixMulVecCLM U.1ᵀ z
    fderiv ℝ (quotientRegularizedRepresentative k H ε) y z ^ 2 ≤
      ∫ V : Matrix.specialOrthogonalGroup (Fin (k + 2)) ℝ,
        quotientFiberHorizontalDerivative k H U a V ^ 2
        ∂HDP.Chapter5.specialOrthogonalHaarMeasure (k + 2) := by
  dsimp only
  let y :=
    (specialOrthogonalSphereOrbit
      (coordinateSpherePoint (secondCoordinateIndex k)) U :
        EuclideanSpace ℝ (Fin (k + 3)))
  let a := matrixMulVecCLM U.1ᵀ z
  let A : Matrix (Fin (k + 3)) (Fin (k + 3)) ℝ :=
    Matrix.vecMulVec (fun i => a i)
        (fun j => quotientReference k j) -
      Matrix.vecMulVec (fun i => quotientReference k i)
        (fun j => a j)
  let q :=
    quotientAmbientAverage k H
      (HDP.gaussianMatrixVectorize U.1)
  let dQ :=
    quotientAmbientDirectionalDerivative k H
      (HDP.gaussianMatrixVectorize U.1)
      (HDP.gaussianMatrixVectorize (U.1 * A))
  let I :=
    ∫ V : Matrix.specialOrthogonalGroup (Fin (k + 2)) ℝ,
      quotientFiberHorizontalDerivative k H U a V ^ 2
      ∂HDP.Chapter5.specialOrthogonalHaarMeasure (k + 2)
  let R := quotientRegularizedRepresentative k H ε
  have hy : ‖y‖ = 1 := by
    exact norm_coe_mem_unitSphere
      (specialOrthogonalSphereOrbit
        (coordinateSpherePoint (secondCoordinateIndex k)) U)
  let ys : Metric.sphere
      (0 : EuclideanSpace ℝ (Fin (k + 3))) 1 :=
    ⟨y, by simpa [Metric.mem_sphere, dist_zero_right] using hy⟩
  have hq_nonneg : 0 ≤ q :=
    quotientAmbientAverage_nonneg k H _
  have hI_nonneg : 0 ≤ I := by
    exact integral_nonneg fun V => sq_nonneg _
  have hqpatch :
      quotientPatchedAverage k H y = q := by
    rw [show y =
        (specialOrthogonalSphereOrbit
          (coordinateSpherePoint (secondCoordinateIndex k)) U :
            EuclideanSpace ℝ (Fin (k + 3))) by rfl,
      quotientPatchedAverage_eq_rightAverage_orbit
        k H hHdiff.continuous U,
      ← quotientAmbientAverage_vectorize_specialOrthogonal
        k H hHdiff.continuous U]
  have hRdiff :
      DifferentiableAt ℝ R y :=
    (contDiff_one_quotientRegularizedRepresentative
      k H hHdiff hHderiv hε).differentiable
        (by norm_num) y
  have hqdiff :
      DifferentiableAt ℝ (quotientPatchedAverage k H) y :=
    (contDiff_one_quotientPatchedAverage
      k H hHdiff hHderiv).differentiable
        (by norm_num) y
  have hsquare_deriv :
      2 * R y * fderiv ℝ R y z =
        fderiv ℝ (quotientPatchedAverage k H) y z := by
    have hagree :
        fderiv ℝ (fun x => R x ^ 2) y z =
          fderiv ℝ
            (fun x => quotientPatchedAverage k H x + ε) y z :=
      fderiv_eq_of_eq_on_unitSphere_of_tangent
        (fun x => R x ^ 2)
        (fun x => quotientPatchedAverage k H x + ε)
        y z (hRdiff.pow 2) (hqdiff.add_const ε)
        hy htangent (fun x hx => by
          let xs : Metric.sphere
              (0 : EuclideanSpace ℝ (Fin (k + 3))) 1 :=
            ⟨x, by simpa [Metric.mem_sphere, dist_zero_right] using hx⟩
          exact quotientRegularizedRepresentative_sq_on_sphere
            k H hε.le xs)
    have hleft :
        fderiv ℝ (fun x => R x ^ 2) y z =
          2 * R y * fderiv ℝ R y z := by
      have hp := hRdiff.hasFDerivAt.pow 2
      rw [hp.fderiv]
      simp only [pow_one, ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [two_nsmul]
      ring
    have hright :
        fderiv ℝ
            (fun x => quotientPatchedAverage k H x + ε) y z =
          fderiv ℝ (quotientPatchedAverage k H) y z := by
      have ha := hqdiff.hasFDerivAt.add_const ε
      rw [ha.fderiv]
    rw [hleft, hright] at hagree
    exact hagree
  have hpatched_deriv :
      fderiv ℝ (quotientPatchedAverage k H) y z = dQ := by
    simpa only [y, a, A, dQ] using
      fderiv_quotientPatchedAverage_orbit_tangent
        k H hHdiff hHderiv U z htangent
  have hR_sq : R y ^ 2 = q + ε := by
    calc
      R y ^ 2 =
          quotientPatchedAverage k H y + ε := by
            exact quotientRegularizedRepresentative_sq_on_sphere
              k H hε.le ys
      _ = q + ε := by rw [hqpatch]
  have hcs : dQ ^ 2 ≤ q * (4 * I) := by
    simpa only [a, A, q, dQ, I] using
      quotientAmbientDirectionalDerivative_sq_le
        k H hHdiff.continuous hHderiv U a
  have hmain :
      R y ^ 2 * (fderiv ℝ R y z ^ 2) ≤ q * I := by
    rw [hpatched_deriv] at hsquare_deriv
    have hdQ_sq :
        dQ ^ 2 =
          4 * (R y ^ 2) * (fderiv ℝ R y z ^ 2) := by
      rw [← hsquare_deriv]
      ring
    rw [hdQ_sq] at hcs
    nlinarith
  have hR_sq_pos : 0 < R y ^ 2 := by
    rw [hR_sq]
    linarith
  have hratio : q / (R y ^ 2) ≤ 1 := by
    exact (div_le_one hR_sq_pos).2 (by
      rw [hR_sq]
      linarith)
  calc
    fderiv ℝ R y z ^ 2 =
        (R y ^ 2 * fderiv ℝ R y z ^ 2) / (R y ^ 2) := by
          apply (eq_div_iff hR_sq_pos.ne').2
          ring
    _ ≤ (q * I) / (R y ^ 2) :=
      (div_le_div_iff_of_pos_right hR_sq_pos).2 hmain
    _ = (q / (R y ^ 2)) * I := by ring
    _ ≤ 1 * I :=
      mul_le_mul_of_nonneg_right hratio hI_nonneg
    _ = I := one_mul I

lemma fderiv_quotientRegularizedRepresentative_tangent_sq_le_horizontal
    (k : ℕ) (H : FrobeniusEuclidean (k + 3) → ℝ)
    (hHdiff : Differentiable ℝ H)
    (hHderiv : Continuous (fderiv ℝ H))
    {ε : ℝ} (hε : 0 < ε)
    (U : Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ)
    (z : EuclideanSpace ℝ (Fin (k + 3)))
    (htangent :
      euclideanDot
        (specialOrthogonalSphereOrbit
          (coordinateSpherePoint (secondCoordinateIndex k)) U) z = 0) :
    let y :=
      (specialOrthogonalSphereOrbit
        (coordinateSpherePoint (secondCoordinateIndex k)) U :
          EuclideanSpace ℝ (Fin (k + 3)))
    fderiv ℝ (quotientRegularizedRepresentative k H ε) y z ^ 2 ≤
      2 *
        (∫ V : Matrix.specialOrthogonalGroup (Fin (k + 2)) ℝ,
          horizontalSquareEnergy
            (tangentGradient H
              (U * coordinateStabilizerHom
                (secondCoordinateIndex k) V))
            (secondCoordinateIndex k)
          ∂HDP.Chapter5.specialOrthogonalHaarMeasure (k + 2)) *
        ‖z‖ ^ 2 := by
  dsimp only
  let y :=
    (specialOrthogonalSphereOrbit
      (coordinateSpherePoint (secondCoordinateIndex k)) U :
        EuclideanSpace ℝ (Fin (k + 3)))
  let a := matrixMulVecCLM U.1ᵀ z
  have hfirst :
      fderiv ℝ (quotientRegularizedRepresentative k H ε) y z ^ 2 ≤
        ∫ V : Matrix.specialOrthogonalGroup (Fin (k + 2)) ℝ,
          quotientFiberHorizontalDerivative k H U a V ^ 2
          ∂HDP.Chapter5.specialOrthogonalHaarMeasure (k + 2) := by
    simpa only [y, a] using
      fderiv_quotientRegularizedRepresentative_tangent_sq_le_fiber
        k H hHdiff hHderiv hε U z htangent
  have hsecond :=
    integral_quotientFiberHorizontalDerivative_sq_le
      k H hHderiv U a
  have hanorm : ‖a‖ = ‖z‖ :=
    norm_matrixMulVecCLM_transpose_special U z
  calc
    fderiv ℝ (quotientRegularizedRepresentative k H ε) y z ^ 2 ≤
        ∫ V : Matrix.specialOrthogonalGroup (Fin (k + 2)) ℝ,
          quotientFiberHorizontalDerivative k H U a V ^ 2
          ∂HDP.Chapter5.specialOrthogonalHaarMeasure (k + 2) :=
      hfirst
    _ ≤
        ∫ V : Matrix.specialOrthogonalGroup (Fin (k + 2)) ℝ,
          2 *
            horizontalSquareEnergy
              (tangentGradient H
                (U * coordinateStabilizerHom
                  (secondCoordinateIndex k) V))
              (secondCoordinateIndex k) *
            ‖a‖ ^ 2
          ∂HDP.Chapter5.specialOrthogonalHaarMeasure (k + 2) :=
      hsecond
    _ =
        2 *
          (∫ V : Matrix.specialOrthogonalGroup (Fin (k + 2)) ℝ,
            horizontalSquareEnergy
              (tangentGradient H
                (U * coordinateStabilizerHom
                  (secondCoordinateIndex k) V))
              (secondCoordinateIndex k)
            ∂HDP.Chapter5.specialOrthogonalHaarMeasure (k + 2)) *
          ‖z‖ ^ 2 := by
      rw [hanorm, ← integral_const_mul, integral_mul_const]

lemma sphereTangentEnergy_quotientRegularizedRepresentative_orbit_le
    (k : ℕ) (H : FrobeniusEuclidean (k + 3) → ℝ)
    (hHdiff : Differentiable ℝ H)
    (hHderiv : Continuous (fderiv ℝ H))
    {ε : ℝ} (hε : 0 < ε)
    (U : Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ) :
    HDP.Appendix.sphereTangentEnergy
        (quotientRegularizedRepresentative k H ε)
        (specialOrthogonalSphereOrbit
          (coordinateSpherePoint (secondCoordinateIndex k)) U) ≤
      2 *
        ∫ V : Matrix.specialOrthogonalGroup (Fin (k + 2)) ℝ,
          horizontalSquareEnergy
            (tangentGradient H
              (U * coordinateStabilizerHom
                (secondCoordinateIndex k) V))
            (secondCoordinateIndex k)
          ∂HDP.Chapter5.specialOrthogonalHaarMeasure (k + 2) := by
  let y :=
    (specialOrthogonalSphereOrbit
      (coordinateSpherePoint (secondCoordinateIndex k)) U :
        EuclideanSpace ℝ (Fin (k + 3)))
  let E :=
    ∫ V : Matrix.specialOrthogonalGroup (Fin (k + 2)) ℝ,
      horizontalSquareEnergy
        (tangentGradient H
          (U * coordinateStabilizerHom
            (secondCoordinateIndex k) V))
        (secondCoordinateIndex k)
      ∂HDP.Chapter5.specialOrthogonalHaarMeasure (k + 2)
  let C := 2 * E
  let L :=
    (fderiv ℝ (quotientRegularizedRepresentative k H ε) y).comp
      (HDP.Appendix.sphereTangentProjection y)
  have hy : ‖y‖ = 1 := by
    exact norm_coe_mem_unitSphere
      (specialOrthogonalSphereOrbit
        (coordinateSpherePoint (secondCoordinateIndex k)) U)
  have hE : 0 ≤ E := by
    exact integral_nonneg fun V => by
      unfold horizontalSquareEnergy rowSquareEnergy
      positivity
  have hC : 0 ≤ C := mul_nonneg (by norm_num) hE
  have hscalar (v : EuclideanSpace ℝ (Fin (k + 3))) :
      L v ^ 2 ≤ C * ‖v‖ ^ 2 := by
    let z := HDP.Appendix.sphereTangentProjection y v
    have hztangent : euclideanDot y z = 0 :=
      euclideanDot_sphereTangentProjection y v hy
    have hzbound :
        fderiv ℝ (quotientRegularizedRepresentative k H ε) y z ^ 2 ≤
          C * ‖z‖ ^ 2 := by
      simpa only [y, z, E, C] using
        fderiv_quotientRegularizedRepresentative_tangent_sq_le_horizontal
          k H hHdiff hHderiv hε U z hztangent
    have hznorm : ‖z‖ ≤ ‖v‖ :=
      norm_sphereTangentProjection_apply_le y v hy
    have hzsq : ‖z‖ ^ 2 ≤ ‖v‖ ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hznorm
    change
      fderiv ℝ (quotientRegularizedRepresentative k H ε) y z ^ 2 ≤
        C * ‖v‖ ^ 2
    exact hzbound.trans (mul_le_mul_of_nonneg_left hzsq hC)
  have hLnorm : ‖L‖ ≤ Real.sqrt C := by
    apply ContinuousLinearMap.opNorm_le_bound L (Real.sqrt_nonneg C)
    intro v
    apply
      (sq_le_sq₀ (norm_nonneg (L v))
        (mul_nonneg (Real.sqrt_nonneg C) (norm_nonneg v))).mp
    calc
      ‖L v‖ ^ 2 = L v ^ 2 := by
        rw [Real.norm_eq_abs, sq_abs]
      _ ≤ C * ‖v‖ ^ 2 := hscalar v
      _ = (Real.sqrt C * ‖v‖) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hC]
  unfold HDP.Appendix.sphereTangentEnergy
  change ‖L‖ ^ 2 ≤ C
  calc
    ‖L‖ ^ 2 ≤ (Real.sqrt C) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg C)).2 hLnorm
    _ = C := Real.sq_sqrt hC

lemma integral_horizontalSquareEnergy_coordinateStabilizer_eq
    (k : ℕ) (H : FrobeniusEuclidean (k + 3) → ℝ)
    (hHderiv : Continuous (fderiv ℝ H)) :
    (∫ U : Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ,
        ∫ V : Matrix.specialOrthogonalGroup (Fin (k + 2)) ℝ,
          horizontalSquareEnergy
            (tangentGradient H
              (U * coordinateStabilizerHom
                (secondCoordinateIndex k) V))
            (secondCoordinateIndex k)
          ∂HDP.Chapter5.specialOrthogonalHaarMeasure (k + 2)
        ∂HDP.Chapter5.specialOrthogonalHaarMeasure (k + 3)) =
      ∫ U : Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ,
        horizontalSquareEnergy
          (tangentGradient H U) (secondCoordinateIndex k)
        ∂HDP.Chapter5.specialOrthogonalHaarMeasure (k + 3) := by
  let μ := HDP.Chapter5.specialOrthogonalHaarMeasure (k + 3)
  let ν := HDP.Chapter5.specialOrthogonalHaarMeasure (k + 2)
  let i := secondCoordinateIndex k
  let e :
      Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ → ℝ :=
    fun U => horizontalSquareEnergy (tangentGradient H U) i
  let F :
      Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ ×
        Matrix.specialOrthogonalGroup (Fin (k + 2)) ℝ → ℝ :=
    fun p => e (p.1 * coordinateStabilizerHom i p.2)
  have he : Continuous e := by
    exact continuous_tangentFieldHorizontalEnergy
      (continuous_tangentGradient hHderiv) i
  have hF : Continuous F := by
    exact he.comp
      (continuous_fst.mul
        ((continuous_coordinateStabilizerHom i).comp continuous_snd))
  have hFint : Integrable F (μ.prod ν) := by
    simpa only [IntegrableOn, Measure.restrict_univ] using
      hF.continuousOn.integrableOn_compact
        (μ := μ.prod ν) isCompact_univ
  have hright
      (V : Matrix.specialOrthogonalGroup (Fin (k + 2)) ℝ) :
      (∫ U : Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ,
          e (U * coordinateStabilizerHom i V) ∂μ) =
        ∫ U : Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ,
          e U ∂μ := by
    calc
      (∫ U : Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ,
          e (U * coordinateStabilizerHom i V) ∂μ) =
          ∫ W : Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ,
            e W
            ∂Measure.map
              (fun U : Matrix.specialOrthogonalGroup
                  (Fin (k + 3)) ℝ =>
                U * coordinateStabilizerHom i V) μ := by
            symm
            exact integral_map
              (by fun_prop : AEMeasurable
                (fun U : Matrix.specialOrthogonalGroup
                    (Fin (k + 3)) ℝ =>
                  U * coordinateStabilizerHom i V) μ)
              he.aestronglyMeasurable
      _ = ∫ U : Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ,
            e U ∂μ := by
          rw [HDP.Appendix.probabilityHaar_map_mul_right_eq_self
            μ (coordinateStabilizerHom i V)]
  change (∫ U, ∫ V, F (U, V) ∂ν ∂μ) = ∫ U, e U ∂μ
  rw [integral_integral_swap hFint]
  change
    (∫ V, ∫ U, e (U * coordinateStabilizerHom i V) ∂μ ∂ν) =
      ∫ U, e U ∂μ
  simp_rw [hright]
  simp

lemma continuous_conditionalHorizontalAverage
    (k : ℕ) (H : FrobeniusEuclidean (k + 3) → ℝ)
    (hHderiv : Continuous (fderiv ℝ H)) :
    Continuous
      (fun U : Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ =>
        ∫ V : Matrix.specialOrthogonalGroup (Fin (k + 2)) ℝ,
          horizontalSquareEnergy
            (tangentGradient H
              (U * coordinateStabilizerHom
                (secondCoordinateIndex k) V))
            (secondCoordinateIndex k)
          ∂HDP.Chapter5.specialOrthogonalHaarMeasure (k + 2)) := by
  let ν := HDP.Chapter5.specialOrthogonalHaarMeasure (k + 2)
  let i := secondCoordinateIndex k
  let F :
      Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ →
        Matrix.specialOrthogonalGroup (Fin (k + 2)) ℝ → ℝ :=
    fun U V =>
      horizontalSquareEnergy
        (tangentGradient H
          (U * coordinateStabilizerHom i V)) i
  have he :
      Continuous
        (fun U : Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ =>
          horizontalSquareEnergy (tangentGradient H U) i) :=
    continuous_tangentFieldHorizontalEnergy
      (continuous_tangentGradient hHderiv) i
  have hF : Continuous (Function.uncurry F) := by
    exact he.comp
      (continuous_fst.mul
        ((continuous_coordinateStabilizerHom i).comp continuous_snd))
  simpa only [ν, i, F, Measure.restrict_univ] using
    continuous_parametric_integral_of_continuous
      (μ := ν) hF (s := Set.univ) isCompact_univ

lemma integral_sphereTangentEnergy_quotientRegularizedRepresentative_le
    (k : ℕ) (H : FrobeniusEuclidean (k + 3) → ℝ)
    (hHdiff : Differentiable ℝ H)
    (hHderiv : Continuous (fderiv ℝ H))
    {ε : ℝ} (hε : 0 < ε) :
    (∫ u : Metric.sphere
          (0 : EuclideanSpace ℝ (Fin (k + 3))) 1,
        HDP.Appendix.sphereTangentEnergy
          (quotientRegularizedRepresentative k H ε) u
        ∂HDP.unitSphereMeasure
          (EuclideanSpace ℝ (Fin (k + 3)))) ≤
      2 *
        ∫ U : Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ,
          horizontalSquareEnergy
            (tangentGradient H U) (secondCoordinateIndex k)
          ∂HDP.Chapter5.specialOrthogonalHaarMeasure (k + 3) := by
  let μ := HDP.Chapter5.specialOrthogonalHaarMeasure (k + 3)
  let σ := HDP.unitSphereMeasure
    (EuclideanSpace ℝ (Fin (k + 3)))
  let orbit :=
    specialOrthogonalSphereOrbit
      (coordinateSpherePoint (secondCoordinateIndex k))
  let R := quotientRegularizedRepresentative k H ε
  let A :
      Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ → ℝ :=
    fun U =>
      ∫ V : Matrix.specialOrthogonalGroup (Fin (k + 2)) ℝ,
        horizontalSquareEnergy
          (tangentGradient H
            (U * coordinateStabilizerHom
              (secondCoordinateIndex k) V))
          (secondCoordinateIndex k)
        ∂HDP.Chapter5.specialOrthogonalHaarMeasure (k + 2)
  have hRderiv : Continuous (fderiv ℝ R) :=
    (contDiff_one_quotientRegularizedRepresentative
      k H hHdiff hHderiv hε).continuous_fderiv (by norm_num)
  have henergy :
      Continuous (HDP.Appendix.sphereTangentEnergy R) :=
    HDP.Appendix.continuous_sphereTangentEnergy hRderiv
  have horbit : Continuous orbit :=
    continuous_specialOrthogonalSphereOrbit
      (coordinateSpherePoint (secondCoordinateIndex k))
  have hleftInt :
      Integrable
        (fun U : Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ =>
          HDP.Appendix.sphereTangentEnergy R (orbit U)) μ := by
    have hc :
        Continuous
          (fun U : Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ =>
            HDP.Appendix.sphereTangentEnergy R (orbit U)) := by
      exact henergy.comp horbit
    simpa only [IntegrableOn, Measure.restrict_univ] using
      hc.continuousOn.integrableOn_compact
        (μ := μ) isCompact_univ
  have hA : Continuous A := by
    exact continuous_conditionalHorizontalAverage k H hHderiv
  have hrightInt : Integrable (fun U => 2 * A U) μ := by
    have hc : Continuous (fun U => 2 * A U) := by
      exact continuous_const.mul hA
    simpa only [IntegrableOn, Measure.restrict_univ] using
      hc.continuousOn.integrableOn_compact
        (μ := μ) isCompact_univ
  calc
    (∫ u : Metric.sphere
          (0 : EuclideanSpace ℝ (Fin (k + 3))) 1,
        HDP.Appendix.sphereTangentEnergy R u ∂σ) =
        ∫ U : Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ,
          HDP.Appendix.sphereTangentEnergy R (orbit U) ∂μ := by
      change
        (∫ u : Metric.sphere
              (0 : EuclideanSpace ℝ (Fin (k + 3))) 1,
            HDP.Appendix.sphereTangentEnergy R u
            ∂HDP.unitSphereMeasure
              (EuclideanSpace ℝ (Fin (k + 3)))) =
          ∫ U : Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ,
            HDP.Appendix.sphereTangentEnergy R (orbit U)
            ∂HDP.Chapter5.specialOrthogonalHaarMeasure (k + 3)
      rw [← map_specialOrthogonalSphereOrbit_second
        (k + 3) (by omega)]
      exact integral_map horbit.aemeasurable
        henergy.aestronglyMeasurable
    _ ≤ ∫ U : Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ,
          2 * A U ∂μ := by
      apply integral_mono hleftInt hrightInt
      intro U
      exact
        sphereTangentEnergy_quotientRegularizedRepresentative_orbit_le
          k H hHdiff hHderiv hε U
    _ = 2 * ∫ U : Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ,
          A U ∂μ := integral_const_mul 2 A
    _ = 2 * ∫ U : Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ,
          horizontalSquareEnergy
            (tangentGradient H U) (secondCoordinateIndex k) ∂μ := by
      rw [integral_horizontalSquareEnergy_coordinateStabilizer_eq
        k H hHderiv]

lemma tangentFieldHorizontalEnergy_sqrtTwo_tangentGradient
    (k : ℕ) (H : FrobeniusEuclidean (k + 3) → ℝ)
    (U : Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ) :
    tangentFieldHorizontalEnergy
        (fun W => Real.sqrt 2 • tangentGradient H W)
        (secondCoordinateIndex k) U =
      2 * horizontalSquareEnergy
        (tangentGradient H U) (secondCoordinateIndex k) := by
  unfold tangentFieldHorizontalEnergy horizontalSquareEnergy
    rowSquareEnergy
  simp only [Matrix.smul_apply, smul_eq_mul]
  calc
    2 * (∑ j : Fin (k + 3),
        (Real.sqrt 2 * tangentGradient H U
          (secondCoordinateIndex k) j) ^ 2) =
        2 * ((Real.sqrt 2) ^ 2 *
          ∑ j : Fin (k + 3),
            tangentGradient H U (secondCoordinateIndex k) j ^ 2) := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = 2 * (2 *
          ∑ j : Fin (k + 3),
            tangentGradient H U (secondCoordinateIndex k) j ^ 2) := by
      rw [Real.sq_sqrt (by norm_num)]

theorem continuous_boltzmannEntropy_add_const
    {α : Type*}
    [TopologicalSpace α] [T2Space α] [CompactSpace α]
    [SecondCountableTopology α]
    [MeasurableSpace α] [BorelSpace α]
    (μ : Measure α) [IsFiniteMeasure μ]
    (q : α → ℝ) (hq : Continuous q) :
    Continuous
      (fun ε : ℝ =>
        boltzmannEntropy μ (fun x => q x + ε)) := by
  let F : ℝ → α → ℝ := fun ε x => q x + ε
  let M : ℝ → ℝ := fun ε => ∫ x, F ε x ∂μ
  let J : ℝ → ℝ :=
    fun ε => ∫ x, F ε x * Real.log (F ε x) ∂μ
  have hF : Continuous (Function.uncurry F) := by
    exact (hq.comp continuous_snd).add continuous_fst
  have hM : Continuous M := by
    simpa only [M, Measure.restrict_univ] using
      continuous_parametric_integral_of_continuous
        (μ := μ) hF (s := Set.univ) isCompact_univ
  have hJ : Continuous J := by
    have hFlog :
        Continuous
          (fun p : ℝ × α =>
            F p.1 p.2 * Real.log (F p.1 p.2)) :=
      Real.continuous_mul_log.comp hF
    simpa only [J, Measure.restrict_univ] using
      continuous_parametric_integral_of_continuous
        (μ := μ) hFlog (s := Set.univ) isCompact_univ
  unfold boltzmannEntropy
  change Continuous (fun ε => J ε - M ε * Real.log (M ε))
  exact hJ.sub (Real.continuous_mul_log.comp hM)

theorem tendsto_boltzmannEntropy_add_const
    {α : Type*}
    [TopologicalSpace α] [T2Space α] [CompactSpace α]
    [SecondCountableTopology α]
    [MeasurableSpace α] [BorelSpace α]
    (μ : Measure α) [IsFiniteMeasure μ]
    (q : α → ℝ) (hq : Continuous q) :
    Filter.Tendsto
      (fun ε : ℝ =>
        boltzmannEntropy μ (fun x => q x + ε))
      (𝓝 0) (𝓝 (boltzmannEntropy μ q)) := by
  have h :=
    (continuous_boltzmannEntropy_add_const μ q hq).continuousAt
      (x := (0 : ℝ))
  change
    Filter.Tendsto
      (fun ε : ℝ =>
        boltzmannEntropy μ (fun x => q x + ε))
      (𝓝 0)
      (𝓝 (boltzmannEntropy μ (fun x => q x + 0))) at h
  simpa only [add_zero] using h

theorem secondCoordinate_quotient_entropy_add_epsilon_le_ambient_six
    (k : ℕ) (H : FrobeniusEuclidean (k + 3) → ℝ)
    (hHdiff : Differentiable ℝ H)
    (hHderiv : Continuous (fderiv ℝ H))
    {ε : ℝ} (hε : 0 < ε) :
    boltzmannEntropy
        (HDP.Chapter5.specialOrthogonalHaarMeasure (k + 3))
        (fun U =>
          rightAverage
              (coordinateStabilizerMeasure (secondCoordinateIndex k))
              (fun W => H (HDP.gaussianMatrixVectorize W.1) ^ 2) U +
            ε) ≤
      2 * (6 / (((k + 3 : ℕ) : ℝ))) *
        ∫ U : Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ,
          horizontalSquareEnergy
            (tangentGradient H U) (secondCoordinateIndex k)
          ∂HDP.Chapter5.specialOrthogonalHaarMeasure (k + 3) := by
  let G := Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ
  let μ := HDP.Chapter5.specialOrthogonalHaarMeasure (k + 3)
  let i := secondCoordinateIndex k
  let g : G → ℝ :=
    fun U => H (HDP.gaussianMatrixVectorize U.1)
  let qg : G → ℝ := fun U => g U ^ 2
  let gε : G → ℝ := fun U => Real.sqrt (qg U + ε)
  let R := quotientRegularizedRepresentative k H ε
  let X₂ : G → Matrix (Fin (k + 3)) (Fin (k + 3)) ℝ :=
    fun U => Real.sqrt 2 • tangentGradient H U
  have hg : Continuous g :=
    hHdiff.continuous.comp
      (continuous_gaussianMatrixVectorize.comp continuous_subtype_val)
  have hqg : Continuous qg := hg.pow 2
  have hgε : Continuous gε :=
    Real.continuous_sqrt.comp (hqg.add continuous_const)
  have hRdiff : Differentiable ℝ R :=
    (contDiff_one_quotientRegularizedRepresentative
      k H hHdiff hHderiv hε).differentiable (by norm_num)
  have hRderiv : Continuous (fderiv ℝ R) :=
    (contDiff_one_quotientRegularizedRepresentative
      k H hHdiff hHderiv hε).continuous_fderiv (by norm_num)
  obtain ⟨C, D, hC, hD, hRbound, hRderivBound⟩ :=
    quotientRegularizedRepresentative_exists_bounds
      k H hHdiff hHderiv hε
  have havg (U : G) :
      rightAverage (coordinateStabilizerMeasure i)
          (fun W => gε W ^ 2) U =
        rightAverage (coordinateStabilizerMeasure i) qg U + ε := by
    have hbaseInt :
        Integrable (fun W : G => qg (U * W))
          (coordinateStabilizerMeasure i) := by
      have hc : Continuous (fun W : G => qg (U * W)) := by
        exact hqg.comp (continuous_const.mul continuous_id)
      simpa only [IntegrableOn, Measure.restrict_univ] using
        hc.continuousOn.integrableOn_compact
          (μ := coordinateStabilizerMeasure i) isCompact_univ
    unfold rightAverage
    simp_rw [show ∀ W : G, gε W ^ 2 = qg W + ε by
      intro W
      exact Real.sq_sqrt
        (add_nonneg (sq_nonneg (g W)) hε.le)]
    change
      (∫ W : G, qg (U * W) + ε
          ∂coordinateStabilizerMeasure i) =
        (∫ W : G, qg (U * W)
          ∂coordinateStabilizerMeasure i) + ε
    rw [integral_add hbaseInt (integrable_const ε), integral_const]
    simp
  have hRepresentative (U : G) :
      rightAverage (coordinateStabilizerMeasure i)
          (fun W => gε W ^ 2) U =
        R (specialOrthogonalSphereOrbit
          (coordinateSpherePoint i) U) ^ 2 := by
    calc
      rightAverage (coordinateStabilizerMeasure i)
          (fun W => gε W ^ 2) U =
          rightAverage (coordinateStabilizerMeasure i) qg U + ε :=
        havg U
      _ = quotientPatchedAverage k H
            (specialOrthogonalSphereOrbit
              (coordinateSpherePoint i) U) + ε := by
        rw [quotientPatchedAverage_eq_rightAverage_orbit
          k H hHdiff.continuous U]
      _ = R (specialOrthogonalSphereOrbit
            (coordinateSpherePoint i) U) ^ 2 := by
        symm
        exact quotientRegularizedRepresentative_sq_on_sphere
          k H hε.le
            (specialOrthogonalSphereOrbit
              (coordinateSpherePoint i) U)
  have hX₂ (U : G) :
      tangentFieldHorizontalEnergy X₂ i U =
        2 * horizontalSquareEnergy (tangentGradient H U) i := by
    simpa only [G, X₂, i] using
      tangentFieldHorizontalEnergy_sqrtTwo_tangentGradient k H U
  have hEnergy :
      (∫ u : Metric.sphere
            (0 : EuclideanSpace ℝ (Fin (k + 3))) 1,
          HDP.Appendix.sphereTangentEnergy R u
          ∂HDP.unitSphereMeasure
            (EuclideanSpace ℝ (Fin (k + 3)))) ≤
        ∫ U : G,
          tangentFieldHorizontalEnergy X₂ i U ∂μ := by
    calc
      (∫ u : Metric.sphere
            (0 : EuclideanSpace ℝ (Fin (k + 3))) 1,
          HDP.Appendix.sphereTangentEnergy R u
          ∂HDP.unitSphereMeasure
            (EuclideanSpace ℝ (Fin (k + 3)))) ≤
          2 * ∫ U : G,
            horizontalSquareEnergy
              (tangentGradient H U) i
              ∂μ := by
        simpa only [G, μ, i, R] using
          integral_sphereTangentEnergy_quotientRegularizedRepresentative_le
            k H hHdiff hHderiv hε
      _ = ∫ U : G,
            tangentFieldHorizontalEnergy X₂ i U ∂μ := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards []
        intro U
        exact (hX₂ U).symm
  have hlsi :=
    secondCoordinate_quotient_entropy_le_three
      k gε X₂ R hRdiff hRderiv hC hD
      hRbound hRderivBound hRepresentative hEnergy
  have havgfun :
      rightAverage (coordinateStabilizerMeasure i)
          (fun W => gε W ^ 2) =
        fun U => rightAverage (coordinateStabilizerMeasure i) qg U + ε := by
    funext U
    exact havg U
  have hscaled :
      (∫ U : G, tangentFieldHorizontalEnergy X₂ i U ∂μ) =
        2 * ∫ U : G,
          horizontalSquareEnergy (tangentGradient H U) i ∂μ := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards []
    intro U
    exact hX₂ U
  rw [havgfun, hscaled] at hlsi
  simpa only [G, μ, i, g, qg] using
    (show
      boltzmannEntropy μ
          (fun U =>
            rightAverage (coordinateStabilizerMeasure i) qg U + ε) ≤
        2 * (6 / (((k + 3 : ℕ) : ℝ))) *
          ∫ U : G,
            horizontalSquareEnergy (tangentGradient H U) i ∂μ by
      calc
        _ ≤ 2 * (3 / (((k + 3 : ℕ) : ℝ))) *
              (2 * ∫ U : G,
                horizontalSquareEnergy (tangentGradient H U) i ∂μ) :=
          hlsi
        _ = 2 * (6 / (((k + 3 : ℕ) : ℝ))) *
              ∫ U : G,
                horizontalSquareEnergy (tangentGradient H U) i ∂μ := by
          ring)

theorem secondCoordinate_quotient_entropy_le_ambient_six
    (k : ℕ) (H : FrobeniusEuclidean (k + 3) → ℝ)
    (hHdiff : Differentiable ℝ H)
    (hHderiv : Continuous (fderiv ℝ H)) :
    boltzmannEntropy
        (HDP.Chapter5.specialOrthogonalHaarMeasure (k + 3))
        (rightAverage
          (coordinateStabilizerMeasure (secondCoordinateIndex k))
          (fun W => H (HDP.gaussianMatrixVectorize W.1) ^ 2)) ≤
      2 * (6 / (((k + 3 : ℕ) : ℝ))) *
        ∫ U : Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ,
          horizontalSquareEnergy
            (tangentGradient H U) (secondCoordinateIndex k)
          ∂HDP.Chapter5.specialOrthogonalHaarMeasure (k + 3) := by
  let G := Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ
  let μ := HDP.Chapter5.specialOrthogonalHaarMeasure (k + 3)
  let i := secondCoordinateIndex k
  let qg : G → ℝ :=
    fun U => H (HDP.gaussianMatrixVectorize U.1) ^ 2
  let q : G → ℝ :=
    rightAverage (coordinateStabilizerMeasure i) qg
  let B :=
    2 * (6 / (((k + 3 : ℕ) : ℝ))) *
      ∫ U : G,
        horizontalSquareEnergy (tangentGradient H U) i ∂μ
  have hqg : Continuous qg :=
    (hHdiff.continuous.comp
      (continuous_gaussianMatrixVectorize.comp
        continuous_subtype_val)).pow 2
  have hq : Continuous q :=
    continuous_rightAverage_coordinateStabilizer i hqg
  have htend :
      Filter.Tendsto
        (fun ε : ℝ =>
          boltzmannEntropy μ (fun U => q U + ε))
        (𝓝 0) (𝓝 (boltzmannEntropy μ q)) :=
    tendsto_boltzmannEntropy_add_const μ q hq
  have htendWithin :
      Filter.Tendsto
        (fun ε : ℝ =>
          boltzmannEntropy μ (fun U => q U + ε))
        (𝓝[>] 0) (𝓝 (boltzmannEntropy μ q)) :=
    htend.mono_left inf_le_left
  have hevent :
      ∀ᶠ ε : ℝ in 𝓝[>] 0,
        boltzmannEntropy μ (fun U => q U + ε) ≤ B := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact
      secondCoordinate_quotient_entropy_add_epsilon_le_ambient_six
        k H hHdiff hHderiv hε
  have hfinal : boltzmannEntropy μ q ≤ B :=
    le_of_tendsto htendWithin hevent
  simpa only [G, μ, i, qg, q, B] using hfinal

end

end HDP.Appendix.SpecialOrthogonal
