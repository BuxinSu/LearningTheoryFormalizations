import HighDimensionalProbability.Appendix.Infra.SphereRegularization
import HighDimensionalProbability.Appendix.Infra.SphereGaussianFactorization

/-!
# Convergence of regularized radial observables

This file supplies the measure-theoretic half of the Gaussian proof of the
spherical logarithmic Sobolev inequality.  A bounded continuous observable,
composed with the smooth regularized radial projection

`x ↦ x / sqrt (‖x‖² + ε²)`,

converges in Gaussian integral to its spherical average as `ε ↓ 0`.
-/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Topology

namespace HDP.Appendix

noncomputable section

private lemma ae_ne_zero_stdGaussian
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [Nontrivial E] :
    ∀ᵐ x : E ∂stdGaussian E, x ≠ 0 := by
  rw [← HDP.gaussianRadialMeasure_eq_stdGaussian E,
    HDP.gaussianRadialMeasure]
  have hvol : ∀ᵐ x : E ∂(volume : Measure E), x ≠ 0 := by
    have hzero : (volume : Measure E) ({0} : Set E) = 0 :=
      measure_singleton 0
    have hmem : ({0} : Set E)ᶜ ∈ ae (volume : Measure E) :=
      compl_mem_ae_iff.mpr hzero
    filter_upwards [hmem] with x hx
    simpa using hx
  exact (withDensity_absolutelyContinuous
    (volume : Measure E) _).ae_le hvol

private lemma coe_gaussianDirection_eq_inv_norm_smul
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [Nontrivial E] (x : E) (hx : x ≠ 0) :
    ((HDP.gaussianDirection x :
        Metric.sphere (0 : E) 1) : E) =
      ‖x‖⁻¹ • x := by
  let y : ({0}ᶜ : Set E) := ⟨x, by simpa⟩
  have h := congrArg Subtype.val
    (HDP.gaussianDirection_coe (E := E) y)
  simpa [y, homeomorphUnitSphereProd_apply_fst_coe] using h

/-- Integrating an ambient continuous observable of Gaussian direction is
the same as integrating its restriction against normalized spherical
measure. -/
lemma integral_comp_gaussianDirection
    (k : ℕ)
    (H : EuclideanSpace ℝ (Fin (k + 3)) → ℝ)
    (hH : Continuous H) :
    (∫ x : EuclideanSpace ℝ (Fin (k + 3)),
        H (HDP.gaussianDirection x)
          ∂stdGaussian (EuclideanSpace ℝ (Fin (k + 3)))) =
      ∫ u : Metric.sphere
          (0 : EuclideanSpace ℝ (Fin (k + 3))) 1,
        H u
          ∂HDP.unitSphereMeasure
            (EuclideanSpace ℝ (Fin (k + 3))):= by
  rw [← HDP.map_gaussianDirection_stdGaussian
    (E := EuclideanSpace ℝ (Fin (k + 3)))]
  simpa [Function.comp_apply] using
    (integral_map
      (HDP.measurable_gaussianDirection
        (E := EuclideanSpace ℝ (Fin (k + 3)))).aemeasurable
      (hH.comp continuous_subtype_val).aestronglyMeasurable).symm

/-- Dominated convergence from the regularized radial projection to the
uniform spherical law. -/
theorem tendsto_integral_comp_regularizedDirection
    (k : ℕ)
    (H : EuclideanSpace ℝ (Fin (k + 3)) → ℝ)
    (hH : Continuous H)
    {C : ℝ} (hH_bound : ∀ x, ‖H x‖ ≤ C) :
    Filter.Tendsto
      (fun ε : ℝ =>
        ∫ x : EuclideanSpace ℝ (Fin (k + 3)),
          H (regularizedDirection ε x)
            ∂stdGaussian
              (EuclideanSpace ℝ (Fin (k + 3))))
      (𝓝[>] 0)
      (𝓝
        (∫ u : Metric.sphere
            (0 : EuclideanSpace ℝ (Fin (k + 3))) 1,
          H u
            ∂HDP.unitSphereMeasure
              (EuclideanSpace ℝ (Fin (k + 3))))) := by
  let E := EuclideanSpace ℝ (Fin (k + 3))
  let γ := stdGaussian E
  have hlim :
      ∀ᵐ x : E ∂γ,
        Filter.Tendsto
          (fun ε : ℝ => H (regularizedDirection ε x))
          (𝓝[>] 0)
          (𝓝 (H (HDP.gaussianDirection x))) := by
    filter_upwards [ae_ne_zero_stdGaussian E] with x hx
    have hreg :
        Filter.Tendsto
          (fun ε : ℝ => regularizedDirection ε x)
          (𝓝[>] 0) (𝓝 (‖x‖⁻¹ • x)) :=
      (tendsto_regularizedDirection x hx).mono_left
        nhdsWithin_le_nhds
    rw [coe_gaussianDirection_eq_inv_norm_smul x hx]
    change Filter.Tendsto
      (H ∘ fun ε : ℝ => regularizedDirection ε x)
      (𝓝[>] 0) (𝓝 (H (‖x‖⁻¹ • x)))
    exact hH.continuousAt.tendsto.comp hreg
  have hint :
      Filter.Tendsto
        (fun ε : ℝ =>
          ∫ x : E, H (regularizedDirection ε x) ∂γ)
        (𝓝[>] 0)
        (𝓝 (∫ x : E, H (HDP.gaussianDirection x) ∂γ)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun _ : E => C)
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact Continuous.aestronglyMeasurable
        (hH.comp
          (differentiable_regularizedDirection hε).continuous)
    · filter_upwards [] with ε
      filter_upwards [] with x
      exact hH_bound _
    · exact integrable_const_iff.2 (Or.inr inferInstance)
    · exact hlim
  simpa [E, γ, integral_comp_gaussianDirection k H hH] using hint

/-- The Boltzmann entropy of a bounded continuous ambient observable also
converges from the regularized Gaussian model to its spherical restriction. -/
theorem tendsto_boltzmannEntropy_comp_regularizedDirection
    (k : ℕ)
    (H : EuclideanSpace ℝ (Fin (k + 3)) → ℝ)
    (hH : Continuous H)
    {C : ℝ} (hC : 0 ≤ C)
    (hH_bound : ∀ x, ‖H x‖ ≤ C) :
    Filter.Tendsto
      (fun ε : ℝ =>
        boltzmannEntropy
          (stdGaussian
            (EuclideanSpace ℝ (Fin (k + 3))))
          (fun x => H (regularizedDirection ε x) ^ 2))
      (𝓝[>] 0)
      (𝓝
        (boltzmannEntropy
          (HDP.unitSphereMeasure
            (EuclideanSpace ℝ (Fin (k + 3))))
          (fun u : Metric.sphere
              (0 : EuclideanSpace ℝ (Fin (k + 3))) 1 =>
            H u ^ 2))) := by
  let Hsq : EuclideanSpace ℝ (Fin (k + 3)) → ℝ :=
    fun x => H x ^ 2
  have hHsq : Continuous Hsq := hH.pow 2
  have hsq_le : ∀ x, H x ^ 2 ≤ C ^ 2 := by
    intro x
    have hx : |H x| ≤ C := by
      simpa [Real.norm_eq_abs] using hH_bound x
    nlinarith [abs_nonneg (H x), sq_abs (H x)]
  have hHsq_bound : ∀ x, ‖Hsq x‖ ≤ C ^ 2 := by
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hsq_le x
  have hsq_lim :=
    tendsto_integral_comp_regularizedDirection
      k Hsq hHsq hHsq_bound
  let Hlog : EuclideanSpace ℝ (Fin (k + 3)) → ℝ :=
    fun x => Hsq x * Real.log (Hsq x)
  have hHlog : Continuous Hlog := by
    exact Real.continuous_mul_log.comp hHsq
  obtain ⟨B, hB⟩ :=
    GaussianPoincare.mul_log_bounded_on_Icc
      C hC
  have hHlog_bound : ∀ x, ‖Hlog x‖ ≤ B := by
    intro x
    rw [Real.norm_eq_abs]
    exact hB (Hsq x) ⟨sq_nonneg _, hsq_le x⟩
  have hlog_lim :=
    tendsto_integral_comp_regularizedDirection
      k Hlog hHlog hHlog_bound
  have hmean_mul_log :=
    Real.continuous_mul_log.continuousAt.tendsto.comp hsq_lim
  unfold boltzmannEntropy
  exact hlog_lim.sub hmean_mul_log

end

end HDP.Appendix
