import HighDimensionalProbability.Appendix.Infra.SphereRegularizationConvergence

/-!
# Spherical logarithmic Sobolev inequality from Gaussian regularization

This file completes the analytic Gaussian-to-sphere transfer for bounded
`C¹` ambient functions.  The energy in the limiting inequality is the
ambient derivative restricted to the tangent hyperplane, so the statement
is suitable for quotient-energy arguments on compact groups.
-/

open MeasureTheory ProbabilityTheory Real
open scoped RealInnerProductSpace Topology

namespace HDP.Appendix

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Orthogonal projection onto the hyperplane perpendicular to `u`.  On the
unit sphere this is the tangent-space projection. -/
def sphereTangentProjection (u : E) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E - (innerSL ℝ u).smulRight u

/-- Squared norm of the ambient derivative restricted to the tangent
hyperplane at a point of the unit sphere. -/
def sphereTangentEnergy
    (H : E → ℝ) (u : Metric.sphere (0 : E) 1) : ℝ :=
  ‖(fderiv ℝ H (u : E)).comp
      (sphereTangentProjection (u : E))‖ ^ 2

/-- Squared derivative energy of an ambient function after composition
with the regularized radial projection. -/
def regularizedDirectionEnergy
    (H : E → ℝ) (ε : ℝ) (x : E) : ℝ :=
  ‖(fderiv ℝ H (regularizedDirection ε x)).comp
      (fderiv ℝ (regularizedDirection ε) x)‖ ^ 2

lemma continuous_sphereTangentProjection :
    Continuous (sphereTangentProjection (E := E)) := by
  unfold sphereTangentProjection
  fun_prop

lemma continuous_sphereTangentEnergy
    {H : E → ℝ}
    (hH_grad_cont : Continuous (fun x => fderiv ℝ H x)) :
    Continuous (sphereTangentEnergy H) := by
  unfold sphereTangentEnergy
  have hgrad :
      Continuous (fun u : Metric.sphere (0 : E) 1 =>
        fderiv ℝ H (u : E)) :=
    hH_grad_cont.comp continuous_subtype_val
  have hproj :
      Continuous (fun u : Metric.sphere (0 : E) 1 =>
        sphereTangentProjection (u : E)) :=
    continuous_sphereTangentProjection.comp continuous_subtype_val
  exact (hgrad.clm_comp hproj).norm.pow 2

lemma continuous_regularizedDirectionEnergy
    {H : E → ℝ}
    (hH_grad_cont : Continuous (fun x => fderiv ℝ H x))
    {ε : ℝ} (hε : 0 < ε) :
    Continuous (regularizedDirectionEnergy H ε) := by
  unfold regularizedDirectionEnergy
  have hleft :
      Continuous (fun x : E =>
        fderiv ℝ H (regularizedDirection ε x)) :=
    hH_grad_cont.comp
      (differentiable_regularizedDirection hε).continuous
  exact
    (hleft.clm_comp
      (continuous_fderiv_regularizedDirection hε)).norm.pow 2

/-- The regularized direction always lies in the closed unit ball. -/
lemma norm_regularizedDirection_le_one
    {ε : ℝ} (hε : 0 < ε) (x : E) :
    ‖regularizedDirection ε x‖ ≤ 1 := by
  have hr : 0 < Real.sqrt (‖x‖ ^ 2 + ε ^ 2) := by
    apply Real.sqrt_pos.2
    nlinarith [sq_nonneg ‖x‖, sq_pos_of_pos hε]
  rw [regularizedDirection, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hr)]
  rw [inv_mul_le_one₀ hr]
  simpa [Real.sqrt_sq (norm_nonneg x)] using
    Real.sqrt_le_sqrt
      (show ‖x‖ ^ 2 ≤ ‖x‖ ^ 2 + ε ^ 2 from
        le_add_of_nonneg_right (sq_nonneg ε))

/-- For fixed positive regularization, the derivative is globally bounded
by the reciprocal regularization scale. -/
lemma norm_fderiv_regularizedDirection_le_inv_epsilon
    {ε : ℝ} (hε : 0 < ε) (x : E) :
    ‖fderiv ℝ (regularizedDirection ε) x‖ ≤ ε⁻¹ := by
  refine (norm_fderiv_regularizedDirection_le hε x).trans ?_
  have hr :
      0 < Real.sqrt (‖x‖ ^ 2 + ε ^ 2) := by
    apply Real.sqrt_pos.2
    nlinarith [sq_nonneg ‖x‖, sq_pos_of_pos hε]
  apply (inv_le_inv₀ hr hε).2
  calc
    ε = Real.sqrt (ε ^ 2) := (Real.sqrt_sq hε.le).symm
    _ ≤ Real.sqrt (‖x‖ ^ 2 + ε ^ 2) :=
      Real.sqrt_le_sqrt
        (show ε ^ 2 ≤ ‖x‖ ^ 2 + ε ^ 2 from
          le_add_of_nonneg_left (sq_nonneg ‖x‖))

/-- The inverse-square Gaussian radius is integrable in every dimension
`k + 3`. -/
lemma integrable_norm_sq_inv_stdGaussian (k : ℕ) :
    Integrable
      (fun x : EuclideanSpace ℝ (Fin (k + 3)) =>
        (‖x‖ ^ 2)⁻¹)
      (stdGaussian (EuclideanSpace ℝ (Fin (k + 3)))) := by
  by_contra h
  have hz := integral_undef h
  rw [integral_norm_sq_inv_stdGaussian k] at hz
  have hne : (((k + 1 : ℕ) : ℝ))⁻¹ ≠ 0 := by positivity
  exact hne hz

private lemma ae_ne_zero_stdGaussian
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [Nontrivial E] :
    ∀ᵐ x : E ∂stdGaussian E, x ≠ 0 := by
  rw [← HDP.gaussianRadialMeasure_eq_stdGaussian E,
    HDP.gaussianRadialMeasure]
  have hvol : ∀ᵐ x : E ∂(volume : Measure E), x ≠ 0 := by
    rw [ae_iff]
    simpa using (measure_singleton (μ := (volume : Measure E)) (0 : E))
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

/-- The limiting radial derivative is inverse radius times tangent
projection at the Gaussian direction. -/
lemma radialDirectionDerivative_eq_inv_norm_smul_tangent
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [Nontrivial E] (x : E) (hx : x ≠ 0) :
    radialDirectionDerivative x =
      ‖x‖⁻¹ •
        sphereTangentProjection
          ((HDP.gaussianDirection x :
            Metric.sphere (0 : E) 1) : E) := by
  have hdir := coe_gaussianDirection_eq_inv_norm_smul x hx
  ext v
  simp only [radialDirectionDerivative, sphereTangentProjection,
    sub_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
  rw [hdir]
  simp only [inner_smul_left, smul_smul, starRingEnd_apply,
    star_trivial, ContinuousLinearMap.id_apply]
  rw [smul_sub, smul_smul]
  congr 1
  ring

/-- Pointwise convergence of the regularized composition energy away from
the Gaussian origin. -/
lemma tendsto_regularizedDirectionEnergy
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [Nontrivial E]
    (H : E → ℝ)
    (hH_grad_cont : Continuous (fun y => fderiv ℝ H y))
    (x : E) (hx : x ≠ 0) :
    Filter.Tendsto
      (fun ε : ℝ => regularizedDirectionEnergy H ε x)
      (𝓝[>] 0)
      (𝓝 (
        ‖(fderiv ℝ H
            ((HDP.gaussianDirection x :
              Metric.sphere (0 : E) 1) : E)).comp
            (radialDirectionDerivative x)‖ ^ 2)) := by
  have hreg :
      Filter.Tendsto
        (fun ε : ℝ => regularizedDirection ε x)
        (𝓝[>] 0) (𝓝 (‖x‖⁻¹ • x)) :=
    (tendsto_regularizedDirection x hx).mono_left
      nhdsWithin_le_nhds
  have hgrad :
      Filter.Tendsto
        (fun ε : ℝ =>
          fderiv ℝ H (regularizedDirection ε x))
        (𝓝[>] 0) (𝓝 (fderiv ℝ H (‖x‖⁻¹ • x))) :=
    hH_grad_cont.continuousAt.tendsto.comp hreg
  have hcomp :
      Filter.Tendsto
        (fun ε : ℝ =>
          (fderiv ℝ H (regularizedDirection ε x)).comp
            (fderiv ℝ (regularizedDirection ε) x))
        (𝓝[>] 0)
        (𝓝
          ((fderiv ℝ H (‖x‖⁻¹ • x)).comp
            (radialDirectionDerivative x))) :=
    by
      simpa [Function.comp_def] using
        ((ContinuousLinearMap.compL ℝ E E ℝ).continuous₂.tendsto
          (fderiv ℝ H (‖x‖⁻¹ • x),
            radialDirectionDerivative x)).comp
          (hgrad.prodMk_nhds
            (tendsto_fderiv_regularizedDirection x hx))
  simpa [regularizedDirectionEnergy,
    coe_gaussianDirection_eq_inv_norm_smul x hx] using
    hcomp.norm.pow 2

/-- The limiting radial composition energy splits into angular tangent
energy and inverse-square radial weight. -/
lemma radialDirectionEnergy_eq_sphereTangentEnergy_mul_inv_norm_sq
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [Nontrivial E]
    (H : E → ℝ) (x : E) (hx : x ≠ 0) :
    ‖(fderiv ℝ H
        ((HDP.gaussianDirection x :
          Metric.sphere (0 : E) 1) : E)).comp
        (radialDirectionDerivative x)‖ ^ 2 =
      sphereTangentEnergy H (HDP.gaussianDirection x) *
        (‖x‖ ^ 2)⁻¹ := by
  rw [radialDirectionDerivative_eq_inv_norm_smul_tangent x hx,
    ContinuousLinearMap.comp_smul]
  simp only [sphereTangentEnergy, norm_smul, norm_inv, norm_norm]
  rw [← inv_pow]
  ring

/-- Gaussian integrals of the regularized composition energies converge to
the spherical tangent energy, with the exact inverse-square radial moment
`1 / (k + 1)`. -/
theorem tendsto_integral_regularizedDirectionEnergy
    (k : ℕ)
    (H : EuclideanSpace ℝ (Fin (k + 3)) → ℝ)
    (hH_grad_cont : Continuous (fun y => fderiv ℝ H y))
    {D : ℝ} (hD : 0 ≤ D)
    (hH_grad_bound : ∀ y, ‖fderiv ℝ H y‖ ≤ D) :
    Filter.Tendsto
      (fun ε : ℝ =>
        ∫ x : EuclideanSpace ℝ (Fin (k + 3)),
          regularizedDirectionEnergy H ε x
            ∂stdGaussian
              (EuclideanSpace ℝ (Fin (k + 3))))
      (𝓝[>] 0)
      (𝓝 (
        (((k + 1 : ℕ) : ℝ))⁻¹ *
          ∫ u : Metric.sphere
              (0 : EuclideanSpace ℝ (Fin (k + 3))) 1,
            sphereTangentEnergy H u
              ∂HDP.unitSphereMeasure
                (EuclideanSpace ℝ (Fin (k + 3))))) := by
  let E := EuclideanSpace ℝ (Fin (k + 3))
  let γ := stdGaussian E
  have hbound :
      ∀ᶠ ε : ℝ in 𝓝[>] 0,
        ∀ᵐ x : E ∂γ,
          ‖regularizedDirectionEnergy H ε x‖ ≤
            D ^ 2 * (‖x‖ ^ 2)⁻¹ := by
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    filter_upwards [ae_ne_zero_stdGaussian E] with x hx
    have hcomp :
        ‖(fderiv ℝ H (regularizedDirection ε x)).comp
            (fderiv ℝ (regularizedDirection ε) x)‖ ≤
          D * ‖x‖⁻¹ := by
      calc
        ‖(fderiv ℝ H (regularizedDirection ε x)).comp
            (fderiv ℝ (regularizedDirection ε) x)‖ ≤
            ‖fderiv ℝ H (regularizedDirection ε x)‖ *
              ‖fderiv ℝ (regularizedDirection ε) x‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ D * ‖x‖⁻¹ :=
          mul_le_mul
            (hH_grad_bound _)
            (norm_fderiv_regularizedDirection_le_inv_norm hε hx)
            (norm_nonneg _)
            hD
    have hsq :
        regularizedDirectionEnergy H ε x ≤
          D ^ 2 * (‖x‖ ^ 2)⁻¹ := by
      unfold regularizedDirectionEnergy
      calc
        ‖(fderiv ℝ H (regularizedDirection ε x)).comp
            (fderiv ℝ (regularizedDirection ε) x)‖ ^ 2 ≤
            (D * ‖x‖⁻¹) ^ 2 :=
          (sq_le_sq₀ (norm_nonneg _)
            (mul_nonneg hD (inv_nonneg.mpr (norm_nonneg x)))).2
            hcomp
        _ = D ^ 2 * (‖x‖ ^ 2)⁻¹ := by
          rw [← inv_pow]
          ring
    rw [Real.norm_eq_abs,
      abs_of_nonneg
        (show 0 ≤ regularizedDirectionEnergy H ε x by
          exact sq_nonneg _)]
    exact hsq
  have hmeas :
      ∀ᶠ ε : ℝ in 𝓝[>] 0,
        AEStronglyMeasurable
          (regularizedDirectionEnergy H ε) γ := by
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    exact
      (continuous_regularizedDirectionEnergy
        hH_grad_cont hε).aestronglyMeasurable
  have hlim :
      ∀ᵐ x : E ∂γ,
        Filter.Tendsto
          (fun ε : ℝ => regularizedDirectionEnergy H ε x)
          (𝓝[>] 0)
          (𝓝
            (sphereTangentEnergy H (HDP.gaussianDirection x) *
              (‖x‖ ^ 2)⁻¹)) := by
    filter_upwards [ae_ne_zero_stdGaussian E] with x hx
    simpa only [
      radialDirectionEnergy_eq_sphereTangentEnergy_mul_inv_norm_sq
        H x hx] using
      tendsto_regularizedDirectionEnergy H hH_grad_cont x hx
  have hdom :
      Integrable
        (fun x : E => D ^ 2 * (‖x‖ ^ 2)⁻¹) γ := by
    simpa [E, γ] using
      (integrable_norm_sq_inv_stdGaussian k).const_mul (D ^ 2)
  have hint :
      Filter.Tendsto
        (fun ε : ℝ =>
          ∫ x : E, regularizedDirectionEnergy H ε x ∂γ)
        (𝓝[>] 0)
        (𝓝
          (∫ x : E,
            sphereTangentEnergy H (HDP.gaussianDirection x) *
              (‖x‖ ^ 2)⁻¹ ∂γ)) :=
    tendsto_integral_filter_of_dominated_convergence
      (fun x : E => D ^ 2 * (‖x‖ ^ 2)⁻¹)
      hmeas hbound hdom hlim
  rw [integral_gaussianDirection_mul_norm_sq_inv
    k (sphereTangentEnergy H)
    (continuous_sphereTangentEnergy hH_grad_cont)] at hint
  simpa [E, γ] using hint

/-- Euclidean Gaussian logarithmic Sobolev applied to a bounded ambient
function after positive radial regularization. -/
lemma gaussian_logSobolev_regularizedDirection
    (k : ℕ)
    (H : EuclideanSpace ℝ (Fin (k + 3)) → ℝ)
    (hH_diff : Differentiable ℝ H)
    (hH_grad_cont : Continuous (fun y => fderiv ℝ H y))
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hH_bound : ∀ y, ‖H y‖ ≤ C)
    (hH_grad_bound : ∀ y, ‖fderiv ℝ H y‖ ≤ D)
    {ε : ℝ} (hε : 0 < ε) :
    boltzmannEntropy
        (stdGaussian (EuclideanSpace ℝ (Fin (k + 3))))
        (fun x => H (regularizedDirection ε x) ^ 2) ≤
      2 * ∫ x : EuclideanSpace ℝ (Fin (k + 3)),
        regularizedDirectionEnergy H ε x
          ∂stdGaussian
            (EuclideanSpace ℝ (Fin (k + 3))) := by
  let g : EuclideanSpace ℝ (Fin (k + 3)) → ℝ :=
    H ∘ regularizedDirection ε
  have hg_diff : Differentiable ℝ g :=
    hH_diff.comp (differentiable_regularizedDirection hε)
  have hg_fderiv :
      ∀ x : EuclideanSpace ℝ (Fin (k + 3)),
        fderiv ℝ g x =
          (fderiv ℝ H (regularizedDirection ε x)).comp
            (fderiv ℝ (regularizedDirection ε) x) := by
    intro x
    simpa [g, Function.comp_def] using
      (fderiv_comp
        (𝕜 := ℝ) (f := regularizedDirection ε)
        (g := H) (x := x)
        (hH_diff (regularizedDirection ε x))
        ((differentiable_regularizedDirection hε) x))
  have hg_grad_cont :
      Continuous (fun x => fderiv ℝ g x) := by
    simp_rw [hg_fderiv]
    exact
      (hH_grad_cont.comp
        (differentiable_regularizedDirection hε).continuous).clm_comp
        (continuous_fderiv_regularizedDirection hε)
  have hg_bound : ∀ x, ‖g x‖ ≤ C := by
    intro x
    exact hH_bound _
  have hg_grad_bound :
      ∀ x, ‖fderiv ℝ g x‖ ≤ D * ε⁻¹ := by
    intro x
    rw [hg_fderiv]
    calc
      ‖(fderiv ℝ H (regularizedDirection ε x)).comp
          (fderiv ℝ (regularizedDirection ε) x)‖ ≤
          ‖fderiv ℝ H (regularizedDirection ε x)‖ *
            ‖fderiv ℝ (regularizedDirection ε) x‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ D * ε⁻¹ :=
        mul_le_mul
          (hH_grad_bound _)
          (norm_fderiv_regularizedDirection_le_inv_epsilon hε x)
          (norm_nonneg _)
          hD
  have hlsi :=
    gaussian_logSobolev_euclidean_of_bound
      hg_diff hg_grad_cont hC hg_bound hg_grad_bound
  simp_rw [hg_fderiv] at hlsi
  simpa [g, Function.comp_def, regularizedDirectionEnergy] using hlsi

/-- Entropy of a bounded continuous observable composed with regularized
direction converges to its spherical entropy. -/
theorem tendsto_boltzmannEntropy_sq_comp_regularizedDirection
    (k : ℕ)
    (H : EuclideanSpace ℝ (Fin (k + 3)) → ℝ)
    (hH : Continuous H)
    {C : ℝ} (hC : 0 ≤ C)
    (hH_bound : ∀ x, ‖H x‖ ≤ C) :
    Filter.Tendsto
      (fun ε : ℝ =>
        boltzmannEntropy
          (stdGaussian (EuclideanSpace ℝ (Fin (k + 3))))
          (fun x => H (regularizedDirection ε x) ^ 2))
      (𝓝[>] 0)
      (𝓝
        (boltzmannEntropy
          (HDP.unitSphereMeasure
            (EuclideanSpace ℝ (Fin (k + 3))))
          (fun u => H u ^ 2))) := by
  let J : EuclideanSpace ℝ (Fin (k + 3)) → ℝ :=
    fun x => H x ^ 2 * Real.log (H x ^ 2)
  have hsq_cont : Continuous (fun x => H x ^ 2) := hH.pow 2
  have hJ_cont : Continuous J := hsq_cont.mul_log
  have hsq_bound : ∀ x, ‖H x ^ 2‖ ≤ C ^ 2 := by
    intro x
    rw [norm_pow]
    exact (sq_le_sq₀ (norm_nonneg _) hC).2 (hH_bound x)
  obtain ⟨B, hB⟩ :=
    GaussianPoincare.mul_log_bounded_on_Icc C hC
  have hJ_bound : ∀ x, ‖J x‖ ≤ B := by
    intro x
    rw [Real.norm_eq_abs]
    apply hB
    refine ⟨sq_nonneg _, ?_⟩
    have hx : |H x| ≤ C := by
      simpa [Real.norm_eq_abs] using hH_bound x
    calc
      H x ^ 2 = |H x| ^ 2 := (sq_abs (H x)).symm
      _ ≤ C ^ 2 := by nlinarith [abs_nonneg (H x)]
  have hJlim :=
    tendsto_integral_comp_regularizedDirection
      k J hJ_cont hJ_bound
  have hsqlim :=
    tendsto_integral_comp_regularizedDirection
      k (fun x => H x ^ 2) hsq_cont hsq_bound
  unfold boltzmannEntropy
  exact hJlim.sub
    (Real.continuous_mul_log.continuousAt.tendsto.comp hsqlim)

/-- Spherical logarithmic Sobolev inequality for bounded ambient `C¹`
functions.  The right side uses only the derivative tangent to the sphere,
and the constant is the sharp Gaussian-radial transfer constant
`2 / (k + 1)` in ambient dimension `k + 3`. -/
theorem sphere_logSobolev_bounded_C1
    (k : ℕ)
    (H : EuclideanSpace ℝ (Fin (k + 3)) → ℝ)
    (hH_diff : Differentiable ℝ H)
    (hH_grad_cont : Continuous (fun y => fderiv ℝ H y))
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hH_bound : ∀ y, ‖H y‖ ≤ C)
    (hH_grad_bound : ∀ y, ‖fderiv ℝ H y‖ ≤ D) :
    boltzmannEntropy
        (HDP.unitSphereMeasure
          (EuclideanSpace ℝ (Fin (k + 3))))
        (fun u => H u ^ 2) ≤
      2 * (
        (((k + 1 : ℕ) : ℝ))⁻¹ *
          ∫ u : Metric.sphere
              (0 : EuclideanSpace ℝ (Fin (k + 3))) 1,
            sphereTangentEnergy H u
              ∂HDP.unitSphereMeasure
                (EuclideanSpace ℝ (Fin (k + 3)))) := by
  have hEntropy :=
    tendsto_boltzmannEntropy_sq_comp_regularizedDirection
      k H hH_diff.continuous hC hH_bound
  have hEnergy :=
    tendsto_integral_regularizedDirectionEnergy
      k H hH_grad_cont hD hH_grad_bound
  have hEnergy_two :
      Filter.Tendsto
        (fun ε : ℝ =>
          2 * ∫ x : EuclideanSpace ℝ (Fin (k + 3)),
            regularizedDirectionEnergy H ε x
              ∂stdGaussian
                (EuclideanSpace ℝ (Fin (k + 3))))
        (𝓝[>] 0)
        (𝓝
          (2 * (
            (((k + 1 : ℕ) : ℝ))⁻¹ *
              ∫ u : Metric.sphere
                  (0 : EuclideanSpace ℝ (Fin (k + 3))) 1,
                sphereTangentEnergy H u
                  ∂HDP.unitSphereMeasure
                    (EuclideanSpace ℝ (Fin (k + 3)))))) :=
    tendsto_const_nhds.mul hEnergy
  have hineq :
      (fun ε : ℝ =>
        boltzmannEntropy
          (stdGaussian (EuclideanSpace ℝ (Fin (k + 3))))
          (fun x => H (regularizedDirection ε x) ^ 2)) ≤ᶠ[𝓝[>] 0]
        (fun ε : ℝ =>
          2 * ∫ x : EuclideanSpace ℝ (Fin (k + 3)),
            regularizedDirectionEnergy H ε x
              ∂stdGaussian
                (EuclideanSpace ℝ (Fin (k + 3)))) := by
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    exact
      gaussian_logSobolev_regularizedDirection
        k H hH_diff hH_grad_cont hC hD
        hH_bound hH_grad_bound hε
  exact le_of_tendsto_of_tendsto hEntropy hEnergy_two hineq

end

end HDP.Appendix
