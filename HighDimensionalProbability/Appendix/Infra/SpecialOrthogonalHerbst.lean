import HighDimensionalProbability.Appendix.Infra.SpecialOrthogonalLipschitzApproximation
import HighDimensionalProbability.Appendix.Infra.Herbst

/-!
# Direct Herbst argument for ambient smooth functions on `SO(n)`

The stabilizer induction naturally proves a logarithmic-Sobolev inequality
for restrictions of ambient `C¹` functions.  This file turns precisely that
form into a centered sub-Gaussian MGF bound.  Keeping the statement direct in
the ambient representative avoids making a Dirichlet energy depend on a
noncanonical choice of extension.
-/

open Matrix MeasureTheory ProbabilityTheory Real
open scoped NNReal RealInnerProductSpace Topology

namespace HDP.Appendix.SpecialOrthogonal

noncomputable section

private lemma boltzmannEntropy_sq_exp_half'
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (t : ℝ) :
    HDP.Appendix.boltzmannEntropy μ
        (fun ω => Real.exp (t * X ω / 2) ^ 2) =
      t * ∫ ω, X ω * Real.exp (t * X ω) ∂μ -
        mgf X μ t * Real.log (mgf X μ t) := by
  have hsquare (ω : Ω) :
      Real.exp (t * X ω / 2) ^ 2 =
        Real.exp (t * X ω) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [HDP.Appendix.boltzmannEntropy, mgf]
  simp_rw [hsquare]
  congr 1
  calc
    (∫ ω, Real.exp (t * X ω) *
          Real.log (Real.exp (t * X ω)) ∂μ) =
        ∫ ω, t * (X ω * Real.exp (t * X ω)) ∂μ := by
      apply integral_congr_ae
      filter_upwards with ω
      rw [Real.log_exp]
      ring
    _ = t * ∫ ω, X ω * Real.exp (t * X ω) ∂μ :=
      integral_const_mul _ _

private lemma fderiv_exp_half_norm_sq_le
    {n : ℕ}
    (H : FrobeniusEuclidean n → ℝ)
    (hHdiff : Differentiable ℝ H)
    (hHbound : ∀ y, ‖fderiv ℝ H y‖ ≤ 1)
    (t : ℝ) (y : FrobeniusEuclidean n) :
    ‖fderiv ℝ
        (fun z => Real.exp ((t / 2) * H z)) y‖ ^ 2 ≤
      (t ^ 2 / 4) * Real.exp (t * H y) := by
  rw [show fderiv ℝ
      (fun z => Real.exp ((t / 2) * H z)) y =
        Real.exp ((t / 2) * H y) •
          ((t / 2) • fderiv ℝ H y) by
    rw [fderiv_exp]
    · rw [fderiv_const_mul hHdiff.differentiableAt]
    · fun_prop]
  rw [norm_smul, norm_smul, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hb2 : ‖fderiv ℝ H y‖ ^ 2 ≤ 1 := by
    nlinarith [norm_nonneg (fderiv ℝ H y), hHbound y]
  have he :
      Real.exp ((t / 2) * H y) ^ 2 =
        Real.exp (t * H y) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [mul_pow, mul_pow, he]
  have hab : |t / 2| ^ 2 = t ^ 2 / 4 := by
    rw [sq_abs]
    ring
  rw [hab]
  calc
    Real.exp (t * H y) *
          (t ^ 2 / 4 * ‖fderiv ℝ H y‖ ^ 2) ≤
        Real.exp (t * H y) * (t ^ 2 / 4 * 1) := by
      gcongr
    _ = t ^ 2 / 4 * Real.exp (t * H y) := by ring

/-- An ambient `C¹` logarithmic-Sobolev estimate on `SO(n)` gives the
standard centered MGF bound for every ambient function whose derivative norm
is at most one. -/
theorem hasSubgaussianMGF_centered_of_ambient_logSobolev
    (n : ℕ)
    (μ : Measure (Matrix.specialOrthogonalGroup (Fin n) ℝ))
    [IsProbabilityMeasure μ]
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hLSI :
      ∀ K : FrobeniusEuclidean n → ℝ,
        Differentiable ℝ K →
        Continuous (fderiv ℝ K) →
        HDP.Appendix.boltzmannEntropy μ
            (fun U =>
              K (specialOrthogonalEmbedding n U) ^ 2) ≤
          2 * ρ *
            ∫ U,
              HDP.matrixFrobeniusNorm
                (tangentGradient K U) ^ 2 ∂μ)
    (H : FrobeniusEuclidean n → ℝ)
    (hHdiff : Differentiable ℝ H)
    (hHf : Continuous (fderiv ℝ H))
    (hHbound : ∀ y, ‖fderiv ℝ H y‖ ≤ 1) :
    HasSubgaussianMGF
      (fun U =>
        H (specialOrthogonalEmbedding n U) -
          ∫ V,
            H (specialOrthogonalEmbedding n V) ∂μ)
      ⟨ρ, hρ⟩ μ := by
  let X : Matrix.specialOrthogonalGroup (Fin n) ℝ → ℝ :=
    fun U => H (specialOrthogonalEmbedding n U)
  have hXcont : Continuous X :=
    hHdiff.continuous.comp
      (continuous_specialOrthogonalEmbedding n)
  have hExp :
      ∀ t : ℝ,
        Integrable (fun U => Real.exp (t * X U)) μ := by
    intro t
    have hcont :
        Continuous (fun U => Real.exp (t * X U)) := by
      fun_prop
    simpa using
      hcont.continuousOn.integrableOn_compact
        (μ := μ) isCompact_univ
  have hHerbst :
      HDP.Appendix.HasHerbstEntropyBound μ X ρ := by
    refine ⟨hExp, ?_⟩
    intro t _
    let K : FrobeniusEuclidean n → ℝ :=
      fun y => Real.exp ((t / 2) * H y)
    have hHc1 : ContDiff ℝ 1 H :=
      contDiff_one_iff_fderiv.2 ⟨hHdiff, hHf⟩
    have hKc1 : ContDiff ℝ 1 K := by
      dsimp [K]
      fun_prop
    have hKdiff : Differentiable ℝ K :=
      hKc1.differentiable (by norm_num)
    have hKf : Continuous (fderiv ℝ K) :=
      hKc1.continuous_fderiv (by norm_num)
    have hpoint
        (U : Matrix.specialOrthogonalGroup (Fin n) ℝ) :
        HDP.matrixFrobeniusNorm
              (tangentGradient K U) ^ 2 ≤
          (t ^ 2 / 4) * Real.exp (t * X U) := by
      calc
        HDP.matrixFrobeniusNorm
              (tangentGradient K U) ^ 2 ≤
            ‖fderiv ℝ K
              (specialOrthogonalEmbedding n U)‖ ^ 2 :=
          tangentGradient_energy_le_fderiv K U
        _ ≤ (t ^ 2 / 4) * Real.exp (t * X U) := by
          simpa [K, X] using
            fderiv_exp_half_norm_sq_le
              H hHdiff hHbound t
                (specialOrthogonalEmbedding n U)
    have henergyCont :
        Continuous
          (fun U :
              Matrix.specialOrthogonalGroup (Fin n) ℝ =>
            HDP.matrixFrobeniusNorm
              (tangentGradient K U) ^ 2) := by
      have htangent : Continuous (tangentGradient K) :=
        continuous_tangentGradient hKf
      unfold HDP.matrixFrobeniusNorm
      fun_prop
    have henergyInt :
        Integrable
          (fun U :
              Matrix.specialOrthogonalGroup (Fin n) ℝ =>
            HDP.matrixFrobeniusNorm
              (tangentGradient K U) ^ 2) μ := by
      simpa using
        henergyCont.continuousOn.integrableOn_compact
          (μ := μ) isCompact_univ
    have hrhsInt :
        Integrable
          (fun U =>
            (t ^ 2 / 4) * Real.exp (t * X U)) μ :=
      (hExp t).const_mul _
    have hint :
        (∫ U,
            HDP.matrixFrobeniusNorm
              (tangentGradient K U) ^ 2 ∂μ) ≤
          (t ^ 2 / 4) * mgf X μ t := by
      calc
        (∫ U,
            HDP.matrixFrobeniusNorm
              (tangentGradient K U) ^ 2 ∂μ) ≤
            ∫ U,
              (t ^ 2 / 4) *
                Real.exp (t * X U) ∂μ :=
          integral_mono henergyInt hrhsInt hpoint
        _ = (t ^ 2 / 4) * mgf X μ t := by
          rw [mgf, integral_const_mul]
    have hlsi := hLSI K hKdiff hKf
    have hleft :
        HDP.Appendix.boltzmannEntropy μ
            (fun U =>
              K (specialOrthogonalEmbedding n U) ^ 2) =
          t * ∫ U,
              X U * Real.exp (t * X U) ∂μ -
            mgf X μ t *
              Real.log (mgf X μ t) := by
      rw [← boltzmannEntropy_sq_exp_half' μ X t]
      congr 1
      funext U
      dsimp [K, X]
      congr 1
      ring
    rw [hleft] at hlsi
    calc
      t * ∫ U, X U * Real.exp (t * X U) ∂μ -
            mgf X μ t * Real.log (mgf X μ t) ≤
          2 * ρ *
            ∫ U,
              HDP.matrixFrobeniusNorm
                (tangentGradient K U) ^ 2 ∂μ :=
        hlsi
      _ ≤
          2 * ρ *
            ((t ^ 2 / 4) * mgf X μ t) := by
        exact mul_le_mul_of_nonneg_left hint
          (mul_nonneg (by norm_num) hρ)
      _ = (ρ * t ^ 2 / 2) * mgf X μ t := by
        ring
  simpa [X] using
    HDP.Appendix.hasSubgaussianMGF_centered_of_hasHerbstEntropyBound
      μ X hρ hHerbst

end

end HDP.Appendix.SpecialOrthogonal
