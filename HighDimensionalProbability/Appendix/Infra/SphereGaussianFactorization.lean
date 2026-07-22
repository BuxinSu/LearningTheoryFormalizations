import HighDimensionalProbability.Appendix.Infra.GaussianInverseRadius
import Mathlib.Probability.Independence.Integration

/-!
# Gaussian radial-angular factorization

The direction and radius of a standard Gaussian vector are independent.
Combining that fact with the exact inverse-square radial moment gives the
weighted polar identity used in the Gaussian proof of the spherical
logarithmic Sobolev inequality.
-/

open MeasureTheory ProbabilityTheory

namespace HDP.Appendix

noncomputable section

/-- An inverse-square radial weight separates from every continuous angular
observable under standard Gaussian measure. -/
theorem integral_gaussianDirection_mul_norm_sq_inv
    (k : ℕ)
    (F : Metric.sphere
      (0 : EuclideanSpace ℝ (Fin (k + 3))) 1 → ℝ)
    (hF : Continuous F) :
    (∫ x : EuclideanSpace ℝ (Fin (k + 3)),
        F (HDP.gaussianDirection x) * (‖x‖ ^ 2)⁻¹
          ∂stdGaussian (EuclideanSpace ℝ (Fin (k + 3)))) =
      (((k + 1 : ℕ) : ℝ))⁻¹ *
        ∫ u, F u
          ∂HDP.unitSphereMeasure
            (EuclideanSpace ℝ (Fin (k + 3))) := by
  let E := EuclideanSpace ℝ (Fin (k + 3))
  let γ := stdGaussian E
  let σ := HDP.unitSphereMeasure E
  have hInd :
      HDP.gaussianDirection (E := E) ⟂ᵢ[γ]
        (fun x : E => ‖x‖) :=
    HDP.indepFun_gaussianDirection_norm_stdGaussian (E := E)
  have hfactor :=
    hInd.integral_fun_comp_mul_comp
      (HDP.measurable_gaussianDirection (E := E)).aemeasurable
      measurable_norm.aemeasurable
      hF.aestronglyMeasurable
      (Measurable.aestronglyMeasurable
        (by fun_prop :
          Measurable (fun r : ℝ => (r ^ 2)⁻¹)))
  have hangular :
      (∫ x : E, F (HDP.gaussianDirection x) ∂γ) =
        ∫ u, F u ∂σ := by
    change
      (∫ x : E, F (HDP.gaussianDirection x)
        ∂stdGaussian E) =
        ∫ u, F u ∂HDP.unitSphereMeasure E
    rw [← HDP.map_gaussianDirection_stdGaussian (E := E)]
    exact (integral_map
      (HDP.measurable_gaussianDirection (E := E)).aemeasurable
      hF.aestronglyMeasurable).symm
  have hradial :
      (∫ x : E, (‖x‖ ^ 2)⁻¹ ∂γ) =
        (((k + 1 : ℕ) : ℝ))⁻¹ :=
    integral_norm_sq_inv_stdGaussian k
  change
    (∫ x : E,
        F (HDP.gaussianDirection x) *
          ((fun r : ℝ => (r ^ 2)⁻¹) ‖x‖) ∂γ) = _
  rw [hfactor, hangular, hradial]
  ring

end

end HDP.Appendix
