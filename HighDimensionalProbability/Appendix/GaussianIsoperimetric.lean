import HighDimensionalProbability.Appendix.Infra.PoincareIsoperimetricLimit
import HighDimensionalProbability.Chapter5_ConcentrationWithoutIndependence

/-!
# Gaussian isoperimetry

This is the closed-neighborhood formulation printed on physical PDF page 154
(printed page 146).
-/

open MeasureTheory ProbabilityTheory Set Metric InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace

namespace HDP.Chapter5

/-- Euclidean half-space used in the Gaussian isoperimetric declaration. -/
def gaussianHalfspace {n : ℕ} (u : EuclideanSpace ℝ (Fin n)) (a : ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | inner ℝ u x ≤ a}

/-- **HDP Theorem 5.2.2 (Gaussian isoperimetric inequality).**

The proof is the classical Poincaré limit of spherical isoperimetry. -/
theorem gaussian_isoperimetric {n : ℕ} [NeZero n]
    (A : Set (EuclideanSpace ℝ (Fin n))) (hA : MeasurableSet A)
    (u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1)
    (a ε : ℝ) (hε : 0 < ε)
    (hmass : stdGaussian (EuclideanSpace ℝ (Fin n)) A =
      stdGaussian (EuclideanSpace ℝ (Fin n)) (gaussianHalfspace u a)) :
    stdGaussian (EuclideanSpace ℝ (Fin n))
        (HDP.Appendix.closedExpansion ε (gaussianHalfspace u a)) ≤
      stdGaussian (EuclideanSpace ℝ (Fin n))
        (HDP.Appendix.closedExpansion ε A) := by
  simpa [gaussianHalfspace, HDP.Appendix.gaussianLinearHalfspace] using
    HDP.Appendix.gaussian_isoperimetric_poincare
      A hA u hu a ε hε (by
        simpa [gaussianHalfspace,
          HDP.Appendix.gaussianLinearHalfspace] using hmass)

end HDP.Chapter5
