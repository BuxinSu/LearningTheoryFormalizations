import HighDimensionalProbability.Appendix.Infra.SphericalEndpoint

/-!
# Spherical isoperimetry

The positive-cap-mass hypothesis removes the zero-area singleton-cap
counterexample in the old declaration.  Neighborhoods use the source's
closed chordal expansion (physical PDF page 152 / printed page 144).
-/

open MeasureTheory Set Metric InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace

namespace HDP.Chapter5

/-- **HDP Theorem 5.1.5 (spherical isoperimetric inequality).**

The proof in the appendix follows the Baernstein--Taylor two-point
polarization argument.  Compactness in the Hausdorff hyperspace produces a
moment-minimizing cap; continuity of metric expansions removes the auxiliary
radius slack and then passes to arbitrary measurable competitors.
-/
theorem spherical_isoperimetric {n : ℕ} (hn : 2 ≤ n)
    (A : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1))
    (hA : MeasurableSet A) (u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1)
    (a ε : ℝ) (hε : 0 < ε)
    (hcap : 0 < HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
      (sphericalCap u a))
    (hmass : HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)) A =
      HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)) (sphericalCap u a)) :
    HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
        (HDP.Appendix.closedExpansion ε (sphericalCap u a)) ≤
      HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
        (HDP.Appendix.closedExpansion ε A) := by
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  exact HDP.Appendix.spherical_isoperimetric_measurable
    hn A hA u hu a ε hε hcap hmass

end HDP.Chapter5
