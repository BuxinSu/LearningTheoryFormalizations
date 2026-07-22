import HighDimensionalProbability.Prelude.Sphere

/-! Basic spherical-cap notation, kept below the isoperimetric theorem. -/

open Set Metric InnerProductSpace
open scoped RealInnerProductSpace

namespace HDP.Chapter5

/-- A spherical cap in the normalized unit-sphere model. -/
def sphericalCap {n : ℕ} (u : EuclideanSpace ℝ (Fin n)) (a : ℝ) :
    Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
  {x | inner ℝ u (x : EuclideanSpace ℝ (Fin n)) ≤ a}

end HDP.Chapter5
