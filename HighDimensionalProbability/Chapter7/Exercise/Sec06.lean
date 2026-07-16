import HighDimensionalProbability.Chapter6.Main
import HighDimensionalProbability.Chapter5_ConcentrationWithoutIndependence

/-!
# Book Chapter 7 exercises attached to Section 7.6

Exercises 7.24--7.26 are used by the random-projection main line and belong
to core.  The two matrix-sketching conclusions of Exercise 7.27 are the only
non-load-bearing proof payloads in this leaf.
-/

open Matrix MeasureTheory ProbabilityTheory Set WithLp
open scoped BigOperators ENNReal NNReal Matrix.Norms.L2Operator
  RealInnerProductSpace

noncomputable section

namespace HDP.Chapter7.Exercise

/-- Expected norm of a fixed matrix after Haar projection onto an
`m`-dimensional subspace.

**Lean implementation helper.** -/
def projectedMatrixNormMean {n k : ℕ} (m : ℕ)
    (A : Matrix (Fin n) (Fin k) ℝ) : ℝ :=
  ∫ P : HDP.Chapter5.Grassmannian n m, HDP.matrixOpNorm (P.1 * A)
    ∂HDP.Chapter5.grassmannHaarMeasure n m

/-- **Exercise 7.27(a).** Operator norm of a Haar-projected fixed matrix.

**Book Exercise 7.27(a).** -/
theorem exercise_7_27a :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {m n k : ℕ}, 0 < n → 0 < m → m ≤ n →
      ∀ A : Matrix (Fin n) (Fin k) ℝ,
        c * ((Real.sqrt n)⁻¹ * HDP.matrixFrobeniusNorm A +
          Real.sqrt ((m : ℝ) / n) * HDP.matrixOpNorm A) ≤
            projectedMatrixNormMean m A ∧
        projectedMatrixNormMean m A ≤
          C * ((Real.sqrt n)⁻¹ * HDP.matrixFrobeniusNorm A +
            Real.sqrt ((m : ℝ) / n) * HDP.matrixOpNorm A) := by
  -- EXERCISE-SORRY (category A): non-load-bearing Exercise 7.27(a).
  sorry

/-- Canonical iid standard-Gaussian matrix used for Gaussian sketching.

**Lean implementation helper.** -/
def sketchGaussianMatrix {m n : ℕ}
    (g : EuclideanSpace ℝ (Fin m × Fin n)) : Matrix (Fin m) (Fin n) ℝ :=
  fun i j => g (i, j)

/-- Expected norm of a Gaussian sketch of a fixed matrix.

**Lean implementation helper.** -/
def gaussianSketchNormMean {m n k : ℕ}
    (A : Matrix (Fin n) (Fin k) ℝ) : ℝ :=
  ∫ g : EuclideanSpace ℝ (Fin m × Fin n),
    HDP.matrixOpNorm (sketchGaussianMatrix g * A)
      ∂stdGaussian (EuclideanSpace ℝ (Fin m × Fin n))

/-- **Exercise 7.27(b).** Gaussian matrix sketching. The Frobenius norm is
the corrected PDF quantity (the old conversion accidentally wrote `A_F`).

**Book Exercise 7.27(b).** -/
theorem exercise_7_27b :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {m n k : ℕ}, 0 < m →
      ∀ A : Matrix (Fin n) (Fin k) ℝ,
        c * (HDP.matrixFrobeniusNorm A +
          Real.sqrt m * HDP.matrixOpNorm A) ≤
            gaussianSketchNormMean (m := m) A ∧
        gaussianSketchNormMean (m := m) A ≤
          C * (HDP.matrixFrobeniusNorm A +
            Real.sqrt m * HDP.matrixOpNorm A) := by
  -- EXERCISE-SORRY (category A): non-load-bearing Exercise 7.27(b).
  sorry

end HDP.Chapter7.Exercise
