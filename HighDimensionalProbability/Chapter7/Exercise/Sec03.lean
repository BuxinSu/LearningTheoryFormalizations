import HighDimensionalProbability.Chapter6.Main

/-!
# Book Chapter 7 exercises attached to Section 7.3

The rank-one Frobenius estimate (Exercise 7.10) and the eventual monotonicity
fact in Exercise 7.12 are load-bearing and live in core.  This file contains
the two non-load-bearing Gaussian-matrix applications.
-/

open Matrix MeasureTheory ProbabilityTheory Set WithLp
open scoped BigOperators ENNReal NNReal Matrix.Norms.L2Operator
  RealInnerProductSpace

noncomputable section

namespace HDP.Chapter7.Exercise

/-- A canonical GOE matrix synthesized from independent standard Gaussian
coordinates. Only the upper-triangular coordinates are used.

**Lean implementation helper.** -/
def canonicalGOE {n : ℕ}
    (g : EuclideanSpace ℝ (Fin n × Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j =>
    if i = j then Real.sqrt 2 * g (i, i)
    else if i < j then g (i, j) else g (j, i)

/-- **Exercise 7.11(a).** Sharp expectation bound for the GOE operator norm.

**Book Exercise 7.11(a).** -/
theorem exercise_7_11a {n : ℕ} (_hn : 0 < n) :
    (∫ g : EuclideanSpace ℝ (Fin n × Fin n),
      HDP.matrixOpNorm (canonicalGOE g)
        ∂stdGaussian (EuclideanSpace ℝ (Fin n × Fin n))) ≤
      2 * Real.sqrt n := by
  -- EXERCISE-SORRY (category A): non-load-bearing Exercise 7.11(a).
  sorry

/-- **Exercise 7.11(b).** Gaussian concentration upgrades the GOE
expectation estimate to a subgaussian upper tail.

**Book Exercise 7.11(b).** -/
theorem exercise_7_11b :
    ∃ c : ℝ, 0 < c ∧ ∀ {n : ℕ}, 0 < n → ∀ t : ℝ, 0 ≤ t →
      (stdGaussian (EuclideanSpace ℝ (Fin n × Fin n))).real
        {g | 2 * Real.sqrt n + t ≤ HDP.matrixOpNorm (canonicalGOE g)} ≤
          2 * Real.exp (-c * t ^ 2) := by
  -- EXERCISE-SORRY (category A): non-load-bearing Exercise 7.11(b).
  sorry

/-- The canonical iid standard-Gaussian rectangular matrix.

**Lean implementation helper.** -/
def canonicalGaussianMatrix {m n : ℕ}
    (g : EuclideanSpace ℝ (Fin m × Fin n)) : Matrix (Fin m) (Fin n) ℝ :=
  fun i j => g (i, j)

/-- The smallest of the `n` source singular values of an `m × n` matrix.

**Lean implementation helper.** -/
def sourceSmallestSingularValue {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  HDP.matrixSingularValue A (n - 1)

/-- **Exercise 7.13(a).** Sharp expectation lower bound for the smallest
singular value; the suitable absolute dimension threshold is explicit as an
existential natural number.

**Book Exercise 7.13(a).** -/
theorem exercise_7_13a :
    ∃ C : ℕ, ∀ {m n : ℕ}, C ≤ n → n ≤ m → 0 < n →
      Real.sqrt m - Real.sqrt n ≤
        ∫ g : EuclideanSpace ℝ (Fin m × Fin n),
          sourceSmallestSingularValue (canonicalGaussianMatrix g)
            ∂stdGaussian (EuclideanSpace ℝ (Fin m × Fin n)) := by
  -- EXERCISE-SORRY (category A): non-load-bearing Exercise 7.13(a).
  sorry

/-- **Exercise 7.13(b).** Lower-tail estimate for the smallest singular
value, with absolute constants quantified outside the dimensions.

**Book Exercise 7.13(b).** -/
theorem exercise_7_13b :
    ∃ C : ℕ, ∃ c : ℝ, 0 < c ∧
      ∀ {m n : ℕ}, C ≤ n → n ≤ m → 0 < n →
      ∀ t : ℝ, 0 ≤ t →
        (stdGaussian (EuclideanSpace ℝ (Fin m × Fin n))).real
          {g | sourceSmallestSingularValue (canonicalGaussianMatrix g) ≤
            Real.sqrt m - Real.sqrt n - t} ≤
          2 * Real.exp (-c * t ^ 2) := by
  -- EXERCISE-SORRY (category A): non-load-bearing Exercise 7.13(b).
  sorry

end HDP.Chapter7.Exercise
