import HighDimensionalProbability.Chapter6.Main

/-!
# Book Chapter 7 exercises attached to Section 7.5

The load-bearing Gaussian-width exercises 7.15, 7.17, 7.18, 7.20 and 7.21,
as well as the optimality witnesses in Exercise 7.16, belong to core.  This
leaf contains only Exercises 7.19, 7.22 and 7.23.
-/

open Matrix MeasureTheory ProbabilityTheory Set WithLp
open scoped BigOperators ENNReal NNReal Matrix.Norms.L2Operator
  RealInnerProductSpace

noncomputable section

namespace HDP.Chapter7.Exercise

/-- Gaussian width of the operator-norm unit ball, written directly in the
matrix/Frobenius ambient Euclidean space.

**Lean implementation helper.** -/
def operatorBallGaussianWidth (n : ℕ) : ℝ :=
  ∫ g : EuclideanSpace ℝ (Fin n × Fin n),
    sSup {r : ℝ | ∃ B : Matrix (Fin n) (Fin n) ℝ,
      HDP.matrixOpNorm B ≤ 1 ∧
        r = ∑ i, ∑ j, g (i, j) * B i j}
      ∂stdGaussian (EuclideanSpace ℝ (Fin n × Fin n))

/-- **Exercise 7.19.** The Gaussian width of the operator-norm unit ball is
of order `n^(3/2)`.

**Book Exercise 7.19.** -/
theorem exercise_7_19 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ {n : ℕ}, 0 < n →
      c * Real.rpow n (3 / 2 : ℝ) ≤ operatorBallGaussianWidth n ∧
        operatorBallGaussianWidth n ≤ C * Real.rpow n (3 / 2 : ℝ) := by
  -- EXERCISE-SORRY (category A): non-load-bearing Exercise 7.19.
  sorry

/-- Squared diameter of a nonempty finite Euclidean set.

**Lean implementation helper.** -/
def finiteDiameterSq {n : ℕ} (T : Finset (EuclideanSpace ℝ (Fin n)))
    (hT : T.Nonempty) : ℝ :=
  (T.product T).sup' (hT.product hT) fun xy => ‖xy.1 - xy.2‖ ^ 2

/-- Squared `h(T-T)` for a nonempty finite Euclidean set.

**Lean implementation helper.** -/
def finiteDifferenceGaussianHSq {n : ℕ}
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty) : ℝ :=
  ∫ g : EuclideanSpace ℝ (Fin n),
    (T.product T).sup' (hT.product hT) (fun xy =>
      |inner ℝ g (xy.1 - xy.2)| ^ 2)
      ∂stdGaussian (EuclideanSpace ℝ (Fin n))

/-- Effective dimension for finite sets, using the exact `h`-definition from
the source. A positive-diameter hypothesis is imposed by the theorem below.

**Lean implementation helper.** -/
def finiteEffectiveDimension {n : ℕ}
    (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty) : ℝ :=
  finiteDifferenceGaussianHSq T hT / finiteDiameterSq T hT

/-- **Exercise 7.22, corrected nondegenerate form.** Positive diameter avoids
the source's undefined `0/0` effective dimension for singleton sets.

**Book Exercise 7.22.** -/
theorem exercise_7_22 :
    ∃ C : ℝ, 0 < C ∧ ∀ {n : ℕ}
      (T : Finset (EuclideanSpace ℝ (Fin n))) (hT : T.Nonempty),
      0 < finiteDiameterSq T hT →
        finiteEffectiveDimension T hT ≤ C * Real.log T.card := by
  -- EXERCISE-SORRY (category A): non-load-bearing Exercise 7.22.
  sorry

/-- Gaussian width of the ellipsoid `A(B₂)`, using its support function
`g ↦ ‖Aᵀg‖₂`.

**Lean implementation helper.** -/
def ellipsoidGaussianWidth {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ∫ g : EuclideanSpace ℝ (Fin m),
    ‖WithLp.toLp 2 (Aᵀ *ᵥ (WithLp.ofLp g : Fin m → ℝ))‖
      ∂stdGaussian (EuclideanSpace ℝ (Fin m))

/-- **Exercise 7.23(a).** Gaussian width of an ellipsoid is comparable to
the Frobenius norm of its defining map.

**Book Exercise 7.23(a).** -/
theorem exercise_7_23a :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ),
        c * HDP.matrixFrobeniusNorm A ≤ ellipsoidGaussianWidth A ∧
          ellipsoidGaussianWidth A ≤ C * HDP.matrixFrobeniusNorm A := by
  -- EXERCISE-SORRY (category A): non-load-bearing Exercise 7.23(a).
  sorry

/-- Exact effective dimension of a nondegenerate ellipsoid.

**Lean implementation helper.** -/
def ellipsoidEffectiveDimension {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  HDP.matrixFrobeniusNorm A ^ 2 / HDP.matrixOpNorm A ^ 2

/-- **Exercise 7.23(b), corrected nonzero form.** The effective dimension of
`A(B₂)` equals both the effective rank of `AᵀA` and the stable rank of `A`.
The nonzero hypothesis excludes the source's `0/0` case.

**Book Exercise 7.23(b).** -/
theorem exercise_7_23b {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (_hA : A ≠ 0) :
    ellipsoidEffectiveDimension A = HDP.effectiveRank (HDP.gramMatrix A) ∧
      ellipsoidEffectiveDimension A = HDP.stableRank A := by
  -- EXERCISE-SORRY (category A): non-load-bearing Exercise 7.23(b).
  sorry

end HDP.Chapter7.Exercise
