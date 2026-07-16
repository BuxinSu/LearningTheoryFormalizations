/-
Copyright (c) 2026 Buxin Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Buxin Su
-/

import HighDimensionalProbability.Chapter9.Main
import HighDimensionalProbability.Chapter9.Exercise.Sec01
import HighDimensionalProbability.Chapter9.Exercise.Sec04
import HighDimensionalProbability.Chapter9.Exercise.Sec06

/-!
# Book Chapter 9 exercises attached to Section 9.7

Exercises 9.37 and 9.40 are core inputs and are not redeclared here;
Exercise 9.43 is likewise promoted because it is the source's true-projection
endpoint.  This leaf contains the four remaining proof questions.  The two JL
specializations use distinct constants for normalization, dimension growth,
and probability, avoiding the source's overloaded letter `C`.
-/

open Matrix MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped BigOperators ENNReal NNReal RealInnerProductSpace Topology
  Matrix.Norms.L2Operator Pointwise

namespace HDP.Chapter9.Exercise

noncomputable section

/-- Maximum coordinate magnitude, with the safe supremum convention.

**Lean implementation helper.** -/
def ellInfinityNorm {m : ℕ} (x : Euc m) : ℝ :=
  sSup (Set.range fun i : Fin m => |x i|)

/-- Relative `ℓ¹` embedding of a finite Euclidean point cloud.

**Lean implementation helper.** -/
def IsL1EpsilonIsometryOn {m n : ℕ}
    (Q : Matrix (Fin m) (Fin n) ℝ) (X : Finset (Euc n))
    (ε : ℝ) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X,
    (1 - ε) * ‖x - y‖ ≤ ellOneNorm (matrixApply Q x - matrixApply Q y) ∧
      ellOneNorm (matrixApply Q x - matrixApply Q y) ≤
        (1 + ε) * ‖x - y‖

/-- Relative `ℓ∞` embedding of a finite Euclidean point cloud.

**Lean implementation helper.** -/
def IsLInfinityEpsilonIsometryOn {m n : ℕ}
    (Q : Matrix (Fin m) (Fin n) ℝ) (X : Finset (Euc n))
    (ε : ℝ) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X,
    (1 - ε) * ‖x - y‖ ≤
        ellInfinityNorm (matrixApply Q x - matrixApply Q y) ∧
      ellInfinityNorm (matrixApply Q x - matrixApply Q y) ≤
        (1 + ε) * ‖x - y‖

/-- Closed convex hull, used where the source's ordinary convex hull need not
be closed for an arbitrary bounded set.

**Lean implementation helper.** -/
def closedConvexHullSet {E : Type*} [TopologicalSpace E]
    [AddCommMonoid E] [Module ℝ E] (T : Set E) : Set E :=
  closure (convexHull ℝ T)

/-- Effective dimension `w(T)^2 / rad(T)^2`, used only under a positive-radius
hypothesis.

**Lean implementation helper.** -/
def setEffectiveDimension {n : ℕ} (T : Set (Euc n)) : ℝ :=
  (setGaussianWidth T / setRadius T) ^ 2

/-- **Exercise 9.38 (Johnson--Lindenstrauss into `ℓ¹`).** The exact
normalization is `sqrt (pi/2) / m`, and both the dimension condition and tail
show their dependence on `ε`.

**Book Exercise 9.38.** -/
theorem exercise_9_38 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {m n : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}
        {μ : Measure Ω} [IsProbabilityMeasure μ]
        (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
        (X : Finset (Euc n)) (ε : ℝ),
        0 < m → 0 < n → 2 ≤ X.card → 0 < ε → ε < 1 →
        C * ε⁻¹ ^ 2 * Real.log X.card ≤ m →
        IsStandardGaussianRandomMatrix μ A →
        MeasurableSet {ω | IsL1EpsilonIsometryOn
          ((Real.sqrt (Real.pi / 2) / m) • A ω) X ε} →
        μ.real {ω | IsL1EpsilonIsometryOn
          ((Real.sqrt (Real.pi / 2) / m) • A ω) X ε} ≥
          1 - 2 * Real.exp (-c * ε ^ 2 * m) := by
  -- EXERCISE-SORRY: Category A, non-load-bearing Exercise 9.38.
  sorry

/-- **Exercise 9.39 (Johnson--Lindenstrauss into `ℓ∞`).** The assumptions
`m>1` and exponent at least one justify the source's observation that this is
an embedding rather than dimension reduction.

**Book Exercise 9.39.** -/
theorem exercise_9_39 :
    ∃ c C D : ℝ, 0 < c ∧ 1 ≤ C ∧ 0 < D ∧
      ∀ {m n : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}
        {μ : Measure Ω} [IsProbabilityMeasure μ]
        (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
        (X : Finset (Euc n)) (ε : ℝ),
        2 ≤ m → 0 < n → 2 ≤ X.card → 0 < ε → ε < 1 →
        Real.rpow X.card (C * ε⁻¹ ^ 2) ≤ m →
        IsStandardGaussianRandomMatrix μ A →
        MeasurableSet {ω | IsLInfinityEpsilonIsometryOn
          ((D / Real.sqrt (Real.log m)) • A ω) X ε} →
        μ.real {ω | IsLInfinityEpsilonIsometryOn
          ((D / Real.sqrt (Real.log m)) • A ω) X ε} ≥
          1 - 2 * Real.exp (-c * ε ^ 2 * Real.log m) := by
  -- EXERCISE-SORRY: Category A, non-load-bearing Exercise 9.39.
  sorry

/-- **Exercise 9.41 (high-probability Dvoretzky--Milman).** As in Theorem
9.7.2, the set is an arbitrary bounded set: no symmetry assumption is needed.
The effective-dimension hypothesis makes the additive deviation small enough
to give the displayed relative radii. The source's unspecified “high
probability” is made quantitative here.

**Book Exercise 9.41.** -/
theorem exercise_9_41 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {m n : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}
        {μ : Measure Ω} [IsProbabilityMeasure μ]
        (A : HDP.RandomMatrix (Fin m) (Fin n) Ω)
        (T : Set (Euc n)) (ε : ℝ),
        0 < m → 0 < n → T.Nonempty → Bornology.IsBounded T →
        0 < setRadius T → 0 < ε → ε < 1 →
        m ≤ c * ε ^ 2 * setEffectiveDimension T →
        IsStandardGaussianRandomMatrix μ A →
        MeasurableSet {ω |
          Metric.closedBall (0 : Euc m)
              ((1 - ε) * setGaussianWidth T) ⊆
            closedConvexHullSet (matrixImage (A ω) T) ∧
          closedConvexHullSet (matrixImage (A ω) T) ⊆
            Metric.closedBall (0 : Euc m)
              ((1 + ε) * setGaussianWidth T)} →
        μ.real {ω |
          Metric.closedBall (0 : Euc m)
              ((1 - ε) * setGaussianWidth T) ⊆
            closedConvexHullSet (matrixImage (A ω) T) ∧
          closedConvexHullSet (matrixImage (A ω) T) ⊆
            Metric.closedBall (0 : Euc m)
              ((1 + ε) * setGaussianWidth T)} ≥
          1 - 2 * Real.exp
            (-C * ε ^ 2 * setEffectiveDimension T) := by
  -- EXERCISE-SORRY: Category A, non-load-bearing Exercise 9.41.
  sorry

/-- **Exercise 9.42 (a Gaussian cloud is nearly round).** “Approximately”
is represented by two absolute radii and “high probability” by an exponential
tail. No artificial symmetrization is introduced: the hull is that of the
`n` points printed in the source.

**Book Exercise 9.42.** -/
theorem exercise_9_42 :
    ∃ c C D : ℝ, 0 < c ∧ 1 < C ∧ 0 < D ∧
      ∀ {m n : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}
        {μ : Measure Ω} [IsProbabilityMeasure μ]
        (g : Fin n → Ω → Euc m),
        0 < m → 2 ≤ n → m ≤ c * Real.log n →
        (∀ i, HasLaw (g i) (stdGaussian (Euc m)) μ) →
        iIndepFun g μ →
        MeasurableSet {ω |
          Metric.closedBall (0 : Euc m) (c * Real.sqrt (Real.log n)) ⊆
            closedConvexHullSet (Set.range fun i => g i ω) ∧
          closedConvexHullSet (Set.range fun i => g i ω) ⊆
            Metric.closedBall (0 : Euc m)
              (C * Real.sqrt (Real.log n))} →
        μ.real {ω |
          Metric.closedBall (0 : Euc m) (c * Real.sqrt (Real.log n)) ⊆
            closedConvexHullSet (Set.range fun i => g i ω) ∧
          closedConvexHullSet (Set.range fun i => g i ω) ⊆
            Metric.closedBall (0 : Euc m)
              (C * Real.sqrt (Real.log n))} ≥
          1 - 2 * Real.exp (-D * m) := by
  -- EXERCISE-SORRY: Category A, non-load-bearing Exercise 9.42.
  sorry

end

end HDP.Chapter9.Exercise
