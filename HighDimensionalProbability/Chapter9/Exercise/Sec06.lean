/-
Copyright (c) 2026 Buxin Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Buxin Su
-/

import HighDimensionalProbability.Chapter9.Main
import HighDimensionalProbability.Chapter9.Exercise.Sec01

/-!
# Book Chapter 9 exercises attached to Section 9.6

Exercises 9.34 and 9.37 are promoted to core: 9.34 is used in the proof of
the general deviation theorem, while 9.37 is the common general-norm JL result
specialized in the next section.  The two remaining proof requests are stated
here in exact expectation and tail forms.
-/

open Matrix MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped BigOperators ENNReal NNReal RealInnerProductSpace Topology
  Matrix.Norms.L2Operator

namespace HDP.Chapter9.Exercise

noncomputable section

/-- A sublinear functional is positive-homogeneous and subadditive and may take negative values. Positive homogeneity for nonnegative real scalars.

**Book Definition 9.6.1.** -/
def IsPositivelyHomogeneous {E : Type*} [SMul ℝ E]
    (f : E → ℝ) : Prop :=
  ∀ (c : ℝ), 0 ≤ c → ∀ x, f (c • x) = c * f x

/-- A sublinear functional is positive-homogeneous and subadditive and may take negative values. Subadditivity.

**Book Definition 9.6.1.** -/
def IsSubadditive {E : Type*} [Add E] (f : E → ℝ) : Prop :=
  ∀ x y, f (x + y) ≤ f x + f y

/-- Sublinear functional has Euclidean linear growth `f(x) <= b ‖x‖`. Uniform Euclidean growth bound used by Theorem 9.6.3.

**Book Equation (9.36).** -/
def HasEuclideanGrowth {E : Type*} [Norm E]
    (f : E → ℝ) (b : ℝ) : Prop :=
  ∀ z, |f z| ≤ b * ‖z‖

/-- Independent standard-Gaussian entries of a random matrix.

**Lean implementation helper.** -/
def IsStandardGaussianRandomMatrix {m n : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A : HDP.RandomMatrix (Fin m) (Fin n) Ω) : Prop :=
  (∀ i j, HasLaw (fun ω => A ω i j) (gaussianReal 0 1) μ) ∧
    iIndepFun (fun q : Fin m × Fin n => fun ω => A ω q.1 q.2) μ

/-- Supremal centered functional deviation on an arbitrary set.

**Lean implementation helper.** -/
def functionalSetDeviation {m n : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω)
    (A : Ω → Matrix (Fin m) (Fin n) ℝ)
    (f : Euc m → ℝ) (T : Set (Euc n)) (ω : Ω) : ℝ :=
  sSup {r : ℝ | ∃ x ∈ T,
    r = |f (matrixApply (A ω) x) -
      ∫ ξ, f (matrixApply (A ξ) x) ∂μ|}

/-- **Exercise 9.35 (anisotropic Gaussian general deviation).** A possibly
singular covariance is represented by a square-root factor `S`; the random
matrix is `G S`, so no whitening inverse is assumed.

**Book Exercise 9.35.** -/
theorem exercise_9_35 :
    ∃ C : ℝ, 0 < C ∧
      ∀ {m n : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}
        {μ : Measure Ω} [IsProbabilityMeasure μ]
        (G : HDP.RandomMatrix (Fin m) (Fin n) Ω)
        (S : Matrix (Fin n) (Fin n) ℝ)
        (f : Euc m → ℝ) (T : Set (Euc n)) (b : ℝ),
        0 < m → 0 < n → T.Nonempty → Bornology.IsBounded T →
        0 ≤ b → IsPositivelyHomogeneous f → IsSubadditive f →
        HasEuclideanGrowth f b → Continuous f →
        IsStandardGaussianRandomMatrix μ G →
        (∀ ω, BddAbove {r : ℝ | ∃ x ∈ T,
          r = |f (matrixApply (G ω * S) x) -
            ∫ ξ, f (matrixApply (G ξ * S) x) ∂μ|}) →
        Measurable (functionalSetDeviation μ (fun ω => G ω * S) f T) →
        Integrable (functionalSetDeviation μ (fun ω => G ω * S) f T) μ →
        (∫ ω, functionalSetDeviation μ (fun ξ => G ξ * S) f T ω ∂μ) ≤
          C * b * setGaussianComplexity (matrixImage S T) := by
  -- EXERCISE-SORRY: Category A, non-load-bearing Exercise 9.35.
  sorry

/-- **Exercise 9.36 (general matrix deviation, high probability).** The
source asks for a tail statement without printing one. This is the standard
`complexity + u · radius` form with Gaussian tail `2 exp (-u²)`.

**Book Exercise 9.36.** -/
theorem exercise_9_36 :
    ∃ C : ℝ, 0 < C ∧
      ∀ {m n : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}
        {μ : Measure Ω} [IsProbabilityMeasure μ]
        (G : HDP.RandomMatrix (Fin m) (Fin n) Ω)
        (f : Euc m → ℝ) (T : Set (Euc n)) (b u : ℝ),
        0 < m → 0 < n → T.Nonempty → Bornology.IsBounded T →
        0 ≤ b → 0 ≤ u →
        IsPositivelyHomogeneous f → IsSubadditive f →
        HasEuclideanGrowth f b → Continuous f →
        IsStandardGaussianRandomMatrix μ G →
        MeasurableSet {ω |
          functionalSetDeviation μ G f T ω ≤
            C * b * (setGaussianComplexity T + u * setRadius T)} →
        μ.real {ω |
          functionalSetDeviation μ G f T ω ≤
            C * b * (setGaussianComplexity T + u * setRadius T)} ≥
          1 - 2 * Real.exp (-u ^ 2) := by
  -- EXERCISE-SORRY: Category A, non-load-bearing Exercise 9.36.
  sorry

end

end HDP.Chapter9.Exercise
