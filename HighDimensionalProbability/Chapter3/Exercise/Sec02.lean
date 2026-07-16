import HighDimensionalProbability.Chapter3_RandomVectorsInHighDimensions

/-!
# Book Chapter 3 non-load-bearing exercises 3.4--3.13

Only category-A proof questions remain in this leaf. Exercises 3.5--3.7,
3.9--3.10, and 3.13 are promoted to `05_MomentGeometry.lean` because Chapter 3 or
later chapters use them.
-/

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators ENNReal NNReal RealInnerProductSpace

namespace HDP.Chapter3

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/- EXERCISE-SORRY (category A): Exercise 3.4 is not load-bearing. -/
/-- Projecting onto the span of the top `k` second-moment eigenvectors captures
the sum of the top `k` eigenvalues in expected squared norm and maximizes this
expectation among all orthonormal `k`-frames.

**Book Exercise 3.4.** -/
theorem exercise_3_4 {n k : ℕ} (hk : k ≤ n)
    {X : Ω → EuclideanSpace ℝ (Fin n)}
    {lam : Fin n → ℝ} {v : Fin n → EuclideanSpace ℝ (Fin n)}
    (hv : ∀ i j, inner ℝ (v i) (v j) = if i = j then 1 else 0)
    (hlam : Antitone lam)
    (hsecond : ∀ u : EuclideanSpace ℝ (Fin n),
      (∫ ω, inner ℝ (X ω) u ^ 2 ∂μ) =
        ∑ i, lam i * inner ℝ (v i) u ^ 2) :
    let vk : Fin k → EuclideanSpace ℝ (Fin n) :=
      fun i => v ⟨i, lt_of_lt_of_le i.isLt hk⟩
    (∫ ω, ‖finiteFrameProjection vk (X ω)‖ ^ 2 ∂μ) =
        ∑ i : Fin k, lam ⟨i, lt_of_lt_of_le i.isLt hk⟩ ∧
      ∀ w : Fin k → EuclideanSpace ℝ (Fin n),
        (∀ i j, inner ℝ (w i) (w j) = if i = j then 1 else 0) →
        (∫ ω, ‖finiteFrameProjection w (X ω)‖ ^ 2 ∂μ) ≤
          ∫ ω, ‖finiteFrameProjection vk (X ω)‖ ^ 2 ∂μ := by
  sorry

/- EXERCISE-SORRY (category A): Exercise 3.8(a) is not load-bearing; its
constructive sharpness subpart is recorded separately and skipped. -/
/-- The mean of an integrable isotropic random vector has Euclidean norm at
most `1`.

**Book Exercise 3.8(a).** -/
theorem exercise_3_8a [IsProbabilityMeasure μ] {n : ℕ}
    {X : Ω → EuclideanSpace ℝ (Fin n)} (hXint : Integrable X μ)
    (hX : HDP.IsIsotropic X μ) :
    ‖∫ ω, X ω ∂μ‖ ≤ 1 := by
  sorry

/- EXERCISE-SORRY (category A): Exercise 3.11(a) is not load-bearing; part
(b) is heuristic prose. -/
/-- A uniformly random permutation of a zero-sum unit vector has zero
coordinate means, diagonal covariance `1/n`, and off-diagonal covariance
`-1/(n(n-1))`.

**Book Exercise 3.11(a).** -/
theorem exercise_3_11 {n : ℕ} (hn : 2 ≤ n)
    (x : EuclideanSpace ℝ (Fin n))
    (hsum : ∑ i, x i = 0) (hsq : ∑ i, x i ^ 2 = 1) :
    letI : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤
    let ν := uniformOn (Set.univ : Set (Equiv.Perm (Fin n)))
    let X := permutedVector x
    (∀ i, ∫ σ, X σ i ∂ν = 0) ∧
      (∀ i, HDP.covarianceMatrix X ν i i = 1 / n) ∧
      (∀ i j, i ≠ j →
        HDP.covarianceMatrix X ν i j = -(1 / ((n : ℝ) * (n - 1)))) := by
  sorry

/- EXERCISE-SORRY (category A): Exercise 3.12 is not load-bearing. -/
/-- Two independent centered isotropic vectors in `ℝⁿ` have expected squared
distance `2n`.

**Book Exercise 3.12.** -/
theorem exercise_3_12 [IsProbabilityMeasure μ] {n : ℕ}
    {X Y : Ω → EuclideanSpace ℝ (Fin n)}
    (hXY : IndepFun X Y μ) (hX0 : ∫ ω, X ω ∂μ = 0)
    (hY0 : ∫ ω, Y ω ∂μ = 0) (hXiso : HDP.IsIsotropic X μ)
    (hYiso : HDP.IsIsotropic Y μ)
    (hmem : MemLp (fun ω => ‖X ω - Y ω‖) 2 μ) :
    ∫ ω, ‖X ω - Y ω‖ ^ 2 ∂μ = 2 * n := by
  sorry

end HDP.Chapter3
