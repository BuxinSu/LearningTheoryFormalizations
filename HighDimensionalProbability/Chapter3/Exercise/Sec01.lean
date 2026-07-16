import HighDimensionalProbability.Chapter3_RandomVectorsInHighDimensions

/-!
# Book Chapter 3 non-load-bearing exercises 3.1 and 3.3

Exercise 3.2 is promoted to the thematic core file `02_ThinShell.lean` because
Chapter 7 uses it. The two source-facing declarations below are leaf-only and
no core module imports them.
-/

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators ENNReal NNReal RealInnerProductSpace

namespace HDP.Chapter3

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The Euclidean norm of an independent, variance-one subgaussian vector has
variance at most `2 (normConcentrationConstant · K²)²`.

**Book Theorem 3.1.1.** -/
theorem exercise_3_1 [IsProbabilityMeasure μ] {n : ℕ} (hn : 0 < n)
    {X : Fin n → Ω → ℝ} (hXm : ∀ i, AEMeasurable (X i) μ)
    (hX : ∀ i, HDP.SubGaussian (X i) μ)
    (hsecond : ∀ i, ∫ ω, X i ω ^ 2 ∂μ = 1)
    (hindep : iIndepFun X μ) {K : ℝ} (hK : 0 < K)
    (hKb : ∀ i, HDP.psi2Norm (X i) μ ≤ K) :
    Var[euclideanRadius X; μ] ≤
      2 * (normConcentrationConstant * K ^ 2) ^ 2 := by
  exact thinShellVariance_subGaussian hn hXm hX hsecond hindep hK hKb

/-- Under the stated lower fourth-moment fluctuation, upper sixth-moment, and
dimension conditions, an independent variance-one vector has a quantitative
reverse thin-shell variance bound and a corresponding deficit in its expected
Euclidean norm.

**Book Exercise 3.3.** -/
theorem exercise_3_3 [IsProbabilityMeasure μ] {n : ℕ} (hn : 0 < n)
    {X : Fin n → Ω → ℝ} (hXm : ∀ i, Measurable (X i))
    (hindep : iIndepFun X μ)
    (hsecond : ∀ i, ∫ ω, X i ω ^ 2 ∂μ = 1)
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hvar : ∀ i, α < Var[fun ω => X i ω ^ 2; μ])
    (h6int : ∀ i, Integrable (fun ω => X i ω ^ 6) μ)
    (h6 : ∀ i, ∫ ω, X i ω ^ 6 ∂μ ≤ β)
    (hlarge : ReverseThinShellLargeEnough n α β) :
    (1 / 262144 : ℝ) * α ≤ Var[euclideanRadius X; μ] ∧
      (∫ ω, euclideanRadius X ω ∂μ) ≤
        Real.sqrt n - (1 / 262144 : ℝ) * α / Real.sqrt n := by
  exact reverseThinShellVariance hn hXm hindep hsecond hα hβ hvar h6int h6 hlarge

end HDP.Chapter3
