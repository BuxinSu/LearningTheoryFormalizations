import HighDimensionalProbability.Chapter1_AnalysisAndProbabilityRefresher
import Mathlib.Probability.Distributions.Poisson.Basic

/-!
# Book Chapter 1 Exercise folder: Exercises 1.7, 1.8, and 1.13

Only the non-load-bearing category-A exercises remain here.  Exercises 1.9,
1.10, 1.12, and body formula (1.20)/Exercise 1.11 are declared only in core
modules because Chapter 2 or later material consumes them.
-/

open MeasureTheory ProbabilityTheory Real Filter Set
open scoped ENNReal NNReal BigOperators Topology unitInterval

namespace HDP.Chapter1

/- EXERCISE-SORRY (category A): Exercise 1.7 is not used by the main line. -/
/-- The Poisson mixture of the `G(n,p)` laws has no isolated
vertex with probability at least `1 - 1/λ` under the source threshold.

`EXERCISE-SORRY`: exact mixture statement, deliberately deferred as non-load-bearing.

**Book Exercise 1.7.** -/
theorem exercise_1_7 {lam : ℝ≥0} (hlam : 0 < lam) (p : I)
    (hp : 2 * Real.log (lam : ℝ) / (lam : ℝ) ≤ (p : ℝ)) :
    1 - 1 / (lam : ℝ) ≤
      ∑' n : ℕ, (poissonMeasure lam).real {n} *
        (HDP.erdosRenyi n p).real (noIsolatedVertices n) := by
  sorry

/-- A finite vertex set is independent when none of its internal edges is present.

**Lean implementation helper.** -/
def IsIndependentVertexSet {n : ℕ} (S : Finset (Fin n)) (G : HDP.ERSample n) : Prop :=
  ∀ e : HDP.EREdge n, (∀ v ∈ e.1, v ∈ S) → G e = false

/- EXERCISE-SORRY (category A): Exercise 1.8 is not used by the main line. -/
/-- For `n ≥ 7`, a `G(n,1/2)` graph has no independent
set larger than `2 log₂ n` with probability at least `1 - 1/n`.

`EXERCISE-SORRY`: exact finite-graph statement, deliberately deferred as
non-load-bearing.

**Book Exercise 1.8.** -/
theorem exercise_1_8 {n : ℕ} (hn : 7 ≤ n) :
    1 - 1 / (n : ℝ) ≤
      (HDP.erdosRenyi n ⟨1 / 2, by constructor <;> norm_num⟩).real
        {G | ∀ S : Finset (Fin n),
          2 * (Real.log n / Real.log 2) < (S.card : ℝ) →
            ¬ IsIndependentVertexSet S G} := by
  sorry

/- EXERCISE-SORRY (category A): Exercise 1.13 is not used by the main line. -/
/-- For a nonempty finite family of nonnegative integrable random variables,
the expected maximum lies between the largest expectation and `n` times that
largest expectation.

`EXERCISE-SORRY`: the inequality part is faithfully stated and deliberately deferred.
The witness-only optimality constructions in parts (b) and (c) are recorded below.

**Book Exercise 1.13(a).** -/
theorem exercise_1_13a {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ} (hn : 0 < n) {X : Fin n → Ω → ℝ}
    (hX0 : ∀ i, 0 ≤ᵐ[μ] X i) (hXi : ∀ i, Integrable (X i) μ)
    (hmax : Integrable (fun ω => Finset.univ.sup' (by
      letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
      exact Finset.univ_nonempty) fun i => X i ω) μ) :
    letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    Finset.univ.sup' Finset.univ_nonempty (fun i => ∫ ω, X i ω ∂μ)
        ≤ ∫ ω, Finset.univ.sup' Finset.univ_nonempty (fun i => X i ω) ∂μ ∧
      (∫ ω, Finset.univ.sup' Finset.univ_nonempty (fun i => X i ω) ∂μ)
        ≤ n * Finset.univ.sup' Finset.univ_nonempty
          (fun i => ∫ ω, X i ω ∂μ) := by
  sorry

/- Exercise 1.13(b,c) asks for explicit extremizing probability spaces and random
variables. These constructive witness-only subparts remain intentionally skipped. -/

end HDP.Chapter1
