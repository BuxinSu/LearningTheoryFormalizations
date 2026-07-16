import HighDimensionalProbability.Chapter2_ConcentrationOfIndependentSums

/-!
# Book Chapter 2 exercises for Section 2.3
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators ENNReal NNReal unitInterval

namespace HDP.Chapter2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/- Exercise 2.11 is the core left-tail Chernoff endpoint `chernoff_lower`, used
in Corollary 2.3.4. It is intentionally absent from this exercise leaf. -/

/- EXERCISE-SORRY (category A): Exercise 2.12 is not used by the main line. -/
/-- A reverse Chernoff bound lower-bounds the point probability that a
`Binom(N, mean/N)` variable equals an integer `t` between its mean and `N`.

**Book Exercise 2.12.** -/
theorem exercise_2_12 [IsProbabilityMeasure μ] {N t : ℕ} (hN : 0 < N)
    {mean : ℝ} (hmean0 : 0 ≤ mean) (hmeant : mean ≤ t) (htN : t ≤ N)
    {q : I} (hq : (q : ℝ) = mean / N) {X : Fin N → Ω → ℝ}
    (hX : ∀ i, HDP.IsBernoulli (X i) q μ) (hindep : iIndepFun X μ) :
    Real.exp (-mean) * (mean / t) ^ (t : ℝ) ≤
      μ.real {ω | ∑ i, X i ω = (t : ℝ)} := by
  sorry

/- EXERCISE-SORRY (category A): Exercise 2.13 is not used by the main line. -/
/-- Above its mean `r`, a Poisson variable has upper tail at most
`exp(-r) · (e r / t)ᵗ`.

**Book Exercise 2.13(a).** -/
theorem exercise_2_13a {Z : Ω → ℕ} {r : ℝ≥0}
    (hZ : HDP.Chapter1.IsPoissonRV Z r μ) {t : ℝ}
    (ht : (r : ℝ) ≤ t) :
    μ.real {ω | t ≤ (Z ω : ℝ)} ≤
      Real.exp (-(r : ℝ)) * (Real.exp 1 * (r : ℝ) / t) ^ t := by
  sorry

/- EXERCISE-SORRY (category A): Exercise 2.13 is not used by the main line. -/
/-- Below its mean `r`, a Poisson variable has lower tail at most
`exp(-r) · (e r / t)ᵗ`.

**Book Exercise 2.13(b).** -/
theorem exercise_2_13b {Z : Ω → ℕ} {r : ℝ≥0}
    (hZ : HDP.Chapter1.IsPoissonRV Z r μ) {t : ℝ} (ht0 : 0 < t)
    (ht : t ≤ (r : ℝ)) :
    μ.real {ω | (Z ω : ℝ) ≤ t} ≤
      Real.exp (-(r : ℝ)) * (Real.exp 1 * (r : ℝ) / t) ^ t := by
  sorry

/- EXERCISE-SORRY (category A): Exercise 2.13 is not used by the main line. -/
/-- A Poisson variable of mean `r` deviates from `r` by at least `δr`, for
`0 ≤ δ ≤ 1`, with probability at most `2 exp(-δ²r/3)`.

**Book Exercise 2.13(c).** -/
theorem exercise_2_13c {Z : Ω → ℕ} {r : ℝ≥0}
    (hZ : HDP.Chapter1.IsPoissonRV Z r μ) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    μ.real {ω | δ * (r : ℝ) ≤ |(Z ω : ℝ) - (r : ℝ)|} ≤
      2 * Real.exp (-δ ^ 2 * (r : ℝ) / 3) := by
  sorry

/- EXERCISE-SORRY (category A): Exercise 2.13 is not used by the main line. -/
/-- The probability that a Poisson variable of mean `r` equals a positive
integer `t` is at least `exp(-r) · (r/t)ᵗ`.

**Book Exercise 2.13(d).** -/
theorem exercise_2_13d {Z : Ω → ℕ} {r : ℝ≥0}
    (hZ : HDP.Chapter1.IsPoissonRV Z r μ) {t : ℕ} (ht : 0 < t) :
    Real.exp (-(r : ℝ)) * ((r : ℝ) / t) ^ (t : ℝ) ≤
      μ.real {ω | Z ω = t} := by
  sorry

/- EXERCISE-SORRY (category A): Exercise 2.14 is not used by the main line. -/
/-- A sum of independent Bernoulli variables deviates from its mean by at
least `δ` times that mean with probability at most
`2 exp(-δ² mean / (2 + δ))`.

**Book Exercise 2.14.** -/
theorem exercise_2_14 [IsProbabilityMeasure μ] {N : ℕ}
    {X : Fin N → Ω → ℝ} {p : Fin N → I}
    (hX : ∀ i, HDP.IsBernoulli (X i) (p i) μ)
    (hindep : iIndepFun X μ) {δ : ℝ} (hδ : 0 ≤ δ) :
    μ.real {ω | δ * ∑ i, (p i : ℝ) ≤
        |∑ i, X i ω - ∑ i, (p i : ℝ)|} ≤
      2 * Real.exp (-(δ ^ 2 * ∑ i, (p i : ℝ)) / (2 + δ)) := by
  sorry

/- EXERCISE-SORRY (category A): Exercise 2.15 is not used by the main line. -/
/-- All three Chernoff bounds remain valid for independent
`[0,1]`-valued random variables with the prescribed means.

**Book Exercise 2.15.** -/
theorem exercise_2_15 [IsProbabilityMeasure μ] {N : ℕ}
    {X : Fin N → Ω → ℝ} {p : Fin N → I}
    (hXm : ∀ i, AEMeasurable (X i) μ)
    (hXint : ∀ i, Integrable (X i) μ)
    (hX01 : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = (p i : ℝ))
    (hindep : iIndepFun X μ) :
    (∀ t : ℝ, 0 < ∑ i, (p i : ℝ) → ∑ i, (p i : ℝ) ≤ t →
      μ.real {ω | t ≤ ∑ i, X i ω} ≤
        Real.exp (-∑ i, (p i : ℝ)) *
          (Real.exp 1 * (∑ i, (p i : ℝ)) / t) ^ t) ∧
    (∀ t : ℝ, 0 < t → t ≤ ∑ i, (p i : ℝ) →
      μ.real {ω | ∑ i, X i ω ≤ t} ≤
        Real.exp (-∑ i, (p i : ℝ)) *
          (Real.exp 1 * (∑ i, (p i : ℝ)) / t) ^ t) ∧
    (∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
      μ.real {ω | δ * ∑ i, (p i : ℝ) ≤
          |∑ i, X i ω - ∑ i, (p i : ℝ)|} ≤
        2 * Real.exp (-δ ^ 2 * (∑ i, (p i : ℝ)) / 3)) := by
  sorry

end HDP.Chapter2
