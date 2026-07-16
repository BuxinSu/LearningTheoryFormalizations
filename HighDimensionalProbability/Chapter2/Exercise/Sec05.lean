import HighDimensionalProbability.Chapter2_ConcentrationOfIndependentSums

/-!
# Book Chapter 2 exercises for Section 2.5

These proof exercises are non-load-bearing and are isolated as category A. Exercise
2.20 uses the corrected source probability `1 - 2⁻ⁿ`, not the impossible printed
`1 - 2ⁿ`.
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators ENNReal NNReal unitInterval

namespace HDP.Chapter2

/- EXERCISE-SORRY (category A): Exercise 2.18 is not used by the main line. -/
/-- With high probability, at least 99 percent of the degrees
of a sufficiently dense Erdős--Rényi graph are within ten percent of their mean.

**Book Exercise 2.18.** -/
theorem exercise_2_18 :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (p : I),
      C ≤ (n - 1 : ℕ) * (p : ℝ) →
      99 / 100 ≤ (HDP.erdosRenyi n p).real
        {G | 99 * n ≤ 100 *
          (Finset.univ.filter fun v : Fin n =>
            (9 / 10 : ℝ) * ((n - 1 : ℕ) * (p : ℝ)) ≤ HDP.degree v G ∧
              HDP.degree v G ≤
                (11 / 10 : ℝ) * ((n - 1 : ℕ) * (p : ℝ))).card} := by
  sorry

/-- The maximum degree of a graph on a nonempty finite vertex set.

**Lean implementation helper.** -/
noncomputable def maxDegree {n : ℕ} [Nonempty (Fin n)] (G : HDP.ERSample n) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun v => HDP.degree v G)

/- EXERCISE-SORRY (category A): Exercise 2.19 is not used by the main line. -/
/-- In the stated sparse regime, the maximum degree of an Erdős--Rényi graph
is, with probability at least `99/100`, of order `log n / log log n`.

**Book Exercise 2.19.** -/
theorem exercise_2_19 :
    ∃ c c₁ c₂ : ℝ, 0 < c ∧ 0 < c₁ ∧ 0 < c₂ ∧
      ∀ (n : ℕ) (p : I) (hn : 3 ≤ n),
        (n - 1 : ℕ) * (p : ℝ) ≤ c * (Real.log n) ^ (99 / 100 : ℝ) →
        letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
        99 / 100 ≤ (HDP.erdosRenyi n p).real
          {G | c₁ * Real.log n / Real.log (Real.log n) ≤ maxDegree G ∧
            maxDegree G ≤ c₂ * Real.log n / Real.log (Real.log n)} := by
  sorry

/-- Counts the present graph edges with one endpoint in each of two disjoint
vertex sets.

**Lean implementation helper.** -/
noncomputable def edgesBetween {n : ℕ} (S T : Finset (Fin n))
    (G : HDP.ERSample n) : ℕ :=
  (Finset.univ.filter fun e : HDP.EREdge n =>
    G e = true ∧ ∃ s ∈ S, ∃ t ∈ T, s ∈ e.1 ∧ t ∈ e.1).card

/- EXERCISE-SORRY (category A): Exercise 2.20 is not used by the main line. -/
/-- Corrected the source Exercise 2.20. Uniform expansion between sufficiently large
disjoint vertex sets, with probability at least `1 - 2⁻ⁿ`.

**Book Exercise 2.20.** -/
theorem exercise_2_20 :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (p : I), 0 < n → 0 < (p : ℝ) →
      1 - (2 : ℝ) ^ (-(n : ℝ)) ≤ (HDP.erdosRenyi n p).real
        {G | ∀ S T : Finset (Fin n), Disjoint S T →
          C * n / (p : ℝ) ≤ (S.card : ℝ) * T.card →
          (9 / 10 : ℝ) * (p : ℝ) ≤
              (edgesBetween S T G : ℝ) / ((S.card : ℝ) * T.card) ∧
            (edgesBetween S T G : ℝ) / ((S.card : ℝ) * T.card) ≤
              (11 / 10 : ℝ) * (p : ℝ)} := by
  sorry

/- EXERCISE-SORRY (category A): Exercise 2.21 is not used by the main line. -/
/-- If each independent Bernoulli trial succeeds with probability
`1/2 + ε`, then sufficiently many trials make a strict majority succeed with
probability at least `1 - δ`.

**Book Exercise 2.21.** -/
theorem exercise_2_21 {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {N : ℕ} {X : Fin N → Ω → ℝ} {q : I}
    (hX : ∀ i, HDP.IsBernoulli (X i) q μ) (hindep : iIndepFun X μ)
    {ε δ : ℝ} (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2)
    (hq : (q : ℝ) = 1 / 2 + ε) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hN : (1 / (2 * ε ^ 2)) * Real.log (1 / δ) ≤ N) :
    1 - δ ≤ μ.real {ω | (N : ℝ) / 2 < ∑ i, X i ω} := by
  sorry

end HDP.Chapter2
