import HighDimensionalProbability.Chapter2_ConcentrationOfIndependentSums
import HighDimensionalProbability.Chapter1_AnalysisAndProbabilityRefresher

/-!
# Book Chapter 2 exercises for Section 2.9

Exercise 2.45 is fully proved here because no main-line or later result uses it.
Exercise 2.47 is promoted to core because it proves Theorem 2.9.5. The other
proof questions are isolated category-A leaves.
-/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped BigOperators ENNReal NNReal Topology

namespace HDP.Chapter2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- A centered sum of independent subexponential variables satisfies a
Bernstein tail bound at the explicit threshold
`8 (√(∑ ‖Xᵢ‖ψ₁²) √u + K u)`.

**Book Exercise 2.45.** -/
theorem exercise_2_45 [IsProbabilityMeasure μ] {N : ℕ}
    {X : Fin N → Ω → ℝ} (hXm : ∀ i, AEMeasurable (X i) μ)
    (hX : ∀ i, HDP.SubExponential (X i) μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hindep : iIndepFun X μ) {K : ℝ} (hK : 0 < K)
    (hKb : ∀ i, HDP.psi1Norm (X i) μ ≤ K) {u : ℝ} (hu : 0 ≤ u) :
    μ {ω | 8 * (Real.sqrt (∑ i, (HDP.psi1Norm (X i) μ) ^ 2) * Real.sqrt u + K * u)
        ≤ |∑ i, X i ω|} ≤ ENNReal.ofReal (2 * Real.exp (-u)) := by
  classical
  let S : ℝ := ∑ i, (HDP.psi1Norm (X i) μ) ^ 2
  let t : ℝ := 8 * (Real.sqrt S * Real.sqrt u + K * u)
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  have ht0 : 0 ≤ t := by positivity
  have hbase := HDP.bernstein_inequality hXm hX hmean hindep hK hKb ht0
  rcases eq_or_lt_of_le hS0 with hSzero | hSpos
  · rcases eq_or_lt_of_le hu with rfl | hupos
    · simp
    · have hXnorm0 : ∀ i, HDP.psi1Norm (X i) μ = 0 := by
        intro i
        have hi : (HDP.psi1Norm (X i) μ) ^ 2 ≤ S := by
          dsimp only [S]
          exact Finset.single_le_sum (fun j _ => sq_nonneg (HDP.psi1Norm (X j) μ))
            (Finset.mem_univ i)
        rw [← hSzero] at hi
        nlinarith [sq_nonneg (HDP.psi1Norm (X i) μ)]
      have hXzero : ∀ i, X i =ᵐ[μ] 0 := fun i =>
        HDP.ae_eq_zero_of_psi1Norm_eq_zero (hXm i) (hX i) (hXnorm0 i)
      have hsumzero : (fun ω => ∑ i, X i ω) =ᵐ[μ] 0 := by
        filter_upwards [ae_all_iff.mpr hXzero] with ω hω
        simp [hω]
      have htpos : 0 < t := by
        dsimp only [t]
        rw [show Real.sqrt S = 0 by simp [← hSzero]]
        nlinarith
      have hnull : μ {ω | t ≤ |∑ i, X i ω|} = 0 := by
        have hsub : {ω | t ≤ |∑ i, X i ω|} ⊆ {ω | (∑ i, X i ω) ≠ 0} := by
          intro ω hω hz
          simp [hz] at hω
          linarith
        exact measure_mono_null hsub (MeasureTheory.ae_iff.mp hsumzero)
      rw [show {ω | 8 * (Real.sqrt (∑ i, (HDP.psi1Norm (X i) μ) ^ 2) * Real.sqrt u
          + K * u) ≤ |∑ i, X i ω|} = {ω | t ≤ |∑ i, X i ω|} by rfl, hnull]
      positivity
  · have hsqrtS : (Real.sqrt S) ^ 2 = S := Real.sq_sqrt hS0
    have hsqrtu : (Real.sqrt u) ^ 2 = u := Real.sq_sqrt hu
    have hfirst : 8 * u ≤ t ^ 2 / S := by
      rw [le_div_iff₀ hSpos]
      have hpart0 : 0 ≤ Real.sqrt S * Real.sqrt u := by positivity
      have htpart : 8 * (Real.sqrt S * Real.sqrt u) ≤ t := by
        dsimp only [t]
        nlinarith
      have hsquares : (8 * (Real.sqrt S * Real.sqrt u)) ^ 2 ≤ t ^ 2 :=
        (sq_le_sq₀ (by positivity : 0 ≤ 8 * (Real.sqrt S * Real.sqrt u)) ht0).mpr htpart
      nlinarith
    have hsecond : 8 * u ≤ t / K := by
      rw [le_div_iff₀ hK]
      dsimp only [t]
      have hpart0 : 0 ≤ Real.sqrt S * Real.sqrt u := by positivity
      nlinarith
    have hmin : 8 * u ≤ min (t ^ 2 / S) (t / K) := le_min hfirst hsecond
    calc
      μ {ω | 8 * (Real.sqrt (∑ i, (HDP.psi1Norm (X i) μ) ^ 2) * Real.sqrt u + K * u)
          ≤ |∑ i, X i ω|}
          ≤ ENNReal.ofReal (2 * Real.exp (-(1 / 8) * min (t ^ 2 / S) (t / K))) := by
            simpa [S, t] using hbase
      _ ≤ ENNReal.ofReal (2 * Real.exp (-u)) := by
          apply ENNReal.ofReal_le_ofReal
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply Real.exp_le_exp.mpr
          nlinarith [hmin]

/- EXERCISE-SORRY (category A): Exercise 2.46 is not load-bearing. -/
/-- The `Lᵖ` norm of a weighted sum of independent centered subexponential
variables is bounded by a universal constant times
`K (√p ‖a‖₂ + p ‖a‖∞)`.

**Book Exercise 2.46.** -/
theorem exercise_2_46 :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
        [IsProbabilityMeasure μ] {N : ℕ} [Nonempty (Fin N)]
        {X : Fin N → Ω → ℝ},
        (∀ i, AEMeasurable (X i) μ) →
        (∀ i, HDP.SubExponential (X i) μ) →
        (∀ i, ∫ ω, X i ω ∂μ = 0) → iIndepFun X μ →
        ∀ {K : ℝ}, 0 < K → (∀ i, HDP.psi1Norm (X i) μ ≤ K) →
        ∀ (a : Fin N → ℝ) {p : ℝ}, 2 ≤ p →
          eLpNorm (fun ω => ∑ i, a i * X i ω) (ENNReal.ofReal p) μ ≤
            ENNReal.ofReal (C * K *
              (Real.sqrt p * HDP.Chapter1.lpNorm 2 a +
                p * HDP.Chapter1.linftyNorm a)) := by
  sorry

/- Exercise 2.47 is fully proved in `BoundedBernstein.lean`; importing this
leaf exposes the canonical declarations `hint_2_47_numeric`,
`exercise_2_47a`, and `exercise_2_47b` without duplicate aliases. -/

/-- Bennett's rate function `h(u) = (1+u) log(1+u) - u`.

**Book Exercise 2.48.** -/
noncomputable def bennettH (u : ℝ) : ℝ :=
  (1 + u) * Real.log (1 + u) - u

/- EXERCISE-SORRY (category A): Exercise 2.48(a) is not load-bearing. -/
/-- The MGF of a centered random variable bounded by `K` is controlled by its
second moment and the Bennett exponential remainder
`exp(λK) - 1 - λK`.

**Book Exercise 2.48(a).** -/
theorem exercise_2_48a [IsProbabilityMeasure μ] {X : Ω → ℝ}
    {K lam : ℝ} (hK : 0 < K) (hlam : 0 < lam)
    (hXm : AEMeasurable X μ) (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ K)
    (hmean : ∫ ω, X ω ∂μ = 0) :
    mgf X μ lam ≤ Real.exp
      (((∫ ω, X ω ^ 2 ∂μ) / K ^ 2) *
        (Real.exp (lam * K) - 1 - lam * K)) := by
  sorry

/- EXERCISE-SORRY (category A): Exercise 2.48(b) is not load-bearing. -/
/-- A sum of independent centered variables bounded by `K` satisfies Bennett's
two-sided tail inequality in terms of the total second moment and `bennettH`.

**Book Exercise 2.48(b).** -/
theorem exercise_2_48b [IsProbabilityMeasure μ] {N : ℕ} (hN : 0 < N)
    {X : Fin N → Ω → ℝ} (hXm : ∀ i, Measurable (X i))
    (hindep : iIndepFun X μ) {K : ℝ} (hK : 0 < K)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ K)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |∑ i, X i ω|} ≤
      2 * Real.exp (-((∑ i, ∫ ω, X i ω ^ 2 ∂μ) / K ^ 2) *
        bennettH (K * t / (∑ i, ∫ ω, X i ω ^ 2 ∂μ))) := by
  sorry

/- EXERCISE-SORRY (category A): Exercise 2.48(c) is not load-bearing. -/
/-- Bennett's function satisfies `bennettH u / u² → 1/2` as `u` tends to zero
from the right.

**Book Exercise 2.48(c).** -/
theorem exercise_2_48c :
    Tendsto (fun u : ℝ => bennettH u / u ^ 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 / 2 : ℝ)) := by
  sorry

/- EXERCISE-SORRY (category A): Exercise 2.48(d), numeric part, is not load-bearing. -/
/-- For `u ≥ 0`, Bennett's function is at least
`(1/2) u log u`.

**Book Exercise 2.48(d).** -/
theorem exercise_2_48d_numeric {u : ℝ} (hu : 0 ≤ u) :
    (1 / 2 : ℝ) * u * Real.log u ≤ bennettH u := by
  sorry

/- EXERCISE-SORRY (category A): Exercise 2.48(d), probabilistic consequence,
is not load-bearing. -/
/-- Combining Bennett's inequality with the lower bound on `bennettH` gives a
power-law upper bound for the tail of a bounded independent centered sum.

**Book Exercise 2.48(d).** -/
theorem exercise_2_48d [IsProbabilityMeasure μ] {N : ℕ} (hN : 0 < N)
    {X : Fin N → Ω → ℝ} (hXm : ∀ i, Measurable (X i))
    (hindep : iIndepFun X μ) {K : ℝ} (hK : 0 < K)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ K)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hvar : 0 < ∑ i, ∫ ω, X i ω ^ 2 ∂μ) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t ≤ |∑ i, X i ω|} ≤
      2 * ((∑ i, ∫ ω, X i ω ^ 2 ∂μ) / (K * t)) ^ (t / (2 * K)) := by
  sorry

end HDP.Chapter2
