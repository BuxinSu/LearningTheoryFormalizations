import MatrixConcentration.Chapter2_MatrixFunctionsAndProbabilityWithMatrices
import MatrixConcentration.Chapter6_SumOfBoundedRandomMatrices
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Chapter 1: Introduction and motivating examples

This consolidated chapter contains:

* **Book Theorem 1.6.1:** the scalar Bernstein inequality;
* **Book Theorem 1.6.2:** the matrix Bernstein inequality;
* **Book §§1.5.1 and 1.6.3:** the sample covariance estimator and its variance controls;
* **Book §1.6.3:** the resulting sample covariance error bounds.

The source blocks appear in dependency order: 02, 03, 01, then 04.
-/

set_option linter.unusedSectionVars false

/-!
# Theorem 1.6.1: scalar Bernstein inequality

The book states **Theorem 1.6.1 (Bernstein Inequality)** and cites
Boucheron--Lugosi--Massart, §2.8, for its proof. The formal proof here follows
the standard moment-generating-function argument:

1. an elementary exponential-series estimate;
2. the centered single-summand mgf bound;
3. mgf multiplicativity for an independent sum;
4. the Chernoff bound at the optimizing parameter;
5. a union bound applied to the sum and its negation.

`bernstein_variance_identity` formalizes the variance identity included in the
theorem statement. Boundedness is expressed almost everywhere, and it supplies
the required integrability.
-/

namespace MatrixConcentration

open MeasureTheory ProbabilityTheory Finset Real

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}

section SeriesBound

/-- Lean implementation helper: `2·3^k ≤ (k+2)!`. -/
private lemma two_mul_three_pow_le_factorial (k : ℕ) :
    2 * 3 ^ k ≤ (k + 2).factorial := by
  induction k with
  | zero => norm_num [Nat.factorial]
  | succ n ih =>
      have h1 : (n + 3).factorial = (n + 3) * (n + 2).factorial :=
        Nat.factorial_succ (n + 2)
      calc 2 * 3 ^ (n + 1) = 3 * (2 * 3 ^ n) := by ring
        _ ≤ 3 * (n + 2).factorial := Nat.mul_le_mul_left 3 ih
        _ ≤ (n + 3) * (n + 2).factorial :=
            Nat.mul_le_mul_right _ (by omega)
        _ = (n + 1 + 2).factorial := by
            rw [show n + 1 + 2 = n + 3 from rfl, h1]

/-- Lean implementation helper.

Source prerequisite recovered from context (the elementary inequality behind the
Bernstein mgf bound, BLM §2.8): for `|y| ≤ c < 3`,
`e^y ≤ 1 + y + y²/(2(1−c/3))`. -/
lemma exp_le_one_add_add_sq_div {y c : ℝ} (hy : |y| ≤ c) (hc : c < 3) :
    Real.exp y ≤ 1 + y + y ^ 2 / (2 * (1 - c / 3)) := by
  have hc0 : 0 ≤ c := le_trans (abs_nonneg y) hy
  have hr0 : (0 : ℝ) ≤ c / 3 := by positivity
  have hr1 : c / 3 < 1 := by linarith
  have hsum : Summable fun n : ℕ => y ^ n / n.factorial :=
    Real.summable_pow_div_factorial y
  have hexp : Real.exp y = ∑' n : ℕ, y ^ n / n.factorial := by
    rw [Real.exp_eq_exp_ℝ]
    exact congrFun NormedSpace.exp_eq_tsum_div y
  have hsplit : (∑ i ∈ Finset.range 2, y ^ i / i.factorial) +
      (∑' i : ℕ, y ^ (i + 2) / (i + 2).factorial) = ∑' n : ℕ, y ^ n / n.factorial :=
    hsum.sum_add_tsum_nat_add 2
  have hrange : (∑ i ∈ Finset.range 2, y ^ i / i.factorial) = 1 + y := by
    simp [Finset.sum_range_succ, Nat.factorial]
  have hterm : ∀ n : ℕ, y ^ (n + 2) / (n + 2).factorial ≤ y ^ 2 / 2 * (c / 3) ^ n := by
    intro n
    have h2 : |y ^ (n + 2) / ((n + 2).factorial : ℝ)| =
        |y| ^ (n + 2) / ((n + 2).factorial : ℝ) := by
      rw [abs_div, abs_pow, Nat.abs_cast]
    have h5 : |y| ^ n ≤ c ^ n := pow_le_pow_left₀ (abs_nonneg y) hy n
    have h3 : |y| ^ (n + 2) ≤ y ^ 2 * c ^ n := by
      calc |y| ^ (n + 2) = |y| ^ n * |y| ^ 2 := by ring
        _ ≤ c ^ n * y ^ 2 := by
            rw [sq_abs]
            exact mul_le_mul_of_nonneg_right h5 (sq_nonneg y)
        _ = y ^ 2 * c ^ n := by ring
    have h7 : (2 * 3 ^ n : ℝ) ≤ ((n + 2).factorial : ℝ) := by
      exact_mod_cast two_mul_three_pow_le_factorial n
    have hfact_pos : (0 : ℝ) < ((n + 2).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_pos (n + 2)
    calc y ^ (n + 2) / ((n + 2).factorial : ℝ)
        ≤ |y ^ (n + 2) / ((n + 2).factorial : ℝ)| := le_abs_self _
      _ = |y| ^ (n + 2) / ((n + 2).factorial : ℝ) := h2
      _ ≤ (y ^ 2 * c ^ n) / (2 * 3 ^ n) := by
          refine div_le_div₀ (by positivity) h3 (by positivity) h7
      _ = y ^ 2 / 2 * (c / 3) ^ n := by
          rw [div_pow]
          ring
  have hsum2 : Summable fun n : ℕ => y ^ (n + 2) / (n + 2).factorial :=
    (summable_nat_add_iff 2).mpr hsum
  have hgeo : Summable fun n : ℕ => y ^ 2 / 2 * (c / 3) ^ n :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have htail : (∑' n : ℕ, y ^ (n + 2) / (n + 2).factorial) ≤
      y ^ 2 / 2 * (1 - c / 3)⁻¹ := by
    calc (∑' n : ℕ, y ^ (n + 2) / (n + 2).factorial)
        ≤ ∑' n : ℕ, y ^ 2 / 2 * (c / 3) ^ n := hsum2.tsum_le_tsum hterm hgeo
      _ = y ^ 2 / 2 * (1 - c / 3)⁻¹ := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  have hDpos : (0 : ℝ) < 1 - c / 3 := by linarith
  have hfin : y ^ 2 / 2 * (1 - c / 3)⁻¹ = y ^ 2 / (2 * (1 - c / 3)) := by
    field_simp
  rw [hexp, ← hsplit, hrange]
  rw [hfin] at htail
  linarith

end SeriesBound

section MgfBound

variable [MeasureTheory.IsProbabilityMeasure μ]

/-- Lean implementation helper: bounded measurable random variables are integrable
with integrable squares. -/
private lemma integrable_of_abs_le {X : Ω → ℝ} (hXm : Measurable X) {L : ℝ}
    (hbdd : ∀ᵐ ω ∂μ, |X ω| ≤ L) :
    MeasureTheory.Integrable X μ ∧
      MeasureTheory.Integrable (fun ω => (X ω) ^ 2) μ := by
  constructor
  · refine MeasureTheory.Integrable.of_bound hXm.aestronglyMeasurable L ?_
    filter_upwards [hbdd] with ω h
    rwa [Real.norm_eq_abs]
  · refine MeasureTheory.Integrable.of_bound
      ((hXm.pow_const 2).aestronglyMeasurable) (L ^ 2) ?_
    filter_upwards [hbdd] with ω h
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2

/-- Lean implementation helper.

Source prerequisite recovered from context (the Bernstein mgf bound, BLM §2.8):
for a centered random variable with `|X| ≤ L` a.s. and `0 ≤ θ` with `θL < 3`,
`𝔼e^{θX} ≤ exp(θ²𝔼X²/(2(1−θL/3)))`. -/
lemma mgf_le_of_centered_of_abs_le {X : Ω → ℝ} (hXm : Measurable X)
    (hcent : ∫ ω, X ω ∂μ = 0) {L θ : ℝ} (hbdd : ∀ᵐ ω ∂μ, |X ω| ≤ L)
    (hθ : 0 ≤ θ) (hθL : θ * L < 3) :
    ProbabilityTheory.mgf X μ θ ≤
      Real.exp (θ ^ 2 * (∫ ω, (X ω) ^ 2 ∂μ) / (2 * (1 - θ * L / 3))) := by
  obtain ⟨hXint, hX2int⟩ := integrable_of_abs_le hXm hbdd
  have hD : (0 : ℝ) < 1 - θ * L / 3 := by linarith
  have hEX2 : 0 ≤ ∫ ω, (X ω) ^ 2 ∂μ :=
    MeasureTheory.integral_nonneg fun ω => sq_nonneg _
  have hpt : ∀ᵐ ω ∂μ, Real.exp (θ * X ω) ≤
      1 + θ * X ω + (θ ^ 2 / (2 * (1 - θ * L / 3))) * (X ω) ^ 2 := by
    filter_upwards [hbdd] with ω h
    have h1 : |θ * X ω| ≤ θ * L := by
      rw [abs_mul, abs_of_nonneg hθ]
      exact mul_le_mul_of_nonneg_left h hθ
    have h2 := exp_le_one_add_add_sq_div h1 hθL
    calc Real.exp (θ * X ω) ≤ 1 + θ * X ω + (θ * X ω) ^ 2 / (2 * (1 - θ * L / 3)) := h2
      _ = 1 + θ * X ω + (θ ^ 2 / (2 * (1 - θ * L / 3))) * (X ω) ^ 2 := by ring
  have hrhsint : MeasureTheory.Integrable (fun ω =>
      1 + θ * X ω + (θ ^ 2 / (2 * (1 - θ * L / 3))) * (X ω) ^ 2) μ :=
    ((MeasureTheory.integrable_const 1).add (hXint.const_mul θ)).add
      (hX2int.const_mul _)
  have hint_le : ProbabilityTheory.mgf X μ θ ≤
      1 + (θ ^ 2 / (2 * (1 - θ * L / 3))) * (∫ ω, (X ω) ^ 2 ∂μ) := by
    have h3 : ProbabilityTheory.mgf X μ θ = ∫ ω, Real.exp (θ * X ω) ∂μ := rfl
    rw [h3]
    calc (∫ ω, Real.exp (θ * X ω) ∂μ)
        ≤ ∫ ω, (1 + θ * X ω + (θ ^ 2 / (2 * (1 - θ * L / 3))) * (X ω) ^ 2) ∂μ :=
          MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le) hrhsint hpt
      _ = 1 + (θ ^ 2 / (2 * (1 - θ * L / 3))) * (∫ ω, (X ω) ^ 2 ∂μ) := by
          have hint1 : MeasureTheory.Integrable (fun ω => 1 + θ * X ω) μ :=
            (MeasureTheory.integrable_const 1).add (hXint.const_mul θ)
          have hint2 : MeasureTheory.Integrable
              (fun ω => (θ ^ 2 / (2 * (1 - θ * L / 3))) * (X ω) ^ 2) μ :=
            hX2int.const_mul _
          have hint0 : MeasureTheory.Integrable (fun _ : Ω => (1 : ℝ)) μ :=
            MeasureTheory.integrable_const 1
          have hint3 : MeasureTheory.Integrable (fun ω => θ * X ω) μ :=
            hXint.const_mul θ
          rw [MeasureTheory.integral_add hint1 hint2,
            MeasureTheory.integral_add hint0 hint3, MeasureTheory.integral_const,
            MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, hcent]
          simp
  have h4 := Real.add_one_le_exp
    ((θ ^ 2 / (2 * (1 - θ * L / 3))) * (∫ ω, (X ω) ^ 2 ∂μ))
  calc ProbabilityTheory.mgf X μ θ
      ≤ 1 + (θ ^ 2 / (2 * (1 - θ * L / 3))) * (∫ ω, (X ω) ^ 2 ∂μ) := hint_le
    _ ≤ Real.exp ((θ ^ 2 / (2 * (1 - θ * L / 3))) * (∫ ω, (X ω) ^ 2 ∂μ)) := by
        linarith
    _ = Real.exp (θ ^ 2 * (∫ ω, (X ω) ^ 2 ∂μ) / (2 * (1 - θ * L / 3))) := by
        congr 1
        ring

end MgfBound

section Bernstein

variable [MeasureTheory.IsProbabilityMeasure μ]
variable {ι : Type*} [Fintype ι] {S : ι → Ω → ℝ} {L : ℝ}

/-- Lean implementation helper.

The one-sided version used to prove Book Theorem 1.6.1:
`ℙ{Z ≥ t} ≤ exp(−t²/2 / (v(Z) + Lt/3))`. Source prerequisite recovered from context
(the two-sided Theorem 1.6.1 follows by a union bound; the one-sided form is also
what Chapter 6 uses). -/
theorem scalar_bernstein_one_sided
    (h_indep : ProbabilityTheory.iIndepFun S μ) (h_meas : ∀ k, Measurable (S k))
    (h_cent : ∀ k, ∫ ω, S k ω ∂μ = 0) (h_bdd : ∀ k, ∀ᵐ ω ∂μ, |S k ω| ≤ L)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ ∑ k, S k ω} ≤
      Real.exp ((-(t ^ 2) / 2) / ((∑ k, ∫ ω, (S k ω) ^ 2 ∂μ) + L * t / 3)) := by
  have hv0 : 0 ≤ ∑ k, ∫ ω, (S k ω) ^ 2 ∂μ :=
    Finset.sum_nonneg fun k _ => MeasureTheory.integral_nonneg fun ω => sq_nonneg _
  have htriv : μ.real {ω | t ≤ ∑ k, S k ω} ≤ 1 :=
    (measureReal_mono (Set.subset_univ _)).trans_eq (by simp)
  rcases le_total ((∑ k, ∫ ω, (S k ω) ^ 2 ∂μ) + L * t / 3) 0 with hD | hD'
  · -- degenerate case: nonpositive denominator makes the right side at least 1
    refine htriv.trans (Real.one_le_exp ?_)
    rcases hD.lt_or_eq with hDneg | hD0
    · have hnum : -(t ^ 2) / 2 ≤ 0 := by
        have : (0 : ℝ) ≤ t ^ 2 := sq_nonneg t
        linarith
      have hinv : ((∑ k, ∫ ω, (S k ω) ^ 2 ∂μ) + L * t / 3)⁻¹ ≤ 0 :=
        inv_nonpos.mpr hDneg.le
      rw [div_eq_mul_inv]
      nlinarith [mul_nonneg (neg_nonneg.mpr hnum) (neg_nonneg.mpr hinv)]
    · rw [hD0, div_zero]
  · rcases hD'.eq_or_lt with hD0 | hD
    case inr.inl =>
      refine htriv.trans (Real.one_le_exp ?_)
      rw [← hD0, div_zero]
    rcases ht.eq_or_lt with ht0 | htpos
    · -- t = 0
      refine htriv.trans (Real.one_le_exp ?_)
      rw [← ht0]
      simp
    · rcases hv0.eq_or_lt with hveq | hvpos
      · -- v = 0: the sum vanishes a.s.
        have hzero : ∀ k, ∀ᵐ ω ∂μ, S k ω = 0 := by
          intro k
          have hkz : ∫ ω, (S k ω) ^ 2 ∂μ = 0 := by
            have h1 : ∀ j ∈ Finset.univ, 0 ≤ ∫ ω, (S j ω) ^ 2 ∂μ := fun j _ =>
              MeasureTheory.integral_nonneg fun ω => sq_nonneg _
            have h2 := (Finset.sum_eq_zero_iff_of_nonneg h1).mp hveq.symm
            exact h2 k (Finset.mem_univ k)
          have hX2int := (integrable_of_abs_le (h_meas k) (h_bdd k)).2
          have h3 := (MeasureTheory.integral_eq_zero_iff_of_nonneg
            (fun ω => sq_nonneg (S k ω)) hX2int).mp hkz
          filter_upwards [h3] with ω hω
          exact pow_eq_zero_iff two_ne_zero |>.mp hω
        have hsumzero : ∀ᵐ ω ∂μ, (∑ k, S k ω) = 0 := by
          filter_upwards [ae_all_iff.mpr hzero] with ω hω
          exact Finset.sum_eq_zero fun k _ => hω k
        have hnull : μ {ω | t ≤ ∑ k, S k ω} = 0 := by
          refine measure_mono_null ?_ (ae_iff.mp hsumzero)
          intro ω hω
          rw [Set.mem_setOf_eq] at hω ⊢
          intro h0
          rw [h0] at hω
          linarith
        rw [measureReal_def, hnull]
        simp [(Real.exp_pos _).le]
      · -- main Chernoff case: t > 0, v > 0
        have hι : Nonempty ι := by
          by_contra h
          rw [not_nonempty_iff] at h
          rw [Finset.univ_eq_empty, Finset.sum_empty] at hvpos
          exact absurd hvpos (lt_irrefl 0)
        have hL0 : 0 ≤ L := by
          obtain ⟨ω, hω⟩ := (h_bdd (Classical.arbitrary ι)).exists
          exact le_trans (abs_nonneg _) hω
        set v := ∑ k, ∫ ω, (S k ω) ^ 2 ∂μ with hvdef
        set D := v + L * t / 3 with hDdef
        set θ := t / D with hθdef
        have hθpos : 0 < θ := div_pos htpos hD
        have hθL : θ * L < 3 := by
          rw [hθdef, div_mul_eq_mul_div, div_lt_iff₀ hD]
          nlinarith
        have hZmeas : Measurable fun ω => ∑ k, S k ω :=
          Finset.measurable_sum _ fun k _ => h_meas k
        have hZbdd : ∀ᵐ ω ∂μ, |∑ k, S k ω| ≤ (Fintype.card ι : ℝ) * L := by
          filter_upwards [ae_all_iff.mpr h_bdd] with ω hω
          calc |∑ k, S k ω| ≤ ∑ k, |S k ω| := Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ _k : ι, L := Finset.sum_le_sum fun k _ => hω k
            _ = (Fintype.card ι : ℝ) * L := by
                rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        have hexpint : MeasureTheory.Integrable
            (fun ω => Real.exp (θ * (∑ k, S k ω))) μ := by
          refine MeasureTheory.Integrable.of_bound
            ((Real.continuous_exp.measurable.comp (hZmeas.const_mul θ)).aestronglyMeasurable)
            (Real.exp (θ * ((Fintype.card ι : ℝ) * L))) ?_
          filter_upwards [hZbdd] with ω h
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          refine Real.exp_le_exp.mpr ?_
          have h1 : (∑ k, S k ω) ≤ (Fintype.card ι : ℝ) * L :=
            le_trans (le_abs_self _) h
          exact mul_le_mul_of_nonneg_left h1 hθpos.le
        -- Chernoff bound
        have hchern := ProbabilityTheory.measure_ge_le_exp_mul_mgf
          (X := fun ω => ∑ k, S k ω) (μ := μ) t hθpos.le hexpint
        -- mgf of the sum
        have hmgf_sum : ProbabilityTheory.mgf (fun ω => ∑ k, S k ω) μ θ =
            ∏ k, ProbabilityTheory.mgf (S k) μ θ := by
          have h1 := ProbabilityTheory.iIndepFun.mgf_sum h_indep h_meas
            Finset.univ (t := θ)
          have h2 : (∑ k ∈ Finset.univ, S k) = fun ω => ∑ k, S k ω := by
            funext ω
            exact Finset.sum_apply ω Finset.univ S
          rwa [h2] at h1
        have hmgf_le : ProbabilityTheory.mgf (fun ω => ∑ k, S k ω) μ θ ≤
            Real.exp (θ ^ 2 * v / (2 * (1 - θ * L / 3))) := by
          rw [hmgf_sum]
          calc (∏ k, ProbabilityTheory.mgf (S k) μ θ)
              ≤ ∏ k, Real.exp (θ ^ 2 * (∫ ω, (S k ω) ^ 2 ∂μ) /
                  (2 * (1 - θ * L / 3))) :=
                Finset.prod_le_prod (fun k _ => ProbabilityTheory.mgf_nonneg)
                  (fun k _ => mgf_le_of_centered_of_abs_le (h_meas k) (h_cent k)
                    (h_bdd k) hθpos.le hθL)
            _ = Real.exp (∑ k, θ ^ 2 * (∫ ω, (S k ω) ^ 2 ∂μ) /
                  (2 * (1 - θ * L / 3))) := (Real.exp_sum _ _).symm
            _ = Real.exp (θ ^ 2 * v / (2 * (1 - θ * L / 3))) := by
                congr 1
                rw [← Finset.sum_div, ← Finset.mul_sum]
        -- the exponent algebra at the optimizing θ
        have hv' : v ≠ 0 := ne_of_gt hvpos
        have hD' : D ≠ 0 := ne_of_gt hD
        have hone : 1 - θ * L / 3 = v / D := by
          rw [hθdef]
          field_simp
          rw [hDdef]
          ring
        have hexp_arith : -θ * t + θ ^ 2 * v / (2 * (1 - θ * L / 3)) =
            (-(t ^ 2) / 2) / D := by
          rw [hone, hθdef]
          field_simp
          ring
        calc μ.real {ω | t ≤ ∑ k, S k ω}
            ≤ Real.exp (-θ * t) * ProbabilityTheory.mgf (fun ω => ∑ k, S k ω) μ θ :=
              hchern
          _ ≤ Real.exp (-θ * t) * Real.exp (θ ^ 2 * v / (2 * (1 - θ * L / 3))) :=
              mul_le_mul_of_nonneg_left hmgf_le (Real.exp_pos _).le
          _ = Real.exp (-θ * t + θ ^ 2 * v / (2 * (1 - θ * L / 3))) :=
              (Real.exp_add _ _).symm
          _ = Real.exp ((-(t ^ 2) / 2) / D) := by rw [hexp_arith]

/-- **Book Theorem 1.6.1 (Bernstein Inequality).**

Explicit source declaration. "Let `S₁, …, Sₙ` be independent, centered, real random
variables, and assume that each one is uniformly bounded: `𝔼Sₖ = 0` and `|Sₖ| ≤ L`.
Introduce the sum `Z = Σₖ Sₖ`, and let `v(Z)` denote the variance of the sum:
`v(Z) = 𝔼Z² = Σₖ𝔼Sₖ²`. Then `ℙ{|Z| ≥ t} ≤ 2·exp(−t²/2 / (v(Z) + Lt/3))` for all
`t ≥ 0`."

The proof follows the mgf argument cited by the book. The identity
`v(Z) = 𝔼Z² = Σₖ𝔼Sₖ²` is `bernstein_variance_identity`; the bound uses
the summand form `Σₖ𝔼Sₖ²` appearing in the theorem. -/
theorem scalar_bernstein
    (h_indep : ProbabilityTheory.iIndepFun S μ) (h_meas : ∀ k, Measurable (S k))
    (h_cent : ∀ k, ∫ ω, S k ω ∂μ = 0) (h_bdd : ∀ k, ∀ᵐ ω ∂μ, |S k ω| ≤ L)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |∑ k, S k ω|} ≤
      2 * Real.exp ((-(t ^ 2) / 2) / ((∑ k, ∫ ω, (S k ω) ^ 2 ∂μ) + L * t / 3)) := by
  -- the negated family
  have h_indepN : ProbabilityTheory.iIndepFun (fun k (ω : Ω) => -(S k ω)) μ :=
    h_indep.comp _ fun k => measurable_neg
  have h_measN : ∀ k, Measurable fun ω => -(S k ω) := fun k => (h_meas k).neg
  have h_centN : ∀ k, ∫ ω, -(S k ω) ∂μ = 0 := fun k => by
    rw [MeasureTheory.integral_neg, h_cent k, neg_zero]
  have h_bddN : ∀ k, ∀ᵐ ω ∂μ, |-(S k ω)| ≤ L := fun k => by
    filter_upwards [h_bdd k] with ω h
    rwa [abs_neg]
  have hvarN : ∀ k, (∫ ω, (-(S k ω)) ^ 2 ∂μ) = ∫ ω, (S k ω) ^ 2 ∂μ := fun k =>
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ω => neg_sq _)
  have hone := scalar_bernstein_one_sided h_indep h_meas h_cent h_bdd ht
  have honeN := scalar_bernstein_one_sided h_indepN h_measN h_centN h_bddN ht
  simp only [hvarN] at honeN
  -- the union bound
  have hsub : {ω | t ≤ |∑ k, S k ω|} ⊆
      {ω | t ≤ ∑ k, S k ω} ∪ {ω | t ≤ ∑ k, -(S k ω)} := by
    intro ω hω
    rw [Set.mem_setOf_eq] at hω
    rcases le_abs.mp hω with h | h
    · exact Set.mem_union_left _ h
    · refine Set.mem_union_right _ ?_
      rw [Set.mem_setOf_eq, Finset.sum_neg_distrib]
      exact h
  calc μ.real {ω | t ≤ |∑ k, S k ω|}
      ≤ μ.real ({ω | t ≤ ∑ k, S k ω} ∪ {ω | t ≤ ∑ k, -(S k ω)}) :=
        measureReal_mono hsub
    _ ≤ μ.real {ω | t ≤ ∑ k, S k ω} + μ.real {ω | t ≤ ∑ k, -(S k ω)} :=
        measureReal_union_le _ _
    _ ≤ 2 * Real.exp ((-(t ^ 2) / 2) /
          ((∑ k, ∫ ω, (S k ω) ^ 2 ∂μ) + L * t / 3)) := by
        linarith

/-- **Book Theorem 1.6.1 (variance identity).**

The implicit claim inside Theorem 1.6.1's statement:
"let `v(Z)` denote the variance of the sum: `v(Z) = 𝔼Z² = Σₖ𝔼Sₖ²`" — the variance of
an independent centered sum is the sum of the second moments. Implicit source
declaration, proved via `IndepFun.variance_sum`. -/
theorem bernstein_variance_identity [DecidableEq ι]
    (h_indep : ProbabilityTheory.iIndepFun S μ) (h_meas : ∀ k, Measurable (S k))
    (h_cent : ∀ k, ∫ ω, S k ω ∂μ = 0) (h_bdd : ∀ k, ∀ᵐ ω ∂μ, |S k ω| ≤ L) :
    ∫ ω, (∑ k, S k ω) ^ 2 ∂μ = ∑ k, ∫ ω, (S k ω) ^ 2 ∂μ := by
  have hMem : ∀ k, MeasureTheory.MemLp (S k) 2 μ := fun k =>
    MeasureTheory.memLp_of_bounded
      (by filter_upwards [h_bdd k] with ω h
          exact Set.mem_Icc.mpr (abs_le.mp h))
      (h_meas k).aestronglyMeasurable 2
  -- for centered X, Var X = 𝔼X²
  have hvar_eq : ∀ (X : Ω → ℝ), Measurable X → (∫ ω, X ω ∂μ) = 0 →
      ProbabilityTheory.variance X μ = ∫ ω, (X ω) ^ 2 ∂μ := by
    intro X hXm hX0
    rw [ProbabilityTheory.variance_eq_integral hXm.aemeasurable]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    show (X ω - μ[X]) ^ 2 = X ω ^ 2
    rw [hX0, sub_zero]
  have hsum_cent : ∫ ω, (∑ k ∈ Finset.univ, S k) ω ∂μ = 0 := by
    have h1 : ∀ ω, (∑ k ∈ Finset.univ, S k) ω = ∑ k, S k ω := fun ω =>
      Finset.sum_apply ω Finset.univ S
    simp only [h1]
    rw [MeasureTheory.integral_finsetSum _ fun k _ =>
      (integrable_of_abs_le (h_meas k) (h_bdd k)).1]
    exact Finset.sum_eq_zero fun k _ => h_cent k
  have hvs := ProbabilityTheory.IndepFun.variance_sum (s := Finset.univ)
    (fun k _ => hMem k)
    (fun i _ j _ hij => h_indep.indepFun hij)
  have hZmeas : Measurable (∑ k ∈ Finset.univ, S k) := by
    have h1 : (∑ k ∈ Finset.univ, S k) = fun ω => ∑ k, S k ω := by
      funext ω
      exact Finset.sum_apply ω Finset.univ S
    rw [h1]
    exact Finset.measurable_sum _ fun k _ => h_meas k
  have h2 := hvar_eq (∑ k ∈ Finset.univ, S k) hZmeas hsum_cent
  rw [hvs] at h2
  have h3 : ∀ ω, (∑ k ∈ Finset.univ, S k) ω = ∑ k, S k ω := fun ω =>
    Finset.sum_apply ω Finset.univ S
  simp only [h3] at h2
  rw [← h2]
  exact Finset.sum_congr rfl fun k _ => hvar_eq (S k) (h_meas k) (h_cent k)

end Bernstein

end MatrixConcentration

set_option linter.unusedSectionVars false

/-!
# Theorem 1.6.2: matrix Bernstein inequality

This section formalizes the three displays associated with **Theorem 1.6.2**:

* `matrix_bernstein_variance_eq` -- matrix variance, equation (1.6.4);
* `matrix_bernstein_tail` -- the tail estimate, equation (1.6.5);
* `matrix_bernstein_expectation` -- the expectation estimate, equation (1.6.6).

The tail and expectation proofs use the rectangular Matrix Bernstein results
from the Chapter 6 module. The declaration comments record the explicit
boundary and integrability conventions used by Lean.
-/

namespace MatrixConcentration

open Matrix MeasureTheory ProbabilityTheory Finset
open scoped Matrix.Norms.L2Operator

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

section VarianceConsistency

variable [MeasureTheory.IsProbabilityMeasure μ]

/-- Lean implementation helper: for a centered random matrix, `mVar₁(Z) = 𝔼(ZZ*)`. -/
lemma matrixVar1_of_centered {Z : Ω → Matrix m n ℂ} (hcent : expectation μ Z = 0) :
    matrixVar1 μ Z = expectation μ (fun ω => Z ω * (Z ω)ᴴ) := by
  rw [matrixVar1, hcent]
  simp only [sub_zero]

/-- Lean implementation helper: for a centered random matrix, `mVar₂(Z) = 𝔼(Z*Z)`. -/
lemma matrixVar2_of_centered {Z : Ω → Matrix m n ℂ} (hcent : expectation μ Z = 0) :
    matrixVar2 μ Z = expectation μ (fun ω => (Z ω)ᴴ * Z ω) := by
  rw [matrixVar2, hcent]
  simp only [sub_zero]

/-- **Book equation (1.6.4).**

For independent, centered summands the two formulas for
the matrix variance statistic agree,
`max{‖𝔼(ZZ*)‖, ‖𝔼(Z*Z)‖} = max{‖Σₖ𝔼(SₖSₖ*)‖, ‖Σₖ𝔼(Sₖ*Sₖ)‖}` with `Z = Σₖ Sₖ`.
This is the variance identity used in Theorem 1.6.2. -/
theorem matrix_bernstein_variance_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Ω → Matrix m n ℂ}
    (hind : ProbabilityTheory.iIndepFun S μ) (hmeas : ∀ k, Measurable (S k))
    (hS : ∀ k, MIntegrable (S k) μ)
    (hS1 : ∀ k, MIntegrable (fun ω => S k ω * (S k ω)ᴴ) μ)
    (hS2 : ∀ k, MIntegrable (fun ω => (S k ω)ᴴ * S k ω) μ)
    (hcent : ∀ k, expectation μ (S k) = 0) :
    max ‖expectation μ (fun ω => (∑ k, S k ω) * (∑ k, S k ω)ᴴ)‖
        ‖expectation μ (fun ω => (∑ k, S k ω)ᴴ * (∑ k, S k ω))‖ =
      max ‖∑ k, expectation μ (fun ω => S k ω * (S k ω)ᴴ)‖
          ‖∑ k, expectation μ (fun ω => (S k ω)ᴴ * S k ω)‖ := by
  have hEsum : expectation μ (fun ω => ∑ k, S k ω) = 0 := by
    rw [expectation_finsetSum _ fun k _ => hS k]
    exact Finset.sum_eq_zero fun k _ => hcent k
  have h1 : expectation μ (fun ω => (∑ k, S k ω) * (∑ k, S k ω)ᴴ) =
      ∑ k, expectation μ (fun ω => S k ω * (S k ω)ᴴ) := by
    rw [← matrixVar1_of_centered hEsum,
      matrixVar1_sum hind hmeas hS hS1]
    exact Finset.sum_congr rfl fun k _ => matrixVar1_of_centered (hcent k)
  have h2 : expectation μ (fun ω => (∑ k, S k ω)ᴴ * (∑ k, S k ω)) =
      ∑ k, expectation μ (fun ω => (S k ω)ᴴ * S k ω) := by
    rw [← matrixVar2_of_centered hEsum,
      matrixVar2_sum hind hmeas hS hS2]
    exact Finset.sum_congr rfl fun k _ => matrixVar2_of_centered (hcent k)
  rw [h1, h2]

end VarianceConsistency

section MatrixBernstein

variable [MeasureTheory.IsProbabilityMeasure μ]
variable {d₁ d₂ : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Book equation (1.6.5), Matrix Bernstein tail bound.**

The statistic `v(Z)` is written via equation (1.6.4); the equality
with the summand form is `matrix_bernstein_variance_eq`.  The hypothesis
`0 < d₁ + d₂` records the nonzero dimension, while boundedness is stated
almost everywhere.

Author note: Lean makes the book’s implicit boundary and regularity conditions
explicit: positive total dimension, a nonnegative norm bound, and an
almost-everywhere boundedness hypothesis; boundedness supplies the required
matrix integrability. -/
theorem matrix_bernstein_tail (hd : 0 < d₁ + d₂)
    {S : ι → Ω → Matrix (Fin d₁) (Fin d₂) ℂ} {L : ℝ}
    (h_indep : ProbabilityTheory.iIndepFun S μ) (h_meas : ∀ k, Measurable (S k))
    (h_cent : ∀ k, expectation μ (S k) = 0)
    (h_bdd : ∀ k, ∀ᵐ ω ∂μ, ‖S k ω‖ ≤ L) (hL : 0 ≤ L) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ ‖∑ k, S k ω‖} ≤
      (d₁ + d₂) * Real.exp ((-(t ^ 2) / 2) /
        (max ‖expectation μ (fun ω => (∑ k, S k ω) * (∑ k, S k ω)ᴴ)‖
             ‖expectation μ (fun ω => (∑ k, S k ω)ᴴ * (∑ k, S k ω))‖ + L * t / 3)) := by
  haveI : Nonempty (Fin d₁ ⊕ Fin d₂) := by
    rcases Nat.lt_or_ge 0 d₁ with h | h
    · exact ⟨Sum.inl ⟨0, h⟩⟩
    · exact ⟨Sum.inr ⟨0, by omega⟩⟩
  -- integrability plumbing from the a.e. bounds
  have hS : ∀ k, MIntegrable (S k) μ := fun k =>
    MIntegrable.of_bound (h_meas k) L ((h_bdd k).mono fun ω h i j =>
      (norm_entry_le_l2_opNorm_rect _ _ _).trans h)
  have hS1 : ∀ k, MIntegrable (fun ω => S k ω * (S k ω)ᴴ) μ := fun k =>
    MIntegrable.of_bound (measurable_mul_conjTranspose_self (h_meas k)) (L * L)
      ((h_bdd k).mono fun ω h i j => by
        calc ‖(S k ω * (S k ω)ᴴ) i j‖ ≤ ‖S k ω * (S k ω)ᴴ‖ :=
              norm_entry_le_l2_opNorm_rect _ _ _
        _ ≤ ‖S k ω‖ * ‖(S k ω)ᴴ‖ := Matrix.l2_opNorm_mul _ _
        _ = ‖S k ω‖ * ‖S k ω‖ := by rw [Matrix.l2_opNorm_conjTranspose]
        _ ≤ L * L := by nlinarith [norm_nonneg (S k ω)])
  have hS2 : ∀ k, MIntegrable (fun ω => (S k ω)ᴴ * S k ω) μ := fun k =>
    MIntegrable.of_bound (measurable_conjTranspose_mul_self (h_meas k)) (L * L)
      ((h_bdd k).mono fun ω h i j => by
        calc ‖((S k ω)ᴴ * S k ω) i j‖ ≤ ‖(S k ω)ᴴ * S k ω‖ :=
              norm_entry_le_l2_opNorm_rect _ _ _
        _ ≤ ‖(S k ω)ᴴ‖ * ‖S k ω‖ := Matrix.l2_opNorm_mul _ _
        _ = ‖S k ω‖ * ‖S k ω‖ := by rw [Matrix.l2_opNorm_conjTranspose]
        _ ≤ L * L := by nlinarith [norm_nonneg (S k ω)])
  have hvar := matrix_bernstein_variance_eq h_indep h_meas hS hS1 hS2 h_cent
  have h := matrix_bernstein_rect_tail_ae (μ := μ) h_meas h_bdd hL h_cent
    h_indep ht
  rw [hvar]
  rw [show ((Fintype.card (Fin d₁) : ℝ)) = (d₁ : ℝ) from by
      rw [Fintype.card_fin],
    show ((Fintype.card (Fin d₂) : ℝ)) = (d₂ : ℝ) from by
      rw [Fintype.card_fin]] at h
  exact h

/-- **Book equation (1.6.6), Matrix Bernstein expectation bound.**

This is the expectation estimate highlighted by the book. Its boundary and
regularity conventions match `matrix_bernstein_tail`.

Author note: Lean makes the book’s implicit boundary and regularity conditions
explicit: positive total dimension, a nonnegative norm bound, and an
almost-everywhere boundedness hypothesis; boundedness supplies the required
matrix integrability. -/
theorem matrix_bernstein_expectation (hd : 0 < d₁ + d₂)
    {S : ι → Ω → Matrix (Fin d₁) (Fin d₂) ℂ} {L : ℝ}
    (h_indep : ProbabilityTheory.iIndepFun S μ) (h_meas : ∀ k, Measurable (S k))
    (h_cent : ∀ k, expectation μ (S k) = 0)
    (h_bdd : ∀ k, ∀ᵐ ω ∂μ, ‖S k ω‖ ≤ L) (hL : 0 ≤ L) :
    ∫ ω, ‖∑ k, S k ω‖ ∂μ ≤
      Real.sqrt (2 * (max ‖expectation μ (fun ω => (∑ k, S k ω) * (∑ k, S k ω)ᴴ)‖
          ‖expectation μ (fun ω => (∑ k, S k ω)ᴴ * (∑ k, S k ω))‖) *
        Real.log (d₁ + d₂)) +
      (1 / 3) * L * Real.log (d₁ + d₂) := by
  haveI : Nonempty (Fin d₁ ⊕ Fin d₂) := by
    rcases Nat.lt_or_ge 0 d₁ with h | h
    · exact ⟨Sum.inl ⟨0, h⟩⟩
    · exact ⟨Sum.inr ⟨0, by omega⟩⟩
  have hS : ∀ k, MIntegrable (S k) μ := fun k =>
    MIntegrable.of_bound (h_meas k) L ((h_bdd k).mono fun ω h i j =>
      (norm_entry_le_l2_opNorm_rect _ _ _).trans h)
  have hS1 : ∀ k, MIntegrable (fun ω => S k ω * (S k ω)ᴴ) μ := fun k =>
    MIntegrable.of_bound (measurable_mul_conjTranspose_self (h_meas k)) (L * L)
      ((h_bdd k).mono fun ω h i j => by
        calc ‖(S k ω * (S k ω)ᴴ) i j‖ ≤ ‖S k ω * (S k ω)ᴴ‖ :=
              norm_entry_le_l2_opNorm_rect _ _ _
        _ ≤ ‖S k ω‖ * ‖(S k ω)ᴴ‖ := Matrix.l2_opNorm_mul _ _
        _ = ‖S k ω‖ * ‖S k ω‖ := by rw [Matrix.l2_opNorm_conjTranspose]
        _ ≤ L * L := by nlinarith [norm_nonneg (S k ω)])
  have hS2 : ∀ k, MIntegrable (fun ω => (S k ω)ᴴ * S k ω) μ := fun k =>
    MIntegrable.of_bound (measurable_conjTranspose_mul_self (h_meas k)) (L * L)
      ((h_bdd k).mono fun ω h i j => by
        calc ‖((S k ω)ᴴ * S k ω) i j‖ ≤ ‖(S k ω)ᴴ * S k ω‖ :=
              norm_entry_le_l2_opNorm_rect _ _ _
        _ ≤ ‖(S k ω)ᴴ‖ * ‖S k ω‖ := Matrix.l2_opNorm_mul _ _
        _ = ‖S k ω‖ * ‖S k ω‖ := by rw [Matrix.l2_opNorm_conjTranspose]
        _ ≤ L * L := by nlinarith [norm_nonneg (S k ω)])
  have hvar := matrix_bernstein_variance_eq h_indep h_meas hS hS1 hS2 h_cent
  have h := matrix_bernstein_rect_expectation_ae (μ := μ) h_meas h_bdd hL
    h_cent h_indep
  rw [hvar]
  rw [show ((Fintype.card (Fin d₁) : ℝ)) = (d₁ : ℝ) from by
      rw [Fintype.card_fin],
    show ((Fintype.card (Fin d₂) : ℝ)) = (d₂ : ℝ) from by
      rw [Fintype.card_fin]] at h
  calc ∫ ω, ‖∑ k, S k ω‖ ∂μ
      ≤ Real.sqrt (2 * max ‖∑ k, expectation μ (fun ω => S k ω * (S k ω)ᴴ)‖
          ‖∑ k, expectation μ (fun ω => (S k ω)ᴴ * S k ω)‖ *
        Real.log ((d₁ : ℝ) + (d₂ : ℝ))) +
        L / 3 * Real.log ((d₁ : ℝ) + (d₂ : ℝ)) := h
  _ = Real.sqrt (2 * (max ‖∑ k, expectation μ (fun ω => S k ω * (S k ω)ᴴ)‖
          ‖∑ k, expectation μ (fun ω => (S k ω)ᴴ * S k ω)‖) *
        Real.log ((d₁ : ℝ) + (d₂ : ℝ))) +
        (1 / 3) * L * Real.log ((d₁ : ℝ) + (d₂ : ℝ)) := by
      ring_nf

end MatrixBernstein

end MatrixConcentration

set_option linter.unusedSectionVars false

/-!
# The sample covariance estimator (Book §1.5.1 and §1.6.3)

* `covarianceMatrix`, its entrywise and matrix-unit forms, and positivity --
  equation (1.5.1);
* `sampleCovariance` and its unbiasedness -- equation (1.5.2) and the prose
  immediately following it;
* `sampleCovSummand`, centering, independence, and the decomposition of the
  estimation error -- §1.6.3;
* uniform summand and square-function bounds culminating in
  `sampleCov_norm_sum_sq_le` -- the display sequence in §1.6.3.

The uniform sample bound is stated almost everywhere for each sample. For
identically distributed samples this is the measure-theoretic form of the
book's single boundedness hypothesis.
-/

namespace MatrixConcentration

open Matrix MeasureTheory ProbabilityTheory Finset
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
variable {n : Type*} [Fintype n] [DecidableEq n]

section RankOne

/-- Lean implementation helper.

Book §1.5.1 (implicit in "the positive-semidefinite matrix"): the rank-one matrix
`xx*` is positive semidefinite. Implicit source declaration. -/
lemma posSemidef_vecMulVec_star (x : n → ℂ) : (vecMulVec x (star x)).PosSemidef := by
  have h2 : vecMulVec x (star x) =
      Matrix.replicateCol Unit x * (Matrix.replicateCol Unit x)ᴴ := by
    ext i j
    simp [Matrix.mul_apply, vecMulVec_apply]
  rw [h2]
  exact Matrix.posSemidef_self_mul_conjTranspose _

/-- Lean implementation helper: `ω ↦ x(ω)x(ω)*` is measurable. -/
lemma measurable_vecMulVec_star {x : Ω → (n → ℂ)} (hx : Measurable x) :
    Measurable fun ω => vecMulVec (x ω) (star (x ω)) := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  have h1 : (fun ω => vecMulVec (x ω) (star (x ω)) i j) =
      fun ω => x ω i * (starRingEnd ℂ) (x ω j) := rfl
  rw [h1]
  exact ((measurable_pi_apply i).comp hx).mul
    (RCLike.continuous_conj.measurable.comp ((measurable_pi_apply j).comp hx))

/-- Lean implementation helper: entrywise bound `|xᵢ x̄ⱼ| ≤ ‖x‖²`. -/
lemma abs_entry_vecMulVec_le (x : n → ℂ) (i j : n) :
    ‖vecMulVec x (star x) i j‖ ≤ l2norm x ^ 2 := by
  have h1 : ‖vecMulVec x (star x) i j‖ = ‖x i‖ * ‖x j‖ := by
    rw [vecMulVec_apply, norm_mul]
    congr 1
    exact RCLike.norm_conj _
  rw [h1]
  have h2 : ∀ k, ‖x k‖ ≤ l2norm x := fun k => by
    have h3 := l2norm_sq x
    have h4 : ‖x k‖ ^ 2 ≤ ∑ i, ‖x i‖ ^ 2 :=
      Finset.single_le_sum (f := fun i => ‖x i‖ ^ 2) (fun i _ => by positivity)
        (Finset.mem_univ k)
    nlinarith [l2norm_nonneg x, norm_nonneg (x k)]
  calc ‖x i‖ * ‖x j‖ ≤ l2norm x * l2norm x :=
        mul_le_mul (h2 i) (h2 j) (norm_nonneg _) (l2norm_nonneg x)
    _ = l2norm x ^ 2 := (sq (l2norm x)).symm

/-- Lean implementation helper: integrability of `xx*` under the book's boundedness
hypothesis (standing convention §2.2.1). -/
lemma mintegrable_vecMulVec_of_bound [MeasureTheory.IsProbabilityMeasure μ]
    {x : Ω → (n → ℂ)} (hx : Measurable x) {B : ℝ}
    (hB : ∀ᵐ ω ∂μ, l2norm (x ω) ^ 2 ≤ B) :
    MIntegrable (fun ω => vecMulVec (x ω) (star (x ω))) μ := by
  refine MIntegrable.of_bound (measurable_vecMulVec_star hx) B ?_
  filter_upwards [hB] with ω hω
  intro i j
  exact (abs_entry_vecMulVec_le (x ω) i j).trans hω

end RankOne

section Covariance

variable [MeasureTheory.IsProbabilityMeasure μ]

/-- **Book equation (1.5.1).** The covariance matrix
`A = 𝔼(xx*)` of a (centered) random vector. Implicit source declaration ("The
covariance matrix `A` of the random vector `x` is the positive-semidefinite
matrix…"). -/
noncomputable def covarianceMatrix (μ : MeasureTheory.Measure Ω) (x : Ω → (n → ℂ)) :
    Matrix n n ℂ :=
  expectation μ fun ω => vecMulVec (x ω) (star (x ω))

/-- **Book equation (1.5.1), entrywise form.**

Book eq. (1.5.1), entrywise reading (the `Σⱼₖ 𝔼(XⱼXₖ*)Eⱼₖ` display): the `(j,k)`
entry of `A` records the covariance of the `j`-th and `k`-th entries of `x`. -/
lemma covarianceMatrix_apply (x : Ω → (n → ℂ)) (j k : n) :
    covarianceMatrix μ x j k = ∫ ω, x ω j * (starRingEnd ℂ) (x ω k) ∂μ := rfl

/-- **Book equation (1.5.1), matrix-unit expansion.**

Book eq. (1.5.1), the `A = Σⱼₖ 𝔼(Xⱼ X̄ₖ) Eⱼₖ` display: expansion of the covariance
matrix in the standard matrix basis `Eⱼₖ = Matrix.single j k 1`. Implicit source
identity. -/
lemma covarianceMatrix_eq_sum_single (x : Ω → (n → ℂ)) :
    covarianceMatrix μ x = ∑ j, ∑ k,
      Matrix.single j k (∫ ω, x ω j * (starRingEnd ℂ) (x ω k) ∂μ) := by
  rw [Matrix.matrix_eq_sum_single (covarianceMatrix μ x)]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by
    rw [covarianceMatrix_apply]

/-- **Book equation (1.5.1), positivity statement.**

Book §1.5.1: the covariance matrix is positive semidefinite. Implicit source
claim. -/
theorem posSemidef_covarianceMatrix {x : Ω → (n → ℂ)}
    (hxx : MIntegrable (fun ω => vecMulVec (x ω) (star (x ω))) μ) :
    (covarianceMatrix μ x).PosSemidef :=
  posSemidef_expectation hxx
    (Filter.Eventually.of_forall fun ω => posSemidef_vecMulVec_star (x ω))

/-- **Book §1.6.3.** The bound `‖A‖ = ‖𝔼(xx*)‖ ≤ 𝔼‖xx*‖ = 𝔼‖x‖² ≤ B`
— "This expression depends on Jensen's inequality and the hypothesis that `x` is
bounded." Intermediate claim of the source, fully proved (Jensen instance
`norm_expectation_le` + `‖xx*‖ = ‖x‖²`). -/
theorem norm_covarianceMatrix_le {x : Ω → (n → ℂ)} (hx : Measurable x) {B : ℝ}
    (hB : ∀ᵐ ω ∂μ, l2norm (x ω) ^ 2 ≤ B) :
    ‖covarianceMatrix μ x‖ ≤ B := by
  have hxx := mintegrable_vecMulVec_of_bound hx hB
  have hnormmeas : Measurable fun ω => ‖vecMulVec (x ω) (star (x ω))‖ :=
    continuous_norm.measurable.comp (measurable_vecMulVec_star hx)
  have hnormbd : ∀ᵐ ω ∂μ, ‖vecMulVec (x ω) (star (x ω))‖ ≤ B := by
    filter_upwards [hB] with ω hω
    rw [l2_opNorm_vecMulVec_star_self]
    exact hω
  have hnormint : MeasureTheory.Integrable
      (fun ω => ‖vecMulVec (x ω) (star (x ω))‖) μ := by
    refine MeasureTheory.Integrable.of_bound hnormmeas.aestronglyMeasurable B ?_
    filter_upwards [hnormbd] with ω hω
    calc ‖‖vecMulVec (x ω) (star (x ω))‖‖ = ‖vecMulVec (x ω) (star (x ω))‖ :=
          norm_norm _
      _ ≤ B := hω
  calc ‖covarianceMatrix μ x‖ ≤ ∫ ω, ‖vecMulVec (x ω) (star (x ω))‖ ∂μ :=
        norm_expectation_le hxx hnormint
    _ ≤ ∫ _, B ∂μ := MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun ω => norm_nonneg _)
        (MeasureTheory.integrable_const B) hnormbd
    _ = B := by simp

end Covariance

section SampleCovariance

variable [MeasureTheory.IsProbabilityMeasure μ]
variable {P nn : ℕ}

/-- **Book equation (1.5.2).** The sample covariance
estimator `Y = n⁻¹ Σₖ xₖxₖ*` built from `n` samples. Implicit source declaration. -/
noncomputable def sampleCovariance (μ : MeasureTheory.Measure Ω) (nn : ℕ)
    (xs : Fin nn → Ω → (Fin P → ℂ)) (ω : Ω) : Matrix (Fin P) (Fin P) ℂ :=
  (nn : ℝ)⁻¹ • ∑ k, vecMulVec (xs k ω) (star (xs k ω))

/-- Lean implementation helper: real-scalar version of expectation homogeneity. -/
lemma expectation_smul_real {m' n' : Type*} [Fintype m'] [Fintype n'] [DecidableEq m']
    [DecidableEq n'] (α : ℝ) (Z : Ω → Matrix m' n' ℂ) :
    expectation μ (fun ω => α • Z ω) = α • expectation μ Z := by
  ext i j
  show (∫ ω, (α • Z ω) i j ∂μ) = α • expectation μ Z i j
  have h1 : (fun ω => (α • Z ω) i j) = fun ω => α • (Z ω i j) := rfl
  rw [h1, MeasureTheory.integral_smul]
  rfl

/-- Lean implementation helper: transport of the second-moment matrix along equal
distributions (the samples "with the same distribution as `x`"). -/
lemma expectation_vecMulVec_of_identDistrib {x y : Ω → (Fin P → ℂ)}
    (hid : ProbabilityTheory.IdentDistrib y x μ μ) :
    expectation μ (fun ω => vecMulVec (y ω) (star (y ω))) =
      expectation μ (fun ω => vecMulVec (x ω) (star (x ω))) := by
  ext i j
  rw [expectation_apply, expectation_apply]
  have hg : Measurable fun v : Fin P → ℂ => v i * (starRingEnd ℂ) (v j) :=
    (measurable_pi_apply i).mul
      (RCLike.continuous_conj.measurable.comp (measurable_pi_apply j))
  exact (hid.comp hg).integral_eq

/-- **Book §1.5.1, prose after equation (1.5.2).**

Book §1.5.1: "The random matrix `Y` is an unbiased estimator for the … covariance
matrix: `𝔼Y = A`." Implicit source claim, fully proved. -/
theorem expectation_sampleCovariance (hnn : nn ≠ 0) {x : Ω → (Fin P → ℂ)}
    {xs : Fin nn → Ω → (Fin P → ℂ)}
    (hid : ∀ k, ProbabilityTheory.IdentDistrib (xs k) x μ μ)
    (hxs : ∀ k, MIntegrable (fun ω => vecMulVec (xs k ω) (star (xs k ω))) μ) :
    expectation μ (sampleCovariance μ nn xs) = covarianceMatrix μ x := by
  rw [show sampleCovariance μ nn xs =
    fun ω => (nn : ℝ)⁻¹ • ∑ k, vecMulVec (xs k ω) (star (xs k ω)) from rfl]
  rw [expectation_smul_real, expectation_finsetSum _ fun k _ => hxs k]
  rw [Finset.sum_congr rfl fun k _ => expectation_vecMulVec_of_identDistrib (hid k)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul (R := ℝ), smul_smul,
    show ((nn : ℝ)⁻¹ * (nn : ℝ)) = 1 from by field_simp, one_smul]
  rfl

end SampleCovariance

section Analysis

variable [MeasureTheory.IsProbabilityMeasure μ]
variable {P nn : ℕ} {x : Ω → (Fin P → ℂ)} {xs : Fin nn → Ω → (Fin P → ℂ)} {B : ℝ}

/-- **Book §1.6.3.**

The summands `Sₖ = n⁻¹(xₖxₖ* − A)` of §1.6.3. Implicit source declaration
(the display defining `Z = Y − A = Σ Sₖ`). -/
noncomputable def sampleCovSummand (μ : MeasureTheory.Measure Ω)
    (x : Ω → (Fin P → ℂ)) (nn : ℕ) (xs : Fin nn → Ω → (Fin P → ℂ)) (k : Fin nn)
    (ω : Ω) : Matrix (Fin P) (Fin P) ℂ :=
  (nn : ℝ)⁻¹ • (vecMulVec (xs k ω) (star (xs k ω)) - covarianceMatrix μ x)

/-- **Book §1.6.3.**

§1.6.3 setup: the decomposition `Y − A = Σₖ Sₖ`. Implicit source claim. -/
lemma sampleCov_decomposition (hnn : nn ≠ 0) (ω : Ω) :
    sampleCovariance μ nn xs ω - covarianceMatrix μ x =
      ∑ k, sampleCovSummand μ x nn xs k ω := by
  rw [sampleCovariance]
  rw [show (∑ k, sampleCovSummand μ x nn xs k ω) =
    (nn : ℝ)⁻¹ • ∑ k, (vecMulVec (xs k ω) (star (xs k ω)) - covarianceMatrix μ x) from
    (Finset.smul_sum).symm]
  rw [Finset.sum_sub_distrib, smul_sub]
  congr 1
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul (R := ℝ), smul_smul,
    show ((nn : ℝ)⁻¹ * (nn : ℝ)) = 1 from by field_simp, one_smul]

/-- **Book §1.6.3.**

§1.6.3 setup: the summands are centered, `𝔼Sₖ = 0`. Implicit source claim
("independent, identically distributed, and centered"). -/
lemma sampleCov_summand_centered
    (hid : ∀ k, ProbabilityTheory.IdentDistrib (xs k) x μ μ)
    (hxs : ∀ k, MIntegrable (fun ω => vecMulVec (xs k ω) (star (xs k ω))) μ)
    (k : Fin nn) : expectation μ (sampleCovSummand μ x nn xs k) = 0 := by
  rw [show sampleCovSummand μ x nn xs k = fun ω => (nn : ℝ)⁻¹ •
    (vecMulVec (xs k ω) (star (xs k ω)) - covarianceMatrix μ x) from rfl]
  rw [expectation_smul_real, expectation_sub (hxs k) (MIntegrable.const _),
    expectation_const, expectation_vecMulVec_of_identDistrib (hid k)]
  rw [show expectation μ (fun ω => vecMulVec (x ω) (star (x ω))) =
    covarianceMatrix μ x from rfl]
  rw [sub_self, smul_zero]

/-- **Book §1.6.3, first display** (p. 9): the uniform bound
`‖Sₖ‖ = n⁻¹‖xₖxₖ* − A‖ ≤ n⁻¹(‖xₖxₖ*‖ + ‖A‖) ≤ 2B/n` — "The first relation is the
triangle inequality. The second follows from the assumption that `x` is bounded and
the observation [`‖A‖ ≤ B`]." Intermediate claim, fully proved. -/
theorem sampleCov_summand_norm_le (hx : Measurable x)
    (hB : ∀ᵐ ω ∂μ, l2norm (x ω) ^ 2 ≤ B)
    (hBs : ∀ k, ∀ᵐ ω ∂μ, l2norm (xs k ω) ^ 2 ≤ B) (k : Fin nn) :
    ∀ᵐ ω ∂μ, ‖sampleCovSummand μ x nn xs k ω‖ ≤ 2 * B / nn := by
  have hA := norm_covarianceMatrix_le hx hB
  filter_upwards [hBs k] with ω hω
  rw [sampleCovSummand, norm_smul]
  have h1 : ‖vecMulVec (xs k ω) (star (xs k ω)) - covarianceMatrix μ x‖ ≤ 2 * B := by
    calc ‖vecMulVec (xs k ω) (star (xs k ω)) - covarianceMatrix μ x‖
        ≤ ‖vecMulVec (xs k ω) (star (xs k ω))‖ + ‖covarianceMatrix μ x‖ :=
          norm_sub_le _ _
      _ ≤ B + B := by
          refine add_le_add ?_ hA
          rw [l2_opNorm_vecMulVec_star_self]
          exact hω
      _ = 2 * B := by ring
  calc ‖(nn : ℝ)⁻¹‖ * ‖vecMulVec (xs k ω) (star (xs k ω)) - covarianceMatrix μ x‖
      ≤ ‖(nn : ℝ)⁻¹‖ * (2 * B) := by
        refine mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = 2 * B / nn := by
        rw [Real.norm_of_nonneg (by positivity)]
        ring

/-- Lean implementation helper: the Loewner order is compatible with nonnegative real
scaling. -/
lemma loewner_smul_le {M N : Matrix n n ℂ} {c : ℝ} (hc : 0 ≤ c) (h : M ≤ N) :
    c • M ≤ c • N := by
  rw [Matrix.le_iff] at h ⊢
  rw [← smul_sub]
  exact posSemidef_smul_nonneg h hc

/-- Lean implementation helper: matrix multiplication of measurable random matrices is
measurable. -/
lemma measurable_matrix_mul {l m' p' : Type*} [Fintype l] [Fintype m'] [Fintype p']
    [DecidableEq l] [DecidableEq m'] [DecidableEq p']
    {f : Ω → Matrix l m' ℂ} {g : Ω → Matrix m' p' ℂ}
    (hf : Measurable f) (hg : Measurable g) : Measurable fun ω => f ω * g ω := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  have h1 : (fun ω => (f ω * g ω) i j) = fun ω => ∑ k, f ω i k * g ω k j :=
    funext fun ω => Matrix.mul_apply
  rw [h1]
  exact Finset.measurable_sum _ fun k _ =>
    ((measurable_entry i k).comp hf).mul ((measurable_entry k j).comp hg)

/-- Lean implementation helper: real smul preserves Hermitianness. -/
lemma isHermitian_smul_real {M : Matrix n n ℂ} (hM : M.IsHermitian) (α : ℝ) :
    ((α : ℝ) • M).IsHermitian := by
  show ((α : ℝ) • M)ᴴ = (α : ℝ) • M
  ext i j
  show (starRingEnd ℂ) (α • M j i) = α • M i j
  rw [show (starRingEnd ℂ) (α • M j i) = α • (starRingEnd ℂ) (M j i) from by
    simp [Complex.real_smul]]
  congr 1
  calc (starRingEnd ℂ) (M j i) = Mᴴ i j := rfl
    _ = M i j := by rw [hM]

/-- Lean implementation helper: `MIntegrable` is closed under real smul. -/
lemma MIntegrable.smul_real {m' n' : Type*} [Fintype m'] [Fintype n'] [DecidableEq m']
    [DecidableEq n'] {Z : Ω → Matrix m' n' ℂ} (hZ : MIntegrable Z μ) (α : ℝ) :
    MIntegrable (fun ω => α • Z ω) μ := fun i j => by
  have h1 : (fun ω => (α • Z ω) i j) = fun ω => α • (Z ω i j) := rfl
  rw [h1]
  exact (hZ i j).smul α

/-- Lean implementation helper: the matrix-valued variance of a centered random matrix
is the expectation of its square (square version of `matrixVar1_of_centered`). -/
lemma matrixVar_of_centered {Y : Ω → Matrix n n ℂ} (hcent : expectation μ Y = 0) :
    matrixVar μ Y = expectation μ (fun ω => Y ω * Y ω) := by
  rw [matrixVar, hcent]
  simp only [sub_zero]

/-- Lean implementation helper: the rank-one square identity
`(xx*)(xx*) = ‖x‖²·(xx*)` used in the §1.6.3 display. -/
lemma vecMulVec_star_sq (v : Fin P → ℂ) :
    vecMulVec v (star v) * vecMulVec v (star v) =
      (l2norm v ^ 2 : ℝ) • vecMulVec v (star v) := by
  rw [Matrix.vecMulVec_mul_vecMulVec]
  have h1 : (star v ⬝ᵥ v) • (star v) = ((l2norm v ^ 2 : ℝ) : ℂ) • star v := by
    rw [dotProduct_star_self_eq]
  rw [h1, Matrix.vecMulVec_smul]
  ext i j
  show ((l2norm v ^ 2 : ℝ) : ℂ) • vecMulVec v (star v) i j =
    (l2norm v ^ 2 : ℝ) • vecMulVec v (star v) i j
  simp [Complex.real_smul]

/-- **Book §1.6.3, second display** (p. 9, the chain computing `𝔼Sₖ²`): the summand
variance bound `𝔼Sₖ² ≼ (B/n²)·A`. The Lean proof follows the source's chain: expand
the square, use `(xx*)² = ‖x‖²·xx*`, compare `‖x‖² ≤ B` in the semidefinite order
("expectation preserves the semidefinite order"), and drop the negative-semidefinite
term `−A²`. Intermediate claim, fully proved. -/
theorem sampleCov_summand_sq_le (hx : Measurable x)
    (hxs_meas : ∀ k, Measurable (xs k)) (hB0 : 0 ≤ B)
    (hB : ∀ᵐ ω ∂μ, l2norm (x ω) ^ 2 ≤ B)
    (hBs : ∀ k, ∀ᵐ ω ∂μ, l2norm (xs k ω) ^ 2 ≤ B)
    (hid : ∀ k, ProbabilityTheory.IdentDistrib (xs k) x μ μ) (k : Fin nn) :
    expectation μ (fun ω =>
        sampleCovSummand μ x nn xs k ω * sampleCovSummand μ x nn xs k ω) ≤
      (B / (nn : ℝ) ^ 2) • covarianceMatrix μ x := by
  have hMint : MIntegrable (fun ω => vecMulVec (xs k ω) (star (xs k ω))) μ :=
    mintegrable_vecMulVec_of_bound (hxs_meas k) (hBs k)
  have hEM : expectation μ (fun ω => vecMulVec (xs k ω) (star (xs k ω))) =
      covarianceMatrix μ x := expectation_vecMulVec_of_identDistrib (hid k)
  have hMM_eq : ∀ ω, vecMulVec (xs k ω) (star (xs k ω)) *
      vecMulVec (xs k ω) (star (xs k ω)) =
      (l2norm (xs k ω) ^ 2 : ℝ) • vecMulVec (xs k ω) (star (xs k ω)) :=
    fun ω => vecMulVec_star_sq (xs k ω)
  have hMMint : MIntegrable (fun ω => vecMulVec (xs k ω) (star (xs k ω)) *
      vecMulVec (xs k ω) (star (xs k ω))) μ := by
    refine MIntegrable.of_bound
      (measurable_matrix_mul (measurable_vecMulVec_star (hxs_meas k))
        (measurable_vecMulVec_star (hxs_meas k))) (B * B) ?_
    filter_upwards [hBs k] with ω hω
    intro i j
    rw [hMM_eq ω]
    have h2 : ‖((l2norm (xs k ω) ^ 2 : ℝ) •
        vecMulVec (xs k ω) (star (xs k ω))) i j‖ =
        (l2norm (xs k ω) ^ 2) * ‖vecMulVec (xs k ω) (star (xs k ω)) i j‖ := by
      show ‖(l2norm (xs k ω) ^ 2 : ℝ) • vecMulVec (xs k ω) (star (xs k ω)) i j‖ = _
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    rw [h2]
    have h3 := abs_entry_vecMulVec_le (xs k ω) i j
    have h4 := l2norm_nonneg (xs k ω)
    nlinarith [norm_nonneg (vecMulVec (xs k ω) (star (xs k ω)) i j)]
  -- 𝔼(M·M) ≼ B•A
  have hEMM_le : expectation μ (fun ω => vecMulVec (xs k ω) (star (xs k ω)) *
      vecMulVec (xs k ω) (star (xs k ω))) ≤ B • covarianceMatrix μ x := by
    have h5 : expectation μ (fun ω => B • vecMulVec (xs k ω) (star (xs k ω))) =
        B • covarianceMatrix μ x := by
      rw [expectation_smul_real, hEM]
    rw [← h5]
    refine expectation_loewner_mono hMMint (hMint.smul_real B) ?_
    filter_upwards [hBs k] with ω hω
    rw [hMM_eq ω, Matrix.le_iff, ← sub_smul]
    exact posSemidef_smul_nonneg (posSemidef_vecMulVec_star (xs k ω)) (by linarith)
  -- 𝔼((M−A)²) = 𝔼(M·M) − A² via `matrixVar_eq_sub`
  have hvar : expectation μ (fun ω =>
      (vecMulVec (xs k ω) (star (xs k ω)) - covarianceMatrix μ x) *
      (vecMulVec (xs k ω) (star (xs k ω)) - covarianceMatrix μ x)) =
      expectation μ (fun ω => vecMulVec (xs k ω) (star (xs k ω)) *
        vecMulVec (xs k ω) (star (xs k ω))) -
      covarianceMatrix μ x * covarianceMatrix μ x := by
    have h6 := matrixVar_eq_sub hMint hMMint
    rw [matrixVar, hEM] at h6
    exact h6
  -- the psd matrix A²
  have hA2 : (0 : Matrix (Fin P) (Fin P) ℂ) ≤
      covarianceMatrix μ x * covarianceMatrix μ x := by
    rw [Matrix.nonneg_iff_posSemidef]
    exact posSemidef_sq (posSemidef_covarianceMatrix
      (mintegrable_vecMulVec_of_bound hx hB)).1
  -- assemble
  have hsummand : (fun ω => sampleCovSummand μ x nn xs k ω *
      sampleCovSummand μ x nn xs k ω) = fun ω => ((nn : ℝ)⁻¹ * (nn : ℝ)⁻¹) •
      ((vecMulVec (xs k ω) (star (xs k ω)) - covarianceMatrix μ x) *
       (vecMulVec (xs k ω) (star (xs k ω)) - covarianceMatrix μ x)) := by
    funext ω
    rw [sampleCovSummand, smul_mul_smul_comm]
  rw [hsummand, expectation_smul_real, hvar]
  calc ((nn : ℝ)⁻¹ * (nn : ℝ)⁻¹) •
      (expectation μ (fun ω => vecMulVec (xs k ω) (star (xs k ω)) *
        vecMulVec (xs k ω) (star (xs k ω))) -
        covarianceMatrix μ x * covarianceMatrix μ x)
      ≤ ((nn : ℝ)⁻¹ * (nn : ℝ)⁻¹) • (B • covarianceMatrix μ x -
          covarianceMatrix μ x * covarianceMatrix μ x) := by
        refine loewner_smul_le (by positivity) ?_
        exact sub_le_sub_right hEMM_le _
    _ ≤ ((nn : ℝ)⁻¹ * (nn : ℝ)⁻¹) • (B • covarianceMatrix μ x) := by
        refine loewner_smul_le (by positivity) ?_
        exact sub_le_self _ hA2
    _ = (B / (nn : ℝ) ^ 2) • covarianceMatrix μ x := by
        rw [smul_smul]
        congr 1
        ring

/-- **Book §1.6.3, third display** (pp. 10–11): summing the relation over `k`,
`0 ≼ Σₖ𝔼Sₖ² ≼ (B/n)·A` — "The matrix is positive-semidefinite because it is a sum of
squares of Hermitian matrices." Intermediate claim, fully proved. -/
theorem sampleCov_sum_sq_le (hx : Measurable x)
    (hxs_meas : ∀ k, Measurable (xs k)) (hB0 : 0 ≤ B)
    (hB : ∀ᵐ ω ∂μ, l2norm (x ω) ^ 2 ≤ B)
    (hBs : ∀ k, ∀ᵐ ω ∂μ, l2norm (xs k ω) ^ 2 ≤ B)
    (hid : ∀ k, ProbabilityTheory.IdentDistrib (xs k) x μ μ)
    (hxs_int : ∀ k, MIntegrable (fun ω =>
      sampleCovSummand μ x nn xs k ω * sampleCovSummand μ x nn xs k ω) μ) :
    (0 : Matrix (Fin P) (Fin P) ℂ) ≤
      (∑ k, expectation μ (fun ω =>
        sampleCovSummand μ x nn xs k ω * sampleCovSummand μ x nn xs k ω)) ∧
    (∑ k, expectation μ (fun ω =>
        sampleCovSummand μ x nn xs k ω * sampleCovSummand μ x nn xs k ω)) ≤
      (B / (nn : ℝ)) • covarianceMatrix μ x := by
  constructor
  · rw [Matrix.nonneg_iff_posSemidef]
    refine Matrix.posSemidef_sum _ fun k _ => ?_
    refine posSemidef_expectation (hxs_int k) ?_
    refine Filter.Eventually.of_forall fun ω => ?_
    refine posSemidef_sq ?_
    exact isHermitian_smul_real
      (((posSemidef_vecMulVec_star (xs k ω)).1).sub
        (posSemidef_covarianceMatrix (mintegrable_vecMulVec_of_bound hx hB)).1) _
  · calc (∑ k, expectation μ (fun ω =>
        sampleCovSummand μ x nn xs k ω * sampleCovSummand μ x nn xs k ω))
        ≤ ∑ _k : Fin nn, (B / (nn : ℝ) ^ 2) • covarianceMatrix μ x :=
          Finset.sum_le_sum fun k _ =>
            sampleCov_summand_sq_le hx hxs_meas hB0 hB hBs hid k
      _ = (B / (nn : ℝ)) • covarianceMatrix μ x := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            ← Nat.cast_smul_eq_nsmul (R := ℝ), smul_smul]
          congr 1
          rcases Nat.eq_zero_or_pos nn with h | h
          · subst h
            norm_num
          · have hnn : (nn : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h.ne'
            field_simp

/-- **Book §1.6.3, final display** (p. 11): "Extract the spectral norm to arrive at
`v(Z) = ‖Σₖ𝔼Sₖ²‖ ≤ B‖A‖/n`" — using the implicit norm-monotonicity on the psd cone
(`norm_le_norm_of_loewner_le`). Intermediate claim, fully proved. -/
theorem sampleCov_norm_sum_sq_le (hx : Measurable x)
    (hxs_meas : ∀ k, Measurable (xs k)) (hB0 : 0 ≤ B)
    (hB : ∀ᵐ ω ∂μ, l2norm (x ω) ^ 2 ≤ B)
    (hBs : ∀ k, ∀ᵐ ω ∂μ, l2norm (xs k ω) ^ 2 ≤ B)
    (hid : ∀ k, ProbabilityTheory.IdentDistrib (xs k) x μ μ)
    (hxs_int : ∀ k, MIntegrable (fun ω =>
      sampleCovSummand μ x nn xs k ω * sampleCovSummand μ x nn xs k ω) μ) :
    ‖∑ k, expectation μ (fun ω =>
        sampleCovSummand μ x nn xs k ω * sampleCovSummand μ x nn xs k ω)‖ ≤
      B * ‖covarianceMatrix μ x‖ / nn := by
  obtain ⟨h0, hle⟩ := sampleCov_sum_sq_le hx hxs_meas hB0 hB hBs hid hxs_int
  have h1 : ‖∑ k, expectation μ (fun ω =>
      sampleCovSummand μ x nn xs k ω * sampleCovSummand μ x nn xs k ω)‖ ≤
      ‖(B / (nn : ℝ)) • covarianceMatrix μ x‖ := by
    refine norm_le_norm_of_loewner_le ?_ hle
    rwa [← Matrix.nonneg_iff_posSemidef]
  calc ‖∑ k, expectation μ (fun ω =>
      sampleCovSummand μ x nn xs k ω * sampleCovSummand μ x nn xs k ω)‖
      ≤ ‖(B / (nn : ℝ)) • covarianceMatrix μ x‖ := h1
    _ = B * ‖covarianceMatrix μ x‖ / nn := by
        rw [norm_smul, Real.norm_of_nonneg (by positivity)]
        ring

end Analysis

end MatrixConcentration

set_option linter.unusedSectionVars false

/-!
# Sample covariance error bounds (Book §1.6.3)

* `sampleCov_indep_summands` and `sampleCov_varStat_eq` identify the independent
  centered summands and their variance statistic;
* `sampleCovariance_expected_error` proves the expected-error display;
* `sampleCovariance_relative_error` proves the sample-complexity consequence.

The relative-error theorem makes the positivity of the covariance norm
explicit, as recorded in its Author note.
-/

namespace MatrixConcentration

open Matrix MeasureTheory ProbabilityTheory Finset
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
variable [MeasureTheory.IsProbabilityMeasure μ]
variable {P nn : ℕ} {x : Ω → (Fin P → ℂ)} {xs : Fin nn → Ω → (Fin P → ℂ)} {B : ℝ}

/-- Lean implementation helper: the summand map is measurable as a function of the
sample. -/
lemma measurable_sampleCovSummand_map :
    Measurable fun v : Fin P → ℂ =>
      (nn : ℝ)⁻¹ • (vecMulVec v (star v) - covarianceMatrix μ x) := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  have h1 : (fun v : Fin P → ℂ =>
      ((nn : ℝ)⁻¹ • (vecMulVec v (star v) - covarianceMatrix μ x)) i j) =
      fun v : Fin P → ℂ =>
        (((nn : ℝ)⁻¹ : ℝ) : ℂ) *
          (v i * (starRingEnd ℂ) (v j) - covarianceMatrix μ x i j) := by
    funext v
    show (nn : ℝ)⁻¹ • ((vecMulVec v (star v) - covarianceMatrix μ x) i j) = _
    rw [Complex.real_smul]
    rfl
  rw [h1]
  have hi : Measurable fun v : Fin P → ℂ => v i := measurable_pi_apply i
  have hj : Measurable fun v : Fin P → ℂ => (starRingEnd ℂ) (v j) :=
    RCLike.continuous_conj.measurable.comp (measurable_pi_apply j)
  exact ((hi.mul hj).sub_const _).const_mul _

/-- **Book §1.6.3.**

§1.6.3 setup: "The random matrices `Sₖ` are independent" (inherited from the
independence of the samples). Implicit source claim. -/
lemma sampleCov_indep_summands (hxs_ind : ProbabilityTheory.iIndepFun xs μ) :
    ProbabilityTheory.iIndepFun (sampleCovSummand μ x nn xs) μ :=
  hxs_ind.comp _ fun _ => measurable_sampleCovSummand_map

/-- Lean implementation helper: measurability of each summand. -/
lemma measurable_sampleCovSummand (hxs_meas : ∀ k, Measurable (xs k)) (k : Fin nn) :
    Measurable (sampleCovSummand μ x nn xs k) :=
  measurable_sampleCovSummand_map.comp (hxs_meas k)

/-- Lean implementation helper: each summand is Hermitian. -/
lemma isHermitian_sampleCovSummand
    (hxx : MIntegrable (fun ω => vecMulVec (x ω) (star (x ω))) μ) (k : Fin nn) (ω : Ω) :
    (sampleCovSummand μ x nn xs k ω).IsHermitian :=
  isHermitian_smul_real
    (((posSemidef_vecMulVec_star (xs k ω)).1).sub
      (posSemidef_covarianceMatrix hxx).1) _

/-- Lean implementation helper: integrability of each summand. -/
lemma mintegrable_sampleCovSummand (hxs_meas : ∀ k, Measurable (xs k))
    (hBs : ∀ k, ∀ᵐ ω ∂μ, l2norm (xs k ω) ^ 2 ≤ B) (k : Fin nn) :
    MIntegrable (sampleCovSummand μ x nn xs k) μ := by
  have h1 := mintegrable_vecMulVec_of_bound (hxs_meas k) (hBs k)
  exact (h1.sub (MIntegrable.const _)).smul_real _

/-- **Book §1.6.3.**

§1.6.3, p. 10–11: "The matrix `Z` is Hermitian, so the two squares in this formula
coincide: `v(Z) = ‖𝔼Z²‖ = ‖Σₖ𝔼Sₖ²‖`." The matrix variance statistic of the deviation
`Z = Σₖ Sₖ` equals the quantity bounded in `sampleCov_norm_sum_sq_le`. Implicit source
claim, fully proved (via `matrixVar_sum` and centering). -/
theorem sampleCov_varStat_eq (hx : Measurable x)
    (hxs_meas : ∀ k, Measurable (xs k))
    (hB : ∀ᵐ ω ∂μ, l2norm (x ω) ^ 2 ≤ B)
    (hBs : ∀ k, ∀ᵐ ω ∂μ, l2norm (xs k ω) ^ 2 ≤ B)
    (hid : ∀ k, ProbabilityTheory.IdentDistrib (xs k) x μ μ)
    (hxs_ind : ProbabilityTheory.iIndepFun xs μ)
    (hxs_int : ∀ k, MIntegrable (fun ω =>
      sampleCovSummand μ x nn xs k ω * sampleCovSummand μ x nn xs k ω) μ) :
    varStatHerm μ (fun ω => ∑ k, sampleCovSummand μ x nn xs k ω) =
      ‖∑ k, expectation μ (fun ω =>
        sampleCovSummand μ x nn xs k ω * sampleCovSummand μ x nn xs k ω)‖ := by
  have hcent : ∀ k, expectation μ (sampleCovSummand μ x nn xs k) = 0 := fun k =>
    sampleCov_summand_centered hid (fun j => mintegrable_vecMulVec_of_bound
      (hxs_meas j) (hBs j)) k
  show ‖matrixVar μ (fun ω => ∑ k, sampleCovSummand μ x nn xs k ω)‖ = _
  rw [matrixVar_sum (sampleCov_indep_summands hxs_ind)
    (measurable_sampleCovSummand hxs_meas)
    (mintegrable_sampleCovSummand hxs_meas hBs) hxs_int]
  congr 1
  exact Finset.sum_congr rfl fun k _ => matrixVar_of_centered (hcent k)

section Conditional

/-- **Book §1.6.3, expected-error display.** The bound for the sample
covariance estimator,
`𝔼‖Y − A‖ ≤ √(2B‖A‖ log(2p)/n) + 2B log(2p)/(3n)`.
This is the intermediate display used for the relative-error conclusion. -/
theorem sampleCovariance_expected_error (hP : 0 < P) (hnn : nn ≠ 0)
    (hx : Measurable x) (hxs_meas : ∀ k, Measurable (xs k)) (hB0 : 0 ≤ B)
    (hB : ∀ᵐ ω ∂μ, l2norm (x ω) ^ 2 ≤ B)
    (hBs : ∀ k, ∀ᵐ ω ∂μ, l2norm (xs k ω) ^ 2 ≤ B)
    (hid : ∀ k, ProbabilityTheory.IdentDistrib (xs k) x μ μ)
    (hxs_ind : ProbabilityTheory.iIndepFun xs μ)
    (hxs_int : ∀ k, MIntegrable (fun ω =>
      sampleCovSummand μ x nn xs k ω * sampleCovSummand μ x nn xs k ω) μ) :
    ∫ ω, ‖sampleCovariance μ nn xs ω - covarianceMatrix μ x‖ ∂μ ≤
      Real.sqrt (2 * (B * ‖covarianceMatrix μ x‖) * Real.log (2 * P) / nn) +
        2 * B * Real.log (2 * P) / (3 * nn) := by
  have hxx := mintegrable_vecMulVec_of_bound hx hB
  have hHermS : ∀ k ω, (sampleCovSummand μ x nn xs k ω).IsHermitian := fun k ω =>
    isHermitian_sampleCovSummand hxx k ω
  -- the summand-square integrabilities in the two conjugate-transpose forms
  have hS1 : ∀ k, MIntegrable (fun ω => sampleCovSummand μ x nn xs k ω *
      (sampleCovSummand μ x nn xs k ω)ᴴ) μ := fun k => by
    have h1 : (fun ω => sampleCovSummand μ x nn xs k ω *
        (sampleCovSummand μ x nn xs k ω)ᴴ) =
        fun ω => sampleCovSummand μ x nn xs k ω * sampleCovSummand μ x nn xs k ω := by
      funext ω
      rw [hHermS k ω]
    rw [h1]
    exact hxs_int k
  have hS2 : ∀ k, MIntegrable (fun ω => (sampleCovSummand μ x nn xs k ω)ᴴ *
      sampleCovSummand μ x nn xs k ω) μ := fun k => by
    have h1 : (fun ω => (sampleCovSummand μ x nn xs k ω)ᴴ *
        sampleCovSummand μ x nn xs k ω) =
        fun ω => sampleCovSummand μ x nn xs k ω * sampleCovSummand μ x nn xs k ω := by
      funext ω
      rw [hHermS k ω]
    rw [h1]
    exact hxs_int k
  have hcent : ∀ k, expectation μ (sampleCovSummand μ x nn xs k) = 0 := fun k =>
    sampleCov_summand_centered hid (fun j => mintegrable_vecMulVec_of_bound
      (hxs_meas j) (hBs j)) k
  -- apply the matrix Bernstein expectation bound (Theorem 1.6.2, proved via
  -- Chapter 6) with L = 2B/n
  have hbern := matrix_bernstein_expectation (μ := μ) (d₁ := P) (d₂ := P)
    (by omega) (sampleCov_indep_summands hxs_ind)
    (measurable_sampleCovSummand hxs_meas) hcent
    (fun k => sampleCov_summand_norm_le hx hB hBs k)
    (by positivity)
  -- identify the integrand with ‖Y − A‖
  have hdecomp : (∫ ω, ‖∑ k, sampleCovSummand μ x nn xs k ω‖ ∂μ) =
      ∫ ω, ‖sampleCovariance μ nn xs ω - covarianceMatrix μ x‖ ∂μ := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    show ‖∑ k, sampleCovSummand μ x nn xs k ω‖ =
      ‖sampleCovariance μ nn xs ω - covarianceMatrix μ x‖
    rw [sampleCov_decomposition hnn ω]
  -- identify and bound the variance statistic
  set V := max ‖expectation μ (fun ω => (∑ k, sampleCovSummand μ x nn xs k ω) *
      (∑ k, sampleCovSummand μ x nn xs k ω)ᴴ)‖
    ‖expectation μ (fun ω => (∑ k, sampleCovSummand μ x nn xs k ω)ᴴ *
      (∑ k, sampleCovSummand μ x nn xs k ω))‖ with hVdef
  have hVbound : V ≤ B * ‖covarianceMatrix μ x‖ / nn := by
    have h2 := matrix_bernstein_variance_eq (sampleCov_indep_summands hxs_ind)
      (measurable_sampleCovSummand hxs_meas)
      (mintegrable_sampleCovSummand hxs_meas hBs) hS1 hS2 hcent
    rw [hVdef, h2]
    have h3 : (∑ k, expectation μ (fun ω => sampleCovSummand μ x nn xs k ω *
        (sampleCovSummand μ x nn xs k ω)ᴴ)) =
        ∑ k, expectation μ (fun ω => sampleCovSummand μ x nn xs k ω *
          sampleCovSummand μ x nn xs k ω) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      congr 1
      funext ω
      rw [hHermS k ω]
    have h4 : (∑ k, expectation μ (fun ω => (sampleCovSummand μ x nn xs k ω)ᴴ *
        sampleCovSummand μ x nn xs k ω)) =
        ∑ k, expectation μ (fun ω => sampleCovSummand μ x nn xs k ω *
          sampleCovSummand μ x nn xs k ω) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      congr 1
      funext ω
      rw [hHermS k ω]
    rw [h3, h4, max_self]
    exact sampleCov_norm_sum_sq_le hx hxs_meas hB0 hB hBs hid hxs_int
  -- assemble, using monotonicity of the right-hand side in the variance statistic
  rw [hdecomp] at hbern
  have hlog0 : 0 ≤ Real.log ((P : ℝ) + P) := by
    refine Real.log_nonneg ?_
    have : (1 : ℝ) ≤ P := by exact_mod_cast hP
    linarith
  have hVnn : 0 ≤ V := le_max_of_le_left (norm_nonneg _)
  calc ∫ ω, ‖sampleCovariance μ nn xs ω - covarianceMatrix μ x‖ ∂μ
      ≤ Real.sqrt (2 * V * Real.log ((P : ℝ) + P)) +
        1 / 3 * (2 * B / nn) * Real.log ((P : ℝ) + P) := hbern
    _ ≤ Real.sqrt (2 * (B * ‖covarianceMatrix μ x‖ / nn) * Real.log ((P : ℝ) + P)) +
        1 / 3 * (2 * B / nn) * Real.log ((P : ℝ) + P) := by
        have h5 : 2 * V * Real.log ((P : ℝ) + P) ≤
            2 * (B * ‖covarianceMatrix μ x‖ / nn) * Real.log ((P : ℝ) + P) := by
          nlinarith
        exact add_le_add (Real.sqrt_le_sqrt h5) le_rfl
    _ = Real.sqrt (2 * (B * ‖covarianceMatrix μ x‖) * Real.log (2 * P) / nn) +
        2 * B * Real.log (2 * P) / (3 * nn) := by
        rw [show ((P : ℝ) + P) = 2 * P from by ring]
        congr 1
        · congr 1
          ring
        · ring

/-- **Book §1.6.3, sample-complexity display.** If we wish to obtain a relative
error on the order of ε, we may take `n ≥ 2B log(2p)/(ε²‖A‖)`. This selection yields
`𝔼‖Y − A‖ ≤ (ε + ε²)·‖A‖`.

Author note: Lean assumes `0 < ‖covarianceMatrix μ x‖`, which is needed to
divide by the covariance norm and is implicit in the book’s relative-error
discussion. -/
theorem sampleCovariance_relative_error (hP : 0 < P) (hnn : nn ≠ 0)
    (hx : Measurable x) (hxs_meas : ∀ k, Measurable (xs k)) (hB0 : 0 ≤ B)
    (hB : ∀ᵐ ω ∂μ, l2norm (x ω) ^ 2 ≤ B)
    (hBs : ∀ k, ∀ᵐ ω ∂μ, l2norm (xs k ω) ^ 2 ≤ B)
    (hid : ∀ k, ProbabilityTheory.IdentDistrib (xs k) x μ μ)
    (hxs_ind : ProbabilityTheory.iIndepFun xs μ)
    (hxs_int : ∀ k, MIntegrable (fun ω =>
      sampleCovSummand μ x nn xs k ω * sampleCovSummand μ x nn xs k ω) μ)
    {ε : ℝ} (hε : 0 < ε) (hA : 0 < ‖covarianceMatrix μ x‖)
    (hsamples : 2 * B * Real.log (2 * P) / (ε ^ 2 * ‖covarianceMatrix μ x‖) ≤ nn) :
    ∫ ω, ‖sampleCovariance μ nn xs ω - covarianceMatrix μ x‖ ∂μ ≤
      (ε + ε ^ 2) * ‖covarianceMatrix μ x‖ := by
  have hmain := sampleCovariance_expected_error hP hnn hx hxs_meas hB0 hB hBs hid
    hxs_ind hxs_int
  have hnn' : (0 : ℝ) < nn := by
    have : 0 < nn := Nat.pos_of_ne_zero hnn
    exact_mod_cast this
  have hlog0 : 0 ≤ Real.log (2 * P) := by
    refine Real.log_nonneg ?_
    have : (1 : ℝ) ≤ P := by exact_mod_cast hP
    linarith
  -- from the sample-count hypothesis: 2B log(2p)/n ≤ ε²‖A‖
  have hkey : 2 * B * Real.log (2 * P) / nn ≤ ε ^ 2 * ‖covarianceMatrix μ x‖ := by
    rw [div_le_iff₀ hnn']
    have h1 := (div_le_iff₀ (by positivity : (0:ℝ) < ε ^ 2 * ‖covarianceMatrix μ x‖)).mp hsamples
    nlinarith
  -- first term: √(2B‖A‖ log(2p)/n) ≤ ε‖A‖
  have hterm1 : Real.sqrt (2 * (B * ‖covarianceMatrix μ x‖) * Real.log (2 * P) / nn) ≤
      ε * ‖covarianceMatrix μ x‖ := by
    have h2 : 2 * (B * ‖covarianceMatrix μ x‖) * Real.log (2 * P) / nn ≤
        (ε * ‖covarianceMatrix μ x‖) ^ 2 := by
      have h3 : 2 * (B * ‖covarianceMatrix μ x‖) * Real.log (2 * P) / nn =
          (2 * B * Real.log (2 * P) / nn) * ‖covarianceMatrix μ x‖ := by ring
      rw [h3]
      calc (2 * B * Real.log (2 * P) / nn) * ‖covarianceMatrix μ x‖
          ≤ (ε ^ 2 * ‖covarianceMatrix μ x‖) * ‖covarianceMatrix μ x‖ := by
            exact mul_le_mul_of_nonneg_right hkey hA.le
        _ = (ε * ‖covarianceMatrix μ x‖) ^ 2 := by ring
    calc Real.sqrt (2 * (B * ‖covarianceMatrix μ x‖) * Real.log (2 * P) / nn)
        ≤ Real.sqrt ((ε * ‖covarianceMatrix μ x‖) ^ 2) := Real.sqrt_le_sqrt h2
      _ = ε * ‖covarianceMatrix μ x‖ := Real.sqrt_sq (by positivity)
  -- second term: 2B log(2p)/(3n) ≤ ε²‖A‖/3 ≤ ε²‖A‖
  have hterm2 : 2 * B * Real.log (2 * P) / (3 * nn) ≤ ε ^ 2 * ‖covarianceMatrix μ x‖ := by
    have h4 : 2 * B * Real.log (2 * P) / (3 * nn) =
        (2 * B * Real.log (2 * P) / nn) / 3 := by ring
    rw [h4]
    nlinarith
  calc ∫ ω, ‖sampleCovariance μ nn xs ω - covarianceMatrix μ x‖ ∂μ
      ≤ Real.sqrt (2 * (B * ‖covarianceMatrix μ x‖) * Real.log (2 * P) / nn) +
        2 * B * Real.log (2 * P) / (3 * nn) := hmain
    _ ≤ ε * ‖covarianceMatrix μ x‖ + ε ^ 2 * ‖covarianceMatrix μ x‖ := by
        exact add_le_add hterm1 hterm2
    _ = (ε + ε ^ 2) * ‖covarianceMatrix μ x‖ := by ring

end Conditional

end MatrixConcentration
