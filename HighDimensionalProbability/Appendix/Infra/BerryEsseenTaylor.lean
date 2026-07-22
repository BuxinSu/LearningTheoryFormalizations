import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Quantitative Taylor bounds for Berry--Esseen

This file collects the pointwise complex-exponential and characteristic-function
remainders used by the quantitative central-limit argument.
-/

open MeasureTheory ProbabilityTheory Real Complex

namespace HDP.Appendix

variable {μ : Measure ℝ} [IsFiniteMeasure μ]

/-- The third derivative of a characteristic function is bounded by the third
absolute moment.  The estimate is uniform in the Fourier variable. -/
lemma norm_iteratedDeriv_charFun_three_le (hμ : MemLp id 3 μ) (t : ℝ) :
    ‖iteratedDeriv 3 (charFun μ) t‖ ≤ ∫ x, |x| ^ 3 ∂μ := by
  rw [iteratedDeriv_charFun hμ]
  simp only [norm_mul, norm_pow, norm_I, one_pow, one_mul]
  refine MeasureTheory.norm_integral_le_of_norm_le hμ.integrable_norm_pow' ?_
  filter_upwards with x
  rw [norm_mul, Complex.norm_exp]
  simp

/-- Quantitative second-order Taylor expansion of a characteristic function.
The `1 / 6` is the exact integral-remainder constant. -/
lemma norm_charFun_sub_taylorWithinEval_two_le (hμ : MemLp id 3 μ) (t : ℝ) :
    ‖charFun μ t - taylorWithinEval (charFun μ) 2 Set.univ 0 t‖ ≤
      |t| ^ 3 / 6 * ∫ x, |x| ^ 3 ∂μ := by
  by_cases ht : t = 0
  · simp [ht]
  let M : ℝ := ∫ x, |x| ^ 3 ∂μ
  have hM : 0 ≤ M := integral_nonneg fun _ ↦ by positivity
  have hcont : ContDiff ℝ 3 (charFun μ) := contDiff_charFun hμ
  have hu : UniqueDiffOn ℝ (Set.uIcc 0 t) :=
    uniqueDiffOn_Icc (by simpa [Set.uIcc, ht] using (min_lt_max (a := (0 : ℝ)) (b := t)))
  have htaylor :
      taylorWithinEval (charFun μ) 2 (Set.uIcc 0 t) 0 t =
        taylorWithinEval (charFun μ) 2 Set.univ 0 t := by
    simp only [taylor_within_apply]
    apply Finset.sum_congr rfl
    intro k hk
    have hklt : k < 3 := Finset.mem_range.mp hk
    congr 1
    rw [iteratedDerivWithin_eq_iteratedDeriv hu
      ((hcont.of_le (by exact_mod_cast hklt.le)).contDiffAt) (by simp),
      iteratedDerivWithin_univ]
  have hrem := taylor_integral_remainder
    (f := charFun μ) (x := t) (x₀ := 0) (n := 2) hcont.contDiffOn
  rw [← htaylor, hrem]
  norm_num
  have hg : IntervalIntegrable (fun y : ℝ => ((t - y) ^ 2 / 2) * M) volume 0 t :=
    (by fun_prop : Continuous (fun y : ℝ => ((t - y) ^ 2 / 2) * M)).intervalIntegrable 0 t
  refine (intervalIntegral.norm_integral_le_abs_of_norm_le ?_ hg).trans ?_
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with y hy
    rw [norm_mul]
    have hcoeff : ‖((t : ℂ) - y) ^ 2 / 2‖ = (t - y) ^ 2 / 2 := by
      rw [← ofReal_sub, ← ofReal_pow, ← ofReal_ofNat, ← ofReal_div, norm_real,
        Real.norm_eq_abs, abs_of_nonneg]
      positivity
    rw [hcoeff]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [iteratedDerivWithin_eq_iteratedDeriv hu hcont.contDiffAt
        (Set.uIoc_subset_uIcc hy)]
    exact norm_iteratedDeriv_charFun_three_le hμ y
  · change
      |∫ y in (0 : ℝ)..t, ((t - y) ^ 2 / 2) * M| ≤ |t| ^ 3 / 6 * M
    rw [show (∫ y in (0 : ℝ)..t, ((t - y) ^ 2 / 2) * M) = t ^ 3 * M / 6 by
      rw [intervalIntegral.integral_comp_sub_left
        (f := fun z : ℝ => (z ^ 2 / 2) * M) t]
      simp only [sub_self, sub_zero]
      rw [intervalIntegral.integral_mul_const]
      simp only [div_eq_mul_inv]
      rw [intervalIntegral.integral_mul_const, integral_pow]
      ring]
    rw [abs_div, abs_mul, abs_pow, abs_of_nonneg hM]
    norm_num
    ring_nf
    exact le_rfl

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- The centered, variance-one form of the third-order characteristic-function
remainder. -/
lemma norm_charFun_map_sub_gaussianQuadratic_le [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : MemLp X 3 P) (hmean : ∫ ω, X ω ∂P = 0)
    (hsecond : ∫ ω, X ω ^ 2 ∂P = 1) (t : ℝ) :
    ‖charFun (P.map X) t - (1 - t ^ 2 / 2)‖ ≤
      |t| ^ 3 / 6 * ∫ ω, |X ω| ^ 3 ∂P := by
  have hXm : AEMeasurable X P := hX.aestronglyMeasurable.aemeasurable
  have hmap3 : MemLp id 3 (P.map X) := by
    rw [memLp_map_measure_iff aestronglyMeasurable_id hXm]
    simpa only [Function.id_comp] using hX
  have h := norm_charFun_sub_taylorWithinEval_two_le hmap3 t
  rw [taylorWithinEval_charFun_two_zero' hXm hmean hsecond] at h
  rw [integral_map hXm (by fun_prop)] at h
  simpa only [Function.comp_apply, id_eq] using h

end HDP.Appendix
