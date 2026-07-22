import HighDimensionalProbability.Chapter1_AnalysisAndProbabilityRefresher
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Independence.CharacteristicFunction

/-!
# Analytic infrastructure for the triangular-array Poisson limit

This file contains the source-neutral finite-product asymptotic used in the
proof of HDP Theorem 1.7.6.
-/

open Filter Topology
open scoped BigOperators

namespace HDP.Appendix

private lemma norm_log_one_add_sub_self_le_sq {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) :
    ‖Complex.log (1 + w) - w‖ ≤ ‖w‖ ^ 2 := by
  have hw1 : ‖w‖ < 1 := lt_of_le_of_lt hw (by norm_num)
  have hinv : (1 - ‖w‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (sub_pos.mpr hw1) (by norm_num : (0 : ℝ) < 2)]
    linarith
  calc
    ‖Complex.log (1 + w) - w‖
        ≤ ‖w‖ ^ 2 * (1 - ‖w‖)⁻¹ / 2 :=
      Complex.norm_log_one_add_sub_self_le hw1
    _ ≤ ‖w‖ ^ 2 := by
      have hs : 0 ≤ ‖w‖ ^ 2 := sq_nonneg _
      nlinarith

/-- A triangular-array finite-product asymptotic.  If all entries are
nonnegative, their maximum tends to zero, and their sum tends to `a`, then
`∏ᵢ (1 + pᵢ z)` tends to `exp (a z)`. -/
theorem tendsto_prod_one_add_of_max_sum
    (q : ∀ N : ℕ, Fin N → ℝ) (a : ℝ)
    (hq : ∀ N i, 0 ≤ q N i)
    (hmax : Tendsto (fun N => ⨆ i : Fin N, q N i) atTop (𝓝 0))
    (hsum : Tendsto (fun N => ∑ i : Fin N, q N i) atTop (𝓝 a))
    (z : ℂ) :
    Tendsto (fun N => ∏ i : Fin N, (1 + (q N i : ℂ) * z))
      atTop (𝓝 (Complex.exp ((a : ℂ) * z))) := by
  let M : ℕ → ℝ := fun N => ⨆ i : Fin N, q N i
  let A : ℕ → ℝ := fun N => ∑ i : Fin N, q N i
  let L : ℕ → ℂ :=
    fun N => ∑ i : Fin N, Complex.log (1 + (q N i : ℂ) * z)
  have hM : Tendsto M atTop (𝓝 0) := hmax
  have hA : Tendsto A atTop (𝓝 a) := hsum
  have hMA : Tendsto (fun N => M N * A N) atTop (𝓝 0) := by
    simpa using hM.mul hA
  have hMz : Tendsto (fun N => M N * ‖z‖) atTop (𝓝 0) := by
    simpa using hM.mul_const ‖z‖
  have hbound :
      ∀ᶠ N in atTop, 1 ≤ N ∧ M N * ‖z‖ < 1 / 2 := by
    filter_upwards [
      eventually_ge_atTop 1,
      hMz.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
    ] with N hN hzN
    simpa using And.intro hN hzN
  have herror_bound :
      ∀ᶠ N in atTop,
        ‖L N - (A N : ℂ) * z‖ ≤ ‖z‖ ^ 2 * (M N * A N) := by
    filter_upwards [hbound] with N hN
    rcases hN with ⟨hNpos, hsmall⟩
    have hnonempty : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hNpos
    have hqi_le (i : Fin N) : q N i ≤ M N := by
      exact Finite.le_ciSup (q N) i
    have hwi (i : Fin N) : ‖(q N i : ℂ) * z‖ ≤ 1 / 2 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hq N i)]
      exact (mul_le_mul_of_nonneg_right (hqi_le i) (norm_nonneg z)).trans hsmall.le
    have hlog (i : Fin N) :
        ‖Complex.log (1 + (q N i : ℂ) * z) - (q N i : ℂ) * z‖
          ≤ (q N i) ^ 2 * ‖z‖ ^ 2 := by
      calc
        ‖Complex.log (1 + (q N i : ℂ) * z) - (q N i : ℂ) * z‖
            ≤ ‖(q N i : ℂ) * z‖ ^ 2 :=
          norm_log_one_add_sub_self_le_sq (hwi i)
        _ = (q N i) ^ 2 * ‖z‖ ^ 2 := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hq N i)]
          ring
    calc
      ‖L N - (A N : ℂ) * z‖
          = ‖∑ i : Fin N,
              (Complex.log (1 + (q N i : ℂ) * z) - (q N i : ℂ) * z)‖ := by
            congr 1
            simp only [L, A, Finset.sum_sub_distrib, Finset.sum_mul,
              Complex.ofReal_sum]
      _ ≤ ∑ i : Fin N,
            ‖Complex.log (1 + (q N i : ℂ) * z) - (q N i : ℂ) * z‖ :=
        norm_sum_le _ _
      _ ≤ ∑ i : Fin N, (q N i) ^ 2 * ‖z‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => hlog i
      _ ≤ ∑ i : Fin N, (M N * q N i) * ‖z‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        gcongr
        calc
          q N i ^ 2 = q N i * q N i := pow_two _
          _ ≤ M N * q N i := mul_le_mul_of_nonneg_right (hqi_le i) (hq N i)
      _ = ‖z‖ ^ 2 * (M N * A N) := by
        rw [show (∑ i : Fin N, (M N * q N i) * ‖z‖ ^ 2) =
            M N * (∑ i : Fin N, q N i) * ‖z‖ ^ 2 by
              rw [← Finset.sum_mul, Finset.mul_sum]]
        simp only [A]
        ring
  have herror_norm :
      Tendsto (fun N => ‖L N - (A N : ℂ) * z‖) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) herror_bound
    simpa [mul_assoc] using (hMA.const_mul (‖z‖ ^ 2))
  have herror :
      Tendsto (fun N => L N - (A N : ℂ) * z) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr herror_norm
  have hAc : Tendsto (fun N => (A N : ℂ)) atTop (𝓝 (a : ℂ)) :=
    (Complex.continuous_ofReal.tendsto a).comp hA
  have hlinear :
      Tendsto (fun N => (A N : ℂ) * z) atTop (𝓝 ((a : ℂ) * z)) :=
    hAc.mul_const z
  have hL : Tendsto L atTop (𝓝 ((a : ℂ) * z)) := by
    have := herror.add hlinear
    simpa only [sub_add_cancel, zero_add] using this
  have hexp :
      Tendsto (fun N => Complex.exp (L N)) atTop
        (𝓝 (Complex.exp ((a : ℂ) * z))) :=
    (Complex.continuous_exp.tendsto _).comp hL
  apply hexp.congr'
  filter_upwards [hbound] with N hN
  rcases hN with ⟨hNpos, hsmall⟩
  have hnonempty : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hNpos
  have hqi_le (i : Fin N) : q N i ≤ M N := by
    exact Finite.le_ciSup (q N) i
  have hne (i : Fin N) : 1 + (q N i : ℂ) * z ≠ 0 := by
    intro hzero
    have hw : (q N i : ℂ) * z = -1 :=
      eq_neg_of_add_eq_zero_left (by simpa [add_comm] using hzero)
    have hnorm_lt : ‖(q N i : ℂ) * z‖ < 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hq N i)]
      exact (mul_le_mul_of_nonneg_right (hqi_le i) (norm_nonneg z)).trans_lt
        (hsmall.trans (by norm_num))
    rw [hw, norm_neg, norm_one] at hnorm_lt
    exact (lt_irrefl 1 hnorm_lt)
  rw [Complex.exp_sum]
  exact Finset.prod_congr rfl fun i _ => Complex.exp_log (hne i)

end HDP.Appendix
