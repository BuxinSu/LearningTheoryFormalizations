import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Data.Real.Sign
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Vaaler's pointwise sign majorant

This file develops the real-variable core of Vaaler's extremal approximation
to the sign function.  The auxiliary function `vaalerH` satisfies the sharp
pointwise estimate

`|sign x - vaalerH x| ≤ sinc (π x)²`.

The proof is elementary: two telescoping estimates control the tail of the
partial-fraction series occurring in Vaaler's function.
-/

open Real Complex Filter MeasureTheory ProbabilityTheory intervalIntegral Set
open scoped Interval UpperHalfPlane Topology FourierTransform

namespace HDP.Appendix

/-- The one-sided inverse-square tail appearing in Vaaler's approximation. -/
noncomputable def vaalerTail (x : ℝ) : ℝ :=
  ∑' n : ℕ, 1 / (x + (n + 1 : ℕ)) ^ 2

lemma summable_vaalerTail {x : ℝ} (hx : 0 < x) :
    Summable (fun n : ℕ => 1 / (x + (n + 1 : ℕ)) ^ 2) := by
  have hs : Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) ^ 2)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).2 hasSum_zeta_two.summable
  apply Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hs
  have hn0 : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hden : ((n + 1 : ℕ) : ℝ) ≤ x + (n + 1 : ℕ) := by linarith
  have hden0 : 0 < x + (n + 1 : ℕ) := by positivity
  rw [one_div, one_div]
  exact (inv_le_inv₀ (sq_pos_of_pos hden0) (sq_pos_of_pos hn0)).2
    (by nlinarith [sq_nonneg (x + (n + 1 : ℕ) - (n + 1 : ℕ))])

lemma hasSum_vaaler_telescoping {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℕ =>
      1 / ((x + n) * (x + n + 1))) (1 / x) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun n => by positivity)]
  have hlim : Tendsto (fun n : ℕ => 1 / (x + n)) atTop (nhds 0) := by
    have hat : Tendsto (fun n : ℕ => x + (n : ℝ)) atTop atTop :=
      tendsto_const_nhds.add_atTop tendsto_natCast_atTop_atTop
    have h := tendsto_inv_atTop_zero.comp hat
    simpa only [Function.comp_def, one_div] using h
  have hsum : (fun n : ℕ => ∑ i ∈ Finset.range n,
      1 / ((x + i) * (x + i + 1))) =
      (fun n : ℕ => 1 / x - 1 / (x + n)) := by
    funext n
    calc
      ∑ i ∈ Finset.range n, 1 / ((x + i) * (x + i + 1)) =
          ∑ i ∈ Finset.range n, (1 / (x + i) - 1 / (x + (i + 1))) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hxi : 0 < x + i := by positivity
        have hxi1 : 0 < x + i + 1 := by positivity
        field_simp [hxi.ne', hxi1.ne']
        ring
      _ = 1 / x - 1 / (x + n) := by
        simpa only [Nat.cast_zero, Nat.cast_add, Nat.cast_one, add_zero,
          add_assoc] using
          (Finset.sum_range_sub' (fun i : ℕ => 1 / (x + (i : ℝ))) n)
  rw [hsum]
  simpa using tendsto_const_nhds.sub hlim

lemma vaalerTail_le_inv {x : ℝ} (hx : 0 < x) :
    vaalerTail x ≤ 1 / x := by
  have hpoint : ∀ n : ℕ,
      1 / (x + (n + 1 : ℕ)) ^ 2 ≤
        1 / ((x + n) * (x + n + 1)) := by
    intro n
    have ha : 0 < x + n := by positivity
    have hb : 0 < x + n + 1 := by positivity
    have hcast : x + (n + 1 : ℕ) = x + n + 1 := by
      push_cast
      ring
    rw [hcast]
    rw [one_div, one_div]
    exact (inv_le_inv₀ (sq_pos_of_pos hb) (mul_pos ha hb)).2
      (by nlinarith [hb.le])
  change (∑' n : ℕ, 1 / (x + (n + 1 : ℕ)) ^ 2) ≤ 1 / x
  calc
    (∑' n : ℕ, 1 / (x + (n + 1 : ℕ)) ^ 2) ≤
        ∑' n : ℕ, 1 / ((x + n) * (x + n + 1)) :=
      (summable_vaalerTail hx).tsum_le_tsum hpoint
        (hasSum_vaaler_telescoping hx).summable
    _ = 1 / x := (hasSum_vaaler_telescoping hx).tsum_eq

lemma inv_sub_half_inv_sq_le_vaalerTail {x : ℝ} (hx : 0 < x) :
    1 / x - 1 / (2 * x ^ 2) ≤ vaalerTail x := by
  have hpoint : ∀ n : ℕ,
      2 / ((x + n) * (x + n + 1)) ≤
        1 / (x + n) ^ 2 + 1 / (x + n + 1) ^ 2 := by
    intro n
    have ha : 0 < x + n := by positivity
    have hb : 0 < x + n + 1 := by positivity
    field_simp [ha.ne', hb.ne']
    nlinarith [sq_nonneg ((x + n) - (x + n + 1))]
  have hleft := (hasSum_vaaler_telescoping hx).summable.mul_left 2
  have hleft' : Summable (fun n : ℕ =>
      2 / ((x + n) * (x + n + 1))) := by
    simpa only [div_eq_mul_inv, one_mul] using hleft
  have hs0 : Summable (fun n : ℕ => 1 / (x + n) ^ 2) := by
    have htail := summable_vaalerTail hx
    rw [← summable_nat_add_iff 1]
    simpa only [Nat.cast_add, Nat.cast_one] using htail
  have hs1 : Summable (fun n : ℕ => 1 / (x + n + 1) ^ 2) := by
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using
      summable_vaalerTail hx
  have hright := hs0.add hs1
  have hsum := hleft'.tsum_le_tsum hpoint hright
  have hleftsum :
      (∑' n : ℕ, 2 / ((x + n) * (x + n + 1))) = 2 * (1 / x) := by
    calc
      (∑' n : ℕ, 2 / ((x + n) * (x + n + 1))) =
          ∑' n : ℕ, 2 * (1 / ((x + n) * (x + n + 1))) := by
        apply tsum_congr
        intro n
        ring
      _ = 2 * ∑' n : ℕ, 1 / ((x + n) * (x + n + 1)) :=
        tsum_mul_left
      _ = 2 * (1 / x) := by rw [(hasSum_vaaler_telescoping hx).tsum_eq]
  have hrightsum :
      (∑' n : ℕ, (1 / (x + n) ^ 2 + 1 / (x + n + 1) ^ 2)) =
        (∑' n : ℕ, 1 / (x + n) ^ 2) +
          ∑' n : ℕ, 1 / (x + n + 1) ^ 2 :=
    Summable.tsum_add hs0 hs1
  rw [hleftsum, hrightsum] at hsum
  have hshift :
      ∑' n : ℕ, 1 / (x + n) ^ 2 =
        1 / x ^ 2 + vaalerTail x := by
    rw [hs0.tsum_eq_zero_add]
    simp only [Nat.cast_zero, add_zero, vaalerTail, Nat.cast_add,
      Nat.cast_one]
  have hshift' :
      ∑' n : ℕ, 1 / (x + n + 1) ^ 2 = vaalerTail x := by
    simp only [vaalerTail]
    apply tsum_congr
    intro n
    push_cast
    ring
  rw [hshift, hshift'] at hsum
  calc
    1 / x - 1 / (2 * x ^ 2) =
        (2 * (1 / x) - 1 / x ^ 2) / 2 := by ring
    _ ≤ (2 * vaalerTail x) / 2 := by
      apply div_le_div_of_nonneg_right ?_ (by norm_num)
      linarith only [hsum]
    _ = vaalerTail x := by ring

/-- Vaaler's squared-sinc error kernel. -/
noncomputable def vaalerK (x : ℝ) : ℝ :=
  Real.sinc (Real.pi * x) ^ 2

/-- The positive-half-line formula for Vaaler's sign approximant. -/
noncomputable def vaalerHPos (x : ℝ) : ℝ :=
  1 + (Real.sin (Real.pi * x) / Real.pi) ^ 2 *
    (2 / x - 1 / x ^ 2 - 2 * vaalerTail x)

/-- The odd extension of `vaalerHPos`, with value zero at the origin. -/
noncomputable def vaalerH (x : ℝ) : ℝ :=
  if 0 < x then vaalerHPos x
  else if x < 0 then -vaalerHPos (-x)
  else 0

lemma vaalerK_eq {x : ℝ} (hx : x ≠ 0) :
    vaalerK x =
      (Real.sin (Real.pi * x) / Real.pi) ^ 2 / x ^ 2 := by
  rw [vaalerK, Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero hx)]
  field_simp [Real.pi_ne_zero, hx]

lemma vaalerK_nonneg (x : ℝ) : 0 ≤ vaalerK x := by
  dsimp [vaalerK]
  positivity

lemma vaalerHPos_le_one {x : ℝ} (hx : 0 < x) :
    vaalerHPos x ≤ 1 := by
  have htail := inv_sub_half_inv_sq_le_vaalerTail hx
  have hfac : 0 ≤ (Real.sin (Real.pi * x) / Real.pi) ^ 2 := sq_nonneg _
  dsimp [vaalerHPos]
  have hbracket :
      2 / x - 1 / x ^ 2 - 2 * vaalerTail x ≤ 0 := by
    have h := mul_le_mul_of_nonneg_left htail (by norm_num : (0 : ℝ) ≤ 2)
    calc
      2 / x - 1 / x ^ 2 - 2 * vaalerTail x =
          2 * (1 / x - 1 / (2 * x ^ 2) - vaalerTail x) := by ring
      _ ≤ 0 := by linarith only [h]
  have hm := mul_nonpos_of_nonneg_of_nonpos hfac hbracket
  linarith only [hm]

lemma one_sub_vaalerK_le_vaalerHPos {x : ℝ} (hx : 0 < x) :
    1 - vaalerK x ≤ vaalerHPos x := by
  have htail := vaalerTail_le_inv hx
  have hfac : 0 ≤ (Real.sin (Real.pi * x) / Real.pi) ^ 2 := sq_nonneg _
  have hbracket :
      -(1 / x ^ 2) ≤
        2 / x - 1 / x ^ 2 - 2 * vaalerTail x := by
    have hdiff : 0 ≤ 2 * (1 / x - vaalerTail x) :=
      mul_nonneg (by norm_num) (sub_nonneg.mpr htail)
    calc
      -(1 / x ^ 2) ≤ -(1 / x ^ 2) + 2 * (1 / x - vaalerTail x) := by
        linarith only [hdiff]
      _ = 2 / x - 1 / x ^ 2 - 2 * vaalerTail x := by ring
  rw [vaalerK_eq hx.ne']
  dsimp [vaalerHPos]
  have hm := mul_le_mul_of_nonneg_left hbracket hfac
  calc
    1 - (Real.sin (Real.pi * x) / Real.pi) ^ 2 / x ^ 2 =
        1 + (Real.sin (Real.pi * x) / Real.pi) ^ 2 *
          (-(1 / x ^ 2)) := by ring
    _ ≤ 1 + (Real.sin (Real.pi * x) / Real.pi) ^ 2 *
          (2 / x - 1 / x ^ 2 - 2 * vaalerTail x) :=
      by simpa only [add_comm] using add_le_add_left hm 1

lemma vaalerH_odd (x : ℝ) : vaalerH (-x) = -vaalerH x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [vaalerH, if_pos (neg_pos.mpr hx)]
    rw [vaalerH, if_neg (not_lt_of_ge hx.le), if_pos hx]
    simp
  · simp [vaalerH]
  · rw [vaalerH, if_neg (not_lt_of_ge (neg_nonpos.mpr hx.le)),
      if_pos (neg_lt_zero.mpr hx)]
    rw [vaalerH, if_pos hx]
    simp

lemma vaalerK_even (x : ℝ) : vaalerK (-x) = vaalerK x := by
  simp [vaalerK, Real.sinc_neg]

lemma abs_sign_sub_vaalerH_le (x : ℝ) :
    |Real.sign x - vaalerH x| ≤ vaalerK x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have hp := one_sub_vaalerK_le_vaalerHPos (neg_pos.mpr hx)
    have hu := vaalerHPos_le_one (neg_pos.mpr hx)
    have hk := vaalerK_nonneg (-x)
    have hHx : vaalerH x = -vaalerHPos (-x) := by
      rw [vaalerH, if_neg (not_lt_of_ge hx.le), if_pos hx]
    rw [hHx, Real.sign_of_neg hx]
    rw [show -1 - -vaalerHPos (-x) = -(1 - vaalerHPos (-x)) by ring,
      abs_neg, ← vaalerK_even x]
    rw [abs_le]
    constructor <;> linarith
  · simp [vaalerH, vaalerK]
  · have hp := one_sub_vaalerK_le_vaalerHPos hx
    have hu := vaalerHPos_le_one hx
    have hk := vaalerK_nonneg x
    have hHx : vaalerH x = vaalerHPos x := by
      rw [vaalerH, if_pos hx]
    rw [hHx, Real.sign_of_pos hx, abs_le]
    constructor <;> linarith

lemma hasDerivAt_cexp_mul (c : ℂ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.exp (c * y))
      (Complex.exp (c * x) * c) x := by
  have hinner : HasDerivAt (fun y : ℝ => c * (y : ℂ)) c x := by
    simpa using! (((hasDerivAt_id (x : ℂ)).const_mul c).comp_ofReal)
  simpa only [Function.comp_apply] using!
    (Complex.hasDerivAt_exp (c * (x : ℂ))).comp x hinner

lemma hasDerivAt_cexp_div (c : ℂ) (hc : c ≠ 0) (x : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.exp (c * y) / c)
      (Complex.exp (c * x)) x := by
  simpa only [mul_div_cancel_right₀ _ hc] using
    (hasDerivAt_cexp_mul c x).div_const c

lemma integral_one_sub_mul_cexp (c : ℂ) (hc : c ≠ 0) :
    (∫ t : ℝ in 0..1, ((1 - t : ℝ) : ℂ) * Complex.exp (c * t)) =
      -1 / c + (Complex.exp c - 1) / c ^ 2 := by
  have hu : ∀ x ∈ [[(0 : ℝ), 1]],
      HasDerivAt (fun y : ℝ => ((1 - y : ℝ) : ℂ)) (-1 : ℂ) x := by
    intro x hx
    simpa using
      ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).ofReal_comp
  have hv : ∀ x ∈ [[(0 : ℝ), 1]],
      HasDerivAt (fun y : ℝ => Complex.exp (c * y) / c)
        (Complex.exp (c * x)) x := fun x hx => hasDerivAt_cexp_div c hc x
  have h := integral_mul_deriv_eq_deriv_mul hu hv
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)
  rw [h]
  simp_rw [div_eq_mul_inv]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const]
  rw [integral_exp_mul_complex hc]
  norm_num [Complex.exp_zero]
  field_simp [hc]

lemma integral_one_add_mul_cexp (c : ℂ) (hc : c ≠ 0) :
    (∫ t : ℝ in -1..0, ((1 + t : ℝ) : ℂ) * Complex.exp (c * t)) =
      1 / c - (1 - Complex.exp (-c)) / c ^ 2 := by
  have hu : ∀ x ∈ [[(-1 : ℝ), 0]],
      HasDerivAt (fun y : ℝ => ((1 + y : ℝ) : ℂ)) (1 : ℂ) x := by
    intro x hx
    simpa using
      ((hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)).ofReal_comp
  have hv : ∀ x ∈ [[(-1 : ℝ), 0]],
      HasDerivAt (fun y : ℝ => Complex.exp (c * y) / c)
        (Complex.exp (c * x)) x := fun x hx => hasDerivAt_cexp_div c hc x
  have h := integral_mul_deriv_eq_deriv_mul hu hv
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)
  rw [h]
  simp_rw [div_eq_mul_inv]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const]
  rw [integral_exp_mul_complex hc]
  norm_num [Complex.exp_zero]
  field_simp [hc]

lemma intervalIntegral_triangle_cexp (c : ℂ) (hc : c ≠ 0) :
    (∫ t : ℝ in -1..1, ((1 - |t| : ℝ) : ℂ) * Complex.exp (c * t)) =
      (Complex.exp c + Complex.exp (-c) - 2) / c ^ 2 := by
  have hleft : IntervalIntegrable
      (fun t : ℝ => ((1 - |t| : ℝ) : ℂ) * Complex.exp (c * t))
      volume (-1) 0 := by
    apply ContinuousOn.intervalIntegrable
    fun_prop
  have hright : IntervalIntegrable
      (fun t : ℝ => ((1 - |t| : ℝ) : ℂ) * Complex.exp (c * t))
      volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    fun_prop
  rw [← integral_add_adjacent_intervals hleft hright]
  have hneg :
      (∫ t : ℝ in -1..0, ((1 - |t| : ℝ) : ℂ) * Complex.exp (c * t)) =
        ∫ t : ℝ in -1..0, ((1 + t : ℝ) : ℂ) * Complex.exp (c * t) := by
    apply integral_congr
    intro t ht
    have ht0 : t ≤ 0 := by simpa using ht.2
    change ((1 - |t| : ℝ) : ℂ) * Complex.exp (c * t) =
      ((1 + t : ℝ) : ℂ) * Complex.exp (c * t)
    congr 2
    rw [abs_of_nonpos ht0]
    ring
  have hpos :
      (∫ t : ℝ in 0..1, ((1 - |t| : ℝ) : ℂ) * Complex.exp (c * t)) =
        ∫ t : ℝ in 0..1, ((1 - t : ℝ) : ℂ) * Complex.exp (c * t) := by
    apply integral_congr
    intro t ht
    have ht0 : 0 ≤ t := by simpa using ht.1
    change ((1 - |t| : ℝ) : ℂ) * Complex.exp (c * t) =
      ((1 - t : ℝ) : ℂ) * Complex.exp (c * t)
    congr 2
    rw [abs_of_nonneg ht0]
  rw [hneg, hpos, integral_one_add_mul_cexp c hc,
    integral_one_sub_mul_cexp c hc]
  field_simp [hc]
  ring

lemma intervalIntegral_triangle_fourier (x : ℝ) :
    (∫ t : ℝ in -1..1,
      ((1 - |t| : ℝ) : ℂ) *
        Complex.exp ((((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) * t)) =
      ((Real.sinc (Real.pi * x) ^ 2 : ℝ) : ℂ) := by
  by_cases hx : x = 0
  · subst x
    simp only [mul_zero, ofReal_zero, zero_mul, Complex.exp_zero, mul_one,
      Real.sinc_zero, one_pow, ofReal_one]
    have hleft : IntervalIntegrable
        (fun t : ℝ => ((1 - |t| : ℝ) : ℂ)) volume (-1) 0 := by
      apply ContinuousOn.intervalIntegrable
      fun_prop
    have hright : IntervalIntegrable
        (fun t : ℝ => ((1 - |t| : ℝ) : ℂ)) volume 0 1 := by
      apply ContinuousOn.intervalIntegrable
      fun_prop
    rw [← integral_add_adjacent_intervals hleft hright]
    have hneg :
        (∫ t : ℝ in -1..0, ((1 - |t| : ℝ) : ℂ)) =
          ∫ t : ℝ in -1..0, ((1 + t : ℝ) : ℂ) := by
      apply integral_congr
      intro t ht
      have ht0 : t ≤ 0 := by simpa using ht.2
      simp [abs_of_nonpos ht0]
    have hpos :
        (∫ t : ℝ in 0..1, ((1 - |t| : ℝ) : ℂ)) =
          ∫ t : ℝ in 0..1, ((1 - t : ℝ) : ℂ) := by
      apply integral_congr
      intro t ht
      have ht0 : 0 ≤ t := by simpa using ht.1
      simp [abs_of_nonneg ht0]
    rw [hneg, hpos]
    rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal]
    have hiNeg : (∫ t : ℝ in -1..0, 1 + t) = 1 / 2 := by
      rw [intervalIntegral.integral_add
        (by apply Continuous.intervalIntegrable; fun_prop)
        (by apply Continuous.intervalIntegrable; fun_prop)]
      rw [intervalIntegral.integral_const, integral_id]
      norm_num
    have hiPos : (∫ t : ℝ in 0..1, 1 - t) = 1 / 2 := by
      rw [intervalIntegral.integral_sub
        (by apply Continuous.intervalIntegrable; fun_prop)
        (by apply Continuous.intervalIntegrable; fun_prop)]
      rw [intervalIntegral.integral_const, integral_id]
      norm_num
    rw [hiNeg, hiPos]
    norm_num
  · let c : ℂ := (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
    have hc : c ≠ 0 := by
      dsimp [c]
      exact mul_ne_zero
        (ofReal_ne_zero.mpr
          (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hx))
        Complex.I_ne_zero
    rw [intervalIntegral_triangle_cexp c hc]
    dsimp [c]
    have hnum :
        Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) +
            Complex.exp (-(((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)) - 2 =
          ((-4 * Real.sin (Real.pi * x) ^ 2 : ℝ) : ℂ) := by
      rw [Complex.exp_mul_I]
      rw [show -(((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) =
          ((-(2 * Real.pi * x) : ℝ) : ℂ) * Complex.I by push_cast; ring]
      rw [Complex.exp_mul_I]
      rw [← Complex.ofReal_cos (2 * Real.pi * x),
        ← Complex.ofReal_sin (2 * Real.pi * x),
        ← Complex.ofReal_cos (-(2 * Real.pi * x)),
        ← Complex.ofReal_sin (-(2 * Real.pi * x))]
      rw [Real.cos_neg, Real.sin_neg]
      rw [show 2 * Real.pi * x = 2 * (Real.pi * x) by ring,
        Real.cos_two_mul]
      push_cast
      linear_combination
        4 * Complex.cos_sq_add_sin_sq (((Real.pi : ℂ) * (x : ℂ)))
    have hden :
        ((((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) ^ 2) =
          ((-4 * (Real.pi * x) ^ 2 : ℝ) : ℂ) := by
      rw [mul_pow, Complex.I_sq]
      push_cast
      ring
    rw [hnum, hden]
    rw [Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero hx)]
    push_cast
    field_simp [Real.pi_ne_zero, hx]

lemma intervalIntegral_triangle_fourier_eq_vaalerK (x : ℝ) :
    (∫ t : ℝ in -1..1,
      ((1 - |t| : ℝ) : ℂ) *
        Complex.exp ((((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) * t)) =
      (vaalerK x : ℂ) := by
  simpa only [vaalerK] using intervalIntegral_triangle_fourier x

lemma intervalIntegral_sign_cexp (c : ℂ) (hc : c ≠ 0) :
    (∫ t : ℝ in -1..1,
      ((Real.sign t : ℝ) : ℂ) * Complex.exp (c * t)) =
      (Complex.exp c + Complex.exp (-c) - 2) / c := by
  let f : ℝ → ℂ := fun t =>
    ((Real.sign t : ℝ) : ℂ) * Complex.exp (c * t)
  let fn : ℝ → ℂ := fun t => -Complex.exp (c * t)
  let fp : ℝ → ℂ := fun t => Complex.exp (c * t)
  have hn_ae : f =ᵐ[volume.restrict (uIoc (-1) 0)] fn := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc,
      (volume.restrict (uIoc (-1) 0)).ae_ne 0] with t ht ht0
    norm_num at ht
    have htle : t ≤ 0 := ht.2
    have htneg : t < 0 := lt_of_le_of_ne htle ht0
    simp [f, fn, Real.sign_of_neg htneg]
  have hp_ae : f =ᵐ[volume.restrict (uIoc 0 1)] fp := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc,
      (volume.restrict (uIoc 0 1)).ae_ne 0] with t ht ht0
    norm_num at ht
    have htle : 0 ≤ t := le_of_lt ht.1
    have htpos : 0 < t := lt_of_le_of_ne htle (Ne.symm ht0)
    simp [f, fp, Real.sign_of_pos htpos]
  have hn : IntervalIntegrable f volume (-1) 0 := by
    apply IntervalIntegrable.congr_ae
      (show IntervalIntegrable fn volume (-1) 0 by
        apply Continuous.intervalIntegrable
        fun_prop)
    exact hn_ae.symm
  have hp : IntervalIntegrable f volume 0 1 := by
    apply IntervalIntegrable.congr_ae
      (show IntervalIntegrable fp volume 0 1 by
        apply Continuous.intervalIntegrable
        fun_prop)
    exact hp_ae.symm
  change (∫ t : ℝ in -1..1, f t) = _
  rw [← integral_add_adjacent_intervals hn hp]
  have hintn : (∫ t : ℝ in -1..0, f t) =
      ∫ t : ℝ in -1..0, fn t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [volume.ae_ne 0] with t ht0 ht
    have htneg : t < 0 := by
      norm_num at ht
      have htle : t ≤ 0 := ht.2
      exact lt_of_le_of_ne htle ht0
    simp [f, fn, Real.sign_of_neg htneg]
  have hintp : (∫ t : ℝ in 0..1, f t) =
      ∫ t : ℝ in 0..1, fp t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [volume.ae_ne 0] with t ht0 ht
    have htpos : 0 < t := by
      norm_num at ht
      have htle : 0 ≤ t := le_of_lt ht.1
      exact lt_of_le_of_ne htle (Ne.symm ht0)
    simp [f, fp, Real.sign_of_pos htpos]
  rw [hintn, hintp]
  dsimp [fn, fp]
  rw [intervalIntegral.integral_neg]
  rw [integral_exp_mul_complex hc, integral_exp_mul_complex hc]
  norm_num [Complex.exp_zero]
  field_simp [hc]
  ring

lemma intervalIntegral_sign_fourier (x : ℝ) :
    (∫ t : ℝ in -1..1,
      ((Real.sign t : ℝ) : ℂ) *
        Complex.exp ((((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) * t)) =
      (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) *
        ((Real.sinc (Real.pi * x) ^ 2 : ℝ) : ℂ) := by
  by_cases hx : x = 0
  · subst x
    simp only [mul_zero, ofReal_zero, zero_mul, Complex.exp_zero, mul_one,
      Real.sinc_zero, one_pow, ofReal_one]
    let f : ℝ → ℂ := fun t => ((Real.sign t : ℝ) : ℂ)
    let fn : ℝ → ℂ := fun _ => -1
    let fp : ℝ → ℂ := fun _ => 1
    have hn_ae : f =ᵐ[volume.restrict (uIoc (-1) 0)] fn := by
      filter_upwards [ae_restrict_mem measurableSet_uIoc,
        (volume.restrict (uIoc (-1) 0)).ae_ne 0] with t ht ht0
      norm_num at ht
      have htle : t ≤ 0 := ht.2
      have htneg : t < 0 := lt_of_le_of_ne htle ht0
      simp [f, fn, Real.sign_of_neg htneg]
    have hp_ae : f =ᵐ[volume.restrict (uIoc 0 1)] fp := by
      filter_upwards [ae_restrict_mem measurableSet_uIoc,
        (volume.restrict (uIoc 0 1)).ae_ne 0] with t ht ht0
      norm_num at ht
      have htle : 0 ≤ t := le_of_lt ht.1
      have htpos : 0 < t := lt_of_le_of_ne htle (Ne.symm ht0)
      simp [f, fp, Real.sign_of_pos htpos]
    have hn : IntervalIntegrable f volume (-1) 0 := by
      apply IntervalIntegrable.congr_ae
        (show IntervalIntegrable fn volume (-1) 0 by
          apply Continuous.intervalIntegrable
          fun_prop)
      exact hn_ae.symm
    have hp : IntervalIntegrable f volume 0 1 := by
      apply IntervalIntegrable.congr_ae
        (show IntervalIntegrable fp volume 0 1 by
          apply Continuous.intervalIntegrable
          fun_prop)
      exact hp_ae.symm
    change (∫ t : ℝ in -1..1, f t) = 0
    rw [← integral_add_adjacent_intervals hn hp]
    have hintn : (∫ t : ℝ in -1..0, f t) =
        ∫ t : ℝ in -1..0, fn t := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [volume.ae_ne 0] with t ht0 ht
      norm_num at ht
      have htle : t ≤ 0 := ht.2
      have htneg : t < 0 := lt_of_le_of_ne htle ht0
      simp [f, fn, Real.sign_of_neg htneg]
    have hintp : (∫ t : ℝ in 0..1, f t) =
        ∫ t : ℝ in 0..1, fp t := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [volume.ae_ne 0] with t ht0 ht
      norm_num at ht
      have htle : 0 ≤ t := le_of_lt ht.1
      have htpos : 0 < t := lt_of_le_of_ne htle (Ne.symm ht0)
      simp [f, fp, Real.sign_of_pos htpos]
    rw [hintn, hintp]
    simp [fn, fp]
  · let c : ℂ := (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
    have hc : c ≠ 0 := by
      dsimp [c]
      exact mul_ne_zero
        (ofReal_ne_zero.mpr
          (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hx))
        Complex.I_ne_zero
    rw [intervalIntegral_sign_cexp c hc]
    have hratio : (Complex.exp c + Complex.exp (-c) - 2) / c =
        c * ((Complex.exp c + Complex.exp (-c) - 2) / c ^ 2) := by
      field_simp [hc]
    rw [hratio]
    rw [← intervalIntegral_triangle_cexp c hc]
    rw [intervalIntegral_triangle_fourier x]

lemma intervalIntegral_sign_fourier_eq_vaalerK (x : ℝ) :
    (∫ t : ℝ in -1..1,
      ((Real.sign t : ℝ) : ℂ) *
        Complex.exp ((((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) * t)) =
      (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) * (vaalerK x : ℂ) := by
  simpa only [vaalerK] using intervalIntegral_sign_fourier x

/-! ## The real cosecant partial-fraction expansion -/

lemma hasDerivAt_pi_mul_cot_pi {z : ℂ}
    (hz : Complex.sin ((Real.pi : ℂ) * z) ≠ 0) :
    HasDerivAt (fun w : ℂ =>
      (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * w))
      (-((Real.pi : ℂ) ^ 2) /
        Complex.sin ((Real.pi : ℂ) * z) ^ 2) z := by
  have hinner : HasDerivAt (fun w : ℂ => (Real.pi : ℂ) * w)
      (Real.pi : ℂ) z := by
    simpa using (hasDerivAt_id z).const_mul (Real.pi : ℂ)
  have hc : HasDerivAt
      (fun w : ℂ => Complex.cos ((Real.pi : ℂ) * w))
      (-Complex.sin ((Real.pi : ℂ) * z) * (Real.pi : ℂ)) z := by
    simpa only [Function.comp_apply] using!
      (Complex.hasDerivAt_cos ((Real.pi : ℂ) * z)).comp z hinner
  have hs : HasDerivAt
      (fun w : ℂ => Complex.sin ((Real.pi : ℂ) * w))
      (Complex.cos ((Real.pi : ℂ) * z) * (Real.pi : ℂ)) z := by
    simpa only [Function.comp_apply] using!
      (Complex.hasDerivAt_sin ((Real.pi : ℂ) * z)).comp z hinner
  have hq := hc.div hs hz
  have hm := hq.const_mul (Real.pi : ℂ)
  have heq :
      (Real.pi : ℂ) *
          ((-Complex.sin ((Real.pi : ℂ) * z) * (Real.pi : ℂ) *
              Complex.sin ((Real.pi : ℂ) * z) -
            Complex.cos ((Real.pi : ℂ) * z) *
              (Complex.cos ((Real.pi : ℂ) * z) * (Real.pi : ℂ))) /
            Complex.sin ((Real.pi : ℂ) * z) ^ 2) =
        -((Real.pi : ℂ) ^ 2) /
          Complex.sin ((Real.pi : ℂ) * z) ^ 2 := by
    field_simp [hz]
    rw [← Complex.sin_sq_add_cos_sq ((Real.pi : ℂ) * z)]
    ring
  rw [← heq]
  simpa only [Complex.cot] using! hm

lemma tsum_int_inv_sq_upper {z : ℂ}
    (hz : z ∈ UpperHalfPlane.upperHalfPlaneSet) :
    (∑' n : ℤ, 1 / (z + n) ^ 2) =
      (Real.pi : ℂ) ^ 2 /
        Complex.sin ((Real.pi : ℂ) * z) ^ 2 := by
  have hsin : Complex.sin ((Real.pi : ℂ) * z) ≠ 0 :=
    sin_pi_mul_ne_zero
      (UpperHalfPlane.coe_mem_integerComplement ⟨z, hz⟩)
  have hseries :=
    iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_div_pow
      (k := 1) (by norm_num) hz
  rw [iteratedDerivWithin_one,
    derivWithin_of_isOpen UpperHalfPlane.isOpen_upperHalfPlaneSet hz,
    (hasDerivAt_pi_mul_cot_pi hsin).deriv] at hseries
  norm_num at hseries
  have hseries' :
      -((Real.pi : ℂ) ^ 2 /
          Complex.sin ((Real.pi : ℂ) * z) ^ 2) =
        -(∑' n : ℤ, ((z + n) ^ 2)⁻¹) := by
    calc
      -((Real.pi : ℂ) ^ 2 /
          Complex.sin ((Real.pi : ℂ) * z) ^ 2) =
          -((Real.pi : ℂ) ^ 2) /
            Complex.sin ((Real.pi : ℂ) * z) ^ 2 := by ring
      _ = -(∑' n : ℤ, ((z + n) ^ 2)⁻¹) := hseries
  simpa only [one_div] using (neg_inj.mp hseries').symm

lemma tsum_int_inv_sq_real {t : ℝ}
    (ht : (t : ℂ) ∈ Complex.integerComplement) :
    (∑' n : ℤ, 1 / (((t : ℂ) + n) ^ 2)) =
      (Real.pi : ℂ) ^ 2 /
        Complex.sin ((Real.pi : ℂ) * t) ^ 2 := by
  let f : ℝ → ℤ → ℂ := fun y n =>
    1 / (((t : ℂ) + (y : ℂ) * Complex.I + n) ^ 2)
  let g : ℤ → ℂ := fun n => 1 / (((t : ℂ) + n) ^ 2)
  let bound : ℤ → ℝ := fun n => ‖g n‖
  have hgSummable : Summable g := by
    simpa only [g, one_div, Int.cast_one, one_mul] using!
      (EisensteinSeries.linear_right_summable (t : ℂ) 1
        (k := 2) (by norm_num))
  have hboundSummable : Summable bound := hgSummable.norm
  have hterm (n : ℤ) :
      Tendsto (fun y : ℝ => f y n) (nhdsWithin 0 (Ioi 0))
        (nhds (g n)) := by
    have hne : ((t : ℂ) + n) ^ 2 ≠ 0 :=
      pow_ne_zero 2 (Complex.integerComplement_add_ne_zero ht n)
    have hcont : ContinuousAt (fun y : ℝ =>
        1 / (((t : ℂ) + (y : ℂ) * Complex.I + n) ^ 2)) 0 := by
      apply ContinuousAt.div continuousAt_const
      · fun_prop
      · simpa using hne
    simpa only [f, g, ofReal_zero, zero_mul, add_zero] using
      hcont.tendsto.mono_left
        (show nhdsWithin (0 : ℝ) (Ioi 0) ≤ nhds 0 from inf_le_left)
  have hdom :
      ∀ᶠ y in nhdsWithin 0 (Ioi 0),
        ∀ n : ℤ, ‖f y n‖ ≤ bound n := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    intro n
    have ha0 : ((t : ℂ) + n) ≠ 0 :=
      Complex.integerComplement_add_ne_zero ht n
    have hz0 : (t : ℂ) + (y : ℂ) * Complex.I + n ≠ 0 := by
      intro hzero
      have him := congrArg Complex.im hzero
      simp at him
      exact (ne_of_gt hy) him
    have hnorm :
        ‖(t : ℂ) + n‖ ≤
          ‖(t : ℂ) + (y : ℂ) * Complex.I + n‖ := by
      rw [← (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _))]
      rw [Complex.sq_norm, Complex.sq_norm]
      rw [show (t : ℂ) + (y : ℂ) * Complex.I + n =
          (((t + n : ℝ) : ℂ) + (y : ℂ) * Complex.I) by
            push_cast
            ring]
      rw [show (t : ℂ) + n = ((t + n : ℝ) : ℂ) by
            push_cast
            ring]
      rw [Complex.normSq_add_mul_I, Complex.normSq_ofReal]
      nlinarith [sq_nonneg y]
    dsimp only [f, bound, g]
    simp only [one_div, norm_inv, norm_pow]
    exact (inv_le_inv₀ (sq_pos_of_pos (norm_pos_iff.mpr hz0))
      (sq_pos_of_pos (norm_pos_iff.mpr ha0))).2
        ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hnorm)
  have hsumTendsto :
      Tendsto (fun y : ℝ => ∑' n : ℤ, f y n)
        (nhdsWithin 0 (Ioi 0)) (nhds (∑' n : ℤ, g n)) :=
    tendsto_tsum_of_dominated_convergence
      hboundSummable hterm hdom
  have hsin :
      Complex.sin ((Real.pi : ℂ) * (t : ℂ)) ≠ 0 :=
    sin_pi_mul_ne_zero ht
  have hrhsTendsto :
      Tendsto (fun y : ℝ =>
        (Real.pi : ℂ) ^ 2 /
          Complex.sin ((Real.pi : ℂ) *
            ((t : ℂ) + (y : ℂ) * Complex.I)) ^ 2)
        (nhdsWithin 0 (Ioi 0))
        (nhds ((Real.pi : ℂ) ^ 2 /
          Complex.sin ((Real.pi : ℂ) * (t : ℂ)) ^ 2)) := by
    have hcont : ContinuousAt (fun y : ℝ =>
        (Real.pi : ℂ) ^ 2 /
          Complex.sin ((Real.pi : ℂ) *
            ((t : ℂ) + (y : ℂ) * Complex.I)) ^ 2) 0 := by
      apply ContinuousAt.div continuousAt_const
      · fun_prop
      · simpa using pow_ne_zero 2 hsin
    simpa only [ofReal_zero, zero_mul, add_zero] using
      hcont.tendsto.mono_left
        (show nhdsWithin (0 : ℝ) (Ioi 0) ≤ nhds 0 from inf_le_left)
  have heq :
      ∀ᶠ y in nhdsWithin 0 (Ioi 0),
        (∑' n : ℤ, f y n) =
          (Real.pi : ℂ) ^ 2 /
            Complex.sin ((Real.pi : ℂ) *
              ((t : ℂ) + (y : ℂ) * Complex.I)) ^ 2 := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hzmem :
        ((t : ℂ) + (y : ℂ) * Complex.I) ∈
          UpperHalfPlane.upperHalfPlaneSet := by
      change 0 < ((t : ℂ) + (y : ℂ) * Complex.I).im
      simpa using hy
    simpa only [f, add_assoc] using tsum_int_inv_sq_upper hzmem
  have heq' :
      (fun y : ℝ =>
        (Real.pi : ℂ) ^ 2 /
          Complex.sin ((Real.pi : ℂ) *
            ((t : ℂ) + (y : ℂ) * Complex.I)) ^ 2) =ᶠ[
        nhdsWithin 0 (Ioi 0)]
          (fun y : ℝ => ∑' n : ℤ, f y n) := by
    filter_upwards [heq] with y hy
    exact hy.symm
  have hsumTendsto' := hrhsTendsto.congr' heq'
  have hlim := tendsto_nhds_unique hsumTendsto hsumTendsto'
  simpa only [g] using hlim

lemma csc_sq_series_complex {t : ℝ}
    (ht : (t : ℂ) ∈ Complex.integerComplement) :
    (Real.pi : ℂ) ^ 2 /
        Complex.sin ((Real.pi : ℂ) * t) ^ 2 =
      1 / (t : ℂ) ^ 2 +
        ∑' n : ℕ,
          (1 / ((t : ℂ) - (n + 1)) ^ 2 +
            1 / ((t : ℂ) + (n + 1)) ^ 2) := by
  let f : ℤ → ℂ := fun n => 1 / (((t : ℂ) + n) ^ 2)
  have hf : Summable f := by
    simpa only [f, one_div, Int.cast_one, one_mul] using!
      (EisensteinSeries.linear_right_summable (t : ℂ) 1
        (k := 2) (by norm_num))
  have hpos0 : Summable (fun n : ℕ => f n) :=
    (summable_int_iff_summable_nat_and_neg.mp hf).1
  have hneg0 : Summable (fun n : ℕ => f (-n)) :=
    (summable_int_iff_summable_nat_and_neg.mp hf).2
  have hpos : Summable (fun n : ℕ => f (n + 1)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).2 hpos0
  have hneg : Summable (fun n : ℕ => f (-(n + 1))) := by
    simpa only [Nat.cast_add, Nat.cast_one, Int.cast_neg] using
      (summable_nat_add_iff 1).2 hneg0
  have hsplit := tsum_of_add_one_of_neg_add_one hpos hneg
  have hcsc := (tsum_int_inv_sq_real ht).symm
  rw [hcsc, hsplit]
  calc
    (∑' n : ℕ, f (n + 1)) + f 0 +
        ∑' n : ℕ, f (-(n + 1)) =
      f 0 + ((∑' n : ℕ, f (-(n + 1))) +
        ∑' n : ℕ, f (n + 1)) := by ring
    _ = f 0 +
        ∑' n : ℕ, (f (-(n + 1)) + f (n + 1)) := by
      rw [Summable.tsum_add hneg hpos]
    _ = 1 / (t : ℂ) ^ 2 +
        ∑' n : ℕ,
          (1 / ((t : ℂ) - (n + 1)) ^ 2 +
            1 / ((t : ℂ) + (n + 1)) ^ 2) := by
      congr 1
      · simp [f]
      · apply tsum_congr
        intro n
        dsimp [f]
        push_cast
        congr 2

lemma csc_sq_series_real {t : ℝ}
    (ht : (t : ℂ) ∈ Complex.integerComplement) :
    Real.pi ^ 2 / Real.sin (Real.pi * t) ^ 2 =
      1 / t ^ 2 +
        ∑' n : ℕ,
          (1 / (t - (n + 1)) ^ 2 +
            1 / (t + (n + 1)) ^ 2) := by
  have h := csc_sq_series_complex ht
  exact_mod_cast h

lemma summable_inv_sq_add_nat (t : ℝ) :
    Summable
      (fun n : ℕ => 1 / (t + (n + 1 : ℕ)) ^ 2) := by
  let f : ℤ → ℂ := fun n => 1 / (((t : ℂ) + n) ^ 2)
  have hf : Summable f := by
    simpa only [f, one_div, Int.cast_one, one_mul] using!
      (EisensteinSeries.linear_right_summable (t : ℂ) 1
        (k := 2) (by norm_num))
  have hpos0 : Summable (fun n : ℕ => f n) :=
    (summable_int_iff_summable_nat_and_neg.mp hf).1
  have hpos : Summable (fun n : ℕ => f (n + 1)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).2 hpos0
  apply Complex.summable_ofReal.mp
  convert hpos using 1
  ext n
  dsimp [f]
  push_cast
  rfl

lemma summable_inv_sq_sub_nat (t : ℝ) :
    Summable
      (fun n : ℕ => 1 / (t - (n + 1 : ℕ)) ^ 2) := by
  let f : ℤ → ℂ := fun n => 1 / (((t : ℂ) + n) ^ 2)
  have hf : Summable f := by
    simpa only [f, one_div, Int.cast_one, one_mul] using!
      (EisensteinSeries.linear_right_summable (t : ℂ) 1
        (k := 2) (by norm_num))
  have hneg0 : Summable (fun n : ℕ => f (-n)) :=
    (summable_int_iff_summable_nat_and_neg.mp hf).2
  have hneg : Summable (fun n : ℕ => f (-(n + 1))) := by
    simpa only [Nat.cast_add, Nat.cast_one, Int.cast_neg] using
      (summable_nat_add_iff 1).2 hneg0
  apply Complex.summable_ofReal.mp
  convert hneg using 1
  ext n
  dsimp [f]
  push_cast
  congr 2

/-! ## A cardinal-series representation of `vaalerH` -/

lemma vaalerK_sub_nat_eq {x : ℝ} (n : ℕ)
    (hx : x - (n + 1 : ℕ) ≠ 0) :
    vaalerK (x - (n + 1 : ℕ)) =
      (Real.sin (Real.pi * x) / Real.pi) ^ 2 /
        (x - (n + 1 : ℕ)) ^ 2 := by
  rw [vaalerK_eq hx]
  rw [show Real.pi * (x - (n + 1 : ℕ)) =
      Real.pi * x - (n + 1 : ℕ) * Real.pi by
        push_cast
        ring]
  rw [Real.sin_sub_nat_mul_pi]
  have hs : ((-1 : ℝ) ^ (n + 1)) ^ 2 = 1 := by
    rw [← pow_mul]
    norm_num
  rw [div_pow, mul_pow, hs, one_mul]
  ring

lemma vaalerK_add_nat_eq {x : ℝ} (n : ℕ)
    (hx : x + (n + 1 : ℕ) ≠ 0) :
    vaalerK (x + (n + 1 : ℕ)) =
      (Real.sin (Real.pi * x) / Real.pi) ^ 2 /
        (x + (n + 1 : ℕ)) ^ 2 := by
  rw [vaalerK_eq hx]
  rw [show Real.pi * (x + (n + 1 : ℕ)) =
      Real.pi * x + (n + 1 : ℕ) * Real.pi by
        push_cast
        ring]
  rw [Real.sin_add_nat_mul_pi]
  have hs : ((-1 : ℝ) ^ (n + 1)) ^ 2 = 1 := by
    rw [← pow_mul]
    norm_num
  rw [div_pow, mul_pow, hs, one_mul]
  ring

lemma vaaler_sub_nat_ne_zero_of_mem_integerComplement {x : ℝ}
    (hx : (x : ℂ) ∈ Complex.integerComplement) (n : ℕ) :
    x - (n + 1 : ℕ) ≠ 0 := by
  rw [Complex.mem_integerComplement_iff] at hx
  intro h
  apply hx
  refine ⟨((n + 1 : ℕ) : ℤ), ?_⟩
  exact_mod_cast (sub_eq_zero.mp h).symm

lemma vaaler_add_nat_ne_zero_of_mem_integerComplement {x : ℝ}
    (hx : (x : ℂ) ∈ Complex.integerComplement) (n : ℕ) :
    x + (n + 1 : ℕ) ≠ 0 := by
  have hc :=
    Complex.integerComplement_add_ne_zero hx ((n + 1 : ℕ) : ℤ)
  exact_mod_cast hc

lemma summable_vaalerK_sub {x : ℝ}
    (hx : (x : ℂ) ∈ Complex.integerComplement) :
    Summable (fun n : ℕ =>
      vaalerK (x - (n + 1 : ℕ))) := by
  let a := (Real.sin (Real.pi * x) / Real.pi) ^ 2
  have hs := (summable_inv_sq_sub_nat x).mul_left a
  apply hs.congr
  intro n
  dsimp [a]
  rw [vaalerK_sub_nat_eq n
    (vaaler_sub_nat_ne_zero_of_mem_integerComplement hx n)]
  ring

lemma summable_vaalerK_add {x : ℝ}
    (hx : (x : ℂ) ∈ Complex.integerComplement) :
    Summable (fun n : ℕ =>
      vaalerK (x + (n + 1 : ℕ))) := by
  let a := (Real.sin (Real.pi * x) / Real.pi) ^ 2
  have hs := (summable_inv_sq_add_nat x).mul_left a
  apply hs.congr
  intro n
  dsimp [a]
  rw [vaalerK_add_nat_eq n
    (vaaler_add_nat_ne_zero_of_mem_integerComplement hx n)]
  ring

/-- The shifted squared-sinc series representation of Vaaler's sign approximant. -/
noncomputable def vaalerHShift (x : ℝ) : ℝ :=
  (∑' n : ℕ,
    (vaalerK (x - (n + 1 : ℕ)) -
      vaalerK (x + (n + 1 : ℕ)))) +
    2 * x * vaalerK x

lemma vaalerHShift_eq_vaalerHPos {x : ℝ} (hx0 : 0 < x)
    (hx : (x : ℂ) ∈ Complex.integerComplement) :
    vaalerHShift x = vaalerHPos x := by
  let a : ℝ := (Real.sin (Real.pi * x) / Real.pi) ^ 2
  let A : ℝ :=
    ∑' n : ℕ, 1 / (x - (n + 1 : ℕ)) ^ 2
  let B : ℝ :=
    ∑' n : ℕ, 1 / (x + (n + 1 : ℕ)) ^ 2
  have hsinC := sin_pi_mul_ne_zero hx
  have hsin : Real.sin (Real.pi * x) ≠ 0 := by
    intro h
    apply hsinC
    exact_mod_cast h
  have hKx : vaalerK x = a / x ^ 2 := by
    dsimp [a]
    exact vaalerK_eq hx0.ne'
  have hsubsum :
      (∑' n : ℕ, vaalerK (x - (n + 1 : ℕ))) =
        a * A := by
    dsimp [A]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    dsimp [a]
    rw [vaalerK_sub_nat_eq n
      (vaaler_sub_nat_ne_zero_of_mem_integerComplement hx n)]
    ring
  have haddsum :
      (∑' n : ℕ, vaalerK (x + (n + 1 : ℕ))) =
        a * B := by
    dsimp [B]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    dsimp [a]
    rw [vaalerK_add_nat_eq n
      (vaaler_add_nat_ne_zero_of_mem_integerComplement hx n)]
    ring
  have hdiff :
      (∑' n : ℕ,
        (vaalerK (x - (n + 1 : ℕ)) -
          vaalerK (x + (n + 1 : ℕ)))) =
        a * A - a * B := by
    rw [Summable.tsum_sub (summable_vaalerK_sub hx)
      (summable_vaalerK_add hx), hsubsum, haddsum]
  have hcsc := csc_sq_series_real hx
  have hsumadd :
      (∑' n : ℕ,
        (1 / (x - (n + 1)) ^ 2 +
          1 / (x + (n + 1)) ^ 2)) = A + B := by
    dsimp [A, B]
    simpa only [Nat.cast_add, Nat.cast_one] using
      Summable.tsum_add (summable_inv_sq_sub_nat x)
        (summable_inv_sq_add_nat x)
  rw [hsumadd] at hcsc
  have haCsc :
      a * (Real.pi ^ 2 / Real.sin (Real.pi * x) ^ 2) = 1 := by
    dsimp [a]
    field_simp [Real.pi_ne_zero, hsin]
  have hid : a * (1 / x ^ 2 + A + B) = 1 := by
    rw [show 1 / x ^ 2 + A + B =
      1 / x ^ 2 + (A + B) by ring, ← hcsc]
    exact haCsc
  rw [vaalerHShift, hdiff, hKx]
  dsimp [vaalerHPos, vaalerTail]
  change a * A - a * B + 2 * x * (a / x ^ 2) =
    1 + a * (2 / x - 1 / x ^ 2 - 2 * B)
  field_simp [hx0.ne'] at hid ⊢
  nlinarith

lemma vaalerHShift_eq_vaalerH {x : ℝ} (hx0 : 0 < x)
    (hx : (x : ℂ) ∈ Complex.integerComplement) :
    vaalerHShift x = vaalerH x := by
  rw [vaalerH, if_pos hx0]
  exact vaalerHShift_eq_vaalerHPos hx0 hx

lemma vaalerHShift_neg (x : ℝ) :
    vaalerHShift (-x) = -vaalerHShift x := by
  rw [vaalerHShift, vaalerHShift]
  have hterm : ∀ n : ℕ,
      vaalerK (-x - (n + 1 : ℕ)) -
          vaalerK (-x + (n + 1 : ℕ)) =
        -(vaalerK (x - (n + 1 : ℕ)) -
          vaalerK (x + (n + 1 : ℕ))) := by
    intro n
    rw [show -x - (n + 1 : ℕ) =
        -(x + (n + 1 : ℕ)) by ring,
      show -x + (n + 1 : ℕ) =
        -(x - (n + 1 : ℕ)) by ring,
      vaalerK_even, vaalerK_even]
    ring
  simp_rw [hterm]
  rw [tsum_neg, vaalerK_even]
  ring_nf

lemma vaaler_neg_mem_integerComplement {x : ℝ}
    (hx : (x : ℂ) ∈ Complex.integerComplement) :
    ((-x : ℝ) : ℂ) ∈ Complex.integerComplement := by
  rw [Complex.mem_integerComplement_iff] at hx ⊢
  rintro ⟨n, hn⟩
  apply hx
  refine ⟨-n, ?_⟩
  simpa using congrArg Neg.neg hn

lemma vaalerHShift_zero : vaalerHShift 0 = 0 := by
  have hz : (fun n : ℕ =>
      vaalerK ((0 : ℝ) - (n + 1 : ℕ)) -
        vaalerK ((0 : ℝ) + (n + 1 : ℕ))) = 0 := by
    funext n
    simp only [Pi.zero_apply]
    rw [show (0 : ℝ) - (n + 1 : ℕ) =
      -(((n + 1 : ℕ) : ℝ)) by ring, vaalerK_even]
    ring
  rw [vaalerHShift, hz]
  change (∑' _ : ℕ, (0 : ℝ)) + 2 * 0 * vaalerK 0 = 0
  rw [tsum_zero]
  ring

lemma vaalerHShift_eq_vaalerH_of_mem_integerComplement {x : ℝ}
    (hx : (x : ℂ) ∈ Complex.integerComplement) :
    vaalerHShift x = vaalerH x := by
  rcases lt_trichotomy x 0 with hx0 | rfl | hx0
  · have hpos := vaalerHShift_eq_vaalerH (neg_pos.mpr hx0)
      (vaaler_neg_mem_integerComplement hx)
    have hneg := congrArg Neg.neg hpos
    calc
      vaalerHShift x = -vaalerHShift (-x) := by
        rw [vaalerHShift_neg]
        ring
      _ = -vaalerH (-x) := hneg
      _ = vaalerH x := by
        rw [vaalerH_odd]
        ring
  · rw [vaalerHShift_zero]
    simp [vaalerH]
  · exact vaalerHShift_eq_vaalerH hx0 hx

lemma vaalerK_intCast (k : ℤ) :
    vaalerK (k : ℝ) = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · subst k
    simp [vaalerK]
  · rw [if_neg hk, vaalerK, Real.sinc_of_ne_zero]
    · rw [show Real.pi * (k : ℝ) =
        (k : ℝ) * Real.pi by ring, Real.sin_int_mul_pi]
      simp
    · exact mul_ne_zero Real.pi_ne_zero (by exact_mod_cast hk)

lemma vaalerK_posNat (m : ℕ) :
    vaalerK (m + 1 : ℕ) = 0 := by
  rw [show ((m + 1 : ℕ) : ℝ) =
      (((m + 1 : ℕ) : ℤ) : ℝ) by norm_cast,
    vaalerK_intCast]
  have h : (((m + 1 : ℕ) : ℤ) ≠ 0) := by omega
  rw [if_neg h]

lemma vaalerK_nat_sub_nat (m n : ℕ) :
    vaalerK (((m + 1 : ℕ) : ℝ) - (n + 1 : ℕ)) =
      if n = m then 1 else 0 := by
  rw [show ((m + 1 : ℕ) : ℝ) - (n + 1 : ℕ) =
      (((m + 1 : ℕ) : ℤ) -
        ((n + 1 : ℕ) : ℤ) : ℤ) by norm_cast,
    vaalerK_intCast]
  by_cases hnm : n = m
  · subst n
    have hd :
        (((m + 1 : ℕ) : ℤ) -
          ((m + 1 : ℕ) : ℤ)) = 0 := by ring
    rw [if_pos hd, if_pos rfl]
  · have hd :
        (((m + 1 : ℕ) : ℤ) -
          ((n + 1 : ℕ) : ℤ)) ≠ 0 := by omega
    rw [if_neg hd, if_neg hnm]

lemma vaalerK_nat_add_nat (m n : ℕ) :
    vaalerK (((m + 1 : ℕ) : ℝ) + (n + 1 : ℕ)) = 0 := by
  rw [show ((m + 1 : ℕ) : ℝ) + (n + 1 : ℕ) =
      (((m + 1 : ℕ) : ℤ) +
        ((n + 1 : ℕ) : ℤ) : ℤ) by norm_cast,
    vaalerK_intCast]
  have h :
      (((m + 1 : ℕ) : ℤ) +
        ((n + 1 : ℕ) : ℤ)) ≠ 0 := by omega
  rw [if_neg h]

lemma vaalerHShift_posNat (m : ℕ) :
    vaalerHShift (m + 1 : ℕ) = 1 := by
  rw [vaalerHShift]
  simp_rw [vaalerK_nat_sub_nat m, vaalerK_nat_add_nat m]
  rw [show (∑' n : ℕ,
      ((if n = m then 1 else 0) - 0 : ℝ)) = 1 by
    simpa using (tsum_ite_eq m (fun _ : ℕ => (1 : ℝ)))]
  rw [vaalerK_posNat]
  ring

lemma vaalerH_posNat (m : ℕ) :
    vaalerH (m + 1 : ℕ) = 1 := by
  rw [vaalerH, if_pos (by positivity)]
  dsimp [vaalerHPos]
  rw [show Real.pi * ((m + 1 : ℕ) : ℝ) =
      ((m + 1 : ℕ) : ℝ) * Real.pi by ring,
    Real.sin_nat_mul_pi]
  simp

lemma vaalerHShift_eq_vaalerH_intCast (k : ℤ) :
    vaalerHShift (k : ℝ) = vaalerH (k : ℝ) := by
  cases k with
  | ofNat n =>
      cases n with
      | zero =>
          norm_num
          rw [vaalerHShift_zero]
          simp [vaalerH]
      | succ m =>
          change vaalerHShift (((m + 1 : ℕ) : ℝ)) =
            vaalerH (((m + 1 : ℕ) : ℝ))
          rw [vaalerHShift_posNat, vaalerH_posNat]
  | negSucc m =>
      have h : vaalerHShift (-(((m + 1 : ℕ) : ℝ))) =
          vaalerH (-(((m + 1 : ℕ) : ℝ))) := by
        rw [vaalerHShift_neg, vaalerH_odd,
          vaalerHShift_posNat, vaalerH_posNat]
      exact_mod_cast h

lemma vaalerHShift_eq_vaalerH_all (x : ℝ) :
    vaalerHShift x = vaalerH x := by
  by_cases hx : (x : ℂ) ∈ Complex.integerComplement
  · exact vaalerHShift_eq_vaalerH_of_mem_integerComplement hx
  · rw [Complex.mem_integerComplement_iff] at hx
    push Not at hx
    obtain ⟨k, hk⟩ := hx
    have hkR : (k : ℝ) = x := by exact_mod_cast hk
    rw [← hkR]
    exact vaalerHShift_eq_vaalerH_intCast k

lemma summable_vaalerShiftTerm_posNat (m : ℕ) :
    Summable (fun n : ℕ =>
      vaalerK (((m + 1 : ℕ) : ℝ) - (n + 1 : ℕ)) -
        vaalerK (((m + 1 : ℕ) : ℝ) + (n + 1 : ℕ))) := by
  have hfun :
      (fun n : ℕ =>
        vaalerK (((m + 1 : ℕ) : ℝ) - (n + 1 : ℕ)) -
          vaalerK (((m + 1 : ℕ) : ℝ) + (n + 1 : ℕ))) =
        (fun n : ℕ => if n = m then (1 : ℝ) else 0) := by
    funext n
    rw [vaalerK_nat_sub_nat, vaalerK_nat_add_nat]
    split_ifs <;> ring
  rw [hfun]
  exact (hasSum_ite_eq m (1 : ℝ)).summable

lemma summable_vaalerShiftTerm_zero :
    Summable (fun n : ℕ =>
      vaalerK ((0 : ℝ) - (n + 1 : ℕ)) -
        vaalerK ((0 : ℝ) + (n + 1 : ℕ))) := by
  have hfun :
      (fun n : ℕ =>
        vaalerK ((0 : ℝ) - (n + 1 : ℕ)) -
          vaalerK ((0 : ℝ) + (n + 1 : ℕ))) = 0 := by
    funext n
    simp only [Pi.zero_apply]
    rw [show (0 : ℝ) - (n + 1 : ℕ) =
      -(((n + 1 : ℕ) : ℝ)) by ring, vaalerK_even]
    ring
  rw [hfun]
  exact summable_zero

lemma summable_vaalerShiftTerm_neg_posNat (m : ℕ) :
    Summable (fun n : ℕ =>
      vaalerK (-(((m + 1 : ℕ) : ℝ)) - (n + 1 : ℕ)) -
        vaalerK (-(((m + 1 : ℕ) : ℝ)) + (n + 1 : ℕ))) := by
  have hs := (summable_vaalerShiftTerm_posNat m).neg
  apply hs.congr
  intro n
  rw [show -(((m + 1 : ℕ) : ℝ)) - (n + 1 : ℕ) =
      -((((m + 1 : ℕ) : ℝ) + (n + 1 : ℕ))) by ring,
    show -(((m + 1 : ℕ) : ℝ)) + (n + 1 : ℕ) =
      -((((m + 1 : ℕ) : ℝ) - (n + 1 : ℕ))) by ring,
    vaalerK_even, vaalerK_even]
  ring

lemma summable_vaalerShiftTerm_intCast (k : ℤ) :
    Summable (fun n : ℕ =>
      vaalerK ((k : ℝ) - (n + 1 : ℕ)) -
        vaalerK ((k : ℝ) + (n + 1 : ℕ))) := by
  cases k with
  | ofNat n =>
      cases n with
      | zero =>
          simpa using summable_vaalerShiftTerm_zero
      | succ m =>
          change Summable (fun n : ℕ =>
            vaalerK (((m + 1 : ℕ) : ℝ) - (n + 1 : ℕ)) -
              vaalerK (((m + 1 : ℕ) : ℝ) + (n + 1 : ℕ)))
          exact summable_vaalerShiftTerm_posNat m
  | negSucc m =>
      have hs := summable_vaalerShiftTerm_neg_posNat m
      exact_mod_cast hs

lemma summable_vaalerShiftTerm (x : ℝ) :
    Summable (fun n : ℕ =>
      vaalerK (x - (n + 1 : ℕ)) -
        vaalerK (x + (n + 1 : ℕ))) := by
  by_cases hx : (x : ℂ) ∈ Complex.integerComplement
  · exact (summable_vaalerK_sub hx).sub
      (summable_vaalerK_add hx)
  · rw [Complex.mem_integerComplement_iff] at hx
    push Not at hx
    obtain ⟨k, hk⟩ := hx
    have hkR : (k : ℝ) = x := by exact_mod_cast hk
    rw [← hkR]
    exact summable_vaalerShiftTerm_intCast k

/-- The `N`-term truncation of the shifted series for `vaalerH`. -/
noncomputable def vaalerHFin (N : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N,
      (vaalerK (x - (n + 1 : ℕ)) -
        vaalerK (x + (n + 1 : ℕ))) +
    2 * x * vaalerK x

lemma tendsto_vaalerHFin (x : ℝ) :
    Tendsto (fun N : ℕ => vaalerHFin N x) atTop
      (nhds (vaalerH x)) := by
  have hs := summable_vaalerShiftTerm x
  have ht := hs.hasSum.tendsto_sum_nat
  have htc := ht.add_const (2 * x * vaalerK x)
  rw [← vaalerHShift_eq_vaalerH_all x]
  simpa only [vaalerHFin, vaalerHShift] using htc

/-! ## Finite Fourier representations -/

/-- The Fourier oscillation `exp (2π i x t)`. -/
noncomputable def vaalerOsc (x t : ℝ) : ℂ :=
  Complex.exp ((((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) * t)

/-- The finite antisymmetric Dirichlet sum used by the Vaaler kernel. -/
noncomputable def vaalerDirichlet (N : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.range N,
    (vaalerOsc (-((n + 1 : ℕ) : ℝ)) t -
      vaalerOsc (((n + 1 : ℕ) : ℝ)) t)

/-- The finite Fourier kernel representing the truncated Vaaler approximant. -/
noncomputable def vaalerHFinKernel (N : ℕ) (t : ℝ) : ℂ :=
  (((1 - |t| : ℝ) : ℂ) * vaalerDirichlet N t) +
    ((Real.sign t : ℝ) : ℂ) /
      ((Real.pi : ℂ) * Complex.I)

lemma vaalerOsc_add (x y t : ℝ) :
    vaalerOsc (x + y) t = vaalerOsc x t * vaalerOsc y t := by
  rw [vaalerOsc, vaalerOsc, vaalerOsc, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma vaalerOsc_zero (t : ℝ) : vaalerOsc 0 t = 1 := by
  simp [vaalerOsc]

lemma vaalerOsc_neg (x t : ℝ) :
    vaalerOsc (-x) t = (vaalerOsc x t)⁻¹ := by
  rw [vaalerOsc, vaalerOsc, ← Complex.exp_neg]
  congr 1
  push_cast
  ring

lemma continuous_vaalerOsc (x : ℝ) :
    Continuous (vaalerOsc x) := by
  unfold vaalerOsc
  fun_prop

lemma intervalIntegrable_vaalerTriangleOsc (x : ℝ) :
    IntervalIntegrable
      (fun t : ℝ => ((1 - |t| : ℝ) : ℂ) * vaalerOsc x t)
      volume (-1) 1 := by
  apply Continuous.intervalIntegrable
  exact (show Continuous (fun t : ℝ =>
      ((1 - |t| : ℝ) : ℂ)) by fun_prop).mul
    (continuous_vaalerOsc x)

lemma intervalIntegral_vaalerTriangleOsc (x : ℝ) :
    (∫ t : ℝ in -1..1,
      ((1 - |t| : ℝ) : ℂ) * vaalerOsc x t) =
      (vaalerK x : ℂ) := by
  simpa only [vaalerOsc] using
    intervalIntegral_triangle_fourier_eq_vaalerK x

lemma intervalIntegral_vaalerK_shift_sub
    (x : ℝ) (n : ℕ) :
    (∫ t : ℝ in -1..1,
      ((1 - |t| : ℝ) : ℂ) * vaalerOsc x t *
        vaalerOsc (-((n + 1 : ℕ) : ℝ)) t) =
      (vaalerK (x - (n + 1 : ℕ)) : ℂ) := by
  rw [← intervalIntegral_vaalerTriangleOsc
    (x - (n + 1 : ℕ))]
  apply intervalIntegral.integral_congr
  intro t _
  change ((1 - |t| : ℝ) : ℂ) * vaalerOsc x t *
      vaalerOsc (-((n + 1 : ℕ) : ℝ)) t =
    ((1 - |t| : ℝ) : ℂ) *
      vaalerOsc (x + -((n + 1 : ℕ) : ℝ)) t
  rw [vaalerOsc_add]
  ring

lemma intervalIntegral_vaalerK_shift_add
    (x : ℝ) (n : ℕ) :
    (∫ t : ℝ in -1..1,
      ((1 - |t| : ℝ) : ℂ) * vaalerOsc x t *
        vaalerOsc (((n + 1 : ℕ) : ℝ)) t) =
      (vaalerK (x + (n + 1 : ℕ)) : ℂ) := by
  rw [← intervalIntegral_vaalerTriangleOsc
    (x + (n + 1 : ℕ))]
  apply intervalIntegral.integral_congr
  intro t _
  change ((1 - |t| : ℝ) : ℂ) * vaalerOsc x t *
      vaalerOsc (((n + 1 : ℕ) : ℝ)) t =
    ((1 - |t| : ℝ) : ℂ) *
      vaalerOsc (x + ((n + 1 : ℕ) : ℝ)) t
  rw [vaalerOsc_add]
  ring

lemma intervalIntegrable_vaalerK_shift_factor
    (x y : ℝ) :
    IntervalIntegrable
      (fun t : ℝ =>
        ((1 - |t| : ℝ) : ℂ) * vaalerOsc x t *
          vaalerOsc y t)
      volume (-1) 1 := by
  apply Continuous.intervalIntegrable
  exact ((show Continuous (fun t : ℝ =>
      ((1 - |t| : ℝ) : ℂ)) by fun_prop).mul
        (continuous_vaalerOsc x)).mul
    (continuous_vaalerOsc y)

lemma intervalIntegral_vaalerK_shift_diff
    (x : ℝ) (n : ℕ) :
    (∫ t : ℝ in -1..1,
      ((1 - |t| : ℝ) : ℂ) * vaalerOsc x t *
        (vaalerOsc (-((n + 1 : ℕ) : ℝ)) t -
          vaalerOsc (((n + 1 : ℕ) : ℝ)) t)) =
      ((vaalerK (x - (n + 1 : ℕ)) -
        vaalerK (x + (n + 1 : ℕ)) : ℝ) : ℂ) := by
  have hneg := intervalIntegrable_vaalerK_shift_factor
    x (-((n + 1 : ℕ) : ℝ))
  have hpos := intervalIntegrable_vaalerK_shift_factor
    x (((n + 1 : ℕ) : ℝ))
  have hcongr :
      (fun t : ℝ =>
        ((1 - |t| : ℝ) : ℂ) * vaalerOsc x t *
          (vaalerOsc (-((n + 1 : ℕ) : ℝ)) t -
            vaalerOsc (((n + 1 : ℕ) : ℝ)) t)) =
      (fun t : ℝ =>
        ((1 - |t| : ℝ) : ℂ) * vaalerOsc x t *
            vaalerOsc (-((n + 1 : ℕ) : ℝ)) t -
          ((1 - |t| : ℝ) : ℂ) * vaalerOsc x t *
            vaalerOsc (((n + 1 : ℕ) : ℝ)) t) := by
    funext t
    ring
  rw [hcongr, intervalIntegral.integral_sub hneg hpos,
    intervalIntegral_vaalerK_shift_sub,
    intervalIntegral_vaalerK_shift_add]
  push_cast
  rfl

lemma intervalIntegrable_vaalerDirichletPart
    (N : ℕ) (x : ℝ) :
    IntervalIntegrable
      (fun t : ℝ =>
        ((1 - |t| : ℝ) : ℂ) * vaalerOsc x t *
          vaalerDirichlet N t)
      volume (-1) 1 := by
  apply Continuous.intervalIntegrable
  refine ((show Continuous (fun t : ℝ =>
      ((1 - |t| : ℝ) : ℂ)) by fun_prop).mul
        (continuous_vaalerOsc x)).mul ?_
  unfold vaalerDirichlet
  apply continuous_finset_sum
  intro n hn
  exact (continuous_vaalerOsc _).sub (continuous_vaalerOsc _)

lemma intervalIntegral_vaalerDirichletPart
    (N : ℕ) (x : ℝ) :
    (∫ t : ℝ in -1..1,
      ((1 - |t| : ℝ) : ℂ) * vaalerOsc x t *
        vaalerDirichlet N t) =
      ((∑ n ∈ Finset.range N,
        (vaalerK (x - (n + 1 : ℕ)) -
          vaalerK (x + (n + 1 : ℕ))) : ℝ) : ℂ) := by
  let f : ℕ → ℝ → ℂ := fun n t =>
    ((1 - |t| : ℝ) : ℂ) * vaalerOsc x t *
      (vaalerOsc (-((n + 1 : ℕ) : ℝ)) t -
        vaalerOsc (((n + 1 : ℕ) : ℝ)) t)
  have hpoint :
      (fun t : ℝ =>
        ((1 - |t| : ℝ) : ℂ) * vaalerOsc x t *
          vaalerDirichlet N t) =
        (fun t : ℝ => ∑ n ∈ Finset.range N, f n t) := by
    funext t
    dsimp [f, vaalerDirichlet]
    rw [Finset.mul_sum]
  rw [hpoint]
  rw [intervalIntegral.integral_finset_sum]
  · simp_rw [show ∀ n : ℕ,
        (∫ t : ℝ in -1..1, f n t) =
          ((vaalerK (x - (n + 1 : ℕ)) -
            vaalerK (x + (n + 1 : ℕ)) : ℝ) : ℂ) by
        intro n
        exact intervalIntegral_vaalerK_shift_diff x n]
    push_cast
    rfl
  · intro n hn
    dsimp [f]
    have hneg := intervalIntegrable_vaalerK_shift_factor
      x (-((n + 1 : ℕ) : ℝ))
    have hpos := intervalIntegrable_vaalerK_shift_factor
      x (((n + 1 : ℕ) : ℝ))
    refine IntervalIntegrable.congr ?_ (hneg.sub hpos)
    intro t _
    ring

lemma intervalIntegrable_vaalerSign :
    IntervalIntegrable
      (fun t : ℝ => ((Real.sign t : ℝ) : ℂ))
      volume (-1) 1 := by
  let f : ℝ → ℂ := fun t => ((Real.sign t : ℝ) : ℂ)
  let fn : ℝ → ℂ := fun _ => -1
  let fp : ℝ → ℂ := fun _ => 1
  have hn_ae :
      f =ᵐ[volume.restrict (uIoc (-1) 0)] fn := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc,
      (volume.restrict (uIoc (-1) 0)).ae_ne 0] with t ht ht0
    norm_num at ht
    have htle : t ≤ 0 := ht.2
    have htneg : t < 0 := lt_of_le_of_ne htle ht0
    simp [f, fn, Real.sign_of_neg htneg]
  have hp_ae :
      f =ᵐ[volume.restrict (uIoc 0 1)] fp := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc,
      (volume.restrict (uIoc 0 1)).ae_ne 0] with t ht ht0
    norm_num at ht
    have htle : 0 ≤ t := le_of_lt ht.1
    have htpos : 0 < t := lt_of_le_of_ne htle (Ne.symm ht0)
    simp [f, fp, Real.sign_of_pos htpos]
  have hn : IntervalIntegrable f volume (-1) 0 := by
    apply IntervalIntegrable.congr_ae
      (show IntervalIntegrable fn volume (-1) 0 by
        apply Continuous.intervalIntegrable
        fun_prop)
    exact hn_ae.symm
  have hp : IntervalIntegrable f volume 0 1 := by
    apply IntervalIntegrable.congr_ae
      (show IntervalIntegrable fp volume 0 1 by
        apply Continuous.intervalIntegrable
        fun_prop)
    exact hp_ae.symm
  exact hn.trans hp

lemma intervalIntegrable_vaalerSignOsc (x : ℝ) :
    IntervalIntegrable
      (fun t : ℝ =>
        ((Real.sign t : ℝ) : ℂ) * vaalerOsc x t)
      volume (-1) 1 := by
  exact intervalIntegrable_vaalerSign.mul_continuousOn
    (continuous_vaalerOsc x).continuousOn

lemma intervalIntegrable_vaalerSignPart (x : ℝ) :
    IntervalIntegrable
      (fun t : ℝ =>
        vaalerOsc x t *
          (((Real.sign t : ℝ) : ℂ) /
            ((Real.pi : ℂ) * Complex.I)))
      volume (-1) 1 := by
  have h := (intervalIntegrable_vaalerSignOsc x).mul_const
    (((Real.pi : ℂ) * Complex.I)⁻¹)
  apply IntervalIntegrable.congr ?_ h
  intro t _
  simp only [div_eq_mul_inv]
  ring

lemma intervalIntegral_vaalerSignPart (x : ℝ) :
    (∫ t : ℝ in -1..1,
      vaalerOsc x t *
        (((Real.sign t : ℝ) : ℂ) /
          ((Real.pi : ℂ) * Complex.I))) =
      ((2 * x * vaalerK x : ℝ) : ℂ) := by
  let d : ℂ := (Real.pi : ℂ) * Complex.I
  have hd : d ≠ 0 := by
    exact mul_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
      Complex.I_ne_zero
  have hfun :
      (fun t : ℝ =>
        vaalerOsc x t *
          (((Real.sign t : ℝ) : ℂ) /
            ((Real.pi : ℂ) * Complex.I))) =
      (fun t : ℝ =>
        (((Real.sign t : ℝ) : ℂ) * vaalerOsc x t) *
          d⁻¹) := by
    funext t
    dsimp [d]
    simp only [div_eq_mul_inv]
    ring
  rw [hfun, intervalIntegral.integral_mul_const]
  have hsign := intervalIntegral_sign_fourier_eq_vaalerK x
  change
    ((∫ t : ℝ in -1..1,
      ((Real.sign t : ℝ) : ℂ) * vaalerOsc x t) * d⁻¹) =
      ((2 * x * vaalerK x : ℝ) : ℂ)
  rw [show (∫ t : ℝ in -1..1,
      ((Real.sign t : ℝ) : ℂ) * vaalerOsc x t) =
      (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) *
        (vaalerK x : ℂ) by
      simpa only [vaalerOsc] using hsign]
  dsimp [d]
  field_simp [Real.pi_ne_zero, Complex.I_ne_zero]
  push_cast
  ring

lemma intervalIntegral_vaalerHFinKernel (N : ℕ) (x : ℝ) :
    (∫ t : ℝ in -1..1,
      vaalerOsc x t * vaalerHFinKernel N t) =
      (vaalerHFin N x : ℂ) := by
  have hdir := intervalIntegrable_vaalerDirichletPart N x
  have hsign := intervalIntegrable_vaalerSignPart x
  have hcongr :
      (fun t : ℝ =>
        vaalerOsc x t * vaalerHFinKernel N t) =
      (fun t : ℝ =>
        ((1 - |t| : ℝ) : ℂ) * vaalerOsc x t *
            vaalerDirichlet N t +
          vaalerOsc x t *
            (((Real.sign t : ℝ) : ℂ) /
              ((Real.pi : ℂ) * Complex.I))) := by
    funext t
    dsimp [vaalerHFinKernel]
    ring
  rw [hcongr, intervalIntegral.integral_add hdir hsign,
    intervalIntegral_vaalerDirichletPart,
    intervalIntegral_vaalerSignPart]
  dsimp [vaalerHFin]
  push_cast
  rfl

lemma vaalerOsc_eq_cos_add_sin_mul_I (x t : ℝ) :
    vaalerOsc x t =
      (Real.cos (2 * Real.pi * x * t) : ℂ) +
        (Real.sin (2 * Real.pi * x * t) : ℂ) * Complex.I := by
  rw [vaalerOsc]
  rw [show ((((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) * t) =
      ((2 * Real.pi * x * t : ℝ) : ℂ) * Complex.I by
        push_cast
        ring]
  rw [Complex.exp_mul_I]
  simp

lemma vaalerOsc_neg_sub_vaalerOsc (x t : ℝ) :
    vaalerOsc (-x) t - vaalerOsc x t =
      -2 * Complex.I *
        (Real.sin (2 * Real.pi * x * t) : ℂ) := by
  rw [vaalerOsc_eq_cos_add_sin_mul_I,
    vaalerOsc_eq_cos_add_sin_mul_I]
  rw [show 2 * Real.pi * -x * t =
      -(2 * Real.pi * x * t) by ring,
    Real.cos_neg, Real.sin_neg]
  push_cast
  ring

lemma vaalerDirichlet_succ (N : ℕ) (t : ℝ) :
    vaalerDirichlet (N + 1) t =
      vaalerDirichlet N t +
        (vaalerOsc (-((N + 1 : ℕ) : ℝ)) t -
          vaalerOsc (((N + 1 : ℕ) : ℝ)) t) := by
  unfold vaalerDirichlet
  rw [Finset.sum_range_succ]

lemma vaalerDirichlet_eq_cot_add_remainder
    (N : ℕ) {t : ℝ} (hsin : Real.sin (Real.pi * t) ≠ 0) :
    vaalerDirichlet N t =
      -Complex.I * (Real.cot (Real.pi * t) : ℂ) +
        Complex.I *
          ((Real.cos (((2 * N + 1 : ℕ) : ℝ) * Real.pi * t) /
            Real.sin (Real.pi * t) : ℝ) : ℂ) := by
  induction N with
  | zero =>
      simp [vaalerDirichlet, Real.cot_eq_cos_div_sin]
  | succ N ih =>
      rw [vaalerDirichlet_succ, ih,
        vaalerOsc_neg_sub_vaalerOsc]
      rw [Real.cot_eq_cos_div_sin]
      let A : ℝ :=
        (((2 * (N + 1) + 1 : ℕ) : ℝ) * Real.pi * t)
      let B : ℝ :=
        (((2 * N + 1 : ℕ) : ℝ) * Real.pi * t)
      have hA :
          (((2 * (N + 1) + 1 : ℕ) : ℝ) * Real.pi * t) = A := rfl
      have hB :
          (((2 * N + 1 : ℕ) : ℝ) * Real.pi * t) = B := rfl
      rw [hA, hB]
      have havg :
          (A + B) / 2 =
            2 * Real.pi * ((N + 1 : ℕ) : ℝ) * t := by
        dsimp [A, B]
        push_cast
        ring
      have hdiff :
          (A - B) / 2 = Real.pi * t := by
        dsimp [A, B]
        push_cast
        ring
      have hcos := Real.cos_sub_cos A B
      rw [havg, hdiff] at hcos
      have hratio :
          Real.cos A / Real.sin (Real.pi * t) -
              Real.cos B / Real.sin (Real.pi * t) =
            -2 *
              Real.sin
                (2 * Real.pi * ((N + 1 : ℕ) : ℝ) * t) := by
        rw [← sub_div, hcos]
        field_simp [hsin]
      have heqR :
          Real.cos A / Real.sin (Real.pi * t) =
            Real.cos B / Real.sin (Real.pi * t) +
              (-2 *
                Real.sin
                  (2 * Real.pi * ((N + 1 : ℕ) : ℝ) * t)) := by
        linarith only [hratio]
      rw [heqR]
      push_cast
      ring

lemma norm_vaalerOsc (x t : ℝ) :
    ‖vaalerOsc x t‖ = 1 := by
  rw [vaalerOsc, Complex.norm_exp]
  simp

lemma measurable_real_sign : Measurable Real.sign := by
  unfold Real.sign
  apply Measurable.ite
  · exact measurableSet_Iio
  · exact measurable_const
  · apply Measurable.ite
    · exact measurableSet_Ioi
    · exact measurable_const
    · exact measurable_const

lemma abs_real_sign_le_one (x : ℝ) :
    |Real.sign x| ≤ 1 := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · simp [Real.sign_of_neg hx]
  · simp
  · simp [Real.sign_of_pos hx]

lemma continuous_vaalerDirichlet (N : ℕ) :
    Continuous (vaalerDirichlet N) := by
  unfold vaalerDirichlet
  apply continuous_finset_sum
  intro n hn
  exact (continuous_vaalerOsc _).sub (continuous_vaalerOsc _)

lemma measurable_vaalerHFinKernel (N : ℕ) :
    Measurable (vaalerHFinKernel N) := by
  unfold vaalerHFinKernel
  exact (((show Continuous (fun t : ℝ =>
      ((1 - |t| : ℝ) : ℂ)) by fun_prop).measurable.mul
        (continuous_vaalerDirichlet N).measurable).add
      (((Complex.continuous_ofReal.measurable.comp
        measurable_real_sign).div measurable_const)))

lemma norm_vaalerDirichlet_le (N : ℕ) (t : ℝ) :
    ‖vaalerDirichlet N t‖ ≤ 2 * N := by
  unfold vaalerDirichlet
  calc
    ‖∑ n ∈ Finset.range N,
        (vaalerOsc (-((n + 1 : ℕ) : ℝ)) t -
          vaalerOsc (((n + 1 : ℕ) : ℝ)) t)‖
        ≤ ∑ n ∈ Finset.range N,
          ‖vaalerOsc (-((n + 1 : ℕ) : ℝ)) t -
            vaalerOsc (((n + 1 : ℕ) : ℝ)) t‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.range N, (2 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      calc
        ‖vaalerOsc (-((n + 1 : ℕ) : ℝ)) t -
            vaalerOsc (((n + 1 : ℕ) : ℝ)) t‖
            ≤ ‖vaalerOsc (-((n + 1 : ℕ) : ℝ)) t‖ +
              ‖vaalerOsc (((n + 1 : ℕ) : ℝ)) t‖ :=
          norm_sub_le _ _
        _ = 2 := by rw [norm_vaalerOsc, norm_vaalerOsc]; norm_num
    _ = 2 * N := by simp; ring

lemma norm_vaalerHFinKernel_le (N : ℕ) {t : ℝ}
    (ht : t ∈ uIcc (-1) 1) :
    ‖vaalerHFinKernel N t‖ ≤ 2 * N + 1 := by
  have ht' : -1 ≤ t ∧ t ≤ 1 := by
    simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      mem_Icc] using ht
  have habst : |t| ≤ 1 := (abs_le).2 ht'
  have htri0 : 0 ≤ 1 - |t| := sub_nonneg.mpr habst
  have htri :
      ‖((1 - |t| : ℝ) : ℂ)‖ ≤ 1 := by
    rw [norm_real, Real.norm_eq_abs, abs_of_nonneg htri0]
    nlinarith [abs_nonneg t]
  have hfirst :
      ‖((1 - |t| : ℝ) : ℂ) * vaalerDirichlet N t‖ ≤
        2 * N := by
    rw [norm_mul]
    calc
      ‖((1 - |t| : ℝ) : ℂ)‖ * ‖vaalerDirichlet N t‖
          ≤ 1 * (2 * N) := mul_le_mul htri
            (norm_vaalerDirichlet_le N t) (norm_nonneg _) (by norm_num)
      _ = 2 * N := by ring
  have hsecond :
      ‖((Real.sign t : ℝ) : ℂ) /
          ((Real.pi : ℂ) * Complex.I)‖ ≤ 1 := by
    simp only [norm_div, norm_mul, norm_real, norm_I,
      Real.norm_eq_abs, mul_one]
    rw [abs_of_pos Real.pi_pos]
    calc
      |Real.sign t| / Real.pi ≤ 1 / Real.pi :=
        div_le_div_of_nonneg_right (abs_real_sign_le_one t)
          Real.pi_pos.le
      _ ≤ 1 := by
        exact (div_le_one Real.pi_pos).2
          (by nlinarith [Real.pi_gt_three])
  unfold vaalerHFinKernel
  calc
    ‖((1 - |t| : ℝ) : ℂ) * vaalerDirichlet N t +
        ((Real.sign t : ℝ) : ℂ) /
          ((Real.pi : ℂ) * Complex.I)‖
        ≤ ‖((1 - |t| : ℝ) : ℂ) * vaalerDirichlet N t‖ +
          ‖((Real.sign t : ℝ) : ℂ) /
            ((Real.pi : ℂ) * Complex.I)‖ := norm_add_le _ _
    _ ≤ 2 * N + 1 := add_le_add hfirst hsecond

lemma integral_vaalerOsc_sub
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (a t : ℝ) :
    (∫ y : ℝ, vaalerOsc (y - a) t ∂μ) =
      vaalerOsc (-a) t * charFun μ (2 * Real.pi * t) := by
  have hfun :
      (fun y : ℝ => vaalerOsc (y - a) t) =
        (fun y : ℝ => vaalerOsc y t * vaalerOsc (-a) t) := by
    funext y
    rw [show y - a = y + -a by ring, vaalerOsc_add]
  rw [hfun, MeasureTheory.integral_mul_const]
  have hchar :
      (∫ y : ℝ, vaalerOsc y t ∂μ) =
        charFun μ (2 * Real.pi * t) := by
    rw [charFun_apply_real]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with y
    unfold vaalerOsc
    congr 1
    push_cast
    ring
  rw [hchar]
  ring

lemma integrable_vaalerFourierProduct
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (N : ℕ) (a : ℝ) :
    Integrable
      (Function.uncurry (fun t y : ℝ =>
        vaalerOsc (y - a) t * vaalerHFinKernel N t))
      ((volume.restrict (uIoc (-1 : ℝ) (1 : ℝ))).prod μ) := by
  letI : IsFiniteMeasure
      (volume.restrict (uIoc (-1 : ℝ) (1 : ℝ))) := by
    rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    infer_instance
  letI : IsFiniteMeasure
      ((volume.restrict (uIoc (-1 : ℝ) (1 : ℝ))).prod μ) :=
    inferInstance
  let f : ℝ × ℝ → ℂ := fun z =>
    vaalerOsc (z.2 - a) z.1 * vaalerHFinKernel N z.1
  have hosc : Measurable (fun z : ℝ × ℝ =>
      vaalerOsc (z.2 - a) z.1) := by
    apply Continuous.measurable
    unfold vaalerOsc
    fun_prop
  have hf : Measurable f := by
    exact hosc.mul
      ((measurable_vaalerHFinKernel N).comp measurable_fst)
  refine Integrable.mono'
    (integrable_const (2 * (N : ℝ) + 1 : ℝ))
    hf.aestronglyMeasurable ?_
  have hp : MeasurableSet {z : ℝ × ℝ |
      ‖f z‖ ≤ 2 * (N : ℝ) + 1} :=
    measurableSet_le hf.norm measurable_const
  apply (Measure.ae_prod_iff_ae_ae hp).2
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
  filter_upwards with y
  dsimp [f]
  rw [norm_mul, norm_vaalerOsc, one_mul]
  exact norm_vaalerHFinKernel_le N (uIoc_subset_uIcc ht)

lemma integral_vaalerHFin_sub_fourier
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (N : ℕ) (a : ℝ) :
    ((∫ y : ℝ, vaalerHFin N (y - a) ∂μ : ℝ) : ℂ) =
      ∫ t : ℝ in -1..1,
        vaalerOsc (-a) t * charFun μ (2 * Real.pi * t) *
          vaalerHFinKernel N t := by
  let f : ℝ → ℝ → ℂ := fun t y =>
    vaalerOsc (y - a) t * vaalerHFinKernel N t
  have hf : Integrable (Function.uncurry f)
      ((volume.restrict (uIoc (-1 : ℝ) (1 : ℝ))).prod μ) := by
    simpa only [f] using integrable_vaalerFourierProduct μ N a
  have hswap := intervalIntegral_integral_swap hf
  calc
    ((∫ y : ℝ, vaalerHFin N (y - a) ∂μ : ℝ) : ℂ) =
        ∫ y : ℝ, (vaalerHFin N (y - a) : ℂ) ∂μ := by
      rw [integral_complex_ofReal]
    _ = ∫ y : ℝ, (∫ t : ℝ in -1..1, f t y) ∂μ := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with y
      dsimp [f]
      rw [intervalIntegral_vaalerHFinKernel]
    _ = ∫ t : ℝ in -1..1, (∫ y : ℝ, f t y ∂μ) := hswap.symm
    _ = ∫ t : ℝ in -1..1,
        vaalerOsc (-a) t * charFun μ (2 * Real.pi * t) *
          vaalerHFinKernel N t := by
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp [f]
      rw [MeasureTheory.integral_mul_const,
        integral_vaalerOsc_sub]

lemma intervalIntegrable_vaalerCharKernel
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (N : ℕ) (a : ℝ) :
    IntervalIntegrable
      (fun t : ℝ =>
        vaalerOsc (-a) t * charFun μ (2 * Real.pi * t) *
          vaalerHFinKernel N t)
      volume (-1) 1 := by
  let f : ℝ → ℝ → ℂ := fun t y =>
    vaalerOsc (y - a) t * vaalerHFinKernel N t
  have hf : Integrable (Function.uncurry f)
      ((volume.restrict (uIoc (-1 : ℝ) (1 : ℝ))).prod μ) := by
    simpa only [f] using integrable_vaalerFourierProduct μ N a
  have hi :
      Integrable (fun t : ℝ => ∫ y : ℝ, f t y ∂μ)
        (volume.restrict (uIoc (-1 : ℝ) (1 : ℝ))) :=
    hf.integral_prod_left
  rw [intervalIntegrable_iff]
  apply Integrable.congr hi
  filter_upwards with t
  dsimp [f]
  rw [MeasureTheory.integral_mul_const,
    integral_vaalerOsc_sub]

lemma integral_vaalerHFin_sub_difference_fourier
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (N : ℕ) (a : ℝ) :
    (((∫ y : ℝ, vaalerHFin N (y - a) ∂μ) -
        ∫ y : ℝ, vaalerHFin N (y - a) ∂ν : ℝ) : ℂ) =
      ∫ t : ℝ in -1..1,
        vaalerOsc (-a) t *
          (charFun μ (2 * Real.pi * t) -
            charFun ν (2 * Real.pi * t)) *
          vaalerHFinKernel N t := by
  have hμ := integral_vaalerHFin_sub_fourier μ N a
  have hν := integral_vaalerHFin_sub_fourier ν N a
  have hiμ := intervalIntegrable_vaalerCharKernel μ N a
  have hiν := intervalIntegrable_vaalerCharKernel ν N a
  rw [ofReal_sub, hμ, hν]
  rw [← intervalIntegral.integral_sub hiμ hiν]
  apply intervalIntegral.integral_congr
  intro t ht
  ring

/-! ## Pointwise cdf-step bounds -/

/-- The two-valued step function equal to `1` on `y ≤ a` and `-1` otherwise. -/
noncomputable def vaalerCdfStep (a y : ℝ) : ℝ :=
  if y ≤ a then 1 else -1

lemma vaalerCdfStep_bounds (a y : ℝ) :
    -vaalerH (y - a) - vaalerK (y - a) ≤
        vaalerCdfStep a y ∧
      vaalerCdfStep a y ≤
        -vaalerH (y - a) + vaalerK (y - a) := by
  rcases lt_trichotomy y a with hya | hya | hya
  · have hsign : Real.sign (y - a) = -1 :=
      Real.sign_of_neg (sub_neg.mpr hya)
    have henv := abs_sign_sub_vaalerH_le (y - a)
    rw [hsign, abs_le] at henv
    simp only [vaalerCdfStep, if_pos hya.le]
    constructor <;> linarith
  · subst y
    simp [vaalerCdfStep, vaalerH, vaalerK]
  · have hsign : Real.sign (y - a) = 1 :=
      Real.sign_of_pos (sub_pos.mpr hya)
    have henv := abs_sign_sub_vaalerH_le (y - a)
    rw [hsign, abs_le] at henv
    simp only [vaalerCdfStep, if_neg (not_le.mpr hya)]
    constructor <;> linarith

lemma continuous_vaalerK : Continuous vaalerK := by
  unfold vaalerK
  fun_prop

lemma measurable_vaalerH : Measurable vaalerH := by
  have hsum : Measurable (fun x : ℝ =>
      ∑' n : ℕ,
        (vaalerK (x - (n + 1 : ℕ)) -
          vaalerK (x + (n + 1 : ℕ)))) := by
    apply Measurable.tsum
    intro n
    exact (continuous_vaalerK.comp
      (show Continuous (fun x : ℝ =>
        x - (n + 1 : ℕ)) by fun_prop)).measurable.sub
      (continuous_vaalerK.comp
        (show Continuous (fun x : ℝ =>
          x + (n + 1 : ℕ)) by fun_prop)).measurable
  have hshift : Measurable vaalerHShift := by
    unfold vaalerHShift
    exact hsum.add
      (((measurable_const.mul measurable_id).mul
        continuous_vaalerK.measurable))
  have heq : vaalerH = vaalerHShift := by
    funext x
    exact (vaalerHShift_eq_vaalerH_all x).symm
  rw [heq]
  exact hshift

lemma vaalerK_le_one (x : ℝ) : vaalerK x ≤ 1 := by
  have h := Real.abs_sinc_le_one (Real.pi * x)
  have h0 := abs_nonneg (Real.sinc (Real.pi * x))
  have hsq := sq_abs (Real.sinc (Real.pi * x))
  dsimp [vaalerK]
  nlinarith

lemma abs_vaalerH_le_two (x : ℝ) :
    |vaalerH x| ≤ 2 := by
  have henv := abs_sign_sub_vaalerH_le x
  have hk := vaalerK_le_one x
  calc
    |vaalerH x| =
        |Real.sign x - (Real.sign x - vaalerH x)| := by
      congr 1
      ring
    _ ≤ |Real.sign x| +
        |Real.sign x - vaalerH x| := abs_sub _ _
    _ ≤ 1 + 1 := add_le_add (abs_real_sign_le_one x)
      (henv.trans hk)
    _ = 2 := by norm_num

lemma integrable_vaalerK (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable vaalerK μ := by
  refine Integrable.mono' (integrable_const (1 : ℝ))
    continuous_vaalerK.measurable.aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (vaalerK_nonneg x)]
  exact vaalerK_le_one x

lemma integrable_vaalerH (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable vaalerH μ := by
  refine Integrable.mono' (integrable_const (2 : ℝ))
    measurable_vaalerH.aestronglyMeasurable ?_
  filter_upwards with x
  simpa only [Real.norm_eq_abs] using abs_vaalerH_le_two x

lemma integrable_vaalerK_sub (μ : Measure ℝ) [IsFiniteMeasure μ]
    (a : ℝ) :
    Integrable (fun y : ℝ => vaalerK (y - a)) μ := by
  have hm : Measurable (fun y : ℝ => vaalerK (y - a)) :=
    (continuous_vaalerK.comp
      (show Continuous (fun y : ℝ => y - a) by fun_prop)).measurable
  refine Integrable.mono' (integrable_const (1 : ℝ))
    hm.aestronglyMeasurable ?_
  filter_upwards with y
  rw [Real.norm_eq_abs,
    abs_of_nonneg (vaalerK_nonneg (y - a))]
  exact vaalerK_le_one (y - a)

lemma integrable_vaalerH_sub (μ : Measure ℝ) [IsFiniteMeasure μ]
    (a : ℝ) :
    Integrable (fun y : ℝ => vaalerH (y - a)) μ := by
  have hm : Measurable (fun y : ℝ => vaalerH (y - a)) :=
    measurable_vaalerH.comp
      (show Measurable (fun y : ℝ => y - a) by fun_prop)
  refine Integrable.mono' (integrable_const (2 : ℝ))
    hm.aestronglyMeasurable ?_
  filter_upwards with y
  simpa only [Real.norm_eq_abs] using abs_vaalerH_le_two (y - a)

lemma measurable_vaalerCdfStep (a : ℝ) :
    Measurable (vaalerCdfStep a) := by
  unfold vaalerCdfStep
  exact Measurable.ite
    (measurableSet_le measurable_id measurable_const)
    measurable_const measurable_const

lemma integrable_vaalerCdfStep (μ : Measure ℝ) [IsFiniteMeasure μ]
    (a : ℝ) :
    Integrable (vaalerCdfStep a) μ := by
  refine Integrable.mono' (integrable_const (1 : ℝ))
    (measurable_vaalerCdfStep a).aestronglyMeasurable ?_
  filter_upwards with y
  simp only [vaalerCdfStep]
  split_ifs <;> simp

lemma integral_vaalerCdfStep_eq (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a : ℝ) :
    ∫ y : ℝ, vaalerCdfStep a y ∂μ = 2 * cdf μ a - 1 := by
  have hfun :
      vaalerCdfStep a =
        fun y : ℝ => 2 * (Iic a).indicator (1 : ℝ → ℝ) y - 1 := by
    funext y
    by_cases hy : y ≤ a
    · norm_num [vaalerCdfStep, hy]
    · norm_num [vaalerCdfStep, hy]
  rw [hfun]
  have hind : Integrable ((Iic a).indicator (1 : ℝ → ℝ)) μ :=
    (integrable_const (1 : ℝ)).indicator measurableSet_Iic
  rw [integral_sub (hind.const_mul 2) (integrable_const (1 : ℝ)),
    MeasureTheory.integral_const_mul,
    integral_indicator_one measurableSet_Iic,
    MeasureTheory.integral_const, cdf_eq_real]
  simp only [probReal_univ, one_smul]

lemma cdf_vaaler_lower_bound (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (a : ℝ) :
    -(∫ y : ℝ, vaalerH (y - a) ∂μ) -
        ∫ y : ℝ, vaalerK (y - a) ∂μ ≤
      2 * cdf μ a - 1 := by
  have hH := integrable_vaalerH_sub μ a
  have hK := integrable_vaalerK_sub μ a
  have hstep := integrable_vaalerCdfStep μ a
  have hmono :
      (∫ y : ℝ,
        (-vaalerH (y - a) - vaalerK (y - a)) ∂μ) ≤
        ∫ y : ℝ, vaalerCdfStep a y ∂μ := by
    apply integral_mono (hH.neg.sub hK) hstep
    intro y
    exact (vaalerCdfStep_bounds a y).1
  have hlin :
      (∫ y : ℝ,
        (-vaalerH (y - a) - vaalerK (y - a)) ∂μ) =
        -(∫ y : ℝ, vaalerH (y - a) ∂μ) -
          ∫ y : ℝ, vaalerK (y - a) ∂μ := by
    have hsub :
        (∫ y : ℝ,
          (-vaalerH (y - a) - vaalerK (y - a)) ∂μ) =
          (∫ y : ℝ, -vaalerH (y - a) ∂μ) -
            ∫ y : ℝ, vaalerK (y - a) ∂μ := by
      simpa only [Pi.neg_apply] using integral_sub hH.neg hK
    have hneg :
        (∫ y : ℝ, -vaalerH (y - a) ∂μ) =
          -(∫ y : ℝ, vaalerH (y - a) ∂μ) := by
      simpa only using
        (MeasureTheory.integral_neg
          (μ := μ) (fun y : ℝ => vaalerH (y - a)))
    rw [hsub, hneg]
  calc
    -(∫ y : ℝ, vaalerH (y - a) ∂μ) -
          ∫ y : ℝ, vaalerK (y - a) ∂μ =
        ∫ y : ℝ,
          (-vaalerH (y - a) - vaalerK (y - a)) ∂μ :=
      hlin.symm
    _ ≤ ∫ y : ℝ, vaalerCdfStep a y ∂μ := hmono
    _ = 2 * cdf μ a - 1 := integral_vaalerCdfStep_eq μ a

lemma cdf_vaaler_upper_bound (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (a : ℝ) :
    2 * cdf μ a - 1 ≤
      -(∫ y : ℝ, vaalerH (y - a) ∂μ) +
        ∫ y : ℝ, vaalerK (y - a) ∂μ := by
  have hH := integrable_vaalerH_sub μ a
  have hK := integrable_vaalerK_sub μ a
  have hstep := integrable_vaalerCdfStep μ a
  have hmono :
      (∫ y : ℝ, vaalerCdfStep a y ∂μ) ≤
        ∫ y : ℝ,
          (-vaalerH (y - a) + vaalerK (y - a)) ∂μ := by
    apply integral_mono hstep (hH.neg.add hK)
    intro y
    exact (vaalerCdfStep_bounds a y).2
  have hlin :
      (∫ y : ℝ,
        (-vaalerH (y - a) + vaalerK (y - a)) ∂μ) =
        -(∫ y : ℝ, vaalerH (y - a) ∂μ) +
          ∫ y : ℝ, vaalerK (y - a) ∂μ := by
    have hadd :
        (∫ y : ℝ,
          (-vaalerH (y - a) + vaalerK (y - a)) ∂μ) =
          (∫ y : ℝ, -vaalerH (y - a) ∂μ) +
            ∫ y : ℝ, vaalerK (y - a) ∂μ := by
      simpa only [Pi.neg_apply] using integral_add hH.neg hK
    have hneg :
        (∫ y : ℝ, -vaalerH (y - a) ∂μ) =
          -(∫ y : ℝ, vaalerH (y - a) ∂μ) := by
      simpa only using
        (MeasureTheory.integral_neg
          (μ := μ) (fun y : ℝ => vaalerH (y - a)))
    rw [hadd, hneg]
  calc
    2 * cdf μ a - 1 =
        ∫ y : ℝ, vaalerCdfStep a y ∂μ :=
      (integral_vaalerCdfStep_eq μ a).symm
    _ ≤ ∫ y : ℝ,
      (-vaalerH (y - a) + vaalerK (y - a)) ∂μ := hmono
    _ = -(∫ y : ℝ, vaalerH (y - a) ∂μ) +
        ∫ y : ℝ, vaalerK (y - a) ∂μ := hlin

lemma two_mul_abs_cdf_sub_le_vaaler_integrals
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (a : ℝ) :
    2 * |cdf μ a - cdf ν a| ≤
      |(∫ y : ℝ, vaalerH (y - a) ∂μ) -
        ∫ y : ℝ, vaalerH (y - a) ∂ν| +
      (∫ y : ℝ, vaalerK (y - a) ∂μ) +
        ∫ y : ℝ, vaalerK (y - a) ∂ν := by
  let hμ : ℝ := ∫ y : ℝ, vaalerH (y - a) ∂μ
  let hν : ℝ := ∫ y : ℝ, vaalerH (y - a) ∂ν
  let kμ : ℝ := ∫ y : ℝ, vaalerK (y - a) ∂μ
  let kν : ℝ := ∫ y : ℝ, vaalerK (y - a) ∂ν
  have hμlo := cdf_vaaler_lower_bound μ a
  have hμhi := cdf_vaaler_upper_bound μ a
  have hνlo := cdf_vaaler_lower_bound ν a
  have hνhi := cdf_vaaler_upper_bound ν a
  have habslo : -(abs (hμ - hν)) ≤ hμ - hν :=
    neg_abs_le (hμ - hν)
  have habshi : hμ - hν ≤ abs (hμ - hν) :=
    le_abs_self (hμ - hν)
  dsimp [hμ, hν, kμ, kν] at *
  let d : ℝ := cdf μ a - cdf ν a
  let R : ℝ :=
    |(∫ y : ℝ, vaalerH (y - a) ∂μ) -
        ∫ y : ℝ, vaalerH (y - a) ∂ν| +
      (∫ y : ℝ, vaalerK (y - a) ∂μ) +
        ∫ y : ℝ, vaalerK (y - a) ∂ν
  have hlo : -R ≤ 2 * d := by
    dsimp [R, d]
    linarith
  have hhi : 2 * d ≤ R := by
    dsimp [R, d]
    linarith
  have habs : |2 * d| ≤ R := (abs_le).2 ⟨hlo, hhi⟩
  calc
    2 * |cdf μ a - cdf ν a| = |2 * d| := by
      dsimp [d]
      rw [abs_mul]
      norm_num
    _ ≤ R := habs
    _ = _ := rfl

/-! ## Uniform bounds for the finite cardinal approximants -/

lemma vaalerK_partition_unity_of_mem_integerComplement {x : ℝ}
    (hx : (x : ℂ) ∈ Complex.integerComplement) :
    vaalerK x +
        (∑' n : ℕ, vaalerK (x - (n + 1 : ℕ))) +
      (∑' n : ℕ, vaalerK (x + (n + 1 : ℕ))) = 1 := by
  let a : ℝ := (Real.sin (Real.pi * x) / Real.pi) ^ 2
  let A : ℝ := ∑' n : ℕ, 1 / (x - (n + 1 : ℕ)) ^ 2
  let B : ℝ := ∑' n : ℕ, 1 / (x + (n + 1 : ℕ)) ^ 2
  have hx0 : x ≠ 0 := by
    intro h
    subst x
    rw [Complex.mem_integerComplement_iff] at hx
    exact hx ⟨0, by norm_num⟩
  have hsinC := sin_pi_mul_ne_zero hx
  have hsin : Real.sin (Real.pi * x) ≠ 0 := by
    intro h
    apply hsinC
    exact_mod_cast h
  have hKx : vaalerK x = a / x ^ 2 := by
    dsimp [a]
    exact vaalerK_eq hx0
  have hsubsum :
      (∑' n : ℕ, vaalerK (x - (n + 1 : ℕ))) = a * A := by
    dsimp [A]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    dsimp [a]
    rw [vaalerK_sub_nat_eq n
      (vaaler_sub_nat_ne_zero_of_mem_integerComplement hx n)]
    ring
  have haddsum :
      (∑' n : ℕ, vaalerK (x + (n + 1 : ℕ))) = a * B := by
    dsimp [B]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    dsimp [a]
    rw [vaalerK_add_nat_eq n
      (vaaler_add_nat_ne_zero_of_mem_integerComplement hx n)]
    ring
  have hcsc := csc_sq_series_real hx
  have hsumadd :
      (∑' n : ℕ,
        (1 / (x - (n + 1)) ^ 2 +
          1 / (x + (n + 1)) ^ 2)) = A + B := by
    dsimp [A, B]
    simpa only [Nat.cast_add, Nat.cast_one] using
      Summable.tsum_add (summable_inv_sq_sub_nat x)
        (summable_inv_sq_add_nat x)
  rw [hsumadd] at hcsc
  have haCsc :
      a * (Real.pi ^ 2 / Real.sin (Real.pi * x) ^ 2) = 1 := by
    dsimp [a]
    field_simp [Real.pi_ne_zero, hsin]
  have hid : a * (1 / x ^ 2 + A + B) = 1 := by
    rw [show 1 / x ^ 2 + A + B =
      1 / x ^ 2 + (A + B) by ring, ← hcsc]
    exact haCsc
  rw [hKx, hsubsum, haddsum]
  calc
    a / x ^ 2 + a * A + a * B =
        a * (1 / x ^ 2 + A + B) := by ring
    _ = 1 := hid

lemma vaalerK_partition_unity_intCast (k : ℤ) :
    vaalerK (k : ℝ) +
        (∑' n : ℕ, vaalerK ((k : ℝ) - (n + 1 : ℕ))) +
      (∑' n : ℕ, vaalerK ((k : ℝ) + (n + 1 : ℕ))) = 1 := by
  cases k with
  | ofNat n =>
      cases n with
      | zero =>
          have hsub : (fun n : ℕ =>
              vaalerK ((0 : ℝ) - (n + 1 : ℕ))) = 0 := by
            funext n
            simp only [Pi.zero_apply]
            rw [show (0 : ℝ) - (n + 1 : ℕ) =
              -(((n + 1 : ℕ) : ℝ)) by ring,
              vaalerK_even, vaalerK_posNat]
          have hadd : (fun n : ℕ =>
              vaalerK ((0 : ℝ) + (n + 1 : ℕ))) = 0 := by
            funext n
            simp only [Pi.zero_apply]
            simpa using vaalerK_posNat n
          norm_num only [Int.cast_ofNat]
          rw [hsub, hadd]
          change vaalerK 0 + (∑' _ : ℕ, (0 : ℝ)) +
            (∑' _ : ℕ, (0 : ℝ)) = 1
          rw [tsum_zero]
          simp [vaalerK]
      | succ m =>
          change vaalerK (((m + 1 : ℕ) : ℝ)) +
              (∑' n : ℕ,
                vaalerK (((m + 1 : ℕ) : ℝ) - (n + 1 : ℕ))) +
              (∑' n : ℕ,
                vaalerK (((m + 1 : ℕ) : ℝ) + (n + 1 : ℕ))) = 1
          rw [vaalerK_posNat]
          simp_rw [vaalerK_nat_sub_nat m,
            vaalerK_nat_add_nat m]
          rw [show (∑' n : ℕ,
              (if n = m then (1 : ℝ) else 0)) = 1 by
            simpa using tsum_ite_eq m (fun _ : ℕ => (1 : ℝ))]
          simp
  | negSucc m =>
      have hneg :
          vaalerK (-(((m + 1 : ℕ) : ℝ))) +
              (∑' n : ℕ,
                vaalerK (-(((m + 1 : ℕ) : ℝ)) -
                  (n + 1 : ℕ))) +
              (∑' n : ℕ,
                vaalerK (-(((m + 1 : ℕ) : ℝ)) +
                  (n + 1 : ℕ))) = 1 := by
        rw [vaalerK_even, vaalerK_posNat]
        have hsub : (fun n : ℕ =>
            vaalerK (-(((m + 1 : ℕ) : ℝ)) - (n + 1 : ℕ))) =
            (fun n : ℕ =>
              vaalerK (((m + 1 : ℕ) : ℝ) + (n + 1 : ℕ))) := by
          funext n
          rw [show -(((m + 1 : ℕ) : ℝ)) - (n + 1 : ℕ) =
            -((((m + 1 : ℕ) : ℝ) + (n + 1 : ℕ))) by ring,
            vaalerK_even]
        have hadd : (fun n : ℕ =>
            vaalerK (-(((m + 1 : ℕ) : ℝ)) + (n + 1 : ℕ))) =
            (fun n : ℕ =>
              vaalerK (((m + 1 : ℕ) : ℝ) - (n + 1 : ℕ))) := by
          funext n
          rw [show -(((m + 1 : ℕ) : ℝ)) + (n + 1 : ℕ) =
            -((((m + 1 : ℕ) : ℝ) - (n + 1 : ℕ))) by ring,
            vaalerK_even]
        rw [hsub, hadd]
        simp_rw [vaalerK_nat_add_nat m,
          vaalerK_nat_sub_nat m]
        rw [show (∑' n : ℕ,
            (if n = m then (1 : ℝ) else 0)) = 1 by
          simpa using tsum_ite_eq m (fun _ : ℕ => (1 : ℝ))]
        simp
      exact_mod_cast hneg

lemma vaalerK_partition_unity (x : ℝ) :
    vaalerK x +
        (∑' n : ℕ, vaalerK (x - (n + 1 : ℕ))) +
      (∑' n : ℕ, vaalerK (x + (n + 1 : ℕ))) = 1 := by
  by_cases hx : (x : ℂ) ∈ Complex.integerComplement
  · exact vaalerK_partition_unity_of_mem_integerComplement hx
  · rw [Complex.mem_integerComplement_iff] at hx
    push Not at hx
    obtain ⟨k, hk⟩ := hx
    have hkR : (k : ℝ) = x := by exact_mod_cast hk
    rw [← hkR]
    exact vaalerK_partition_unity_intCast k

lemma summable_vaalerK_sub_posNat (m : ℕ) :
    Summable (fun n : ℕ =>
      vaalerK (((m + 1 : ℕ) : ℝ) - (n + 1 : ℕ))) := by
  have hfun :
      (fun n : ℕ =>
        vaalerK (((m + 1 : ℕ) : ℝ) - (n + 1 : ℕ))) =
        (fun n : ℕ => if n = m then (1 : ℝ) else 0) := by
    funext n
    exact vaalerK_nat_sub_nat m n
  rw [hfun]
  exact (hasSum_ite_eq m (1 : ℝ)).summable

lemma summable_vaalerK_add_posNat (m : ℕ) :
    Summable (fun n : ℕ =>
      vaalerK (((m + 1 : ℕ) : ℝ) + (n + 1 : ℕ))) := by
  have hfun :
      (fun n : ℕ =>
        vaalerK (((m + 1 : ℕ) : ℝ) + (n + 1 : ℕ))) = 0 := by
    funext n
    simp only [Pi.zero_apply]
    exact vaalerK_nat_add_nat m n
  rw [hfun]
  exact summable_zero

lemma summable_vaalerK_sub_zero :
    Summable (fun n : ℕ =>
      vaalerK ((0 : ℝ) - (n + 1 : ℕ))) := by
  have hfun :
      (fun n : ℕ => vaalerK ((0 : ℝ) - (n + 1 : ℕ))) = 0 := by
    funext n
    simp only [Pi.zero_apply]
    rw [show (0 : ℝ) - (n + 1 : ℕ) =
      -(((n + 1 : ℕ) : ℝ)) by ring,
      vaalerK_even, vaalerK_posNat]
  rw [hfun]
  exact summable_zero

lemma summable_vaalerK_add_zero :
    Summable (fun n : ℕ =>
      vaalerK ((0 : ℝ) + (n + 1 : ℕ))) := by
  have hfun :
      (fun n : ℕ => vaalerK ((0 : ℝ) + (n + 1 : ℕ))) = 0 := by
    funext n
    simp only [Pi.zero_apply]
    simpa using vaalerK_posNat n
  rw [hfun]
  exact summable_zero

lemma summable_vaalerK_sub_negPosNat (m : ℕ) :
    Summable (fun n : ℕ =>
      vaalerK (-(((m + 1 : ℕ) : ℝ)) - (n + 1 : ℕ))) := by
  have hs := summable_vaalerK_add_posNat m
  apply hs.congr
  intro n
  rw [show -(((m + 1 : ℕ) : ℝ)) - (n + 1 : ℕ) =
    -((((m + 1 : ℕ) : ℝ) + (n + 1 : ℕ))) by ring,
    vaalerK_even]

lemma summable_vaalerK_add_negPosNat (m : ℕ) :
    Summable (fun n : ℕ =>
      vaalerK (-(((m + 1 : ℕ) : ℝ)) + (n + 1 : ℕ))) := by
  have hs := summable_vaalerK_sub_posNat m
  apply hs.congr
  intro n
  rw [show -(((m + 1 : ℕ) : ℝ)) + (n + 1 : ℕ) =
    -((((m + 1 : ℕ) : ℝ) - (n + 1 : ℕ))) by ring,
    vaalerK_even]

lemma summable_vaalerK_sub_intCast (k : ℤ) :
    Summable (fun n : ℕ =>
      vaalerK ((k : ℝ) - (n + 1 : ℕ))) := by
  cases k with
  | ofNat n =>
      cases n with
      | zero =>
          norm_num only [Int.cast_ofNat]
          exact summable_vaalerK_sub_zero
      | succ m =>
          change Summable (fun n : ℕ =>
            vaalerK (((m + 1 : ℕ) : ℝ) - (n + 1 : ℕ)))
          exact summable_vaalerK_sub_posNat m
  | negSucc m =>
      have hs := summable_vaalerK_sub_negPosNat m
      exact_mod_cast hs

lemma summable_vaalerK_add_intCast (k : ℤ) :
    Summable (fun n : ℕ =>
      vaalerK ((k : ℝ) + (n + 1 : ℕ))) := by
  cases k with
  | ofNat n =>
      cases n with
      | zero =>
          norm_num only [Int.cast_ofNat]
          exact summable_vaalerK_add_zero
      | succ m =>
          change Summable (fun n : ℕ =>
            vaalerK (((m + 1 : ℕ) : ℝ) + (n + 1 : ℕ)))
          exact summable_vaalerK_add_posNat m
  | negSucc m =>
      have hs := summable_vaalerK_add_negPosNat m
      exact_mod_cast hs

lemma summable_vaalerK_sub_all (x : ℝ) :
    Summable (fun n : ℕ =>
      vaalerK (x - (n + 1 : ℕ))) := by
  by_cases hx : (x : ℂ) ∈ Complex.integerComplement
  · exact summable_vaalerK_sub hx
  · rw [Complex.mem_integerComplement_iff] at hx
    push Not at hx
    obtain ⟨k, hk⟩ := hx
    have hkR : (k : ℝ) = x := by exact_mod_cast hk
    rw [← hkR]
    exact summable_vaalerK_sub_intCast k

lemma summable_vaalerK_add_all (x : ℝ) :
    Summable (fun n : ℕ =>
      vaalerK (x + (n + 1 : ℕ))) := by
  by_cases hx : (x : ℂ) ∈ Complex.integerComplement
  · exact summable_vaalerK_add hx
  · rw [Complex.mem_integerComplement_iff] at hx
    push Not at hx
    obtain ⟨k, hk⟩ := hx
    have hkR : (k : ℝ) = x := by exact_mod_cast hk
    rw [← hkR]
    exact summable_vaalerK_add_intCast k

lemma tsum_abs_vaalerShiftTerm_le_one (x : ℝ) :
    (∑' n : ℕ,
      |vaalerK (x - (n + 1 : ℕ)) -
        vaalerK (x + (n + 1 : ℕ))|) ≤ 1 := by
  have hs := summable_vaalerShiftTerm x
  have hsabs : Summable (fun n : ℕ =>
      |vaalerK (x - (n + 1 : ℕ)) -
        vaalerK (x + (n + 1 : ℕ))|) := by
    simpa only [Real.norm_eq_abs] using hs.norm
  have hsub := summable_vaalerK_sub_all x
  have hadd := summable_vaalerK_add_all x
  have hpoint : ∀ n : ℕ,
      |vaalerK (x - (n + 1 : ℕ)) -
        vaalerK (x + (n + 1 : ℕ))| ≤
      vaalerK (x - (n + 1 : ℕ)) +
        vaalerK (x + (n + 1 : ℕ)) := by
    intro n
    calc
      |vaalerK (x - (n + 1 : ℕ)) -
          vaalerK (x + (n + 1 : ℕ))|
          ≤ |vaalerK (x - (n + 1 : ℕ))| +
            |vaalerK (x + (n + 1 : ℕ))| := abs_sub _ _
      _ = vaalerK (x - (n + 1 : ℕ)) +
          vaalerK (x + (n + 1 : ℕ)) := by
        rw [abs_of_nonneg (vaalerK_nonneg _),
          abs_of_nonneg (vaalerK_nonneg _)]
  have hle := hsabs.tsum_le_tsum hpoint (hsub.add hadd)
  rw [Summable.tsum_add hsub hadd] at hle
  have hpart := vaalerK_partition_unity x
  nlinarith [vaalerK_nonneg x]

lemma abs_vaalerShiftPartialSum_le_one (N : ℕ) (x : ℝ) :
    |∑ n ∈ Finset.range N,
      (vaalerK (x - (n + 1 : ℕ)) -
        vaalerK (x + (n + 1 : ℕ)))| ≤ 1 := by
  have hsabs : Summable (fun n : ℕ =>
      |vaalerK (x - (n + 1 : ℕ)) -
        vaalerK (x + (n + 1 : ℕ))|) := by
    simpa only [Real.norm_eq_abs] using
      (summable_vaalerShiftTerm x).norm
  calc
    |∑ n ∈ Finset.range N,
        (vaalerK (x - (n + 1 : ℕ)) -
          vaalerK (x + (n + 1 : ℕ)))|
        ≤ ∑ n ∈ Finset.range N,
          |vaalerK (x - (n + 1 : ℕ)) -
            vaalerK (x + (n + 1 : ℕ))| := by
      simpa only [Real.norm_eq_abs] using
        (norm_sum_le (Finset.range N)
          (fun n => vaalerK (x - (n + 1 : ℕ)) -
            vaalerK (x + (n + 1 : ℕ))))
    _ ≤ ∑' n : ℕ,
        |vaalerK (x - (n + 1 : ℕ)) -
          vaalerK (x + (n + 1 : ℕ))| :=
      hsabs.sum_le_tsum (Finset.range N)
        (fun n hn => abs_nonneg _)
    _ ≤ 1 := tsum_abs_vaalerShiftTerm_le_one x

lemma abs_two_mul_mul_vaalerK_le_three (x : ℝ) :
    |2 * x * vaalerK x| ≤ 3 := by
  have hsum :
      |∑' n : ℕ,
        (vaalerK (x - (n + 1 : ℕ)) -
          vaalerK (x + (n + 1 : ℕ)))| ≤ 1 := by
    calc
      |∑' n : ℕ,
          (vaalerK (x - (n + 1 : ℕ)) -
            vaalerK (x + (n + 1 : ℕ)))|
          ≤ ∑' n : ℕ,
            |vaalerK (x - (n + 1 : ℕ)) -
              vaalerK (x + (n + 1 : ℕ))| := by
        simpa only [Real.norm_eq_abs] using
          norm_tsum_le_tsum_norm
            (show Summable (fun n : ℕ =>
              ‖vaalerK (x - (n + 1 : ℕ)) -
                vaalerK (x + (n + 1 : ℕ))‖) by
              simpa only [Real.norm_eq_abs] using
                (summable_vaalerShiftTerm x).norm)
      _ ≤ 1 := tsum_abs_vaalerShiftTerm_le_one x
  have hEq := vaalerHShift_eq_vaalerH_all x
  unfold vaalerHShift at hEq
  have hH := abs_vaalerH_le_two x
  rw [← hEq] at hH
  have htri :
      |2 * x * vaalerK x| ≤
        |(∑' n : ℕ,
          (vaalerK (x - (n + 1 : ℕ)) -
            vaalerK (x + (n + 1 : ℕ)))) +
          2 * x * vaalerK x| +
        |∑' n : ℕ,
          (vaalerK (x - (n + 1 : ℕ)) -
            vaalerK (x + (n + 1 : ℕ)))| := by
    let S : ℝ := ∑' n : ℕ,
      (vaalerK (x - (n + 1 : ℕ)) -
        vaalerK (x + (n + 1 : ℕ)))
    calc
      |2 * x * vaalerK x| =
          |(S + 2 * x * vaalerK x) - S| := by
        congr 1
        ring
      _ ≤ |S + 2 * x * vaalerK x| + |S| :=
        abs_sub _ _
  linarith

lemma abs_vaalerHFin_le_four (N : ℕ) (x : ℝ) :
    |vaalerHFin N x| ≤ 4 := by
  unfold vaalerHFin
  have hpartial := abs_vaalerShiftPartialSum_le_one N x
  have hbase := abs_two_mul_mul_vaalerK_le_three x
  calc
    |(∑ n ∈ Finset.range N,
        (vaalerK (x - (n + 1 : ℕ)) -
          vaalerK (x + (n + 1 : ℕ)))) +
        2 * x * vaalerK x|
        ≤ |∑ n ∈ Finset.range N,
          (vaalerK (x - (n + 1 : ℕ)) -
            vaalerK (x + (n + 1 : ℕ)))| +
          |2 * x * vaalerK x| := abs_add_le _ _
    _ ≤ 4 := by linarith

lemma continuous_vaalerHFin (N : ℕ) :
    Continuous (vaalerHFin N) := by
  unfold vaalerHFin
  apply Continuous.add
  · apply continuous_finset_sum
    intro n hn
    exact (continuous_vaalerK.comp
      (show Continuous (fun x : ℝ =>
        x - (n + 1 : ℕ)) by fun_prop)).sub
      (continuous_vaalerK.comp
        (show Continuous (fun x : ℝ =>
          x + (n + 1 : ℕ)) by fun_prop))
  · exact ((continuous_const.mul continuous_id).mul
      continuous_vaalerK)

lemma tendsto_integral_vaalerHFin_sub
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (a : ℝ) :
    Tendsto
      (fun N : ℕ => ∫ y : ℝ, vaalerHFin N (y - a) ∂μ)
      atTop
      (nhds (∫ y : ℝ, vaalerH (y - a) ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence
    (fun _ : ℝ => (4 : ℝ))
  · intro N
    have hm : Measurable (fun y : ℝ =>
        vaalerHFin N (y - a)) :=
      ((continuous_vaalerHFin N).comp
        (show Continuous (fun y : ℝ => y - a) by fun_prop)).measurable
    exact hm.aestronglyMeasurable
  · exact integrable_const (4 : ℝ)
  · intro N
    filter_upwards with y
    simpa only [Real.norm_eq_abs] using
      abs_vaalerHFin_le_four N (y - a)
  · filter_upwards with y
    exact tendsto_vaalerHFin (y - a)

lemma tendsto_integral_vaalerHFin_sub_difference
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (a : ℝ) :
    Tendsto
      (fun N : ℕ =>
        (∫ y : ℝ, vaalerHFin N (y - a) ∂μ) -
          ∫ y : ℝ, vaalerHFin N (y - a) ∂ν)
      atTop
      (nhds ((∫ y : ℝ, vaalerH (y - a) ∂μ) -
        ∫ y : ℝ, vaalerH (y - a) ∂ν)) := by
  exact (tendsto_integral_vaalerHFin_sub μ a).sub
    (tendsto_integral_vaalerHFin_sub ν a)

/-! ## Oscillatory limits -/

lemma riemannLebesgue_cos_atTop (g : ℝ → ℂ) (hg : Integrable g) :
    Tendsto
      (fun w : ℝ =>
        ∫ t : ℝ, (Real.cos (2 * Real.pi * t * w) : ℂ) * g t)
      atTop (𝓝 0) := by
  let A : ℝ → ℂ :=
    fun w => ∫ t : ℝ, 𝐞 (-(t * w)) • g t
  have hpos : Tendsto A atTop (𝓝 0) := by
    exact (Real.tendsto_integral_exp_smul_cocompact g).mono_left
      atTop_le_cocompact
  have hneg : Tendsto (fun w : ℝ => A (-w)) atTop (𝓝 0) := by
    exact ((Real.tendsto_integral_exp_smul_cocompact g).mono_left
      atBot_le_cocompact).comp tendsto_neg_atTop_atBot
  have havg :
      Tendsto (fun w : ℝ => (1 / 2 : ℂ) * (A w + A (-w)))
        atTop (𝓝 0) := by
    simpa using (hpos.add hneg).const_mul (1 / 2 : ℂ)
  apply havg.congr'
  filter_upwards with w
  dsimp only [A]
  have hgw : Integrable (fun t : ℝ =>
      𝐞 (-(t * w)) • g t) := by
    simpa [mul_comm] using
      ((Real.fourierIntegral_convergent_iff (V := ℝ) w).2 hg)
  have hgn : Integrable (fun t : ℝ =>
      𝐞 (-(t * -w)) • g t) := by
    simpa [mul_comm] using
      ((Real.fourierIntegral_convergent_iff (V := ℝ) (-w)).2 hg)
  rw [← MeasureTheory.integral_add hgw hgn,
    ← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with t
  rw [Circle.smul_def, Circle.smul_def,
    Real.fourierChar_apply, Real.fourierChar_apply]
  rw [show -(t * -w) = t * w by ring]
  simp only [smul_eq_mul]
  rw [show 2 * Real.pi * -(t * w) =
      -(2 * Real.pi * t * w) by ring]
  rw [show 2 * Real.pi * (t * w) =
      2 * Real.pi * t * w by ring]
  rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  push_cast
  rw [Complex.cos_neg, Complex.sin_neg]
  ring

lemma riemannLebesgue_odd_cos (g : ℝ → ℂ) (hg : Integrable g) :
    Tendsto
      (fun N : ℕ => ∫ t : ℝ,
        g t * (Real.cos (((2 * N + 1 : ℕ) : ℝ) *
          Real.pi * t) : ℂ))
      atTop (𝓝 0) := by
  have hw :
      Tendsto (fun N : ℕ => (N : ℝ) + 1 / 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 / 2)
      tendsto_natCast_atTop_atTop
  have h := (riemannLebesgue_cos_atTop g hg).comp hw
  apply h.congr'
  filter_upwards with N
  apply MeasureTheory.integral_congr_ae
  filter_upwards with t
  rw [mul_comm (g t)]
  congr 2
  congr 1
  push_cast
  ring

lemma riemannLebesgue_odd_cos_interval
    (g : ℝ → ℂ) (hg : IntervalIntegrable g volume (-1) 1) :
    Tendsto
      (fun N : ℕ => ∫ t : ℝ in -1..1,
        g t * (Real.cos (((2 * N + 1 : ℕ) : ℝ) *
          Real.pi * t) : ℂ))
      atTop (𝓝 0) := by
  let G : ℝ → ℂ := (Ioc (-1) 1).indicator g
  have hG : Integrable G volume := by
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le
      (show (-1 : ℝ) ≤ 1 by norm_num)).mp hg).integrable_indicator
        measurableSet_Ioc
  have h := riemannLebesgue_odd_cos G hG
  apply h.congr'
  filter_upwards with N
  rw [intervalIntegral.integral_of_le
    (show (-1 : ℝ) ≤ 1 by norm_num)]
  rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with t
  by_cases ht : t ∈ Ioc (-1 : ℝ) 1
  · simp [G, ht]
  · simp [G, ht]

lemma two_mul_abs_le_abs_sin_pi {t : ℝ}
    (ht : |t| ≤ 1 / 2) :
    2 * |t| ≤ |Real.sin (Real.pi * t)| := by
  have harg : |Real.pi * t| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have h := Real.mul_abs_le_abs_sin harg
  calc
    2 * |t| = 2 / Real.pi * |Real.pi * t| := by
      rw [abs_mul, abs_of_pos Real.pi_pos]
      field_simp [Real.pi_ne_zero]
    _ ≤ |Real.sin (Real.pi * t)| := h

lemma two_mul_one_sub_abs_le_abs_sin_pi {t : ℝ}
    (htlo : 1 / 2 ≤ |t|) (hthi : |t| ≤ 1) :
    2 * (1 - |t|) ≤ |Real.sin (Real.pi * t)| := by
  have hs0 : 0 ≤ 1 - |t| := by linarith
  have hs1 : 1 - |t| ≤ 1 / 2 := by linarith
  have harg :
      |Real.pi * (1 - |t|)| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos,
      abs_of_nonneg hs0]
    nlinarith [Real.pi_pos]
  have h := Real.mul_abs_le_abs_sin harg
  have hleft :
      2 / Real.pi * |Real.pi * (1 - |t|)| =
        2 * (1 - |t|) := by
    rw [abs_mul, abs_of_pos Real.pi_pos,
      abs_of_nonneg hs0]
    field_simp [Real.pi_ne_zero]
  have hsine :
      |Real.sin (Real.pi * (1 - |t|))| =
        |Real.sin (Real.pi * t)| := by
    have habsarg : |Real.pi * t| ≤ Real.pi := by
      rw [abs_mul, abs_of_pos Real.pi_pos]
      exact mul_le_of_le_one_right Real.pi_pos.le hthi
    have hsinabs :
        |Real.sin (Real.pi * t)| =
          Real.sin (Real.pi * |t|) := by
      rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi habsarg]
      congr 1
      rw [abs_mul, abs_of_pos Real.pi_pos]
    rw [hsinabs]
    rw [show Real.pi * (1 - |t|) =
      Real.pi - Real.pi * |t| by ring,
      Real.sin_pi_sub]
    have hnonneg : 0 ≤ Real.sin (Real.pi * |t|) :=
      Real.sin_nonneg_of_nonneg_of_le_pi
        (mul_nonneg Real.pi_pos.le (abs_nonneg t))
        (mul_le_of_le_one_right Real.pi_pos.le hthi)
    rw [abs_of_nonneg hnonneg]
  rw [hleft, hsine] at h
  exact h

lemma norm_mul_vaaler_ratio_le
    {C t : ℝ} (hC : 0 ≤ C) (ht : |t| ≤ 1)
    (z : ℂ) (hzsmall : |t| ≤ 1 / 2 →
      ‖z‖ ≤ C * |t|)
    (hzglobal : ‖z‖ ≤ 2) :
    ‖z * (((1 - |t|) / Real.sin (Real.pi * t) : ℝ) : ℂ)‖ ≤
      C + 2 := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div]
  have hnum0 : 0 ≤ 1 - |t| := by linarith
  rw [abs_of_nonneg hnum0]
  by_cases hsmall : |t| ≤ 1 / 2
  · by_cases ht0 : t = 0
    · subst t
      simp
      linarith
    · have hat0 : 0 < |t| := abs_pos.mpr ht0
      have hsin := two_mul_abs_le_abs_sin_pi hsmall
      have hsin0 : 0 < |Real.sin (Real.pi * t)| :=
        lt_of_lt_of_le (mul_pos two_pos hat0) hsin
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hsin0).2
      have hone : 1 - |t| ≤ 1 := by
        linarith [abs_nonneg t]
      have hleft :
          ‖z‖ * (1 - |t|) ≤ C * |t| := by
        calc
          ‖z‖ * (1 - |t|)
              ≤ (C * |t|) * (1 - |t|) :=
            mul_le_mul_of_nonneg_right (hzsmall hsmall) hnum0
          _ ≤ (C * |t|) * 1 :=
            mul_le_mul_of_nonneg_left hone
              (mul_nonneg hC (abs_nonneg t))
          _ = C * |t| := by ring
      have hright :
          C * |t| ≤ (C + 2) * |Real.sin (Real.pi * t)| := by
        calc
          C * |t| ≤ (C + 2) * (2 * |t|) := by
            nlinarith [mul_nonneg hC (abs_nonneg t)]
          _ ≤ (C + 2) * |Real.sin (Real.pi * t)| :=
            mul_le_mul_of_nonneg_left hsin (by positivity)
      exact hleft.trans hright
  · have hlarge : 1 / 2 ≤ |t| := le_of_not_ge hsmall
    let s : ℝ := 1 - |t|
    have hs0 : 0 ≤ s := by dsimp [s]; linarith
    by_cases hsz : s = 0
    · rw [show 1 - |t| = 0 by simpa [s] using hsz]
      simp
      linarith
    · have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hsz)
      have hsin :=
        two_mul_one_sub_abs_le_abs_sin_pi hlarge ht
      have hsin0 : 0 < |Real.sin (Real.pi * t)| := by
        have : 0 < 2 * (1 - |t|) := by
          simpa [s] using mul_pos two_pos hspos
        exact this.trans_le hsin
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hsin0).2
      have hleft :
          ‖z‖ * (1 - |t|) ≤ 2 * (1 - |t|) :=
        mul_le_mul_of_nonneg_right hzglobal hnum0
      have hright :
          2 * (1 - |t|) ≤
              (C + 2) * |Real.sin (Real.pi * t)| := by
        calc
          2 * (1 - |t|) ≤
              1 * |Real.sin (Real.pi * t)| := by
            simpa using hsin
          _ ≤ (C + 2) * |Real.sin (Real.pi * t)| := by
            gcongr
            linarith
      exact hleft.trans hright

lemma intervalIntegrable_mul_vaaler_ratio
    (Δ : ℝ → ℂ) (hΔm : Measurable Δ)
    {C : ℝ} (hC : 0 ≤ C)
    (hΔsmall : ∀ t : ℝ, |t| ≤ 1 / 2 →
      ‖Δ t‖ ≤ C * |t|)
    (hΔglobal : ∀ t : ℝ, ‖Δ t‖ ≤ 2) :
    IntervalIntegrable
      (fun t : ℝ =>
        Δ t * (((1 - |t|) /
          Real.sin (Real.pi * t) : ℝ) : ℂ))
      volume (-1) 1 := by
  apply IntervalIntegrable.mono_fun'
    (g := fun _ : ℝ => C + 2)
    (_root_.intervalIntegrable_const : IntervalIntegrable
      (fun _ : ℝ => C + 2) volume (-1) 1)
  · have hm : Measurable (fun t : ℝ =>
        Δ t * (((1 - |t|) /
          Real.sin (Real.pi * t) : ℝ) : ℂ)) := by
      fun_prop
    exact hm.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    have ht' : |t| ≤ 1 := by
      rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at ht
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]
    exact norm_mul_vaaler_ratio_le hC ht' (Δ t)
      (hΔsmall t)
      (hΔglobal t)

/-- The limiting Fourier kernel for Vaaler's sign approximant. -/
noncomputable def vaalerHLimitKernel (t : ℝ) : ℂ :=
  -Complex.I *
    (((1 - |t|) * Real.cot (Real.pi * t) +
      Real.sign t / Real.pi : ℝ) : ℂ)

/-- The oscillatory remainder between the finite and limiting Vaaler kernels. -/
noncomputable def vaalerHKernelRemainder
    (N : ℕ) (t : ℝ) : ℂ :=
  Complex.I *
    ((((1 - |t|) / Real.sin (Real.pi * t)) *
      Real.cos (((2 * N + 1 : ℕ) : ℝ) *
        Real.pi * t) : ℝ) : ℂ)

lemma vaalerHFinKernel_eq_limit_add_remainder
    (N : ℕ) {t : ℝ}
    (hsin : Real.sin (Real.pi * t) ≠ 0) :
    vaalerHFinKernel N t =
      vaalerHLimitKernel t + vaalerHKernelRemainder N t := by
  unfold vaalerHFinKernel vaalerHLimitKernel
    vaalerHKernelRemainder
  rw [vaalerDirichlet_eq_cot_add_remainder N hsin]
  have hsign :
      ((Real.sign t : ℝ) : ℂ) /
          ((Real.pi : ℂ) * Complex.I) =
        -Complex.I *
          (((Real.sign t / Real.pi : ℝ) : ℂ)) := by
    push_cast
    field_simp [Real.pi_ne_zero, Complex.I_ne_zero]
    simp [Complex.I_sq]
  have hratio :
      ((1 - |t| : ℝ) : ℂ) *
          (Complex.I *
            ((Real.cos (((2 * N + 1 : ℕ) : ℝ) *
                Real.pi * t) /
              Real.sin (Real.pi * t) : ℝ) : ℂ)) =
        Complex.I *
          ((((1 - |t|) / Real.sin (Real.pi * t)) *
            Real.cos (((2 * N + 1 : ℕ) : ℝ) *
              Real.pi * t) : ℝ) : ℂ) := by
    push_cast
    field_simp [hsin]
  rw [hsign]
  rw [mul_add, hratio]
  push_cast
  ring

/-- The difference of the characteristic functions of `μ` and `ν` at frequency `2πt`. -/
noncomputable def vaalerCharDifference
    (μ ν : Measure ℝ) (t : ℝ) : ℂ :=
  charFun μ (2 * Real.pi * t) -
    charFun ν (2 * Real.pi * t)

lemma measurable_vaalerCharDifference
    (μ ν : Measure ℝ) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    Measurable (vaalerCharDifference μ ν) := by
  unfold vaalerCharDifference
  exact (measurable_charFun.comp (by fun_prop)).sub
    (measurable_charFun.comp (by fun_prop))

lemma norm_vaalerCharDifference_le_two
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (t : ℝ) :
    ‖vaalerCharDifference μ ν t‖ ≤ 2 := by
  unfold vaalerCharDifference
  calc
    ‖charFun μ (2 * Real.pi * t) -
        charFun ν (2 * Real.pi * t)‖
        ≤ ‖charFun μ (2 * Real.pi * t)‖ +
          ‖charFun ν (2 * Real.pi * t)‖ :=
      norm_sub_le _ _
    _ ≤ 1 + 1 := add_le_add
      (norm_charFun_le_one _) (norm_charFun_le_one _)
    _ = 2 := by norm_num

/-- The characteristic-function integrand underlying the Vaaler kernel remainder. -/
noncomputable def vaalerCharRemainderBase
    (μ ν : Measure ℝ) (a t : ℝ) : ℂ :=
  (vaalerCharDifference μ ν t *
      (((1 - |t|) /
        Real.sin (Real.pi * t) : ℝ) : ℂ)) *
    vaalerOsc (-a) t * Complex.I

lemma intervalIntegrable_vaalerCharRemainderBase
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    {C : ℝ} (hC : 0 ≤ C)
    (hsmall : ∀ t : ℝ, |t| ≤ 1 / 2 →
      ‖vaalerCharDifference μ ν t‖ ≤ C * |t|)
    (a : ℝ) :
    IntervalIntegrable
      (vaalerCharRemainderBase μ ν a)
      volume (-1) 1 := by
  have hratio := intervalIntegrable_mul_vaaler_ratio
    (vaalerCharDifference μ ν)
    (measurable_vaalerCharDifference μ ν)
    hC hsmall (norm_vaalerCharDifference_le_two μ ν)
  have hphase := hratio.mul_continuousOn
    (continuous_vaalerOsc (-a)).continuousOn
  have hI := hphase.mul_const Complex.I
  exact IntervalIntegrable.congr (fun t _ => by
    rfl) hI

lemma tendsto_integral_vaalerCharKernelRemainder
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    {C : ℝ} (hC : 0 ≤ C)
    (hsmall : ∀ t : ℝ, |t| ≤ 1 / 2 →
      ‖vaalerCharDifference μ ν t‖ ≤ C * |t|)
    (a : ℝ) :
    Tendsto
      (fun N : ℕ => ∫ t : ℝ in -1..1,
        vaalerOsc (-a) t *
          vaalerCharDifference μ ν t *
          vaalerHKernelRemainder N t)
      atTop (𝓝 0) := by
  have hbase := intervalIntegrable_vaalerCharRemainderBase
    μ ν hC hsmall a
  have hRL := riemannLebesgue_odd_cos_interval
    (vaalerCharRemainderBase μ ν a) hbase
  apply hRL.congr'
  filter_upwards with N
  apply intervalIntegral.integral_congr
  intro t ht
  unfold vaalerCharRemainderBase vaalerHKernelRemainder
  push_cast
  ring

lemma ae_sin_pi_ne_zero_on_vaalerInterval :
    ∀ᵐ t : ℝ ∂volume.restrict (uIoc (-1 : ℝ) 1),
      Real.sin (Real.pi * t) ≠ 0 := by
  filter_upwards [
    ae_restrict_mem measurableSet_uIoc,
    (volume.restrict (uIoc (-1 : ℝ) 1)).ae_ne 0,
    (volume.restrict (uIoc (-1 : ℝ) 1)).ae_ne 1]
      with t ht ht0 ht1
  rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at ht
  have hlo : -Real.pi < Real.pi * t := by
    nlinarith [Real.pi_pos, ht.1]
  have hhi : Real.pi * t < Real.pi := by
    have htlt : t < 1 := lt_of_le_of_ne ht.2 ht1
    nlinarith [Real.pi_pos]
  intro hsin
  have hzero :=
    (Real.sin_eq_zero_iff_of_lt_of_lt hlo hhi).mp hsin
  exact (mul_ne_zero Real.pi_ne_zero ht0) hzero

lemma intervalIntegrable_vaalerCharDifferenceKernel
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (N : ℕ) (a : ℝ) :
    IntervalIntegrable
      (fun t : ℝ =>
        vaalerOsc (-a) t *
          vaalerCharDifference μ ν t *
          vaalerHFinKernel N t)
      volume (-1) 1 := by
  have hμ := intervalIntegrable_vaalerCharKernel μ N a
  have hν := intervalIntegrable_vaalerCharKernel ν N a
  apply IntervalIntegrable.congr (fun t ht => ?_)
    (hμ.sub hν)
  unfold vaalerCharDifference
  ring

lemma intervalIntegrable_vaalerCharKernelRemainder
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    {C : ℝ} (hC : 0 ≤ C)
    (hsmall : ∀ t : ℝ, |t| ≤ 1 / 2 →
      ‖vaalerCharDifference μ ν t‖ ≤ C * |t|)
    (N : ℕ) (a : ℝ) :
    IntervalIntegrable
      (fun t : ℝ =>
        vaalerOsc (-a) t *
          vaalerCharDifference μ ν t *
          vaalerHKernelRemainder N t)
      volume (-1) 1 := by
  have hbase := intervalIntegrable_vaalerCharRemainderBase
    μ ν hC hsmall a
  have hcos : Continuous (fun t : ℝ =>
      (Real.cos (((2 * N + 1 : ℕ) : ℝ) *
        Real.pi * t) : ℂ)) := by
    fun_prop
  have hmul := hbase.mul_continuousOn hcos.continuousOn
  apply IntervalIntegrable.congr (fun t ht => ?_) hmul
  unfold vaalerCharRemainderBase vaalerHKernelRemainder
  push_cast
  ring

lemma intervalIntegrable_vaalerCharLimitKernel
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    {C : ℝ} (hC : 0 ≤ C)
    (hsmall : ∀ t : ℝ, |t| ≤ 1 / 2 →
      ‖vaalerCharDifference μ ν t‖ ≤ C * |t|)
    (a : ℝ) :
    IntervalIntegrable
      (fun t : ℝ =>
        vaalerOsc (-a) t *
          vaalerCharDifference μ ν t *
          vaalerHLimitKernel t)
      volume (-1) 1 := by
  have hfin :=
    intervalIntegrable_vaalerCharDifferenceKernel μ ν 0 a
  have hrem :=
    intervalIntegrable_vaalerCharKernelRemainder
      μ ν hC hsmall 0 a
  apply IntervalIntegrable.congr_ae (hfin.sub hrem)
  filter_upwards [ae_sin_pi_ne_zero_on_vaalerInterval]
    with t hsin
  rw [vaalerHFinKernel_eq_limit_add_remainder 0 hsin]
  ring

lemma tendsto_integral_vaalerCharDifferenceKernel
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    {C : ℝ} (hC : 0 ≤ C)
    (hsmall : ∀ t : ℝ, |t| ≤ 1 / 2 →
      ‖vaalerCharDifference μ ν t‖ ≤ C * |t|)
    (a : ℝ) :
    Tendsto
      (fun N : ℕ => ∫ t : ℝ in -1..1,
        vaalerOsc (-a) t *
          vaalerCharDifference μ ν t *
          vaalerHFinKernel N t)
      atTop
      (𝓝 (∫ t : ℝ in -1..1,
        vaalerOsc (-a) t *
          vaalerCharDifference μ ν t *
          vaalerHLimitKernel t)) := by
  have hlim := intervalIntegrable_vaalerCharLimitKernel
    μ ν hC hsmall a
  have hremN : ∀ N : ℕ, IntervalIntegrable
      (fun t : ℝ =>
        vaalerOsc (-a) t *
          vaalerCharDifference μ ν t *
          vaalerHKernelRemainder N t)
      volume (-1) 1 :=
    fun N => intervalIntegrable_vaalerCharKernelRemainder
      μ ν hC hsmall N a
  have hremT := tendsto_integral_vaalerCharKernelRemainder
    μ ν hC hsmall a
  have hadd :
      Tendsto
        (fun N : ℕ =>
          (∫ t : ℝ in -1..1,
            vaalerOsc (-a) t *
              vaalerCharDifference μ ν t *
              vaalerHLimitKernel t) +
          ∫ t : ℝ in -1..1,
            vaalerOsc (-a) t *
              vaalerCharDifference μ ν t *
              vaalerHKernelRemainder N t)
        atTop
        (𝓝 (∫ t : ℝ in -1..1,
          vaalerOsc (-a) t *
            vaalerCharDifference μ ν t *
            vaalerHLimitKernel t)) := by
    simpa using (tendsto_const_nhds.add hremT)
  apply hadd.congr'
  filter_upwards with N
  rw [← intervalIntegral.integral_add hlim (hremN N)]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [volume.ae_ne 0, volume.ae_ne 1]
    with t ht0 ht1
  intro ht
  rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at ht
  have hlo : -Real.pi < Real.pi * t := by
    nlinarith [Real.pi_pos, ht.1]
  have hhi : Real.pi * t < Real.pi := by
    have htlt : t < 1 := lt_of_le_of_ne ht.2 ht1
    nlinarith [Real.pi_pos]
  have hsin : Real.sin (Real.pi * t) ≠ 0 := by
    intro hz
    have hzero :=
      (Real.sin_eq_zero_iff_of_lt_of_lt hlo hhi).mp hz
    exact (mul_ne_zero Real.pi_ne_zero ht0) hzero
  change
    vaalerOsc (-a) t * vaalerCharDifference μ ν t *
          vaalerHLimitKernel t +
        vaalerOsc (-a) t * vaalerCharDifference μ ν t *
          vaalerHKernelRemainder N t =
      vaalerOsc (-a) t * vaalerCharDifference μ ν t *
        vaalerHFinKernel N t
  rw [vaalerHFinKernel_eq_limit_add_remainder N hsin]
  ring

lemma integral_vaalerH_sub_difference_fourier_limit
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    {C : ℝ} (hC : 0 ≤ C)
    (hsmall : ∀ t : ℝ, |t| ≤ 1 / 2 →
      ‖vaalerCharDifference μ ν t‖ ≤ C * |t|)
    (a : ℝ) :
    (((∫ y : ℝ, vaalerH (y - a) ∂μ) -
        ∫ y : ℝ, vaalerH (y - a) ∂ν : ℝ) : ℂ) =
      ∫ t : ℝ in -1..1,
        vaalerOsc (-a) t *
          vaalerCharDifference μ ν t *
          vaalerHLimitKernel t := by
  let f : ℕ → ℂ := fun N =>
    (((∫ y : ℝ, vaalerHFin N (y - a) ∂μ) -
      ∫ y : ℝ, vaalerHFin N (y - a) ∂ν : ℝ) : ℂ)
  have hleftR :=
    tendsto_integral_vaalerHFin_sub_difference μ ν a
  have hleft :
      Tendsto f atTop
        (𝓝 (((∫ y : ℝ, vaalerH (y - a) ∂μ) -
          ∫ y : ℝ, vaalerH (y - a) ∂ν : ℝ) : ℂ)) := by
    have hcomp :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp hleftR
    simpa only [Function.comp_def, f] using hcomp
  have hright0 :=
    tendsto_integral_vaalerCharDifferenceKernel
      μ ν hC hsmall a
  have heq : ∀ N : ℕ,
      f N =
        ∫ t : ℝ in -1..1,
          vaalerOsc (-a) t *
            vaalerCharDifference μ ν t *
            vaalerHFinKernel N t := by
    intro N
    simpa only [f, vaalerCharDifference] using
      integral_vaalerHFin_sub_difference_fourier μ ν N a
  have hright :
      Tendsto f atTop
        (𝓝 (∫ t : ℝ in -1..1,
          vaalerOsc (-a) t *
            vaalerCharDifference μ ν t *
            vaalerHLimitKernel t)) := by
    apply hright0.congr'
    filter_upwards with N
    exact (heq N).symm
  exact tendsto_nhds_unique hleft hright

end HDP.Appendix
