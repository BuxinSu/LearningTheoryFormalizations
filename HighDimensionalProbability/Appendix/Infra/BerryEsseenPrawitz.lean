import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Data.Real.Sign
import Mathlib.NumberTheory.ZetaValues

/-!
# The Prawitz smoothing kernel

This file records the elementary analytic estimates for the compactly supported
kernel used in Prawitz's sharpened form of Esseen smoothing.  The value at zero
is irrelevant for integration; away from zero the kernel has its classical
formula

`(1 - |t|) / 2 + (i / 2) ((1 - |t|) cot (πt) + sign(t) / π)`.

The main estimate is the cancellation bound

`‖K(t) - i / (2 π t)‖ ≤ 1 / 2`,  `0 < t < 1`.
-/

open Real Complex

namespace HDP.Appendix

lemma real_mem_integerComplement {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    (t : ℂ) ∈ Complex.integerComplement := by
  rw [Complex.mem_integerComplement_iff]
  rintro ⟨n, hn⟩
  have hnR : (n : ℝ) = t := by
    exact_mod_cast hn
  have hn0 : 0 < n := by
    exact_mod_cast (hnR.symm ▸ ht0)
  have hn1 : n < 1 := by
    exact_mod_cast (hnR.symm ▸ ht1)
  omega

lemma cotTerm_real_eq {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (n : ℕ) :
    cotTerm (t : ℂ) n =
      (((-2 * t) / (((n + 1 : ℕ) : ℝ) ^ 2 - t ^ 2) : ℝ) : ℂ) := by
  rw [cotTerm_identity (real_mem_integerComplement ht0 ht1)]
  have hprod :
      ((t : ℂ) + (n + 1)) * ((t : ℂ) - (n + 1)) =
        -((((n + 1 : ℕ) : ℝ) ^ 2 - t ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hprod]
  push_cast
  simp only [one_div, inv_neg, mul_neg]
  ring

lemma cot_series_real {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    Real.pi * Real.cot (Real.pi * t) - 1 / t =
      ∑' n : ℕ, (-2 * t) / (((n + 1 : ℕ) : ℝ) ^ 2 - t ^ 2) := by
  have h := cot_series_rep' (real_mem_integerComplement ht0 ht1)
  have hterm (n : ℕ) :
      (1 / ((t : ℂ) - (n + 1)) + 1 / ((t : ℂ) + (n + 1))) =
        (((-2 * t) / (((n + 1 : ℕ) : ℝ) ^ 2 - t ^ 2) : ℝ) : ℂ) := by
    change cotTerm (t : ℂ) n = _
    exact cotTerm_real_eq ht0 ht1 n
  have hcast :
      (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * (t : ℂ)) -
        1 / (t : ℂ) =
      ((Real.pi * Real.cot (Real.pi * t) - 1 / t : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  rw [hcast] at h
  simp_rw [hterm] at h
  exact_mod_cast h

lemma inv_sub_cot_eq_tsum {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    1 / (Real.pi * t) - Real.cot (Real.pi * t) =
      (2 * t / Real.pi) *
        ∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℝ) ^ 2 - t ^ 2) := by
  have h := cot_series_real ht0 ht1
  calc
    1 / (Real.pi * t) - Real.cot (Real.pi * t) =
        -(Real.pi * Real.cot (Real.pi * t) - 1 / t) / Real.pi := by
      field_simp [Real.pi_ne_zero, ht0.ne']
      ring
    _ = -(∑' n : ℕ, (-2 * t) /
          (((n + 1 : ℕ) : ℝ) ^ 2 - t ^ 2)) / Real.pi := by rw [h]
    _ = (2 * t / Real.pi) *
        ∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℝ) ^ 2 - t ^ 2) := by
      have heq :
          (fun n : ℕ => (-2 * t) /
              (((n + 1 : ℕ) : ℝ) ^ 2 - t ^ 2)) =
            fun n : ℕ => (-2 * t) *
              (1 / (((n + 1 : ℕ) : ℝ) ^ 2 - t ^ 2)) := by
        funext n
        ring
      rw [heq, tsum_mul_left]
      ring

lemma tsum_inv_nat_succ_sq :
    ∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℝ) ^ 2) = Real.pi ^ 2 / 6 := by
  have h := hasSum_zeta_two.summable.sum_add_tsum_nat_add 1
  calc
    ∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℝ) ^ 2) =
        ∑' n : ℕ, 1 / (n : ℝ) ^ 2 := by simpa using h
    _ = Real.pi ^ 2 / 6 := hasSum_zeta_two.tsum_eq

lemma summable_inv_nat_succ_sq_sub {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    Summable (fun n : ℕ =>
      1 / (((n + 1 : ℕ) : ℝ) ^ 2 - t ^ 2)) := by
  have hc : Summable (fun n => cotTerm (t : ℂ) n) :=
    summable_cotTerm (real_mem_integerComplement ht0 ht1)
  have hcast : Summable (fun n : ℕ =>
      (((-2 * t) / (((n + 1 : ℕ) : ℝ) ^ 2 - t ^ 2) : ℝ) : ℂ)) :=
    hc.congr fun n => cotTerm_real_eq ht0 ht1 n
  have hr : Summable (fun n : ℕ =>
      (-2 * t) / (((n + 1 : ℕ) : ℝ) ^ 2 - t ^ 2)) :=
    Complex.summable_ofReal.mp hcast
  have heq :
      (fun n : ℕ =>
        (-2 * t) / (((n + 1 : ℕ) : ℝ) ^ 2 - t ^ 2)) =
      fun n : ℕ => (-2 * t) *
        (1 / (((n + 1 : ℕ) : ℝ) ^ 2 - t ^ 2)) := by
    funext n
    ring
  rw [heq] at hr
  exact (summable_mul_left_iff (by nlinarith : -2 * t ≠ 0)).mp hr

lemma tsum_inv_nat_succ_sq_sub_le {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℝ) ^ 2 - t ^ 2) ≤
      (1 / (1 - t ^ 2)) * (Real.pi ^ 2 / 6) := by
  have ht2 : 0 < 1 - t ^ 2 := by nlinarith
  let f : ℕ → ℝ := fun n =>
    1 / (((n + 1 : ℕ) : ℝ) ^ 2 - t ^ 2)
  let g : ℕ → ℝ := fun n =>
    (1 / (1 - t ^ 2)) * (1 / (((n + 1 : ℕ) : ℝ) ^ 2))
  have hfg : ∀ n, f n ≤ g n := by
    intro n
    have hn : (1 : ℝ) ≤ (n + 1 : ℕ) := by norm_num
    have hn_sq : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by
      nlinarith [sq_nonneg ((((n + 1 : ℕ) : ℝ) - 1))]
    have hden :
        (1 - t ^ 2) * (((n + 1 : ℕ) : ℝ) ^ 2) ≤
          ((n + 1 : ℕ) : ℝ) ^ 2 - t ^ 2 := by
      have hnonneg :
          0 ≤ t ^ 2 * ((((n + 1 : ℕ) : ℝ) ^ 2) - 1) :=
        mul_nonneg (sq_nonneg t) (sub_nonneg.mpr hn_sq)
      nlinarith
    have hden0 : 0 <
        ((n + 1 : ℕ) : ℝ) ^ 2 - t ^ 2 := by
      nlinarith
    have hprod0 : 0 <
        (1 - t ^ 2) * (((n + 1 : ℕ) : ℝ) ^ 2) := by positivity
    dsimp [f, g]
    rw [one_div, one_div, one_div]
    calc
      (((n + 1 : ℕ) : ℝ) ^ 2 - t ^ 2)⁻¹
          ≤ ((1 - t ^ 2) * (((n + 1 : ℕ) : ℝ) ^ 2))⁻¹ :=
        (inv_le_inv₀ hden0 hprod0).2 hden
      _ = (1 - t ^ 2)⁻¹ *
          ((((n + 1 : ℕ) : ℝ) ^ 2)⁻¹) := by
        rw [mul_inv_rev]
        ring
  have hf : Summable f := by
    apply Summable.of_nonneg_of_le (fun n => by
      dsimp [f]
      have hn : (1 : ℝ) ≤ (n + 1 : ℕ) := by norm_num
      have hn_sq : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by
        nlinarith [sq_nonneg ((((n + 1 : ℕ) : ℝ) - 1))]
      have : 0 < ((n + 1 : ℕ) : ℝ) ^ 2 - t ^ 2 := by nlinarith
      positivity) hfg
    have hs : Summable (fun n : ℕ =>
        1 / (((n + 1 : ℕ) : ℝ) ^ 2)) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (summable_nat_add_iff 1).2 hasSum_zeta_two.summable
    change Summable (fun n : ℕ =>
      (1 / (1 - t ^ 2)) * (1 / (((n + 1 : ℕ) : ℝ) ^ 2)))
    exact hs.mul_left (1 / (1 - t ^ 2))
  have hg : Summable g := by
    have hs : Summable (fun n : ℕ =>
        1 / (((n + 1 : ℕ) : ℝ) ^ 2)) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (summable_nat_add_iff 1).2 hasSum_zeta_two.summable
    change Summable (fun n : ℕ =>
      (1 / (1 - t ^ 2)) * (1 / (((n + 1 : ℕ) : ℝ) ^ 2)))
    exact hs.mul_left (1 / (1 - t ^ 2))
  calc
    ∑' n, f n ≤ ∑' n, g n := Summable.tsum_le_tsum hfg hf hg
    _ = (1 / (1 - t ^ 2)) * (Real.pi ^ 2 / 6) := by
      dsimp [g]
      rw [tsum_mul_left, tsum_inv_nat_succ_sq]

/-- The first term of the cotangent series already gives the matching lower
comparison with the Basel series. -/
lemma tsum_inv_nat_succ_sq_le_sq_sub {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    Real.pi ^ 2 / 6 ≤
      ∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℝ) ^ 2 - t ^ 2) := by
  have hpoint : ∀ n : ℕ,
      1 / (((n + 1 : ℕ) : ℝ) ^ 2) ≤
        1 / (((n + 1 : ℕ) : ℝ) ^ 2 - t ^ 2) := by
    intro n
    have hn : (1 : ℝ) ≤ (n + 1 : ℕ) := by norm_num
    have hn_sq : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by
      nlinarith [sq_nonneg ((((n + 1 : ℕ) : ℝ) - 1))]
    have hn0 : 0 < ((n + 1 : ℕ) : ℝ) ^ 2 := by positivity
    have hden0 : 0 <
        ((n + 1 : ℕ) : ℝ) ^ 2 - t ^ 2 := by
      nlinarith
    rw [one_div, one_div]
    exact (inv_le_inv₀ hn0 hden0).2 (by nlinarith [sq_nonneg t])
  have hleft : Summable (fun n : ℕ =>
      1 / (((n + 1 : ℕ) : ℝ) ^ 2)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).2 hasSum_zeta_two.summable
  have hright := summable_inv_nat_succ_sq_sub ht0 ht1
  calc
    Real.pi ^ 2 / 6 =
        ∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℝ) ^ 2) :=
      tsum_inv_nat_succ_sq.symm
    _ ≤ ∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℝ) ^ 2 - t ^ 2) :=
      Summable.tsum_le_tsum hpoint hleft hright

/-- The regular part of cotangent admits the classical sharp series bound. -/
lemma inv_sub_cot_sharp_upper {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    1 / (Real.pi * t) - Real.cot (Real.pi * t) ≤
      Real.pi * t / (3 * (1 - t ^ 2)) := by
  rw [inv_sub_cot_eq_tsum ht0 ht1]
  have hsum := tsum_inv_nat_succ_sq_sub_le ht0 ht1
  have hcoef : 0 ≤ 2 * t / Real.pi := by positivity
  calc
    (2 * t / Real.pi) *
        ∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℝ) ^ 2 - t ^ 2)
      ≤ (2 * t / Real.pi) *
        ((1 / (1 - t ^ 2)) * (Real.pi ^ 2 / 6)) :=
        mul_le_mul_of_nonneg_left hsum hcoef
    _ = Real.pi * t / (3 * (1 - t ^ 2)) := by
      field_simp [Real.pi_ne_zero]
      ring

lemma inv_sub_cot_sharp_lower {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    Real.pi * t / 3 ≤
      1 / (Real.pi * t) - Real.cot (Real.pi * t) := by
  rw [inv_sub_cot_eq_tsum ht0 ht1]
  have hsum := tsum_inv_nat_succ_sq_le_sq_sub ht0 ht1
  have hcoef : 0 ≤ 2 * t / Real.pi := by positivity
  calc
    Real.pi * t / 3 =
        (2 * t / Real.pi) * (Real.pi ^ 2 / 6) := by
      field_simp [Real.pi_ne_zero]
      ring
    _ ≤ (2 * t / Real.pi) *
        ∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℝ) ^ 2 - t ^ 2) :=
      mul_le_mul_of_nonneg_left hsum hcoef

/-- On the first quadrant, `x cos x ≤ sin x`. -/
lemma mul_cos_le_sin_of_mem_Icc {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ Real.pi / 2) :
    x * Real.cos x ≤ Real.sin x := by
  rcases lt_or_eq_of_le hx1 with h | h
  · have hcos : 0 < Real.cos x :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h⟩
    have htan := Real.le_tan hx0 h
    rw [Real.tan_eq_sin_div_cos] at htan
    exact (le_div_iff₀ hcos).mp htan
  · rw [h, Real.cos_pi_div_two]
    simp

/-- A local upper bound for the regular part of cotangent near zero. -/
lemma inv_sub_cot_small {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1 / 2) :
    0 ≤ 1 / (Real.pi * t) - Real.cot (Real.pi * t) ∧
      1 / (Real.pi * t) - Real.cot (Real.pi * t) ≤
        (5 / 2 : ℝ) * t := by
  let x := Real.pi * t
  have hx0 : 0 < x := mul_pos Real.pi_pos ht0
  have hx1 : x ≤ Real.pi / 2 := by
    dsimp [x]
    nlinarith [Real.pi_pos]
  have hsin0 : 0 < Real.sin x :=
    Real.sin_pos_of_pos_of_lt_pi hx0
      (lt_of_le_of_lt hx1 (by linarith [Real.pi_pos]))
  have hnum0 : 0 ≤ Real.sin x - x * Real.cos x := by
    exact sub_nonneg.mpr (mul_cos_le_sin_of_mem_Icc hx0.le hx1)
  have hsin_le : Real.sin x ≤ x := Real.sin_le hx0.le
  have hcos_lower : 1 - x ^ 2 / 2 ≤ Real.cos x :=
    Real.one_sub_sq_div_two_le_cos
  have hnum_le : Real.sin x - x * Real.cos x ≤ x ^ 3 / 2 := by
    have hxcos : x * (1 - x ^ 2 / 2) ≤ x * Real.cos x :=
      mul_le_mul_of_nonneg_left hcos_lower hx0.le
    nlinarith
  have hjordan : 2 / Real.pi * x ≤ Real.sin x :=
    Real.mul_le_sin hx0.le hx1
  have hden0 : 0 < x * Real.sin x := mul_pos hx0 hsin0
  have hden_lower : 2 / Real.pi * x ^ 2 ≤ x * Real.sin x := by
    nlinarith
  have hid :
      1 / x - Real.cot x =
        (Real.sin x - x * Real.cos x) / (x * Real.sin x) := by
    rw [Real.cot_eq_cos_div_sin]
    field_simp [hx0.ne', hsin0.ne']
  have hquot0 : 0 ≤ 1 / x - Real.cot x := by
    rw [hid]
    positivity
  have hquot1 :
      1 / x - Real.cot x ≤ (Real.pi * x) / 4 := by
    rw [hid]
    calc
      (Real.sin x - x * Real.cos x) / (x * Real.sin x)
          ≤ (x ^ 3 / 2) / (x * Real.sin x) := by
            exact div_le_div_of_nonneg_right hnum_le hden0.le
      _ ≤ (x ^ 3 / 2) / (2 / Real.pi * x ^ 2) := by
            exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden_lower
      _ = (Real.pi * x) / 4 := by
            field_simp [Real.pi_ne_zero, hx0.ne']
            ring
  have hpi2 : Real.pi ^ 2 < 10 := by
    nlinarith [Real.pi_lt_d2, Real.pi_pos]
  constructor
  · simpa [x] using hquot0
  · calc
      1 / (Real.pi * t) - Real.cot (Real.pi * t)
          = 1 / x - Real.cot x := by rfl
      _ ≤ (Real.pi * x) / 4 := hquot1
      _ ≤ (5 / 2 : ℝ) * t := by
        dsimp [x]
        nlinarith [ht0.le]

/-- A complementary upper bound for the cotangent term near one. -/
lemma inv_sub_cot_large {t : ℝ} (ht0 : 1 / 2 ≤ t) (ht1 : t < 1) :
    0 ≤ 1 / (Real.pi * t) - Real.cot (Real.pi * t) ∧
      (1 - t) * (1 / (Real.pi * t) - Real.cot (Real.pi * t)) ≤
        (2 / 3 : ℝ) := by
  let s := 1 - t
  have htpos : 0 < t := by linarith
  have hs0 : 0 < s := by dsimp [s]; linarith
  have hs1 : s ≤ 1 / 2 := by dsimp [s]; linarith
  have hxs0 : 0 < Real.pi * s := mul_pos Real.pi_pos hs0
  have hxs1 : Real.pi * s ≤ Real.pi / 2 := by
    nlinarith [Real.pi_pos]
  have hsine0 : 0 < Real.sin (Real.pi * s) :=
    Real.sin_pos_of_pos_of_lt_pi hxs0
      (lt_of_le_of_lt hxs1 (by linarith [Real.pi_pos]))
  have hcotid :
      Real.cot (Real.pi * t) = -Real.cot (Real.pi * s) := by
    rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin]
    have harg : Real.pi * t = Real.pi - Real.pi * s := by
      dsimp [s]
      ring
    rw [harg, Real.sin_pi_sub, Real.cos_pi_sub, neg_div]
  have hcot_s_nonneg : 0 ≤ Real.cot (Real.pi * s) := by
    rw [Real.cot_eq_cos_div_sin]
    have hcos0 : 0 ≤ Real.cos (Real.pi * s) :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hxs1⟩
    positivity
  have hfirst0 : 0 ≤ 1 / (Real.pi * t) := by positivity
  have hrewrite :
      (1 - t) * (1 / (Real.pi * t) - Real.cot (Real.pi * t)) =
        s / (Real.pi * t) + s * Real.cot (Real.pi * s) := by
    rw [hcotid]
    dsimp [s]
    ring
  have hterm1 : s / (Real.pi * t) ≤ 1 / 3 := by
    have hst : s ≤ t := by dsimp [s]; linarith
    have hpit : 0 < Real.pi * t := mul_pos Real.pi_pos htpos
    calc
      s / (Real.pi * t) ≤ t / (Real.pi * t) :=
        div_le_div_of_nonneg_right hst hpit.le
      _ = 1 / Real.pi := by field_simp [Real.pi_ne_zero, htpos.ne']
      _ ≤ 1 / 3 := by
        exact (div_le_div_iff₀ Real.pi_pos (by norm_num)).2
          (by nlinarith [Real.pi_gt_three])
  have hterm2 : s * Real.cot (Real.pi * s) ≤ 1 / 3 := by
    have hmul :=
      mul_cos_le_sin_of_mem_Icc hxs0.le hxs1
    rw [Real.cot_eq_cos_div_sin]
    calc
      s * (Real.cos (Real.pi * s) / Real.sin (Real.pi * s))
          = ((Real.pi * s) * Real.cos (Real.pi * s)) /
              (Real.pi * Real.sin (Real.pi * s)) := by
            field_simp [Real.pi_ne_zero, hsine0.ne']
      _ ≤ Real.sin (Real.pi * s) /
              (Real.pi * Real.sin (Real.pi * s)) := by
            exact div_le_div_of_nonneg_right hmul (by positivity)
      _ = 1 / Real.pi := by field_simp [Real.pi_ne_zero, hsine0.ne']
      _ ≤ 1 / 3 := by
        exact (div_le_div_iff₀ Real.pi_pos (by norm_num)).2
          (by nlinarith [Real.pi_gt_three])
  constructor
  · rw [hcotid]
    linarith
  · rw [hrewrite]
    linarith

/-- The Prawitz kernel.  Its value at zero is immaterial. -/
noncomputable def prawitzKernel (t : ℝ) : ℂ :=
  ⟨(1 - |t|) / 2,
    ((1 - |t|) * Real.cot (Real.pi * t) + Real.sign t / Real.pi) / 2⟩

lemma prawitzKernel_sub_singular_eq {t : ℝ} (ht : 0 < t) :
    prawitzKernel t - Complex.I / ((2 * Real.pi * t : ℝ) : ℂ) =
      ⟨(1 - t) / 2,
        -((1 - t) / 2 *
          (1 / (Real.pi * t) - Real.cot (Real.pi * t)))⟩ := by
  apply Complex.ext
  · simp [prawitzKernel, abs_of_pos ht, Real.sign_of_pos ht, div_eq_mul_inv]
  · simp [prawitzKernel, abs_of_pos ht, Real.sign_of_pos ht, div_eq_mul_inv]
    field_simp [Real.pi_ne_zero, ht.ne']
    ring

lemma norm_prawitzKernel_sub_singular_sq {t : ℝ} (ht : 0 < t) :
    ‖prawitzKernel t - Complex.I / ((2 * Real.pi * t : ℝ) : ℂ)‖ ^ 2 =
      ((1 - t) / 2) ^ 2 +
        (((1 - t) / 2) *
          (1 / (Real.pi * t) - Real.cot (Real.pi * t))) ^ 2 := by
  rw [prawitzKernel_sub_singular_eq ht, Complex.sq_norm]
  simp only [Complex.normSq_apply]
  ring

lemma inv_sub_cot_nonneg {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    0 ≤ 1 / (Real.pi * t) - Real.cot (Real.pi * t) := by
  by_cases h : t ≤ 1 / 2
  · exact (inv_sub_cot_small ht0 h).1
  · exact (inv_sub_cot_large (le_of_not_ge h) ht1).1

lemma pi_mul_one_sub_mul_inv_sub_cot_le_one {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) :
    Real.pi * t * (1 - t) *
        (1 / (Real.pi * t) - Real.cot (Real.pi * t)) ≤ 1 := by
  by_cases hsmall : t ≤ 2 / 3
  · have hd := inv_sub_cot_sharp_upper ht0 ht1
    have h1mt : 0 ≤ 1 - t := by linarith
    have hpt : 0 ≤ Real.pi * t * (1 - t) := by positivity
    have hden : 0 < 1 - t ^ 2 := by nlinarith
    have hpi2 : Real.pi ^ 2 < 10 := by
      nlinarith [Real.pi_lt_d2, Real.pi_pos]
    have hquad : 10 * t ^ 2 ≤ 3 * (1 + t) := by
      have hsq : t ^ 2 ≤ (2 / 3 : ℝ) * t := by nlinarith
      nlinarith
    calc
      Real.pi * t * (1 - t) *
          (1 / (Real.pi * t) - Real.cot (Real.pi * t))
          ≤ Real.pi * t * (1 - t) *
              (Real.pi * t / (3 * (1 - t ^ 2))) :=
        mul_le_mul_of_nonneg_left hd hpt
      _ = Real.pi ^ 2 * t ^ 2 / (3 * (1 + t)) := by
        field_simp [hden.ne', (by linarith : 1 + t ≠ 0)]
        ring
      _ ≤ 1 := by
        apply (div_le_one (by positivity : 0 < 3 * (1 + t))).2
        nlinarith
  · let s : ℝ := 1 - t
    have ht23 : 2 / 3 ≤ t := le_of_not_ge hsmall
    have hs0 : 0 < s := by dsimp [s]; linarith
    have hs1 : s ≤ 1 / 3 := by dsimp [s]; linarith
    have hxs0 : 0 < Real.pi * s := mul_pos Real.pi_pos hs0
    have hxs1 : Real.pi * s ≤ Real.pi / 2 := by
      nlinarith [Real.pi_pos]
    have hsine0 : 0 < Real.sin (Real.pi * s) :=
      Real.sin_pos_of_pos_of_lt_pi hxs0
        (lt_of_le_of_lt hxs1 (by linarith [Real.pi_pos]))
    have hcotid :
        Real.cot (Real.pi * t) = -Real.cot (Real.pi * s) := by
      rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin]
      have harg : Real.pi * t = Real.pi - Real.pi * s := by
        dsimp [s]
        ring
      rw [harg, Real.sin_pi_sub, Real.cos_pi_sub, neg_div]
    have hxcot : Real.pi * s * Real.cot (Real.pi * s) ≤ 1 := by
      have hmul := mul_cos_le_sin_of_mem_Icc hxs0.le hxs1
      rw [Real.cot_eq_cos_div_sin]
      calc
        Real.pi * s *
            (Real.cos (Real.pi * s) / Real.sin (Real.pi * s)) =
            ((Real.pi * s) * Real.cos (Real.pi * s)) /
              Real.sin (Real.pi * s) := by ring
        _ ≤ Real.sin (Real.pi * s) / Real.sin (Real.pi * s) :=
          div_le_div_of_nonneg_right hmul hsine0.le
        _ = 1 := div_self hsine0.ne'
    have ht0' : 0 ≤ t := ht0.le
    calc
      Real.pi * t * (1 - t) *
          (1 / (Real.pi * t) - Real.cot (Real.pi * t)) =
          s + t * (Real.pi * s * Real.cot (Real.pi * s)) := by
        rw [hcotid]
        dsimp [s]
        field_simp [Real.pi_ne_zero, ht0.ne']
        ring
      _ ≤ s + t * 1 := by
        gcongr
      _ = 1 := by dsimp [s]; ring

/-- The refined Prawitz-kernel cancellation estimate.  This is the form used
in the constant-one Berry--Esseen calculation. -/
lemma norm_prawitzKernel_sub_singular_le_refined {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) :
    ‖prawitzKernel t - Complex.I / ((2 * Real.pi * t : ℝ) : ℂ)‖ ≤
      (1 - t + Real.pi ^ 2 * t ^ 2 / 18) / 2 := by
  let d : ℝ := 1 / (Real.pi * t) - Real.cot (Real.pi * t)
  have ht_nonneg : 0 ≤ t := ht0.le
  have h1mt : 0 ≤ 1 - t := by linarith
  have h1pt : 0 < 1 + t := by linarith
  have hd0 : 0 ≤ d := by
    simpa [d] using inv_sub_cot_nonneg ht0 ht1
  have hd_upper : d ≤ Real.pi * t / (3 * (1 - t ^ 2)) := by
    simpa [d] using inv_sub_cot_sharp_upper ht0 ht1
  have hden : 0 < 1 - t ^ 2 := by nlinarith
  have hprod : (1 - t) * d ≤ Real.pi * t / (3 * (1 + t)) := by
    calc
      (1 - t) * d ≤ (1 - t) *
          (Real.pi * t / (3 * (1 - t ^ 2))) :=
        mul_le_mul_of_nonneg_left hd_upper h1mt
      _ = Real.pi * t / (3 * (1 + t)) := by
        field_simp [h1pt.ne', hden.ne']
        ring
  have hprod0 : 0 ≤ (1 - t) * d := mul_nonneg h1mt hd0
  have hprod_sq : ((1 - t) * d) ^ 2 ≤
      (Real.pi * t / (3 * (1 + t))) ^ 2 :=
    (sq_le_sq₀ hprod0 (by positivity)).2 hprod
  have hpi_sq : (9 : ℝ) ≤ Real.pi ^ 2 := by
    nlinarith [Real.pi_gt_three]
  have hmulpi : 9 * (t * (1 + t) ^ 2) ≤
      Real.pi ^ 2 * (t * (1 + t) ^ 2) := by
    exact mul_le_mul_of_nonneg_right hpi_sq (by positivity)
  have hfactor : 0 ≤ (t - 1) * (t ^ 2 - t - 4) := by
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by nlinarith)
  have hbase : 0 ≤ 9 * (t ^ 3 - 2 * t ^ 2 - 3 * t + 4) := by
    nlinarith [hfactor]
  have hinside : 0 ≤ Real.pi ^ 2 * t ^ 3 +
      2 * Real.pi ^ 2 * t ^ 2 + Real.pi ^ 2 * t -
      36 * t ^ 2 - 36 * t + 36 := by
    nlinarith [hmulpi, hbase]
  have htarget :
      (1 - t) ^ 2 + (Real.pi * t / (3 * (1 + t))) ^ 2 ≤
        (1 - t + Real.pi ^ 2 * t ^ 2 / 18) ^ 2 := by
    rw [div_pow]
    apply sub_nonneg.mp
    field_simp [h1pt.ne']
    nlinarith [mul_nonneg (sq_nonneg Real.pi) (by positivity : 0 ≤ t ^ 3)]
  have hsq :
      ((1 - t) / 2) ^ 2 + (((1 - t) / 2) * d) ^ 2 ≤
        ((1 - t + Real.pi ^ 2 * t ^ 2 / 18) / 2) ^ 2 := by
    nlinarith [hprod_sq, htarget]
  have hrhs0 : 0 ≤ (1 - t + Real.pi ^ 2 * t ^ 2 / 18) / 2 := by
    positivity
  rw [← sq_le_sq₀ (norm_nonneg _) hrhs0,
    norm_prawitzKernel_sub_singular_sq ht0]
  simpa [d] using hsq

/-- The sharp elementary cancellation estimate for the Prawitz kernel. -/
lemma norm_prawitzKernel_sub_singular_le_half {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) :
    ‖prawitzKernel t - Complex.I / ((2 * Real.pi * t : ℝ) : ℂ)‖ ≤
      1 / 2 := by
  rw [← sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 2),
    norm_prawitzKernel_sub_singular_sq ht0]
  by_cases hsmall : t ≤ 1 / 2
  · obtain ⟨hd0, hd1⟩ := inv_sub_cot_small ht0 hsmall
    let d := 1 / (Real.pi * t) - Real.cot (Real.pi * t)
    have hd0' : 0 ≤ d := by simpa [d] using hd0
    have hd1' : d ≤ (5 / 2 : ℝ) * t := by simpa [d] using hd1
    have hd_sq : d ^ 2 ≤ ((5 / 2 : ℝ) * t) ^ 2 :=
      (sq_le_sq₀ hd0' (by positivity)).2 hd1'
    have hpoly :
        (1 - t) ^ 2 * (1 + (25 / 4 : ℝ) * t ^ 2) ≤ 1 := by
      have ht3 : t ^ 3 ≤ (1 / 2 : ℝ) * t ^ 2 := by
        nlinarith [sq_nonneg t]
      have hquad : (-75 / 2 : ℝ) * t ^ 2 + 29 * t - 8 < 0 := by
        nlinarith [sq_nonneg (75 * t - 29)]
      nlinarith
    dsimp [d] at hd_sq
    nlinarith [sq_nonneg (1 - t)]
  · have hlarge : 1 / 2 ≤ t := le_of_not_ge hsmall
    obtain ⟨hd0, hd1⟩ := inv_sub_cot_large hlarge ht1
    let d := 1 / (Real.pi * t) - Real.cot (Real.pi * t)
    have h1mt : 0 ≤ 1 - t := by linarith
    have h1mt_le : 1 - t ≤ 1 / 2 := by linarith
    have hprod0 : 0 ≤ (1 - t) * d := by
      dsimp [d]
      positivity
    have hprod_sq :
        ((1 - t) * d) ^ 2 ≤ (2 / 3 : ℝ) ^ 2 :=
      (sq_le_sq₀ hprod0 (by norm_num)).2 (by simpa [d] using hd1)
    have hreal_sq : (1 - t) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 :=
      (sq_le_sq₀ h1mt (by norm_num)).2 h1mt_le
    dsimp [d] at hprod_sq
    nlinarith

lemma norm_scaled_prawitzKernel_sq {t : ℝ} (ht : 0 < t) :
    ‖(((2 * Real.pi * t : ℝ) : ℂ) * prawitzKernel t)‖ ^ 2 =
      (Real.pi * t * (1 - t)) ^ 2 +
        (1 - Real.pi * t * (1 - t) *
          (1 / (Real.pi * t) - Real.cot (Real.pi * t))) ^ 2 := by
  rw [Complex.sq_norm]
  simp only [prawitzKernel, abs_of_pos ht, Real.sign_of_pos ht,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  field_simp [Real.pi_ne_zero, ht.ne']
  ring

set_option maxHeartbeats 400000 in
/-- A rational version of the classical `1.0253 /(2πt)` kernel estimate.
The factor `21/20` follows from a Bernstein-basis certificate on three
rational subintervals of `[0,1]`. -/
lemma norm_prawitzKernel_le_twenty_one_twentieths_div {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) :
    ‖prawitzKernel t‖ ≤ (21 / 20 : ℝ) / (2 * Real.pi * t) := by
  let d : ℝ := 1 / (Real.pi * t) - Real.cot (Real.pi * t)
  let q : ℝ := t ^ 2 * (1 - t)
  let y : ℝ := Real.pi * t * (1 - t) * d
  have ht_nonneg : 0 ≤ t := ht0.le
  have ht_le : t ≤ 1 := ht1.le
  have h1mt : 0 ≤ 1 - t := by linarith
  have hd0 : 0 ≤ d := by
    simpa [d] using inv_sub_cot_nonneg ht0 ht1
  have hdlower : Real.pi * t / 3 ≤ d := by
    simpa [d] using inv_sub_cot_sharp_lower ht0 ht1
  have hy0 : 0 ≤ y := by
    dsimp [y]
    positivity
  have hy1 : y ≤ 1 := by
    simpa [y, d] using pi_mul_one_sub_mul_inv_sub_cot_le_one ht0 ht1
  have hpi2lower : (9 : ℝ) ≤ Real.pi ^ 2 := by
    nlinarith [Real.pi_gt_three]
  have hq0 : 0 ≤ q := by
    dsimp [q]
    positivity
  have hy_lower : 3 * q ≤ y := by
    have hcoef : 0 ≤ Real.pi * t * (1 - t) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hdlower hcoef
    dsimp [q, y] at *
    nlinarith [mul_le_mul_of_nonneg_right hpi2lower
      (mul_nonneg (sq_nonneg t) h1mt)]
  have htx : t * (1 - t) ≤ 1 / 4 := by
    nlinarith [sq_nonneg (t - 1 / 2)]
  have hq_quarter : q ≤ 1 / 4 := by
    dsimp [q]
    calc
      t ^ 2 * (1 - t) = t * (t * (1 - t)) := by ring
      _ ≤ t * (1 / 4) := mul_le_mul_of_nonneg_left htx ht_nonneg
      _ ≤ 1 * (1 / 4) := by gcongr
      _ = 1 / 4 := by ring
  have hthreeq1 : 3 * q ≤ 1 := by linarith
  have hres_sq : (1 - y) ^ 2 ≤ (1 - 3 * q) ^ 2 := by
    apply (sq_le_sq₀ (by linarith) (by linarith)).2
    linarith
  have hpi2upper : Real.pi ^ 2 ≤ 10 := by
    nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hreal_sq :
      (Real.pi * t * (1 - t)) ^ 2 ≤
        10 * t ^ 2 * (1 - t) ^ 2 := by
    have hm := mul_le_mul_of_nonneg_right hpi2upper
      (mul_nonneg (sq_nonneg t) (sq_nonneg (1 - t)))
    nlinarith
  have hrewrite :
      10 * t ^ 2 * (1 - t) ^ 2 + (1 - 3 * q) ^ 2 =
        1 + q * (4 - 10 * t) + 9 * q ^ 2 := by
    dsimp [q]
    ring
  have hpoly :
      1 + q * (4 - 10 * t) + 9 * q ^ 2 ≤ (21 / 20 : ℝ) ^ 2 := by
    rw [← sub_nonneg]
    by_cases hquarter : t ≤ 1 / 4
    · let z : ℝ := 4 * t
      have hz0 : 0 ≤ z := by dsimp [z]; positivity
      have hz1 : z ≤ 1 := by dsimp [z]; linarith
      have hbern :
          (21 / 20 : ℝ) ^ 2 -
              (1 + q * (4 - 10 * t) + 9 * q ^ 2) =
            (41 / 400 : ℝ) * (1 - z) ^ 6 +
            6 * (41 / 400 : ℝ) * z * (1 - z) ^ 5 +
            15 * (103 / 1200 : ℝ) * z ^ 2 * (1 - z) ^ 4 +
            20 * (203 / 3200 : ℝ) * z ^ 3 * (1 - z) ^ 3 +
            15 * (793 / 19200 : ℝ) * z ^ 4 * (1 - z) ^ 2 +
            6 * (599 / 25600 : ℝ) * z ^ 5 * (1 - z) +
            (1271 / 102400 : ℝ) * z ^ 6 := by
        dsimp [q, z]
        ring
      rw [hbern]
      positivity
    · have hquarter' : 1 / 4 ≤ t := le_of_not_ge hquarter
      by_cases htwofifths : t ≤ 2 / 5
      · let z : ℝ := (20 / 3) * (t - 1 / 4)
        have hz0 : 0 ≤ z := by dsimp [z]; positivity
        have hz1 : z ≤ 1 := by dsimp [z]; linarith
        have hbern :
            (21 / 20 : ℝ) ^ 2 -
                (1 + q * (4 - 10 * t) + 9 * q ^ 2) =
              (1271 / 102400 : ℝ) * (1 - z) ^ 6 +
              6 * (149 / 25600 : ℝ) * z * (1 - z) ^ 5 +
              15 * (11 / 6400 : ℝ) * z ^ 2 * (1 - z) ^ 4 +
              20 * (11 / 16000 : ℝ) * z ^ 3 * (1 - z) ^ 3 +
              15 * (157 / 50000 : ℝ) * z ^ 4 * (1 - z) ^ 2 +
              6 * (469 / 50000 : ℝ) * z ^ 5 * (1 - z) +
              (4889 / 250000 : ℝ) * z ^ 6 := by
          dsimp [q, z]
          ring
        rw [hbern]
        positivity
      · have htwofifths' : 2 / 5 ≤ t := le_of_not_ge htwofifths
        let z : ℝ := (5 / 3) * (t - 2 / 5)
        have hz0 : 0 ≤ z := by dsimp [z]; positivity
        have hz1 : z ≤ 1 := by dsimp [z]; linarith
        have hbern :
            (21 / 20 : ℝ) ^ 2 -
                (1 + q * (4 - 10 * t) + 9 * q ^ 2) =
              (4889 / 250000 : ℝ) * (1 - z) ^ 6 +
              6 * (3013 / 50000 : ℝ) * z * (1 - z) ^ 5 +
              15 * (8197 / 50000 : ℝ) * z ^ 2 * (1 - z) ^ 4 +
              20 * (3401 / 10000 : ℝ) * z ^ 3 * (1 - z) ^ 3 +
              15 * (1117 / 2000 : ℝ) * z ^ 4 * (1 - z) ^ 2 +
              6 * (281 / 400 : ℝ) * z ^ 5 * (1 - z) +
              (41 / 400 : ℝ) * z ^ 6 := by
          dsimp [q, z]
          ring
        rw [hbern]
        positivity
  have hscaled_sq :
      ‖(((2 * Real.pi * t : ℝ) : ℂ) * prawitzKernel t)‖ ^ 2 ≤
        (21 / 20 : ℝ) ^ 2 := by
    rw [norm_scaled_prawitzKernel_sq ht0]
    dsimp [y] at *
    calc
      (Real.pi * t * (1 - t)) ^ 2 +
          (1 - Real.pi * t * (1 - t) * d) ^ 2
          ≤ 10 * t ^ 2 * (1 - t) ^ 2 + (1 - 3 * q) ^ 2 :=
        add_le_add hreal_sq hres_sq
      _ = 1 + q * (4 - 10 * t) + 9 * q ^ 2 := hrewrite
      _ ≤ (21 / 20 : ℝ) ^ 2 := hpoly
  have hscaled :
      ‖(((2 * Real.pi * t : ℝ) : ℂ) * prawitzKernel t)‖ ≤
        (21 / 20 : ℝ) := by
    rw [← sq_le_sq₀ (norm_nonneg _) (by norm_num)]
    exact hscaled_sq
  have hfactor : 0 < 2 * Real.pi * t := by positivity
  rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hfactor] at hscaled
  apply (le_div_iff₀ hfactor).2
  simpa [mul_comm] using hscaled

/-- A slightly weaker decimal form retained for downstream callers. -/
lemma norm_prawitzKernel_le_eleven_tenths_div {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) :
    ‖prawitzKernel t‖ ≤ (11 / 10 : ℝ) / (2 * Real.pi * t) := by
  calc
    ‖prawitzKernel t‖ ≤
        (21 / 20 : ℝ) / (2 * Real.pi * t) :=
      norm_prawitzKernel_le_twenty_one_twentieths_div ht0 ht1
    _ ≤ (11 / 10 : ℝ) / (2 * Real.pi * t) := by
      exact div_le_div_of_nonneg_right (by norm_num) (by positivity)

/-- A convenient bound for the full Prawitz kernel on `(0,1)`. -/
lemma norm_prawitzKernel_le {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ‖prawitzKernel t‖ ≤ 1 / 2 + 1 / (2 * Real.pi * t) := by
  let z : ℂ := Complex.I / ((2 * Real.pi * t : ℝ) : ℂ)
  have hz : ‖z‖ = 1 / (2 * Real.pi * t) := by
    dsimp [z]
    rw [norm_div, norm_I, norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < 2 * Real.pi * t)]
  calc
    ‖prawitzKernel t‖ =
        ‖(prawitzKernel t - z) + z‖ := by congr 1; ring
    _ ≤ ‖prawitzKernel t - z‖ + ‖z‖ := norm_add_le _ _
    _ ≤ 1 / 2 + 1 / (2 * Real.pi * t) := by
      rw [hz]
      gcongr
      simpa [z] using norm_prawitzKernel_sub_singular_le_half ht0 ht1

end HDP.Appendix
