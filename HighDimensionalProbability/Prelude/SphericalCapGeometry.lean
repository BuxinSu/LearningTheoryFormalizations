import Mathlib

/-!
# Spherical-cap neighborhood geometry

This file proves the geometric inclusion displayed as equation (5.3): on the
sphere of radius `sqrt d`, the Euclidean `t`-neighborhood of a hemisphere
contains the band whose first coordinate is at most `t / sqrt 2`.
-/

open Real
open Set Metric

namespace HDP.Chapter5

/-- A point on a sphere admits a nearby point in the selected hemisphere,
with distance controlled by its positive normal coordinate.

**Lean implementation helper.** -/
private theorem hemisphere_nearby_point
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e v x : E) (r : ℝ) (hr : 0 ≤ r)
    (he : ‖e‖ = 1) (hv : ‖v‖ = 1) (hev : inner ℝ e v = 0)
    (hx : ‖x‖ = r) :
    ∃ y : E, ‖y‖ = r ∧ inner ℝ e y ≤ 0 ∧
      dist x y ≤ Real.sqrt 2 * max (inner ℝ e x) 0 := by
  let a : ℝ := inner ℝ e x
  by_cases ha : a ≤ 0
  · refine ⟨x, hx, ha, ?_⟩
    simp [a, ha]
  · have ha0 : 0 < a := lt_of_not_ge ha
    let z : E := x - a • e
    have heinner : inner ℝ e e = 1 := by
      rw [real_inner_self_eq_norm_sq, he]
      norm_num
    have hez : inner ℝ e z = 0 := by
      simp [z, a, inner_sub_right, inner_smul_right, he]
    have hzx : x = a • e + z := by simp [z]
    have hzsq : ‖z‖ ^ 2 = r ^ 2 - a ^ 2 := by
      have horth : inner ℝ (a • e) z = 0 := by
        rw [real_inner_smul_left, hez, mul_zero]
      have horthrev : inner ℝ z (a • e) = 0 := by
        rw [real_inner_comm, horth]
      have hnormx := congrArg (fun q : ℝ => q ^ 2) hx
      rw [hzx, ← real_inner_self_eq_norm_sq,
        inner_add_left, inner_add_right, inner_add_right,
        horth, real_inner_comm] at hnormx
      simp [horthrev, real_inner_self_eq_norm_sq, norm_smul, he,
        abs_of_pos ha0] at hnormx
      nlinarith
    have hzr : ‖z‖ ≤ r := by
      have hz0 : 0 ≤ ‖z‖ := norm_nonneg _
      nlinarith [sq_nonneg a]
    by_cases hz : z = 0
    · have hasq : a ^ 2 = r ^ 2 := by
        have := hzsq
        simp [hz] at this
        linarith
      have har : a = r := by nlinarith
      refine ⟨r • v, by simp [norm_smul, hv, abs_of_nonneg hr],
        ?_, ?_⟩
      · simp [inner_smul_right, hev]
      · rw [dist_eq_norm, hzx, hz, add_zero, har]
        have hnormsq :
            ‖r • e - r • v‖ ^ 2 = 2 * r ^ 2 := by
          rw [norm_sub_sq_real]
          simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, he, hv,
            real_inner_smul_left, inner_smul_right, hev]
          ring
        have hsqrt : (Real.sqrt 2) ^ 2 = 2 := by norm_num
        have hnonneg : 0 ≤ Real.sqrt 2 * a := mul_nonneg (Real.sqrt_nonneg _) ha0.le
        have hcoord : inner ℝ e (r • e) = a := by
          simp [inner_smul_right, real_inner_self_eq_norm_sq, he, har]
        rw [hcoord, max_eq_left ha0.le]
        nlinarith [norm_nonneg (r • e - r • v)]
    · have hznorm : 0 < ‖z‖ := norm_pos_iff.mpr hz
      let y : E := (r / ‖z‖) • z
      refine ⟨y, ?_, ?_, ?_⟩
      · simp [y, norm_smul, abs_of_nonneg hr, abs_of_pos hznorm,
          div_mul_cancel₀ r (ne_of_gt hznorm)]
      · simp [y, inner_smul_right, hez]
      · rw [dist_eq_norm, hzx]
        have horth : inner ℝ (a • e) z = 0 := by
          rw [real_inner_smul_left, hez, mul_zero]
        have hdiff : a • e + z - y = a • e + (1 - r / ‖z‖) • z := by
          simp [y, sub_eq_add_neg, add_assoc]
          module
        rw [hdiff]
        have horth' : inner ℝ (a • e) ((1 - r / ‖z‖) • z) = 0 := by
          rw [inner_smul_right, horth, mul_zero]
        have hratio : 1 ≤ r / ‖z‖ := (le_div_iff₀ hznorm).2 (by
          simpa using hzr)
        have habs : |1 - r / ‖z‖| = r / ‖z‖ - 1 := by
          convert abs_of_nonpos (sub_nonpos.mpr hratio) using 1 <;> ring
        have hnormsq :
            ‖a • e + (1 - r / ‖z‖) • z‖ ^ 2 =
              a ^ 2 + (r - ‖z‖) ^ 2 := by
          rw [norm_add_sq_real]
          simp [horth', norm_smul, Real.norm_eq_abs, he, abs_of_pos ha0,
            habs]
          field_simp [ne_of_gt hznorm]
        have hsq : ‖a • e + (1 - r / ‖z‖) • z‖ ^ 2 ≤ 2 * a ^ 2 := by
          rw [hnormsq]
          nlinarith [mul_nonneg (sub_nonneg.mpr hzr) (norm_nonneg z)]
        have hcoord : inner ℝ e (a • e + z) = a := by
          simp [inner_add_right, inner_smul_right,
            real_inner_self_eq_norm_sq, he, hez]
        rw [hcoord, max_eq_left ha0.le]
        have hsqrt : (Real.sqrt 2) ^ 2 = 2 := by norm_num
        have hnonneg : 0 ≤ Real.sqrt 2 * a :=
          mul_nonneg (Real.sqrt_nonneg _) ha0.le
        nlinarith [norm_nonneg (a • e + (1 - r / ‖z‖) • z)]

/-- The closed hemisphere of the `sqrt (n + 2)`-sphere selected by its first
coordinate.

**Lean implementation helper.** -/
def sphericalHemisphere (n : ℕ) :
    Set (EuclideanSpace ℝ (Fin (n + 2))) :=
  {x | ‖x‖ = Real.sqrt (n + 2 : ℝ) ∧ x 0 ≤ 0}

/-- The `t`-neighborhood of a hemisphere contains the coordinate band
`x₀ ≤ t / sqrt 2`.

**Book Equation (5.3).** -/
theorem sphericalCapBand_subset_neighborhood (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    {x : EuclideanSpace ℝ (Fin (n + 2)) |
        ‖x‖ = Real.sqrt (n + 2 : ℝ) ∧ x 0 ≤ t / Real.sqrt 2} ⊆
      {x | infDist x (sphericalHemisphere n) ≤ t} := by
  intro x hx
  let e : EuclideanSpace ℝ (Fin (n + 2)) := EuclideanSpace.single 0 1
  let v : EuclideanSpace ℝ (Fin (n + 2)) := EuclideanSpace.single 1 1
  have he : ‖e‖ = 1 := by simp [e]
  have hv : ‖v‖ = 1 := by simp [v]
  have hev : inner ℝ e v = 0 := by
    simp [e, v, EuclideanSpace.inner_single_left]
  have hr : 0 ≤ Real.sqrt (n + 2 : ℝ) := Real.sqrt_nonneg _
  obtain ⟨y, hyNorm, hyCoord, hxy⟩ :=
    hemisphere_nearby_point e v x (Real.sqrt (n + 2 : ℝ))
      hr he hv hev hx.1
  have hecoord (w : EuclideanSpace ℝ (Fin (n + 2))) :
      inner ℝ e w = w 0 := by
    simp [e, EuclideanSpace.inner_single_left]
  have hyMem : y ∈ sphericalHemisphere n := by
    exact ⟨hyNorm, by simpa [hecoord] using hyCoord⟩
  apply (infDist_le_dist_of_mem hyMem).trans
  apply hxy.trans
  rw [hecoord]
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  by_cases hx0 : x 0 ≤ 0
  · simp [max_eq_right hx0, ht]
  · rw [max_eq_left (le_of_not_ge hx0)]
    simpa [mul_comm] using (le_div_iff₀ hsqrt).mp hx.2

end HDP.Chapter5
