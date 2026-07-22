import HighDimensionalProbability.Appendix.Infra.BerryEsseenTaylor
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Characteristic-function bounds for Berry--Esseen

This file turns the one-variable Taylor estimate into a quantitative estimate
for the characteristic function of a normalized i.i.d. sum.
-/

open MeasureTheory ProbabilityTheory Real Complex
open scoped Real

namespace HDP.Appendix

/-- Powers are Lipschitz on the closed unit disk, with Lipschitz constant `n`. -/
lemma norm_pow_sub_pow_le (a b : ℂ) (n : ℕ)
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖a ^ n - b ^ n‖ ≤ n * ‖a - b‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ]
      have hid : a ^ n * a - b ^ n * b =
          a ^ n * (a - b) + (a ^ n - b ^ n) * b := by
        ring
      rw [hid]
      calc
        ‖a ^ n * (a - b) + (a ^ n - b ^ n) * b‖
            ≤ ‖a ^ n * (a - b)‖ + ‖(a ^ n - b ^ n) * b‖ := norm_add_le _ _
        _ = ‖a‖ ^ n * ‖a - b‖ + ‖a ^ n - b ^ n‖ * ‖b‖ := by
          rw [norm_mul, norm_mul, norm_pow]
        _ ≤ 1 * ‖a - b‖ + (n * ‖a - b‖) * 1 := by
          gcongr
          exact pow_le_one₀ (norm_nonneg a) ha
        _ = (Nat.succ n) * ‖a - b‖ := by
          norm_num [Nat.cast_succ]
          ring

/-- Refined power-difference estimate retaining the geometric decay when both
base points lie in a disk of radius `r`. -/
lemma norm_pow_succ_sub_pow_succ_le (a b : ℂ) (n : ℕ) (r : ℝ)
    (hr : 0 ≤ r) (ha : ‖a‖ ≤ r) (hb : ‖b‖ ≤ r) :
    ‖a ^ (n + 1) - b ^ (n + 1)‖ ≤
      (n + 1) * ‖a - b‖ * r ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hid : a ^ (n + 2) - b ^ (n + 2) =
          a ^ (n + 1) * (a - b) +
            (a ^ (n + 1) - b ^ (n + 1)) * b := by
        ring
      rw [hid]
      calc
        ‖a ^ (n + 1) * (a - b) +
            (a ^ (n + 1) - b ^ (n + 1)) * b‖
            ≤ ‖a ^ (n + 1) * (a - b)‖ +
              ‖(a ^ (n + 1) - b ^ (n + 1)) * b‖ := norm_add_le _ _
        _ = ‖a‖ ^ (n + 1) * ‖a - b‖ +
              ‖a ^ (n + 1) - b ^ (n + 1)‖ * ‖b‖ := by
          rw [norm_mul, norm_mul, norm_pow]
        _ ≤ r ^ (n + 1) * ‖a - b‖ +
              ((n + 1) * ‖a - b‖ * r ^ n) * r := by
          gcongr
        _ = (Nat.succ n + 1) * ‖a - b‖ * r ^ (Nat.succ n) := by
          norm_num [Nat.cast_succ, pow_succ]
          ring

/-- The quadratic remainder bound for `exp (-x)`, valid on the whole
nonnegative half-line. -/
lemma abs_exp_neg_sub_linear_le (x : ℝ) (hx : 0 ≤ x) :
    |Real.exp (-x) - (1 - x)| ≤ x ^ 2 / 2 := by
  have hlow : 1 - x ≤ Real.exp (-x) := Real.one_sub_le_exp_neg x
  rw [abs_of_nonneg (sub_nonneg.mpr hlow)]
  have hseries : 1 + x + x ^ 2 / 2 ≤ Real.exp x := by
    have h := Real.sum_le_exp_of_nonneg hx 3
    norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
    exact h
  have hp : 0 < 1 + x + x ^ 2 / 2 := by
    positivity
  have hinv : (1 + x + x ^ 2 / 2)⁻¹ ≤ 1 - x + x ^ 2 / 2 := by
    rw [inv_le_iff_one_le_mul₀ hp]
    nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x - 1)]
  have heinv : (Real.exp x)⁻¹ ≤ (1 + x + x ^ 2 / 2)⁻¹ :=
    (inv_le_inv₀ (Real.exp_pos x) hp).2 hseries
  calc
    Real.exp (-x) - (1 - x)
        = (Real.exp x)⁻¹ - (1 - x) := by rw [Real.exp_neg]
    _ ≤ (1 + x + x ^ 2 / 2)⁻¹ - (1 - x) := sub_le_sub_right heinv _
    _ ≤ (1 - x + x ^ 2 / 2) - (1 - x) := sub_le_sub_right hinv _
    _ = x ^ 2 / 2 := by ring

/-- The accumulated quadratic error between `(1 - x)ⁿ` and `exp (-n x)`. -/
lemma norm_one_sub_pow_sub_exp_le (n : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ‖(((1 - x : ℝ) : ℂ) ^ n) - (Real.exp (-(n * x)) : ℂ)‖ ≤
      n * (x ^ 2 / 2) := by
  have ha : ‖((1 - x : ℝ) : ℂ)‖ ≤ 1 := by
    rw [norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hx1)]
    linarith
  have hb : ‖(Real.exp (-x) : ℂ)‖ ≤ 1 := by
    rw [norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx0)
  have hpow :=
    norm_pow_sub_pow_le ((1 - x : ℝ) : ℂ) (Real.exp (-x) : ℂ) n ha hb
  have hone : ‖((1 - x : ℝ) : ℂ) - (Real.exp (-x) : ℂ)‖ ≤ x ^ 2 / 2 := by
    rw [← ofReal_sub, norm_real, Real.norm_eq_abs, abs_sub_comm]
    exact abs_exp_neg_sub_linear_le x hx0
  calc
    ‖(((1 - x : ℝ) : ℂ) ^ n) - (Real.exp (-(n * x)) : ℂ)‖
        = ‖(((1 - x : ℝ) : ℂ) ^ n) - ((Real.exp (-x) : ℂ) ^ n)‖ := by
          congr 2
          norm_cast
          rw [← Real.exp_nat_mul]
          congr 1
          ring
    _ ≤ n * ‖((1 - x : ℝ) : ℂ) - (Real.exp (-x) : ℂ)‖ := hpow
    _ ≤ n * (x ^ 2 / 2) := by
      gcongr

/-- The same exponential comparison with the geometric damping factor kept. -/
lemma norm_one_sub_pow_sub_exp_le_decay (n : ℕ) (hn : 0 < n)
    (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ‖(((1 - x : ℝ) : ℂ) ^ n) - (Real.exp (-(n * x)) : ℂ)‖ ≤
      n * (x ^ 2 / 2) * Real.exp (-((n - 1) * x)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hq0 : 0 ≤ 1 - x := sub_nonneg.mpr hx1
  have hqexp : 1 - x ≤ Real.exp (-x) := Real.one_sub_le_exp_neg x
  have hq :
      ‖((1 - x : ℝ) : ℂ)‖ ≤ Real.exp (-x) := by
    rw [norm_real, Real.norm_eq_abs, abs_of_nonneg hq0]
    exact hqexp
  have he :
      ‖(Real.exp (-x) : ℂ)‖ ≤ Real.exp (-x) := by
    rw [norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hpow := norm_pow_succ_sub_pow_succ_le
    ((1 - x : ℝ) : ℂ) (Real.exp (-x) : ℂ) k
    (Real.exp (-x)) (le_of_lt (Real.exp_pos _)) hq he
  have hone : ‖((1 - x : ℝ) : ℂ) - (Real.exp (-x) : ℂ)‖ ≤
      x ^ 2 / 2 := by
    rw [← ofReal_sub, norm_real, Real.norm_eq_abs, abs_sub_comm]
    exact abs_exp_neg_sub_linear_le x hx0
  calc
    ‖(((1 - x : ℝ) : ℂ) ^ (k + 1)) -
        (Real.exp (-((↑(k + 1) : ℝ) * x)) : ℂ)‖
        = ‖(((1 - x : ℝ) : ℂ) ^ (k + 1)) -
            ((Real.exp (-x) : ℂ) ^ (k + 1))‖ := by
          congr 2
          norm_cast
          rw [← Real.exp_nat_mul]
          congr 1
          ring
    _ ≤ (k + 1) *
          ‖((1 - x : ℝ) : ℂ) - (Real.exp (-x) : ℂ)‖ *
            Real.exp (-x) ^ k := hpow
    _ ≤ (k + 1) * (x ^ 2 / 2) * Real.exp (-x) ^ k := by
      gcongr
    _ = (k + 1) * (x ^ 2 / 2) *
          Real.exp (-((k : ℝ) * x)) := by
      rw [← Real.exp_nat_mul]
      congr 2
      ring
    _ = (↑(k + 1) : ℝ) * (x ^ 2 / 2) *
          Real.exp (-(((↑(k + 1) : ℝ) - 1) * x)) := by
      norm_num [Nat.cast_succ]

/-- A one-step characteristic-function approximation, propagated through an
`n`th power and compared with the corresponding Gaussian exponential. -/
lemma norm_charFun_pow_sub_gaussian_le (A : ℂ) (n : ℕ) (u beta : ℝ)
    (hA : ‖A‖ ≤ 1) (hx : u ^ 2 / 2 ≤ 1)
    (hone : ‖A - (1 - u ^ 2 / 2)‖ ≤ |u| ^ 3 / 6 * beta) :
    ‖A ^ n - (Real.exp (-(n * (u ^ 2 / 2))) : ℂ)‖ ≤
      n * (|u| ^ 3 / 6 * beta) + n * ((u ^ 2 / 2) ^ 2 / 2) := by
  let x : ℝ := u ^ 2 / 2
  have hx0 : 0 ≤ x := by
    dsimp [x]
    positivity
  have hq : ‖((1 - x : ℝ) : ℂ)‖ ≤ 1 := by
    rw [norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr (by simpa [x] using hx))]
    exact sub_le_self 1 hx0
  have h1 := norm_pow_sub_pow_le A ((1 - x : ℝ) : ℂ) n hA hq
  have h1' : ‖A ^ n - ((1 - x : ℝ) : ℂ) ^ n‖ ≤
      n * (|u| ^ 3 / 6 * beta) := by
    calc
      ‖A ^ n - ((1 - x : ℝ) : ℂ) ^ n‖
          ≤ n * ‖A - ((1 - x : ℝ) : ℂ)‖ := h1
      _ ≤ n * (|u| ^ 3 / 6 * beta) := by
        gcongr
        simpa [x] using hone
  have h2 := norm_one_sub_pow_sub_exp_le n x hx0 (by simpa [x] using hx)
  have htri :
      ‖A ^ n - (Real.exp (-(n * x)) : ℂ)‖ ≤
        ‖A ^ n - ((1 - x : ℝ) : ℂ) ^ n‖ +
          ‖((1 - x : ℝ) : ℂ) ^ n - (Real.exp (-(n * x)) : ℂ)‖ := by
    rw [show A ^ n - (Real.exp (-(n * x)) : ℂ) =
      (A ^ n - ((1 - x : ℝ) : ℂ) ^ n) +
        (((1 - x : ℝ) : ℂ) ^ n - (Real.exp (-(n * x)) : ℂ)) by ring]
    exact norm_add_le _ _
  calc
    ‖A ^ n - (Real.exp (-(n * (u ^ 2 / 2))) : ℂ)‖
        = ‖A ^ n - (Real.exp (-(n * x)) : ℂ)‖ := by rfl
    _ ≤ ‖A ^ n - ((1 - x : ℝ) : ℂ) ^ n‖ +
          ‖((1 - x : ℝ) : ℂ) ^ n - (Real.exp (-(n * x)) : ℂ)‖ := htri
    _ ≤ n * (|u| ^ 3 / 6 * beta) + n * (x ^ 2 / 2) := add_le_add h1' h2
    _ = n * (|u| ^ 3 / 6 * beta) + n * ((u ^ 2 / 2) ^ 2 / 2) := by rfl

/-- Local characteristic-function comparison with Gaussian damping.  The
condition `|u| * beta ≤ 1` is the classical Berry--Esseen low-frequency
window. -/
lemma norm_charFun_pow_sub_gaussian_le_decay
    (A : ℂ) (n : ℕ) (hn : 0 < n) (u beta : ℝ)
    (hbeta : 1 ≤ beta) (hu : |u| * beta ≤ 1)
    (hone : ‖A - (1 - u ^ 2 / 2)‖ ≤ |u| ^ 3 / 6 * beta) :
    ‖A ^ n - (Real.exp (-(n * (u ^ 2 / 2))) : ℂ)‖ ≤
      n * (|u| ^ 3 / 6 * beta) *
          Real.exp (-((n - 1) * (u ^ 2 / 3))) +
        n * ((u ^ 2 / 2) ^ 2 / 2) *
          Real.exp (-((n - 1) * (u ^ 2 / 2))) := by
  have habs0 : 0 ≤ |u| := abs_nonneg _
  have habs1 : |u| ≤ 1 := by
    calc
      |u| = |u| * 1 := by ring
      _ ≤ |u| * beta := mul_le_mul_of_nonneg_left hbeta habs0
      _ ≤ 1 := hu
  have hu2 : u ^ 2 ≤ 1 := by
    nlinarith [sq_abs u]
  let x : ℝ := u ^ 2 / 2
  have hx0 : 0 ≤ x := by
    dsimp [x]
    positivity
  have hx1 : x ≤ 1 := by
    dsimp [x]
    nlinarith
  have hq0 : 0 ≤ 1 - x := sub_nonneg.mpr hx1
  have hrem : |u| ^ 3 / 6 * beta ≤ u ^ 2 / 6 := by
    calc
      |u| ^ 3 / 6 * beta =
          (|u| ^ 2 / 6) * (|u| * beta) := by ring
      _ = (u ^ 2 / 6) * (|u| * beta) := by
        rw [sq_abs]
      _ ≤ (u ^ 2 / 6) * 1 :=
        mul_le_mul_of_nonneg_left hu (by positivity)
      _ = u ^ 2 / 6 := by ring
  let r : ℝ := Real.exp (-(u ^ 2 / 3))
  have hr0 : 0 ≤ r := le_of_lt (Real.exp_pos _)
  have hlinear_exp : 1 - u ^ 2 / 3 ≤ r := by
    dsimp [r]
    exact Real.one_sub_le_exp_neg _
  have hq : ‖((1 - x : ℝ) : ℂ)‖ ≤ r := by
    rw [norm_real, Real.norm_eq_abs, abs_of_nonneg hq0]
    calc
      1 - x ≤ 1 - u ^ 2 / 3 := by
        dsimp [x]
        nlinarith
      _ ≤ r := hlinear_exp
  have hA : ‖A‖ ≤ r := by
    calc
      ‖A‖ = ‖(A - ((1 - x : ℝ) : ℂ)) + ((1 - x : ℝ) : ℂ)‖ := by
        congr 1
        ring
      _ ≤ ‖A - ((1 - x : ℝ) : ℂ)‖ +
          ‖((1 - x : ℝ) : ℂ)‖ := norm_add_le _ _
      _ ≤ (|u| ^ 3 / 6 * beta) + (1 - x) := by
        gcongr
        · simpa [x] using hone
        · rw [norm_real, Real.norm_eq_abs, abs_of_nonneg hq0]
      _ ≤ u ^ 2 / 6 + (1 - x) := add_le_add hrem le_rfl
      _ = 1 - u ^ 2 / 3 := by
        dsimp [x]
        ring
      _ ≤ r := hlinear_exp
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hfirst := norm_pow_succ_sub_pow_succ_le
    A ((1 - x : ℝ) : ℂ) k r hr0 hA hq
  have hfirst' :
      ‖A ^ (k + 1) - ((1 - x : ℝ) : ℂ) ^ (k + 1)‖ ≤
        (k + 1) * (|u| ^ 3 / 6 * beta) *
          Real.exp (-(((↑(k + 1) : ℝ) - 1) * (u ^ 2 / 3))) := by
    calc
      ‖A ^ (k + 1) - ((1 - x : ℝ) : ℂ) ^ (k + 1)‖
          ≤ (k + 1) * ‖A - ((1 - x : ℝ) : ℂ)‖ * r ^ k := hfirst
      _ ≤ (k + 1) * (|u| ^ 3 / 6 * beta) * r ^ k := by
        gcongr
        simpa [x] using hone
      _ = (k + 1) * (|u| ^ 3 / 6 * beta) *
          Real.exp (-(((↑(k + 1) : ℝ) - 1) * (u ^ 2 / 3))) := by
        dsimp [r]
        rw [← Real.exp_nat_mul]
        congr 2
        norm_num [Nat.cast_succ]
  have hsecond := norm_one_sub_pow_sub_exp_le_decay
    (k + 1) (Nat.succ_pos k) x hx0 hx1
  have hsecond' :
      ‖((1 - x : ℝ) : ℂ) ^ (k + 1) -
          (Real.exp (-((↑(k + 1) : ℝ) * x)) : ℂ)‖ ≤
        (k + 1) * (x ^ 2 / 2) *
          Real.exp (-(((↑(k + 1) : ℝ) - 1) * x)) := by
    simpa [Nat.cast_succ] using hsecond
  have htri :
      ‖A ^ (k + 1) -
          (Real.exp (-((↑(k + 1) : ℝ) * x)) : ℂ)‖ ≤
        ‖A ^ (k + 1) - ((1 - x : ℝ) : ℂ) ^ (k + 1)‖ +
          ‖((1 - x : ℝ) : ℂ) ^ (k + 1) -
            (Real.exp (-((↑(k + 1) : ℝ) * x)) : ℂ)‖ := by
    rw [show A ^ (k + 1) -
        (Real.exp (-((↑(k + 1) : ℝ) * x)) : ℂ) =
      (A ^ (k + 1) - ((1 - x : ℝ) : ℂ) ^ (k + 1)) +
        (((1 - x : ℝ) : ℂ) ^ (k + 1) -
          (Real.exp (-((↑(k + 1) : ℝ) * x)) : ℂ)) by ring]
    exact norm_add_le _ _
  have hfinal :
      ‖A ^ (k + 1) -
          (Real.exp (-((↑(k + 1) : ℝ) * (u ^ 2 / 2))) : ℂ)‖ ≤
        (↑(k + 1) : ℝ) * (|u| ^ 3 / 6 * beta) *
            Real.exp (-(((↑(k + 1) : ℝ) - 1) * (u ^ 2 / 3))) +
          (↑(k + 1) : ℝ) * ((u ^ 2 / 2) ^ 2 / 2) *
            Real.exp (-(((↑(k + 1) : ℝ) - 1) * (u ^ 2 / 2))) := by
    calc
      ‖A ^ (k + 1) -
          (Real.exp (-((↑(k + 1) : ℝ) * (u ^ 2 / 2))) : ℂ)‖
          = ‖A ^ (k + 1) -
              (Real.exp (-((↑(k + 1) : ℝ) * x)) : ℂ)‖ := by rfl
      _ ≤ ‖A ^ (k + 1) - ((1 - x : ℝ) : ℂ) ^ (k + 1)‖ +
            ‖((1 - x : ℝ) : ℂ) ^ (k + 1) -
              (Real.exp (-((↑(k + 1) : ℝ) * x)) : ℂ)‖ := htri
      _ ≤ (↑(k + 1) : ℝ) * (|u| ^ 3 / 6 * beta) *
            Real.exp (-(((↑(k + 1) : ℝ) - 1) * (u ^ 2 / 3))) +
          (↑(k + 1) : ℝ) * (x ^ 2 / 2) *
            Real.exp (-(((↑(k + 1) : ℝ) - 1) * x)) := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          add_le_add hfirst' hsecond'
      _ = (↑(k + 1) : ℝ) * (|u| ^ 3 / 6 * beta) *
            Real.exp (-(((↑(k + 1) : ℝ) - 1) * (u ^ 2 / 3))) +
          (↑(k + 1) : ℝ) * ((u ^ 2 / 2) ^ 2 / 2) *
            Real.exp (-(((↑(k + 1) : ℝ) - 1) * (u ^ 2 / 2))) := by rfl
  simpa only [Nat.cast_succ] using hfinal

/-- A medium-frequency decay bound.  The constant `3 / 2` is chosen so
that the elementary third-order Taylor estimate still forces a fixed
quadratic loss in the modulus. -/
lemma norm_le_exp_neg_sq_div_eight_of_taylor
    (A : ℂ) (u beta : ℝ)
    (hbeta : 1 ≤ beta) (hu : |u| * beta ≤ 3 / 2)
    (hone : ‖A - (1 - u ^ 2 / 2)‖ ≤ |u| ^ 3 / 6 * beta) :
    ‖A‖ ≤ Real.exp (-(u ^ 2 / 8)) := by
  have habs0 : 0 ≤ |u| := abs_nonneg _
  have habs : |u| ≤ 3 / 2 := by
    calc
      |u| = |u| * 1 := by ring
      _ ≤ |u| * beta := mul_le_mul_of_nonneg_left hbeta habs0
      _ ≤ 3 / 2 := hu
  have hu2 : u ^ 2 ≤ 9 / 4 := by
    nlinarith [sq_abs u]
  have hrem : |u| ^ 3 / 6 * beta ≤ u ^ 2 / 4 := by
    calc
      |u| ^ 3 / 6 * beta =
          (|u| ^ 2 / 6) * (|u| * beta) := by ring
      _ = (u ^ 2 / 6) * (|u| * beta) := by rw [sq_abs]
      _ ≤ (u ^ 2 / 6) * (3 / 2) :=
        mul_le_mul_of_nonneg_left hu (by positivity)
      _ = u ^ 2 / 4 := by ring
  have htri :
      ‖A‖ ≤ ‖A - ((1 - u ^ 2 / 2 : ℝ) : ℂ)‖ +
        ‖((1 - u ^ 2 / 2 : ℝ) : ℂ)‖ := by
    calc
      ‖A‖ = ‖(A - ((1 - u ^ 2 / 2 : ℝ) : ℂ)) +
          ((1 - u ^ 2 / 2 : ℝ) : ℂ)‖ := by congr 1; ring
      _ ≤ _ := norm_add_le _ _
  have hlinear : ‖A‖ ≤ 1 - u ^ 2 / 8 := by
    by_cases hq : u ^ 2 ≤ 2
    · have hq0 : 0 ≤ 1 - u ^ 2 / 2 := by linarith
      calc
        ‖A‖ ≤ ‖A - ((1 - u ^ 2 / 2 : ℝ) : ℂ)‖ +
            ‖((1 - u ^ 2 / 2 : ℝ) : ℂ)‖ := htri
        _ ≤ u ^ 2 / 4 + (1 - u ^ 2 / 2) := by
          gcongr
          · simpa using hone.trans hrem
          · rw [norm_real, Real.norm_eq_abs, abs_of_nonneg hq0]
        _ ≤ 1 - u ^ 2 / 8 := by nlinarith [sq_nonneg u]
    · have hq0 : 1 - u ^ 2 / 2 ≤ 0 := by linarith
      calc
        ‖A‖ ≤ ‖A - ((1 - u ^ 2 / 2 : ℝ) : ℂ)‖ +
            ‖((1 - u ^ 2 / 2 : ℝ) : ℂ)‖ := htri
        _ ≤ u ^ 2 / 4 + -(1 - u ^ 2 / 2) := by
          gcongr
          · simpa using hone.trans hrem
          · rw [norm_real, Real.norm_eq_abs, abs_of_nonpos hq0]
        _ ≤ 1 - u ^ 2 / 8 := by nlinarith
  exact hlinear.trans (Real.one_sub_le_exp_neg _)

/-- The medium-frequency estimate propagated through an `n`th power. -/
lemma norm_pow_le_exp_neg_nat_mul_sq_div_eight_of_taylor
    (A : ℂ) (n : ℕ) (u beta : ℝ)
    (hbeta : 1 ≤ beta) (hu : |u| * beta ≤ 3 / 2)
    (hone : ‖A - (1 - u ^ 2 / 2)‖ ≤ |u| ^ 3 / 6 * beta) :
    ‖A ^ n‖ ≤ Real.exp (-((n : ℝ) * u ^ 2 / 8)) := by
  have hbase :=
    norm_le_exp_neg_sq_div_eight_of_taylor A u beta hbeta hu hone
  calc
    ‖A ^ n‖ = ‖A‖ ^ n := norm_pow _ _
    _ ≤ (Real.exp (-(u ^ 2 / 8))) ^ n := by
      exact pow_le_pow_left₀ (norm_nonneg A) hbase n
    _ = Real.exp (-((n : ℝ) * u ^ 2 / 8)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- Lyapunov's moment inequality in the variance-one case:
the third absolute moment is at least one. -/
lemma third_absolute_moment_ge_one [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : MemLp X 3 P)
    (hsecond : ∫ ω, X ω ^ 2 ∂P = 1) :
    1 ≤ ∫ ω, |X ω| ^ 3 ∂P := by
  have he : eLpNorm X 2 P ≤ eLpNorm X 3 P :=
    eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
      hX.aestronglyMeasurable
  have hlp : lpNorm X 2 P ≤ lpNorm X 3 P := by
    rw [← toReal_eLpNorm hX.aestronglyMeasurable,
      ← toReal_eLpNorm hX.aestronglyMeasurable]
    exact ENNReal.toReal_mono hX.eLpNorm_ne_top he
  have hlp2 : lpNorm X 2 P = 1 := by
    rw [lpNorm_eq_integral_norm_rpow_toReal (p := (2 : ENNReal))
      (by norm_num) (by norm_num) hX.aestronglyMeasurable]
    have hi : (∫ x, ‖X x‖ ^ (2 : ℝ) ∂P) = 1 := by
      calc
        (∫ x, ‖X x‖ ^ (2 : ℝ) ∂P) =
            ∫ x, X x ^ 2 ∂P := by
          congr with x
          rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
        _ = 1 := hsecond
    simp only [ENNReal.toReal_ofNat]
    rw [hi]
    simp
  have hlp3 : lpNorm X 3 P =
      (∫ ω, |X ω| ^ 3 ∂P) ^ ((3 : ℝ)⁻¹) := by
    rw [lpNorm_eq_integral_norm_rpow_toReal (p := (3 : ENNReal))
      (by norm_num) (by norm_num) hX.aestronglyMeasurable]
    simp only [ENNReal.toReal_ofNat]
    congr 2
    funext x
    calc
      ‖X x‖ ^ (3 : ℝ) = |X x| ^ (3 : ℝ) := by rfl
      _ = |X x| ^ (3 : ℕ) := Real.rpow_natCast _ 3
  rw [hlp2, hlp3] at hlp
  have hbeta0 : 0 ≤ ∫ ω, |X ω| ^ 3 ∂P :=
    integral_nonneg fun _ => by positivity
  have hcubed :=
    pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1) hlp 3
  norm_num at hcubed
  have hid :
      ((∫ ω, |X ω| ^ 3 ∂P) ^ ((3 : ℝ)⁻¹)) ^ 3 =
        ∫ ω, |X ω| ^ 3 ∂P :=
    Real.rpow_inv_natCast_pow hbeta0 (by norm_num)
  nlinarith

/-- Quantitative characteristic-function approximation for a normalized sum
of centered, variance-one i.i.d. random variables. -/
lemma norm_charFun_inv_sqrt_mul_sum_sub_gaussian_le [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (hindep : iIndepFun X P)
    (hident : ∀ i : ℕ, IdentDistrib (X i) (X 0) P P)
    (hX : MemLp (X 0) 3 P) (hmean : ∫ ω, X 0 ω ∂P = 0)
    (hsecond : ∫ ω, X 0 ω ^ 2 ∂P = 1)
    {n : ℕ} (hn : 0 < n) (t : ℝ)
    (ht : ((√n)⁻¹ * t) ^ 2 / 2 ≤ 1) :
    ‖charFun (P.map (fun ω ↦ (√n)⁻¹ * ∑ k ∈ Finset.range n, X k ω)) t -
        (Real.exp (-(t ^ 2 / 2)) : ℂ)‖ ≤
      |t| ^ 3 / (6 * √n) * (∫ ω, |X 0 ω| ^ 3 ∂P) +
        t ^ 4 / (8 * n) := by
  rw [charFun_inv_sqrt_mul_sum hindep hident]
  let u : ℝ := (√n)⁻¹ * t
  let beta : ℝ := ∫ ω, |X 0 ω| ^ 3 ∂P
  letI : IsProbabilityMeasure (P.map (X 0)) :=
    Measure.isProbabilityMeasure_map hX.aestronglyMeasurable.aemeasurable
  have hcf : ‖charFun (P.map (X 0)) u‖ ≤ 1 := norm_charFun_le_one u
  have htaylor :
      ‖charFun (P.map (X 0)) u - (1 - u ^ 2 / 2)‖ ≤
        |u| ^ 3 / 6 * beta := by
    simpa [u, beta] using
      norm_charFun_map_sub_gaussianQuadratic_le hX hmean hsecond u
  have h := norm_charFun_pow_sub_gaussian_le
    (charFun (P.map (X 0)) u) n u beta hcf (by simpa [u] using ht) htaylor
  have hscale : (n : ℝ) * (u ^ 2 / 2) = t ^ 2 / 2 := by
    dsimp [u]
    have hnR : (n : ℝ) ≠ 0 := by
      exact_mod_cast hn.ne'
    field_simp [hnR]
    rw [Real.sq_sqrt (Nat.cast_nonneg n)]
  have hfirst :
      (n : ℝ) * (|u| ^ 3 / 6 * beta) = |t| ^ 3 / (6 * √n) * beta := by
    dsimp [u]
    have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
    rw [abs_mul, abs_inv, abs_of_pos hs]
    field_simp [hs.ne']
    rw [Real.sq_sqrt (Nat.cast_nonneg n)]
  have hsecond' :
      (n : ℝ) * ((u ^ 2 / 2) ^ 2 / 2) = t ^ 4 / (8 * n) := by
    dsimp [u]
    have hnR : (n : ℝ) ≠ 0 := by
      exact_mod_cast hn.ne'
    have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
    field_simp [hnR, hs.ne']
    rw [show √(n : ℝ) ^ 4 = (√(n : ℝ) ^ 2) ^ 2 by ring,
      Real.sq_sqrt (Nat.cast_nonneg n)]
    ring
  calc
    ‖charFun (P.map (X 0)) ((√n)⁻¹ * t) ^ n -
        (Real.exp (-(t ^ 2 / 2)) : ℂ)‖
        ≤ n * (|u| ^ 3 / 6 * beta) + n * ((u ^ 2 / 2) ^ 2 / 2) := by
          simpa [u, hscale] using h
    _ = |t| ^ 3 / (6 * √n) * (∫ ω, |X 0 ω| ^ 3 ∂P) +
        t ^ 4 / (8 * n) := by
      rw [hfirst, hsecond']

/-- The normalized-sum characteristic-function estimate with Gaussian
damping retained throughout the Berry--Esseen low-frequency window. -/
lemma norm_charFun_inv_sqrt_mul_sum_sub_gaussian_le_decay
    [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (hindep : iIndepFun X P)
    (hident : ∀ i : ℕ, IdentDistrib (X i) (X 0) P P)
    (hX : MemLp (X 0) 3 P) (hmean : ∫ ω, X 0 ω ∂P = 0)
    (hsecond : ∫ ω, X 0 ω ^ 2 ∂P = 1)
    {n : ℕ} (hn : 0 < n) (t : ℝ)
    (ht : |(√n)⁻¹ * t| * (∫ ω, |X 0 ω| ^ 3 ∂P) ≤ 1) :
    ‖charFun (P.map (fun ω ↦ (√n)⁻¹ * ∑ k ∈ Finset.range n, X k ω)) t -
        (Real.exp (-(t ^ 2 / 2)) : ℂ)‖ ≤
      n * (|(√n)⁻¹ * t| ^ 3 / 6 *
          (∫ ω, |X 0 ω| ^ 3 ∂P)) *
        Real.exp (-((n - 1) * (((√n)⁻¹ * t) ^ 2 / 3))) +
      n * (((((√n)⁻¹ * t) ^ 2 / 2) ^ 2) / 2) *
        Real.exp (-((n - 1) * (((√n)⁻¹ * t) ^ 2 / 2))) := by
  rw [charFun_inv_sqrt_mul_sum hindep hident]
  let u : ℝ := (√n)⁻¹ * t
  let beta : ℝ := ∫ ω, |X 0 ω| ^ 3 ∂P
  letI : IsProbabilityMeasure (P.map (X 0)) :=
    Measure.isProbabilityMeasure_map hX.aestronglyMeasurable.aemeasurable
  have htaylor :
      ‖charFun (P.map (X 0)) u - (1 - u ^ 2 / 2)‖ ≤
        |u| ^ 3 / 6 * beta := by
    simpa [u, beta] using
      norm_charFun_map_sub_gaussianQuadratic_le hX hmean hsecond u
  have hbeta : 1 ≤ beta := by
    simpa [beta] using third_absolute_moment_ge_one hX hsecond
  have h := norm_charFun_pow_sub_gaussian_le_decay
    (charFun (P.map (X 0)) u) n hn u beta hbeta
      (by simpa [u, beta] using ht) htaylor
  have hscale : (n : ℝ) * (u ^ 2 / 2) = t ^ 2 / 2 := by
    dsimp [u]
    have hnR : (n : ℝ) ≠ 0 := by
      exact_mod_cast hn.ne'
    field_simp [hnR]
    rw [Real.sq_sqrt (Nat.cast_nonneg n)]
  simpa [u, beta, hscale] using h

/-- Medium-frequency decay for the characteristic function of the normalized
i.i.d. sum. -/
lemma norm_charFun_inv_sqrt_mul_sum_le_exp_neg_sq_div_eight
    [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (hindep : iIndepFun X P)
    (hident : ∀ i : ℕ, IdentDistrib (X i) (X 0) P P)
    (hX : MemLp (X 0) 3 P) (hmean : ∫ ω, X 0 ω ∂P = 0)
    (hsecond : ∫ ω, X 0 ω ^ 2 ∂P = 1)
    {n : ℕ} (hn : 0 < n) (t : ℝ)
    (ht : |(√n)⁻¹ * t| * (∫ ω, |X 0 ω| ^ 3 ∂P) ≤ 3 / 2) :
    ‖charFun (P.map (fun ω ↦ (√n)⁻¹ *
        ∑ k ∈ Finset.range n, X k ω)) t‖ ≤
      Real.exp (-(t ^ 2 / 8)) := by
  rw [charFun_inv_sqrt_mul_sum hindep hident]
  let u : ℝ := (√n)⁻¹ * t
  let beta : ℝ := ∫ ω, |X 0 ω| ^ 3 ∂P
  letI : IsProbabilityMeasure (P.map (X 0)) :=
    Measure.isProbabilityMeasure_map hX.aestronglyMeasurable.aemeasurable
  have htaylor :
      ‖charFun (P.map (X 0)) u - (1 - u ^ 2 / 2)‖ ≤
        |u| ^ 3 / 6 * beta := by
    simpa [u, beta] using
      norm_charFun_map_sub_gaussianQuadratic_le hX hmean hsecond u
  have hbeta : 1 ≤ beta := by
    simpa [beta] using third_absolute_moment_ge_one hX hsecond
  have h := norm_pow_le_exp_neg_nat_mul_sq_div_eight_of_taylor
    (charFun (P.map (X 0)) u) n u beta hbeta
      (by simpa [u, beta] using ht) htaylor
  have hscale : (n : ℝ) * u ^ 2 = t ^ 2 := by
    dsimp [u]
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp [hnR]
    rw [Real.sq_sqrt (Nat.cast_nonneg n)]
  simpa [u, beta, hscale] using h

end HDP.Appendix
