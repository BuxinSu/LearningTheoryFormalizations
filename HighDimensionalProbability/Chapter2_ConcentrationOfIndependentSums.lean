/-
Copyright (c) 2026 Buxin Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Buxin Su
-/

import HighDimensionalProbability.Chapter1_AnalysisAndProbabilityRefresher
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Complex.ExponentialBounds
import HighDimensionalProbability.Prelude.RandomGraph
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Data.Real.Pointwise
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import HighDimensionalProbability.Prelude.Orlicz
import Mathlib.MeasureTheory.Integral.Lebesgue.Sub
import Mathlib.Probability.Distributions.Exponential

/-!
# Chapter 2 — Concentration of Sums of Independent Random Variables

## Contents

- §2.1 Why concentration inequalities?
  - Gaussian tail estimates. **Book Proposition 2.1.2; Remark 2.1.3;
    Equations (2.2)–(2.4).**
  - Gaussian moments and their asymptotic scale. **Book Theorem 2.1.4.**
- §2.2 Hoeffding inequality
  - Rademacher sums and their MGF bounds. **Book Theorem 2.2.1;
    Equations (2.5)–(2.8).**
  - Bounded variables and Bernoulli sums. **Book Theorems 2.2.5 and 2.2.6.**
- §2.3 Chernoff inequality
  - Binomial upper and lower deviations. **Book Theorem 2.3.1;
    Equations (2.9)–(2.13); Corollary 2.3.4.**
- §2.4 Median-of-means estimator
  - A robust mean estimator under a finite-variance assumption. **Book Theorem 2.4.1.**
- §2.5 Degrees of random graphs
  - Degree concentration in the Erdős–Rényi model. **Book Proposition 2.5.1.**
- §2.6 Subgaussian distributions
  - Equivalent tails and moments, the ψ₂ norm, and centering.
    **Book Proposition 2.6.1; Definition 2.6.4; Proposition 2.6.6.**
- §2.7 Subgaussian Hoeffding and Khintchine inequalities
  - Subgaussian sums, Khintchine inequalities, and Gaussian comparison.
    **Book Proposition 2.7.1; Theorems 2.7.3 and 2.7.5; Proposition 2.7.6.**
  - Second-moment comparison and an expectation bound. **Book Equation (2.23);
    Lemma 2.7.8.**
- §2.8 Subexponential distributions
  - Equivalent tails and moments, the ψ₁ norm, and closure properties.
    **Book Proposition 2.8.1; Definition 2.8.4; Lemmas 2.8.5–2.8.6.**
- §2.9 Bernstein inequality
  - Bernstein's inequality and its two regimes. **Book Theorem 2.9.1;
    Equations (2.27)–(2.28).**
  - Weighted and bounded-summand forms. **Book Corollary 2.9.2; Theorem 2.9.5.**
-/

/-! ## Material formerly in `01_GaussianTails.lean` -/

section Source_01_GaussianTails

/-
Book Chapter 2, Section 2.1: Gaussian tails and motivating estimates.


and Exercises 2.2, 2.4, 2.6 on PDF pages 58--59 (printed 50--51).

The Gaussian-tail estimates are proved from the density by the same integration
arguments as in the source.  Exercise 2.4(b) is stated with the necessary hypothesis
`t > 0`; the printed range `t \in R` makes its right-hand side negative for `t < 0`.
-/






open MeasureTheory ProbabilityTheory Real Filter
open scoped ENNReal NNReal Topology unitInterval Nat

namespace HDP.Chapter2

variable {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}

/-- The standard Gaussian density, written in the form used in the source Proposition 2.1.2.

**Book Proposition 2.1.2.** -/
noncomputable def stdGaussianDensity (x : Real) : Real :=
  Real.exp (-x ^ 2 / 2) * (1 / Real.sqrt (2 * Real.pi))

/-- Identifies the standard Gaussian density with Mathlib's real Gaussian density.

**Lean implementation helper.** -/
lemma stdGaussianDensity_eq_gaussianPDFReal (x : Real) :
    stdGaussianDensity x = gaussianPDFReal 0 1 x := by
  rw [stdGaussianDensity, gaussianPDFReal_def]
  norm_num [one_div, mul_comm]

/-- Shows that the standard Gaussian density is positive.

**Lean implementation helper.** -/
lemma stdGaussianDensity_pos (x : Real) : 0 < stdGaussianDensity x := by
  rw [stdGaussianDensity]
  positivity

/-- Shows that the standard Gaussian density is nonnegative.

**Lean implementation helper.** -/
lemma stdGaussianDensity_nonneg (x : Real) : 0 <= stdGaussianDensity x :=
  (stdGaussianDensity_pos x).le

/-- Shows that the standard Gaussian density is continuous.

**Lean implementation helper.** -/
@[fun_prop]
lemma continuous_stdGaussianDensity : Continuous stdGaussianDensity := by
  unfold stdGaussianDensity
  fun_prop

/-- `stdGaussianDensity` is integrable on the real line.

**Lean implementation helper.** -/
lemma integrable_stdGaussianDensity : Integrable stdGaussianDensity := by
  rw [show stdGaussianDensity = gaussianPDFReal 0 1 by
    funext x
    exact stdGaussianDensity_eq_gaussianPDFReal x]
  exact integrable_gaussianPDFReal 0 1

/-- The first-moment integrand `x ↦ x * stdGaussianDensity x`, denoted by the `mul_stdGaussianDensity` term, is integrable on the real line.

**Lean implementation helper.** -/
lemma integrable_mul_stdGaussianDensity :
    Integrable (fun x : Real => x * stdGaussianDensity x) := by
  rw [show (fun x : Real => x * stdGaussianDensity x) =
      fun x => (x * Real.exp (-(1 / 2 : Real) * x ^ 2)) *
        (1 / Real.sqrt (2 * Real.pi)) by
    funext x
    simp only [stdGaussianDensity]
    ring_nf]
  exact (integrable_mul_exp_neg_mul_sq (by norm_num : (0 : Real) < 1 / 2)).mul_const _

/-- The second-moment integrand `x ↦ x ^ 2 * stdGaussianDensity x`, denoted by the `sq_mul_stdGaussianDensity` term, is integrable on the real line.

**Lean implementation helper.** -/
lemma integrable_sq_mul_stdGaussianDensity :
    Integrable (fun x : Real => x ^ 2 * stdGaussianDensity x) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq
    (by norm_num : (0 : Real) < 1 / 2) (by norm_num : (-1 : Real) < 2)
  convert h.mul_const (1 / Real.sqrt (2 * Real.pi)) using 1
  ext x
  simp only [stdGaussianDensity]
  rw [show -x ^ 2 / 2 = -(1 / 2 : Real) * x ^ 2 by ring]
  simp [mul_comm, mul_assoc]

/-- Computes the derivative of the standard Gaussian density.

**Lean implementation helper.** -/
lemma hasDerivAt_stdGaussianDensity (x : Real) :
    HasDerivAt stdGaussianDensity (-x * stdGaussianDensity x) x := by
  have hinner : HasDerivAt (fun y : Real => -y ^ 2 / 2) (-x) x := by
    exact ((hasDerivAt_pow 2 x).neg.div_const 2).congr_deriv (by ring)
  change HasDerivAt (fun y => Real.exp (-y ^ 2 / 2) *
    (1 / Real.sqrt (2 * Real.pi)))
    (-x * (Real.exp (-x ^ 2 / 2) * (1 / Real.sqrt (2 * Real.pi)))) x
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    hinner.exp.mul_const (1 / Real.sqrt (2 * Real.pi))

/-- Proves the convergence statement for the standard Gaussian density quantity `atTop`.

**Lean implementation helper.** -/
lemma tendsto_stdGaussianDensity_atTop :
    Tendsto stdGaussianDensity atTop (nhds 0) := by
  have hpow : Tendsto (fun x : Real => x ^ (2 : Nat)) atTop atTop :=
    tendsto_pow_atTop (by norm_num)
  have hinner : Tendsto (fun x : Real => -(1 / 2 : Real) * x ^ 2) atTop atBot :=
    hpow.const_mul_atTop_of_neg (by norm_num)
  have hexp : Tendsto (fun x : Real => Real.exp (-(1 / 2 : Real) * x ^ 2))
      atTop (nhds 0) := tendsto_exp_atBot.comp hinner
  convert hexp.mul_const (1 / Real.sqrt (2 * Real.pi)) using 1
  · ext x
    simp only [stdGaussianDensity]
    congr 1
    ring_nf
  · simp

/-- The standard Gaussian tail is the Lebesgue integral of its density.

**Lean implementation helper.** -/
lemma stdGaussian_tail_eq_integral (t : Real) :
    (gaussianReal 0 1).real (Set.Ici t) =
      ∫ x in Set.Ioi t, stdGaussianDensity x := by
  rw [measureReal_def, gaussianReal_apply_eq_integral 0 (by norm_num) (Set.Ici t),
    ENNReal.toReal_ofReal]
  · rw [integral_Ici_eq_integral_Ioi]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    exact (stdGaussianDensity_eq_gaussianPDFReal x).symm
  · exact setIntegral_nonneg measurableSet_Ici
      (fun x _ => gaussianPDFReal_nonneg 0 1 x)

/-- First integration identity for the standard Gaussian density:
`integral_t^infinity x phi(x) dx = phi(t)`.

**Lean implementation helper.** -/
lemma integral_mul_stdGaussianDensity_Ioi (t : Real) :
    (∫ x in Set.Ioi t, x * stdGaussianDensity x) =
      stdGaussianDensity t := by
  have hderiv : ∀ x : Real, x ∈ Set.Ici t ->
      HasDerivAt (-stdGaussianDensity)
        (x * stdGaussianDensity x) x := by
    intro x _
    simpa [mul_comm] using (hasDerivAt_stdGaussianDensity x).neg
  have htend : Tendsto (fun x : Real => -stdGaussianDensity x) atTop (nhds 0) := by
    simpa using tendsto_stdGaussianDensity_atTop.neg
  have hint := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv
    integrable_mul_stdGaussianDensity.integrableOn htend
  simpa using hint

/-- Integration by parts expresses the standard Gaussian tail as its leading
Mills-ratio term minus a positive correction. This identity supports the lower
tail estimate and the expansion discussed after Proposition 2.1.2; it is not
the full alternating expansion mentioned in Remark 2.1.3.

**Lean implementation helper.** -/
lemma gaussian_mills_identity {t : Real} (ht : 0 < t) :
    (∫ x in Set.Ioi t, stdGaussianDensity x) =
      stdGaussianDensity t / t -
        ∫ x in Set.Ioi t, stdGaussianDensity x / x ^ 2 := by
  let u : Real -> Real := fun x => x⁻¹
  let v : Real -> Real := fun x => -stdGaussianDensity x
  let u' : Real -> Real := fun x => -(x ^ 2)⁻¹
  let v' : Real -> Real := fun x => x * stdGaussianDensity x
  have hu : ∀ x, x ∈ Set.Ioi t -> HasDerivAt u (u' x) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (ht.trans hx)
    simpa [u, u', one_div, pow_two] using (hasDerivAt_inv hx0)
  have hv : ∀ x, x ∈ Set.Ioi t -> HasDerivAt v (v' x) x := by
    intro x _
    change HasDerivAt (-stdGaussianDensity) (x * stdGaussianDensity x) x
    simpa [mul_comm] using (hasDerivAt_stdGaussianDensity x).neg
  have huv' : IntegrableOn (u * v') (Set.Ioi t) := by
    have heq : Set.EqOn (u * v') stdGaussianDensity (Set.Ioi t) := by
      intro x hx
      have hx0 : x ≠ 0 := ne_of_gt (ht.trans hx)
      simp [u, v', hx0]
    exact integrable_stdGaussianDensity.integrableOn.congr_fun heq.symm measurableSet_Ioi
  have hu'v : IntegrableOn (u' * v) (Set.Ioi t) := by
    have hdom : IntegrableOn (fun x => (t⁻¹ ^ 2) * stdGaussianDensity x)
        (Set.Ioi t) := (integrable_stdGaussianDensity.const_mul _).integrableOn
    change Integrable (u' * v) (volume.restrict (Set.Ioi t))
    refine hdom.integrable.mono ?_ ?_
    · exact (((measurable_id'.pow_const 2).inv.neg.mul
        continuous_stdGaussianDensity.measurable.neg).aestronglyMeasurable).mono_measure
          Measure.restrict_le_self
    · rw [ae_restrict_iff' measurableSet_Ioi]
      filter_upwards with x hx
      simp only [u', v, Pi.mul_apply]
      have hphi := stdGaussianDensity_nonneg x
      have hxpos : 0 < x := ht.trans hx
      simp only [Real.norm_eq_abs, abs_mul, abs_neg, abs_inv, abs_pow,
        abs_of_pos hxpos, abs_of_pos ht, abs_of_nonneg hphi]
      have hinv : x⁻¹ ≤ t⁻¹ := (inv_le_inv₀ hxpos ht).2 hx.le
      have hinvpow : (x ^ 2)⁻¹ ≤ t⁻¹ ^ 2 := by
        calc
          (x ^ 2)⁻¹ = x⁻¹ ^ 2 := (inv_pow x 2).symm
          _ ≤ t⁻¹ ^ 2 := pow_le_pow_left₀ (inv_nonneg.mpr hxpos.le) hinv 2
      exact mul_le_mul_of_nonneg_right hinvpow (stdGaussianDensity_nonneg x)
  have hzero : Tendsto (u * v) (nhdsWithin t (Set.Ioi t))
      (nhds (-stdGaussianDensity t / t)) := by
    change Tendsto (fun x => u x * v x) (nhdsWithin t (Set.Ioi t))
      (nhds (-stdGaussianDensity t / t))
    have hucont : Tendsto u (nhdsWithin t (Set.Ioi t)) (nhds t⁻¹) :=
      (continuousAt_inv₀ ht.ne').tendsto.mono_left inf_le_left
    have hvcont : Tendsto v (nhdsWithin t (Set.Ioi t))
        (nhds (-stdGaussianDensity t)) :=
      ((hasDerivAt_stdGaussianDensity t).continuousAt.neg.tendsto).mono_left
        inf_le_left
    convert hucont.mul hvcont using 1
    ring_nf
  have hinfty : Tendsto (u * v) atTop (nhds 0) := by
    change Tendsto (fun x => u x * v x) atTop (nhds 0)
    have hu0 : Tendsto u atTop (nhds 0) := by
      simpa [u] using tendsto_inv_atTop_zero
    have hv0 : Tendsto v atTop (nhds 0) := by
      simpa [v] using tendsto_stdGaussianDensity_atTop.neg
    simpa using hu0.mul hv0
  have h := integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v hzero hinfty
  rw [show (∫ x in Set.Ioi t, u x * v' x) =
      ∫ x in Set.Ioi t, stdGaussianDensity x by
        exact setIntegral_congr_fun measurableSet_Ioi (fun x hx => by
          have hx0 : x ≠ 0 := ne_of_gt (ht.trans hx)
          simp [u, v', hx0])] at h
  rw [show (∫ x in Set.Ioi t, u' x * v x) =
      ∫ x in Set.Ioi t, stdGaussianDensity x / x ^ 2 by
        exact setIntegral_congr_fun measurableSet_Ioi (fun x hx => by
          have hx0 : x ≠ 0 := ne_of_gt (ht.trans hx)
          simp [u', v, div_eq_mul_inv]
          ac_rfl)] at h
  convert h using 1
  all_goals ring

/-! ## Book Proposition 2.1.2: Gaussian tails -/

/-- First for the canonical standard Gaussian
measure: `P{g >= t} <= phi(t)/t` for `t > 0`.

**Book Proposition 2.1.2.** -/
theorem gaussian_tail_upper_measure {t : Real} (ht : 0 < t) :
    (gaussianReal 0 1).real (Set.Ici t) <= stdGaussianDensity t / t := by
  rw [stdGaussian_tail_eq_integral]
  calc
    (∫ x in Set.Ioi t, stdGaussianDensity x)
        <= ∫ x in Set.Ioi t, t⁻¹ * (x * stdGaussianDensity x) := by
      refine setIntegral_mono_on integrable_stdGaussianDensity.integrableOn
        (integrable_mul_stdGaussianDensity.const_mul _).integrableOn measurableSet_Ioi ?_
      intro x hx
      have hxpos : 0 < x := ht.trans hx
      calc
        stdGaussianDensity x = t⁻¹ * (t * stdGaussianDensity x) := by
          field_simp
        _ <= t⁻¹ * (x * stdGaussianDensity x) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hx.le (stdGaussianDensity_nonneg x))
            (inv_nonneg.mpr ht.le)
    _ = t⁻¹ * stdGaussianDensity t := by
      rw [integral_const_mul, integral_mul_stdGaussianDensity_Ioi]
    _ = stdGaussianDensity t / t := by rw [inv_mul_eq_div]

/-- For the canonical
standard Gaussian measure.

**Book Exercise 2.2.** -/
theorem gaussian_tail_lower_measure {t : Real} (ht : 0 < t) :
    (t / (t ^ 2 + 1)) * stdGaussianDensity t <=
      (gaussianReal 0 1).real (Set.Ici t) := by
  let T := ∫ x in Set.Ioi t, stdGaussianDensity x
  let R := ∫ x in Set.Ioi t, stdGaussianDensity x / x ^ 2
  have hT : 0 <= T := setIntegral_nonneg measurableSet_Ioi
    (fun x _ => stdGaussianDensity_nonneg x)
  have hRint : IntegrableOn (fun x => stdGaussianDensity x / x ^ 2) (Set.Ioi t) := by
    have hdom : IntegrableOn (fun x => t⁻¹ ^ 2 * stdGaussianDensity x) (Set.Ioi t) :=
      (integrable_stdGaussianDensity.const_mul _).integrableOn
    change Integrable (fun x => stdGaussianDensity x / x ^ 2)
      (volume.restrict (Set.Ioi t))
    refine hdom.integrable.mono ?_ ?_
    · exact ((continuous_stdGaussianDensity.measurable.div
        (measurable_id'.pow_const 2)).aestronglyMeasurable).mono_measure
          Measure.restrict_le_self
    · rw [ae_restrict_iff' measurableSet_Ioi]
      filter_upwards with x hx
      have hxpos : 0 < x := ht.trans hx
      simp only [Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos hxpos,
        abs_of_nonneg (stdGaussianDensity_nonneg x)]
      rw [div_eq_mul_inv, mul_comm]
      rw [abs_of_nonneg (mul_nonneg (sq_nonneg t⁻¹)
        (stdGaussianDensity_nonneg x))]
      have hinv : x⁻¹ ≤ t⁻¹ := (inv_le_inv₀ hxpos ht).2 hx.le
      have hinvpow : (x ^ 2)⁻¹ ≤ t⁻¹ ^ 2 := by
        calc
          (x ^ 2)⁻¹ = x⁻¹ ^ 2 := (inv_pow x 2).symm
          _ ≤ t⁻¹ ^ 2 := pow_le_pow_left₀ (inv_nonneg.mpr hxpos.le) hinv 2
      exact mul_le_mul_of_nonneg_right
        hinvpow
        (stdGaussianDensity_nonneg x)
  have hR : R <= T / t ^ 2 := by
    change (∫ x in Set.Ioi t, stdGaussianDensity x / x ^ 2) <=
      (∫ x in Set.Ioi t, stdGaussianDensity x) / t ^ 2
    calc
      (∫ x in Set.Ioi t, stdGaussianDensity x / x ^ 2)
          <= ∫ x in Set.Ioi t, t⁻¹ ^ 2 * stdGaussianDensity x := by
        refine setIntegral_mono_on hRint
          (integrable_stdGaussianDensity.const_mul _).integrableOn measurableSet_Ioi ?_
        intro x hx
        have hxpos : 0 < x := ht.trans hx
        rw [div_eq_mul_inv, mul_comm]
        have hinv : x⁻¹ ≤ t⁻¹ := (inv_le_inv₀ hxpos ht).2 hx.le
        have hinvpow : (x ^ 2)⁻¹ ≤ t⁻¹ ^ 2 := by
          calc
            (x ^ 2)⁻¹ = x⁻¹ ^ 2 := (inv_pow x 2).symm
            _ ≤ t⁻¹ ^ 2 := pow_le_pow_left₀ (inv_nonneg.mpr hxpos.le) hinv 2
        exact mul_le_mul_of_nonneg_right
          hinvpow
          (stdGaussianDensity_nonneg x)
      _ = T / t ^ 2 := by
        rw [integral_const_mul]
        simp only [T]
        field_simp
  have hmills : T = stdGaussianDensity t / t - R := by
    simpa only [T, R] using gaussian_mills_identity ht
  have haux : stdGaussianDensity t / t <= T + T / t ^ 2 := by
    linarith
  have hmul := mul_le_mul_of_nonneg_right haux (sq_nonneg t)
  have htne : t ≠ 0 := ht.ne'
  field_simp [htne] at hmul
  rw [stdGaussian_tail_eq_integral]
  change (t / (t ^ 2 + 1)) * stdGaussianDensity t <= T
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : 0 < t ^ 2 + 1)]
  nlinarith

/-- For a random variable with
standard Gaussian law.

**Book Proposition 2.1.2.** -/
theorem gaussian_tail_upper {g : Omega -> Real}
    (hg : HasLaw g (gaussianReal 0 1) mu) {t : Real} (ht : 0 < t) :
    mu.real {omega | t <= g omega} <= stdGaussianDensity t / t := by
  rw [hg.measureReal_eq measurableSet_Ici]
  exact gaussian_tail_upper_measure ht

/-- For a random variable with standard Gaussian law. This is a main-text
proposition, so no exercise-leaf wrapper is provided.

**Book Proposition 2.1.2.** -/
theorem gaussian_tail_lower {g : Omega -> Real}
    (hg : HasLaw g (gaussianReal 0 1) mu) {t : Real} (ht : 0 < t) :
    (t / (t ^ 2 + 1)) * stdGaussianDensity t <=
      mu.real {omega | t <= g omega} := by
  rw [hg.measureReal_eq measurableSet_Ici]
  exact gaussian_tail_lower_measure ht

/-- For `t >= 1`, the standard Gaussian upper tail is bounded by
the value of its density at `t`.

**Book Proposition 2.1.2.** -/
theorem gaussian_tail_le_density {g : Omega -> Real}
    (hg : HasLaw g (gaussianReal 0 1) mu) {t : Real} (ht : 1 <= t) :
    mu.real {omega | t <= g omega} <= stdGaussianDensity t := by
  calc
    mu.real {omega | t <= g omega} <= stdGaussianDensity t / t :=
      gaussian_tail_upper hg (lt_of_lt_of_le zero_lt_one ht)
    _ <= stdGaussianDensity t := by
      rw [div_le_iff₀ (lt_of_lt_of_le zero_lt_one ht)]
      nlinarith [stdGaussianDensity_nonneg t]

/-! ## Book Exercises 2.4 and 2.6 -/

/-- Canonical-measure form:
`E[g 1_{g>t}] = phi(t)`. The identity in fact holds for every real `t`; the
source only asks for `t > 0`.

**Book Exercise 2.4(a).** -/
theorem gaussian_truncated_first_moment_measure (t : Real) :
    (∫ x in Set.Ioi t, x ∂gaussianReal 0 1) = stdGaussianDensity t := by
  rw [← integral_indicator measurableSet_Ioi,
    integral_gaussianReal_eq_integral_smul (by norm_num : (1 : NNReal) ≠ 0)]
  have hfun :
      (fun x : Real => gaussianPDFReal 0 1 x •
        Set.indicator (Set.Ioi t) (fun y : Real => y) x) =
        Set.indicator (Set.Ioi t) (fun x => x * stdGaussianDensity x) := by
    funext x
    by_cases hx : x ∈ Set.Ioi t
    · simp [hx, stdGaussianDensity_eq_gaussianPDFReal, mul_comm]
    · simp [hx]
  rw [hfun, integral_indicator measurableSet_Ioi]
  exact integral_mul_stdGaussianDensity_Ioi t

/-- Exercise 2.4(a) for a random variable with standard Gaussian law.

**Book Exercise 2.4(a).** -/
theorem gaussian_truncated_first_moment {g : Omega -> Real}
    (hg : HasLaw g (gaussianReal 0 1) mu) (hgm : Measurable g) (t : Real) :
    (∫ omega in {omega | t < g omega}, g omega ∂mu) = stdGaussianDensity t := by
  calc
    (∫ omega in {omega | t < g omega}, g omega ∂mu) =
        ∫ omega, Set.indicator (Set.Ioi t) (fun x : Real => x) (g omega) ∂mu := by
      change (∫ omega in g ⁻¹' Set.Ioi t, g omega ∂mu) = _
      have hfun :
          (fun omega => Set.indicator (Set.Ioi t) (fun x : Real => x) (g omega)) =
            Set.indicator (g ⁻¹' Set.Ioi t) g := by
        funext omega
        by_cases homega : g omega ∈ Set.Ioi t <;> simp [homega]
      rw [hfun, integral_indicator (hgm measurableSet_Ioi)]
    _ = ∫ x, Set.indicator (Set.Ioi t) (fun y : Real => y) x
          ∂gaussianReal 0 1 :=
      hg.integral_comp ((measurable_id.indicator measurableSet_Ioi).aestronglyMeasurable)
    _ = ∫ x in Set.Ioi t, x ∂gaussianReal 0 1 := by
      rw [integral_indicator measurableSet_Ioi]
    _ = stdGaussianDensity t := gaussian_truncated_first_moment_measure t

/-- Proves the convergence statement for `mul_stdGaussianDensity_atTop`.

**Lean implementation helper.** -/
lemma tendsto_mul_stdGaussianDensity_atTop :
    Tendsto (fun x : Real => x * stdGaussianDensity x) atTop (nhds 0) := by
  have hsmall := rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg
    (b := (1 / 2 : Real)) (by norm_num) (1 : Real)
  have href : Tendsto (fun x : Real => Real.exp (-(1 / 2 : Real) * x))
      atTop (nhds 0) := by
    have hlin : Tendsto (fun x : Real => -(1 / 2 : Real) * x) atTop atBot :=
      tendsto_id.const_mul_atTop_of_neg (by norm_num)
    exact tendsto_exp_atBot.comp hlin
  have hbase : Tendsto
      (fun x : Real => x ^ (1 : Real) * Real.exp (-(1 / 2 : Real) * x ^ 2))
      atTop (nhds 0) := hsmall.tendsto_zero_of_tendsto href
  have heq : (fun x : Real => x * stdGaussianDensity x) =ᶠ[atTop]
      (fun x => (x ^ (1 : Real) * Real.exp (-(1 / 2 : Real) * x ^ 2)) *
        (1 / Real.sqrt (2 * Real.pi))) := by
    filter_upwards [eventually_gt_atTop (0 : Real)] with x hx
    simp only [stdGaussianDensity, Real.rpow_one]
    rw [show -x ^ 2 / 2 = -(1 / 2 : Real) * x ^ 2 by ring]
    ring
  have hscaled : Tendsto
      (fun x => (x ^ (1 : Real) * Real.exp (-(1 / 2 : Real) * x ^ 2)) *
        (1 / Real.sqrt (2 * Real.pi))) atTop (nhds 0) := by
    simpa using hbase.mul_const (1 / Real.sqrt (2 * Real.pi))
  exact hscaled.congr' heq.symm

/-- Integration-by-parts identity behind Exercise 2.4(b).

**Book Exercise 2.4(b).** -/
lemma gaussian_truncated_second_moment_identity (t : Real) :
    (∫ x in Set.Ioi t, x ^ 2 * stdGaussianDensity x) =
      t * stdGaussianDensity t + ∫ x in Set.Ioi t, stdGaussianDensity x := by
  let F : Real -> Real := fun x => -x * stdGaussianDensity x
  let F' : Real -> Real := fun x => x ^ 2 * stdGaussianDensity x - stdGaussianDensity x
  have hderiv : ∀ x : Real, x ∈ Set.Ici t -> HasDerivAt F (F' x) x := by
    intro x _
    change HasDerivAt (fun y : Real => -y * stdGaussianDensity y)
      (x ^ 2 * stdGaussianDensity x - stdGaussianDensity x) x
    have h := (hasDerivAt_id x).neg.mul (hasDerivAt_stdGaussianDensity x)
    exact h.congr_deriv (by simp [id_eq]; ring)
  have hint : Integrable F' := by
    exact integrable_sq_mul_stdGaussianDensity.sub integrable_stdGaussianDensity
  have htend : Tendsto F atTop (nhds 0) := by
    simpa [F] using tendsto_mul_stdGaussianDensity_atTop.neg
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint.integrableOn htend
  simp only [F, F'] at h
  rw [integral_sub integrable_sq_mul_stdGaussianDensity.integrableOn
    integrable_stdGaussianDensity.integrableOn] at h
  linarith

/-- The second truncated moment under the canonical standard Gaussian measure.

**Lean implementation helper.** -/
lemma gaussian_truncated_second_moment_measure (t : Real) :
    (∫ x in Set.Ioi t, x ^ 2 ∂gaussianReal 0 1) =
      t * stdGaussianDensity t + (gaussianReal 0 1).real (Set.Ici t) := by
  rw [← integral_indicator measurableSet_Ioi,
    integral_gaussianReal_eq_integral_smul (by norm_num : (1 : NNReal) ≠ 0)]
  have hfun :
      (fun x : Real => gaussianPDFReal 0 1 x • Set.indicator (Set.Ioi t) (fun y => y ^ 2) x) =
        Set.indicator (Set.Ioi t) (fun x => x ^ 2 * stdGaussianDensity x) := by
    funext x
    by_cases hx : x ∈ Set.Ioi t
    · simp [hx, stdGaussianDensity_eq_gaussianPDFReal, mul_comm]
    · simp [hx]
  rw [hfun, integral_indicator measurableSet_Ioi,
    gaussian_truncated_second_moment_identity, stdGaussian_tail_eq_integral]

/-- **Corrected the source Exercise 2.4(b)**. The printed claim says `t ∈ R`, but its
right-hand side is negative for `t < 0`; the mathematically valid statement assumes
`t > 0`.

**Book Exercise 2.4(b).** -/
theorem gaussian_truncated_second_moment_upper_measure {t : Real} (ht : 0 < t) :
    (∫ x in Set.Ioi t, x ^ 2 ∂gaussianReal 0 1) <=
      (t + 1 / t) * stdGaussianDensity t := by
  rw [gaussian_truncated_second_moment_measure]
  have htail := gaussian_tail_upper_measure ht
  calc
    t * stdGaussianDensity t + (gaussianReal 0 1).real (Set.Ici t)
        <= t * stdGaussianDensity t + stdGaussianDensity t / t :=
      add_le_add le_rfl htail
    _ = (t + 1 / t) * stdGaussianDensity t := by ring

/-- Corrected to
`t > 0`, for a standard Gaussian random variable.

**Book Exercise 2.2.** -/
theorem gaussian_truncated_second_moment_upper {g : Omega -> Real}
    (hg : HasLaw g (gaussianReal 0 1) mu) (hgm : Measurable g)
    {t : Real} (ht : 0 < t) :
    (∫ omega in {omega | t < g omega}, (g omega) ^ 2 ∂mu) <=
      (t + 1 / t) * stdGaussianDensity t := by
  calc
    (∫ omega in {omega | t < g omega}, (g omega) ^ 2 ∂mu) =
        ∫ omega, Set.indicator (Set.Ioi t) (fun x : Real => x ^ 2) (g omega) ∂mu := by
      change (∫ omega in g ⁻¹' Set.Ioi t, (g omega) ^ 2 ∂mu) = _
      have hfun :
          (fun omega => Set.indicator (Set.Ioi t) (fun x : Real => x ^ 2) (g omega)) =
            Set.indicator (g ⁻¹' Set.Ioi t) (fun omega => (g omega) ^ 2) := by
        funext omega
        by_cases homega : g omega ∈ Set.Ioi t <;> simp [homega]
      rw [hfun, integral_indicator (hgm measurableSet_Ioi)]
    _ = ∫ x, Set.indicator (Set.Ioi t) (fun y : Real => y ^ 2) x
          ∂gaussianReal 0 1 :=
      hg.integral_comp
        (((measurable_id.pow_const 2).indicator measurableSet_Ioi).aestronglyMeasurable)
    _ = ∫ x in Set.Ioi t, x ^ 2 ∂gaussianReal 0 1 := by
      rw [integral_indicator measurableSet_Ioi]
    _ <= (t + 1 / t) * stdGaussianDensity t :=
      gaussian_truncated_second_moment_upper_measure ht

/-- The standard Gaussian MGF, used in the exponential-moment proof of Exercise 2.6.

**Book Equation (2.16).** -/
theorem gaussian_mgf {g : Omega -> Real}
    (hg : HasLaw g (gaussianReal 0 1) mu) (lam : Real) :
    mgf g mu lam = Real.exp (lam ^ 2 / 2) := by
  rw [mgf_gaussianReal hg.map_eq]
  congr 1
  norm_num

/-- If `g` has the standard Gaussian law, then the `exp_mul_of_hasLaw_standardGaussian` integrand `ω ↦ exp (lam * g ω)` is integrable.

**Lean implementation helper.** -/
lemma integrable_exp_mul_of_hasLaw_standardGaussian {g : Omega -> Real}
    (hg : HasLaw g (gaussianReal 0 1) mu) (lam : Real) :
    Integrable (fun omega => Real.exp (lam * g omega)) mu := by
  have h := integrable_exp_mul_gaussianReal (μ := (0 : Real)) (v := (1 : NNReal)) lam
  rw [← hg.map_eq] at h
  exact h.comp_aemeasurable hg.aemeasurable

/-- Gaussian upper
tail by the exponential moment method.

**Book Exercise 2.2.** -/
theorem gaussian_tail_exponential {g : Omega -> Real}
    (hg : HasLaw g (gaussianReal 0 1) mu) {t : Real} (ht : 0 <= t) :
    mu.real {omega | t <= g omega} <= Real.exp (-t ^ 2 / 2) := by
  letI : IsProbabilityMeasure mu := hg.isProbabilityMeasure
  have h := measure_ge_le_exp_mul_mgf (μ := mu) (X := g) t ht
    (integrable_exp_mul_of_hasLaw_standardGaussian hg t)
  rw [gaussian_mgf hg] at h
  calc
    mu.real {omega | t <= g omega}
        <= Real.exp (-t * t) * Real.exp (t ^ 2 / 2) := h
    _ = Real.exp (-t ^ 2 / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-! ## Gaussian square-exponential integral (Exercise 2.24(d) infrastructure) -/

/-- A convenient unsimplified form of the Gaussian square-exponential integral.
For `a < 1/2`, `E exp(a g^2)` is another Gaussian integral.

**Lean implementation helper.** -/
theorem integral_exp_sq_mul_standardGaussian {a : Real} (_ha : a < 1 / 2) :
    (∫ x, Real.exp (a * x ^ 2) ∂gaussianReal 0 1) =
      (Real.sqrt (2 * Real.pi))⁻¹ *
        Real.sqrt (Real.pi / (1 / 2 - a)) := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : NNReal) ≠ 0)]
  have hfun :
      (fun x : Real => gaussianPDFReal 0 1 x • Real.exp (a * x ^ 2)) =
        fun x => (Real.sqrt (2 * Real.pi))⁻¹ *
          Real.exp (-(1 / 2 - a) * x ^ 2) := by
    funext x
    simp only [smul_eq_mul, gaussianPDFReal_def, NNReal.coe_one, mul_one, sub_zero]
    ring_nf
    rw [mul_assoc]
    rw [← Real.exp_add]
  rw [hfun, integral_const_mul, integral_gaussian]

/-- Integrability companion to `integral_exp_sq_mul_standardGaussian`.

**Lean implementation helper.** -/
lemma integrable_exp_sq_mul_standardGaussian {a : Real} (ha : a < 1 / 2) :
    Integrable (fun x : Real => Real.exp (a * x ^ 2)) (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : NNReal) ≠ 0),
    integrable_withDensity_iff (measurable_gaussianPDF 0 1)
      (ae_of_all _ (fun _ => gaussianPDF_lt_top))]
  have hfun :
      (fun x : Real => Real.exp (a * x ^ 2) * (gaussianPDF 0 1 x).toReal) =
        fun x => (Real.sqrt (2 * Real.pi))⁻¹ *
          Real.exp (-(1 / 2 - a) * x ^ 2) := by
    funext x
    rw [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 1 x)]
    simp only [gaussianPDFReal_def, NNReal.coe_one, mul_one, sub_zero]
    ring_nf
    rw [mul_comm (Real.exp (a * x ^ 2))]
    rw [mul_assoc]
    rw [← Real.exp_add]
  rw [hfun]
  exact (integrable_exp_neg_mul_sq (sub_pos.mpr ha)).const_mul _

/-- The defining equality for the standard Gaussian ψ₂ norm:
`E exp(3 g² / 8) = 2`. A later module can combine this with strict monotonicity
in the scale parameter to obtain `psi2Norm g = sqrt (8/3)` without reversing
the chapter import graph.

**Lean implementation helper.** -/
theorem integral_exp_three_eighths_sq_standardGaussian :
    (∫ x, Real.exp ((3 / 8 : Real) * x ^ 2) ∂gaussianReal 0 1) = 2 := by
  rw [integral_exp_sq_mul_standardGaussian (by norm_num : (3 / 8 : Real) < 1 / 2)]
  refine (sq_eq_sq₀ (by positivity) (by norm_num)).1 ?_
  rw [mul_pow, inv_pow, Real.sq_sqrt (by positivity),
    Real.sq_sqrt (by positivity)]
  field_simp
  norm_num

/-- `ℝ≥0∞` form of the same identity, matching the ψ₂ functional's interface.

**Lean implementation helper.** -/
theorem lintegral_exp_three_eighths_sq_standardGaussian :
    (∫⁻ x, ENNReal.ofReal (Real.exp ((3 / 8 : Real) * x ^ 2))
      ∂gaussianReal 0 1) = 2 := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_exp_sq_mul_standardGaussian
      (by norm_num : (3 / 8 : Real) < 1 / 2))
    (ae_of_all _ (fun x => (Real.exp_pos _).le)),
    integral_exp_three_eighths_sq_standardGaussian]
  norm_num

/-! ## Exercise 2.22: exact Gaussian moments and Stirling correction -/


/-- The absolute moments of a centered Gaussian measure reduce to the standard Gamma-function integral.

**Lean implementation helper.** -/
lemma gaussian_absolute_moment_measure_raw {p : Real} (hp : -1 < p) :
    (∫ x, |x| ^ p ∂gaussianReal 0 1) =
      (1 / Real.sqrt (2 * Real.pi)) * 2 *
        ((1 / 2 : Real) ^ (-(p + 1) / 2) * (1 / 2) *
          Real.Gamma ((p + 1) / 2)) := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : NNReal) ≠ 0)]
  have hfun :
      (fun x : Real => gaussianPDFReal 0 1 x • |x| ^ p) =
        fun x => (1 / Real.sqrt (2 * Real.pi)) *
          (|x| ^ p * Real.exp (-(1 / 2 : Real) * |x| ^ (2 : Real))) := by
    funext x
    simp only [smul_eq_mul, gaussianPDFReal_def, NNReal.coe_one, mul_one, sub_zero]
    rw [show |x| ^ (2 : Real) = x ^ 2 by
      rw [Real.rpow_two, sq_abs]]
    ring_nf
  rw [hfun, integral_const_mul]
  rw [show (∫ a : Real, |a| ^ p * Real.exp (-(1 / 2 : Real) * |a| ^ (2 : Real))) =
      ∫ a : Real, (fun r : Real => r ^ p *
        Real.exp (-(1 / 2 : Real) * r ^ (2 : Real))) |a| by rfl]
  have habs := integral_comp_abs
    (f := fun r : Real => r ^ p * Real.exp (-(1 / 2 : Real) * r ^ (2 : Real)))
  rw [habs]
  rw [integral_rpow_mul_exp_neg_mul_rpow (by norm_num : (0 : Real) < 2) hp
    (by norm_num : (0 : Real) < 1 / 2)]
  ring

/-- A centered Gaussian with variance `σ²` has the stated closed formula for every positive absolute moment.

**Lean implementation helper.** -/
theorem gaussian_absolute_moment_measure {p : Real} (hp : 1 <= p) :
    (∫ x, |x| ^ p ∂gaussianReal 0 1) =
      2 ^ (p / 2) / Real.sqrt Real.pi * Real.Gamma ((p + 1) / 2) := by
  rw [gaussian_absolute_moment_measure_raw (by linarith)]
  have hcoef :
      (1 / Real.sqrt (2 * Real.pi)) * 2 *
          ((1 / 2 : Real) ^ (-(p + 1) / 2) * (1 / 2)) =
        2 ^ (p / 2) / Real.sqrt Real.pi := by
    rw [show -(p + 1) / 2 = -((p + 1) / 2) by ring,
      Real.rpow_neg_eq_inv_rpow]
    rw [show (1 / 2 : Real) = (2 : Real)⁻¹ by norm_num]
    rw [inv_inv]
    rw [show Real.sqrt (2 * Real.pi) = Real.sqrt 2 * Real.sqrt Real.pi by
      rw [Real.sqrt_mul (by norm_num : (0 : Real) ≤ 2)]]
    rw [show (p + 1) / 2 = p / 2 + 1 / 2 by ring,
      Real.rpow_add (by norm_num : (0 : Real) < 2)]
    rw [show (2 : Real) ^ (1 / 2 : Real) = Real.sqrt 2 by
      rw [← Real.sqrt_eq_rpow]]
    have hsqrt2 : Real.sqrt 2 ≠ 0 := by positivity
    have hsqrtpi : Real.sqrt Real.pi ≠ 0 := by positivity
    field_simp
  rw [show (1 / Real.sqrt (2 * Real.pi)) * 2 *
        ((1 / 2 : Real) ^ (-(p + 1) / 2) * (1 / 2) *
          Real.Gamma ((p + 1) / 2)) =
      ((1 / Real.sqrt (2 * Real.pi)) * 2 *
        ((1 / 2 : Real) ^ (-(p + 1) / 2) * (1 / 2))) *
          Real.Gamma ((p + 1) / 2) by ring,
    hcoef]

/-- Gaussian `L^p` norms grow like `sqrt(p)`.

**Book Equation (2.17).** -/
theorem gaussian_absolute_moment {g : Omega -> Real}
    (hg : HasLaw g (gaussianReal 0 1) mu) {p : Real} (hp : 1 <= p) :
    (∫ omega, |g omega| ^ p ∂mu) =
      2 ^ (p / 2) / Real.sqrt Real.pi * Real.Gamma ((p + 1) / 2) := by
  calc
    (∫ omega, |g omega| ^ p ∂mu) =
        ∫ x, |x| ^ p ∂gaussianReal 0 1 := by
      simpa only [Function.comp_apply] using hg.integral_comp
        (((Real.continuous_rpow_const (zero_le_one.trans hp)).comp continuous_abs)
          |>.aestronglyMeasurable)
    _ = _ := gaussian_absolute_moment_measure hp

/-- Proves the convergence statement for `gaussian_moment_stirling_correction`.

**Lean implementation helper.** -/
lemma tendsto_gaussian_moment_stirling_correction :
    Tendsto (fun p : Real =>
      Real.sqrt (Real.exp 1 * ((p - 1) / p)) *
        (1 + 1 / (p - 1)) ^ (-(p - 1) / 2))
      atTop (nhds 1) := by
  have hratio : Tendsto (fun p : Real => (p - 1) / p) atTop (nhds 1) := by
    have hinv : Tendsto (fun p : Real => 1 / p) atTop (nhds 0) :=
      by simpa [one_div] using tendsto_inv_atTop_zero
    have h := (tendsto_const_nhds (x := (1 : Real))).sub hinv
    have h' : Tendsto (fun p : Real => 1 - 1 / p) atTop (nhds 1) := by
      simpa only [sub_zero] using h
    apply h'.congr'
    filter_upwards [eventually_ne_atTop (0 : Real)] with p hp
    field_simp
  have hfirst : Tendsto (fun p : Real =>
      Real.sqrt (Real.exp 1 * ((p - 1) / p))) atTop
      (nhds (Real.sqrt (Real.exp 1))) := by
    apply (Real.continuous_sqrt.tendsto _).comp
    simpa only [mul_one] using
      ((tendsto_const_nhds (x := Real.exp 1)).mul hratio)
  have hy : Tendsto (fun p : Real => p - 1) atTop atTop :=
    by simpa [sub_eq_add_neg] using
      (tendsto_atTop_add_const_right atTop (-1 : Real) tendsto_id)
  have hpow := (Real.tendsto_one_add_div_rpow_exp 1).comp hy
  have hpow' : Tendsto (fun p : Real =>
      ((1 + 1 / (p - 1)) ^ (p - 1)) ^ (-(1 / 2 : Real))) atTop
      (nhds ((Real.exp 1) ^ (-(1 / 2 : Real)))) :=
    hpow.rpow_const (Or.inl (Real.exp_ne_zero 1))
  have hsecond : Tendsto (fun p : Real =>
      (1 + 1 / (p - 1)) ^ (-(p - 1) / 2)) atTop
      (nhds ((Real.exp 1) ^ (-(1 / 2 : Real)))) := by
    apply hpow'.congr'
    filter_upwards [eventually_gt_atTop (1 : Real)] with p hp
    have hb : 0 ≤ 1 + 1 / (p - 1) := by positivity
    rw [← Real.rpow_mul hb]
    congr 1
    ring
  have hlimit : Real.sqrt (Real.exp 1) *
      (Real.exp 1) ^ (-(1 / 2 : Real)) = 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add (Real.exp_pos 1)]
    norm_num
  simpa only [hlimit] using hfirst.mul hsecond


/-- The Gaussian absolute-moment formula can be rewritten in the Stirling-normalized form used for asymptotics.

**Lean implementation helper.** -/
lemma gaussian_moment_stirling_identity {p : Real} (hp : 1 < p) :
    (2 ^ (p / 2) / Real.sqrt Real.pi * Real.Gamma ((p + 1) / 2)) /
        ((p / Real.exp 1) ^ (p / 2)) =
      (Real.Gamma (((p - 1) / 2) + 1) /
          HDP.Chapter1.gammaStirlingMain ((p - 1) / 2)) *
        Real.sqrt 2 *
        (Real.sqrt (Real.exp 1 * ((p - 1) / p)) *
          (1 + 1 / (p - 1)) ^ (-(p - 1) / 2)) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hp1 : 0 < p - 1 := sub_pos.mpr hp
  have hx : 0 < (p - 1) / 2 := by positivity
  have hpi : 0 < Real.pi := Real.pi_pos
  have hcorrbase : 0 < 1 + 1 / (p - 1) := by positivity
  have hlogcorr : Real.log (1 + 1 / (p - 1)) =
      Real.log p - Real.log (p - 1) := by
    rw [show 1 + 1 / (p - 1) = p / (p - 1) by
      field_simp
      ring]
    rw [Real.log_div hp0.ne' hp1.ne']
  have hlogx : Real.log ((p - 1) / 2) =
      Real.log (p - 1) - Real.log 2 := by
    rw [Real.log_div hp1.ne' (by norm_num : (2 : Real) ≠ 0)]
  have hlogmainprod : Real.log (2 * Real.pi * ((p - 1) / 2)) =
      Real.log Real.pi + Real.log (p - 1) := by
    rw [show 2 * Real.pi * ((p - 1) / 2) = Real.pi * (p - 1) by ring]
    rw [Real.log_mul hpi.ne' hp1.ne']
  have hgamma : 0 < Real.Gamma (((p - 1) / 2) + 1) :=
    Real.Gamma_pos_of_pos (by linarith)
  have hmain : 0 < HDP.Chapter1.gammaStirlingMain ((p - 1) / 2) := by
    rw [HDP.Chapter1.gammaStirlingMain]
    positivity
  have hratioPos : 0 < Real.Gamma (((p - 1) / 2) + 1) /
      HDP.Chapter1.gammaStirlingMain ((p - 1) / 2) := div_pos hgamma hmain
  have hsqrt2 : 0 < Real.sqrt 2 := by positivity
  have hcorrSqrt : 0 < Real.sqrt (Real.exp 1 * ((p - 1) / p)) := by positivity
  have hcorrPow : 0 < (1 + 1 / (p - 1)) ^ (-(p - 1) / 2) :=
    Real.rpow_pos_of_pos hcorrbase _
  have hcorr : 0 < Real.sqrt (Real.exp 1 * ((p - 1) / p)) *
      (1 + 1 / (p - 1)) ^ (-(p - 1) / 2) := mul_pos hcorrSqrt hcorrPow
  apply Real.log_injOn_pos (Set.mem_Ioi.2 (by positivity)) (Set.mem_Ioi.2 (by
    apply mul_pos
    · apply mul_pos
      · apply div_pos
        · exact Real.Gamma_pos_of_pos (by linarith)
        · rw [HDP.Chapter1.gammaStirlingMain]
          positivity
      · positivity
    · apply mul_pos <;> positivity))
  rw [Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_div (by positivity) (by positivity),
    Real.log_rpow (by positivity),
    Real.log_mul (mul_pos hratioPos hsqrt2).ne' hcorr.ne',
    Real.log_mul hratioPos.ne' hsqrt2.ne',
    Real.log_div hgamma.ne' hmain.ne',
    Real.log_mul hcorrSqrt.ne' hcorrPow.ne']
  rw [show (p + 1) / 2 = (p - 1) / 2 + 1 by ring]
  rw [HDP.Chapter1.log_gammaStirlingMain hx]
  rw [Real.log_rpow (by positivity : 0 < p / Real.exp 1)]
  rw [Real.log_rpow hcorrbase]
  rw [hlogcorr]
  rw [Real.log_sqrt hpi.le]
  rw [Real.log_sqrt (by norm_num : (0 : Real) ≤ 2)]
  rw [Real.log_sqrt (by positivity : 0 ≤ Real.exp 1 * ((p - 1) / p))]
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_div hp0.ne' (Real.exp_ne_zero 1), Real.log_exp]
  rw [Real.log_div hp1.ne' hp0.ne']
  unfold HDP.Chapter1.gammaStirlingLog
  rw [hlogx, hlogmainprod]
  ring

/-- Proves the convergence statement for `gaussian_absolute_moment_formula_normalized`.

**Lean implementation helper.** -/
theorem tendsto_gaussian_absolute_moment_formula_normalized :
    Tendsto (fun p : Real =>
      (2 ^ (p / 2) / Real.sqrt Real.pi * Real.Gamma ((p + 1) / 2)) /
        ((p / Real.exp 1) ^ (p / 2))) atTop (nhds (Real.sqrt 2)) := by
  have hx : Tendsto (fun p : Real => (p - 1) / 2) atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop (2 * b + 1)] with p hp
    linarith
  have hgamma := HDP.Chapter1.gamma_stirling_ratio_tendsto_one.comp hx
  have h := (hgamma.mul (tendsto_const_nhds (x := Real.sqrt 2))).mul
    tendsto_gaussian_moment_stirling_correction
  have h' : Tendsto (fun p : Real =>
      (Real.Gamma (((p - 1) / 2) + 1) /
          HDP.Chapter1.gammaStirlingMain ((p - 1) / 2)) *
        Real.sqrt 2 *
        (Real.sqrt (Real.exp 1 * ((p - 1) / p)) *
          (1 + 1 / (p - 1)) ^ (-(p - 1) / 2)))
      atTop (nhds (Real.sqrt 2)) := by
    simpa using h
  apply h'.congr'
  filter_upwards [eventually_gt_atTop (1 : Real)] with p hp
  exact (gaussian_moment_stirling_identity hp).symm

/-- Proves the convergence statement for `gaussian_absolute_moment_measure_normalized`.

**Lean implementation helper.** -/
theorem tendsto_gaussian_absolute_moment_measure_normalized :
    Tendsto (fun p : Real =>
      (∫ x, |x| ^ p ∂gaussianReal 0 1) /
        ((p / Real.exp 1) ^ (p / 2))) atTop (nhds (Real.sqrt 2)) := by
  apply tendsto_gaussian_absolute_moment_formula_normalized.congr'
  filter_upwards [eventually_gt_atTop (1 : Real)] with p hp
  rw [gaussian_absolute_moment_measure hp.le]

/-- For `p > 1`, `gaussian_lpNorm_normalized_identity` rewrites the normalized Gaussian `Lᵖ` norm as `((∫ |x| ^ p dγ) / (p / e) ^ (p / 2)) ^ (1 / p)`.

**Lean implementation helper.** -/
lemma gaussian_lpNorm_normalized_identity {p : Real} (hp : 1 < p) :
    HDP.Chapter1.lpNormRV (fun x : Real => x) p (gaussianReal 0 1) /
        Real.sqrt (p / Real.exp 1) =
      ((∫ x, |x| ^ p ∂gaussianReal 0 1) /
        ((p / Real.exp 1) ^ (p / 2))) ^ (1 / p) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hA : 0 < p / Real.exp 1 := by positivity
  have hM : 0 < ∫ x, |x| ^ p ∂gaussianReal 0 1 := by
    rw [gaussian_absolute_moment_measure hp.le]
    positivity
  have hApow : 0 < (p / Real.exp 1) ^ (p / 2) :=
    Real.rpow_pos_of_pos hA _
  rw [HDP.Chapter1.lpNormRV]
  apply Real.log_injOn_pos (Set.mem_Ioi.2 (by positivity)) (Set.mem_Ioi.2 (by positivity))
  rw [Real.log_div (Real.rpow_pos_of_pos hM _).ne' (Real.sqrt_pos.mpr hA).ne',
    Real.log_rpow hM, Real.log_sqrt hA.le,
    Real.log_rpow (div_pos hM hApow),
    Real.log_div hM.ne' hApow.ne',
    Real.log_rpow hA]
  field_simp

/-- `‖g‖_{L^p} / √(p/e) → 1` for the standard Gaussian law.

**Book Exercise 2.22.** -/
theorem tendsto_gaussian_lpNorm_measure_normalized :
    Tendsto (fun p : Real =>
      HDP.Chapter1.lpNormRV (fun x : Real => x) p (gaussianReal 0 1) /
        Real.sqrt (p / Real.exp 1)) atTop (nhds 1) := by
  have hinv : Tendsto (fun p : Real => 1 / p) atTop (nhds 0) := by
    simpa [one_div] using tendsto_inv_atTop_zero
  have h := tendsto_gaussian_absolute_moment_measure_normalized.rpow hinv
    (Or.inl (by positivity : Real.sqrt 2 ≠ 0))
  have h' : Tendsto (fun p : Real =>
      ((∫ x, |x| ^ p ∂gaussianReal 0 1) /
        ((p / Real.exp 1) ^ (p / 2))) ^ (1 / p)) atTop (nhds 1) := by
    simpa using h
  apply h'.congr'
  filter_upwards [eventually_gt_atTop (1 : Real)] with p hp
  exact (gaussian_lpNorm_normalized_identity hp).symm

/-- Identifies the finite-dimensional ℓᵖ norm quantity `RV` with `of_hasLaw_standardGaussian`.

**Lean implementation helper.** -/
lemma lpNormRV_eq_of_hasLaw_standardGaussian {g : Omega → Real}
    (hg : HasLaw g (gaussianReal 0 1) mu) {p : Real} (hp : 1 ≤ p) :
    HDP.Chapter1.lpNormRV g p mu =
      HDP.Chapter1.lpNormRV (fun x : Real => x) p (gaussianReal 0 1) := by
  rw [HDP.Chapter1.lpNormRV, HDP.Chapter1.lpNormRV,
    gaussian_absolute_moment hg hp, gaussian_absolute_moment_measure hp]

/-- Every
standard Gaussian random variable satisfies `‖g‖_{L^p} = √(p/e)(1+o(1))`.

**Book Equation (2.17).** -/
theorem tendsto_gaussian_lpNorm_normalized {g : Omega → Real}
    (hg : HasLaw g (gaussianReal 0 1) mu) :
    Tendsto (fun p : Real =>
      HDP.Chapter1.lpNormRV g p mu / Real.sqrt (p / Real.exp 1))
      atTop (nhds 1) := by
  apply tendsto_gaussian_lpNorm_measure_normalized.congr'
  filter_upwards [eventually_gt_atTop (1 : Real)] with p hp
  rw [lpNormRV_eq_of_hasLaw_standardGaussian hg hp.le]

/-- The central binomial probability equals the displayed ratio of Stirling-normalized factorial terms.

**Lean implementation helper.** -/
lemma centralBinomial_stirlingSeq_identity (n : Nat) (hn : 0 < n) :
    ((n.centralBinom : Real) / (4 : Real) ^ n) *
        Real.sqrt (Real.pi * n) =
      Stirling.stirlingSeq (2 * n) / (Stirling.stirlingSeq n) ^ 2 *
        Real.sqrt Real.pi := by
  have hnR : (0 : Real) < n := by exact_mod_cast hn
  have hfact : (n.centralBinom : Real) * (n ! : Real) ^ 2 =
      ((2 * n) ! : Real) := by
    norm_cast
    rw [Nat.centralBinom_eq_two_mul_choose]
    have h := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
    simpa [show 2 * n - n = n by omega, pow_two, mul_assoc] using h
  have hnfac : (n ! : Real) ≠ 0 := by positivity
  have hcentral : (n.centralBinom : Real) =
      ((2 * n) ! : Real) / (n ! : Real) ^ 2 := by
    rw [eq_div_iff (pow_ne_zero 2 hnfac)]
    exact hfact
  rw [hcentral]
  unfold Stirling.stirlingSeq
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  field_simp
  have hsqrtPiN : Real.sqrt (Real.pi * (n : Real)) =
      Real.sqrt Real.pi * Real.sqrt n := by
    rw [Real.sqrt_mul Real.pi_nonneg]
  have hsqrtFourN : Real.sqrt ((n : Real) * 2 ^ 2) =
      Real.sqrt n * 2 := by
    rw [Real.sqrt_mul hnR.le, Real.sqrt_sq_eq_abs]
    norm_num
  have hsqrtTwoNSq : Real.sqrt ((n : Real) * 2) ^ 2 = (n : Real) * 2 := by
    rw [Real.sq_sqrt]
    positivity
  have hpow : ((n : Real) * 2 / Real.exp 1) ^ (2 * n) =
      (4 : Real) ^ n * (((n : Real) / Real.exp 1) ^ n) ^ 2 := by
    calc
      ((n : Real) * 2 / Real.exp 1) ^ (2 * n) =
          (2 * ((n : Real) / Real.exp 1)) ^ (2 * n) := by
            congr 2
            ring
      _ = (2 * ((n : Real) / Real.exp 1)) ^ (n * 2) := by
            rw [Nat.mul_comm]
      _ = ((2 * ((n : Real) / Real.exp 1)) ^ n) ^ 2 := by
            rw [pow_mul]
      _ = ((2 : Real) ^ n * ((n : Real) / Real.exp 1) ^ n) ^ 2 := by
            rw [mul_pow]
      _ = (4 : Real) ^ n * (((n : Real) / Real.exp 1) ^ n) ^ 2 := by
            rw [mul_pow, ← pow_mul, Nat.mul_comm n 2, pow_mul]
            norm_num
  rw [hsqrtPiN, hsqrtFourN, hsqrtTwoNSq, hpow]
  have hsqrtn : Real.sqrt (n : Real) * Real.sqrt n = n := by
    nlinarith [Real.sq_sqrt hnR.le]
  rw [show Real.sqrt Real.pi * Real.sqrt n * (Real.sqrt n * 2) =
      Real.sqrt Real.pi * (Real.sqrt n * Real.sqrt n) * 2 by ring, hsqrtn]
  ring

/-- `P(S_N=N/2)` is asymptotic to `sqrt(2/(pi N))`, showing the `N^-1/2` CLT-error scale is unavoidable.

**Book Chapter 2.** -/
theorem centralBinomialProbability_asymptotic :
    Tendsto (fun n : Nat =>
      ((n.centralBinom : Real) / (4 : Real) ^ n) *
        Real.sqrt (Real.pi * n)) atTop (nhds 1) := by
  have hs := Stirling.tendsto_stirlingSeq_sqrt_pi
  have hs2 := hs.comp (tendsto_id.const_mul_atTop' (by norm_num : (0 : Nat) < 2))
  have hlim := (hs2.div (hs.pow 2) (by positivity)).mul
    (tendsto_const_nhds (x := Real.sqrt Real.pi))
  have hlim' : Tendsto (fun n : Nat =>
      Stirling.stirlingSeq (2 * n) / (Stirling.stirlingSeq n) ^ 2 *
        Real.sqrt Real.pi) atTop (nhds 1) := by
    simp only [Function.comp_apply, id_eq, Pi.div_apply] at hlim
    convert hlim using 1
    field_simp
  apply hlim'.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (centralBinomial_stirlingSeq_identity n hn).symm

end HDP.Chapter2

end Source_01_GaussianTails

/-! ## Material formerly in `02_Hoeffding.lean` -/

section Source_02_Hoeffding

/-!
# Book Chapter 2, Section 2.2

Hoeffding's inequalities for Rademacher sums and bounded independent random
variables, including Exercises 2.5 and 2.8–2.10. The source is PDF pages 36–38
(printed 28–30).
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal unitInterval

namespace HDP.Chapter2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-! ## Exercise 2.5 = Book (2.7) -/

/-- "Completing the proof of Hoeffding inequality"):
`cosh x ≤ e^{x²/2}` for all real `x`. Explicit source exercise, load-bearing for the
proof of Theorem 2.2.1; Mathlib correspondence via `Real.cosh_le_exp_half_sq`
(the term-by-term Taylor comparison of the source hint).

**Book Equation (2.7).** -/
theorem exercise_2_5 (x : ℝ) : Real.cosh x ≤ Real.exp (x^2 / 2) :=
  Real.cosh_le_exp_half_sq x

/-! ## The MGF of a scaled Rademacher variable -/

/-- Unnumbered display in the proof of Theorem 2.2.1:
`𝔼 exp(λ aᵢXᵢ) = cosh(λaᵢ)` for a Rademacher `Xᵢ`. Implicit source claim.

**Book Equation (2.6).** -/
lemma mgf_rademacher_scaled {X : Ω → ℝ} (hX : HDP.IsRademacher X μ) (a t : ℝ) :
    mgf (fun ω => a * X ω) μ t = Real.cosh (t * a) := by
  have h1 : mgf (fun ω => a * X ω) μ t = ∫ ω, Real.exp ((t * a) * X ω) ∂μ := by
    rw [mgf]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by
      simp only [← mul_assoc])
  rw [h1, hX.integral_comp (fun x => Real.exp ((t * a) * x)), Real.cosh_eq]
  simp only [mul_one, mul_neg]

/-- A scaled Rademacher variable `aX` has sub-Gaussian MGF
with parameter `a²` — this is precisely the source's bound
`𝔼 exp(λaX) ≤ exp(λ²a²/2)` obtained from (2.7).

**Lean implementation helper.** -/
lemma hasSubgaussianMGF_rademacher_scaled {X : Ω → ℝ} (hX : HDP.IsRademacher X μ)
    (a : ℝ) :
    HasSubgaussianMGF (fun ω => a * X ω) (‖a‖₊^2) μ := by
  have := hX.isProbabilityMeasure
  refine ⟨fun t => ?_, fun t => ?_⟩
  · -- integrability of `exp(t·aX)`: `aX` is a.e. bounded
    exact hX.integrable_comp (fun x => Real.exp (t * (a * x)))
  · rw [mgf_rademacher_scaled hX a t]
    calc Real.cosh (t * a) ≤ Real.exp ((t * a)^2 / 2) := exercise_2_5 _
      _ = Real.exp ((‖a‖₊:ℝ)^2 * t^2 / 2) := by
          congr 1
          rw [coe_nnnorm, Real.norm_eq_abs, sq_abs]
          ring

/-! ## Book Theorem 2.2.1: Hoeffding's inequality for Rademacher sums -/

/-- For independent Rademacher `X₁, …, X_N`, a fixed
coefficient vector `a` and `t ≥ 0`:
`ℙ{∑ᵢ aᵢXᵢ ≥ t} ≤ exp(−t²/(2‖a‖₂²))`, with the source's exact constant.

The Lean proof is the source's exponential moment method: the Chernoff step (2.5) and
the MGF product rule (2.6) are Mathlib's `HasSubgaussianMGF` machinery, the per-term
bound is `hasSubgaussianMGF_rademacher_scaled` (via (2.7)), and the optimization of
`λ = t/‖a‖₂²` is `HasSubgaussianMGF.measure_ge_le`.

**Book Theorem 2.2.1.** -/
theorem hoeffding_rademacher [IsProbabilityMeasure μ] {N : ℕ} {X : Fin N → Ω → ℝ}
    (hX : ∀ i, HDP.IsRademacher (X i) μ) (hindep : iIndepFun X μ)
    (a : Fin N → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ ∑ i, a i * X i ω}
      ≤ Real.exp (-t^2 / (2 * ∑ i, (a i)^2)) := by
  have hYindep : iIndepFun (fun i ω => a i * X i ω) μ :=
    hindep.comp (fun i x => a i * x) (fun i => measurable_const_mul (a i))
  have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun (s := Finset.univ)
    hYindep (c := fun i => ‖a i‖₊^2)
    (fun i _ => hasSubgaussianMGF_rademacher_scaled (hX i) (a i)) ht
  have hcast : ((∑ i, ‖a i‖₊^2 : ℝ≥0) : ℝ) = ∑ i, (a i)^2 := by
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.norm_eq_abs, sq_abs]
  rw [hcast] at h
  exact h

/-- `ℙ{|∑ᵢaᵢXᵢ| ≥ t} ≤ 2exp(−t²/(2‖a‖₂²))`.
The Lean proof follows the source: split the two-sided tail and apply Theorem 2.2.1 to
the families `Xᵢ` and `−Xᵢ` (implemented as coefficients `aᵢ` and `−aᵢ`).

**Book Remark 2.2.2.** -/
theorem hoeffding_rademacher_two_sided [IsProbabilityMeasure μ] {N : ℕ}
    {X : Fin N → Ω → ℝ} (hX : ∀ i, HDP.IsRademacher (X i) μ)
    (hindep : iIndepFun X μ) (a : Fin N → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |∑ i, a i * X i ω|}
      ≤ 2 * Real.exp (-t^2 / (2 * ∑ i, (a i)^2)) := by
  have hsplit := HDP.real_tail_abs_le_add (μ := μ) (fun ω => ∑ i, a i * X i ω) t
  have h1 := hoeffding_rademacher hX hindep a ht
  have h2 := hoeffding_rademacher hX hindep (fun i => -(a i)) ht
  have hneg : ∀ ω, ∑ i, (-(a i)) * X i ω = -(∑ i, a i * X i ω) := by
    intro ω
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hsq : ∑ i, (-(a i))^2 = ∑ i, (a i)^2 :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [hsq] at h2
  simp only [hneg] at h2
  calc μ.real {ω | t ≤ |∑ i, a i * X i ω|}
      ≤ μ.real {ω | t ≤ ∑ i, a i * X i ω}
        + μ.real {ω | t ≤ -(∑ i, a i * X i ω)} := hsplit
    _ ≤ Real.exp (-t^2 / (2 * ∑ i, (a i)^2))
        + Real.exp (-t^2 / (2 * ∑ i, (a i)^2)) := add_le_add h1 h2
    _ = 2 * Real.exp (-t^2 / (2 * ∑ i, (a i)^2)) := by ring

/-! ## Book Remark 2.2.4: the probability of ¾N heads -/

/-- Remark 2.2.4 (implicit claim): if `X ∼ Ber(1/2)` then `2X − 1` is
Rademacher. Implicit source claim ("Note that if `Y ∼ Ber(1/2)`, then `2Y−1` is
Rademacher random variable").

**Book Remark 2.2.4.** -/
lemma bernoulli_to_rademacher {X : Ω → ℝ}
    (hX : HDP.IsBernoulli X ⟨1 / 2, by norm_num, by norm_num⟩ μ) :
    HDP.IsRademacher (fun ω => 2 * X ω - 1) μ := by
  refine ⟨(hX.aemeasurable.const_mul 2).sub_const 1, ?_⟩
  have h1 : (fun ω => 2 * X ω - 1) = (fun x => 2 * x - 1) ∘ X := rfl
  rw [h1, ← AEMeasurable.map_map_of_aemeasurable (by fun_prop) hX.aemeasurable,
    hX.map_eq, map_bernoulliMeasure' _ _ (by fun_prop)]
  norm_num

/-- Answering Question 2.1.1:
if `S_N` is the number of heads in `N` fair coin tosses (a sum of independent
`Ber(1/2)` variables), then `ℙ{S_N ≥ ¾N} ≤ exp(−N/8)`.

Explicit source declaration (remark with substantive computation); the Lean proof
follows the source: `2S_N − N` is a sum of independent Rademacher variables, and
Theorem 2.2.1 applies with `t = N/2`.

**Book Equation (2.4).** -/
theorem remark_2_2_4 [IsProbabilityMeasure μ] {N : ℕ} {X : Fin N → Ω → ℝ}
    (hX : ∀ i, HDP.IsBernoulli (X i) ⟨1 / 2, by norm_num, by norm_num⟩ μ)
    (hindep : iIndepFun X μ) :
    μ.real {ω | (3/4 : ℝ) * N ≤ ∑ i, X i ω} ≤ Real.exp (-(N:ℝ)/8) := by
  have hrad : ∀ i, HDP.IsRademacher (fun ω => 2 * X i ω - 1) μ :=
    fun i => bernoulli_to_rademacher (hX i)
  have hYindep : iIndepFun (fun i ω => 2 * X i ω - 1) μ :=
    hindep.comp (fun i x => 2 * x - 1)
      (fun i => (measurable_const_mul 2).sub_const 1)
  have h := hoeffding_rademacher (a := fun _ => (1:ℝ)) hrad hYindep
    (t := (N:ℝ)/2) (by positivity)
  have hset : {ω | ((N:ℝ)/2) ≤ ∑ i, (1:ℝ) * (2 * X i ω - 1)}
      = {ω | (3/4 : ℝ) * N ≤ ∑ i, X i ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, one_mul]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one]
    constructor
    · intro h'; linarith
    · intro h'; linarith
  rw [hset] at h
  refine h.trans (le_of_eq ?_)
  congr 1
  have hsum : ∑ _i : Fin N, ((1:ℝ))^2 = N := by simp
  rw [hsum]
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; norm_num
  · have hN0 : (N:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
    field_simp
    ring

/-! ## Exercise 2.8: an MGF comparison inequality -/

/-- Let `X` and `Y` have the same
mean, with `X ∈ [a,b]` a.s. and `Y ∈ {a,b}` a.s. Then `𝔼e^{λX} ≤ 𝔼e^{λY}` for all `λ`.

Explicit source exercise, load-bearing (used by the hints to Exercises 2.9 and 2.15).
Proof per the source hint: the chord of the convex function `e^{λ·}` over `[a,b]`
dominates it, with equality at the endpoints.

**Book Theorem 2.2.6.** -/
theorem exercise_2_8 [IsProbabilityMeasure μ] {X Y : Ω → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hXab : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) (hYab : ∀ᵐ ω ∂μ, Y ω = a ∨ Y ω = b)
    (hXint : Integrable X μ) (hYint : Integrable Y μ)
    (hmean : ∫ ω, X ω ∂μ = ∫ ω, Y ω ∂μ) (t : ℝ) :
    mgf X μ t ≤ mgf Y μ t := by
  rcases eq_or_lt_of_le hab with rfl | hab'
  · -- degenerate case `a = b`: both `X` and `Y` are a.s. equal to `a`
    have hXa : ∀ᵐ ω ∂μ, X ω = a := by
      filter_upwards [hXab] with ω h
      exact le_antisymm h.2 h.1
    have hYa : ∀ᵐ ω ∂μ, Y ω = a := by
      filter_upwards [hYab] with ω h
      rcases h with h | h <;> exact h
    have h1 : mgf X μ t = Real.exp (t * a) := by
      rw [mgf]
      rw [integral_congr_ae (g := fun _ => Real.exp (t * a))
        (by filter_upwards [hXa] with ω h; rw [h])]
      simp
    have h2 : mgf Y μ t = Real.exp (t * a) := by
      rw [mgf]
      rw [integral_congr_ae (g := fun _ => Real.exp (t * a))
        (by filter_upwards [hYa] with ω h; rw [h])]
      simp
    rw [h1, h2]
  -- main case `a < b`: chord bound
  · set L : ℝ → ℝ := fun x =>
      ((b - x) * Real.exp (t * a) + (x - a) * Real.exp (t * b)) / (b - a) with hL
    have hba : (0:ℝ) < b - a := by linarith
    -- chord bound: `e^{tx} ≤ L x` on `[a,b]`
    have hchord : ∀ x ∈ Set.Icc a b, Real.exp (t * x) ≤ L x := by
      intro x hx
      have hw1 : (0:ℝ) ≤ (b - x)/(b - a) := by
        apply div_nonneg _ hba.le
        linarith [hx.2]
      have hw2 : (0:ℝ) ≤ (x - a)/(b - a) := by
        apply div_nonneg _ hba.le
        linarith [hx.1]
      have hwsum : (b - x)/(b - a) + (x - a)/(b - a) = 1 := by
        field_simp
        ring
      have hcomb : ((b - x)/(b - a)) * a + ((x - a)/(b - a)) * b = x := by
        field_simp
        ring
      have hconv := convexOn_exp.2 (Set.mem_univ (t * a)) (Set.mem_univ (t * b))
        hw1 hw2 hwsum
      rw [smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul] at hconv
      calc Real.exp (t * x)
          = Real.exp ((b - x)/(b - a) * (t * a) + (x - a)/(b - a) * (t * b)) := by
            congr 1
            have : (b - x)/(b - a) * (t * a) + (x - a)/(b - a) * (t * b)
                = t * (((b - x)/(b - a)) * a + ((x - a)/(b - a)) * b) := by ring
            rw [this, hcomb]
        _ ≤ (b - x)/(b - a) * Real.exp (t * a) + (x - a)/(b - a) * Real.exp (t * b) :=
            hconv
        _ = L x := by
            rw [hL]
            field_simp
    -- equality at the endpoints
    have hend : ∀ x, x = a ∨ x = b → Real.exp (t * x) = L x := by
      intro x hx
      rcases hx with rfl | rfl <;>
        · rw [hL]
          field_simp
          ring
    -- integrate
    have hLX_int : Integrable (fun ω => L (X ω)) μ := by
      have : (fun ω => L (X ω)) = fun ω =>
          ((b - X ω) * Real.exp (t * a) + (X ω - a) * Real.exp (t * b)) / (b - a) :=
        rfl
      rw [this]
      apply Integrable.div_const
      exact (((integrable_const b).sub hXint).mul_const _).add
        ((hXint.sub (integrable_const a)).mul_const _)
    have hLY_int : Integrable (fun ω => L (Y ω)) μ := by
      have : (fun ω => L (Y ω)) = fun ω =>
          ((b - Y ω) * Real.exp (t * a) + (Y ω - a) * Real.exp (t * b)) / (b - a) :=
        rfl
      rw [this]
      apply Integrable.div_const
      exact (((integrable_const b).sub hYint).mul_const _).add
        ((hYint.sub (integrable_const a)).mul_const _)
    have hexpX_int : Integrable (fun ω => Real.exp (t * X ω)) μ := by
      refine (memLp_top_of_bound ?_ (Real.exp (|t| * (|a| + |b|))) ?_).integrable le_top
      · exact (measurable_exp.comp_aemeasurable
          (hXint.aemeasurable.const_mul t)).aestronglyMeasurable
      · filter_upwards [hXab] with ω h
        rw [Real.norm_eq_abs, Real.abs_exp, Real.exp_le_exp]
        have h1 : |X ω| ≤ |a| + |b| := by
          rcases abs_cases (X ω) with ⟨he, _⟩ | ⟨he, _⟩ <;>
            rcases abs_cases a with ⟨ha', _⟩ | ⟨ha', _⟩ <;>
            rcases abs_cases b with ⟨hb', _⟩ | ⟨hb', _⟩ <;>
            nlinarith [h.1, h.2]
        calc t * X ω ≤ |t * X ω| := le_abs_self _
          _ = |t| * |X ω| := abs_mul _ _
          _ ≤ |t| * (|a| + |b|) := by
              exact mul_le_mul_of_nonneg_left h1 (abs_nonneg t)
    -- 𝔼 L(X) = 𝔼 L(Y) since both are affine in the mean
    have hLmean : ∫ ω, L (X ω) ∂μ = ∫ ω, L (Y ω) ∂μ := by
      have hform : ∀ Z : Ω → ℝ, Integrable Z μ →
          ∫ ω, L (Z ω) ∂μ = ((b - ∫ ω, Z ω ∂μ) * Real.exp (t * a)
            + ((∫ ω, Z ω ∂μ) - a) * Real.exp (t * b)) / (b - a) := by
        intro Z hZ
        have : (fun ω => L (Z ω)) = fun ω =>
            ((b - Z ω) * Real.exp (t * a) + (Z ω - a) * Real.exp (t * b)) / (b - a) :=
          rfl
        rw [this]
        rw [integral_div]
        congr 1
        have hi1 : Integrable (fun ω => (b - Z ω) * Real.exp (t * a)) μ :=
          ((integrable_const b).sub hZ).mul_const _
        have hi2 : Integrable (fun ω => (Z ω - a) * Real.exp (t * b)) μ :=
          (hZ.sub (integrable_const a)).mul_const _
        rw [integral_add hi1 hi2, integral_mul_const,
          integral_mul_const, integral_sub (integrable_const b) hZ,
          integral_sub hZ (integrable_const a)]
        simp
      rw [hform X hXint, hform Y hYint, hmean]
    calc mgf X μ t = ∫ ω, Real.exp (t * X ω) ∂μ := rfl
      _ ≤ ∫ ω, L (X ω) ∂μ := by
          refine integral_mono_ae hexpX_int hLX_int ?_
          filter_upwards [hXab] with ω h
          exact hchord _ h
      _ = ∫ ω, L (Y ω) ∂μ := hLmean
      _ = ∫ ω, Real.exp (t * Y ω) ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards [hYab] with ω h
          exact (hend _ h).symm
      _ = mgf Y μ t := rfl

/-! ## Exercise 2.9: Hoeffding's lemma -/

/-- Any random variable `X` with values in
`[a,b]` satisfies `𝔼e^{λ(X−𝔼X)} ≤ exp(λ²(b−a)²/8)` for all `λ`.

Explicit source exercise, load-bearing (proof of Theorem 2.2.6 via Exercise 2.10);
Mathlib correspondence via `hasSubgaussianMGF_of_mem_Icc` (whose proof is the
cumulant-generating-function argument of the source hint).

**Book Theorem 2.2.6.** -/
theorem hoeffding_lemma [IsProbabilityMeasure μ] {X : Ω → ℝ} {a b : ℝ}
    (hm : AEMeasurable X μ) (hab : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) (t : ℝ) :
    mgf (fun ω => X ω - ∫ ω', X ω' ∂μ) μ t ≤ Real.exp (t^2 * (b - a)^2 / 8) := by
  have h := (hasSubgaussianMGF_of_mem_Icc hm hab).mgf_le t
  refine h.trans (le_of_eq ?_)
  congr 1
  push_cast [coe_nnnorm]
  rw [Real.norm_eq_abs, div_pow, sq_abs]
  ring

/-! ## Book Theorem 2.2.6 = Exercise 2.10: Hoeffding for bounded random variables -/

/-- For independent `Xᵢ ∈ [aᵢ, bᵢ]` and `t ≥ 0`:
`ℙ{∑(Xᵢ − 𝔼Xᵢ) ≥ t} ≤ exp(−2t²/∑(bᵢ−aᵢ)²)`, the source's exact constant.

**Book Theorem 2.2.6.** -/
theorem hoeffding_bounded [IsProbabilityMeasure μ] {N : ℕ} {X : Fin N → Ω → ℝ}
    {a b : Fin N → ℝ} (hm : ∀ i, AEMeasurable (X i) μ)
    (hab : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (a i) (b i))
    (hindep : iIndepFun X μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ ∑ i, (X i ω - ∫ ω', X i ω' ∂μ)}
      ≤ Real.exp (-2 * t^2 / ∑ i, (b i - a i)^2) := by
  have hYindep : iIndepFun (fun i ω => X i ω - ∫ ω', X i ω' ∂μ) μ :=
    hindep.comp (fun i x => x - ∫ ω', X i ω' ∂μ)
      (fun i => measurable_id.sub_const _)
  have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun (s := Finset.univ)
    hYindep (c := fun i => (‖b i - a i‖₊/2)^2)
    (fun i _ => hasSubgaussianMGF_of_mem_Icc (hm i) (hab i)) ht
  refine h.trans (le_of_eq ?_)
  congr 1
  have hcast : ((∑ i, (‖b i - a i‖₊/2)^2 : ℝ≥0) : ℝ) = (∑ i, (b i - a i)^2) / 4 := by
    push_cast [coe_nnnorm]
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.norm_eq_abs, div_pow, sq_abs]
    norm_num
  rw [hcast]
  rw [show (2 : ℝ) * ((∑ i, (b i - a i)^2) / 4) = (∑ i, (b i - a i)^2) / 2 by ring]
  rw [div_div_eq_mul_div]
  ring_nf

end HDP.Chapter2

end Source_02_Hoeffding

/-! ## Material formerly in `03_Chernoff.lean` -/

section Source_03_Chernoff

/-!
# Book Chapter 2, Section 2.3

Chernoff upper, lower, relative-entropy, and small-deviation bounds for sums of
independent Bernoulli variables. The source is PDF pages 38–40 (printed 30–32).
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal unitInterval

namespace HDP.Chapter2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

section ChernoffCore

variable {N : ℕ} {X : Fin N → Ω → ℝ} {p : Fin N → I}

/-- A sum of Bernoulli variables is a.e. bounded, hence
`exp(λ·S_N)` is integrable for every `λ`.

**Lean implementation helper.** -/
lemma integrable_exp_mul_bernoulli_sum [IsProbabilityMeasure μ]
    (hX : ∀ i, HDP.IsBernoulli (X i) (p i) μ)
    (lam : ℝ) : Integrable (fun ω => Real.exp (lam * ∑ i, X i ω)) μ := by
  refine (memLp_top_of_bound ?_ (Real.exp (|lam| * N)) ?_).integrable le_top
  · have hm : AEMeasurable (∑ i, X i) μ :=
      Finset.aemeasurable_sum Finset.univ (fun i _ => (hX i).aemeasurable)
    have hm' : AEMeasurable (fun ω => ∑ i, X i ω) μ := by
      have hs' : (∑ i, X i) = fun ω => ∑ i, X i ω := by
        funext ω
        rw [Finset.sum_apply]
      rwa [hs'] at hm
    exact (measurable_exp.comp_aemeasurable (hm'.const_mul lam)).aestronglyMeasurable
  · have hbd : ∀ᵐ ω ∂μ, ∀ i, X i ω = 1 ∨ X i ω = 0 :=
      (MeasureTheory.ae_all_iff).mpr fun i => (hX i).ae_mem
    filter_upwards [hbd] with ω hω
    rw [Real.norm_eq_abs, Real.abs_exp, Real.exp_le_exp]
    have h1 : ∀ i, |X i ω| ≤ 1 := by
      intro i
      rcases hω i with h | h <;> rw [h] <;> norm_num
    calc lam * ∑ i, X i ω ≤ |lam * ∑ i, X i ω| := le_abs_self _
      _ = |lam| * |∑ i, X i ω| := abs_mul _ _
      _ ≤ |lam| * N := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg lam)
          calc |∑ i, X i ω| ≤ ∑ i, |X i ω| := Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ _i : Fin N, (1:ℝ) := Finset.sum_le_sum fun i _ => h1 i
            _ = N := by simp

/-- Unnumbered display in the proof of Theorem 2.3.1:
`∏ᵢ 𝔼exp(λXᵢ) ≤ exp((e^λ−1)μ₀)` where `μ₀ = ∑pᵢ` (using `1 + x ≤ e^x` per factor).
Implicit source claim.

**Book Equation (2.9).** -/
lemma mgf_bernoulli_sum_le [_inst : IsProbabilityMeasure μ]
    (hX : ∀ i, HDP.IsBernoulli (X i) (p i) μ)
    (hindep : iIndepFun X μ) (lam : ℝ) :
    mgf (fun ω => ∑ i, X i ω) μ lam
      ≤ Real.exp ((Real.exp lam - 1) * ∑ i, (p i : ℝ)) := by
  have hsum : (fun ω => ∑ i, X i ω) = ∑ i, X i := by
    funext ω
    rw [Finset.sum_apply]
  rw [hsum, iIndepFun.mgf_sum₀ hindep (fun i => (hX i).aemeasurable) Finset.univ]
  have hfac : ∀ i, mgf (X i) μ lam ≤ Real.exp ((Real.exp lam - 1) * (p i : ℝ)) := by
    intro i
    rw [(hX i).mgf_eq]
    have := Real.add_one_le_exp ((Real.exp lam - 1) * (p i : ℝ))
    linarith
  calc ∏ i, mgf (X i) μ lam
      ≤ ∏ i, Real.exp ((Real.exp lam - 1) * (p i : ℝ)) :=
        Finset.prod_le_prod (fun i _ => mgf_nonneg) (fun i _ => hfac i)
    _ = Real.exp ((Real.exp lam - 1) * ∑ i, (p i : ℝ)) := by
        rw [← Real.exp_sum, ← Finset.mul_sum]

variable [IsProbabilityMeasure μ]

/-- Let `Xᵢ` be independent `Ber(pᵢ)` and
`S_N = ∑Xᵢ` with mean `μ₀ = ∑pᵢ`. Then, for `t ≥ μ₀` (with `t, μ₀ > 0`, which the
source uses implicitly through `λ = ln(t/μ₀)`),
`ℙ{S_N ≥ t} ≤ e^{−μ₀}(eμ₀/t)^t`.

The Lean proof is the source's: exponential moment method with `λ = ln(t/μ₀)` and the
per-factor bound `1 + x ≤ e^x`.

**Book Theorem 2.3.1.** -/
theorem chernoff_upper (hX : ∀ i, HDP.IsBernoulli (X i) (p i) μ)
    (hindep : iIndepFun X μ) {t : ℝ} (hμ0 : 0 < ∑ i, (p i : ℝ))
    (ht : ∑ i, (p i : ℝ) ≤ t) :
    μ.real {ω | t ≤ ∑ i, X i ω}
      ≤ Real.exp (-∑ i, (p i : ℝ))
        * (Real.exp 1 * (∑ i, (p i : ℝ)) / t) ^ t := by
  set μ₀ := ∑ i, (p i : ℝ) with hμ₀
  have ht0 : 0 < t := lt_of_lt_of_le hμ0 ht
  set lam := Real.log (t / μ₀) with hlam
  have hlam0 : 0 ≤ lam := Real.log_nonneg (by
    rw [le_div_iff₀ hμ0]
    linarith)
  have hexp_lam : Real.exp lam = t / μ₀ := Real.exp_log (by positivity)
  have h1 := measure_ge_le_exp_mul_mgf (μ := μ) (X := fun ω => ∑ i, X i ω) t hlam0
    (integrable_exp_mul_bernoulli_sum hX lam)
  have h2 := mgf_bernoulli_sum_le hX hindep lam
  calc μ.real {ω | t ≤ ∑ i, X i ω}
      ≤ Real.exp (-lam * t) * mgf (fun ω => ∑ i, X i ω) μ lam := h1
    _ ≤ Real.exp (-lam * t) * Real.exp ((Real.exp lam - 1) * μ₀) := by
        exact mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = Real.exp (-lam * t + (Real.exp lam - 1) * μ₀) := by rw [← Real.exp_add]
    _ = Real.exp (-μ₀) * (Real.exp 1 * μ₀ / t) ^ t := by
        rw [hexp_lam]
        have hbase : (0:ℝ) < Real.exp 1 * μ₀ / t := by positivity
        rw [Real.rpow_def_of_pos hbase, ← Real.exp_add]
        congr 1
        have hlog1 : Real.log (Real.exp 1 * μ₀ / t)
            = 1 + Real.log μ₀ - Real.log t := by
          rw [Real.log_div (by positivity) ht0.ne', Real.log_mul
            (Real.exp_ne_zero 1) hμ0.ne', Real.log_exp]
        have hlog2 : lam = Real.log t - Real.log μ₀ :=
          Real.log_div ht0.ne' hμ0.ne'
        have hexpand : (t/μ₀ - 1) * μ₀ = t - μ₀ := by
          field_simp
        rw [hexpand, hlog1, hlog2]
        ring

/-- For `0 < t ≤ μ₀`: `ℙ{S_N ≤ t} ≤ e^{−μ₀}(eμ₀/t)^t`.

**Book Remark 2.3.2.** -/
theorem chernoff_lower (hX : ∀ i, HDP.IsBernoulli (X i) (p i) μ)
    (hindep : iIndepFun X μ) {t : ℝ} (ht0 : 0 < t) (ht : t ≤ ∑ i, (p i : ℝ)) :
    μ.real {ω | ∑ i, X i ω ≤ t}
      ≤ Real.exp (-∑ i, (p i : ℝ))
        * (Real.exp 1 * (∑ i, (p i : ℝ)) / t) ^ t := by
  set μ₀ := ∑ i, (p i : ℝ) with hμ₀
  have hμ0 : 0 < μ₀ := lt_of_lt_of_le ht0 ht
  set lam := Real.log (t / μ₀) with hlam
  have hlam0 : lam ≤ 0 := by
    apply Real.log_nonpos (by positivity)
    rw [div_le_one hμ0]
    exact ht
  have hexp_lam : Real.exp lam = t / μ₀ := Real.exp_log (by positivity)
  have h1 := measure_le_le_exp_mul_mgf (μ := μ) (X := fun ω => ∑ i, X i ω) t hlam0
    (integrable_exp_mul_bernoulli_sum hX lam)
  have h2 := mgf_bernoulli_sum_le hX hindep lam
  calc μ.real {ω | ∑ i, X i ω ≤ t}
      ≤ Real.exp (-lam * t) * mgf (fun ω => ∑ i, X i ω) μ lam := h1
    _ ≤ Real.exp (-lam * t) * Real.exp ((Real.exp lam - 1) * μ₀) := by
        exact mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = Real.exp (-lam * t + (Real.exp lam - 1) * μ₀) := by rw [← Real.exp_add]
    _ = Real.exp (-μ₀) * (Real.exp 1 * μ₀ / t) ^ t := by
        rw [hexp_lam]
        have hbase : (0:ℝ) < Real.exp 1 * μ₀ / t := by positivity
        rw [Real.rpow_def_of_pos hbase, ← Real.exp_add]
        congr 1
        have hlog1 : Real.log (Real.exp 1 * μ₀ / t)
            = 1 + Real.log μ₀ - Real.log t := by
          rw [Real.log_div (by positivity) ht0.ne', Real.log_mul
            (Real.exp_ne_zero 1) hμ0.ne', Real.log_exp]
        have hlog2 : lam = Real.log t - Real.log μ₀ :=
          Real.log_div ht0.ne' hμ0.ne'
        have hexpand : (t/μ₀ - 1) * μ₀ = t - μ₀ := by
          field_simp
        rw [hexpand, hlog1, hlog2]
        ring

end ChernoffCore

/-! ## The Taylor bound for the relative entropy -/

/-- Intermediate claim in the proof of Corollary 2.3.4
("To check the last bound, subtract `δ²/3` from both sides..."):
`(1+δ)ln(1+δ) − δ ≥ δ²/3` for `0 ≤ δ ≤ 1`. Implicit source claim.

The Lean proof uses concavity of `log` (chord bound `ln(1+δ) ≥ δ ln 2` on `[0,1]`)
and a derivative computation; this is mathematically equivalent to the source's
alternating-series argument.

**Book Corollary 2.3.4.** -/
lemma entropy_ge_sq_third {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) :
    δ^2 / 3 ≤ (1 + δ) * Real.log (1 + δ) - δ := by
  -- chord bound: `ln(1+s) ≥ s·ln 2` on `[0,1]`
  have hchord : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → s * Real.log 2 ≤ Real.log (1 + s) := by
    intro s hs0 hs1
    have hcc := (strictConcaveOn_log_Ioi.concaveOn).2 (Set.mem_Ioi.mpr one_pos)
      (Set.mem_Ioi.mpr two_pos) (by linarith : (0:ℝ) ≤ 1 - s) hs0 (by ring)
    simp only [smul_eq_mul] at hcc
    calc s * Real.log 2 = (1 - s) * Real.log 1 + s * Real.log 2 := by
          rw [Real.log_one]; ring
      _ ≤ Real.log ((1 - s) * 1 + s * 2) := hcc
      _ = Real.log (1 + s) := by ring_nf
  -- define `g(s) = (1+s)ln(1+s) − s − s²/3` and show `g' ≥ 0` on `[0,1]`
  set g : ℝ → ℝ := fun s => (1 + s) * Real.log (1 + s) - s - s^2/3 with hg
  have hderiv : ∀ s : ℝ, 0 < 1 + s →
      HasDerivAt g (Real.log (1 + s) - 2 * s / 3) s := by
    intro s hs
    have h1' : HasDerivAt (fun x : ℝ => 1 + x) 1 s :=
      (hasDerivAt_id s).const_add (1:ℝ)
    have h2' : HasDerivAt (fun x : ℝ => Real.log (1 + x)) ((1 + s)⁻¹ * 1) s :=
      (Real.hasDerivAt_log hs.ne').comp s h1'
    have h3' : HasDerivAt (fun x : ℝ => (1 + x) * Real.log (1 + x))
        (1 * Real.log (1 + s) + (1 + s) * ((1 + s)⁻¹ * 1)) s := h1'.mul h2'
    have h4' : HasDerivAt (fun x : ℝ => x^2/3) (2 * s / 3) s := by
      have := (hasDerivAt_pow 2 s).div_const 3
      simpa [pow_one] using this
    have h5' : HasDerivAt g
        (1 * Real.log (1 + s) + (1 + s) * ((1 + s)⁻¹ * 1) - 1 - 2 * s / 3) s :=
      (h3'.sub (hasDerivAt_id s)).sub h4'
    have heq : 1 * Real.log (1 + s) + (1 + s) * ((1 + s)⁻¹ * 1) - 1 - 2 * s / 3
        = Real.log (1 + s) - 2 * s / 3 := by
      field_simp
      ring
    rw [heq] at h5'
    exact h5'
  have hmono : MonotoneOn g (Set.Icc (0:ℝ) 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1) ?_ ?_ ?_
    · intro s hs
      exact ((hderiv s (by rcases hs with ⟨h, _⟩; linarith)).continuousAt).continuousWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      exact (hderiv s (by rcases hs with ⟨h, _⟩; linarith)).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      obtain ⟨hs0, hs1⟩ := hs
      rw [(hderiv s (by linarith)).deriv]
      have hc := hchord s hs0.le hs1.le
      have hlog2 : (2:ℝ)/3 ≤ Real.log 2 := by
        have := Real.log_two_gt_d9
        linarith
      nlinarith
  have h00 : g 0 = 0 := by simp [hg]
  have := hmono (Set.mem_Icc.mpr ⟨le_refl 0, zero_le_one⟩) (Set.mem_Icc.mpr ⟨h0, h1⟩) h0
  rw [h00] at this
  simp only [hg] at this
  linarith

/-- Intermediate claim for the left small-deviation tail (the source's
"Try it! You should get even a better bound: `exp(−δ²μ/2)`"):
`(1−δ)ln(1−δ) + δ ≥ δ²/2` for `0 ≤ δ < 1`. Implicit source claim.

**Book Section 2.3.** -/
lemma entropy_lower_ge_sq_half {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ < 1) :
    δ^2 / 2 ≤ (1 - δ) * Real.log (1 - δ) + δ := by
  -- with `u = 1 − δ ∈ (0,1]`: `φ(u) = u ln u + 1 − u − (1−u)²/2` is antitone with
  -- `φ(1) = 0`, since `φ'(u) = ln u + 1 − u ≤ 0`.
  set φ : ℝ → ℝ := fun u => u * Real.log u + 1 - u - (1-u)^2/2 with hφ
  have hderiv : ∀ u : ℝ, 0 < u → HasDerivAt φ (Real.log u + 1 - u) u := by
    intro u hu
    have h1' : HasDerivAt (fun x : ℝ => x * Real.log x)
        (1 * Real.log u + u * u⁻¹) u :=
      (hasDerivAt_id u).mul (Real.hasDerivAt_log hu.ne')
    have h2' : HasDerivAt (fun x : ℝ => (1-x)^2/2) ((2 * (1 - u) ^ 1 * (-1))/2) u := by
      have hinner : HasDerivAt (fun x : ℝ => 1 - x) (-1) u :=
        (hasDerivAt_id u).const_sub (1:ℝ)
      exact ((hasDerivAt_pow 2 (1 - u)).comp u hinner).div_const 2
    have h3' : HasDerivAt φ
        (1 * Real.log u + u * u⁻¹ - 1 - (2 * (1 - u) ^ 1 * (-1))/2) u :=
      ((h1'.add_const 1).sub (hasDerivAt_id u)).sub h2'
    have heq : 1 * Real.log u + u * u⁻¹ - 1 - (2 * (1 - u) ^ 1 * (-1))/2
        = Real.log u + 1 - u := by
      rw [mul_inv_cancel₀ hu.ne']
      ring
    rw [heq] at h3'
    exact h3'
  have hu0 : 0 < 1 - δ := by linarith
  have hanti : AntitoneOn φ (Set.Icc (1-δ) 1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) ?_ ?_ ?_
    · intro u hu
      exact ((hderiv u (lt_of_lt_of_le hu0 hu.1)).continuousAt).continuousWithinAt
    · intro u hu
      rw [interior_Icc] at hu
      exact (hderiv u (lt_trans hu0 hu.1)).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [interior_Icc] at hu
      rw [(hderiv u (lt_trans hu0 hu.1)).deriv]
      have := Real.log_le_sub_one_of_pos (lt_trans hu0 hu.1)
      linarith
  have hφ1 : φ 1 = 0 := by simp [hφ]
  have h := hanti (Set.mem_Icc.mpr ⟨le_refl _, by linarith⟩)
    (Set.mem_Icc.mpr ⟨by linarith, le_refl 1⟩) (by linarith)
  rw [hφ1] at h
  simp only [hφ] at h
  nlinarith [h]

/-- The value of the Chernoff bound at `t = cμ₀` in
exponential form, `e^{−μ₀}(eμ₀/(cμ₀))^{cμ₀} = exp(−μ₀(c ln c − c + 1))`.

**Lean implementation helper.** -/
lemma chernoff_bound_exp_form {μ₀ c : ℝ} (hμ0 : 0 < μ₀) (hc : 0 < c) :
    Real.exp (-μ₀) * (Real.exp 1 * μ₀ / (c * μ₀)) ^ (c * μ₀)
      = Real.exp (-μ₀ * (c * Real.log c - c + 1)) := by
  have hbase : Real.exp 1 * μ₀ / (c * μ₀) = Real.exp 1 / c := by
    field_simp
  rw [hbase, Real.rpow_def_of_pos (by positivity), ← Real.exp_add]
  congr 1
  rw [Real.log_div (Real.exp_ne_zero 1) hc.ne', Real.log_exp]
  ring

section SmallDeviations

variable [IsProbabilityMeasure μ] {N : ℕ} {X : Fin N → Ω → ℝ} {p : Fin N → I}

/-- `ℙ{S_N ≥ (1+δ)μ₀} ≤ exp(−μ₀((1+δ)ln(1+δ) − δ))` for `δ ≥ 0`.
Explicit displayed source claim (obtained from Theorem 2.3.1 with `t = (1+δ)μ₀`).

**Book Equation (2.10).** -/
theorem chernoff_relative_entropy_bound (hX : ∀ i, HDP.IsBernoulli (X i) (p i) μ)
    (hindep : iIndepFun X μ) {δ : ℝ} (hδ : 0 ≤ δ) (hμ0 : 0 < ∑ i, (p i : ℝ)) :
    μ.real {ω | (1 + δ) * ∑ i, (p i : ℝ) ≤ ∑ i, X i ω}
      ≤ Real.exp (-(∑ i, (p i : ℝ)) * ((1 + δ) * Real.log (1 + δ) - δ)) := by
  set μ₀ := ∑ i, (p i : ℝ)
  have h := chernoff_upper hX hindep (t := (1 + δ) * μ₀) hμ0 (by nlinarith)
  refine h.trans (le_of_eq ?_)
  rw [chernoff_bound_exp_form hμ0 (by linarith : (0:ℝ) < 1 + δ)]
  congr 1
  ring

/-- In the setting of Theorem 2.3.1, for `0 ≤ δ ≤ 1`:
`ℙ{|S_N − μ₀| ≥ δμ₀} ≤ 2exp(−δ²μ₀/3)`.

The Lean proof follows the source: the right tail via (2.10) and the Taylor bound
`entropy_ge_sq_third`; the left tail via Exercise 2.11 and `entropy_lower_ge_sq_half`
(the source's "even a better bound `exp(−δ²μ/2)`"), with the boundary case `δ = 1`
handled by the exponential moment method at `λ = 1`; then a union bound.

**Book Corollary 2.3.4.** -/
theorem chernoff_small_deviations (hX : ∀ i, HDP.IsBernoulli (X i) (p i) μ)
    (hindep : iIndepFun X μ) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    μ.real {ω | δ * ∑ i, (p i : ℝ) ≤ |∑ i, X i ω - ∑ i, (p i : ℝ)|}
      ≤ 2 * Real.exp (-δ^2 * (∑ i, (p i : ℝ)) / 3) := by
  set μ₀ := ∑ i, (p i : ℝ) with hμ₀def
  have hμ0nn : 0 ≤ μ₀ := Finset.sum_nonneg fun i _ => (p i).2.1
  rcases eq_or_lt_of_le hμ0nn with hμ0 | hμ0
  · -- degenerate case `μ₀ = 0`: the bound is `≥ 2 ≥ 1 ≥` any probability
    rw [← hμ0]
    calc μ.real _ ≤ 1 := measureReal_le_one
      _ ≤ 2 * Real.exp (-δ^2 * 0 / 3) := by norm_num
  -- main case `μ₀ > 0`
  have hsplit := HDP.real_tail_abs_le_add (μ := μ)
    (fun ω => ∑ i, X i ω - μ₀) (δ * μ₀)
  -- right tail
  have hright : μ.real {ω | δ * μ₀ ≤ ∑ i, X i ω - μ₀}
      ≤ Real.exp (-δ^2 * μ₀ / 3) := by
    have hset : {ω | δ * μ₀ ≤ ∑ i, X i ω - μ₀}
        = {ω | (1 + δ) * μ₀ ≤ ∑ i, X i ω} := by
      ext ω
      simp only [Set.mem_setOf_eq]
      constructor <;> intro h <;> nlinarith
    rw [hset]
    refine (chernoff_relative_entropy_bound hX hindep hδ0 hμ0).trans ?_
    rw [Real.exp_le_exp]
    have := entropy_ge_sq_third hδ0 hδ1
    nlinarith
  -- left tail
  have hleft : μ.real {ω | δ * μ₀ ≤ -(∑ i, X i ω - μ₀)}
      ≤ Real.exp (-δ^2 * μ₀ / 3) := by
    have hset : {ω | δ * μ₀ ≤ -(∑ i, X i ω - μ₀)}
        = {ω | ∑ i, X i ω ≤ (1 - δ) * μ₀} := by
      ext ω
      simp only [Set.mem_setOf_eq]
      constructor <;> intro h <;> nlinarith
    rw [hset]
    rcases eq_or_lt_of_le hδ1 with rfl | hδlt
    · -- boundary case `δ = 1`: exponential moment method at `λ = −1`
      have h1 := measure_le_le_exp_mul_mgf (μ := μ) (X := fun ω => ∑ i, X i ω)
        ((1 - 1) * μ₀) (le_of_lt (by norm_num : (-1:ℝ) < 0))
        (integrable_exp_mul_bernoulli_sum hX (-1))
      have h2 := mgf_bernoulli_sum_le hX hindep (-1)
      calc μ.real {ω | ∑ i, X i ω ≤ (1 - 1) * μ₀}
          ≤ Real.exp (-(-1) * ((1-1) * μ₀))
            * mgf (fun ω => ∑ i, X i ω) μ (-1) := h1
        _ = mgf (fun ω => ∑ i, X i ω) μ (-1) := by norm_num
        _ ≤ Real.exp ((Real.exp (-1) - 1) * μ₀) := h2
        _ ≤ Real.exp (-1^2 * μ₀ / 3) := by
            rw [Real.exp_le_exp]
            have hE : Real.exp (-1) ≤ 2/3 := by
              rw [Real.exp_neg]
              rw [inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
              have := Real.exp_one_gt_d9
              linarith
            nlinarith
    · -- `δ < 1`: Exercise 2.11 with `t = (1−δ)μ₀` and the `δ²/2` entropy bound
      have hone : (0:ℝ) < 1 - δ := by linarith
      have h := chernoff_lower hX hindep (t := (1 - δ) * μ₀) (by positivity)
        (by nlinarith)
      refine h.trans ?_
      rw [chernoff_bound_exp_form hμ0 hone]
      rw [Real.exp_le_exp]
      have := entropy_lower_ge_sq_half hδ0 hδlt
      nlinarith
  calc μ.real {ω | δ * μ₀ ≤ |∑ i, X i ω - μ₀|}
      ≤ μ.real {ω | δ * μ₀ ≤ ∑ i, X i ω - μ₀}
        + μ.real {ω | δ * μ₀ ≤ -(∑ i, X i ω - μ₀)} := hsplit
    _ ≤ Real.exp (-δ^2 * μ₀ / 3) + Real.exp (-δ^2 * μ₀ / 3) :=
        add_le_add hright hleft
    _ = 2 * Real.exp (-δ^2 * μ₀ / 3) := by ring

/-- Unnumbered display after Corollary 2.3.4 ("If we set
`Z_N = (S_N − μ)/√μ`..."): `ℙ{|Z_N| ≥ t} ≤ 2exp(−t²/3)` for `0 ≤ t ≤ √μ₀`.
Explicit unnumbered source claim.

**Book Remark 2.3.5.** -/
theorem chernoff_normalized (hX : ∀ i, HDP.IsBernoulli (X i) (p i) μ)
    (hindep : iIndepFun X μ) {t : ℝ} (ht0 : 0 ≤ t)
    (hμ0 : 0 < ∑ i, (p i : ℝ)) (ht : t ≤ Real.sqrt (∑ i, (p i : ℝ))) :
    μ.real {ω | t ≤ |(∑ i, X i ω - ∑ i, (p i : ℝ)) / Real.sqrt (∑ i, (p i : ℝ))|}
      ≤ 2 * Real.exp (-t^2 / 3) := by
  set μ₀ := ∑ i, (p i : ℝ) with hμ₀def
  have hsq : 0 < Real.sqrt μ₀ := Real.sqrt_pos.mpr hμ0
  set δ := t / Real.sqrt μ₀ with hδdef
  have hδ0 : 0 ≤ δ := by positivity
  have hδ1 : δ ≤ 1 := by
    rw [hδdef, div_le_one hsq]
    exact ht
  have hthr : δ * μ₀ = t * Real.sqrt μ₀ := by
    rw [hδdef]
    calc t / Real.sqrt μ₀ * μ₀ = t * (μ₀ / Real.sqrt μ₀) := by ring
      _ = t * Real.sqrt μ₀ := by rw [Real.div_sqrt]
  have hset : {ω | t ≤ |(∑ i, X i ω - μ₀) / Real.sqrt μ₀|}
      = {ω | δ * μ₀ ≤ |∑ i, X i ω - μ₀|} := by
    ext ω
    simp only [Set.mem_setOf_eq, abs_div, abs_of_pos hsq]
    rw [le_div_iff₀ hsq, hthr]
  rw [hset]
  refine (chernoff_small_deviations hX hindep hδ0 hδ1).trans (le_of_eq ?_)
  have harg : -δ^2 * (∑ i, (p i : ℝ)) / 3 = -t^2/3 := by
    rw [hδdef, div_pow, Real.sq_sqrt hμ0.le, ← hμ₀def]
    field_simp
  rw [harg]

end SmallDeviations

end HDP.Chapter2

end Source_03_Chernoff

/-! ## Material formerly in `04_MedianOfMeans.lean` -/

section Source_04_MedianOfMeans

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal unitInterval
namespace HDP.Chapter2
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Median-of-means achieves a Gaussian tail assuming only finite variance.

**Book Theorem 2.4.1.** -/
theorem majority_of_rare_events [IsProbabilityMeasure μ] {B : ℕ}
    {Z : Fin B → Ω → ℝ}
    (hm : ∀ i, AEMeasurable (Z i) μ)
    (h01 : ∀ i, ∀ᵐ ω ∂μ, Z i ω ∈ Set.Icc (0 : ℝ) 1)
    (hindep : iIndepFun Z μ)
    (hmean : ∀ i, ∫ ω, Z i ω ∂μ ≤ 1 / 4) :
    μ.real {ω | (B : ℝ) / 2 ≤ ∑ i, Z i ω} ≤ Real.exp (-(B : ℝ) / 8) := by
  rcases Nat.eq_zero_or_pos B with rfl | hB
  · simp
  have hcenter := hoeffding_bounded (μ := μ) (X := Z)
    (a := fun _ ↦ (0 : ℝ)) (b := fun _ ↦ (1 : ℝ)) hm h01 hindep
    (t := (B : ℝ) / 4) (by positivity)
  have hsubset : {ω | (B : ℝ) / 2 ≤ ∑ i, Z i ω} ⊆
      {ω | (B : ℝ) / 4 ≤ ∑ i, (Z i ω - ∫ ω', Z i ω' ∂μ)} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    rw [Finset.sum_sub_distrib]
    have hm_sum : ∑ i, (∫ ω', Z i ω' ∂μ) ≤ (B : ℝ) / 4 := by
      calc
        ∑ i, (∫ ω', Z i ω' ∂μ) ≤ ∑ _i : Fin B, (1 / 4 : ℝ) :=
          Finset.sum_le_sum fun i _ ↦ hmean i
        _ = (B : ℝ) / 4 := by simp; ring
    linarith
  calc
    μ.real {ω | (B : ℝ) / 2 ≤ ∑ i, Z i ω}
        ≤ μ.real {ω | (B : ℝ) / 4 ≤
          ∑ i, (Z i ω - ∫ ω', Z i ω' ∂μ)} := by
            exact measureReal_mono hsubset (measure_ne_top _ _)
    _ ≤ Real.exp (-2 * ((B : ℝ) / 4)^2 /
          ∑ _i : Fin B, ((1 : ℝ) - 0)^2) := hcenter
    _ = Real.exp (-(B : ℝ) / 8) := by
      congr 1
      simp only [sub_zero, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one]
      have hB0 : (B : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hB.ne'
      field_simp
      ring

/-- A number is a median of a finite family if at least half the observations lie on
each side of it. The cardinal inequalities avoid parity conventions.

**Lean implementation helper.** -/
def IsMedian {B : ℕ} (x : Fin B → ℝ) (M : ℝ) : Prop :=
  B ≤ 2 * (Finset.univ.filter fun i ↦ x i ≤ M).card ∧
    B ≤ 2 * (Finset.univ.filter fun i ↦ M ≤ x i).card

/-- If a finite median is above a threshold, at least half of the sample points are above that threshold.

**Lean implementation helper.** -/
private lemma median_upper_majority {B : ℕ} {x : Fin B → ℝ} {M u : ℝ}
    (hM : IsMedian x M) (hMu : u ≤ M) :
    (B : ℝ) / 2 ≤ ∑ i, if u ≤ x i then (1 : ℝ) else 0 := by
  have hsub : (Finset.univ.filter fun i ↦ M ≤ x i) ⊆
      (Finset.univ.filter fun i ↦ u ≤ x i) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hMu.trans hi
  have hcard := Finset.card_le_card hsub
  have hnat : B ≤ 2 * (Finset.univ.filter fun i ↦ u ≤ x i).card :=
    hM.2.trans (Nat.mul_le_mul_left 2 hcard)
  have hreal : (B : ℝ) ≤ 2 *
      ((Finset.univ.filter fun i ↦ u ≤ x i).card : ℝ) := by exact_mod_cast hnat
  have hhalf : (B : ℝ) / 2 ≤
      ((Finset.univ.filter fun i ↦ u ≤ x i).card : ℝ) := by linarith
  rw [show (∑ i, if u ≤ x i then (1 : ℝ) else 0) =
      ((Finset.univ.filter fun i ↦ u ≤ x i).card : ℝ) by
    rw [← Finset.sum_filter]
    simp]
  exact hhalf

/-- If a finite median is below a threshold, at least half of the sample points are below that threshold.

**Lean implementation helper.** -/
private lemma median_lower_majority {B : ℕ} {x : Fin B → ℝ} {M l : ℝ}
    (hM : IsMedian x M) (hMl : M ≤ l) :
    (B : ℝ) / 2 ≤ ∑ i, if x i ≤ l then (1 : ℝ) else 0 := by
  have hsub : (Finset.univ.filter fun i ↦ x i ≤ M) ⊆
      (Finset.univ.filter fun i ↦ x i ≤ l) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hi.trans hMl
  have hcard := Finset.card_le_card hsub
  have hnat : B ≤ 2 * (Finset.univ.filter fun i ↦ x i ≤ l).card :=
    hM.1.trans (Nat.mul_le_mul_left 2 hcard)
  have hreal : (B : ℝ) ≤ 2 *
      ((Finset.univ.filter fun i ↦ x i ≤ l).card : ℝ) := by exact_mod_cast hnat
  have hhalf : (B : ℝ) / 2 ≤
      ((Finset.univ.filter fun i ↦ x i ≤ l).card : ℝ) := by linarith
  rw [show (∑ i, if x i ≤ l then (1 : ℝ) else 0) =
      ((Finset.univ.filter fun i ↦ x i ≤ l).card : ℝ) by
    rw [← Finset.sum_filter]
    simp]
  exact hhalf

/-- If independent observations cross either of two barriers with probability at most
`1/4`, then any pointwise median crosses a barrier only with exponentially small
probability.

**Book Theorem 2.4.1.** -/
theorem median_of_rare_events [IsProbabilityMeasure μ] {B : ℕ}
    {Y : Fin B → Ω → ℝ} {M : Ω → ℝ} {l u : ℝ}
    (hY : ∀ i, Measurable (Y i))
    (hindep : iIndepFun Y μ)
    (hupper : ∀ i, μ.real {ω | u ≤ Y i ω} ≤ 1 / 4)
    (hlower : ∀ i, μ.real {ω | Y i ω ≤ l} ≤ 1 / 4)
    (hmedian : ∀ ω, IsMedian (fun i ↦ Y i ω) (M ω)) :
    μ.real {ω | M ω ≤ l ∨ u ≤ M ω} ≤ 2 * Real.exp (-(B : ℝ) / 8) := by
  let Zu : Fin B → Ω → ℝ := fun i ↦ (fun x ↦ if u ≤ x then 1 else 0) ∘ Y i
  let Zl : Fin B → Ω → ℝ := fun i ↦ (fun x ↦ if x ≤ l then 1 else 0) ∘ Y i
  have hZu_meas : ∀ i, AEMeasurable (Zu i) μ := by
    intro i
    exact (measurable_const.indicator (measurableSet_le measurable_const (hY i))).aemeasurable
  have hZl_meas : ∀ i, AEMeasurable (Zl i) μ := by
    intro i
    exact (measurable_const.indicator (measurableSet_le (hY i) measurable_const)).aemeasurable
  have hZu01 : ∀ i, ∀ᵐ ω ∂μ, Zu i ω ∈ Set.Icc (0 : ℝ) 1 := by
    intro i
    filter_upwards [] with ω
    by_cases h : u ≤ Y i ω <;> simp [Zu, h]
  have hZl01 : ∀ i, ∀ᵐ ω ∂μ, Zl i ω ∈ Set.Icc (0 : ℝ) 1 := by
    intro i
    filter_upwards [] with ω
    by_cases h : Y i ω ≤ l <;> simp [Zl, h]
  have hZu_indep : iIndepFun Zu μ := by
    exact hindep.comp (fun _ x ↦ if u ≤ x then (1 : ℝ) else 0)
      (fun _ ↦ measurable_const.indicator (measurableSet_Ici))
  have hZl_indep : iIndepFun Zl μ := by
    exact hindep.comp (fun _ x ↦ if x ≤ l then (1 : ℝ) else 0)
      (fun _ ↦ measurable_const.indicator (measurableSet_Iic))
  have hZu_mean : ∀ i, ∫ ω, Zu i ω ∂μ ≤ 1 / 4 := by
    intro i
    rw [show Zu i = {ω | u ≤ Y i ω}.indicator (fun _ ↦ (1 : ℝ)) by
      funext ω
      simp [Zu, Set.indicator]]
    rw [HDP.Chapter1.expectation_indicator _
      (measurableSet_le measurable_const (hY i))]
    exact hupper i
  have hZl_mean : ∀ i, ∫ ω, Zl i ω ∂μ ≤ 1 / 4 := by
    intro i
    rw [show Zl i = {ω | Y i ω ≤ l}.indicator (fun _ ↦ (1 : ℝ)) by
      funext ω
      simp [Zl, Set.indicator]]
    rw [HDP.Chapter1.expectation_indicator _
      (measurableSet_le (hY i) measurable_const)]
    exact hlower i
  have hu := majority_of_rare_events hZu_meas hZu01 hZu_indep hZu_mean
  have hl := majority_of_rare_events hZl_meas hZl01 hZl_indep hZl_mean
  have hsub : {ω | M ω ≤ l ∨ u ≤ M ω} ⊆
      {ω | (B : ℝ) / 2 ≤ ∑ i, Zl i ω} ∪
        {ω | (B : ℝ) / 2 ≤ ∑ i, Zu i ω} := by
    intro ω hω
    rcases hω with hω | hω
    · left
      exact median_lower_majority (hmedian ω) hω
    · right
      exact median_upper_majority (hmedian ω) hω
  calc
    μ.real {ω | M ω ≤ l ∨ u ≤ M ω}
        ≤ μ.real ({ω | (B : ℝ) / 2 ≤ ∑ i, Zl i ω} ∪
          {ω | (B : ℝ) / 2 ≤ ∑ i, Zu i ω}) :=
            measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ μ.real {ω | (B : ℝ) / 2 ≤ ∑ i, Zl i ω} +
          μ.real {ω | (B : ℝ) / 2 ≤ ∑ i, Zu i ω} :=
            measureReal_union_le _ _
    _ ≤ Real.exp (-(B : ℝ) / 8) + Real.exp (-(B : ℝ) / 8) := add_le_add hl hu
    _ = 2 * Real.exp (-(B : ℝ) / 8) := by ring

/-- Counting a predicate after converting a finite tuple to a function agrees with counting it on the tuple.

**Lean implementation helper.** -/
private lemma countP_ofFn {α : Type*} {B : ℕ} (x : Fin B → α) (p : α → Prop)
    [DecidablePred p] :
    (List.ofFn x).countP (fun a ↦ decide (p a)) =
      (Finset.univ.filter fun i ↦ p (x i)).card := by
  have hsum : (List.ofFn x).countP (fun a ↦ decide (p a)) =
      ∑ i, if p (x i) then 1 else 0 := by
    induction B with
    | zero => simp
    | succ B ih =>
        rw [List.ofFn_succ, List.countP_cons, Fin.sum_univ_succ]
        split_ifs <;> simp_all [Nat.add_comm]
  rw [hsum]
  have h := (Finset.sum_boole (fun i : Fin B ↦ p (x i)) Finset.univ :
    (∑ i ∈ Finset.univ, if p (x i) then 1 else 0 : ℕ) =
      (Finset.univ.filter fun i ↦ p (x i)).card)
  exact h

/-- Bounds `sorted_count` above by `getElem`.

**Lean implementation helper.** -/
private lemma sorted_count_le_getElem {l : List ℝ} (hl : l.SortedLE)
    (k : ℕ) (hk : k < l.length) :
    k + 1 ≤ l.countP (fun a ↦ decide (a ≤ l[k])) := by
  rw [List.countP_eq_length_filter]
  have hall : ∀ a ∈ l.take (k + 1), a ≤ l[k] := by
    intro a ha
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
    have hjk : j ≤ k := by
      simp only [List.length_take] at hj
      omega
    rw [List.getElem_take]
    exact hl.getElem_le_getElem_of_le hjk
  have hfilter : (l.take (k + 1)).filter (fun a ↦ decide (a ≤ l[k])) =
      l.take (k + 1) := by
    apply List.filter_eq_self.2
    intro a ha
    simpa using hall a ha
  have hsub := (List.take_sublist (k + 1) l).filter (fun a ↦ decide (a ≤ l[k]))
  rw [hfilter] at hsub
  have := List.Sublist.length_le hsub
  simpa [hk] using this

/-- For a sorted finite tuple, the number of entries below a selected entry is controlled by its index.

**Lean implementation helper.** -/
private lemma sorted_count_getElem_le {l : List ℝ} (hl : l.SortedLE)
    (k : ℕ) (hk : k < l.length) :
    l.length - k ≤ l.countP (fun a ↦ decide (l[k] ≤ a)) := by
  rw [List.countP_eq_length_filter]
  have hall : ∀ a ∈ l.drop k, l[k] ≤ a := by
    intro a ha
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
    rw [List.getElem_drop]
    exact hl.getElem_le_getElem_of_le (Nat.le_add_right k j)
  have hfilter : (l.drop k).filter (fun a ↦ decide (l[k] ≤ a)) = l.drop k := by
    apply List.filter_eq_self.2
    intro a ha
    simpa using hall a ha
  have hsub := (List.drop_sublist k l).filter (fun a ↦ decide (l[k] ≤ a))
  rw [hfilter] at hsub
  have := List.Sublist.length_le hsub
  simpa using this

/-- The middle order statistic, with the harmless value `0` for an empty family.

**Lean implementation helper.** -/
noncomputable def finiteMedian {B : ℕ} (x : Fin B → ℝ) : ℝ :=
  ((List.ofFn x).mergeSort (· ≤ ·)).getD (B / 2) 0

/-- The selected middle order statistic satisfies the defining upper- and lower-majority properties of a median.

**Lean implementation helper.** -/
theorem finiteMedian_isMedian {B : ℕ} (x : Fin B → ℝ) :
    IsMedian x (finiteMedian x) := by
  rcases Nat.eq_zero_or_pos B with rfl | hB
  · simp [IsMedian, finiteMedian]
  let l := (List.ofFn x).mergeSort (· ≤ ·)
  have hlen : l.length = B := by simp [l]
  have hk : B / 2 < l.length := by rw [hlen]; omega
  have hsort : l.SortedLE := by exact List.sortedLE_mergeSort
  have hmed : finiteMedian x = l[B / 2] := by
    rw [finiteMedian, List.getD_eq_getElem]
  have hperm : l.Perm (List.ofFn x) := by exact List.mergeSort_perm _ _
  constructor
  · have hs := sorted_count_le_getElem hsort (B / 2) hk
    have ho : B / 2 + 1 ≤
        (List.ofFn x).countP (fun a ↦ decide (a ≤ finiteMedian x)) := by
      rw [hmed]
      rw [← hperm.countP_eq]
      exact hs
    have hc : B / 2 + 1 ≤
        (Finset.univ.filter fun i ↦ x i ≤ finiteMedian x).card := by
      simpa [countP_ofFn] using ho
    omega
  · have hs := sorted_count_getElem_le hsort (B / 2) hk
    have ho : B - B / 2 ≤
        (List.ofFn x).countP (fun a ↦ decide (finiteMedian x ≤ a)) := by
      rw [hmed]
      rw [← hperm.countP_eq]
      simpa [hlen] using hs
    have hc : B - B / 2 ≤
        (Finset.univ.filter fun i ↦ finiteMedian x ≤ x i).card := by
      simpa [countP_ofFn] using ho
    omega

/-- The median-of-means functional applied to a family of block averages.

**Lean implementation helper.** -/
noncomputable def medianOfMeans {B : ℕ} (Y : Fin B → Ω → ℝ) (ω : Ω) : ℝ :=
  finiteMedian fun i ↦ Y i ω

/-- The median-of-means estimator is a median of the collection of block averages.

**Lean implementation helper.** -/
theorem medianOfMeans_isMedian {B : ℕ} (Y : Fin B → Ω → ℝ) (ω : Ω) :
    IsMedian (fun i ↦ Y i ω) (medianOfMeans Y ω) :=
  finiteMedian_isMedian _

/-- If fewer than half of the block means are bad, the median-of-means estimator lies in the good interval.

**Lean implementation helper.** -/
theorem medianOfMeans_of_rare_events [IsProbabilityMeasure μ] {B : ℕ}
    {Y : Fin B → Ω → ℝ} {l u : ℝ}
    (hY : ∀ i, Measurable (Y i))
    (hindep : iIndepFun Y μ)
    (hupper : ∀ i, μ.real {ω | u ≤ Y i ω} ≤ 1 / 4)
    (hlower : ∀ i, μ.real {ω | Y i ω ≤ l} ≤ 1 / 4) :
    μ.real {ω | medianOfMeans Y ω ≤ l ∨ u ≤ medianOfMeans Y ω} ≤
      2 * Real.exp (-(B : ℝ) / 8) :=
  median_of_rare_events hY hindep hupper hlower (medianOfMeans_isMedian Y)

/-- A Chebyshev wrapper that supplies the rare-event hypotheses for block averages.

**Lean implementation helper.** -/
theorem medianOfMeans_of_variance [IsProbabilityMeasure μ] {B : ℕ}
    {Y : Fin B → Ω → ℝ} {m a : ℝ}
    (ha : 0 < a) (hY : ∀ i, Measurable (Y i))
    (hindep : iIndepFun Y μ) (hmem : ∀ i, MemLp (Y i) 2 μ)
    (hmean : ∀ i, ∫ ω, Y i ω ∂μ = m)
    (hvar : ∀ i, Var[Y i; μ] ≤ a ^ 2 / 4) :
    μ.real {ω | a ≤ |medianOfMeans Y ω - m|} ≤
      2 * Real.exp (-(B : ℝ) / 8) := by
  have hcheb : ∀ i, μ.real {ω | a ≤ |Y i ω - m|} ≤ 1 / 4 := by
    intro i
    have h := HDP.Chapter1.chebyshev_inequality (μ := μ) (hmem i) ha
    rw [hmean i] at h
    calc
      μ.real {ω | a ≤ |Y i ω - m|} ≤ Var[Y i; μ] / a ^ 2 := h
      _ ≤ (a ^ 2 / 4) / a ^ 2 := div_le_div_of_nonneg_right (hvar i) (sq_nonneg a)
      _ = 1 / 4 := by field_simp
  have hupper : ∀ i, μ.real {ω | m + a ≤ Y i ω} ≤ 1 / 4 := by
    intro i
    refine (measureReal_mono ?_ (measure_ne_top _ _)).trans (hcheb i)
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hlower : ∀ i, μ.real {ω | Y i ω ≤ m - a} ≤ 1 / 4 := by
    intro i
    refine (measureReal_mono ?_ (measure_ne_top _ _)).trans (hcheb i)
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hmedian := medianOfMeans_of_rare_events hY hindep hupper hlower
  refine (measureReal_mono ?_ (measure_ne_top _ _)).trans hmedian
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  by_cases h : medianOfMeans Y ω ≤ m
  · left
    rw [abs_of_nonpos (sub_nonpos.mpr h)] at hω
    linarith
  · right
    rw [abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge h))] at hω
    linarith

/-! ## Integer blocks and the source-scale bound -/

/-- We use a rounded number of blocks. The factor `32` leaves room for both the
integer rounding and Chebyshev's inequality.

**Lean implementation helper.** -/
noncomputable def momBlockCount (t : ℝ) : ℕ :=
  max 1 ⌈t ^ 2 / 32⌉₊

/-- Shows that a median-of-means block quantity `Count` is positive.

**Lean implementation helper.** -/
theorem momBlockCount_pos (t : ℝ) : 0 < momBlockCount t := by
  simp [momBlockCount]

/-- The prescribed number of median-of-means blocks satisfies the lower bound needed for the tail estimate.

**Lean implementation helper.** -/
theorem momBlockCount_lower (t : ℝ) :
    t ^ 2 / 32 ≤ (momBlockCount t : ℝ) := by
  calc
    t ^ 2 / 32 ≤ (⌈t ^ 2 / 32⌉₊ : ℕ) := Nat.le_ceil _
    _ ≤ (momBlockCount t : ℝ) := by
      have hceil : ⌈t ^ 2 / 32⌉₊ ≤ momBlockCount t := by
        exact Nat.le_max_right 1 ⌈t ^ 2 / 32⌉₊
      exact_mod_cast hceil

/-- The `b`-th integer block. All non-final blocks have the quotient length
`N / B`; the final block is enlarged to absorb every remaining observation.

**Lean implementation helper.** -/
def momBlock (N B : ℕ) (b : Fin B) : Finset (Fin N) :=
  Finset.univ.filter fun j ↦
    b.1 * (N / B) ≤ j.1 ∧ (b.1 + 1 = B ∨ j.1 < (b.1 + 1) * (N / B))

/-- Characterizes membership in a median-of-means block.

**Lean implementation helper.** -/
@[simp] theorem mem_momBlock {N B : ℕ} {b : Fin B} {j : Fin N} :
    j ∈ momBlock N B b ↔
      b.1 * (N / B) ≤ j.1 ∧ (b.1 + 1 = B ∨ j.1 < (b.1 + 1) * (N / B)) := by
  simp [momBlock]

/-- Defines `momBlockSize`, the mom block size used in the surrounding construction.

**Lean implementation helper.** -/
def momBlockSize (N B : ℕ) (b : Fin B) : ℕ :=
  (momBlock N B b).card

/-- The average on an actual integer block of the original sample.

**Lean implementation helper.** -/
noncomputable def momBlockMean {N : ℕ} (X : Fin N → Ω → ℝ) {B : ℕ}
    (b : Fin B) (ω : Ω) : ℝ :=
  (∑ j ∈ momBlock N B b, X j ω) / momBlockSize N B b

/-- Shows that a median-of-means block average is measurable.

**Lean implementation helper.** -/
theorem momBlockMean_measurable {N B : ℕ} {X : Fin N → Ω → ℝ}
    (hX : ∀ j, Measurable (X j)) (b : Fin B) :
    Measurable (momBlockMean X b) := by
  unfold momBlockMean
  fun_prop

/-- The explicit absolute constant used below.

**Lean implementation helper.** -/
noncomputable def medianOfMeansConstant : ℝ := 1 / 256

/-- Shows that the median-of-means estimator quantity `Constant` is positive.

**Lean implementation helper.** -/
theorem medianOfMeansConstant_pos : 0 < medianOfMeansConstant := by
  norm_num [medianOfMeansConstant]

/-- For `t ≤ 4` the claimed right-hand side is already at least one, so no
concentration argument (and no nonzero-threshold division) is needed.

**Lean implementation helper.** -/
theorem medianOfMeans_small_t [IsProbabilityMeasure μ] {M : Ω → ℝ} {m a t : ℝ}
    (ht : 0 ≤ t) (ht4 : t ≤ 4) :
    μ.real {ω | a ≤ |M ω - m|} ≤
      2 * Real.exp (-medianOfMeansConstant * t ^ 2) := by
  calc
    μ.real {ω | a ≤ |M ω - m|} ≤ 1 := measureReal_le_one
    _ ≤ 2 * Real.exp (-medianOfMeansConstant * t ^ 2) := by
      have ht_sq : t ^ 2 ≤ 16 := by nlinarith
      have he := Real.add_one_le_exp (-medianOfMeansConstant * t ^ 2)
      rw [medianOfMeansConstant] at he ⊢
      norm_num at he ⊢
      nlinarith

/-- The estimator is the median of the averages on the integer blocks `momBlock`; the
last block absorbs the remainder. The hypotheses below are the precise properties
of the block averages used in the proof (measurability, independence, common mean,
and the variance estimate obtained from independent samples).

**Book Theorem 2.4.1.** -/
theorem medianOfMeans_explicit [IsProbabilityMeasure μ] {N : ℕ} (hN : 0 < N)
    {X : Fin N → Ω → ℝ} {m sigma t : ℝ} (hsigma : 0 < sigma) (ht : 0 ≤ t)
    (hY : ∀ b : Fin (momBlockCount t), Measurable (momBlockMean X b))
    (hindep : iIndepFun (fun b : Fin (momBlockCount t) ↦ momBlockMean X b) μ)
    (hmem : ∀ b : Fin (momBlockCount t), MemLp (momBlockMean X b) 2 μ)
    (hmean : ∀ b : Fin (momBlockCount t), ∫ ω, momBlockMean X b ω ∂μ = m)
    (hvar : ∀ b : Fin (momBlockCount t),
      Var[momBlockMean X b; μ] ≤ (t * sigma / Real.sqrt N) ^ 2 / 4) :
    μ.real {ω | t * sigma / Real.sqrt N ≤
        |medianOfMeans (fun b : Fin (momBlockCount t) ↦ momBlockMean X b) ω - m|} ≤
      2 * Real.exp (-medianOfMeansConstant * t ^ 2) := by
  by_cases ht4 : t ≤ 4
  · have hsmall := medianOfMeans_small_t (μ := μ)
      (M := medianOfMeans (fun b : Fin (momBlockCount t) ↦ momBlockMean X b))
      (m := m) (a := t * sigma / Real.sqrt N) ht ht4
    exact hsmall
  · have ha : 0 < t * sigma / Real.sqrt N := by
      have htpos : 0 < t := by
        have : 4 < t := lt_of_not_ge ht4
        linarith
      positivity
    have hmain := medianOfMeans_of_variance (μ := μ) ha hY hindep hmem hmean hvar
    calc
      μ.real {ω | t * sigma / Real.sqrt N ≤
          |medianOfMeans (fun b : Fin (momBlockCount t) ↦ momBlockMean X b) ω - m|}
          ≤ 2 * Real.exp (-(momBlockCount t : ℝ) / 8) := hmain
      _ ≤ 2 * Real.exp (-medianOfMeansConstant * t ^ 2) := by
        gcongr
        have hB := momBlockCount_lower t
        rw [medianOfMeansConstant]
        norm_num
        linarith

/-- The source-style existential-constant wrapper around the explicit theorem.

**Book Theorem 2.4.1.** -/
theorem medianOfMeans_theorem_2_4_1 [IsProbabilityMeasure μ] {N : ℕ} (hN : 0 < N)
    {X : Fin N → Ω → ℝ} {m sigma t : ℝ} (hsigma : 0 < sigma) (ht : 0 ≤ t)
    (_htN : t ≤ Real.sqrt N)
    (hY : ∀ b : Fin (momBlockCount t), Measurable (momBlockMean X b))
    (hindep : iIndepFun (fun b : Fin (momBlockCount t) ↦ momBlockMean X b) μ)
    (hmem : ∀ b : Fin (momBlockCount t), MemLp (momBlockMean X b) 2 μ)
    (hmean : ∀ b : Fin (momBlockCount t), ∫ ω, momBlockMean X b ω ∂μ = m)
    (hvar : ∀ b : Fin (momBlockCount t),
      Var[momBlockMean X b; μ] ≤ (t * sigma / Real.sqrt N) ^ 2 / 4) :
    ∃ c : ℝ, 0 < c ∧
      μ.real {ω | t * sigma / Real.sqrt N ≤
        |medianOfMeans (fun b : Fin (momBlockCount t) ↦ momBlockMean X b) ω - m|} ≤
        2 * Real.exp (-c * t ^ 2) := by
  exact ⟨medianOfMeansConstant, medianOfMeansConstant_pos,
    medianOfMeans_explicit hN hsigma ht hY hindep hmem hmean hvar⟩

end HDP.Chapter2

end Source_04_MedianOfMeans

/-! ## Material formerly in `05_RandomGraphs.lean` -/

section Source_05_RandomGraphs

/-!
# Book §2.5: degrees of random graphs

Chernoff bounds for the concrete finite product-space model from `Prelude.RandomGraph`.
The source's unspecified absolute constant is made explicit as `3000`.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal unitInterval

namespace HDP.Chapter2

/-- A vertex degree differs from its mean by more than ten percent.

**Lean implementation helper.** -/
def badDegreeEvent {n : ℕ} (p : I) (v : Fin n) : Set (HDP.ERSample n) :=
  {G | HDP.expectedDegree n p / 10 < |HDP.degree v G - HDP.expectedDegree n p|}

/-- Some vertex degree differs from its mean by more than ten percent.

**Lean implementation helper.** -/
def badDegreeUnion (n : ℕ) (p : I) : Set (HDP.ERSample n) :=
  ⋃ v : Fin n, badDegreeEvent p v

/-- Shows that `badDegreeEvent` is measurable.

**Lean implementation helper.** -/
lemma badDegreeEvent_measurable {n : ℕ} (p : I) (v : Fin n) :
    MeasurableSet (badDegreeEvent p v) := by
  exact (by fun_prop : Measurable fun G ↦ |HDP.degree v G - HDP.expectedDegree n p|)
    measurableSet_Ioi

/-- Shows that `badDegreeUnion` is measurable.

**Lean implementation helper.** -/
lemma badDegreeUnion_measurable (n : ℕ) (p : I) : MeasurableSet (badDegreeUnion n p) := by
  exact MeasurableSet.iUnion fun v ↦ badDegreeEvent_measurable p v

/-- Chernoff's small-deviation inequality applied to one fixed vertex degree.

**Lean implementation helper.** -/
theorem degree_tail_bound {n : ℕ} (p : I) (v : Fin n) :
    (HDP.erdosRenyi n p).real
        {G | (1 / 10 : ℝ) * HDP.expectedDegree n p ≤
          |HDP.degree v G - HDP.expectedDegree n p|}
      ≤ 2 * Real.exp (-(1 / 10 : ℝ)^2 * HDP.expectedDegree n p / 3) := by
  let e := Fintype.equivFin (HDP.ERNeighbor n v)
  let X : Fin (Fintype.card (HDP.ERNeighbor n v)) → HDP.ERSample n → ℝ :=
    fun i ↦ HDP.edgeIndicator (HDP.incidentEdge v (e.symm i))
  let q : Fin (Fintype.card (HDP.ERNeighbor n v)) → I := fun _ ↦ p
  have hX : ∀ i, HDP.IsBernoulli (X i) (q i) (HDP.erdosRenyi n p) := by
    intro i
    exact HDP.edgeIndicator_isBernoulli p _
  have hi : iIndepFun X (HDP.erdosRenyi n p) := by
    exact iIndepFun.precomp e.symm.injective (HDP.incident_independent p v)
  have hsum (G : HDP.ERSample n) : ∑ i, X i G = HDP.degree v G := by
    change (∑ i, HDP.edgeIndicator (HDP.incidentEdge v (e.symm i)) G) =
      ∑ w, HDP.edgeIndicator (HDP.incidentEdge v w) G
    exact e.symm.sum_comp (fun w ↦ HDP.edgeIndicator (HDP.incidentEdge v w) G)
  have hmean : ∑ i, (q i : ℝ) = HDP.expectedDegree n p := by
    simp [q, HDP.expectedDegree, HDP.ERNeighbor]
  simpa only [hsum, hmean] using
    (chernoff_small_deviations hX hi
      (show (0 : ℝ) ≤ 1 / 10 by norm_num) (show (1 / 10 : ℝ) ≤ 1 by norm_num))

/-- The fixed-vertex tail in the simplified `2 exp(-d/300)` form.

**Lean implementation helper.** -/
lemma fixed_badDegreeEvent_bound {n : ℕ} (p : I) (v : Fin n) :
    (HDP.erdosRenyi n p).real (badDegreeEvent p v)
      ≤ 2 * Real.exp (-HDP.expectedDegree n p / 300) := by
  calc
    (HDP.erdosRenyi n p).real (badDegreeEvent p v)
        ≤ (HDP.erdosRenyi n p).real
          {G | (1 / 10 : ℝ) * HDP.expectedDegree n p ≤
            |HDP.degree v G - HDP.expectedDegree n p|} := by
          refine measureReal_mono ?_ (measure_ne_top _ _)
          intro G hG
          change HDP.expectedDegree n p / 10 <
            |HDP.degree v G - HDP.expectedDegree n p| at hG
          change (1 / 10 : ℝ) * HDP.expectedDegree n p ≤
            |HDP.degree v G - HDP.expectedDegree n p|
          nlinarith
    _ ≤ 2 * Real.exp (-(1 / 10 : ℝ)^2 * HDP.expectedDegree n p / 3) :=
      degree_tail_bound p v
    _ = 2 * Real.exp (-HDP.expectedDegree n p / 300) := by congr 2; ring

/-- Union bound over all vertices.

**Lean implementation helper.** -/
lemma badDegreeUnion_bound (n : ℕ) (p : I) :
    (HDP.erdosRenyi n p).real (badDegreeUnion n p)
      ≤ (n : ℝ) * (2 * Real.exp (-HDP.expectedDegree n p / 300)) := by
  calc
    (HDP.erdosRenyi n p).real (badDegreeUnion n p)
        ≤ ∑ v : Fin n, (HDP.erdosRenyi n p).real (badDegreeEvent p v) :=
          HDP.Chapter1.union_bound_fintype _ (fun v ↦ badDegreeEvent_measurable p v)
    _ ≤ ∑ _v : Fin n, 2 * Real.exp (-HDP.expectedDegree n p / 300) :=
      Finset.sum_le_sum fun v _ ↦ fixed_badDegreeEvent_bound p v
    _ = (n : ℝ) * (2 * Real.exp (-HDP.expectedDegree n p / 300)) := by simp

/-- Numerical estimate behind the explicit absolute constant `3000`.

**Lean implementation helper.** -/
lemma dense_graph_numeric {n : ℕ} (hn : 2 ≤ n) {d : ℝ}
    (hd : 3000 * Real.log n ≤ d) :
    (n : ℝ) * (2 * Real.exp (-d / 300)) ≤ 1 / 100 := by
  have hn0 : (0 : ℝ) < n := by positivity
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hexp : Real.exp (-d / 300) ≤ Real.exp (-10 * Real.log n) := by
    rw [Real.exp_le_exp]
    linarith
  have hlog : Real.exp (-10 * Real.log n) = 1 / (n : ℝ) ^ 10 := by
    rw [show (-10 : ℝ) * Real.log n = -(10 * Real.log n) by ring, Real.exp_neg,
      show (10 : ℝ) * Real.log n = Real.log ((n : ℝ) ^ 10) by
      rw [Real.log_pow]; norm_num]
    rw [Real.exp_log (by positivity)]
    exact (one_div _).symm
  have hpow : (200 : ℝ) ≤ (n : ℝ) ^ 9 := by
    calc
      (200 : ℝ) ≤ 2 ^ 9 := by norm_num
      _ ≤ (n : ℝ) ^ 9 := pow_le_pow_left₀ (by norm_num) hn2 9
  calc
    (n : ℝ) * (2 * Real.exp (-d / 300))
        ≤ (n : ℝ) * (2 * (1 / (n : ℝ) ^ 10)) := by
          gcongr
          exact hexp.trans_eq hlog
    _ = 2 / (n : ℝ) ^ 9 := by field_simp
    _ ≤ 1 / 100 := by
      rw [div_le_div_iff₀ (pow_pos hn0 9) (by norm_num : (0 : ℝ) < 100)]
      nlinarith

/-- Explicit absolute constant used in Proposition 2.5.1.

**Book Proposition 2.5.1.** -/
def denseGraphsAlmostRegularConstant : ℝ := 3000

/-- If expected degree is at least `C log n`, all Erdos--Renyi degrees lie within 10% of the mean with probability at least `.99`.

**Book Proposition 2.5.1.** -/
theorem dense_graphs_almost_regular_explicit {n : ℕ} (p : I) (hn : 2 ≤ n)
    (hd : denseGraphsAlmostRegularConstant * Real.log n ≤ HDP.expectedDegree n p) :
    99 / 100 ≤ (HDP.erdosRenyi n p).real
      {G | ∀ v : Fin n,
        (9 / 10 : ℝ) * HDP.expectedDegree n p ≤ HDP.degree v G ∧
        HDP.degree v G ≤ (11 / 10 : ℝ) * HDP.expectedDegree n p} := by
  let good : Set (HDP.ERSample n) :=
    {G | ∀ v : Fin n,
      (9 / 10 : ℝ) * HDP.expectedDegree n p ≤ HDP.degree v G ∧
      HDP.degree v G ≤ (11 / 10 : ℝ) * HDP.expectedDegree n p}
  have hdnn : 0 ≤ HDP.expectedDegree n p := by
    exact mul_nonneg (by positivity) p.2.1
  have hgood : good = (badDegreeUnion n p)ᶜ := by
    ext G
    simp only [good, Set.mem_setOf_eq, Set.mem_compl_iff, badDegreeUnion,
      Set.mem_iUnion, badDegreeEvent]
    constructor
    · intro h hbad
      obtain ⟨v, hv⟩ := hbad
      rcases h v with ⟨hl, hu⟩
      have habs : |HDP.degree v G - HDP.expectedDegree n p| ≤
          HDP.expectedDegree n p / 10 := by
        rw [abs_le]
        constructor <;> nlinarith
      exact (not_lt_of_ge habs) hv
    · intro h v
      have hv : ¬ HDP.expectedDegree n p / 10 <
          |HDP.degree v G - HDP.expectedDegree n p| := by
        exact fun hv ↦ h ⟨v, hv⟩
      rw [not_lt, abs_le] at hv
      constructor <;> nlinarith
  have hbad : (HDP.erdosRenyi n p).real (badDegreeUnion n p) ≤ 1 / 100 := by
    refine (badDegreeUnion_bound n p).trans ?_
    apply dense_graph_numeric hn
    simpa [denseGraphsAlmostRegularConstant] using hd
  change 99 / 100 ≤ (HDP.erdosRenyi n p).real good
  rw [hgood, measureReal_compl (badDegreeUnion_measurable n p), probReal_univ]
  linarith

/-- Source-facing existential formulation of Proposition 2.5.1.

**Book Proposition 2.5.1.** -/
theorem dense_graphs_almost_regular :
    ∃ C : ℝ, 0 < C ∧ ∀ {n : ℕ} (p : I), 2 ≤ n →
      C * Real.log n ≤ HDP.expectedDegree n p →
      99 / 100 ≤ (HDP.erdosRenyi n p).real
        {G | ∀ v : Fin n,
          (9 / 10 : ℝ) * HDP.expectedDegree n p ≤ HDP.degree v G ∧
          HDP.degree v G ≤ (11 / 10 : ℝ) * HDP.expectedDegree n p} := by
  refine ⟨denseGraphsAlmostRegularConstant, by norm_num [denseGraphsAlmostRegularConstant], ?_⟩
  intro n p hn hd
  exact dense_graphs_almost_regular_explicit p hn hd

end HDP.Chapter2

end Source_05_RandomGraphs

/-! ## Material formerly in `06_SubGaussian.lean` -/

section Source_06_SubGaussian

/-
Book Chapter 2, Section 2.6: Subgaussian distributions — the ψ₂ norm and the
equivalences of Proposition 2.6.1.



Contents:
* the ψ₂ functional `𝔼 exp(X²/K²)` (unconditional `∫⁻` form), subgaussian random
  variables, and the subgaussian norm (Book Definition 2.6.4, (2.18));
* attainment of the infimum in (2.18) (hidden well-definedness obligation);
* the equivalences of Book Proposition 2.6.1 with explicit absolute constants:
  (iii)⇒(i) [K₁ = K₃], (i)⇒(iii) [K₃ = √5·K₁], (iii)⇒(ii) [K₂ = K₃],
  (ii)⇒(iii) [K₃ = 2√e·K₂], (iii)⇒(iv) [K₄ = √(3/2)·K₃, mean zero],
  (iv)⇒(i) [K₁ = 2K₄];
* the ψ₂-norm forms of Book Proposition 2.6.6 (i)–(iv), with the "moreover" optimality
  clauses;
* `X = 0` a.e. when the ψ₂ norm vanishes (needed for the norm axioms of Ex 2.42).

Convention (statement audit): the four properties are stated with expectations of
nonnegative quantities in `∫⁻` form, so each property asserts the finiteness that the
source carries implicitly; Bochner corollaries are provided where used downstream.
The proofs of (i)⇒(ii)/(iii) replace the source's Gamma-function route by equivalent
elementary arguments with absolute constants (documented in the proof audit); the
remaining directions follow the source's proofs.
-/



open MeasureTheory ProbabilityTheory Real Filter
open scoped ENNReal NNReal Topology Nat

namespace HDP

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-! ## The ψ₂ functional, subgaussian random variables, and the ψ₂ norm -/

/-- The ψ₂ functional `𝔼 exp(X²/K²)` of the source (2.18), in unconditional `∫⁻` form
(value in `[0,∞]`). Implicit source definition.

**Book Definition 2.6.4.** -/
noncomputable def psi2MGF (X : Ω → ℝ) (μ : Measure Ω) (K : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (Real.exp ((X ω)^2 / K^2)) ∂μ

/-- First half): `X` is *subgaussian* if `𝔼exp(X²/K²) ≤ 2`
for some `K > 0` (property (iii) of Proposition 2.6.1, which the source takes as
defining). Explicit source declaration.

**Book Equation (2.15).** -/
def SubGaussian (X : Ω → ℝ) (μ : Measure Ω) : Prop :=
  ∃ K : ℝ, 0 < K ∧ psi2MGF X μ K ≤ 2

/-- Second half): the subgaussian norm
`‖X‖_{ψ₂} = inf {K > 0: 𝔼exp(X²/K²) ≤ 2}`. Explicit source declaration.

**Book Definition 2.6.4.** -/
noncomputable def psi2Norm (X : Ω → ℝ) (μ : Measure Ω) : ℝ :=
  sInf {K : ℝ | 0 < K ∧ psi2MGF X μ K ≤ 2}

/-- Shows that the ψ₂ norm is nonnegative.

**Lean implementation helper.** -/
lemma psi2Norm_nonneg (X : Ω → ℝ) (μ : Measure Ω) : 0 ≤ psi2Norm X μ :=
  Real.sInf_nonneg fun _ hx => hx.1.le

/-- Antitonicity of the ψ₂ functional in `K` (the defining set of (2.18) is upward
closed; implicit well-definedness fact).

**Lean implementation helper.** -/
lemma psi2MGF_anti (X : Ω → ℝ) {K K' : ℝ} (hK : 0 < K) (hKK' : K ≤ K') :
    psi2MGF X μ K' ≤ psi2MGF X μ K := by
  refine lintegral_mono fun ω => ?_
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by nlinarith)

/-- If `K > 0` and `psi2MGF X μ K ≤ 2`, then `psi2Norm X μ ≤ K`; this is the bound recorded by `psi2Norm_le`.

**Lean implementation helper.** -/
lemma psi2Norm_le (X : Ω → ℝ) {K : ℝ} (hK : 0 < K) (h : psi2MGF X μ K ≤ 2) :
    psi2Norm X μ ≤ K :=
  csInf_le ⟨0, fun _ hx => hx.1.le⟩ ⟨hK, h⟩

/-- Any `K` strictly above the ψ₂ norm of a subgaussian variable satisfies the
defining bound.

**Lean implementation helper.** -/
lemma psi2MGF_le_two_of_gt {X : Ω → ℝ} (h : SubGaussian X μ) {K : ℝ}
    (hK : psi2Norm X μ < K) : psi2MGF X μ K ≤ 2 := by
  have hne : {K : ℝ | 0 < K ∧ psi2MGF X μ K ≤ 2}.Nonempty := h
  obtain ⟨K', hK'mem, hK'lt⟩ := exists_lt_of_csInf_lt hne hK
  exact (psi2MGF_anti X hK'mem.1 hK'lt.le).trans hK'mem.2

/-- The ψ₂ functional at `K = 0` (junk value: the integrand is `exp 0 = 1`).

**Lean implementation helper.** -/
lemma psi2MGF_zero [IsProbabilityMeasure μ] (X : Ω → ℝ) : psi2MGF X μ 0 = 1 := by
  unfold psi2MGF
  norm_num

/-- **Attainment of the infimum in (2.18)** (hidden well-definedness obligation of
Definition 2.6.4, "the smallest `K₃`"): for subgaussian `X`,
`𝔼 exp(X²/‖X‖²_{ψ₂}) ≤ 2`. Implicit source claim; proved by monotone convergence
along `Kₙ ↓ ‖X‖_{ψ₂}`.

**Book Definition 2.6.4.** -/
theorem psi2MGF_psi2Norm_le_two [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXm : AEMeasurable X μ) (h : SubGaussian X μ) :
    psi2MGF X μ (psi2Norm X μ) ≤ 2 := by
  set K₀ := psi2Norm X μ with hK₀
  rcases eq_or_lt_of_le (psi2Norm_nonneg X μ) with h0 | h0
  · rw [show K₀ = 0 from hK₀.trans h0.symm, psi2MGF_zero]
    norm_num
  set f : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    ENNReal.ofReal (Real.exp ((X ω)^2 / (K₀ + 1/(n+1))^2)) with hf
  have hbound : ∀ n, ∫⁻ ω, f n ω ∂μ ≤ 2 := by
    intro n
    refine psi2MGF_le_two_of_gt h ?_
    have : (0:ℝ) < 1/((n:ℝ)+1) := by positivity
    linarith
  have hmeas : ∀ n, AEMeasurable (f n) μ := fun n =>
    (measurable_exp.comp_aemeasurable
      ((hXm.pow_const 2).div_const _)).ennreal_ofReal
  have hmono : ∀ᵐ ω ∂μ, Monotone fun n => f n ω := by
    refine Filter.Eventually.of_forall fun ω n m hnm => ?_
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have h1 : (1:ℝ)/((m:ℝ)+1) ≤ 1/((n:ℝ)+1) := by
      apply one_div_le_one_div_of_le (by positivity)
      have : ((n:ℝ)+1) ≤ ((m:ℝ)+1) := by
        exact_mod_cast Nat.succ_le_succ hnm
      linarith
    have hKm : (0:ℝ) < K₀ + 1/((m:ℝ)+1) := by positivity
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by nlinarith)
  have htends : ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop
      (𝓝 (ENNReal.ofReal (Real.exp ((X ω)^2 / K₀^2)))) := by
    refine Filter.Eventually.of_forall fun ω => ?_
    have h1 : Tendsto (fun n : ℕ => K₀ + 1/((n:ℝ)+1)) atTop (𝓝 K₀) := by
      have h2 : Tendsto (fun n : ℕ => 1/((n:ℝ)+1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      simpa using tendsto_const_nhds.add h2
    have hsq : Tendsto (fun n : ℕ => ((K₀ + 1/((n:ℝ)+1))^2 : ℝ)) atTop
        (𝓝 (K₀^2)) := by
      simpa [pow_two] using h1.mul h1
    have h2 : Tendsto (fun n : ℕ => (X ω)^2 / (K₀ + 1/((n:ℝ)+1))^2) atTop
        (𝓝 ((X ω)^2 / K₀^2)) :=
      Tendsto.div tendsto_const_nhds hsq (by positivity)
    exact (ENNReal.continuous_ofReal.tendsto _).comp
      ((Real.continuous_exp.tendsto _).comp h2)
  exact le_of_tendsto (lintegral_tendsto_of_tendsto_of_monotone hmeas hmono htends)
    (Filter.Eventually.of_forall hbound)

/-- Bochner-form corollary of (iii): `exp(X²/K²)` is integrable with expectation ≤ 2
(surfaces the integrability obligation).

**Lean implementation helper.** -/
lemma integrable_exp_sq_div {X : Ω → ℝ} (hXm : AEMeasurable X μ) {K : ℝ}
    (h : psi2MGF X μ K ≤ 2) :
    Integrable (fun ω => Real.exp ((X ω)^2 / K^2)) μ ∧
      ∫ ω, Real.exp ((X ω)^2 / K^2) ∂μ ≤ 2 := by
  have hmeas : AEStronglyMeasurable (fun ω => Real.exp ((X ω)^2 / K^2)) μ :=
    (measurable_exp.comp_aemeasurable
      ((hXm.pow_const 2).div_const _)).aestronglyMeasurable
  have hlin : ∫⁻ ω, ‖Real.exp ((X ω)^2 / K^2)‖ₑ ∂μ = psi2MGF X μ K := by
    unfold psi2MGF
    refine lintegral_congr fun ω => ?_
    rw [Real.enorm_eq_ofReal_abs, abs_of_pos (Real.exp_pos _)]
  have hfin : HasFiniteIntegral (fun ω => Real.exp ((X ω)^2 / K^2)) μ := by
    rw [hasFiniteIntegral_iff_enorm, hlin]
    exact lt_of_le_of_lt h (by norm_num)
  refine ⟨⟨hmeas, hfin⟩, ?_⟩
  have h1 : ∫ ω, Real.exp ((X ω)^2 / K^2) ∂μ = (psi2MGF X μ K).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le) hmeas]
    rfl
  rw [h1]
  calc (psi2MGF X μ K).toReal ≤ (2:ℝ≥0∞).toReal :=
        ENNReal.toReal_mono (by norm_num) h
    _ = 2 := by norm_num

/-! ## Proposition 2.6.1: the equivalences

Property forms (file docstring convention):
(i)  `∀ t ≥ 0, ℙ{|X| ≥ t} ≤ 2exp(−t²/K₁²)`;
(ii) `∀ p ≥ 1, 𝔼|X|^p ≤ (K₂√p)^p`;
(iii) `𝔼exp(X²/K₃²) ≤ 2`;
(iv) `∀ λ, 𝔼exp(λX) ≤ exp(K₄²λ²)`. -/

/-- With `K₁ = K₃` (the source's rescaling
argument, exponentiate-and-Markov): `ℙ{|X| ≥ t} ≤ 2e^{−t²/K₃²}`.

**Book Equation (2.15).** -/
theorem subgaussian_iii_to_i [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXm : AEMeasurable X μ) {K : ℝ} (hK : 0 < K) (h : psi2MGF X μ K ≤ 2)
    {t : ℝ} (ht : 0 ≤ t) :
    μ {ω | t ≤ |X ω|} ≤ ENNReal.ofReal (2 * Real.exp (-t^2/K^2)) := by
  set c : ℝ≥0∞ := ENNReal.ofReal (Real.exp (t^2/K^2)) with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hctop : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hf : AEMeasurable (fun ω => ENNReal.ofReal (Real.exp ((X ω)^2/K^2))) μ :=
    (measurable_exp.comp_aemeasurable
      ((hXm.pow_const 2).div_const _)).ennreal_ofReal
  have hsub : {ω | t ≤ |X ω|}
      ⊆ {ω | c ≤ ENNReal.ofReal (Real.exp ((X ω)^2/K^2))} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    rw [hc]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have h1 : t^2 ≤ (X ω)^2 := by
      rw [← sq_abs (X ω)]
      nlinarith [abs_nonneg (X ω)]
    gcongr
  calc μ {ω | t ≤ |X ω|}
      ≤ μ {ω | c ≤ ENNReal.ofReal (Real.exp ((X ω)^2/K^2))} := measure_mono hsub
    _ ≤ (∫⁻ ω, ENNReal.ofReal (Real.exp ((X ω)^2/K^2)) ∂μ) / c :=
        meas_ge_le_lintegral_div hf hc0 hctop
    _ ≤ 2 / c := by
        gcongr
        exact h
    _ = ENNReal.ofReal (2 * Real.exp (-t^2/K^2)) := by
        rw [hc, ENNReal.div_eq_inv_mul,
          ← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← Real.exp_neg]
        rw [show (2:ℝ≥0∞) = ENNReal.ofReal 2 from by norm_num,
          ← ENNReal.ofReal_mul (Real.exp_pos _).le]
        congr 1
        rw [neg_div]
        ring

/-- With `K₃ = √5·K₁` (equivalent alternative to
the source's route (i)⇒(ii)⇒(iii); see the proof audit): the layer-cake formula
(the source Lemma 1.6.1) turns the gaussian tail into a polynomially decaying integrand.

**Book Equation (2.15).** -/
theorem subgaussian_i_to_iii [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXm : AEMeasurable X μ) {K₁ : ℝ} (hK₁ : 0 < K₁)
    (h : ∀ t : ℝ, 0 ≤ t →
      μ {ω | t ≤ |X ω|} ≤ ENNReal.ofReal (2 * Real.exp (-t^2/K₁^2))) :
    psi2MGF X μ (Real.sqrt 5 * K₁) ≤ 2 := by
  set K : ℝ := Real.sqrt 5 * K₁ with hKdef
  have hK : 0 < K := by positivity
  have hKsq : K^2 = 5 * K₁^2 := by
    rw [hKdef, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)]
  -- layer cake
  have hlc : psi2MGF X μ K
      = ∫⁻ t in Set.Ioi (0:ℝ), μ {ω | t < Real.exp ((X ω)^2/K^2)} := by
    unfold psi2MGF
    exact lintegral_eq_lintegral_meas_lt μ
      (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le)
      (measurable_exp.comp_aemeasurable ((hXm.pow_const 2).div_const _))
  rw [hlc]
  -- split the domain at 1
  have hsplit : (Set.Ioi (0:ℝ)) = Set.Ioc 0 1 ∪ Set.Ioi 1 :=
    (Set.Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  rw [hsplit, lintegral_union measurableSet_Ioi Set.Ioc_disjoint_Ioi_same]
  -- piece 1: bounded by `volume (Ioc 0 1) = 1`
  have hpiece1 : ∫⁻ t in Set.Ioc (0:ℝ) 1, μ {ω | t < Real.exp ((X ω)^2/K^2)}
      ≤ 1 := by
    calc ∫⁻ t in Set.Ioc (0:ℝ) 1, μ {ω | t < Real.exp ((X ω)^2/K^2)}
        ≤ ∫⁻ _t in Set.Ioc (0:ℝ) 1, 1 := lintegral_mono fun t => prob_le_one
      _ = 1 := by simp [Real.volume_Ioc]
  -- piece 2: tail bound gives `2t^{-5}`
  have hpiece2 : ∫⁻ t in Set.Ioi (1:ℝ), μ {ω | t < Real.exp ((X ω)^2/K^2)}
      ≤ ENNReal.ofReal (1/2) := by
    have hptw : ∀ t ∈ Set.Ioi (1:ℝ),
        μ {ω | t < Real.exp ((X ω)^2/K^2)}
          ≤ ENNReal.ofReal (2 * t ^ (-5 : ℝ)) := by
      intro t ht
      rw [Set.mem_Ioi] at ht
      have ht0 : (0:ℝ) < t := by linarith
      have hlog : 0 ≤ Real.log t := Real.log_nonneg ht.le
      have hsub2 : {ω | t < Real.exp ((X ω)^2/K^2)}
          ⊆ {ω | K * Real.sqrt (Real.log t) ≤ |X ω|} := by
        intro ω hω
        simp only [Set.mem_setOf_eq] at hω ⊢
        have h1 : Real.log t < (X ω)^2/K^2 := by
          have := Real.log_lt_log ht0 hω
          rwa [Real.log_exp] at this
        have h2 : K^2 * Real.log t ≤ (X ω)^2 := by
          rw [← le_div_iff₀' (by positivity)]
          exact h1.le
        have h3 : (K * Real.sqrt (Real.log t))^2 ≤ |X ω|^2 := by
          rw [mul_pow, Real.sq_sqrt hlog, sq_abs]
          exact h2
        have h4 : 0 ≤ K * Real.sqrt (Real.log t) := by positivity
        nlinarith [abs_nonneg (X ω)]
      calc μ {ω | t < Real.exp ((X ω)^2/K^2)}
          ≤ μ {ω | K * Real.sqrt (Real.log t) ≤ |X ω|} := measure_mono hsub2
        _ ≤ ENNReal.ofReal (2 * Real.exp (-(K * Real.sqrt (Real.log t))^2/K₁^2)) :=
            h _ (by positivity)
        _ = ENNReal.ofReal (2 * t ^ (-5 : ℝ)) := by
            congr 1
            rw [mul_pow, Real.sq_sqrt hlog, hKsq]
            rw [show -(5 * K₁^2 * Real.log t)/K₁^2 = -5 * Real.log t by
              field_simp]
            rw [Real.rpow_def_of_pos ht0]
            ring_nf
    calc ∫⁻ t in Set.Ioi (1:ℝ), μ {ω | t < Real.exp ((X ω)^2/K^2)}
        ≤ ∫⁻ t in Set.Ioi (1:ℝ), ENNReal.ofReal (2 * t ^ (-5 : ℝ)) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          exact hptw t ht
      _ = ENNReal.ofReal (∫ t in Set.Ioi (1:ℝ), 2 * t ^ (-5 : ℝ)) := by
          rw [← ofReal_integral_eq_lintegral_ofReal]
          · exact ((integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).const_mul 2)
          · refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_)
            have ht0 : (0:ℝ) < t := lt_trans one_pos ht
            positivity
      _ = ENNReal.ofReal (1/2) := by
          congr 1
          rw [MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt
            (by norm_num) one_pos]
          norm_num
  calc (∫⁻ t in Set.Ioc (0:ℝ) 1, μ {ω | t < Real.exp ((X ω)^2/K^2)})
        + ∫⁻ t in Set.Ioi (1:ℝ), μ {ω | t < Real.exp ((X ω)^2/K^2)}
      ≤ 1 + ENNReal.ofReal (1/2) := add_le_add hpiece1 hpiece2
    _ ≤ 2 := by
        rw [show (1:ℝ≥0∞) = ENNReal.ofReal 1 by norm_num,
          show (2:ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
          ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
        apply ENNReal.ofReal_le_ofReal
        norm_num

/-- Elementary pointwise inequality used for (iii)⇒(ii): `u^a ≤ (a/e)^a e^u` for
`u ≥ 0`, `a > 0` (a consequence of `ln v ≤ v − 1`).

**Lean implementation helper.** -/
lemma rpow_le_exp_of_pos {u a : ℝ} (hu : 0 ≤ u) (ha : 0 < a) :
    u ^ a ≤ (a / Real.exp 1) ^ a * Real.exp u := by
  rcases eq_or_lt_of_le hu with rfl | hu0
  · rw [Real.zero_rpow ha.ne']
    positivity
  · have hlog : Real.log (u/a) ≤ u/a - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have h1 : a * Real.log u ≤ a * Real.log a - a + u := by
      rw [Real.log_div hu0.ne' ha.ne'] at hlog
      have h2 := mul_le_mul_of_nonneg_left hlog ha.le
      have h3 : a * (u/a - 1) = u - a := by
        field_simp
      nlinarith [h2, h3]
    calc u ^ a = Real.exp (Real.log u * a) := Real.rpow_def_of_pos hu0 a
      _ ≤ Real.exp ((a * Real.log a - a) + u) := by
          rw [Real.exp_le_exp]
          nlinarith
      _ = (a / Real.exp 1) ^ a * Real.exp u := by
          rw [Real.exp_add]
          congr 1
          rw [Real.rpow_def_of_pos (by positivity),
            Real.log_div ha.ne' (Real.exp_ne_zero 1), Real.log_exp]
          ring_nf

/-- With `K₂ = K₃` (equivalent elementary
alternative to the source's Gamma-function computation; see the proof audit):
`𝔼|X|^p ≤ (K√p)^p` for all `p ≥ 1`.

**Book Proposition 2.6.1.** -/
theorem subgaussian_iii_to_ii [IsProbabilityMeasure μ] {X : Ω → ℝ} {K : ℝ}
    (hK : 0 < K) (h : psi2MGF X μ K ≤ 2) {p : ℝ} (hp : 1 ≤ p) :
    ∫⁻ ω, ENNReal.ofReal (|X ω|^p) ∂μ
      ≤ ENNReal.ofReal ((K * Real.sqrt p)^p) := by
  have hp0 : 0 < p := lt_of_lt_of_le one_pos hp
  set C : ℝ := K^p * (p/(2*Real.exp 1))^(p/2) with hC
  have hCpos : 0 < C := by positivity
  have hptw : ∀ ω, |X ω|^p ≤ C * Real.exp ((X ω)^2/K^2) := by
    intro ω
    have h1 : |X ω|^p = K^p * ((X ω)^2/K^2)^(p/2) := by
      have h2 : ((X ω)^2/K^2)^(p/2) = (|X ω|/K)^p := by
        rw [show (X ω)^2/K^2 = (|X ω|/K)^2 by
          rw [div_pow, sq_abs]]
        rw [← Real.rpow_natCast (|X ω|/K) 2, ← Real.rpow_mul (by positivity)]
        congr 1
        push_cast
        ring
      rw [h2, Real.div_rpow (abs_nonneg _) hK.le]
      field_simp
    rw [h1, hC]
    have h3 := rpow_le_exp_of_pos (u := (X ω)^2/K^2) (by positivity)
      (show (0:ℝ) < p/2 by positivity)
    calc K^p * ((X ω)^2/K^2)^(p/2)
        ≤ K^p * ((p/2 / Real.exp 1)^(p/2) * Real.exp ((X ω)^2/K^2)) := by
          exact mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = K^p * (p/(2*Real.exp 1))^(p/2) * Real.exp ((X ω)^2/K^2) := by
          rw [show p/2/Real.exp 1 = p/(2*Real.exp 1) by
            rw [div_div]]
          ring
  calc ∫⁻ ω, ENNReal.ofReal (|X ω|^p) ∂μ
      ≤ ∫⁻ ω, ENNReal.ofReal C * ENNReal.ofReal (Real.exp ((X ω)^2/K^2)) ∂μ := by
        refine lintegral_mono fun ω => ?_
        rw [← ENNReal.ofReal_mul hCpos.le]
        exact ENNReal.ofReal_le_ofReal (hptw ω)
    _ = ENNReal.ofReal C * psi2MGF X μ K := lintegral_const_mul' _ _
        ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal C * 2 := by
        exact mul_le_mul_right h _
    _ ≤ ENNReal.ofReal ((K * Real.sqrt p)^p) := by
        rw [show (2:ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
          ← ENNReal.ofReal_mul hCpos.le]
        apply ENNReal.ofReal_le_ofReal
        -- `C * 2 ≤ (K√p)^p ⟺ 2 ≤ (2e)^{p/2}`, and `(2e)^{p/2} ≥ (2e)^{1/2} ≥ 2`
        have hsqrtp : (K * Real.sqrt p)^p = K^p * p^(p/2) := by
          rw [Real.mul_rpow hK.le (Real.sqrt_nonneg p)]
          congr 1
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hp0.le]
          congr 1
          ring
        rw [hsqrtp]
        have h2e : (2:ℝ) ≤ (2*Real.exp 1)^((1:ℝ)/2) := by
          have h4 : (4:ℝ) ≤ 2*Real.exp 1 := by
            have := Real.add_one_le_exp 1
            linarith
          have h5 : ((4:ℝ))^((1:ℝ)/2) ≤ (2*Real.exp 1)^((1:ℝ)/2) :=
            Real.rpow_le_rpow (by norm_num) h4 (by norm_num)
          have h6 : ((4:ℝ))^((1:ℝ)/2) = 2 := by
            rw [show (4:ℝ) = 2^(2:ℕ) by norm_num, ← Real.rpow_natCast 2 2,
              ← Real.rpow_mul (by norm_num)]
            norm_num
          linarith
        have h2e' : (2:ℝ) ≤ (2*Real.exp 1)^(p/2) := by
          refine h2e.trans (Real.rpow_le_rpow_of_exponent_le ?_ (by linarith))
          have := Real.add_one_le_exp 1
          linarith
        have hBpos : (0:ℝ) < (2*Real.exp 1)^(p/2) := by positivity
        have hCeq : C = K^p * p^(p/2) / (2*Real.exp 1)^(p/2) := by
          rw [hC, Real.div_rpow hp0.le (by positivity)]
          field_simp
        rw [hCeq, div_mul_eq_mul_div, div_le_iff₀ hBpos]
        calc K^p * p^(p/2) * 2
            ≤ K^p * p^(p/2) * (2*Real.exp 1)^(p/2) :=
              mul_le_mul_of_nonneg_left h2e' (by positivity)
          _ = K^p * p^(p/2) * (2*Real.exp 1)^(p/2) := rfl

/-- Bochner/`lpNormRV` corollary of (iii)⇒(ii): the moment bound of the source
Proposition 2.6.6(ii) with the explicit constant `C = 1` relative to the parameter
`K` of (iii): `‖X‖_{L^p} ≤ K√p`.

**Book Proposition 2.6.6(ii).** -/
theorem lpNormRV_le_of_psi2MGF [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXm : AEMeasurable X μ) {K : ℝ} (hK : 0 < K) (h : psi2MGF X μ K ≤ 2)
    {p : ℝ} (hp : 1 ≤ p) :
    Chapter1.lpNormRV X p μ ≤ K * Real.sqrt p := by
  have hp0 : 0 < p := lt_of_lt_of_le one_pos hp
  have hlin := subgaussian_iii_to_ii (μ := μ) hK h hp
  have hmeas : AEStronglyMeasurable (fun ω => |X ω|^p) μ := by
    have h1 : AEStronglyMeasurable (fun ω => |X ω|) μ := by
      simpa [Real.norm_eq_abs] using hXm.aestronglyMeasurable.norm
    exact (Real.continuous_rpow_const hp0.le).comp_aestronglyMeasurable h1
  have hint : ∫ ω, |X ω|^p ∂μ ≤ (K * Real.sqrt p)^p := by
    rw [integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (abs_nonneg _) p) hmeas]
    calc (∫⁻ ω, ENNReal.ofReal (|X ω|^p) ∂μ).toReal
        ≤ (ENNReal.ofReal ((K * Real.sqrt p)^p)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hlin
      _ = (K * Real.sqrt p)^p := ENNReal.toReal_ofReal (by positivity)
  rw [Chapter1.lpNormRV]
  calc (∫ ω, |X ω|^p ∂μ) ^ (1/p)
      ≤ ((K * Real.sqrt p)^p) ^ (1/p) := by
        apply Real.rpow_le_rpow _ hint (by positivity)
        exact integral_nonneg fun ω => Real.rpow_nonneg (abs_nonneg _) p
    _ = K * Real.sqrt p := by
        rw [← Real.rpow_mul (by positivity), mul_one_div, div_self hp0.ne',
          Real.rpow_one]

/-- With `K₃ = 2√e·K₂` (the source's Taylor
series argument; the source's constants are reproduced exactly).

**Book Proposition 2.6.1.** -/
theorem subgaussian_ii_to_iii [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXm : AEMeasurable X μ) {K₂ : ℝ} (hK₂ : 0 < K₂)
    (h : ∀ p : ℝ, 1 ≤ p → ∫⁻ ω, ENNReal.ofReal (|X ω|^p) ∂μ
      ≤ ENNReal.ofReal ((K₂ * Real.sqrt p)^p)) :
    psi2MGF X μ (2 * Real.sqrt (Real.exp 1) * K₂) ≤ 2 := by
  set K : ℝ := 2 * Real.sqrt (Real.exp 1) * K₂ with hKdef
  have hK : 0 < K := by positivity
  have hKsq : K^2 = 4 * Real.exp 1 * K₂^2 := by
    rw [hKdef]
    rw [mul_pow, mul_pow, Real.sq_sqrt (Real.exp_pos 1).le]
    ring
  -- expand the exponential into its Taylor series, term by term
  have hexp_series : ∀ y : ℝ, 0 ≤ y →
      ENNReal.ofReal (Real.exp y) = ∑' n : ℕ, ENNReal.ofReal (y^n / n !) := by
    intro y hy
    rw [show Real.exp y = ∑' n : ℕ, y^n / n ! from
      congrFun (Real.exp_eq_exp_ℝ.trans NormedSpace.exp_eq_tsum_div) y]
    exact ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
      (Real.summable_pow_div_factorial y)
  unfold psi2MGF
  have hrw : ∀ ω, ENNReal.ofReal (Real.exp ((X ω)^2/K^2))
      = ∑' n : ℕ, ENNReal.ofReal (((X ω)^2/K^2)^n / n !) :=
    fun ω => hexp_series _ (by positivity)
  rw [lintegral_congr hrw, lintegral_tsum (fun n =>
    ((((hXm.pow_const 2).div_const _).pow_const n).div_const _).ennreal_ofReal)]
  -- bound the `n`-th term by `2⁻ⁿ`
  have hterm : ∀ n : ℕ,
      ∫⁻ ω, ENNReal.ofReal (((X ω)^2/K^2)^n / n !) ∂μ
        ≤ ENNReal.ofReal ((1/2)^n) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    -- `((X)²/K²)ⁿ/n! = |X|^{2n}/(K^{2n} n!)`
    have hrw2 : ∀ ω, ((X ω)^2/K^2)^n / n !
        = |X ω|^((2*n : ℕ) : ℝ) * (1/(K^(2*n) * n !)) := by
      intro ω
      rw [Real.rpow_natCast]
      rw [div_pow, pow_mul, sq_abs]
      field_simp
      ring_nf
    have h1 : ∫⁻ ω, ENNReal.ofReal (((X ω)^2/K^2)^n / n !) ∂μ
        = ENNReal.ofReal (1/(K^(2*n) * n !))
          * ∫⁻ ω, ENNReal.ofReal (|X ω|^((2*n : ℕ) : ℝ)) ∂μ := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_congr fun ω => ?_
      rw [← ENNReal.ofReal_mul (by positivity), hrw2 ω]
      ring_nf
    rw [h1]
    have h2n1 : (1:ℝ) ≤ ((2*n : ℕ) : ℝ) := by
      push_cast
      have : (1:ℕ) ≤ n := hn
      exact_mod_cast by omega
    have h2 := h ((2*n : ℕ) : ℝ) h2n1
    calc ENNReal.ofReal (1/(K^(2*n) * n !))
          * ∫⁻ ω, ENNReal.ofReal (|X ω|^((2*n : ℕ) : ℝ)) ∂μ
        ≤ ENNReal.ofReal (1/(K^(2*n) * n !))
          * ENNReal.ofReal ((K₂ * Real.sqrt ((2*n : ℕ) : ℝ))^((2*n : ℕ) : ℝ)) :=
          mul_le_mul_right h2 _
      _ ≤ ENNReal.ofReal ((1/2)^n) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          -- numeric core: `(K₂√(2n))^{2n} / (K^{2n} n!) ≤ 2⁻ⁿ`
          have hsq : (K₂ * Real.sqrt ((2*n : ℕ) : ℝ))^((2*n : ℕ) : ℝ)
              = K₂^(2*n) * (2*(n:ℝ))^n := by
            rw [Real.rpow_natCast, mul_pow]
            congr 1
            rw [pow_mul, Real.sq_sqrt (by positivity : (0:ℝ) ≤ ((2*n : ℕ) : ℝ))]
            congr 1
            push_cast
            ring_nf
          rw [hsq]
          have hfact : ((n:ℝ)/Real.exp 1)^n ≤ (n ! : ℝ) :=
            Chapter1.factorial_lower_bound n
          have hK2n : K^(2*n) = (4*Real.exp 1*K₂^2)^n := by
            rw [pow_mul, hKsq]
          rw [hK2n, one_div, inv_mul_le_iff₀ (by positivity)]
          have hid : (2*(n:ℝ))^n = (2*Real.exp 1)^n * ((n:ℝ)/Real.exp 1)^n := by
            rw [← mul_pow]
            congr 1
            field_simp
          rw [hid]
          calc K₂^(2*n) * ((2*Real.exp 1)^n * ((n:ℝ)/Real.exp 1)^n)
              ≤ K₂^(2*n) * ((2*Real.exp 1)^n * (n ! : ℝ)) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                exact mul_le_mul_of_nonneg_left hfact (by positivity)
            _ = (4*Real.exp 1*K₂^2)^n * ↑n ! * (1/2)^n := by
                have hpow : (K₂^2)^n * (2*Real.exp 1)^n
                    = (4*Real.exp 1*K₂^2)^n * (1/2)^n := by
                  rw [← mul_pow, ← mul_pow]
                  congr 1
                  ring
                calc K₂^(2*n) * ((2*Real.exp 1)^n * ↑n !)
                    = ((K₂^2)^n * (2*Real.exp 1)^n) * ↑n ! := by
                      rw [pow_mul]
                      ring
                  _ = ((4*Real.exp 1*K₂^2)^n * (1/2)^n) * ↑n ! := by rw [hpow]
                  _ = (4*Real.exp 1*K₂^2)^n * ↑n ! * (1/2)^n := by ring
  calc ∑' n : ℕ, ∫⁻ ω, ENNReal.ofReal (((X ω)^2/K^2)^n / n !) ∂μ
      ≤ ∑' n : ℕ, ENNReal.ofReal ((1/2)^n) := ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (∑' n : ℕ, (1/2)^n) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
          (summable_geometric_of_lt_one (by norm_num) (by norm_num))).symm
    _ = 2 := by
        rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
        norm_num

/-! ## (iii)⇒(iv) and (iv)⇒(i) -/

/-- Elementary inequality `u ≤ e^{u/2}` for `u ≥ 0` (the source's step "`x² ≤ e^{x²/2}`"
in the proof of (iii)⇒(iv)); via `(√u − 2)² ≥ 0`.

**Lean implementation helper.** -/
lemma self_le_exp_half {u : ℝ} (hu : 0 ≤ u) : u ≤ Real.exp (u/2) := by
  rcases eq_or_lt_of_le hu with rfl | hu0
  · positivity
  · have hs0 : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu0
    have h1 : Real.log (Real.sqrt u) ≤ Real.sqrt u - 1 :=
      Real.log_le_sub_one_of_pos hs0
    have h2 : Real.log u ≤ u/2 := by
      have h3 : Real.log u = 2 * (Real.log u / 2) := by ring
      rw [h3, ← Real.log_sqrt hu]
      nlinarith [sq_nonneg (Real.sqrt u - 2), Real.sq_sqrt hu]
    calc u = Real.exp (Real.log u) := (Real.exp_log hu0).symm
      _ ≤ Real.exp (u/2) := Real.exp_le_exp.mpr h2

/-- Elementary inequality `|x| ≤ K·e^{x²/K²}` for `K > 0` (implicit integrability step
of the source's proof of (iii)⇒(iv): a subgaussian variable is integrable).

**Lean implementation helper.** -/
lemma abs_le_mul_exp_sq_div {x K : ℝ} (hK : 0 < K) :
    |x| ≤ K * Real.exp (x^2/K^2) := by
  rcases le_or_gt (|x|/K) 1 with h | h
  · have h1 : |x| ≤ K := by
      rw [div_le_one hK] at h
      exact h
    calc |x| ≤ K := h1
      _ = K * 1 := (mul_one K).symm
      _ ≤ K * Real.exp (x^2/K^2) := by
          exact mul_le_mul_of_nonneg_left (Real.one_le_exp (by positivity)) hK.le
  · have h2 : |x|/K ≤ (|x|/K)^2 := by nlinarith
    have h3 : (|x|/K)^2 = x^2/K^2 := by
      rw [div_pow, sq_abs]
    have h4 : x^2/K^2 ≤ Real.exp (x^2/K^2) := by
      have := Real.add_one_le_exp (x^2/K^2)
      linarith
    calc |x| = K * (|x|/K) := by field_simp
      _ ≤ K * Real.exp (x^2/K^2) := by
          refine mul_le_mul_of_nonneg_left ?_ hK.le
          calc |x|/K ≤ (|x|/K)^2 := h2
            _ = x^2/K^2 := h3
            _ ≤ Real.exp (x^2/K^2) := h4

/-- With `K₄ = √(3/2)·K₃`, for mean-zero `X`
(the source's Taylor–Lagrange argument, reproduced with the source's constant
`e^{3λ²/2}` in normalized form): `𝔼 e^{λX} ≤ exp((3/2)K₃²λ²)`.

**Book Proposition 2.6.1.** -/
theorem subgaussian_iii_to_iv [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXm : AEMeasurable X μ) {K : ℝ} (hK : 0 < K) (h : psi2MGF X μ K ≤ 2)
    (hmean : ∫ ω, X ω ∂μ = 0) (lam : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * X ω)) ∂μ
      ≤ ENNReal.ofReal (Real.exp ((3/2) * K^2 * lam^2)) := by
  obtain ⟨hEint, hEle⟩ := integrable_exp_sq_div hXm h
  set C : ℝ := lam^2*K^2/2 * Real.exp (lam^2*K^2/2) with hC
  have hC0 : 0 ≤ C := by positivity
  -- pointwise: `e^{λx} ≤ 1 + λx + C e^{x²/K²}`
  have hptw : ∀ ω, Real.exp (lam * X ω)
      ≤ 1 + lam * X ω + C * Real.exp ((X ω)^2/K^2) := by
    intro ω
    have hA := HDP.exp_le_one_add_add_sq_exp_abs (lam * X ω)
    have hB : (lam * X ω)^2/2 * Real.exp |lam * X ω|
        ≤ C * Real.exp ((X ω)^2/K^2) := by
      -- `x² ≤ K² e^{x²/(2K²)}`
      have h1 : (X ω)^2 ≤ K^2 * Real.exp ((X ω)^2/(2*K^2)) := by
        have h1' := self_le_exp_half (u := (X ω)^2/K^2) (by positivity)
        calc (X ω)^2 = K^2 * ((X ω)^2/K^2) := by field_simp
          _ ≤ K^2 * Real.exp ((X ω)^2/K^2/2) :=
              mul_le_mul_of_nonneg_left h1' (by positivity)
          _ = K^2 * Real.exp ((X ω)^2/(2*K^2)) := by
              rw [div_div, mul_comm (K^2) (2:ℝ)]
      -- `|λx| ≤ λ²K²/2 + x²/(2K²)`
      have h2K : (0:ℝ) < 2*K^2 := by positivity
      have h2 : |lam * X ω| ≤ lam^2*K^2/2 + (X ω)^2/(2*K^2) := by
        rw [abs_mul]
        calc |lam| * |X ω| ≤ (lam^2*K^4 + (X ω)^2)/(2*K^2) := by
              rw [le_div_iff₀ h2K, ← sq_abs lam, ← sq_abs (X ω)]
              nlinarith [sq_nonneg (|lam| * K^2 - |X ω|)]
          _ = lam^2*K^2/2 + (X ω)^2/(2*K^2) := by
              field_simp
      have h3 : Real.exp |lam * X ω|
          ≤ Real.exp (lam^2*K^2/2) * Real.exp ((X ω)^2/(2*K^2)) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr h2
      have hx2 : (lam * X ω)^2/2 = lam^2/2 * (X ω)^2 := by
        rw [mul_pow]
        ring
      calc (lam * X ω)^2/2 * Real.exp |lam * X ω|
          = lam^2/2 * (X ω)^2 * Real.exp |lam * X ω| := by rw [hx2]
        _ ≤ lam^2/2 * (K^2 * Real.exp ((X ω)^2/(2*K^2)))
              * (Real.exp (lam^2*K^2/2) * Real.exp ((X ω)^2/(2*K^2))) := by
            apply mul_le_mul _ h3 (Real.exp_pos _).le (by positivity)
            exact mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = C * (Real.exp ((X ω)^2/(2*K^2)) * Real.exp ((X ω)^2/(2*K^2))) := by
            rw [hC]
            ring
        _ = C * Real.exp ((X ω)^2/K^2) := by
            rw [← Real.exp_add]
            congr 1
            field_simp
            ring_nf
    linarith [hA, hB]
  -- integrability
  have hXint : Integrable X μ := by
    refine (hEint.const_mul K).mono' hXm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    exact abs_le_mul_exp_sq_div hK
  have hg_int : Integrable (fun ω => 1 + lam * X ω + C * Real.exp ((X ω)^2/K^2)) μ :=
    ((integrable_const 1).add (hXint.const_mul lam)).add (hEint.const_mul C)
  have hexp_int : Integrable (fun ω => Real.exp (lam * X ω)) μ := by
    refine hg_int.mono'
      (measurable_exp.comp_aemeasurable (hXm.const_mul lam)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hptw ω
  -- take expectations
  have hint : ∫ ω, Real.exp (lam * X ω) ∂μ ≤ Real.exp ((3/2) * K^2 * lam^2) := by
    calc ∫ ω, Real.exp (lam * X ω) ∂μ
        ≤ ∫ ω, (1 + lam * X ω + C * Real.exp ((X ω)^2/K^2)) ∂μ :=
          integral_mono hexp_int hg_int hptw
      _ = 1 + lam * (∫ ω, X ω ∂μ) + C * ∫ ω, Real.exp ((X ω)^2/K^2) ∂μ := by
          have hi1 : Integrable (fun ω => 1 + lam * X ω) μ :=
            (integrable_const 1).add (hXint.const_mul lam)
          have hi2 : Integrable (fun ω => C * Real.exp ((X ω)^2/K^2)) μ :=
            hEint.const_mul C
          rw [integral_add hi1 hi2,
            integral_add (integrable_const 1) (hXint.const_mul lam),
            integral_const, integral_const_mul, integral_const_mul]
          simp
      _ = 1 + C * ∫ ω, Real.exp ((X ω)^2/K^2) ∂μ := by
          rw [hmean]
          ring
      _ ≤ 1 + C * 2 := by nlinarith [hEle, hC0]
      _ ≤ Real.exp ((3/2) * K^2 * lam^2) := by
          rw [hC]
          have e1 : (1:ℝ) ≤ Real.exp (lam^2*K^2/2) := Real.one_le_exp (by positivity)
          have e2 : 1 + lam^2*K^2 ≤ Real.exp (lam^2*K^2) := by
            have := Real.add_one_le_exp (lam^2*K^2)
            linarith
          have e3 : Real.exp (lam^2*K^2) * Real.exp (lam^2*K^2/2)
              = Real.exp ((3/2)*K^2*lam^2) := by
            rw [← Real.exp_add]
            congr 1
            ring
          have e4 : (0:ℝ) ≤ lam^2*K^2 := by positivity
          calc 1 + lam^2*K^2/2*Real.exp (lam^2*K^2/2) * 2
              = 1 + lam^2*K^2 * Real.exp (lam^2*K^2/2) := by ring
            _ ≤ Real.exp (lam^2*K^2/2) + lam^2*K^2*Real.exp (lam^2*K^2/2) := by
                linarith
            _ = (1 + lam^2*K^2) * Real.exp (lam^2*K^2/2) := by ring
            _ ≤ Real.exp (lam^2*K^2) * Real.exp (lam^2*K^2/2) :=
                mul_le_mul_of_nonneg_right e2 (Real.exp_pos _).le
            _ = Real.exp ((3/2)*K^2*lam^2) := e3
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * X ω)) ∂μ
      = ENNReal.ofReal (∫ ω, Real.exp (lam * X ω) ∂μ) :=
        (ofReal_integral_eq_lintegral_ofReal hexp_int
          (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le)).symm
    _ ≤ ENNReal.ofReal (Real.exp ((3/2) * K^2 * lam^2)) :=
        ENNReal.ofReal_le_ofReal hint

/-- Lean implementation helper (the Chernoff step of (iv)⇒(i), in `∫⁻` form):
a one-sided tail bound from an exponential-moment bound.

**Lean implementation helper.** -/
lemma meas_ge_le_of_exp_bound [IsProbabilityMeasure μ] {Y : Ω → ℝ}
    (hYm : AEMeasurable Y μ) {lam t B : ℝ} (hlam : 0 ≤ lam)
    (h : ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * Y ω)) ∂μ ≤ ENNReal.ofReal B) :
    μ {ω | t ≤ Y ω} ≤ ENNReal.ofReal (Real.exp (-(lam * t)) * B) := by
  set c : ℝ≥0∞ := ENNReal.ofReal (Real.exp (lam * t)) with hc
  have hc0 : c ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hctop : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hf : AEMeasurable (fun ω => ENNReal.ofReal (Real.exp (lam * Y ω))) μ :=
    (measurable_exp.comp_aemeasurable (hYm.const_mul lam)).ennreal_ofReal
  have hsub : {ω | t ≤ Y ω}
      ⊆ {ω | c ≤ ENNReal.ofReal (Real.exp (lam * Y ω))} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    rw [hc]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left hω hlam))
  calc μ {ω | t ≤ Y ω}
      ≤ μ {ω | c ≤ ENNReal.ofReal (Real.exp (lam * Y ω))} := measure_mono hsub
    _ ≤ (∫⁻ ω, ENNReal.ofReal (Real.exp (lam * Y ω)) ∂μ) / c :=
        meas_ge_le_lintegral_div hf hc0 hctop
    _ ≤ ENNReal.ofReal B / c := by
        gcongr
    _ = ENNReal.ofReal (Real.exp (-(lam * t)) * B) := by
        rw [hc, ENNReal.div_eq_inv_mul,
          ← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← Real.exp_neg,
          ← ENNReal.ofReal_mul (Real.exp_pos _).le]

/-- With `K₁ = 2K₄` (the source's exponential
moment method with `λ = t/(2K₄²)`, both tails, union bound).

**Book Proposition 2.6.1.** -/
theorem subgaussian_iv_to_i [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXm : AEMeasurable X μ) {K₄ : ℝ} (hK : 0 < K₄)
    (h : ∀ lam : ℝ, ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * X ω)) ∂μ
      ≤ ENNReal.ofReal (Real.exp (K₄^2 * lam^2)))
    {t : ℝ} (ht : 0 ≤ t) :
    μ {ω | t ≤ |X ω|} ≤ ENNReal.ofReal (2 * Real.exp (-t^2/(2*K₄)^2)) := by
  set lam : ℝ := t/(2*K₄^2) with hlam
  have hlam0 : 0 ≤ lam := by positivity
  have hval : Real.exp (-(lam * t)) * Real.exp (K₄^2 * lam^2)
      = Real.exp (-t^2/(2*K₄)^2) := by
    rw [← Real.exp_add]
    congr 1
    rw [hlam]
    field_simp
    ring
  -- right tail
  have hright : μ {ω | t ≤ X ω} ≤ ENNReal.ofReal (Real.exp (-t^2/(2*K₄)^2)) := by
    have := meas_ge_le_of_exp_bound (t := t) hXm hlam0 (h lam)
    rwa [hval] at this
  -- left tail (apply the bound to `−X` via `λ ↦ −λ`)
  have hleft : μ {ω | t ≤ -X ω} ≤ ENNReal.ofReal (Real.exp (-t^2/(2*K₄)^2)) := by
    have hbound : ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * (-X ω))) ∂μ
        ≤ ENNReal.ofReal (Real.exp (K₄^2 * lam^2)) := by
      have h' := h (-lam)
      have hcong : ∀ ω, Real.exp ((-lam) * X ω) = Real.exp (lam * (-X ω)) := by
        intro ω
        congr 1
        ring
      calc ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * (-X ω))) ∂μ
          = ∫⁻ ω, ENNReal.ofReal (Real.exp ((-lam) * X ω)) ∂μ :=
            lintegral_congr fun ω => by rw [hcong ω]
        _ ≤ ENNReal.ofReal (Real.exp (K₄^2 * (-lam)^2)) := h'
        _ = ENNReal.ofReal (Real.exp (K₄^2 * lam^2)) := by
            congr 3
            ring
    have := meas_ge_le_of_exp_bound (t := t) hXm.neg hlam0 hbound
    rwa [hval] at this
  -- union
  have hsub : {ω | t ≤ |X ω|} ⊆ {ω | t ≤ X ω} ∪ {ω | t ≤ -X ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, Set.mem_union] at hω ⊢
    rcases abs_cases (X ω) with ⟨he, _⟩ | ⟨he, _⟩
    · exact Or.inl (by linarith [hω, he.symm.le])
    · exact Or.inr (by linarith [hω, he.symm.le])
  calc μ {ω | t ≤ |X ω|}
      ≤ μ ({ω | t ≤ X ω} ∪ {ω | t ≤ -X ω}) := measure_mono hsub
    _ ≤ μ {ω | t ≤ X ω} + μ {ω | t ≤ -X ω} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-t^2/(2*K₄)^2))
        + ENNReal.ofReal (Real.exp (-t^2/(2*K₄)^2)) := add_le_add hright hleft
    _ = ENNReal.ofReal (2 * Real.exp (-t^2/(2*K₄)^2)) := by
        rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
        congr 1
        ring

/-! ## Vanishing of the ψ₂ norm, and Proposition 2.6.6 -/

/-- If `‖X‖_{ψ₂} = 0` then `X = 0` a.s. (needed for the norm axioms of Exercise 2.42
and for the degenerate cases of Proposition 2.6.6). Implicit source claim.

**Book Exercise 2.42.** -/
theorem ae_eq_zero_of_psi2Norm_eq_zero [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXm : AEMeasurable X μ) (h : SubGaussian X μ) (h0 : psi2Norm X μ = 0) :
    X =ᵐ[μ] 0 := by
  have htail : ∀ t : ℝ, 0 < t → μ {ω | t ≤ |X ω|} = 0 := by
    intro t ht
    have hb : ∀ n : ℕ, μ {ω | t ≤ |X ω|}
        ≤ ENNReal.ofReal (2 * Real.exp (-t^2 * ((n:ℝ)+1))) := by
      intro n
      have hKpos : (0:ℝ) < 1/Real.sqrt ((n:ℝ)+1) := by positivity
      have hKn : psi2MGF X μ (1/Real.sqrt ((n:ℝ)+1)) ≤ 2 :=
        psi2MGF_le_two_of_gt h (by rw [h0]; exact hKpos)
      have hbase := subgaussian_iii_to_i hXm hKpos hKn ht.le
      have harg : -t^2/(1/Real.sqrt ((n:ℝ)+1))^2 = -t^2 * ((n:ℝ)+1) := by
        rw [div_pow, one_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ (n:ℝ)+1)]
        rw [div_div_eq_mul_div, div_one]
      rwa [harg] at hbase
    have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (2 * Real.exp (-t^2 * ((n:ℝ)+1))))
        atTop (𝓝 0) := by
      rw [show (0:ℝ≥0∞) = ENNReal.ofReal 0 from by simp]
      apply ENNReal.tendsto_ofReal
      have hinner : Tendsto (fun n : ℕ => -t^2 * ((n:ℝ)+1)) atTop atBot := by
        refine (tendsto_const_mul_atBot_of_neg (by nlinarith : -t^2 < 0)).mpr ?_
        exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
      have := (Real.tendsto_exp_atBot.comp hinner).const_mul (2:ℝ)
      simpa using this
    have hle := ge_of_tendsto hlim (Filter.Eventually.of_forall hb)
    exact nonpos_iff_eq_zero.mp hle
  have hunion : {ω | X ω ≠ 0} ⊆ ⋃ n : ℕ, {ω | 1/((n:ℝ)+1) ≤ |X ω|} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    have habs : 0 < |X ω| := abs_pos.mpr hω
    obtain ⟨n, hn⟩ := exists_nat_gt (1/|X ω|)
    refine Set.mem_iUnion.mpr ⟨n, ?_⟩
    simp only [Set.mem_setOf_eq]
    have hn1 : 1/|X ω| < (n:ℝ)+1 := hn.trans (by linarith)
    rw [div_lt_iff₀ habs] at hn1
    rw [div_le_iff₀ (by positivity : (0:ℝ) < (n:ℝ)+1)]
    nlinarith [hn1]
  have hnull : μ {ω | X ω ≠ 0} = 0 :=
    measure_mono_null hunion (measure_iUnion_null fun n => htail _ (by positivity))
  exact (MeasureTheory.ae_iff).mpr hnull

/-- `𝔼 exp(X²/‖X‖²_{ψ₂}) ≤ 2` — this is the attainment
lemma `psi2MGF_psi2Norm_le_two` above.

**Book Proposition 2.6.6(iii).** -/
theorem SubGaussian.psi2MGF_bound [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXm : AEMeasurable X μ) (h : SubGaussian X μ) :
    psi2MGF X μ (psi2Norm X μ) ≤ 2 :=
  psi2MGF_psi2Norm_le_two hXm h

/-- A subgaussian variable satisfies the Gaussian tail bound with explicit constant `c = 1`:
`ℙ{|X| ≥ t} ≤ 2exp(−t²/‖X‖²_{ψ₂})` for all `t ≥ 0`.

**Book Proposition 2.6.6(i).** -/
theorem SubGaussian.tail_bound [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXm : AEMeasurable X μ) (h : SubGaussian X μ) {t : ℝ} (ht : 0 ≤ t) :
    μ {ω | t ≤ |X ω|} ≤ ENNReal.ofReal (2 * Real.exp (-t^2/(psi2Norm X μ)^2)) := by
  rcases eq_or_lt_of_le (psi2Norm_nonneg X μ) with h0 | h0
  · rw [← h0, show -t^2/(0:ℝ)^2 = 0 from by norm_num, Real.exp_zero, mul_one]
    calc μ {ω | t ≤ |X ω|} ≤ 1 := prob_le_one
      _ ≤ ENNReal.ofReal 2 := by norm_num
  · exact subgaussian_iii_to_i hXm h0 (psi2MGF_psi2Norm_le_two hXm h) ht

/-- The `L^p` norm of a subgaussian variable is at most its ψ₂ norm times `sqrt p`,
with explicit constant `C = 1`:
`‖X‖_{L^p} ≤ ‖X‖_{ψ₂}·√p` for all `p ≥ 1`.

**Book Proposition 2.6.6(ii).** -/
theorem SubGaussian.moment_bound [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXm : AEMeasurable X μ) (h : SubGaussian X μ) {p : ℝ} (hp : 1 ≤ p) :
    Chapter1.lpNormRV X p μ ≤ psi2Norm X μ * Real.sqrt p := by
  have hp0 : 0 < p := lt_of_lt_of_le one_pos hp
  rcases eq_or_lt_of_le (psi2Norm_nonneg X μ) with h0 | h0
  · have hz := ae_eq_zero_of_psi2Norm_eq_zero hXm h h0.symm
    have hzero : Chapter1.lpNormRV X p μ = 0 := by
      rw [Chapter1.lpNormRV]
      rw [integral_congr_ae (g := fun _ => (0:ℝ)) (by
        filter_upwards [hz] with ω hω
        rw [Pi.zero_apply] at hω
        rw [hω, abs_zero, Real.zero_rpow hp0.ne'])]
      rw [integral_zero, Real.zero_rpow (by positivity)]
    rw [hzero, ← h0, zero_mul]
  · exact lpNormRV_le_of_psi2MGF hXm h0 (psi2MGF_psi2Norm_le_two hXm h) hp

/-- A centered subgaussian variable has a quadratic MGF bound with explicit constant
`C = 3/2`: for mean-zero
subgaussian `X`, `𝔼exp(λX) ≤ exp((3/2)λ²‖X‖²_{ψ₂})` for all `λ`.

**Book Proposition 2.6.6(iv).** -/
theorem SubGaussian.mgf_bound [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXm : AEMeasurable X μ) (h : SubGaussian X μ) (hmean : ∫ ω, X ω ∂μ = 0)
    (lam : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * X ω)) ∂μ
      ≤ ENNReal.ofReal (Real.exp ((3/2) * (psi2Norm X μ)^2 * lam^2)) := by
  rcases eq_or_lt_of_le (psi2Norm_nonneg X μ) with h0 | h0
  · have hz := ae_eq_zero_of_psi2Norm_eq_zero hXm h h0.symm
    have h1 : ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * X ω)) ∂μ = 1 := by
      have hcong : (fun ω => ENNReal.ofReal (Real.exp (lam * X ω)))
          =ᵐ[μ] fun _ => (1:ℝ≥0∞) := by
        filter_upwards [hz] with ω hω
        rw [Pi.zero_apply] at hω
        rw [hω, mul_zero, Real.exp_zero, ENNReal.ofReal_one]
      rw [lintegral_congr_ae hcong]
      simp
    rw [h1, ← h0]
    rw [show (3/2) * (0:ℝ)^2 * lam^2 = 0 from by ring, Real.exp_zero,
      ENNReal.ofReal_one]
  · exact subgaussian_iii_to_iv hXm h0 (psi2MGF_psi2Norm_le_two hXm h) hmean lam

/-- "moreover" clause for (i): if the tail bound of property (i)
holds with parameter `K₁`, then `X` is subgaussian with `‖X‖_{ψ₂} ≤ √5·K₁`
(optimality of the ψ₂ norm up to an absolute constant).

**Book Proposition 2.6.6.** -/
theorem psi2Norm_le_of_tail_bound [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXm : AEMeasurable X μ) {K₁ : ℝ} (hK₁ : 0 < K₁)
    (h : ∀ t : ℝ, 0 ≤ t →
      μ {ω | t ≤ |X ω|} ≤ ENNReal.ofReal (2 * Real.exp (-t^2/K₁^2))) :
    SubGaussian X μ ∧ psi2Norm X μ ≤ Real.sqrt 5 * K₁ := by
  have h3 := subgaussian_i_to_iii hXm hK₁ h
  exact ⟨⟨_, by positivity, h3⟩, psi2Norm_le X (by positivity) h3⟩

/-- "moreover" clause for (ii): if the moment bound of property
(ii) holds with parameter `K₂`, then `X` is subgaussian with `‖X‖_{ψ₂} ≤ 2√e·K₂`.

**Book Proposition 2.6.6.** -/
theorem psi2Norm_le_of_moment_bound [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXm : AEMeasurable X μ) {K₂ : ℝ} (hK₂ : 0 < K₂)
    (h : ∀ p : ℝ, 1 ≤ p → ∫⁻ ω, ENNReal.ofReal (|X ω|^p) ∂μ
      ≤ ENNReal.ofReal ((K₂ * Real.sqrt p)^p)) :
    SubGaussian X μ ∧ psi2Norm X μ ≤ 2 * Real.sqrt (Real.exp 1) * K₂ := by
  have h3 := subgaussian_ii_to_iii hXm hK₂ h
  exact ⟨⟨_, by positivity, h3⟩, psi2Norm_le X (by positivity) h3⟩

/-- "moreover" clause for (iv): if the MGF bound of property (iv)
holds with parameter `K₄` (for mean-zero `X`), then `X` is subgaussian with
`‖X‖_{ψ₂} ≤ 2√5·K₄`.

**Book Proposition 2.6.6.** -/
theorem psi2Norm_le_of_mgf_bound [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXm : AEMeasurable X μ) {K₄ : ℝ} (hK : 0 < K₄)
    (h : ∀ lam : ℝ, ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * X ω)) ∂μ
      ≤ ENNReal.ofReal (Real.exp (K₄^2 * lam^2))) :
    SubGaussian X μ ∧ psi2Norm X μ ≤ Real.sqrt 5 * (2 * K₄) := by
  have h1 := fun (t : ℝ) (ht : 0 ≤ t) => subgaussian_iv_to_i hXm hK h ht
  have h1' : ∀ t : ℝ, 0 ≤ t →
      μ {ω | t ≤ |X ω|} ≤ ENNReal.ofReal (2 * Real.exp (-t^2/(2*K₄)^2)) := h1
  have h3 := subgaussian_i_to_iii hXm (by positivity : (0:ℝ) < 2*K₄) h1'
  exact ⟨⟨_, by positivity, h3⟩, psi2Norm_le X (by positivity) h3⟩

end HDP

end Source_06_SubGaussian

/-! ## Material formerly in `07_SubGaussianConstants.lean` -/

section Source_07_SubGaussianConstants

open MeasureTheory ProbabilityTheory Real Filter
open scoped ENNReal NNReal

namespace HDP

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- If `C ≥ 0` and `psi2MGF X μ K ≤ C`, then the `exp_sq_div_of_real_bound` integrand `ω ↦ exp (X ω)² / K²` is integrable and has integral at most `C`.

**Lean implementation helper.** -/
lemma integrable_exp_sq_div_of_real_bound {X : Ω → ℝ}
    (hXm : AEMeasurable X μ) {K C : ℝ} (hC : 0 ≤ C)
    (h : psi2MGF X μ K ≤ ENNReal.ofReal C) :
    Integrable (fun ω => Real.exp ((X ω) ^ 2 / K ^ 2)) μ ∧
      ∫ ω, Real.exp ((X ω) ^ 2 / K ^ 2) ∂μ ≤ C := by
  have hmeas : AEStronglyMeasurable (fun ω => Real.exp ((X ω) ^ 2 / K ^ 2)) μ :=
    (measurable_exp.comp_aemeasurable
      ((hXm.pow_const 2).div_const _)).aestronglyMeasurable
  have hlin : ∫⁻ ω, ‖Real.exp ((X ω) ^ 2 / K ^ 2)‖ₑ ∂μ = psi2MGF X μ K := by
    unfold psi2MGF
    refine lintegral_congr fun ω => ?_
    rw [Real.enorm_eq_ofReal_abs, abs_of_pos (Real.exp_pos _)]
  have hfin : HasFiniteIntegral (fun ω => Real.exp ((X ω) ^ 2 / K ^ 2)) μ := by
    rw [hasFiniteIntegral_iff_enorm, hlin]
    exact lt_of_le_of_lt h ENNReal.ofReal_lt_top
  refine ⟨⟨hmeas, hfin⟩, ?_⟩
  have h1 : ∫ ω, Real.exp ((X ω) ^ 2 / K ^ 2) ∂μ =
      (psi2MGF X μ K).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le) hmeas]
    rfl
  rw [h1]
  calc
    (psi2MGF X μ K).toReal ≤ (ENNReal.ofReal C).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    _ = C := ENNReal.toReal_ofReal hC

/-- Changing the harmless constant in the square-exponential property only rescales
its denominator.

**Book Remark 2.6.3.** -/
theorem psi2MGF_rescale_constant [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXm : AEMeasurable X μ) {K c a : ℝ} (hK : 0 < K) (hc : 1 < c)
    (ha : 1 < a) (h : psi2MGF X μ K ≤ ENNReal.ofReal c) :
    ∃ K' : ℝ, 0 < K' ∧ psi2MGF X μ K' ≤ ENNReal.ofReal a := by
  by_cases hca : c ≤ a
  · refine ⟨K, hK, h.trans (ENNReal.ofReal_le_ofReal hca)⟩
  · have hac : a < c := lt_of_not_ge hca
    let r : ℝ := Real.log a / Real.log c
    have hlogc : 0 < Real.log c := Real.log_pos hc
    have hr0 : 0 < r := div_pos (Real.log_pos ha) hlogc
    have hr1 : r < 1 := (div_lt_one hlogc).mpr
      (Real.strictMonoOn_log (Set.mem_Ioi.mpr (lt_trans zero_lt_one ha))
        (Set.mem_Ioi.mpr (lt_trans zero_lt_one hc)) hac)
    let K' : ℝ := K / Real.sqrt r
    have hsqrtr : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr0
    have hK' : 0 < K' := div_pos hK hsqrtr
    have hK'sq : K' ^ 2 = K ^ 2 / r := by
      change (K / Real.sqrt r) ^ 2 = K ^ 2 / r
      rw [div_pow, Real.sq_sqrt hr0.le]
    let W : Ω → ℝ := fun ω => Real.exp ((X ω) ^ 2 / K ^ 2)
    have hWpos (ω : Ω) : 0 < W ω := Real.exp_pos _
    have hWone (ω : Ω) : 1 ≤ W ω := by
      dsimp [W]
      exact Real.one_le_exp (by positivity)
    obtain ⟨hWint, hWle⟩ :=
      integrable_exp_sq_div_of_real_bound hXm (le_trans zero_lt_one.le hc.le) h
    have hpoint (ω : Ω) :
        Real.exp ((X ω) ^ 2 / K' ^ 2) = (W ω) ^ r := by
      rw [Real.rpow_def_of_pos (hWpos ω), hK'sq]
      dsimp [W]
      rw [Real.log_exp]
      congr 1
      field_simp
    have hWpowMeas : AEStronglyMeasurable (fun ω => (W ω) ^ r) μ :=
      (Real.continuous_rpow_const hr0.le).comp_aestronglyMeasurable
        ((measurable_exp.comp_aemeasurable
          ((hXm.pow_const 2).div_const _)).aestronglyMeasurable)
    have hWpowInt : Integrable (fun ω => (W ω) ^ r) μ := by
      refine hWint.mono' hWpowMeas (Filter.Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg ((hWone ω).trans' zero_le_one) r)]
      exact (Real.rpow_le_rpow_of_exponent_le (hWone ω) hr1.le).trans_eq
        (Real.rpow_one (W ω))
    have hjensen :
        ∫ ω, (W ω) ^ r ∂μ ≤ (∫ ω, W ω ∂μ) ^ r := by
      exact (Real.concaveOn_rpow hr0.le hr1.le).le_map_integral
        (Real.continuous_rpow_const hr0.le).continuousOn isClosed_Ici
        (Filter.Eventually.of_forall fun ω => (hWpos ω).le) hWint hWpowInt
    have hpow : c ^ r = a := by
      change c ^ (Real.log a / Real.log c) = a
      rw [Real.rpow_def_of_pos (lt_trans zero_lt_one hc)]
      have hlogcne : Real.log c ≠ 0 := ne_of_gt hlogc
      rw [show Real.log c * (Real.log a / Real.log c) = Real.log a by field_simp]
      exact Real.exp_log (lt_trans zero_lt_one ha)
    have hreal : ∫ ω, Real.exp ((X ω) ^ 2 / K' ^ 2) ∂μ ≤ a := by
      rw [integral_congr_ae (Filter.Eventually.of_forall hpoint)]
      calc
        ∫ ω, (W ω) ^ r ∂μ ≤ (∫ ω, W ω ∂μ) ^ r := hjensen
        _ ≤ c ^ r := Real.rpow_le_rpow (integral_nonneg fun ω => (hWpos ω).le)
          hWle hr0.le
        _ = a := hpow
    refine ⟨K', hK', ?_⟩
    have hpowInt : Integrable (fun ω => Real.exp ((X ω) ^ 2 / K' ^ 2)) μ :=
      hWpowInt.congr (Filter.Eventually.of_forall fun ω => (hpoint ω).symm)
    have heq : psi2MGF X μ K' =
        ENNReal.ofReal (∫ ω, Real.exp ((X ω) ^ 2 / K' ^ 2) ∂μ) := by
      unfold psi2MGF
      exact (ofReal_integral_eq_lintegral_ofReal hpowInt
        (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le)).symm
    rw [heq]
    exact ENNReal.ofReal_le_ofReal hreal

/-- For property (iii): the defining constant `2` may be
replaced by any fixed `a > 1`.

**Book Remark 2.6.3.** -/
theorem remark_2_6_3_iii [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXm : AEMeasurable X μ) {a : ℝ} (ha : 1 < a) :
    SubGaussian X μ ↔
      ∃ K : ℝ, 0 < K ∧ psi2MGF X μ K ≤ ENNReal.ofReal a := by
  constructor
  · rintro ⟨K, hK, htwo⟩
    exact psi2MGF_rescale_constant (K := K) (c := 2) (a := a)
      hXm hK (by norm_num) ha (by simpa using htwo)
  · rintro ⟨K, hK, haK⟩
    obtain ⟨K', hK', htwo⟩ :=
      psi2MGF_rescale_constant (K := K) (c := a) (a := 2)
        hXm hK ha (by norm_num) haK
    exact ⟨K', hK', by simpa using htwo⟩

/-- Exponentiate-and-Markov with an arbitrary finite square-exponential bound.

**Lean implementation helper.** -/
theorem square_exponential_tail_bound [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXm : AEMeasurable X μ) {K C : ℝ} (hK : 0 < K)
    (h : psi2MGF X μ K ≤ ENNReal.ofReal C) {t : ℝ} (ht : 0 ≤ t) :
    μ {ω | t ≤ |X ω|} ≤ ENNReal.ofReal (C * Real.exp (-t ^ 2 / K ^ 2)) := by
  set z : ℝ≥0∞ := ENNReal.ofReal (Real.exp (t ^ 2 / K ^ 2)) with hz
  have hz0 : z ≠ 0 := by
    rw [hz]
    exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hztop : z ≠ ⊤ := ENNReal.ofReal_ne_top
  have hf : AEMeasurable (fun ω =>
      ENNReal.ofReal (Real.exp ((X ω) ^ 2 / K ^ 2))) μ :=
    (measurable_exp.comp_aemeasurable
      ((hXm.pow_const 2).div_const _)).ennreal_ofReal
  have hsub : {ω | t ≤ |X ω|} ⊆
      {ω | z ≤ ENNReal.ofReal (Real.exp ((X ω) ^ 2 / K ^ 2))} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    rw [hz]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hsq : t ^ 2 ≤ (X ω) ^ 2 := by
      rw [← sq_abs (X ω)]
      nlinarith [abs_nonneg (X ω)]
    gcongr
  calc
    μ {ω | t ≤ |X ω|}
        ≤ μ {ω | z ≤ ENNReal.ofReal (Real.exp ((X ω) ^ 2 / K ^ 2))} :=
      measure_mono hsub
    _ ≤ (∫⁻ ω, ENNReal.ofReal (Real.exp ((X ω) ^ 2 / K ^ 2)) ∂μ) / z :=
      meas_ge_le_lintegral_div hf hz0 hztop
    _ ≤ ENNReal.ofReal C / z := by
      change psi2MGF X μ K / z ≤ ENNReal.ofReal C / z
      gcongr
    _ = ENNReal.ofReal (C * Real.exp (-t ^ 2 / K ^ 2)) := by
      rw [hz, ENNReal.div_eq_inv_mul,
        ← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← Real.exp_neg,
        ← ENNReal.ofReal_mul (Real.exp_pos _).le]
      congr 1
      ring_nf

/-- For property (i): every subgaussian variable admits the
Gaussian-tail formulation with any fixed leading constant `a > 1`.

**Book Remark 2.6.3.** -/
theorem remark_2_6_3_i [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXm : AEMeasurable X μ) (hX : SubGaussian X μ) {a : ℝ} (ha : 1 < a) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 0 ≤ t →
      μ {ω | t ≤ |X ω|} ≤ ENNReal.ofReal (a * Real.exp (-t ^ 2 / K ^ 2)) := by
  obtain ⟨K, hK, hKa⟩ := (remark_2_6_3_iii hXm ha).mp hX
  exact ⟨K, hK, fun _t ht =>
    square_exponential_tail_bound hXm hK hKa ht⟩

end HDP

end Source_07_SubGaussianConstants

/-! ## Material formerly in `08_SubGaussianNorm.lean` -/

section Source_08_SubGaussianNorm

/-
Book Chapter 2, Section 2.6.1: the subgaussian norm is a norm; examples.


exercises 2.23, 2.24, 2.42 (ψ₂ part) from.

Contents:
* the ψ₂ norm axioms (the ψ₂ part of **Exercise 2.42**, load-bearing for
  Book Lemma 2.7.8): vanishing iff `X = 0` a.s., absolute homogeneity, and the
  triangle inequality `‖X+Y‖_{ψ₂} ≤ ‖X‖_{ψ₂} + ‖Y‖_{ψ₂}` (stated in §2.6.1 of the
  narrative for arbitrary, not necessarily independent, `X` and `Y`);
* **Exercise 2.23**: property (iv) of Proposition 2.6.1 forces `𝔼X = 0`;
* **Exercise 2.24** (a) constants (in the `|c|`-corrected form; the source prints
  `c/√(ln 2)` without absolute values — see the source issue report), (b) bounded
  random variables, (c) Rademacher, (d) the exact standard-Gaussian value
  `√(8/3)`, and (e) the exact Bernoulli value.
-/



open MeasureTheory ProbabilityTheory Real Filter
open scoped ENNReal NNReal Topology Pointwise unitInterval

namespace HDP

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-! ## Vanishing -/

/-- If `X = 0` a.s. then the ψ₂ functional is 1 for every `K`.

**Lean implementation helper.** -/
lemma psi2MGF_of_ae_zero [IsProbabilityMeasure μ] {X : Ω → ℝ} (hz : X =ᵐ[μ] 0)
    (K : ℝ) : psi2MGF X μ K = 1 := by
  unfold psi2MGF
  rw [lintegral_congr_ae (g := fun _ => (1:ℝ≥0∞)) (by
    filter_upwards [hz] with ω hω
    rw [Pi.zero_apply] at hω
    rw [hω]
    norm_num)]
  simp

/-- For
subgaussian `X`, `‖X‖_{ψ₂} = 0 ↔ X = 0` a.s. This is used by the book-wide ψ₂
norm interface.

**Book Section 2.3.** -/
theorem psi2Norm_eq_zero_iff [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXm : AEMeasurable X μ) (h : SubGaussian X μ) :
    psi2Norm X μ = 0 ↔ X =ᵐ[μ] 0 := by
  constructor
  · exact ae_eq_zero_of_psi2Norm_eq_zero hXm h
  · intro hz
    have hset : {K : ℝ | 0 < K ∧ psi2MGF X μ K ≤ 2} = Set.Ioi 0 := by
      ext K
      simp only [Set.mem_setOf_eq, Set.mem_Ioi]
      constructor
      · exact fun hK => hK.1
      · intro hK
        exact ⟨hK, by rw [psi2MGF_of_ae_zero hz]; norm_num⟩
    rw [psi2Norm, hset]
    exact csInf_Ioi

/-! ## Homogeneity -/

/-- Rescaling identity for the ψ₂ functional: `𝔼exp((cX)²/(|c|K)²) = 𝔼exp(X²/K²)`.

**Lean implementation helper.** -/
lemma psi2MGF_const_mul {X : Ω → ℝ} {c : ℝ} (hc : c ≠ 0) (K : ℝ) :
    psi2MGF (fun ω => c * X ω) μ (|c| * K) = psi2MGF X μ K := by
  unfold psi2MGF
  refine lintegral_congr fun ω => ?_
  congr 2
  rw [mul_pow, mul_pow, sq_abs]
  rcases eq_or_ne K 0 with rfl | hK
  · norm_num
  · field_simp

/-- `‖cX‖_{ψ₂} = |c|·‖X‖_{ψ₂}`. Used at the source Example 2.7.4:
"`‖aᵢXᵢ‖_{ψ₂} = |aᵢ|·‖Xᵢ‖_{ψ₂}`").

**Book Section 2.3.** -/
theorem psi2Norm_const_mul [IsProbabilityMeasure μ] (X : Ω → ℝ) (c : ℝ) :
    psi2Norm (fun ω => c * X ω) μ = |c| * psi2Norm X μ := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp only [zero_mul, abs_zero]
    have hz : (fun _ : Ω => (0:ℝ)) =ᵐ[μ] 0 :=
      Filter.Eventually.of_forall fun ω => rfl
    have hset : {K : ℝ | 0 < K ∧ psi2MGF (fun _ : Ω => (0:ℝ)) μ K ≤ 2}
        = Set.Ioi 0 := by
      ext K
      simp only [Set.mem_setOf_eq, Set.mem_Ioi]
      exact ⟨fun hK => hK.1, fun hK =>
        ⟨hK, by rw [psi2MGF_of_ae_zero hz]; norm_num⟩⟩
    rw [psi2Norm, hset]
    exact csInf_Ioi
  · have habs : 0 < |c| := abs_pos.mpr hc
    have hset : {K : ℝ | 0 < K ∧ psi2MGF (fun ω => c * X ω) μ K ≤ 2}
        = (fun K => |c| * K) '' {K : ℝ | 0 < K ∧ psi2MGF X μ K ≤ 2} := by
      ext K
      simp only [Set.mem_setOf_eq, Set.mem_image]
      constructor
      · intro ⟨hK, hb⟩
        refine ⟨K/|c|, ⟨by positivity, ?_⟩, by field_simp⟩
        have := psi2MGF_const_mul (μ := μ) (X := X) hc (K/|c|)
        rw [show |c| * (K/|c|) = K from by field_simp] at this
        rwa [this] at hb
      · rintro ⟨K', ⟨hK', hb'⟩, rfl⟩
        refine ⟨by positivity, ?_⟩
        rw [psi2MGF_const_mul hc K']
        exact hb'
    rw [psi2Norm, hset, psi2Norm]
    -- `sInf (|c| • S) = |c| * sInf S`
    rw [show (fun K => |c| * K) '' {K : ℝ | 0 < K ∧ psi2MGF X μ K ≤ 2}
      = |c| • {K : ℝ | 0 < K ∧ psi2MGF X μ K ≤ 2} from by
        rw [← Set.image_smul]
        rfl]
    rw [Real.sInf_smul_of_nonneg (abs_nonneg c)]
    rfl

/-! ## The triangle inequality (Exercise 2.42, ψ₂ part) -/

/-- The core estimate of the ψ₂ triangle inequality (per the hint to Exercise 2.42):
if `𝔼exp(X²/K²) ≤ 2` and `𝔼exp(Y²/L²) ≤ 2` with `K, L > 0`, then
`𝔼exp((X+Y)²/(K+L)²) ≤ 2`, by convexity of `exp` and of the square.

**Book Exercise 2.42.** -/
lemma psi2MGF_add_le {X Y : Ω → ℝ} (hXm : AEMeasurable X μ) (_hYm : AEMeasurable Y μ)
    {K L : ℝ} (hK : 0 < K) (hL : 0 < L)
    (hX : psi2MGF X μ K ≤ 2) (hY : psi2MGF Y μ L ≤ 2) :
    psi2MGF (fun ω => X ω + Y ω) μ (K + L) ≤ 2 := by
  set w₁ : ℝ := K/(K+L) with hw₁
  set w₂ : ℝ := L/(K+L) with hw₂
  have hKL : (0:ℝ) < K + L := by linarith
  have hw₁0 : 0 ≤ w₁ := by positivity
  have hw₂0 : 0 ≤ w₂ := by positivity
  have hwsum : w₁ + w₂ = 1 := by
    rw [hw₁, hw₂]
    field_simp
  -- pointwise: `exp(((x+y)/(K+L))²) ≤ w₁ exp((x/K)²) + w₂ exp((y/L)²)`
  have hptw : ∀ ω, Real.exp ((X ω + Y ω)^2/(K+L)^2)
      ≤ w₁ * Real.exp ((X ω)^2/K^2) + w₂ * Real.exp ((Y ω)^2/L^2) := by
    intro ω
    have hcomb : (X ω + Y ω)/(K+L) = w₁ * (X ω/K) + w₂ * (Y ω/L) := by
      rw [hw₁, hw₂]
      field_simp
    have hsq : ((X ω + Y ω)/(K+L))^2
        ≤ w₁ * (X ω/K)^2 + w₂ * (Y ω/L)^2 := by
      rw [hcomb]
      nlinarith [sq_nonneg (X ω/K - Y ω/L), mul_nonneg hw₁0 hw₂0,
        sq_nonneg (w₁ * (X ω/K) + w₂ * (Y ω/L))]
    have hconv := convexOn_exp.2 (Set.mem_univ ((X ω/K)^2))
      (Set.mem_univ ((Y ω/L)^2)) hw₁0 hw₂0 hwsum
    rw [smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul] at hconv
    calc Real.exp ((X ω + Y ω)^2/(K+L)^2)
        = Real.exp (((X ω + Y ω)/(K+L))^2) := by
          rw [div_pow]
      _ ≤ Real.exp (w₁ * (X ω/K)^2 + w₂ * (Y ω/L)^2) := Real.exp_le_exp.mpr hsq
      _ ≤ w₁ * Real.exp ((X ω/K)^2) + w₂ * Real.exp ((Y ω/L)^2) := hconv
      _ = w₁ * Real.exp ((X ω)^2/K^2) + w₂ * Real.exp ((Y ω)^2/L^2) := by
          rw [div_pow, div_pow]
  -- integrate
  unfold psi2MGF
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp ((X ω + Y ω)^2/(K+L)^2)) ∂μ
      ≤ ∫⁻ ω, (ENNReal.ofReal (w₁ * Real.exp ((X ω)^2/K^2))
          + ENNReal.ofReal (w₂ * Real.exp ((Y ω)^2/L^2))) ∂μ := by
        refine lintegral_mono fun ω => ?_
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        exact ENNReal.ofReal_le_ofReal (hptw ω)
    _ = (∫⁻ ω, ENNReal.ofReal (w₁ * Real.exp ((X ω)^2/K^2)) ∂μ)
        + ∫⁻ ω, ENNReal.ofReal (w₂ * Real.exp ((Y ω)^2/L^2)) ∂μ := by
        refine lintegral_add_left' ?_ _
        exact ((measurable_exp.comp_aemeasurable
          ((hXm.pow_const 2).div_const _)).const_mul w₁).ennreal_ofReal
    _ ≤ ENNReal.ofReal w₁ * 2 + ENNReal.ofReal w₂ * 2 := by
        gcongr
        · calc ∫⁻ ω, ENNReal.ofReal (w₁ * Real.exp ((X ω)^2/K^2)) ∂μ
              = ENNReal.ofReal w₁ * psi2MGF X μ K := by
                unfold psi2MGF
                rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
                refine lintegral_congr fun ω => ?_
                rw [← ENNReal.ofReal_mul hw₁0]
            _ ≤ ENNReal.ofReal w₁ * 2 := mul_le_mul_right hX _
        · calc ∫⁻ ω, ENNReal.ofReal (w₂ * Real.exp ((Y ω)^2/L^2)) ∂μ
              = ENNReal.ofReal w₂ * psi2MGF Y μ L := by
                unfold psi2MGF
                rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
                refine lintegral_congr fun ω => ?_
                rw [← ENNReal.ofReal_mul hw₂0]
            _ ≤ ENNReal.ofReal w₂ * 2 := mul_le_mul_right hY _
    _ = 2 := by
        rw [show (2:ℝ≥0∞) = ENNReal.ofReal 2 from by norm_num,
          ← ENNReal.ofReal_mul hw₁0, ← ENNReal.ofReal_mul hw₂0,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        nlinarith [hwsum]

/-- Stated in
the §2.6.1 narrative:
"any random variables `X` and `Y`, not necessarily independent, satisfy
`‖X+Y‖_{ψ₂} ≤ ‖X‖_{ψ₂} + ‖Y‖_{ψ₂}`"). Explicit source declaration, load-bearing
for the source Lemma 2.7.8 (centering).

**Book Section 2.3.** -/
theorem psi2Norm_add_le [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hXm : AEMeasurable X μ) (hYm : AEMeasurable Y μ)
    (hX : SubGaussian X μ) (hY : SubGaussian Y μ) :
    psi2Norm (fun ω => X ω + Y ω) μ ≤ psi2Norm X μ + psi2Norm Y μ := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hKb : psi2MGF X μ (psi2Norm X μ + ε/2) ≤ 2 :=
    psi2MGF_le_two_of_gt hX (by linarith)
  have hLb : psi2MGF Y μ (psi2Norm Y μ + ε/2) ≤ 2 :=
    psi2MGF_le_two_of_gt hY (by linarith)
  have hKpos : (0:ℝ) < psi2Norm X μ + ε/2 := by
    linarith [psi2Norm_nonneg X μ]
  have hLpos : (0:ℝ) < psi2Norm Y μ + ε/2 := by
    linarith [psi2Norm_nonneg Y μ]
  have hsum := psi2MGF_add_le hXm hYm hKpos hLpos hKb hLb
  have hle := psi2Norm_le (μ := μ) (fun ω => X ω + Y ω)
    (by linarith : (0:ℝ) < (psi2Norm X μ + ε/2) + (psi2Norm Y μ + ε/2)) hsum
  linarith

/-- `X + Y` is subgaussian when `X` and `Y` are (closure property implicit in the
§2.6.1 narrative).

**Book Section 2.6.1.** -/
theorem SubGaussian.add [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hXm : AEMeasurable X μ) (hYm : AEMeasurable Y μ)
    (hX : SubGaussian X μ) (hY : SubGaussian Y μ) :
    SubGaussian (fun ω => X ω + Y ω) μ := by
  obtain ⟨K, hK, hKb⟩ := hX
  obtain ⟨L, hL, hLb⟩ := hY
  exact ⟨K + L, by linarith, psi2MGF_add_le hXm hYm hK hL hKb hLb⟩

/-! ## Exercise 2.24 (a)–(c): examples -/

/-- In
the `|c|`-corrected form
(the source prints `c/√(ln 2)`; see the source issue report):
`‖c‖_{ψ₂} = |c|/√(ln 2)`. Explicit source exercise (load-bearing via Lemma 2.7.8).

**Book Exercise 2.22--2.24.** -/
theorem psi2Norm_const [IsProbabilityMeasure μ] (c : ℝ) :
    psi2Norm (fun _ => c) μ = |c| / Real.sqrt (Real.log 2) := by
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hMGF : ∀ K : ℝ, psi2MGF (fun _ => c) μ K
      = ENNReal.ofReal (Real.exp (c^2/K^2)) := by
    intro K
    unfold psi2MGF
    simp
  rcases eq_or_ne c 0 with rfl | hc
  · simp only [abs_zero, zero_div]
    have hset : {K : ℝ | 0 < K ∧ psi2MGF (fun _ => (0:ℝ)) μ K ≤ 2} = Set.Ioi 0 := by
      ext K
      simp only [Set.mem_setOf_eq, Set.mem_Ioi]
      refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
      rw [hMGF]
      norm_num
    rw [psi2Norm, hset]
    exact csInf_Ioi
  · have hcpos : 0 < |c| := abs_pos.mpr hc
    have hgoalpos : (0:ℝ) < |c| / Real.sqrt (Real.log 2) := by positivity
    have hmem : ∀ K : ℝ, 0 < K →
        (psi2MGF (fun _ => c) μ K ≤ 2 ↔ |c| / Real.sqrt (Real.log 2) ≤ K) := by
      intro K hK
      rw [hMGF]
      rw [show (2:ℝ≥0∞) = ENNReal.ofReal 2 from by norm_num]
      rw [ENNReal.ofReal_le_ofReal_iff (by norm_num)]
      rw [← Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 2)]
      constructor
      · intro h
        -- `c²/K² ≤ ln 2 → |c|/√(ln2) ≤ K`
        rw [div_le_iff₀ (by positivity : (0:ℝ) < K^2)] at h
        rw [div_le_iff₀ (by positivity : (0:ℝ) < Real.sqrt (Real.log 2))]
        nlinarith [Real.sq_sqrt hlog2.le, Real.sqrt_nonneg (Real.log 2),
          sq_abs c, sq_nonneg (Real.sqrt (Real.log 2) * K - |c|),
          mul_pos hK (Real.sqrt_pos.mpr hlog2)]
      · intro h
        rw [div_le_iff₀ (by positivity : (0:ℝ) < Real.sqrt (Real.log 2))] at h
        rw [div_le_iff₀ (by positivity : (0:ℝ) < K^2)]
        nlinarith [Real.sq_sqrt hlog2.le, sq_abs c,
          mul_nonneg (Real.sqrt_nonneg (Real.log 2)) hK.le]
    have hset : {K : ℝ | 0 < K ∧ psi2MGF (fun _ => c) μ K ≤ 2}
        = Set.Ici (|c| / Real.sqrt (Real.log 2)) := by
      ext K
      simp only [Set.mem_setOf_eq, Set.mem_Ici]
      constructor
      · intro ⟨hK, hb⟩
        exact (hmem K hK).mp hb
      · intro hK
        have hKpos : 0 < K := lt_of_lt_of_le hgoalpos hK
        exact ⟨hKpos, (hmem K hKpos).mpr hK⟩
    rw [psi2Norm, hset]
    exact csInf_Ici

/-- If `|X| ≤ M` a.s. then
`‖X‖_{ψ₂} ≤ M/√(ln 2)`. Explicit source exercise (load-bearing via Lemma 2.7.8;
the source states it with `‖X‖_∞`).

**Book Exercise 2.22--2.24.** -/
theorem psi2Norm_le_of_bounded [IsProbabilityMeasure μ] {X : Ω → ℝ} {M : ℝ}
    (hM : 0 < M) (hb : ∀ᵐ ω ∂μ, |X ω| ≤ M) :
    SubGaussian X μ ∧ psi2Norm X μ ≤ M / Real.sqrt (Real.log 2) := by
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hKpos : (0:ℝ) < M / Real.sqrt (Real.log 2) := by positivity
  have hbound : psi2MGF X μ (M / Real.sqrt (Real.log 2)) ≤ 2 := by
    unfold psi2MGF
    calc ∫⁻ ω, ENNReal.ofReal (Real.exp ((X ω)^2/(M/Real.sqrt (Real.log 2))^2)) ∂μ
        ≤ ∫⁻ _ω, ENNReal.ofReal 2 ∂μ := by
          refine lintegral_mono_ae ?_
          filter_upwards [hb] with ω hω
          apply ENNReal.ofReal_le_ofReal
          rw [← Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 2)]
          rw [div_pow, Real.sq_sqrt hlog2.le]
          rw [div_le_iff₀ (by positivity : (0:ℝ) < M^2/Real.log 2)]
          calc (X ω)^2 ≤ M^2 := by
                nlinarith [abs_nonneg (X ω), sq_abs (X ω)]
            _ = Real.log 2 * (M^2/Real.log 2) := by
                field_simp
      _ = 2 := by
          simp
  exact ⟨⟨_, hKpos, hbound⟩, psi2Norm_le X hKpos hbound⟩

/-- A Rademacher random variable satisfies
`‖X‖_{ψ₂} = 1/√(ln 2)`. Explicit source exercise (load-bearing via Example 2.7.4:
"`‖Xᵢ‖_{ψ₂}` is an absolute constant").

**Book Exercise 2.22--2.24.** -/
theorem psi2Norm_rademacher {X : Ω → ℝ} (h : HDP.IsRademacher X μ) :
    psi2Norm X μ = 1 / Real.sqrt (Real.log 2) := by
  have := h.isProbabilityMeasure
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- the ψ₂ functional of a Rademacher variable is exactly `exp(1/K²)`
  have hMGF : ∀ K : ℝ, psi2MGF X μ K = ENNReal.ofReal (Real.exp (1/K^2)) := by
    intro K
    unfold psi2MGF
    have hcong : (fun ω => ENNReal.ofReal (Real.exp ((X ω)^2/K^2)))
        =ᵐ[μ] fun _ => ENNReal.ofReal (Real.exp (1/K^2)) := by
      filter_upwards [h.ae_mem] with ω hω
      rcases hω with hω | hω <;> rw [hω] <;> norm_num
    rw [lintegral_congr_ae hcong]
    simp
  -- so the defining set is `[1/√(ln2), ∞)`, exactly as for the constant `1`
  have hmem : ∀ K : ℝ, 0 < K →
      (psi2MGF X μ K ≤ 2 ↔ 1 / Real.sqrt (Real.log 2) ≤ K) := by
    intro K hK
    rw [hMGF]
    rw [show (2:ℝ≥0∞) = ENNReal.ofReal 2 from by norm_num]
    rw [ENNReal.ofReal_le_ofReal_iff (by norm_num)]
    rw [← Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 2)]
    constructor
    · intro hle
      rw [div_le_iff₀ (by positivity : (0:ℝ) < K^2)] at hle
      rw [div_le_iff₀ (by positivity : (0:ℝ) < Real.sqrt (Real.log 2))]
      nlinarith [Real.sq_sqrt hlog2.le, Real.sqrt_nonneg (Real.log 2),
        sq_nonneg (Real.sqrt (Real.log 2) * K - 1),
        mul_pos hK (Real.sqrt_pos.mpr hlog2)]
    · intro hle
      rw [div_le_iff₀ (by positivity : (0:ℝ) < Real.sqrt (Real.log 2))] at hle
      rw [div_le_iff₀ (by positivity : (0:ℝ) < K^2)]
      nlinarith [Real.sq_sqrt hlog2.le,
        mul_nonneg (Real.sqrt_nonneg (Real.log 2)) hK.le]
  have hset : {K : ℝ | 0 < K ∧ psi2MGF X μ K ≤ 2}
      = Set.Ici (1 / Real.sqrt (Real.log 2)) := by
    ext K
    simp only [Set.mem_setOf_eq, Set.mem_Ici]
    constructor
    · intro ⟨hK, hb⟩
      exact (hmem K hK).mp hb
    · intro hK
      have hKpos : 0 < K := lt_of_lt_of_le (by positivity) hK
      exact ⟨hKpos, (hmem K hKpos).mpr hK⟩
  rw [psi2Norm, hset]
  exact csInf_Ici

/-! ## Exercise 2.24(d)–(e): Gaussian and Bernoulli examples -/

/-- Defines `gaussianPsi2Scale`, the gaussian psi2 scale used in the surrounding construction.

**Lean implementation helper.** -/
private noncomputable def gaussianPsi2Scale : Real := Real.sqrt (8 / 3)

/-- Shows that `gaussianPsi2Scale` is positive.

**Lean implementation helper.** -/
private lemma gaussianPsi2Scale_pos : 0 < gaussianPsi2Scale := by
  rw [gaussianPsi2Scale]
  positivity

/-- At the critical scale, the `ψ₂` modular of a standard Gaussian coordinate has the stated exact value.

**Lean implementation helper.** -/
lemma psi2MGF_id_standardGaussian_at_scale :
    psi2MGF (fun x : Real => x) (gaussianReal 0 1) gaussianPsi2Scale = 2 := by
  unfold psi2MGF
  calc
    (∫⁻ x, ENNReal.ofReal (Real.exp (x ^ 2 / gaussianPsi2Scale ^ 2))
        ∂gaussianReal 0 1) =
        ∫⁻ x, ENNReal.ofReal (Real.exp ((3 / 8 : Real) * x ^ 2))
          ∂gaussianReal 0 1 := by
      refine lintegral_congr fun x => ?_
      congr 2
      rw [gaussianPsi2Scale, Real.sq_sqrt (by norm_num : (0 : Real) ≤ 8 / 3)]
      ring
    _ = 2 := Chapter2.lintegral_exp_three_eighths_sq_standardGaussian

/-- Above the critical scale, the standard Gaussian `ψ₂` modular is finite and below the defining threshold.

**Lean implementation helper.** -/
lemma psi2MGF_id_standardGaussian_gt_two {K : Real} (hK : 0 < K)
    (hKlt : K < gaussianPsi2Scale) :
    2 < psi2MGF (fun x : Real => x) (gaussianReal 0 1) K := by
  let f : Real -> ENNReal := fun x =>
    ENNReal.ofReal (Real.exp (x ^ 2 / gaussianPsi2Scale ^ 2))
  let g : Real -> ENNReal := fun x => ENNReal.ofReal (Real.exp (x ^ 2 / K ^ 2))
  have hgmeas : AEMeasurable g (gaussianReal 0 1) := by
    exact ((measurable_exp.comp
      (measurable_id.pow_const 2 |>.div_const _)).ennreal_ofReal).aemeasurable
  have hfint : (∫⁻ x, f x ∂gaussianReal 0 1) ≠ ∞ := by
    change psi2MGF (fun x : Real => x) (gaussianReal 0 1) gaussianPsi2Scale ≠ ∞
    rw [psi2MGF_id_standardGaussian_at_scale]
    norm_num
  have hle : f ≤ᵐ[gaussianReal 0 1] g := by
    refine Filter.Eventually.of_forall fun x => ?_
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_left (sq_nonneg x) (by positivity) (by nlinarith)
  have hmeasure : (gaussianReal 0 1) ({0}ᶜ) ≠ 0 := by
    letI : NoAtoms (gaussianReal 0 1) := noAtoms_gaussianReal (by norm_num)
    simp
  have hlt : ∀ᵐ x ∂gaussianReal 0 1, x ∈ ({0} : Set Real)ᶜ -> f x < g x := by
    refine Filter.Eventually.of_forall fun x hx => ?_
    apply (ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos _)).2
    apply Real.exp_lt_exp.mpr
    rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hx
    rw [div_lt_div_iff₀ (sq_pos_of_pos gaussianPsi2Scale_pos) (sq_pos_of_pos hK)]
    exact mul_lt_mul_of_pos_left
      ((sq_lt_sq₀ hK.le gaussianPsi2Scale_pos.le).2 hKlt) (sq_pos_of_ne_zero hx)
  have hstrict := lintegral_strict_mono_of_ae_le_of_ae_lt_on hgmeas hfint hle hmeasure hlt
  change psi2MGF (fun x : Real => x) (gaussianReal 0 1) gaussianPsi2Scale <
    psi2MGF (fun x : Real => x) (gaussianReal 0 1) K at hstrict
  rwa [psi2MGF_id_standardGaussian_at_scale] at hstrict

/-- For the canonical Gaussian
measure. This is the authoritative exact `ψ₂` calculation.

**Book Exercise 2.24(d).** -/
theorem psi2Norm_standardGaussian_measure :
    psi2Norm (fun x : Real => x) (gaussianReal 0 1) = Real.sqrt (8 / 3) := by
  have hbase := psi2MGF_id_standardGaussian_at_scale
  have hmem : ∀ K : Real, 0 < K ->
      (psi2MGF (fun x : Real => x) (gaussianReal 0 1) K ≤ 2 ↔
        gaussianPsi2Scale ≤ K) := by
    intro K hK
    constructor
    · intro hb
      by_contra hn
      have hlt : K < gaussianPsi2Scale := lt_of_not_ge hn
      exact (not_lt_of_ge hb) (psi2MGF_id_standardGaussian_gt_two hK hlt)
    · intro hscale
      exact (psi2MGF_anti (μ := gaussianReal 0 1) (fun x : Real => x)
        gaussianPsi2Scale_pos hscale).trans_eq hbase
  have hset : {K : Real | 0 < K ∧
      psi2MGF (fun x : Real => x) (gaussianReal 0 1) K ≤ 2} =
      Set.Ici gaussianPsi2Scale := by
    ext K
    simp only [Set.mem_setOf_eq, Set.mem_Ici]
    constructor
    · intro h
      exact (hmem K h.1).mp h.2
    · intro h
      have hK : 0 < K := gaussianPsi2Scale_pos.trans_le h
      exact ⟨hK, (hmem K hK).mpr h⟩
  rw [psi2Norm, hset, csInf_Ici, gaussianPsi2Scale]

/-- Identifies `psi2MGF` with `of_hasLaw_standardGaussian`.

**Lean implementation helper.** -/
lemma psi2MGF_eq_of_hasLaw_standardGaussian {g : Ω -> Real}
    (hg : HasLaw g (gaussianReal 0 1) μ) (K : Real) :
    psi2MGF g μ K = psi2MGF (fun x : Real => x) (gaussianReal 0 1) K := by
  unfold psi2MGF
  simpa only [id_eq, Function.comp_apply] using hg.lintegral_comp
    ((measurable_exp.comp (measurable_id.pow_const 2 |>.div_const _)).ennreal_ofReal.aemeasurable)

/-- For a
random variable with standard Gaussian law.

**Book Example 2.6.5.** -/
theorem psi2Norm_standardGaussian {g : Ω -> Real}
    (hg : HasLaw g (gaussianReal 0 1) μ) :
    psi2Norm g μ = Real.sqrt (8 / 3) := by
  have hset : {K : Real | 0 < K ∧ psi2MGF g μ K ≤ 2} =
      {K : Real | 0 < K ∧
        psi2MGF (fun x : Real => x) (gaussianReal 0 1) K ≤ 2} := by
    ext K
    simp only [Set.mem_setOf_eq]
    rw [psi2MGF_eq_of_hasLaw_standardGaussian hg K]
  calc
    psi2Norm g μ = psi2Norm (fun x : Real => x) (gaussianReal 0 1) := by
      rw [psi2Norm, psi2Norm, hset]
    _ = Real.sqrt (8 / 3) := psi2Norm_standardGaussian_measure

/-- The `ψ₂` modular of a centered Bernoulli variable has the stated elementary exponential expression.

**Lean implementation helper.** -/
lemma psi2MGF_bernoulli {X : Ω -> Real} {p : I}
    (h : HDP.IsBernoulli X p μ) (K : Real) :
    psi2MGF X μ K = ENNReal.ofReal
      (1 + (p : Real) * (Real.exp (1 / K ^ 2) - 1)) := by
  letI : IsProbabilityMeasure μ := h.isProbabilityMeasure
  unfold psi2MGF
  rw [← ofReal_integral_eq_lintegral_ofReal
    (h.integrable_comp (fun x : Real => Real.exp (x ^ 2 / K ^ 2)))
    (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)]
  apply congrArg ENNReal.ofReal
  calc
    (∫ x, Real.exp (X x ^ 2 / K ^ 2) ∂μ) =
        (p : Real) * Real.exp (1 ^ 2 / K ^ 2) +
          (1 - (p : Real)) * Real.exp (0 ^ 2 / K ^ 2) :=
      h.integral_comp (fun x : Real => Real.exp (x ^ 2 / K ^ 2))
    _ = 1 + (p : Real) * (Real.exp (1 / K ^ 2) - 1) := by
      norm_num
      ring

/-- The
exact `ψ₂` norm of a Bernoulli random variable, including `p = 0`.

**Book Exercise 2.22--2.24.** -/
theorem psi2Norm_bernoulli {X : Ω -> Real} {p : I}
    (h : HDP.IsBernoulli X p μ) :
    psi2Norm X μ = 1 / Real.sqrt (Real.log (1 + 1 / (p : Real))) := by
  letI : IsProbabilityMeasure μ := h.isProbabilityMeasure
  have hMGF := psi2MGF_bernoulli h
  by_cases hp0 : (p : Real) = 0
  · have hset : {K : Real | 0 < K ∧ psi2MGF X μ K ≤ 2} = Set.Ioi 0 := by
      ext K
      simp only [Set.mem_setOf_eq, Set.mem_Ioi]
      constructor
      · exact fun hK => hK.1
      · intro hK
        refine ⟨hK, ?_⟩
        rw [hMGF]
        simp [hp0]
    rw [psi2Norm, hset, csInf_Ioi, hp0]
    norm_num
  · have hp : 0 < (p : Real) := lt_of_le_of_ne p.2.1 (Ne.symm hp0)
    have harg : 1 < 1 + 1 / (p : Real) := by
      nlinarith [one_div_pos.mpr hp]
    have hlog : 0 < Real.log (1 + 1 / (p : Real)) := Real.log_pos harg
    have hscale : 0 < 1 / Real.sqrt (Real.log (1 + 1 / (p : Real))) := by
      positivity
    have hmem : ∀ K : Real, 0 < K ->
        (psi2MGF X μ K ≤ 2 ↔
          1 / Real.sqrt (Real.log (1 + 1 / (p : Real))) ≤ K) := by
      intro K hK
      rw [hMGF]
      rw [show (2 : ENNReal) = ENNReal.ofReal 2 by norm_num]
      rw [ENNReal.ofReal_le_ofReal_iff (by norm_num)]
      constructor
      · intro hb
        have hexp : Real.exp (1 / K ^ 2) ≤ 1 + 1 / (p : Real) := by
          have hsub : Real.exp (1 / K ^ 2) - 1 ≤ 1 / (p : Real) := by
            rw [le_div_iff₀ hp]
            nlinarith
          linarith
        have hlelog : 1 / K ^ 2 ≤ Real.log (1 + 1 / (p : Real)) :=
          (Real.le_log_iff_exp_le (by positivity)).2 hexp
        rw [div_le_iff₀ (Real.sqrt_pos.mpr hlog)]
        rw [div_le_iff₀ (sq_pos_of_pos hK)] at hlelog
        apply (sq_le_sq₀ zero_le_one
          (mul_nonneg hK.le (Real.sqrt_nonneg _))).mp
        rw [one_pow, mul_pow, Real.sq_sqrt hlog.le]
        simpa [mul_comm] using hlelog
      · intro hb
        rw [div_le_iff₀ (Real.sqrt_pos.mpr hlog)] at hb
        have hlelog : 1 / K ^ 2 ≤ Real.log (1 + 1 / (p : Real)) := by
          rw [div_le_iff₀ (sq_pos_of_pos hK)]
          have hsquare := (sq_le_sq₀ zero_le_one
            (mul_nonneg hK.le (Real.sqrt_nonneg _))).2 hb
          rw [one_pow, mul_pow, Real.sq_sqrt hlog.le] at hsquare
          simpa [mul_comm] using hsquare
        have hexp : Real.exp (1 / K ^ 2) ≤ 1 + 1 / (p : Real) :=
          (Real.le_log_iff_exp_le (by positivity)).1 hlelog
        have hmul := mul_le_mul_of_nonneg_left hexp hp.le
        field_simp at hmul
        nlinarith
    have hset : {K : Real | 0 < K ∧ psi2MGF X μ K ≤ 2} =
        Set.Ici (1 / Real.sqrt (Real.log (1 + 1 / (p : Real)))) := by
      ext K
      simp only [Set.mem_setOf_eq, Set.mem_Ici]
      constructor
      · intro hK
        exact (hmem K hK.1).mp hK.2
      · intro hK
        have hKpos : 0 < K := hscale.trans_le hK
        exact ⟨hKpos, (hmem K hKpos).mpr hK⟩
    rw [psi2Norm, hset, csInf_Ici]

/-! ## Exercise 2.23: property (iv) forces mean zero -/

/-- If
`𝔼exp(λX) ≤ exp(K₄²λ²)` for all `λ` (property (iv) of Proposition 2.6.1, with `X`
integrable), then `𝔼X = 0`. Explicit source exercise (supports Remark 2.6.2).
Proof per the source hint: Jensen for the exponential gives
`exp(λ𝔼X) ≤ exp(K₄²λ²)`, i.e. `λ𝔼X ≤ K₄²λ²` for all `λ`; let `λ → 0±`.

**Book Remark 2.6.2.** -/
theorem exercise_2_23 [IsProbabilityMeasure μ] {X : Ω → ℝ} {K₄ : ℝ}
    (hXint : Integrable X μ)
    (h : ∀ lam : ℝ, ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * X ω)) ∂μ
      ≤ ENNReal.ofReal (Real.exp (K₄^2 * lam^2))) :
    ∫ ω, X ω ∂μ = 0 := by
  -- Jensen: `exp(λ𝔼X) ≤ 𝔼exp(λX)`; combined with (iv): `λ𝔼X ≤ K₄²λ²`.
  have hkey : ∀ lam : ℝ, lam * (∫ ω, X ω ∂μ) ≤ K₄^2 * lam^2 := by
    intro lam
    -- integrability of `exp(λX)` from the `∫⁻` bound
    have hmeas : AEStronglyMeasurable (fun ω => Real.exp (lam * X ω)) μ :=
      (measurable_exp.comp_aemeasurable
        (hXint.aemeasurable.const_mul lam)).aestronglyMeasurable
    have hint : Integrable (fun ω => Real.exp (lam * X ω)) μ := by
      refine ⟨hmeas, ?_⟩
      rw [hasFiniteIntegral_iff_enorm]
      calc ∫⁻ ω, ‖Real.exp (lam * X ω)‖ₑ ∂μ
          = ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * X ω)) ∂μ := by
            refine lintegral_congr fun ω => ?_
            rw [Real.enorm_eq_ofReal_abs, abs_of_pos (Real.exp_pos _)]
        _ ≤ ENNReal.ofReal (Real.exp (K₄^2 * lam^2)) := h lam
        _ < ⊤ := ENNReal.ofReal_lt_top
    have hjensen : Real.exp (lam * ∫ ω, X ω ∂μ)
        ≤ ∫ ω, Real.exp (lam * X ω) ∂μ := by
      have h1 : Real.exp (∫ ω, lam * X ω ∂μ) ≤ ∫ ω, Real.exp (lam * X ω) ∂μ :=
        Chapter1.jensen_inequality convexOn_exp (hXint.const_mul lam) hint
      rwa [integral_const_mul] at h1
    have hbound : ∫ ω, Real.exp (lam * X ω) ∂μ ≤ Real.exp (K₄^2 * lam^2) := by
      have h1 : ∫ ω, Real.exp (lam * X ω) ∂μ
          = (∫⁻ ω, ENNReal.ofReal (Real.exp (lam * X ω)) ∂μ).toReal := by
        rw [integral_eq_lintegral_of_nonneg_ae
          (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le) hmeas]
      rw [h1]
      calc (∫⁻ ω, ENNReal.ofReal (Real.exp (lam * X ω)) ∂μ).toReal
          ≤ (ENNReal.ofReal (Real.exp (K₄^2 * lam^2))).toReal :=
            ENNReal.toReal_mono ENNReal.ofReal_ne_top (h lam)
        _ = Real.exp (K₄^2 * lam^2) := ENNReal.toReal_ofReal (Real.exp_pos _).le
    have := hjensen.trans hbound
    rwa [Real.exp_le_exp] at this
  -- `λ𝔼X ≤ K₄²λ²` for all `λ` forces `𝔼X = 0`: take `λ = 𝔼X/(2(K₄²+1))`.
  by_contra hne
  have hI2 : 0 < (∫ ω, X ω ∂μ)^2 := by positivity
  set A : ℝ := K₄^2 + 1 with hA
  have hApos : (0:ℝ) < A := by positivity
  have h1 := hkey ((∫ ω, X ω ∂μ) / (2*A))
  have hexp1 : (∫ ω, X ω ∂μ)/(2*A) * (∫ ω, X ω ∂μ)
      = (∫ ω, X ω ∂μ)^2/(2*A) := by ring
  have hexp2 : K₄^2 * ((∫ ω, X ω ∂μ)/(2*A))^2
      = K₄^2*(∫ ω, X ω ∂μ)^2/(4*A^2) := by
    field_simp
    ring
  rw [hexp1, hexp2] at h1
  have h2 : (∫ ω, X ω ∂μ)^2/(2*A) * (4*A^2)
      ≤ K₄^2*(∫ ω, X ω ∂μ)^2/(4*A^2) * (4*A^2) :=
    mul_le_mul_of_nonneg_right h1 (by positivity)
  have h3 : (∫ ω, X ω ∂μ)^2/(2*A) * (4*A^2) = 2*A*(∫ ω, X ω ∂μ)^2 := by
    field_simp
    ring
  have h4 : K₄^2*(∫ ω, X ω ∂μ)^2/(4*A^2) * (4*A^2) = K₄^2*(∫ ω, X ω ∂μ)^2 := by
    field_simp
  rw [h3, h4] at h2
  nlinarith [hI2, sq_nonneg K₄]

/-! ## Exercise 2.24(d): arbitrary centered Gaussian scale -/

/-- The square-exponential functional depends only on the law of the random
variable.

**Lean implementation helper.** -/
lemma psi2MGF_eq_of_hasLaw {X : Ω → ℝ} {ν : Measure ℝ}
    (hX : HasLaw X ν μ) (K : ℝ) :
    psi2MGF X μ K = psi2MGF (fun x : ℝ => x) ν K := by
  unfold psi2MGF
  simpa only [id_eq, Function.comp_apply] using hX.lintegral_comp
    ((measurable_exp.comp
      (measurable_id.pow_const 2 |>.div_const _)).ennreal_ofReal.aemeasurable)

/-- The ψ₂ norm depends only on the law of the random variable.

**Lean implementation helper.** -/
lemma psi2Norm_eq_of_hasLaw {X : Ω → ℝ} {ν : Measure ℝ}
    (hX : HasLaw X ν μ) :
    psi2Norm X μ = psi2Norm (fun x : ℝ => x) ν := by
  have hset : {K : ℝ | 0 < K ∧ psi2MGF X μ K ≤ 2} =
      {K : ℝ | 0 < K ∧ psi2MGF (fun x : ℝ => x) ν K ≤ 2} := by
    ext K
    simp only [Set.mem_setOf_eq]
    rw [psi2MGF_eq_of_hasLaw hX K]
  rw [psi2Norm, psi2Norm, hset]

/-- If
`X ∼ N(0, σ²)`, then `‖X‖_{ψ₂} = |σ| √(8/3)`. The absolute value makes the
formula valid for every real scale, including `σ = 0`.

**Book Exercise 2.22--2.24.** -/
theorem psi2Norm_gaussian {X : Ω → ℝ} (sigma : ℝ)
    (hX : HasLaw X
      (gaussianReal 0 ⟨sigma ^ 2, sq_nonneg sigma⟩) μ) :
    psi2Norm X μ = |sigma| * Real.sqrt (8 / 3) := by
  let ν : Measure ℝ := gaussianReal 0 1
  have hid : HasLaw (fun x : ℝ => x) (gaussianReal 0 1) ν := by
    refine ⟨measurable_id.aemeasurable, ?_⟩
    simp [ν]
  have hscaled : HasLaw (fun x : ℝ => sigma * x)
      (gaussianReal 0 ⟨sigma ^ 2, sq_nonneg sigma⟩) ν := by
    have h := ProbabilityTheory.gaussianReal_const_mul hid sigma
    convert h using 1
    rw [mul_zero, mul_one]
    apply congrArg (gaussianReal 0)
    apply NNReal.eq
    rfl
  calc
    psi2Norm X μ =
        psi2Norm (fun x : ℝ => x)
          (gaussianReal 0 ⟨sigma ^ 2, sq_nonneg sigma⟩) :=
      psi2Norm_eq_of_hasLaw hX
    _ = psi2Norm (fun x : ℝ => sigma * x) ν := by
      symm
      exact psi2Norm_eq_of_hasLaw hscaled
    _ = |sigma| * psi2Norm (fun x : ℝ => x) ν := by
      letI : IsProbabilityMeasure ν := by
        dsimp [ν]
        infer_instance
      exact psi2Norm_const_mul (μ := ν) (fun x : ℝ => x) sigma
    _ = |sigma| * Real.sqrt (8 / 3) := by
      dsimp [ν]
      rw [psi2Norm_standardGaussian_measure]

end HDP

end Source_08_SubGaussianNorm

/-! ## Material formerly in `09_SumsSubGaussian.lean` -/

section Source_09_SumsSubGaussian

/-
Book Chapter 2, Section 2.7: Subgaussian Hoeffding inequality and centering.



Contents:
* the Pythagorean identity for independent mean-zero random variables (Book (2.19));
* the subgaussian norm of a sum (Book Proposition 2.7.1), with the explicit absolute
  constant `C = 30` produced by this file's constants
  (`ψ(S)² ≤ (2√5)²·(3/2)·∑ψᵢ² = 30∑ψᵢ²`);
* the subgaussian Hoeffding inequality (Book Theorem 2.7.3), with `c = 1/30`;
* the recovery of classical Hoeffding for Rademacher sums (Book Example 2.7.4 /
  (2.20)), with `c = ln 2/30`;
* centering in `L²` (Book (2.23), from Exercise 0.2) and the ψ₂ centering lemma
  (Book Lemma 2.7.8), with the explicit constant `C = 1 + 1/√(ln 2)`.

Sections §2.7.2 (Khintchine) and §2.7.3 (maximum of subgaussians) are next-session
items; see the Chapter 2 checkpoint.
-/

open MeasureTheory ProbabilityTheory Real Filter
open scoped ENNReal NNReal Topology

namespace HDP

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-! ## Bochner bridge for exponential-moment bounds -/

/-- An `∫⁻` exponential-moment bound yields integrability
of `exp(λX)` and the same bound for the Bochner MGF.

**Lean implementation helper.** -/
lemma mgf_le_of_lintegral_exp_le {X : Ω → ℝ} (hXm : AEMeasurable X μ)
    {lam B : ℝ} (hB : 0 ≤ B)
    (h : ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * X ω)) ∂μ ≤ ENNReal.ofReal B) :
    Integrable (fun ω => Real.exp (lam * X ω)) μ ∧ mgf X μ lam ≤ B := by
  have hmeas : AEStronglyMeasurable (fun ω => Real.exp (lam * X ω)) μ :=
    (measurable_exp.comp_aemeasurable (hXm.const_mul lam)).aestronglyMeasurable
  have hlin : ∫⁻ ω, ‖Real.exp (lam * X ω)‖ₑ ∂μ
      = ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * X ω)) ∂μ := by
    refine lintegral_congr fun ω => ?_
    rw [Real.enorm_eq_ofReal_abs, abs_of_pos (Real.exp_pos _)]
  have hint : Integrable (fun ω => Real.exp (lam * X ω)) μ := by
    refine ⟨hmeas, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, hlin]
    exact lt_of_le_of_lt h ENNReal.ofReal_lt_top
  refine ⟨hint, ?_⟩
  have h1 : mgf X μ lam
      = (∫⁻ ω, ENNReal.ofReal (Real.exp (lam * X ω)) ∂μ).toReal := by
    rw [mgf, integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le) hmeas]
  rw [h1]
  calc (∫⁻ ω, ENNReal.ofReal (Real.exp (lam * X ω)) ∂μ).toReal
      ≤ (ENNReal.ofReal B).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    _ = B := ENNReal.toReal_ofReal hB

/-! ## Book (2.19): the Pythagorean identity -/

/-- Independent (formalized: pairwise
independent, which is what the variance computation uses) mean-zero `L²` random
variables satisfy `𝔼(∑Xᵢ)² = ∑𝔼Xᵢ²`, i.e. `‖∑Xᵢ‖²_{L²} = ∑‖Xᵢ‖²_{L²}`.
Explicit displayed source identity (derived, as the source says, from (1.8)).

**Book Equation (2.19).** -/
theorem pythagorean_identity [IsProbabilityMeasure μ] {N : ℕ} {X : Fin N → Ω → ℝ}
    (hX : ∀ i, MemLp (X i) 2 μ) (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hindep : Set.Pairwise Set.univ fun i j => IndepFun (X i) (X j) μ) :
    ∫ ω, (∑ i, X i ω)^2 ∂μ = ∑ i, ∫ ω, (X i ω)^2 ∂μ := by
  have hsum_fun : (fun ω => ∑ i, X i ω) = ∑ i, X i := by
    funext ω
    rw [Finset.sum_apply]
  have hSmem : MemLp (∑ i, X i) 2 μ := memLp_finsetSum' Finset.univ fun i _ => hX i
  have hSmean : ∫ ω, (∑ i, X i) ω ∂μ = 0 := by
    have h2 : ∫ ω, (∑ i, X i) ω ∂μ = ∫ ω, ∑ i, X i ω ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω => by
        rw [Finset.sum_apply])
    rw [h2, integral_finsetSum Finset.univ fun i _ => (hX i).integrable one_le_two]
    exact Finset.sum_eq_zero fun i _ => hmean i
  have hvarS : Var[∑ i, X i; μ] = ∫ ω, ((∑ i, X i) ω)^2 ∂μ := by
    have := variance_eq_sub hSmem
    rw [hSmean] at this
    simpa using this
  have hvari : ∀ i, Var[X i; μ] = ∫ ω, (X i ω)^2 ∂μ := by
    intro i
    have := variance_eq_sub (hX i)
    rw [hmean i] at this
    simpa using this
  have hsum := IndepFun.variance_sum (s := Finset.univ) (fun i _ => hX i)
    (fun i _ j _ hij => hindep (Set.mem_univ i) (Set.mem_univ j) hij)
  rw [hvarS] at hsum
  calc ∫ ω, (∑ i, X i ω)^2 ∂μ
      = ∫ ω, ((∑ i, X i) ω)^2 ∂μ := by rw [← hsum_fun]
    _ = ∑ i, Var[X i; μ] := hsum
    _ = ∑ i, ∫ ω, (X i ω)^2 ∂μ := Finset.sum_congr rfl fun i _ => hvari i

/-! ## Book Proposition 2.7.1: the subgaussian norm of a sum -/

/-- For independent mean-zero subgaussian `X₁, …, X_N`:
`‖∑ᵢXᵢ‖²_{ψ₂} ≤ C·∑ᵢ‖Xᵢ‖²_{ψ₂}` with the absolute constant `C = 30` (this file's
constant accounting: MGF of the sum ≤ `exp((3/2)λ²∑ψᵢ²)` by Proposition 2.6.6(iv) and
independence; then (iv)⇒(iii) with `K₃ = 2√5·K₄` gives `ψ(S)² ≤ 20·(3/2)∑ψᵢ²`).

The Lean proof is the source's: MGF of the sum = product of MGFs, per-factor bound
from (iv), conclude via (iv)⇒(iii).

**Book Proposition 2.7.1.** -/
theorem psi2Norm_sum_sq_le [IsProbabilityMeasure μ] {N : ℕ} {X : Fin N → Ω → ℝ}
    (hXm : ∀ i, AEMeasurable (X i) μ) (hX : ∀ i, SubGaussian (X i) μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) (hindep : iIndepFun X μ) :
    SubGaussian (fun ω => ∑ i, X i ω) μ ∧
    (psi2Norm (fun ω => ∑ i, X i ω) μ)^2 ≤ 30 * ∑ i, (psi2Norm (X i) μ)^2 := by
  classical
  set σsq : ℝ := ∑ i, (psi2Norm (X i) μ)^2 with hσsq
  have hσ0 : 0 ≤ σsq := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hSm : AEMeasurable (fun ω => ∑ i, X i ω) μ := by
    have h1 : AEMeasurable (∑ i, X i) μ :=
      Finset.aemeasurable_sum Finset.univ fun i _ => hXm i
    have h2 : (∑ i, X i) = fun ω => ∑ i, X i ω := by
      funext ω
      rw [Finset.sum_apply]
    rwa [h2] at h1
  rcases eq_or_lt_of_le hσ0 with hσzero | hσpos
  · -- degenerate case: every `ψᵢ = 0`, so every `Xᵢ = 0` a.s. and the sum vanishes
    have hz : ∀ i, X i =ᵐ[μ] 0 := by
      intro i
      refine ae_eq_zero_of_psi2Norm_eq_zero (hXm i) (hX i) ?_
      have h1 : (psi2Norm (X i) μ)^2 = 0 := by
        have h2 := Finset.sum_eq_zero_iff_of_nonneg
          (fun j (_ : j ∈ Finset.univ) => sq_nonneg (psi2Norm (X j) μ))
        rw [← hσsq, ← hσzero] at h2
        exact h2.mp rfl i (Finset.mem_univ i)
      exact pow_eq_zero_iff (by norm_num) |>.mp h1
    have hzsum : (fun ω => ∑ i, X i ω) =ᵐ[μ] 0 := by
      have hall := (MeasureTheory.ae_all_iff).mpr hz
      filter_upwards [hall] with ω hω
      have : ∑ i, X i ω = 0 := Finset.sum_eq_zero fun i _ => by
        have := hω i
        rwa [Pi.zero_apply] at this
      simpa using this
    have hsub : SubGaussian (fun ω => ∑ i, X i ω) μ :=
      ⟨1, one_pos, by rw [psi2MGF_of_ae_zero hzsum]; norm_num⟩
    refine ⟨hsub, ?_⟩
    rw [(psi2Norm_eq_zero_iff hSm hsub).mpr hzsum]
    nlinarith [hσ0]
  · -- main case
    set K₄ : ℝ := Real.sqrt ((3/2) * σsq) with hK₄
    have hK₄pos : 0 < K₄ := Real.sqrt_pos.mpr (by nlinarith)
    have hK₄sq : K₄^2 = (3/2) * σsq := Real.sq_sqrt (by nlinarith)
    -- (iv) for the sum
    have hmgfS : ∀ lam : ℝ, ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * ∑ i, X i ω)) ∂μ
        ≤ ENNReal.ofReal (Real.exp (K₄^2 * lam^2)) := by
      intro lam
      -- per-factor Bochner bounds
      have hfac : ∀ i, Integrable (fun ω => Real.exp (lam * X i ω)) μ ∧
          mgf (X i) μ lam ≤ Real.exp ((3/2) * (psi2Norm (X i) μ)^2 * lam^2) := by
        intro i
        exact mgf_le_of_lintegral_exp_le (hXm i) (Real.exp_pos _).le
          ((hX i).mgf_bound (hXm i) (hmean i) lam)
      -- product rule
      have hprod : mgf (fun ω => ∑ i, X i ω) μ lam = ∏ i, mgf (X i) μ lam := by
        have h2 : (fun ω => ∑ i, X i ω) = ∑ i, X i := by
          funext ω
          rw [Finset.sum_apply]
        rw [h2]
        exact iIndepFun.mgf_sum₀ hindep (fun i => hXm i) Finset.univ
      have hprod_le : mgf (fun ω => ∑ i, X i ω) μ lam
          ≤ Real.exp (K₄^2 * lam^2) := by
        rw [hprod]
        calc ∏ i, mgf (X i) μ lam
            ≤ ∏ i, Real.exp ((3/2) * (psi2Norm (X i) μ)^2 * lam^2) :=
              Finset.prod_le_prod (fun i _ => mgf_nonneg) (fun i _ => (hfac i).2)
          _ = Real.exp (∑ i, (3/2) * (psi2Norm (X i) μ)^2 * lam^2) :=
              (Real.exp_sum _ _).symm
          _ = Real.exp (K₄^2 * lam^2) := by
              congr 1
              rw [hK₄sq, hσsq, Finset.mul_sum, Finset.sum_mul]
      -- integrability of `exp(λS)` from positivity of the product
      have hSexp_int : Integrable (fun ω => Real.exp (lam * ∑ i, X i ω)) μ := by
        by_contra hni
        have h0 : mgf (fun ω => ∑ i, X i ω) μ lam = 0 := by
          rw [mgf]
          exact integral_undef hni
        have hpos : 0 < ∏ i, mgf (X i) μ lam :=
          Finset.prod_pos fun i _ => mgf_pos' (NeZero.ne μ) (hfac i).1
        rw [hprod] at h0
        exact absurd h0 hpos.ne'
      -- convert back to `∫⁻`
      calc ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * ∑ i, X i ω)) ∂μ
          = ENNReal.ofReal (mgf (fun ω => ∑ i, X i ω) μ lam) := by
            rw [mgf]
            exact (ofReal_integral_eq_lintegral_ofReal hSexp_int
              (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le)).symm
        _ ≤ ENNReal.ofReal (Real.exp (K₄^2 * lam^2)) :=
            ENNReal.ofReal_le_ofReal hprod_le
    -- conclude by (iv)⇒(iii)
    obtain ⟨hsub, hle⟩ := psi2Norm_le_of_mgf_bound hSm hK₄pos hmgfS
    refine ⟨hsub, ?_⟩
    have h5 : (0:ℝ) ≤ Real.sqrt 5 * (2 * K₄) := by positivity
    calc (psi2Norm (fun ω => ∑ i, X i ω) μ)^2
        ≤ (Real.sqrt 5 * (2 * K₄))^2 := by
          have hn := psi2Norm_nonneg (fun ω => ∑ i, X i ω) μ
          nlinarith
      _ = 5 * 4 * K₄^2 := by
          rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)]
          ring
      _ = 30 * σsq := by
          rw [hK₄sq]
          ring

/-! ## Book Theorem 2.7.3: the subgaussian Hoeffding inequality -/

/-- For independent mean-zero subgaussian `X₁, …, X_N` and
`t ≥ 0`: `ℙ{|∑ᵢXᵢ| ≥ t} ≤ 2exp(−ct²/∑ᵢ‖Xᵢ‖²_{ψ₂})` where `c > 0` is an absolute
constant — here produced explicitly as `c = 1/30` (Proposition 2.7.1's constant
combined with Proposition 2.6.6(i) at `c = 1`).

The Lean proof is the source's: rephrase Proposition 2.7.1 via Proposition 2.6.6(i).

**Book Equation (2.14).** -/
theorem subgaussian_hoeffding [IsProbabilityMeasure μ] {N : ℕ} {X : Fin N → Ω → ℝ}
    (hXm : ∀ i, AEMeasurable (X i) μ) (hX : ∀ i, SubGaussian (X i) μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) (hindep : iIndepFun X μ)
    {t : ℝ} (ht : 0 ≤ t) :
    μ {ω | t ≤ |∑ i, X i ω|}
      ≤ ENNReal.ofReal (2 * Real.exp (-t^2/(30 * ∑ i, (psi2Norm (X i) μ)^2))) := by
  obtain ⟨hsub, hle⟩ := psi2Norm_sum_sq_le hXm hX hmean hindep
  have hSm : AEMeasurable (fun ω => ∑ i, X i ω) μ := by
    have h1 : AEMeasurable (∑ i, X i) μ :=
      Finset.aemeasurable_sum Finset.univ fun i _ => hXm i
    have h2 : (∑ i, X i) = fun ω => ∑ i, X i ω := by
      funext ω
      rw [Finset.sum_apply]
    rwa [h2] at h1
  set ψS : ℝ := psi2Norm (fun ω => ∑ i, X i ω) μ with hψS
  set σsq : ℝ := ∑ i, (psi2Norm (X i) μ)^2 with hσsq
  have hψS0 : 0 ≤ ψS := psi2Norm_nonneg _ μ
  have htail := hsub.tail_bound hSm (t := t) ht
  rcases eq_or_lt_of_le hψS0 with hzero | hpos
  · -- `ψ(S) = 0`: the sum vanishes a.s.
    have hz := ae_eq_zero_of_psi2Norm_eq_zero hSm hsub hzero.symm
    rcases eq_or_lt_of_le ht with rfl | htpos
    · -- `t = 0`: probability ≤ 1 ≤ 2exp(0)... the bound is ≥ 1 in all cases
      calc μ {ω | (0:ℝ) ≤ |∑ i, X i ω|} ≤ 1 := prob_le_one
        _ ≤ ENNReal.ofReal (2 * Real.exp (-(0:ℝ)^2/(30 * σsq))) := by
            rw [show -(0:ℝ)^2/(30*σsq) = 0 from by norm_num, Real.exp_zero, mul_one]
            norm_num
    · -- `t > 0`: the event is null
      have hnull : μ {ω | t ≤ |∑ i, X i ω|} = 0 := by
        refine measure_mono_null ?_ ((MeasureTheory.ae_iff).mp hz)
        intro ω hω
        simp only [Set.mem_setOf_eq] at hω ⊢
        intro hz'
        rw [Pi.zero_apply] at hz'
        rw [hz'] at hω
        simp only [abs_zero] at hω
        linarith
      rw [hnull]
      exact bot_le
  · -- main case: compare the exponents
    refine htail.trans (ENNReal.ofReal_le_ofReal ?_)
    have hb : ψS^2 ≤ 30 * σsq := hle
    have hσpos : 0 < 30 * σsq := by nlinarith [sq_nonneg ψS]
    have hexp : -t^2/ψS^2 ≤ -t^2/(30 * σsq) := by
      rw [neg_div, neg_div, neg_le_neg_iff]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hb
    nlinarith [Real.exp_le_exp.mpr hexp, Real.exp_pos (-t^2/ψS^2),
      Real.exp_pos (-t^2/(30*σsq))]

/-! ## Book Example 2.7.4 / (2.20): recovering classical Hoeffding -/

/-- For independent
Rademacher `Xᵢ` and any coefficients `aᵢ`,
`ℙ{|∑aᵢXᵢ| ≥ t} ≤ 2exp(−ct²/‖a‖₂²)`, "just with a different absolute constant `c`
instead of `1/2`" — here `c = ln 2/30` explicitly (since `‖Xᵢ‖_{ψ₂} = 1/√(ln 2)` by
Exercise 2.24(c)). Explicit source declaration.

**Book Example 2.7.4.** -/
theorem example_2_7_4 [IsProbabilityMeasure μ] {N : ℕ} {X : Fin N → Ω → ℝ}
    (hX : ∀ i, HDP.IsRademacher (X i) μ) (hindep : iIndepFun X μ)
    (a : Fin N → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    μ {ω | t ≤ |∑ i, a i * X i ω|}
      ≤ ENNReal.ofReal (2 * Real.exp (-(Real.log 2) * t^2/(30 * ∑ i, (a i)^2))) := by
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hXm : ∀ i, AEMeasurable (fun ω => a i * X i ω) μ :=
    fun i => ((hX i).aemeasurable.const_mul (a i))
  have hsubG : ∀ i, SubGaussian (fun ω => a i * X i ω) μ := by
    intro i
    have := (hX i).isProbabilityMeasure
    rcases eq_or_ne (a i) 0 with hz | hz
    · refine ⟨1, one_pos, ?_⟩
      have hzero : (fun ω => a i * X i ω) =ᵐ[μ] 0 := by
        refine Filter.Eventually.of_forall fun ω => ?_
        simp [hz]
      rw [psi2MGF_of_ae_zero hzero]
      norm_num
    · obtain ⟨hs, _⟩ := psi2Norm_le_of_bounded (M := |a i|)
        (abs_pos.mpr hz) (by
          filter_upwards [(hX i).ae_mem] with ω hω
          have habs : |a i * X i ω| = |a i| * |X i ω| := abs_mul (a i) (X i ω)
          rw [habs]
          rcases hω with hω | hω <;> rw [hω] <;> norm_num)
      exact hs
  have hmean : ∀ i, ∫ ω, a i * X i ω ∂μ = 0 := by
    intro i
    have := (hX i).isProbabilityMeasure
    rw [integral_const_mul, (hX i).integral_eq_zero, mul_zero]
  have hYindep : iIndepFun (fun i ω => a i * X i ω) μ :=
    hindep.comp (fun i x => a i * x) (fun i => measurable_const_mul (a i))
  have h := subgaussian_hoeffding hXm hsubG hmean hYindep ht
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  -- `ψ(aᵢXᵢ)² = aᵢ²/ln2`, so `30∑ψᵢ² = 30∑aᵢ²/ln2` and the exponents agree
  have hψ : ∀ i, (psi2Norm (fun ω => a i * X i ω) μ)^2
      = (a i)^2 / Real.log 2 := by
    intro i
    have := (hX i).isProbabilityMeasure
    rw [psi2Norm_const_mul (X i) (a i), psi2Norm_rademacher (hX i)]
    rw [mul_pow, div_pow, one_pow, Real.sq_sqrt hlog2.le, sq_abs]
    ring
  have hsum : ∑ i, (psi2Norm (fun ω => a i * X i ω) μ)^2
      = (∑ i, (a i)^2) / Real.log 2 := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => hψ i
  rw [hsum]
  have harg : -t^2/(30 * ((∑ i, (a i)^2) / Real.log 2))
      = -(Real.log 2) * t^2/(30 * ∑ i, (a i)^2) := by
    rcases eq_or_ne (∑ i, (a i)^2) 0 with hz | hz
    · rw [hz]
      norm_num
    · field_simp
  rw [harg]

/-! ## Book (2.23) and Lemma 2.7.8: centering -/

/-- `‖X − 𝔼X‖_{L²} ≤ ‖X‖_{L²}` (in squared,
integral form: `𝔼(X−𝔼X)² ≤ 𝔼X²`). Explicit displayed source claim, derived from the
extremal property of Exercise 0.2 with `a = 0` (Prelude).

**Book Equation (2.23).** -/
theorem centering_L2 [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ) :
    ∫ ω, (X ω - ∫ ω', X ω' ∂μ)^2 ∂μ ≤ ∫ ω, (X ω)^2 ∂μ := by
  have h1 := HDP.variance_le_integral_sq_sub hX 0
  simp only [sub_zero] at h1
  have h2 : Var[X; μ] = ∫ ω, (X ω - ∫ ω', X ω' ∂μ)^2 ∂μ :=
    variance_eq_integral hX.aemeasurable
  linarith [h1, h2.symm.le, h2.le]

/-- Any subgaussian `X` satisfies
`‖X − 𝔼X‖_{ψ₂} ≤ C‖X‖_{ψ₂}` with an absolute constant — here `C = 1 + 1/√(ln 2)`
explicitly.

The Lean proof is the source's: the ψ₂ triangle inequality (Exercise 2.42), the
constant computation `‖a‖_{ψ₂} = |a|/√(ln 2)` (Exercise 2.24(a)), Jensen
(`|𝔼X| ≤ 𝔼|X|`), and Proposition 2.6.6(ii) at `p = 1`.

**Book Lemma 2.7.8.** -/
theorem psi2Norm_centering [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXm : AEMeasurable X μ) (hX : SubGaussian X μ) :
    SubGaussian (fun ω => X ω - ∫ ω', X ω' ∂μ) μ ∧
    psi2Norm (fun ω => X ω - ∫ ω', X ω' ∂μ) μ
      ≤ (1 + 1/Real.sqrt (Real.log 2)) * psi2Norm X μ := by
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set m : ℝ := ∫ ω', X ω' ∂μ with hm
  -- the constant `−m` is subgaussian with `ψ₂ = |m|/√(ln2)`
  have hconst_sub : SubGaussian (fun _ : Ω => -m) μ :=
    (psi2Norm_le_of_bounded (μ := μ) (X := fun _ : Ω => -m)
      (M := |m|+1) (by positivity)
      (Filter.Eventually.of_forall fun ω => by
        rw [abs_neg]
        linarith)).1
  have hconst_norm : psi2Norm (fun _ : Ω => -m) μ = |m|/Real.sqrt (Real.log 2) := by
    rw [psi2Norm_const, abs_neg]
  -- `X − m = X + (−m)`: triangle inequality
  have hdecomp : (fun ω => X ω - m) = fun ω => X ω + (fun _ : Ω => -m) ω := by
    funext ω
    ring
  have htri := psi2Norm_add_le hXm (aemeasurable_const (b := -m)) hX hconst_sub
  -- `|m| ≤ 𝔼|X| = ‖X‖_{L¹} ≤ ψ₂(X)` (Jensen + Proposition 2.6.6(ii) at p = 1)
  have hXint : Integrable X μ := by
    obtain ⟨K, hK, hKb⟩ := hX
    obtain ⟨hEint, _⟩ := integrable_exp_sq_div hXm hKb
    refine (hEint.const_mul K).mono' hXm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    exact abs_le_mul_exp_sq_div hK
  have hmean_le : |m| ≤ psi2Norm X μ := by
    have h1 : |m| ≤ ∫ ω, |X ω| ∂μ := by
      rw [hm]
      exact abs_integral_le_integral_abs
    have h2 : ∫ ω, |X ω| ∂μ = Chapter1.lpNormRV X 1 μ := by
      rw [Chapter1.lpNormRV]
      rw [show (1:ℝ)/1 = 1 from by norm_num, Real.rpow_one]
      exact (integral_congr_ae
        (Filter.Eventually.of_forall fun ω => (Real.rpow_one _).symm))
    have h3 := hX.moment_bound hXm (le_refl (1:ℝ))
    rw [Real.sqrt_one, mul_one] at h3
    calc |m| ≤ ∫ ω, |X ω| ∂μ := h1
      _ = Chapter1.lpNormRV X 1 μ := h2
      _ ≤ psi2Norm X μ := h3
  constructor
  · rw [show (fun ω => X ω - ∫ ω', X ω' ∂μ) = fun ω => X ω + (fun _ : Ω => -m) ω
      from hdecomp]
    exact SubGaussian.add hXm (aemeasurable_const (b := -m)) hX hconst_sub
  · calc psi2Norm (fun ω => X ω - ∫ ω', X ω' ∂μ) μ
        = psi2Norm (fun ω => X ω + (fun _ : Ω => -m) ω) μ := by rw [hdecomp]
      _ ≤ psi2Norm X μ + psi2Norm (fun _ : Ω => -m) μ := htri
      _ = psi2Norm X μ + |m|/Real.sqrt (Real.log 2) := by rw [hconst_norm]
      _ ≤ psi2Norm X μ + psi2Norm X μ/Real.sqrt (Real.log 2) := by
          gcongr
      _ = (1 + 1/Real.sqrt (Real.log 2)) * psi2Norm X μ := by ring

end HDP

end Source_09_SumsSubGaussian

/-! ## Material formerly in `10_KhintchineMax.lean` -/

section Source_10_KhintchineMax

/-
Book Chapter 2, Sections 2.7.2–2.7.3: Khintchine inequality and the maximum of
subgaussians.



Contents:
* closure helpers (`psi2MGF_le_two_of_ge`, `SubGaussian.const_mul`,
  `SubGaussian.memLp`, `psi2Norm_mono_abs`, `abs_sup'_le`,
  `integrable_exp_sq_div_of_le`);
* the Khintchine inequality (Book Theorem 2.7.5) for `p ∈ [2,∞)`, with the explicit
  absolute constant `C = √30` (from Proposition 2.7.1's `C = 30`);
* the maximum of subgaussians (Book Proposition 2.7.6): the ψ₂ bound (2.21) in the
  sharp form `‖maxᵢ|Xᵢ|‖_{ψ₂} ≤ √(2ln(2N))·K` produced by the source's second
  proof, the book-display form `≤ 2√(ln N)·K`, the version for `maxᵢXᵢ` ("the same
  bounds obviously hold"), and the expectation bound (2.22) with explicit `C = 2`.

Conventions: the source's `K = maxᵢ‖Xᵢ‖_{ψ₂}` is encoded by a parameter `K`
with `∀ i, ‖Xᵢ‖_{ψ₂} ≤ K` (the source's `K` is the least such bound); the source's
`N ≥ 2` is encoded structurally as `N = n + 2` so that `Fin N` is nonempty by
instance and `maxᵢ` is `Finset.univ.sup'`.
-/

open MeasureTheory ProbabilityTheory Real Filter
open scoped ENNReal NNReal Topology

namespace HDP

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-! ## Closure helpers -/

/-- If `‖X‖_{ψ₂} ≤ K` for a subgaussian `X` and `K > 0`, then `𝔼exp(X²/K²) ≤ 2`
(attainment plus antitonicity; implicit well-definedness fact used throughout
§2.7.3).

**Book Section 2.7.3.** -/
lemma psi2MGF_le_two_of_ge [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXm : AEMeasurable X μ) (h : SubGaussian X μ) {K : ℝ}
    (hK : psi2Norm X μ ≤ K) (_hK0 : 0 < K) : psi2MGF X μ K ≤ 2 := by
  rcases eq_or_lt_of_le hK with heq | hlt
  · rw [← heq]
    exact psi2MGF_psi2Norm_le_two hXm h
  · exact psi2MGF_le_two_of_gt h hlt

/-- Scalar multiples of subgaussian random variables are subgaussian (closure
property implicit in §2.6.1; quantitatively `‖cX‖_{ψ₂} = |c|‖X‖_{ψ₂}` by
`psi2Norm_const_mul`).

**Book Section 2.6.1.** -/
lemma SubGaussian.const_mul [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (h : SubGaussian X μ) (c : ℝ) : SubGaussian (fun ω => c * X ω) μ := by
  rcases eq_or_ne c 0 with rfl | hc
  · refine ⟨1, one_pos, ?_⟩
    have hz : (fun ω => (0:ℝ) * X ω) =ᵐ[μ] 0 :=
      Filter.Eventually.of_forall fun ω => by simp
    rw [psi2MGF_of_ae_zero hz]
    norm_num
  · obtain ⟨K, hK, hKb⟩ := h
    refine ⟨|c| * K, by positivity, ?_⟩
    rw [psi2MGF_const_mul hc K]
    exact hKb

/-- A subgaussian random variable is in every `L^p`, `1 ≤ p < ∞` (finiteness of
all moments; needed to compare `L^p` norms in the proof of Theorem 2.7.5).

**Book Theorem 2.7.5.** -/
lemma SubGaussian.memLp [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXm : AEMeasurable X μ) (h : SubGaussian X μ) {p : ℝ} (hp : 1 ≤ p) :
    MemLp X (ENNReal.ofReal p) μ := by
  have hp0 : 0 < p := lt_of_lt_of_le one_pos hp
  obtain ⟨K, hK, hKb⟩ := h
  have hmom := subgaussian_iii_to_ii (μ := μ) hK hKb hp
  refine ⟨hXm.aestronglyMeasurable, ?_⟩
  have hne : ENNReal.ofReal p ≠ 0 := by
    simpa [ENNReal.ofReal_eq_zero] using not_le.mpr hp0
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hne ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp0.le]
  refine ENNReal.rpow_lt_top_of_nonneg (by positivity) ?_
  have hcong : ∀ ω : Ω, ‖X ω‖ₑ ^ p = ENNReal.ofReal (|X ω| ^ p) := by
    intro ω
    rw [Real.enorm_eq_ofReal_abs,
      ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp0.le]
  rw [lintegral_congr hcong]
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hmom

/-- Ψ₂-monotonicity under pointwise absolute-value domination (used to pass from
`maxᵢ|Xᵢ|` to `maxᵢXᵢ` in Proposition 2.7.6: "the same bounds obviously hold").

**Book Proposition 2.7.6.** -/
lemma psi2Norm_mono_abs [IsProbabilityMeasure μ] {Y Z : Ω → ℝ}
    (hdom : ∀ᵐ ω ∂μ, |Y ω| ≤ |Z ω|) (hZ : SubGaussian Z μ) :
    SubGaussian Y μ ∧ psi2Norm Y μ ≤ psi2Norm Z μ := by
  have hmono : ∀ K : ℝ, psi2MGF Y μ K ≤ psi2MGF Z μ K := by
    intro K
    refine lintegral_mono_ae ?_
    filter_upwards [hdom] with ω hω
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ (by positivity)
    calc (Y ω)^2 = |Y ω|^2 := (sq_abs _).symm
      _ ≤ |Z ω|^2 := by nlinarith [abs_nonneg (Y ω), abs_nonneg (Z ω)]
      _ = (Z ω)^2 := sq_abs _
  obtain ⟨K, hK, hKb⟩ := hZ
  have hYsub : SubGaussian Y μ := ⟨K, hK, (hmono K).trans hKb⟩
  refine ⟨hYsub, ?_⟩
  unfold psi2Norm
  refine le_csInf ⟨K, hK, hKb⟩ fun b hb => ?_
  exact csInf_le ⟨0, fun x hx => hx.1.le⟩ ⟨hb.1, (hmono b).trans hb.2⟩

/-- `|maxᵢ f(i)| ≤ maxᵢ |f(i)|` for a finite maximum (implicit step of
Proposition 2.7.6).

**Book Proposition 2.7.6.** -/
lemma abs_sup'_le {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (f : ι → ℝ) :
    |s.sup' hs f| ≤ s.sup' hs fun i => |f i| := by
  rw [abs_le]
  constructor
  · obtain ⟨j, hj⟩ := id hs
    calc -(s.sup' hs fun i => |f i|) ≤ -|f j| :=
          neg_le_neg (Finset.le_sup' (fun i => |f i|) hj)
      _ ≤ f j := neg_abs_le _
      _ ≤ s.sup' hs f := Finset.le_sup' f hj
  · exact Finset.sup'_le hs _ fun i hi =>
      (le_abs_self _).trans (Finset.le_sup' (fun i => |f i|) hi)

/-- Variant of `integrable_exp_sq_div` with an arbitrary bound `B` in place of `2`
(hidden integrability obligation of Proposition 2.7.6's second proof, where the
bound is `2N`).

**Book Proposition 2.7.6.** -/
lemma integrable_exp_sq_div_of_le {X : Ω → ℝ} (hXm : AEMeasurable X μ)
    {K B : ℝ} (hB : 0 ≤ B) (h : psi2MGF X μ K ≤ ENNReal.ofReal B) :
    Integrable (fun ω => Real.exp ((X ω)^2 / K^2)) μ ∧
      ∫ ω, Real.exp ((X ω)^2 / K^2) ∂μ ≤ B := by
  have hmeas : AEStronglyMeasurable (fun ω => Real.exp ((X ω)^2 / K^2)) μ :=
    (measurable_exp.comp_aemeasurable
      ((hXm.pow_const 2).div_const _)).aestronglyMeasurable
  have hlin : ∫⁻ ω, ‖Real.exp ((X ω)^2 / K^2)‖ₑ ∂μ = psi2MGF X μ K := by
    unfold psi2MGF
    refine lintegral_congr fun ω => ?_
    rw [Real.enorm_eq_ofReal_abs, abs_of_pos (Real.exp_pos _)]
  have hfin : HasFiniteIntegral (fun ω => Real.exp ((X ω)^2 / K^2)) μ := by
    rw [hasFiniteIntegral_iff_enorm, hlin]
    exact lt_of_le_of_lt h ENNReal.ofReal_lt_top
  refine ⟨⟨hmeas, hfin⟩, ?_⟩
  have h1 : ∫ ω, Real.exp ((X ω)^2 / K^2) ∂μ = (psi2MGF X μ K).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le) hmeas]
    rfl
  rw [h1]
  calc (psi2MGF X μ K).toReal ≤ (ENNReal.ofReal B).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    _ = B := ENNReal.toReal_ofReal hB

/-! ## Book Theorem 2.7.5: the Khintchine inequality -/

/-- Let `X₁, …, X_N` be independent subgaussian random
variables with zero means and unit variances (`𝔼Xᵢ² = 1`), `‖Xᵢ‖_{ψ₂} ≤ K`, and
`a ∈ ℝᴺ`. Then for every `p ∈ [2,∞)`:
`(∑aᵢ²)^{1/2} ≤ ‖∑aᵢXᵢ‖_{L^p} ≤ CK√p·(∑aᵢ²)^{1/2}` with the explicit absolute
constant `C = √30` (Proposition 2.7.1's constant).

The Lean proof is the source's: the lower bound from the Pythagorean identity
(2.19) — which gives `‖∑aᵢXᵢ‖_{L²} = (∑aᵢ²)^{1/2}` exactly — and the monotonicity
of `L^p` norms (1.20); the upper bound from Proposition 2.7.1 and
Proposition 2.6.6(ii).

**Book Theorem 2.7.5.** -/
theorem khintchine [IsProbabilityMeasure μ] {N : ℕ} {X : Fin N → Ω → ℝ}
    (hXm : ∀ i, AEMeasurable (X i) μ) (hX : ∀ i, SubGaussian (X i) μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) (hvar : ∀ i, ∫ ω, (X i ω) ^ 2 ∂μ = 1)
    (hindep : iIndepFun X μ) {K : ℝ} (hK : 0 ≤ K)
    (hKb : ∀ i, psi2Norm (X i) μ ≤ K) (a : Fin N → ℝ) {p : ℝ} (hp : 2 ≤ p) :
    Real.sqrt (∑ i, (a i)^2)
        ≤ Chapter1.lpNormRV (fun ω => ∑ i, a i * X i ω) p μ ∧
    Chapter1.lpNormRV (fun ω => ∑ i, a i * X i ω) p μ
        ≤ Real.sqrt 30 * K * Real.sqrt p * Real.sqrt (∑ i, (a i)^2) := by
  have hp1 : (1:ℝ) ≤ p := by linarith
  set Y : Fin N → Ω → ℝ := fun i ω => a i * X i ω with hY
  have hYm : ∀ i, AEMeasurable (Y i) μ := fun i => (hXm i).const_mul (a i)
  have hYsub : ∀ i, SubGaussian (Y i) μ := fun i => (hX i).const_mul (a i)
  have hYmean : ∀ i, ∫ ω, Y i ω ∂μ = 0 := by
    intro i
    rw [hY]
    simp only
    rw [integral_const_mul, hmean i, mul_zero]
  have hYindep : iIndepFun Y μ :=
    hindep.comp (fun i x => a i * x) (fun i => measurable_const_mul (a i))
  obtain ⟨hSsub, hSle⟩ := psi2Norm_sum_sq_le hYm hYsub hYmean hYindep
  have hSm : AEMeasurable (fun ω => ∑ i, Y i ω) μ := by
    have h1 : AEMeasurable (∑ i, Y i) μ :=
      Finset.aemeasurable_sum Finset.univ fun i _ => hYm i
    have h2 : (∑ i, Y i) = fun ω => ∑ i, Y i ω := by
      funext ω
      rw [Finset.sum_apply]
    rwa [h2] at h1
  -- `‖S‖_{L²} = √(∑aᵢ²)` exactly (Pythagorean identity + unit variances)
  have hL2sq : ∫ ω, (∑ i, Y i ω)^2 ∂μ = ∑ i, (a i)^2 := by
    have hYL2 : ∀ i, MemLp (Y i) 2 μ := by
      intro i
      have h2 := (hYsub i).memLp (hYm i) one_le_two
      rwa [ENNReal.ofReal_ofNat] at h2
    have hpyth := pythagorean_identity hYL2 hYmean
      (fun i _ j _ hij => hYindep.indepFun hij)
    rw [hpyth]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hY]
    simp only
    rw [integral_congr_ae (Filter.Eventually.of_forall
      (fun ω => show (a i * X i ω)^2 = (a i)^2 * (X i ω)^2 from by ring)),
      integral_const_mul, hvar i, mul_one]
  have hL2 : Chapter1.lpNormRV (fun ω => ∑ i, Y i ω) 2 μ
      = Real.sqrt (∑ i, (a i)^2) := by
    have hSL2 : MemLp (fun ω => ∑ i, Y i ω) 2 μ := by
      simpa using hSsub.memLp hSm (p := (2 : ℝ)) (by norm_num)
    have hsq := Chapter1.sq_lpNormRV_two_eq_l2InnerRV
      (X := fun ω => ∑ i, Y i ω) (μ := μ) hSL2
    have hinner : Chapter1.l2InnerRV (fun ω => ∑ i, Y i ω)
        (fun ω => ∑ i, Y i ω) μ = ∑ i, (a i)^2 := by
      rw [Chapter1.l2InnerRV, ← hL2sq]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      change (∑ i, Y i ω) * (∑ i, Y i ω) = (∑ i, Y i ω) ^ 2
      rw [pow_two]
    have hnn : 0 ≤ Chapter1.lpNormRV (fun ω => ∑ i, Y i ω) 2 μ := by
      rw [Chapter1.lpNormRV]
      positivity
    calc Chapter1.lpNormRV (fun ω => ∑ i, Y i ω) 2 μ
        = Real.sqrt ((Chapter1.lpNormRV (fun ω => ∑ i, Y i ω) 2 μ)^2) :=
          (Real.sqrt_sq hnn).symm
      _ = Real.sqrt (∑ i, (a i)^2) := by rw [hsq, hinner]
  -- ψ₂ norm of the sum, via Proposition 2.7.1
  have hψS : psi2Norm (fun ω => ∑ i, Y i ω) μ
      ≤ Real.sqrt 30 * K * Real.sqrt (∑ i, (a i)^2) := by
    have hψY : ∀ i, (psi2Norm (Y i) μ)^2
        = (a i)^2 * (psi2Norm (X i) μ)^2 := by
      intro i
      rw [hY]
      simp only
      rw [psi2Norm_const_mul (X i) (a i), mul_pow, sq_abs]
    have h2 : ∑ i, (psi2Norm (Y i) μ)^2 ≤ K^2 * ∑ i, (a i)^2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [hψY i]
      have hψi : (psi2Norm (X i) μ)^2 ≤ K^2 := by
        nlinarith [psi2Norm_nonneg (X i) μ, hKb i]
      calc (a i)^2 * (psi2Norm (X i) μ)^2 ≤ (a i)^2 * K^2 :=
            mul_le_mul_of_nonneg_left hψi (sq_nonneg _)
        _ = K^2 * (a i)^2 := mul_comm _ _
    have h1 : (psi2Norm (fun ω => ∑ i, Y i ω) μ)^2
        ≤ 30 * (K^2 * ∑ i, (a i)^2) := hSle.trans (by nlinarith [h2])
    have hrhs : Real.sqrt (30 * (K^2 * ∑ i, (a i)^2))
        = Real.sqrt 30 * K * Real.sqrt (∑ i, (a i)^2) := by
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 30),
        Real.sqrt_mul (sq_nonneg K), Real.sqrt_sq hK]
      ring
    calc psi2Norm (fun ω => ∑ i, Y i ω) μ
        = Real.sqrt ((psi2Norm (fun ω => ∑ i, Y i ω) μ)^2) :=
          (Real.sqrt_sq (psi2Norm_nonneg _ μ)).symm
      _ ≤ Real.sqrt (30 * (K^2 * ∑ i, (a i)^2)) := Real.sqrt_le_sqrt h1
      _ = _ := hrhs
  refine ⟨?_, ?_⟩
  · rw [← hL2]
    exact Chapter1.exercise_1_11a (by norm_num) hp (hSsub.memLp hSm hp1)
  · calc Chapter1.lpNormRV (fun ω => ∑ i, Y i ω) p μ
        ≤ psi2Norm (fun ω => ∑ i, Y i ω) μ * Real.sqrt p :=
          hSsub.moment_bound hSm hp1
      _ ≤ (Real.sqrt 30 * K * Real.sqrt (∑ i, (a i)^2)) * Real.sqrt p :=
          mul_le_mul_of_nonneg_right hψS (Real.sqrt_nonneg p)
      _ = Real.sqrt 30 * K * Real.sqrt p * Real.sqrt (∑ i, (a i)^2) := by ring

/-! ## Book Proposition 2.7.6: the maximum of subgaussians -/

/-- The alternative proof bounds a Rademacher sum for `N ≥ 2`
subgaussian random variables — *not* necessarily independent — with
`‖Xᵢ‖_{ψ₂} ≤ K`, the maximum satisfies
`‖maxᵢ|Xᵢ|‖_{ψ₂} ≤ √(2 ln(2N))·K` (here `N = n + 2`).

Source location: Chapter 2, §2.7.3 (PDF pages 49–50). Explicit source
declaration. The Lean proof is the source's second proof: `𝔼e^{Z²/K²} ≤ 2N` by
replacing the maximum with the sum, then Jensen (in the equivalent Lyapunov form
`‖·‖_{L¹} ≤ ‖·‖_{L^{M²}}`, Exercise 1.11(a)) with `M = √(2ln(2N))` gives
`𝔼e^{Z²/(MK)²} ≤ (2N)^{1/M²} = e^{1/2} < 2`.

**Book Proposition 2.7.6.** -/
theorem psi2Norm_max_abs_le [IsProbabilityMeasure μ] {n : ℕ}
    {X : Fin (n + 2) → Ω → ℝ} (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, SubGaussian (X i) μ) {K : ℝ} (hK : 0 < K)
    (hKb : ∀ i, psi2Norm (X i) μ ≤ K) :
    SubGaussian (fun ω => Finset.univ.sup' Finset.univ_nonempty
      fun i => |X i ω|) μ ∧
    psi2Norm (fun ω => Finset.univ.sup' Finset.univ_nonempty
      fun i => |X i ω|) μ ≤ Real.sqrt (2 * Real.log (2*((n:ℝ)+2))) * K := by
  set Z : Ω → ℝ := fun ω => Finset.univ.sup' Finset.univ_nonempty
    fun i => |X i ω| with hZdef
  have hZm : Measurable Z := by
    have h1 : Measurable (Finset.univ.sup'
        (Finset.univ_nonempty (α := Fin (n + 2))) fun i ω => |X i ω|) :=
      Finset.measurable_sup' _ fun i _ => continuous_abs.measurable.comp (hXm i)
    have h2 : (Finset.univ.sup' (Finset.univ_nonempty (α := Fin (n + 2)))
        fun i ω => |X i ω|) = Z := by
      funext ω
      simp only [hZdef, Finset.sup'_apply]
    rwa [h2] at h1
  have hcast : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  have hN4 : (4:ℝ) ≤ 2*((n:ℝ)+2) := by linarith
  have hlogN : (0:ℝ) < Real.log (2*((n:ℝ)+2)) := Real.log_pos (by linarith)
  set M : ℝ := Real.sqrt (2 * Real.log (2*((n:ℝ)+2))) with hMdef
  have hMpos : 0 < M := Real.sqrt_pos.mpr (by linarith)
  have hMsq : M^2 = 2 * Real.log (2*((n:ℝ)+2)) := by
    rw [hMdef]
    exact Real.sq_sqrt (by linarith)
  have hM1 : 1 ≤ M := by
    rw [hMdef, show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    apply Real.sqrt_le_sqrt
    have hln4 : (1:ℝ) ≤ Real.log 4 := by
      rw [show (4:ℝ) = 2^(2:ℕ) from by norm_num, Real.log_pow]
      push_cast
      nlinarith [Real.log_two_gt_d9]
    have hmono : Real.log 4 ≤ Real.log (2*((n:ℝ)+2)) :=
      (Real.log_le_log_iff (by norm_num) (by linarith)).mpr hN4
    linarith
  have hq0 : (0:ℝ) < M^2 := by positivity
  have hq1 : (1:ℝ) ≤ M^2 := by nlinarith [hM1]
  -- Step 1: `𝔼 e^{Z²/K²} ≤ 2N` (maximum replaced by the sum)
  have hstep1 : psi2MGF Z μ K ≤ ENNReal.ofReal (2*((n:ℝ)+2)) := by
    unfold psi2MGF
    have hptw : ∀ ω, ENNReal.ofReal (Real.exp ((Z ω)^2 / K^2))
        ≤ ∑ i, ENNReal.ofReal (Real.exp ((X i ω)^2 / K^2)) := by
      intro ω
      obtain ⟨j, _, hjmax⟩ := Finset.exists_mem_eq_sup'
        (H := Finset.univ_nonempty (α := Fin (n + 2))) (fun i => |X i ω|)
      have hZj : (Z ω)^2 = (X j ω)^2 := by
        rw [hZdef]
        simp only
        rw [hjmax, sq_abs]
      rw [hZj]
      exact Finset.single_le_sum
        (f := fun i => ENNReal.ofReal (Real.exp ((X i ω)^2 / K^2)))
        (fun i _ => bot_le) (Finset.mem_univ j)
    calc ∫⁻ ω, ENNReal.ofReal (Real.exp ((Z ω)^2 / K^2)) ∂μ
        ≤ ∫⁻ ω, ∑ i, ENNReal.ofReal (Real.exp ((X i ω)^2 / K^2)) ∂μ :=
          lintegral_mono hptw
      _ = ∑ i, ∫⁻ ω, ENNReal.ofReal (Real.exp ((X i ω)^2 / K^2)) ∂μ :=
          lintegral_finsetSum Finset.univ fun i _ =>
            (measurable_exp.comp
              (((hXm i).pow_const 2).div_const _)).ennreal_ofReal
      _ ≤ ∑ _i : Fin (n + 2), (2:ℝ≥0∞) := Finset.sum_le_sum fun i _ =>
          psi2MGF_le_two_of_ge (hXm i).aemeasurable (hX i) (hKb i) hK
      _ = ENNReal.ofReal (2*((n:ℝ)+2)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul,
            show (2:ℝ) * ((n:ℝ)+2) = ((n + 2:ℕ):ℝ) * 2 from by push_cast; ring,
            ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
          norm_num
  obtain ⟨hWint, hWle⟩ := integrable_exp_sq_div_of_le hZm.aemeasurable
    (by positivity) hstep1
  -- the two exponentials are related by an `rpow`
  have hfW : ∀ ω, Real.exp ((Z ω)^2 / (M*K)^2)
      = (Real.exp ((Z ω)^2 / K^2)) ^ ((1:ℝ)/M^2) := by
    intro ω
    rw [← Real.exp_mul]
    congr 1
    rw [mul_pow]
    field_simp
  have hW1 : ∀ ω, 1 ≤ Real.exp ((Z ω)^2 / K^2) := by
    intro ω
    have h0 : 0 ≤ (Z ω)^2 / K^2 := by positivity
    linarith [Real.add_one_le_exp ((Z ω)^2 / K^2)]
  have hf_meas : AEStronglyMeasurable
      (fun ω => Real.exp ((Z ω)^2 / (M*K)^2)) μ :=
    (measurable_exp.comp
      ((hZm.pow_const 2).div_const _)).aestronglyMeasurable
  have hf_int : Integrable (fun ω => Real.exp ((Z ω)^2 / (M*K)^2)) μ := by
    refine hWint.mono' hf_meas (Filter.Eventually.of_forall fun ω => ?_)
    change ‖Real.exp ((Z ω)^2 / (M*K)^2)‖ ≤ Real.exp ((Z ω)^2 / K^2)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), hfW ω]
    calc (Real.exp ((Z ω)^2 / K^2)) ^ ((1:ℝ)/M^2)
        ≤ (Real.exp ((Z ω)^2 / K^2)) ^ (1:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (hW1 ω)
            (by rw [div_le_one hq0]; exact hq1)
      _ = Real.exp ((Z ω)^2 / K^2) := Real.rpow_one _
  -- Step 2 (Jensen/Lyapunov): `𝔼 e^{Z²/(MK)²} ≤ (𝔼 e^{Z²/K²})^{1/q} ≤ (2N)^{1/q}`
  have hMemLp : MemLp (fun ω => Real.exp ((Z ω)^2 / (M*K)^2))
      (ENNReal.ofReal (M^2)) μ := by
    refine ⟨hf_meas, ?_⟩
    have hqne : ENNReal.ofReal (M^2) ≠ 0 := by
      simpa [ENNReal.ofReal_eq_zero] using not_le.mpr hq0
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hqne ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hq0.le]
    refine ENNReal.rpow_lt_top_of_nonneg (by positivity) ?_
    have hcong : ∀ ω : Ω, ‖Real.exp ((Z ω)^2 / (M*K)^2)‖ₑ ^ (M^2)
        = ENNReal.ofReal (Real.exp ((Z ω)^2 / K^2)) := by
      intro ω
      rw [Real.enorm_eq_ofReal_abs, abs_of_pos (Real.exp_pos _),
        ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hq0.le, hfW ω,
        ← Real.rpow_mul (Real.exp_pos _).le,
        one_div_mul_cancel (ne_of_gt hq0), Real.rpow_one]
    rw [lintegral_congr hcong]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hstep1
  have hL1 : Chapter1.lpNormRV (fun ω => Real.exp ((Z ω)^2 / (M*K)^2)) 1 μ
      = ∫ ω, Real.exp ((Z ω)^2 / (M*K)^2) ∂μ := by
    have hcong : (fun ω => |Real.exp ((Z ω)^2 / (M*K)^2)| ^ (1:ℝ))
        =ᵐ[μ] fun ω => Real.exp ((Z ω)^2 / (M*K)^2) :=
      Filter.Eventually.of_forall fun ω => by
        change |Real.exp ((Z ω)^2 / (M*K)^2)| ^ (1:ℝ)
          = Real.exp ((Z ω)^2 / (M*K)^2)
        rw [Real.rpow_one, abs_of_pos (Real.exp_pos _)]
    rw [Chapter1.lpNormRV, integral_congr_ae hcong,
      show (1:ℝ)/1 = 1 from by norm_num, Real.rpow_one]
  have hLq : Chapter1.lpNormRV (fun ω => Real.exp ((Z ω)^2 / (M*K)^2)) (M^2) μ
      = (∫ ω, Real.exp ((Z ω)^2 / K^2) ∂μ) ^ ((1:ℝ)/M^2) := by
    have hcong : (fun ω => |Real.exp ((Z ω)^2 / (M*K)^2)| ^ (M^2))
        =ᵐ[μ] fun ω => Real.exp ((Z ω)^2 / K^2) :=
      Filter.Eventually.of_forall fun ω => by
        change |Real.exp ((Z ω)^2 / (M*K)^2)| ^ (M^2)
          = Real.exp ((Z ω)^2 / K^2)
        rw [abs_of_pos (Real.exp_pos _), hfW ω,
          ← Real.rpow_mul (Real.exp_pos _).le,
          one_div_mul_cancel (ne_of_gt hq0), Real.rpow_one]
    rw [Chapter1.lpNormRV, integral_congr_ae hcong]
  have harg : Real.log (2*((n:ℝ)+2)) * ((1:ℝ)/M^2) = 1/2 := by
    rw [hMsq]
    field_simp
  have hpow : (2*((n:ℝ)+2)) ^ ((1:ℝ)/M^2) = Real.exp (1/2) := by
    rw [Real.rpow_def_of_pos (by linarith : (0:ℝ) < 2*((n:ℝ)+2)), harg]
  have hexp_half : Real.exp (1/2) ≤ 2 := by
    rw [← Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 2)]
    nlinarith [Real.log_two_gt_d9]
  have hfinal : ∫ ω, Real.exp ((Z ω)^2 / (M*K)^2) ∂μ ≤ 2 := by
    have h1 := Chapter1.exercise_1_11a
      (X := fun ω => Real.exp ((Z ω)^2 / (M*K)^2)) (μ := μ)
      one_pos hq1 hMemLp
    rw [hL1, hLq] at h1
    calc ∫ ω, Real.exp ((Z ω)^2 / (M*K)^2) ∂μ
        ≤ (∫ ω, Real.exp ((Z ω)^2 / K^2) ∂μ) ^ ((1:ℝ)/M^2) := h1
      _ ≤ (2*((n:ℝ)+2)) ^ ((1:ℝ)/M^2) :=
          Real.rpow_le_rpow
            (integral_nonneg fun ω => (Real.exp_pos _).le) hWle
            (by positivity)
      _ = Real.exp (1/2) := hpow
      _ ≤ 2 := hexp_half
  have hgoal : psi2MGF Z μ (M*K) ≤ 2 := by
    have heq : psi2MGF Z μ (M*K)
        = ENNReal.ofReal (∫ ω, Real.exp ((Z ω)^2 / (M*K)^2) ∂μ) := by
      unfold psi2MGF
      exact (ofReal_integral_eq_lintegral_ofReal hf_int
        (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le)).symm
    rw [heq]
    calc ENNReal.ofReal (∫ ω, Real.exp ((Z ω)^2 / (M*K)^2) ∂μ)
        ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal hfinal
      _ = 2 := by norm_num
  exact ⟨⟨M*K, by positivity, hgoal⟩, psi2Norm_le _ (by positivity) hgoal⟩

/-- `‖maxᵢ|Xᵢ|‖_{ψ₂} ≤ 2√(ln N)·K` for `N = n + 2 ≥ 2`
(from the sharp form, since `2ln(2N) ≤ 4ln N` for `N ≥ 2`).

**Book Equation (2.21).** -/
theorem psi2Norm_max_abs_le' [IsProbabilityMeasure μ] {n : ℕ}
    {X : Fin (n + 2) → Ω → ℝ} (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, SubGaussian (X i) μ) {K : ℝ} (hK : 0 < K)
    (hKb : ∀ i, psi2Norm (X i) μ ≤ K) :
    psi2Norm (fun ω => Finset.univ.sup' Finset.univ_nonempty
      fun i => |X i ω|) μ ≤ 2 * Real.sqrt (Real.log ((n:ℝ)+2)) * K := by
  refine ((psi2Norm_max_abs_le hXm hX hK hKb).2).trans ?_
  have hcast : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  have hsplit : Real.log (2*((n:ℝ)+2)) = Real.log 2 + Real.log ((n:ℝ)+2) :=
    Real.log_mul (by norm_num) (by linarith)
  have hL2 : Real.log 2 ≤ Real.log ((n:ℝ)+2) :=
    (Real.log_le_log_iff (by norm_num) (by linarith)).mpr (by linarith)
  have hsqrt4 : Real.sqrt 4 = 2 := by
    rw [show (4:ℝ) = 2^2 from by norm_num,
      Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  have hle : Real.sqrt (2 * Real.log (2*((n:ℝ)+2)))
      ≤ 2 * Real.sqrt (Real.log ((n:ℝ)+2)) := by
    calc Real.sqrt (2 * Real.log (2*((n:ℝ)+2)))
        ≤ Real.sqrt (4 * Real.log ((n:ℝ)+2)) :=
          Real.sqrt_le_sqrt (by rw [hsplit]; linarith)
      _ = 2 * Real.sqrt (Real.log ((n:ℝ)+2)) := by
          rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4), hsqrt4]
  exact mul_le_mul_of_nonneg_right hle hK.le

/-- — the bound (2.21) for `maxᵢ Xᵢ` (without
absolute values); "the same bounds obviously hold", via `|maxᵢXᵢ| ≤ maxᵢ|Xᵢ|` and
ψ₂-monotonicity. Explicit constant `C = 2`.

**Book Proposition 2.7.6.** -/
theorem psi2Norm_max_le [IsProbabilityMeasure μ] {n : ℕ}
    {X : Fin (n + 2) → Ω → ℝ} (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, SubGaussian (X i) μ) {K : ℝ} (hK : 0 < K)
    (hKb : ∀ i, psi2Norm (X i) μ ≤ K) :
    SubGaussian (fun ω => Finset.univ.sup' Finset.univ_nonempty
      fun i => X i ω) μ ∧
    psi2Norm (fun ω => Finset.univ.sup' Finset.univ_nonempty
      fun i => X i ω) μ ≤ 2 * Real.sqrt (Real.log ((n:ℝ)+2)) * K := by
  obtain ⟨hZsub, _⟩ := psi2Norm_max_abs_le hXm hX hK hKb
  have hdom : ∀ᵐ ω ∂μ,
      |Finset.univ.sup' Finset.univ_nonempty fun i => X i ω|
      ≤ abs (Finset.univ.sup' Finset.univ_nonempty fun i => |X i ω|) := by
    refine Filter.Eventually.of_forall fun ω => ?_
    have h2 : (0:ℝ) ≤ Finset.univ.sup' Finset.univ_nonempty
        fun i => |X i ω| := by
      obtain ⟨j, hj⟩ := Finset.univ_nonempty (α := Fin (n + 2))
      exact le_trans (abs_nonneg (X j ω))
        (Finset.le_sup' (fun i => |X i ω|) hj)
    rw [abs_of_nonneg h2]
    exact abs_sup'_le Finset.univ_nonempty (fun i => X i ω)
  obtain ⟨hsub', hle'⟩ := psi2Norm_mono_abs hdom hZsub
  exact ⟨hsub', hle'.trans (psi2Norm_max_abs_le' hXm hX hK hKb)⟩

/-- `𝔼 maxᵢ Xᵢ ≤ CK√(ln N)` with the explicit constant `C = 2`
(for `N = n + 2 ≥ 2`; from (2.21) and the `p = 1` moment bound of
Proposition 2.6.6(ii)).

**Book Proposition 2.7.6.** -/
theorem expectation_max_le [IsProbabilityMeasure μ] {n : ℕ}
    {X : Fin (n + 2) → Ω → ℝ} (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, SubGaussian (X i) μ) {K : ℝ} (hK : 0 < K)
    (hKb : ∀ i, psi2Norm (X i) μ ≤ K) :
    ∫ ω, (Finset.univ.sup' Finset.univ_nonempty fun i => X i ω) ∂μ
      ≤ 2 * Real.sqrt (Real.log ((n:ℝ)+2)) * K := by
  obtain ⟨hsub, hle⟩ := psi2Norm_max_le hXm hX hK hKb
  set Z' : Ω → ℝ := fun ω => Finset.univ.sup' Finset.univ_nonempty
    fun i => X i ω with hZ'def
  have hZ'm : Measurable Z' := by
    have h1 : Measurable (Finset.univ.sup'
        (Finset.univ_nonempty (α := Fin (n + 2))) fun i ω => X i ω) :=
      Finset.measurable_sup' _ fun i _ => hXm i
    have h2 : (Finset.univ.sup' (Finset.univ_nonempty (α := Fin (n + 2)))
        fun i ω => X i ω) = Z' := by
      funext ω
      simp only [hZ'def, Finset.sup'_apply]
    rwa [h2] at h1
  have hint : Integrable Z' μ := by
    have h1 := hsub.memLp hZ'm.aemeasurable (le_refl (1:ℝ))
    rw [ENNReal.ofReal_one] at h1
    exact memLp_one_iff_integrable.mp h1
  have hintabs : Integrable (fun ω => |Z' ω|) μ := by
    have h1 := hint.norm
    simpa [Real.norm_eq_abs] using h1
  have hmb := hsub.moment_bound hZ'm.aemeasurable (le_refl (1:ℝ))
  have hL1 : Chapter1.lpNormRV Z' 1 μ = ∫ ω, |Z' ω| ∂μ := by
    have hcong : (fun ω => |Z' ω| ^ (1:ℝ)) =ᵐ[μ] fun ω => |Z' ω| :=
      Filter.Eventually.of_forall fun ω => Real.rpow_one _
    rw [Chapter1.lpNormRV, integral_congr_ae hcong,
      show (1:ℝ)/1 = 1 from by norm_num, Real.rpow_one]
  calc ∫ ω, Z' ω ∂μ
      ≤ ∫ ω, |Z' ω| ∂μ := integral_mono hint hintabs fun ω => le_abs_self _
    _ = Chapter1.lpNormRV Z' 1 μ := hL1.symm
    _ ≤ psi2Norm Z' μ * Real.sqrt 1 := hmb
    _ = psi2Norm Z' μ := by rw [Real.sqrt_one, mul_one]
    _ ≤ 2 * Real.sqrt (Real.log ((n:ℝ)+2)) * K := hle

end HDP

end Source_10_KhintchineMax

/-! ## Material formerly in `11_SubGaussianInterpolation.lean` -/

section Source_11_SubGaussianInterpolation

/-
Book Chapter 2, Exercise 2.35: interpolation between L1 and Linfinity for the
subgaussian norm, including the scaled-Bernoulli sharpness example.
-/

open MeasureTheory ProbabilityTheory Real Filter
open scoped ENNReal NNReal Topology

namespace HDP.Chapter2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Log-convex interpolation gives the sharp intermediate `Lᵖ` bound between two endpoint moments.

**Lean implementation helper.** -/
theorem exercise_2_35a_interpolation_sharp [IsProbabilityMeasure μ]
    {X : Ω → Real} (hXm : AEMeasurable X μ) {a b : Real}
    (ha : 0 < a) (hab : a ≤ b) (hXint : Integrable X μ)
    (hL1 : (∫ ω, |X ω| ∂μ) = a)
    (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ b) :
    SubGaussian X μ ∧
      psi2Norm X μ ≤ b / Real.sqrt (Real.log (1 + b / a)) := by
  have hb : 0 < b := ha.trans_le hab
  have hratio : 0 < b / a := div_pos hb ha
  let L : Real := Real.log (1 + b / a)
  have hL : 0 < L := by
    dsimp [L]
    exact Real.log_pos (by linarith)
  let K : Real := b / Real.sqrt L
  have hK : 0 < K := by dsimp [K]; positivity
  have hKs : K ^ 2 = b ^ 2 / L := by
    dsimp [K]
    rw [div_pow, Real.sq_sqrt hL.le]
  have hpoint : ∀ᵐ ω ∂μ,
      Real.exp (X ω ^ 2 / K ^ 2) ≤
        1 + (|X ω| / b) * (Real.exp L - 1) := by
    filter_upwards [hbound] with ω hω
    let θ : Real := |X ω| / b
    have hθ0 : 0 ≤ θ := by dsimp [θ]; positivity
    have hθ1 : θ ≤ 1 := by
      dsimp [θ]
      rw [div_le_one hb]
      exact hω
    have harg : X ω ^ 2 / K ^ 2 = θ ^ 2 * L := by
      rw [hKs]
      dsimp [θ]
      rw [← sq_abs (X ω)]
      field_simp [hb.ne', hL.ne']
    have hθsq : θ ^ 2 ≤ θ := by nlinarith
    have hfirst : Real.exp (X ω ^ 2 / K ^ 2) ≤ Real.exp (θ * L) := by
      apply Real.exp_le_exp.mpr
      rw [harg]
      exact mul_le_mul_of_nonneg_right hθsq hL.le
    have hchord : Real.exp (θ * L) ≤
        (1 - θ) * Real.exp 0 + θ * Real.exp L := by
      have hc := convexOn_exp.2 (Set.mem_univ (0 : Real))
        (Set.mem_univ L) (sub_nonneg.mpr hθ1) hθ0 (by ring : (1 - θ) + θ = 1)
      simpa [smul_eq_mul] using hc
    calc
      Real.exp (X ω ^ 2 / K ^ 2) ≤ Real.exp (θ * L) := hfirst
      _ ≤ (1 - θ) * Real.exp 0 + θ * Real.exp L := hchord
      _ = 1 + (|X ω| / b) * (Real.exp L - 1) := by
        rw [Real.exp_zero]
        dsimp [θ]
        ring
  have hRint : Integrable
      (fun ω => 1 + (|X ω| / b) * (Real.exp L - 1)) μ :=
    (integrable_const 1).add ((hXint.abs.div_const b).mul_const _)
  have hEmeas : AEStronglyMeasurable
      (fun ω => Real.exp (X ω ^ 2 / K ^ 2)) μ :=
    (measurable_exp.comp_aemeasurable
      ((hXm.pow_const 2).div_const _)).aestronglyMeasurable
  have hEint : Integrable (fun ω => Real.exp (X ω ^ 2 / K ^ 2)) μ := by
    refine hRint.mono' hEmeas ?_
    filter_upwards [hpoint] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hω
  have hRvalue : (∫ ω, 1 + (|X ω| / b) * (Real.exp L - 1) ∂μ) = 2 := by
    rw [integral_add (integrable_const 1) ((hXint.abs.div_const b).mul_const _),
      integral_const, integral_mul_const]
    have hdiv : (∫ ω, |X ω| / b ∂μ) = a / b := by
      simp_rw [div_eq_mul_inv]
      rw [integral_mul_const, hL1]
    rw [hdiv]
    have hexpL : Real.exp L = 1 + b / a := by
      dsimp [L]
      rw [Real.exp_log]
      linarith
    rw [hexpL]
    simp only [probReal_univ]
    field_simp
    ring
  have hEbound : (∫ ω, Real.exp (X ω ^ 2 / K ^ 2) ∂μ) ≤ 2 := by
    rw [← hRvalue]
    exact integral_mono_ae hEint hRint hpoint
  have hpsi : psi2MGF X μ K ≤ 2 := by
    unfold psi2MGF
    calc
      (∫⁻ ω, ENNReal.ofReal (Real.exp (X ω ^ 2 / K ^ 2)) ∂μ) =
          ENNReal.ofReal (∫ ω, Real.exp (X ω ^ 2 / K ^ 2) ∂μ) :=
        (ofReal_integral_eq_lintegral_ofReal hEint
          (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le)).symm
      _ ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal hEbound
      _ = 2 := by norm_num
  simpa [K, L] using
    (show SubGaussian X μ ∧ psi2Norm X μ ≤ K from
      ⟨⟨K, hK, hpsi⟩, psi2Norm_le X hK hpsi⟩)

/-- In the
printed denominator, with the explicit absolute
constant `C = √2`.

**Book Exercise 2.35.** -/
theorem exercise_2_35a_interpolation [IsProbabilityMeasure μ]
    {X : Ω → Real} (hXm : AEMeasurable X μ) {a b : Real}
    (ha : 0 < a) (hab : a ≤ b) (hXint : Integrable X μ)
    (hL1 : (∫ ω, |X ω| ∂μ) = a)
    (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ b) :
    SubGaussian X μ ∧
      psi2Norm X μ ≤
        Real.sqrt 2 * b / Real.sqrt (Real.log (2 * b / a)) := by
  obtain ⟨hsub, hsharp⟩ := exercise_2_35a_interpolation_sharp
    hXm ha hab hXint hL1 hbound
  refine ⟨hsub, hsharp.trans ?_⟩
  have hb : 0 < b := ha.trans_le hab
  have hr : 1 ≤ b / a := by
    rw [le_div_iff₀ ha]
    simpa using hab
  have hMpos : 0 < Real.log (2 * b / a) := by
    apply Real.log_pos
    calc
      (1 : Real) < 2 := by norm_num
      _ ≤ 2 * b / a := by
        rw [le_div_iff₀ ha]
        nlinarith
  have hLpos : 0 < Real.log (1 + b / a) :=
    Real.log_pos (by linarith)
  have harg : 2 * b / a ≤ (1 + b / a) ^ 2 := by
    have heq : 2 * b / a = 2 * (b / a) := by ring
    rw [heq]
    nlinarith [sq_nonneg (b / a)]
  have hlogle : Real.log (2 * b / a) ≤
      2 * Real.log (1 + b / a) := by
    calc
      Real.log (2 * b / a) ≤ Real.log ((1 + b / a) ^ 2) :=
        Real.log_le_log (by positivity) harg
      _ = 2 * Real.log (1 + b / a) := by
        rw [Real.log_pow]
        norm_num
  have hsqrt : Real.sqrt (Real.log (2 * b / a)) ≤
      Real.sqrt 2 * Real.sqrt (Real.log (1 + b / a)) := by
    calc
      Real.sqrt (Real.log (2 * b / a)) ≤
          Real.sqrt (2 * Real.log (1 + b / a)) :=
        Real.sqrt_le_sqrt hlogle
      _ = Real.sqrt 2 * Real.sqrt (Real.log (1 + b / a)) := by
        rw [Real.sqrt_mul (by norm_num : (0 : Real) ≤ 2)]
  rw [div_le_div_iff₀ (Real.sqrt_pos.mpr hLpos)
    (Real.sqrt_pos.mpr hMpos)]
  nlinarith [Real.sqrt_nonneg 2]

/-- Scaled Bernoulli variables
realize the interpolation scale exactly. Taking `p = a/b` and `|c| = b` gives
every `0 < a ≤ b`.

**Book Exercise 2.35.** -/
theorem exercise_2_35b_scaledBernoulli {B : Ω → Real}
    {p : Set.Icc (0 : Real) 1}
    (hB : HDP.IsBernoulli B p μ) (c : Real) :
    (∫ ω, |c * B ω| ∂μ) = |c| * (p : Real) ∧
    (∀ᵐ ω ∂μ, |c * B ω| ≤ |c|) ∧
    psi2Norm (fun ω => c * B ω) μ =
      |c| / Real.sqrt (Real.log (1 + 1 / (p : Real))) := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  have hL1 : (∫ ω, |c * B ω| ∂μ) = |c| * (p : Real) := by
    calc
      (∫ ω, |c * B ω| ∂μ) =
          (p : Real) * |c * 1| + (1 - (p : Real)) * |c * 0| :=
        hB.integral_comp (fun x : Real => |c * x|)
      _ = |c| * (p : Real) := by
        simp only [mul_one, mul_zero, abs_zero, mul_zero, add_zero]
        ring
  have htop : ∀ᵐ ω ∂μ, |c * B ω| ≤ |c| := by
    filter_upwards [hB.ae_mem] with ω hω
    rcases hω with hω | hω <;> rw [hω] <;> simp
  refine ⟨hL1, htop, ?_⟩
  rw [HDP.psi2Norm_const_mul, HDP.psi2Norm_bernoulli hB]
  ring

end HDP.Chapter2

end Source_11_SubGaussianInterpolation

/-! ## Material formerly in `12_SubGaussianMaximal.lean` -/

section Source_12_SubGaussianMaximal

/-!
# Logarithmically weighted maxima of subgaussian variables

This file proves the uniform finite-prefix formulation of Exercise 2.37.
The bound is independent of the prefix length and requires no independence.
-/

open MeasureTheory ProbabilityTheory Real Filter
open scoped ENNReal NNReal Topology

namespace HDP.Chapter2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Bounds `sum_range_inv_sq` above by `two`.

**Lean implementation helper.** -/
private lemma sum_range_inv_sq_le_two (N : Nat) :
    (∑ k ∈ Finset.range N, (1 : Real) / (k + 1 : Real) ^ 2) ≤ 2 := by
  have hstrong : ∀ N : Nat,
      (∑ k ∈ Finset.range N, (1 : Real) / (k + 1 : Real) ^ 2) ≤
        2 * (1 - 1 / (N + 1 : Real)) := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have hn1 : (0 : Real) < n + 1 := by positivity
      have hn2 : (0 : Real) < n + 2 := by positivity
      have hterm : (1 : Real) / (n + 1 : Real) ^ 2 ≤
          2 * (1 / (n + 1 : Real) - 1 / (n + 2 : Real)) := by
        field_simp [hn1.ne', hn2.ne']
        nlinarith
      calc
        (∑ k ∈ Finset.range n, (1 : Real) / (k + 1 : Real) ^ 2) +
            1 / (↑n + 1) ^ 2 ≤
            2 * (1 - 1 / (n + 1 : Real)) +
              2 * (1 / (n + 1 : Real) - 1 / (n + 2 : Real)) :=
          add_le_add ih hterm
        _ = 2 * (1 - 1 / ((↑(n + 1) : Real) + 1)) := by
          push_cast
          ring
  calc
    (∑ k ∈ Finset.range N, (1 : Real) / (k + 1 : Real) ^ 2) ≤
        2 * (1 - 1 / (N + 1 : Real)) := hstrong N
    _ ≤ 2 := by
      have : 0 ≤ 1 / (N + 1 : Real) := by positivity
      linarith

/-- Defines `logWeightedMax`, the log weighted max used in the surrounding construction.

**Lean implementation helper.** -/
noncomputable def logWeightedMax {n : Nat}
    (X : Fin (n + 2) → Ω → Real) : Ω → Real := fun ω =>
  Finset.univ.sup' Finset.univ_nonempty fun i =>
    |X i ω| / Real.sqrt (Real.log (2 * ((i : Nat) + 1 : Real)))

/-- Shows that `logWeight` is positive.

**Lean implementation helper.** -/
private lemma logWeight_pos {n : Nat} (i : Fin (n + 2)) :
    0 < Real.sqrt (Real.log (2 * ((i : Nat) + 1 : Real))) := by
  apply Real.sqrt_pos.mpr
  apply Real.log_pos
  have hi : (0 : Real) ≤ (i : Nat) := by positivity
  nlinarith

/-- Shows that `logWeightedMax` is measurable.

**Lean implementation helper.** -/
private lemma logWeightedMax_measurable {n : Nat}
    {X : Fin (n + 2) → Ω → Real} (hXm : ∀ i, Measurable (X i)) :
    Measurable (logWeightedMax X) := by
  unfold logWeightedMax
  have h1 : Measurable (Finset.univ.sup'
      (Finset.univ_nonempty (α := Fin (n + 2))) fun i ω =>
        |X i ω| / Real.sqrt (Real.log (2 * ((i : Nat) + 1 : Real)))) :=
    Finset.measurable_sup' _ fun i _ =>
      (continuous_abs.measurable.comp (hXm i)).div_const _
  have h2 : (Finset.univ.sup'
      (Finset.univ_nonempty (α := Fin (n + 2))) fun i ω =>
        |X i ω| / Real.sqrt (Real.log (2 * ((i : Nat) + 1 : Real)))) =
      (fun ω => Finset.univ.sup' Finset.univ_nonempty fun i =>
        |X i ω| / Real.sqrt (Real.log (2 * ((i : Nat) + 1 : Real)))) := by
    funext ω
    simp only [Finset.sup'_apply]
  rwa [h2] at h1

/-- Shows that `logWeightedMax` is nonnegative.

**Lean implementation helper.** -/
private lemma logWeightedMax_nonneg {n : Nat}
    (X : Fin (n + 2) → Ω → Real) (ω : Ω) : 0 ≤ logWeightedMax X ω := by
  obtain ⟨i, hi⟩ := Finset.univ_nonempty (α := Fin (n + 2))
  exact (div_nonneg (abs_nonneg _) (logWeight_pos i).le).trans
    (Finset.le_sup' (fun i =>
      |X i ω| / Real.sqrt (Real.log (2 * ((i : Nat) + 1 : Real)))) hi)

/-- Uniform
finite-prefix form. The constant is explicit and
independent of the prefix length.

**Book Exercise 2.37.** -/
theorem exercise_2_37_finite [IsProbabilityMeasure μ] {n : Nat}
    {X : Fin (n + 2) → Ω → Real} (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, HDP.SubGaussian (X i) μ) {K : Real} (hK : 0 < K)
    (hKb : ∀ i, HDP.psi2Norm (X i) μ ≤ K) :
    HDP.SubGaussian (logWeightedMax X) μ ∧
      HDP.psi2Norm (logWeightedMax X) μ ≤
        Real.sqrt 5 * (2 * K / Real.sqrt (Real.log 2)) := by
  let K₁ : Real := 2 * K / Real.sqrt (Real.log 2)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK₁ : 0 < K₁ := by dsimp [K₁]; positivity
  apply HDP.psi2Norm_le_of_tail_bound
    (logWeightedMax_measurable hXm).aemeasurable hK₁
  intro t ht
  by_cases htlarge : 2 * K < t
  · let s : Real := t ^ 2 / K ^ 2
    have hs4 : 4 < s := by
      dsimp [s]
      rw [lt_div_iff₀ (sq_pos_of_pos hK)]
      nlinarith
    let E : Fin (n + 2) → Set Ω := fun i =>
      {ω | t * Real.sqrt (Real.log (2 * ((i : Nat) + 1 : Real))) ≤ |X i ω|}
    have hsubset : {ω | t ≤ |logWeightedMax X ω|} ⊆
        ⋃ i ∈ (Finset.univ : Finset (Fin (n + 2))), E i := by
      intro ω hω
      change t ≤ |logWeightedMax X ω| at hω
      rw [abs_of_nonneg (logWeightedMax_nonneg X ω)] at hω
      obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup'
        (H := Finset.univ_nonempty (α := Fin (n + 2)))
        (fun i => |X i ω| /
          Real.sqrt (Real.log (2 * ((i : Nat) + 1 : Real))))
      have hj' : t * Real.sqrt (Real.log (2 * ((j : Nat) + 1 : Real))) ≤
          |X j ω| := by
        rw [logWeightedMax, hj] at hω
        rw [le_div_iff₀ (logWeight_pos j)] at hω
        exact hω
      exact Set.mem_iUnion_of_mem j (Set.mem_iUnion_of_mem (Finset.mem_univ j) hj')
    have htaili (i : Fin (n + 2)) : μ (E i) ≤ ENNReal.ofReal
        (2 * Real.exp (-s * Real.log (2 * ((i : Nat) + 1 : Real)))) := by
      have hpsi := HDP.psi2MGF_le_two_of_ge (hXm i).aemeasurable
        (hX i) (hKb i) hK
      have ht0 : 0 ≤ t * Real.sqrt
          (Real.log (2 * ((i : Nat) + 1 : Real))) :=
        mul_nonneg ht (logWeight_pos i).le
      have htail := HDP.subgaussian_iii_to_i (hXm i).aemeasurable hK hpsi ht0
      change μ (E i) ≤ _
      calc
        μ (E i) ≤ ENNReal.ofReal (2 * Real.exp
            (-(t * Real.sqrt (Real.log (2 * ((i : Nat) + 1 : Real)))) ^ 2 /
              K ^ 2)) := htail
        _ = ENNReal.ofReal
            (2 * Real.exp (-s * Real.log (2 * ((i : Nat) + 1 : Real)))) := by
          congr 2
          congr 1
          dsimp [s]
          rw [mul_pow, Real.sq_sqrt (Real.log_nonneg (by
            have hi : (0 : Real) ≤ (i : Nat) := by positivity
            nlinarith))]
          ring
    have hmeasure : μ {ω | t ≤ |logWeightedMax X ω|} ≤
        ∑ i : Fin (n + 2), ENNReal.ofReal
          (2 * Real.exp (-s * Real.log (2 * ((i : Nat) + 1 : Real)))) := by
      calc
        μ {ω | t ≤ |logWeightedMax X ω|} ≤
            μ (⋃ i ∈ (Finset.univ : Finset (Fin (n + 2))), E i) :=
          measure_mono hsubset
        _ ≤ ∑ i ∈ (Finset.univ : Finset (Fin (n + 2))), μ (E i) :=
          measure_biUnion_finset_le _ _
        _ ≤ ∑ i ∈ (Finset.univ : Finset (Fin (n + 2))), ENNReal.ofReal
            (2 * Real.exp (-s * Real.log (2 * ((i : Nat) + 1 : Real)))) :=
          Finset.sum_le_sum fun i _ => htaili i
        _ = ∑ i : Fin (n + 2), ENNReal.ofReal
            (2 * Real.exp (-s * Real.log (2 * ((i : Nat) + 1 : Real)))) := rfl
    refine hmeasure.trans ?_
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hterm (k : Nat) :
        2 * Real.exp (-s * Real.log (2 * (k + 1 : Real))) ≤
          2 * Real.exp (-s * Real.log 2) * (1 / (k + 1 : Real) ^ 2) := by
      have hk : (1 : Real) ≤ k + 1 := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
      have hlogk : 0 ≤ Real.log (k + 1 : Real) := Real.log_nonneg hk
      have hexp : Real.exp (-s * Real.log (k + 1 : Real)) ≤
          1 / (k + 1 : Real) ^ 2 := by
        calc
          Real.exp (-s * Real.log (k + 1 : Real)) ≤
              Real.exp (-2 * Real.log (k + 1 : Real)) := by
            apply Real.exp_le_exp.mpr
            nlinarith
          _ = 1 / (k + 1 : Real) ^ 2 := by
            rw [show -2 * Real.log (k + 1 : Real) =
                Real.log (((k + 1 : Real) ^ 2)⁻¹) by
              rw [Real.log_inv, Real.log_pow]
              norm_num]
            rw [Real.exp_log (inv_pos.mpr
              (pow_pos (by positivity : (0 : Real) < k + 1) 2))]
            rw [one_div]
      have hdecomp : Real.exp (-s * Real.log (2 * (k + 1 : Real))) =
          Real.exp (-s * Real.log 2) *
            Real.exp (-s * Real.log (k + 1 : Real)) := by
        rw [Real.log_mul (by norm_num : (2 : Real) ≠ 0)
          (by positivity : (k + 1 : Real) ≠ 0)]
        rw [mul_add, Real.exp_add]
      rw [hdecomp]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hexp
        (show 0 ≤ 2 * Real.exp (-s * Real.log 2) by positivity)
    have hsum : (∑ i : Fin (n + 2),
        2 * Real.exp (-s * Real.log (2 * ((i : Nat) + 1 : Real)))) ≤
        4 * Real.exp (-s * Real.log 2) := by
      calc
        (∑ i : Fin (n + 2),
            2 * Real.exp (-s * Real.log (2 * ((i : Nat) + 1 : Real)))) =
            ∑ k ∈ Finset.range (n + 2),
              2 * Real.exp (-s * Real.log (2 * (k + 1 : Real))) :=
          by
            simpa using (Fin.sum_univ_eq_sum_range
              (fun k : Nat =>
                2 * Real.exp (-s * Real.log (2 * (k + 1 : Real)))) (n + 2))
        _ ≤ ∑ k ∈ Finset.range (n + 2),
              (2 * Real.exp (-s * Real.log 2) *
                (1 / (k + 1 : Real) ^ 2)) :=
          Finset.sum_le_sum fun k _ => hterm k
        _ = 2 * Real.exp (-s * Real.log 2) *
            (∑ k ∈ Finset.range (n + 2), 1 / (k + 1 : Real) ^ 2) := by
          rw [Finset.mul_sum]
        _ ≤ 2 * Real.exp (-s * Real.log 2) * 2 :=
          mul_le_mul_of_nonneg_left (sum_range_inv_sq_le_two (n + 2))
            (mul_nonneg (by norm_num) (Real.exp_pos _).le)
        _ = 4 * Real.exp (-s * Real.log 2) := by ring
    have hfinal : 4 * Real.exp (-s * Real.log 2) ≤
        2 * Real.exp (-t ^ 2 / K₁ ^ 2) := by
      have hexpid : Real.exp (Real.log 2 - s * Real.log 2) =
          2 * Real.exp (-s * Real.log 2) := by
        rw [sub_eq_add_neg, Real.exp_add,
          Real.exp_log (by norm_num : (0 : Real) < 2)]
        congr 2
        ring
      have hexple : Real.exp (Real.log 2 - s * Real.log 2) ≤
          Real.exp (-s * Real.log 2 / 4) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      have hscale : t ^ 2 / K₁ ^ 2 = s * Real.log 2 / 4 := by
        dsimp [K₁, s]
        rw [div_pow, Real.sq_sqrt hlog2.le]
        field_simp [hK.ne', hlog2.ne']
        ring
      have hscale' : -t ^ 2 / K₁ ^ 2 = -s * Real.log 2 / 4 := by
        rw [show -t ^ 2 / K₁ ^ 2 = -(t ^ 2 / K₁ ^ 2) by ring, hscale]
        ring
      rw [hscale']
      rw [show 4 * Real.exp (-s * Real.log 2) =
          2 * (2 * Real.exp (-s * Real.log 2)) by ring, ← hexpid]
      exact mul_le_mul_of_nonneg_left hexple (by norm_num)
    exact hsum.trans hfinal
  · have htK : t ≤ 2 * K := le_of_not_gt htlarge
    calc
      μ {ω | t ≤ |logWeightedMax X ω|} ≤ 1 := prob_le_one
      _ ≤ ENNReal.ofReal (2 * Real.exp (-t ^ 2 / K₁ ^ 2)) := by
        rw [show (1 : ENNReal) = ENNReal.ofReal 1 by norm_num]
        apply ENNReal.ofReal_le_ofReal
        have hscale : t ^ 2 / K₁ ^ 2 ≤ Real.log 2 := by
          dsimp [K₁]
          rw [div_pow, Real.sq_sqrt hlog2.le]
          have ht2 : t ^ 2 ≤ (2 * K) ^ 2 := by
            nlinarith
          rw [div_le_iff₀ (div_pos (sq_pos_of_pos (by positivity)) hlog2)]
          field_simp [hK.ne', hlog2.ne']
          nlinarith
        have hexp : 1 / 2 ≤ Real.exp (-t ^ 2 / K₁ ^ 2) := by
          have hhalf : (1 / 2 : Real) = Real.exp (-Real.log 2) := by
            rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : Real) < 2)]
            norm_num
          rw [hhalf]
          apply Real.exp_le_exp.mpr
          have hneg := neg_le_neg hscale
          simpa only [neg_div] using hneg
        nlinarith

/-- In the safe
uniform-prefix formulation: the same absolute
constant works for every finite prefix, with no independence assumption.

**Book Exercise 2.35.** -/
theorem exercise_2_37 [IsProbabilityMeasure μ] {n : Nat}
    {X : Fin (n + 2) → Ω → Real} (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, HDP.SubGaussian (X i) μ) {K : Real} (hK : 0 < K)
    (hKb : ∀ i, HDP.psi2Norm (X i) μ ≤ K) :
    HDP.SubGaussian (logWeightedMax X) μ ∧
      HDP.psi2Norm (logWeightedMax X) μ ≤
        Real.sqrt 5 * (2 * K / Real.sqrt (Real.log 2)) :=
  exercise_2_37_finite hXm hX hK hKb

end HDP.Chapter2

end Source_12_SubGaussianMaximal

/-! ## Material formerly in `13_GaussianMaxima.lean` -/

section Source_13_GaussianMaxima

/-
Book Chapter 2, Exercises 2.35, 2.37, and 2.38: interpolation, a weighted
maximal inequality, and sharp Gaussian maxima.

This core module starts with the exact finite-Gaussian estimates from Exercise
2.38(a).  Their proofs use the Gaussian MGF and log-sum-exp directly, so no
independence assumption is needed.
-/




open MeasureTheory ProbabilityTheory Real Filter
open scoped ENNReal NNReal Topology

namespace HDP.Chapter2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The helper `of_hasLaw_standardGaussian` shows that every real random variable with the standard Gaussian law is integrable.

**Lean implementation helper.** -/
lemma integrable_of_hasLaw_standardGaussian {g : Ω → Real}
    (hg : HasLaw g (gaussianReal 0 1) μ) : Integrable g μ := by
  have hp := integrable_exp_mul_of_hasLaw_standardGaussian hg 1
  have hm := integrable_exp_mul_of_hasLaw_standardGaussian hg (-1)
  refine (hp.add hm).mono' hg.aemeasurable.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs]
  by_cases hω : 0 ≤ g ω
  · rw [abs_of_nonneg hω]
    calc
      g ω ≤ g ω + 1 := by linarith
      _ ≤ Real.exp (g ω) := Real.add_one_le_exp _
      _ ≤ Real.exp (1 * g ω) + Real.exp (-1 * g ω) := by
        norm_num
        positivity
  · rw [abs_of_neg (lt_of_not_ge hω)]
    calc
      -g ω ≤ -g ω + 1 := by linarith
      _ ≤ Real.exp (-g ω) := Real.add_one_le_exp _
      _ ≤ Real.exp (1 * g ω) + Real.exp (-1 * g ω) := by
        norm_num
        positivity

/-- Shows that `gaussian_fin_max` is measurable.

**Lean implementation helper.** -/
lemma gaussian_fin_max_measurable {n : Nat} {g : Fin (n + 2) → Ω → Real}
    (hgm : ∀ i, Measurable (g i)) :
    Measurable (fun ω => Finset.univ.sup' Finset.univ_nonempty fun i => g i ω) :=
by
  have h1 : Measurable (Finset.univ.sup'
      (Finset.univ_nonempty (α := Fin (n + 2))) fun i ω => g i ω) :=
    Finset.measurable_sup' _ fun i _ => hgm i
  have h2 : (Finset.univ.sup'
      (Finset.univ_nonempty (α := Fin (n + 2))) fun i ω => g i ω) =
      (fun ω => Finset.univ.sup' Finset.univ_nonempty fun i => g i ω) := by
    funext ω
    simp only [Finset.sup'_apply]
  rwa [h2] at h1

/-- Shows that `gaussian_fin_max` is integrable.

**Lean implementation helper.** -/
lemma gaussian_fin_max_integrable {n : Nat} {g : Fin (n + 2) → Ω → Real}
    (hgm : ∀ i, Measurable (g i))
    (hg : ∀ i, HasLaw (g i) (gaussianReal 0 1) μ) :
    Integrable (fun ω => Finset.univ.sup' Finset.univ_nonempty fun i => g i ω) μ := by
  let Z : Ω → Real := fun ω =>
    Finset.univ.sup' Finset.univ_nonempty fun i => g i ω
  have hZm : Measurable Z := gaussian_fin_max_measurable hgm
  have hsum : Integrable (fun ω => ∑ i, |g i ω|) μ :=
    integrable_finsetSum _ fun i _ => (integrable_of_hasLaw_standardGaussian (hg i)).abs
  refine hsum.mono' hZm.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs]
  calc
    |Z ω| ≤ Finset.univ.sup' Finset.univ_nonempty (fun i => |g i ω|) :=
      HDP.abs_sup'_le Finset.univ_nonempty _
    _ ≤ ∑ i, |g i ω| := Finset.sup'_le _ _ fun i _ =>
      Finset.single_le_sum (f := fun j => |g j ω|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ i)

/-- Shows that `exp_mul_gaussian_fin_max` is integrable.

**Lean implementation helper.** -/
lemma exp_mul_gaussian_fin_max_integrable {n : Nat} {g : Fin (n + 2) → Ω → Real}
    (hgm : ∀ i, Measurable (g i))
    (hg : ∀ i, HasLaw (g i) (gaussianReal 0 1) μ) {lam : Real} (_hlam : 0 < lam) :
    Integrable (fun ω => Real.exp
      (lam * Finset.univ.sup' Finset.univ_nonempty (fun i => g i ω))) μ := by
  let Z : Ω → Real := fun ω =>
    Finset.univ.sup' Finset.univ_nonempty fun i => g i ω
  have hZm : Measurable Z := gaussian_fin_max_measurable hgm
  have hsum : Integrable (fun ω => ∑ i, Real.exp (lam * g i ω)) μ :=
    integrable_finsetSum _ fun i _ =>
      integrable_exp_mul_of_hasLaw_standardGaussian (hg i) lam
  refine hsum.mono'
    (measurable_exp.comp (hZm.const_mul lam)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup'
    (H := Finset.univ_nonempty (α := Fin (n + 2))) (fun i => g i ω)
  rw [hj]
  exact Finset.single_le_sum (f := fun i => Real.exp (lam * g i ω))
    (fun i _ => (Real.exp_pos _).le) (Finset.mem_univ j)

/-- Sharp upper bound for a finite Gaussian maximum.

**Book Remark 2.7.7.** -/
theorem exercise_2_38a_max {n : Nat} {g : Fin (n + 2) → Ω → Real}
    (hgm : ∀ i, Measurable (g i))
    (hg : ∀ i, HasLaw (g i) (gaussianReal 0 1) μ) :
    (∫ ω, Finset.univ.sup' Finset.univ_nonempty (fun i => g i ω) ∂μ) ≤
      Real.sqrt (2 * Real.log (n + 2 : Real)) := by
  letI : IsProbabilityMeasure μ := (hg 0).isProbabilityMeasure
  let N : Real := n + 2
  have hn0 : (0 : Real) ≤ n := Nat.cast_nonneg n
  have hN : 1 < N := by dsimp [N]; linarith
  have hlogN : 0 < Real.log N := Real.log_pos hN
  let lam : Real := Real.sqrt (2 * Real.log N)
  have hlam : 0 < lam := by
    dsimp [lam]
    exact Real.sqrt_pos.mpr (mul_pos (by norm_num) hlogN)
  let Z : Ω → Real := fun ω =>
    Finset.univ.sup' Finset.univ_nonempty fun i => g i ω
  have hZint : Integrable Z μ := gaussian_fin_max_integrable hgm hg
  have hexpint : Integrable (fun ω => Real.exp (lam * Z ω)) μ :=
    exp_mul_gaussian_fin_max_integrable hgm hg hlam
  have hjensen : Real.exp (lam * ∫ ω, Z ω ∂μ) ≤
      ∫ ω, Real.exp (lam * Z ω) ∂μ := by
    have h := HDP.Chapter1.jensen_inequality convexOn_exp
      (hZint.const_mul lam) hexpint
    rwa [integral_const_mul] at h
  have hupper : (∫ ω, Real.exp (lam * Z ω) ∂μ) ≤
      N * Real.exp (lam ^ 2 / 2) := by
    calc
      (∫ ω, Real.exp (lam * Z ω) ∂μ) ≤
          ∫ ω, ∑ i, Real.exp (lam * g i ω) ∂μ := by
        apply integral_mono_ae hexpint
          (integrable_finsetSum _ fun i _ =>
            integrable_exp_mul_of_hasLaw_standardGaussian (hg i) lam)
        filter_upwards [] with ω
        obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup'
          (H := Finset.univ_nonempty (α := Fin (n + 2))) (fun i => g i ω)
        rw [show Z ω = g j ω by exact hj]
        exact Finset.single_le_sum (f := fun i => Real.exp (lam * g i ω))
          (fun i _ => (Real.exp_pos _).le)
          (Finset.mem_univ j)
      _ = ∑ i, ∫ ω, Real.exp (lam * g i ω) ∂μ :=
        integral_finsetSum _ fun i _ =>
          integrable_exp_mul_of_hasLaw_standardGaussian (hg i) lam
      _ = ∑ _i : Fin (n + 2), Real.exp (lam ^ 2 / 2) := by
        apply Finset.sum_congr rfl
        intro i _
        exact gaussian_mgf (hg i) lam
      _ = N * Real.exp (lam ^ 2 / 2) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        simp only [N]
        push_cast
        ring
  have hlog := Real.log_le_log (Real.exp_pos _) (hjensen.trans hupper)
  have hN0 : N ≠ 0 := ne_of_gt (zero_lt_one.trans hN)
  rw [Real.log_exp, Real.log_mul hN0 (Real.exp_ne_zero _), Real.log_exp] at hlog
  have hlamsq : lam ^ 2 = 2 * Real.log N := by
    dsimp [lam]
    rw [Real.sq_sqrt]
    exact mul_nonneg (by norm_num) hlogN.le
  have hresult : (∫ ω, Z ω ∂μ) ≤ lam := by
    rw [hlamsq] at hlog
    nlinarith
  simpa [Z, lam, N] using hresult

/-- Shows that `gaussian_fin_max_abs` is measurable.

**Lean implementation helper.** -/
lemma gaussian_fin_max_abs_measurable {n : Nat}
    {g : Fin (n + 2) → Ω → Real} (hgm : ∀ i, Measurable (g i)) :
    Measurable (fun ω =>
      Finset.univ.sup' Finset.univ_nonempty fun i => |g i ω|) := by
  have h1 : Measurable (Finset.univ.sup'
      (Finset.univ_nonempty (α := Fin (n + 2))) fun i ω => |g i ω|) :=
    Finset.measurable_sup' _ fun i _ =>
      continuous_abs.measurable.comp (hgm i)
  have h2 : (Finset.univ.sup'
      (Finset.univ_nonempty (α := Fin (n + 2))) fun i ω => |g i ω|) =
      (fun ω => Finset.univ.sup' Finset.univ_nonempty fun i => |g i ω|) := by
    funext ω
    simp only [Finset.sup'_apply]
  rwa [h2] at h1

/-- Shows that `gaussian_fin_max_abs` is integrable.

**Lean implementation helper.** -/
lemma gaussian_fin_max_abs_integrable {n : Nat}
    {g : Fin (n + 2) → Ω → Real} (hgm : ∀ i, Measurable (g i))
    (hg : ∀ i, HasLaw (g i) (gaussianReal 0 1) μ) :
    Integrable (fun ω =>
      Finset.univ.sup' Finset.univ_nonempty fun i => |g i ω|) μ := by
  let Z : Ω → Real := fun ω =>
    Finset.univ.sup' Finset.univ_nonempty fun i => |g i ω|
  have hZm : Measurable Z := gaussian_fin_max_abs_measurable hgm
  have hsum : Integrable (fun ω => ∑ i, |g i ω|) μ :=
    integrable_finsetSum _ fun i _ =>
      (integrable_of_hasLaw_standardGaussian (hg i)).abs
  refine hsum.mono' hZm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  have hZ0 : 0 ≤ Z ω := by
    obtain ⟨j, hj⟩ := Finset.univ_nonempty (α := Fin (n + 2))
    exact (abs_nonneg (g j ω)).trans
      (Finset.le_sup' (fun i => |g i ω|) hj)
  rw [Real.norm_eq_abs, abs_of_nonneg hZ0]
  exact Finset.sup'_le _ _ fun i _ =>
    Finset.single_le_sum (f := fun j => |g j ω|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ i)

/-- Shows that `exp_mul_gaussian_fin_max_abs` is integrable.

**Lean implementation helper.** -/
lemma exp_mul_gaussian_fin_max_abs_integrable {n : Nat}
    {g : Fin (n + 2) → Ω → Real} (hgm : ∀ i, Measurable (g i))
    (hg : ∀ i, HasLaw (g i) (gaussianReal 0 1) μ) {lam : Real} :
    Integrable (fun ω => Real.exp (lam *
      Finset.univ.sup' Finset.univ_nonempty (fun i => |g i ω|))) μ := by
  let Z : Ω → Real := fun ω =>
    Finset.univ.sup' Finset.univ_nonempty fun i => |g i ω|
  have hZm : Measurable Z := gaussian_fin_max_abs_measurable hgm
  have hsum : Integrable (fun ω => ∑ i,
      (Real.exp (lam * g i ω) + Real.exp (-lam * g i ω))) μ :=
    integrable_finsetSum _ fun i _ =>
      (integrable_exp_mul_of_hasLaw_standardGaussian (hg i) lam).add
        (integrable_exp_mul_of_hasLaw_standardGaussian (hg i) (-lam))
  refine hsum.mono'
    (measurable_exp.comp (hZm.const_mul lam)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup'
    (H := Finset.univ_nonempty (α := Fin (n + 2))) (fun i => |g i ω|)
  rw [show (Finset.univ.sup' Finset.univ_nonempty
      fun i => |g i ω|) = |g j ω| by exact hj]
  calc
    Real.exp (lam * |g j ω|) ≤
        Real.exp (lam * g j ω) + Real.exp (-lam * g j ω) := by
      by_cases hj0 : 0 ≤ g j ω
      · rw [abs_of_nonneg hj0]
        exact le_add_of_nonneg_right (Real.exp_pos _).le
      · rw [abs_of_neg (lt_of_not_ge hj0)]
        calc
          Real.exp (lam * -g j ω) = Real.exp (-lam * g j ω) := by
            congr 1
            ring
          _ ≤ Real.exp (lam * g j ω) + Real.exp (-lam * g j ω) :=
            le_add_of_nonneg_left (Real.exp_pos _).le
    _ ≤ ∑ i, (Real.exp (lam * g i ω) + Real.exp (-lam * g i ω)) :=
      Finset.single_le_sum
        (f := fun i => Real.exp (lam * g i ω) + Real.exp (-lam * g i ω))
        (fun _ _ => add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
        (Finset.mem_univ j)

/-- Sharp upper bound for the absolute Gaussian maximum.

**Book Remark 2.7.7.** -/
theorem exercise_2_38a_max_abs {n : Nat} {g : Fin (n + 2) → Ω → Real}
    (hgm : ∀ i, Measurable (g i))
    (hg : ∀ i, HasLaw (g i) (gaussianReal 0 1) μ) :
    (∫ ω, Finset.univ.sup' Finset.univ_nonempty
        (fun i => |g i ω|) ∂μ) ≤
      Real.sqrt (2 * Real.log (2 * (n + 2 : Real))) := by
  letI : IsProbabilityMeasure μ := (hg 0).isProbabilityMeasure
  let N : Real := n + 2
  have hn0 : (0 : Real) ≤ n := Nat.cast_nonneg n
  have hN : 1 < N := by dsimp [N]; linarith
  have htwoN : 1 < 2 * N := by nlinarith
  have hlog : 0 < Real.log (2 * N) := Real.log_pos htwoN
  let lam : Real := Real.sqrt (2 * Real.log (2 * N))
  have hlam : 0 < lam := by
    dsimp [lam]
    exact Real.sqrt_pos.mpr (mul_pos (by norm_num) hlog)
  let Z : Ω → Real := fun ω =>
    Finset.univ.sup' Finset.univ_nonempty fun i => |g i ω|
  have hZint : Integrable Z μ := gaussian_fin_max_abs_integrable hgm hg
  have hexpint : Integrable (fun ω => Real.exp (lam * Z ω)) μ :=
    exp_mul_gaussian_fin_max_abs_integrable hgm hg
  have hjensen : Real.exp (lam * ∫ ω, Z ω ∂μ) ≤
      ∫ ω, Real.exp (lam * Z ω) ∂μ := by
    have h := HDP.Chapter1.jensen_inequality convexOn_exp
      (hZint.const_mul lam) hexpint
    rwa [integral_const_mul] at h
  have hupper : (∫ ω, Real.exp (lam * Z ω) ∂μ) ≤
      (2 * N) * Real.exp (lam ^ 2 / 2) := by
    calc
      (∫ ω, Real.exp (lam * Z ω) ∂μ) ≤
          ∫ ω, ∑ i, (Real.exp (lam * g i ω) +
            Real.exp (-lam * g i ω)) ∂μ := by
        apply integral_mono_ae hexpint
          (integrable_finsetSum _ fun i _ =>
            (integrable_exp_mul_of_hasLaw_standardGaussian (hg i) lam).add
              (integrable_exp_mul_of_hasLaw_standardGaussian (hg i) (-lam)))
        filter_upwards [] with ω
        obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup'
          (H := Finset.univ_nonempty (α := Fin (n + 2))) (fun i => |g i ω|)
        rw [show Z ω = |g j ω| by exact hj]
        calc
          Real.exp (lam * |g j ω|) ≤
              Real.exp (lam * g j ω) + Real.exp (-lam * g j ω) := by
            by_cases hj0 : 0 ≤ g j ω
            · rw [abs_of_nonneg hj0]
              exact le_add_of_nonneg_right (Real.exp_pos _).le
            · rw [abs_of_neg (lt_of_not_ge hj0)]
              calc
                Real.exp (lam * -g j ω) = Real.exp (-lam * g j ω) := by
                  congr 1
                  ring
                _ ≤ Real.exp (lam * g j ω) + Real.exp (-lam * g j ω) :=
                  le_add_of_nonneg_left (Real.exp_pos _).le
          _ ≤ ∑ i, (Real.exp (lam * g i ω) +
              Real.exp (-lam * g i ω)) := Finset.single_le_sum
            (f := fun i => Real.exp (lam * g i ω) + Real.exp (-lam * g i ω))
            (fun _ _ => add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
            (Finset.mem_univ j)
      _ = ∑ i, ∫ ω, (Real.exp (lam * g i ω) +
          Real.exp (-lam * g i ω)) ∂μ :=
        integral_finsetSum _ fun i _ =>
          (integrable_exp_mul_of_hasLaw_standardGaussian (hg i) lam).add
            (integrable_exp_mul_of_hasLaw_standardGaussian (hg i) (-lam))
      _ = ∑ i, (∫ ω, Real.exp (lam * g i ω) ∂μ +
          ∫ ω, Real.exp (-lam * g i ω) ∂μ) := by
        apply Finset.sum_congr rfl
        intro i _
        exact integral_add
          (integrable_exp_mul_of_hasLaw_standardGaussian (hg i) lam)
          (integrable_exp_mul_of_hasLaw_standardGaussian (hg i) (-lam))
      _ = ∑ _i : Fin (n + 2), (2 * Real.exp (lam ^ 2 / 2)) := by
        apply Finset.sum_congr rfl
        intro i _
        have hp : (∫ ω, Real.exp (lam * g i ω) ∂μ) =
            Real.exp (lam ^ 2 / 2) := gaussian_mgf (hg i) lam
        have hm : (∫ ω, Real.exp (-lam * g i ω) ∂μ) =
            Real.exp ((-lam) ^ 2 / 2) := by
          calc
            (∫ ω, Real.exp (-lam * g i ω) ∂μ) =
                ∫ ω, Real.exp ((-lam) * g i ω) ∂μ := by
              apply integral_congr_ae
              filter_upwards [] with ω
              congr 1
            _ = Real.exp ((-lam) ^ 2 / 2) := gaussian_mgf (hg i) (-lam)
        rw [hp, hm]
        have hsq : (-lam) ^ 2 = lam ^ 2 := by ring
        rw [hsq]
        ring
      _ = (2 * N) * Real.exp (lam ^ 2 / 2) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        simp only [N]
        push_cast
        ring
  have hlogineq := Real.log_le_log (Real.exp_pos _) (hjensen.trans hupper)
  have htwoN0 : 2 * N ≠ 0 := ne_of_gt (zero_lt_one.trans htwoN)
  rw [Real.log_exp, Real.log_mul htwoN0 (Real.exp_ne_zero _),
    Real.log_exp] at hlogineq
  have hlamsq : lam ^ 2 = 2 * Real.log (2 * N) := by
    dsimp [lam]
    rw [Real.sq_sqrt]
    exact mul_nonneg (by norm_num) hlog.le
  have hresult : (∫ ω, Z ω ∂μ) ≤ lam := by
    rw [hlamsq] at hlogineq
    nlinarith
  simpa [Z, lam, N] using hresult

end HDP.Chapter2

end Source_13_GaussianMaxima

/-! ## Material formerly in `14_GaussianMaximaAsymptotic.lean` -/

section Source_14_GaussianMaximaAsymptotic

/-!
# Sharp asymptotics for independent Gaussian maxima

This module proves Book Exercise 2.38(b).  For an independent sequence of
standard Gaussian variables, the expected maximum and expected absolute
maximum of the first `n + 2` variables, divided by `sqrt (2 log (n + 2))`,
both tend to one.

The lower bound uses the Gaussian Mills-ratio estimate and the exact finite
intersection formula supplied by `iIndepFun`; the upper bounds are Exercise
2.38(a) from `GaussianMaxima`.
-/

open MeasureTheory ProbabilityTheory Real Filter
open scoped ENNReal NNReal Topology

namespace HDP.Chapter2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Defines `gaussianMaxSeq`, the gaussian max seq used in the surrounding construction.

**Lean implementation helper.** -/
noncomputable def gaussianMaxSeq (g : Nat → Ω → Real) (n : Nat) (ω : Ω) : Real :=
  (Finset.range (n + 2)).sup' (by simp) (fun i => g i ω)

/-- Defines `gaussianMaxAbsSeq`, the gaussian max abs seq used in the surrounding construction.

**Lean implementation helper.** -/
noncomputable def gaussianMaxAbsSeq (g : Nat → Ω → Real) (n : Nat) (ω : Ω) : Real :=
  (Finset.range (n + 2)).sup' (by simp) (fun i => |g i ω|)

/-- Identifies the maximum of the Gaussian sequence with `finSup`.

**Lean implementation helper.** -/
lemma gaussianMaxSeq_eq_finSup (g : Nat → Ω → Real) (n : Nat) (ω : Ω) :
    gaussianMaxSeq g n ω = Finset.univ.sup' Finset.univ_nonempty
      (fun i : Fin (n + 2) => g i ω) := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro i hi
    have hin : i < n + 2 := Finset.mem_range.mp hi
    exact Finset.le_sup' (fun j : Fin (n + 2) => g j ω)
      (Finset.mem_univ ⟨i, hin⟩)
  · apply Finset.sup'_le
    intro i _
    exact Finset.le_sup' (fun j : Nat => g j ω)
      (Finset.mem_range.mpr i.isLt)

/-- Identifies the maximum absolute Gaussian coordinate with `finSup`.

**Lean implementation helper.** -/
lemma gaussianMaxAbsSeq_eq_finSup (g : Nat → Ω → Real) (n : Nat) (ω : Ω) :
    gaussianMaxAbsSeq g n ω = Finset.univ.sup' Finset.univ_nonempty
      (fun i : Fin (n + 2) => |g i ω|) := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro i hi
    have hin : i < n + 2 := Finset.mem_range.mp hi
    exact Finset.le_sup' (fun j : Fin (n + 2) => |g j ω|)
      (Finset.mem_univ ⟨i, hin⟩)
  · apply Finset.sup'_le
    intro i _
    exact Finset.le_sup' (fun j : Nat => |g j ω|)
      (Finset.mem_range.mpr i.isLt)

/-- Shows that the maximum of the Gaussian sequence is strictly smaller than `iff`.

**Lean implementation helper.** -/
lemma gaussianMaxSeq_lt_iff {g : Nat → Ω → Real} {n : Nat} {t : Real} {ω : Ω} :
    gaussianMaxSeq g n ω < t ↔ ∀ i ∈ Finset.range (n + 2), g i ω < t := by
  simp [gaussianMaxSeq, Finset.sup'_lt_iff]

/-- Shows that the maximum of the Gaussian sequence is strictly smaller than `set`.

**Lean implementation helper.** -/
lemma gaussianMaxSeq_lt_set {g : Nat → Ω → Real} {n : Nat} {t : Real} :
    {ω | gaussianMaxSeq g n ω < t} =
      ⋂ i ∈ Finset.range (n + 2), g i ⁻¹' Set.Iio t := by
  ext ω
  simp [gaussianMaxSeq_lt_iff]

/-- Identifies the maximum of the Gaussian sequence quantity `lt_measure` with `pow`.

**Lean implementation helper.** -/
lemma gaussianMaxSeq_lt_measure_eq_pow {g : Nat → Ω → Real}
    (hg : ∀ i, HasLaw (g i) (gaussianReal 0 1) μ)
    (hi : iIndepFun g μ) (n : Nat) (t : Real) :
    μ.real {ω | gaussianMaxSeq g n ω < t} =
      ((gaussianReal 0 1).real (Set.Iio t)) ^ (n + 2) := by
  letI : IsProbabilityMeasure μ := (hg 0).isProbabilityMeasure
  have hprod := hi.measure_inter_preimage_eq_mul (Finset.range (n + 2))
    (sets := fun _ => Set.Iio t) (fun _ _ => measurableSet_Iio)
  rw [gaussianMaxSeq_lt_set]
  rw [Measure.real_def, hprod, ENNReal.toReal_prod]
  change (∏ i ∈ Finset.range (n + 2), μ.real (g i ⁻¹' Set.Iio t)) = _
  calc
    _ = ∏ _i ∈ Finset.range (n + 2),
        (gaussianReal 0 1).real (Set.Iio t) := by
      apply Finset.prod_congr rfl
      intro i _
      exact (hg i).measureReal_eq measurableSet_Iio
    _ = _ := by rw [Finset.prod_const, Finset.card_range]

/-- Identifies `gaussian_iio_prob` with `one_sub_tail`.

**Lean implementation helper.** -/
lemma gaussian_iio_prob_eq_one_sub_tail (t : Real) :
    (gaussianReal 0 1).real (Set.Iio t) =
      1 - (gaussianReal 0 1).real (Set.Ici t) := by
  have h := probReal_add_probReal_compl
    (μ := gaussianReal 0 1) (s := Set.Ici t) measurableSet_Ici
  rw [Set.compl_Ici] at h
  linarith

/-- Bounds the maximum of the Gaussian sequence quantity `lt_measure` above by `exp`.

**Lean implementation helper.** -/
lemma gaussianMaxSeq_lt_measure_le_exp {g : Nat → Ω → Real}
    (hg : ∀ i, HasLaw (g i) (gaussianReal 0 1) μ)
    (hi : iIndepFun g μ) (n : Nat) (t : Real) :
    μ.real {ω | gaussianMaxSeq g n ω < t} ≤
      Real.exp (-(n + 2 : Real) * (gaussianReal 0 1).real (Set.Ici t)) := by
  rw [gaussianMaxSeq_lt_measure_eq_pow hg hi,
    gaussian_iio_prob_eq_one_sub_tail]
  let p := (gaussianReal 0 1).real (Set.Ici t)
  have hp0 : 0 ≤ p := measureReal_nonneg
  have hp1 : p ≤ 1 := by
    simp [p]
  calc
    (1 - p) ^ (n + 2) ≤ (Real.exp (-p)) ^ (n + 2) :=
      pow_le_pow_left₀ (sub_nonneg.mpr hp1) (one_sub_le_exp_neg p) _
    _ = Real.exp (-(n + 2 : Real) * p) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring

/-- Defines `gaussianMaxScale`, the gaussian max scale used in the surrounding construction.

**Lean implementation helper.** -/
noncomputable def gaussianMaxScale (n : Nat) : Real :=
  Real.sqrt (2 * Real.log (n + 2 : Real))

/-- Defines `gaussianMaxThreshold`, the gaussian max threshold used in the surrounding construction.

**Lean implementation helper.** -/
noncomputable def gaussianMaxThreshold (c : Real) (n : Nat) : Real :=
  c * gaussianMaxScale n

/-- Proves the convergence statement for `log_nat_add_two`.

**Lean implementation helper.** -/
lemma tendsto_log_nat_add_two :
    Tendsto (fun n : Nat => Real.log (n + 2 : Real)) atTop atTop := by
  apply Real.tendsto_log_atTop.comp
  simpa only [Nat.cast_add, Nat.cast_ofNat] using
    (tendsto_natCast_atTop_atTop.atTop_add
      (tendsto_const_nhds (x := (2 : Real))))

/-- Shows that `gaussianMaxScale` is positive.

**Lean implementation helper.** -/
lemma gaussianMaxScale_pos (n : Nat) : 0 < gaussianMaxScale n := by
  unfold gaussianMaxScale
  apply Real.sqrt_pos.mpr
  apply mul_pos (by norm_num)
  apply Real.log_pos
  have hn : (0 : Real) ≤ n := Nat.cast_nonneg n
  linarith

/-- Proves the convergence statement for `gaussianMaxScale`.

**Lean implementation helper.** -/
lemma tendsto_gaussianMaxScale : Tendsto gaussianMaxScale atTop atTop := by
  apply Real.tendsto_sqrt_atTop.comp
  exact tendsto_log_nat_add_two.const_mul_atTop (by norm_num)

/-- Proves the convergence statement for `gaussian_mills_scale`.

**Lean implementation helper.** -/
lemma tendsto_gaussian_mills_scale {c : Real} (hc0 : 0 < c) (hc1 : c < 1) :
    Tendsto (fun n : Nat =>
      (n + 2 : Real) *
        ((gaussianMaxThreshold c n /
          (gaussianMaxThreshold c n ^ 2 + 1)) *
          stdGaussianDensity (gaussianMaxThreshold c n))) atTop atTop := by
  let a : Real := 1 - c ^ 2
  have ha : 0 < a := by
    dsimp [a]
    nlinarith
  let K : Real := c / (3 * Real.sqrt (2 * Real.pi))
  have hK : 0 < K := by
    dsimp [K]
    positivity
  have hbase : Tendsto (fun n : Nat =>
      K * (Real.exp (a * Real.log (n + 2 : Real)) /
        Real.log (n + 2 : Real))) atTop atTop := by
    have h := (tendsto_exp_mul_div_rpow_atTop 1 a ha).comp
      tendsto_log_nat_add_two
    have h' : Tendsto (fun n : Nat =>
        Real.exp (a * Real.log (n + 2 : Real)) /
          Real.log (n + 2 : Real)) atTop atTop := by
      simpa [Function.comp_def, Real.rpow_one] using h
    exact h'.const_mul_atTop hK
  refine tendsto_atTop_mono' _ ?_ hbase
  filter_upwards [tendsto_log_nat_add_two.eventually_ge_atTop 1] with n hL
  let N : Real := n + 2
  let L : Real := Real.log N
  let t : Real := gaussianMaxThreshold c n
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hN0 : 0 < N := by
    dsimp [N]
    positivity
  have hc0' : 0 ≤ c := hc0.le
  have hc1' : c ≤ 1 := hc1.le
  have hsqrt0 : 0 ≤ Real.sqrt (2 * L) := Real.sqrt_nonneg _
  have hsqrtsq : (Real.sqrt (2 * L)) ^ 2 = 2 * L := by
    rw [Real.sq_sqrt]
    positivity
  have hsqrt1 : 1 ≤ Real.sqrt (2 * L) := by
    rw [← sq_le_sq₀ (by norm_num) hsqrt0]
    nlinarith
  have ht0 : 0 < t := by
    dsimp [t, gaussianMaxThreshold, gaussianMaxScale, L, N]
    exact mul_pos hc0 (Real.sqrt_pos.mpr (by positivity))
  have ht_ge_c : c ≤ t := by
    dsimp [t, gaussianMaxThreshold, gaussianMaxScale, L, N]
    exact (le_mul_iff_one_le_right hc0).mpr hsqrt1
  have htsq : t ^ 2 = 2 * c ^ 2 * L := by
    dsimp [t, gaussianMaxThreshold, gaussianMaxScale, L, N]
    rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.log (n + 2 : Real))]
    ring
  have hc_sq : c ^ 2 ≤ 1 := by nlinarith
  have hden : t ^ 2 + 1 ≤ 3 * L := by
    rw [htsq]
    nlinarith
  have hden0 : 0 < t ^ 2 + 1 := by positivity
  have h3L0 : 0 < 3 * L := by positivity
  have hratio : c / (3 * L) ≤ t / (t ^ 2 + 1) := by
    rw [div_le_div_iff₀ h3L0 hden0]
    nlinarith
  have hexp : Real.exp (-t ^ 2 / 2) =
      Real.exp (-c ^ 2 * L) := by
    congr 1
    rw [htsq]
    ring
  have hNexp : N * Real.exp (-c ^ 2 * L) = Real.exp (a * L) := by
    rw [show N = Real.exp L by
      dsimp [L]
      exact (Real.exp_log hN0).symm, ← Real.exp_add]
    congr 1
    dsimp [a]
    ring
  change K * (Real.exp (a * L) / L) ≤
    N * ((t / (t ^ 2 + 1)) * stdGaussianDensity t)
  rw [stdGaussianDensity, hexp]
  rw [← hNexp]
  dsimp [K]
  have hsqrtpi : 0 < Real.sqrt (2 * Real.pi) := by positivity
  calc
    c / (3 * Real.sqrt (2 * Real.pi)) *
          (N * Real.exp (-c ^ 2 * L) / L) =
        (N * Real.exp (-c ^ 2 * L)) *
          (c / (3 * L)) * (1 / Real.sqrt (2 * Real.pi)) := by
      field_simp
    _ ≤ (N * Real.exp (-c ^ 2 * L)) *
          (t / (t ^ 2 + 1)) * (1 / Real.sqrt (2 * Real.pi)) := by
      gcongr
    _ = N * ((t / (t ^ 2 + 1)) *
          (Real.exp (-c ^ 2 * L) * (1 / Real.sqrt (2 * Real.pi)))) := by
      ring

/-- Proves the convergence statement for `gaussian_tail_scale`.

**Lean implementation helper.** -/
lemma tendsto_gaussian_tail_scale {c : Real} (hc0 : 0 < c) (hc1 : c < 1) :
    Tendsto (fun n : Nat =>
      (n + 2 : Real) * (gaussianReal 0 1).real
        (Set.Ici (gaussianMaxThreshold c n))) atTop atTop := by
  refine tendsto_atTop_mono' _ ?_ (tendsto_gaussian_mills_scale hc0 hc1)
  filter_upwards with n
  have hN : 0 ≤ (n + 2 : Real) := by positivity
  have ht : 0 < gaussianMaxThreshold c n := by
    unfold gaussianMaxThreshold
    apply mul_pos hc0
    apply Real.sqrt_pos.mpr
    have : (1 : Real) < n + 2 := by
      have hn : (0 : Real) ≤ n := Nat.cast_nonneg n
      linarith
    exact mul_pos (by norm_num) (Real.log_pos this)
  exact mul_le_mul_of_nonneg_left (gaussian_tail_lower_measure ht) hN

/-- Shows that the maximum of the Gaussian sequence is strictly smaller than `threshold_tendsto_zero`.

**Lean implementation helper.** -/
lemma gaussianMaxSeq_lt_threshold_tendsto_zero {g : Nat → Ω → Real}
    (hg : ∀ i, HasLaw (g i) (gaussianReal 0 1) μ)
    (hi : iIndepFun g μ) {c : Real} (hc0 : 0 < c) (hc1 : c < 1) :
    Tendsto (fun n : Nat =>
      μ.real {ω | gaussianMaxSeq g n ω < gaussianMaxThreshold c n})
      atTop (𝓝 0) := by
  have htail := tendsto_gaussian_tail_scale hc0 hc1
  have hexp' : Tendsto (fun n : Nat => Real.exp
      (-((n + 2 : Real) * (gaussianReal 0 1).real
        (Set.Ici (gaussianMaxThreshold c n))))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp htail)
  have hexp : Tendsto (fun n : Nat => Real.exp
      (-(n + 2 : Real) * (gaussianReal 0 1).real
        (Set.Ici (gaussianMaxThreshold c n)))) atTop (𝓝 0) := by
    simpa only [neg_mul] using hexp'
  refine squeeze_zero (fun _ => measureReal_nonneg) (fun n => ?_) hexp
  exact gaussianMaxSeq_lt_measure_le_exp hg hi n (gaussianMaxThreshold c n)

/-- Shows that the maximum of the Gaussian sequence is measurable.

**Lean implementation helper.** -/
lemma gaussianMaxSeq_measurable {g : Nat → Ω → Real}
    (hgm : ∀ i, Measurable (g i)) (n : Nat) :
    Measurable (gaussianMaxSeq g n) := by
  simpa only [← gaussianMaxSeq_eq_finSup] using
    (gaussian_fin_max_measurable (n := n) (g := fun i => g i) (fun i => hgm i))

/-- Shows that the maximum of the Gaussian sequence is integrable.

**Lean implementation helper.** -/
lemma gaussianMaxSeq_integrable {g : Nat → Ω → Real}
    (hgm : ∀ i, Measurable (g i))
    (hg : ∀ i, HasLaw (g i) (gaussianReal 0 1) μ) (n : Nat) :
    Integrable (gaussianMaxSeq g n) μ := by
  simpa only [← gaussianMaxSeq_eq_finSup] using
    (gaussian_fin_max_integrable (n := n) (g := fun i => g i)
      (fun i => hgm i) (fun i => hg i))

/-- Shows that the maximum absolute Gaussian coordinate is measurable.

**Lean implementation helper.** -/
lemma gaussianMaxAbsSeq_measurable {g : Nat → Ω → Real}
    (hgm : ∀ i, Measurable (g i)) (n : Nat) :
    Measurable (gaussianMaxAbsSeq g n) := by
  simpa only [← gaussianMaxAbsSeq_eq_finSup] using
    (gaussian_fin_max_abs_measurable (n := n) (g := fun i => g i)
      (fun i => hgm i))

/-- Shows that the maximum absolute Gaussian coordinate is integrable.

**Lean implementation helper.** -/
lemma gaussianMaxAbsSeq_integrable {g : Nat → Ω → Real}
    (hgm : ∀ i, Measurable (g i))
    (hg : ∀ i, HasLaw (g i) (gaussianReal 0 1) μ) (n : Nat) :
    Integrable (gaussianMaxAbsSeq g n) μ := by
  simpa only [← gaussianMaxAbsSeq_eq_finSup] using
    (gaussian_fin_max_abs_integrable (n := n) (g := fun i => g i)
      (fun i => hgm i) (fun i => hg i))

/-- Bounds the maximum of the Gaussian sequence above by the maximum absolute Gaussian coordinate.

**Lean implementation helper.** -/
lemma gaussianMaxSeq_le_gaussianMaxAbsSeq (g : Nat → Ω → Real) (n : Nat) (ω : Ω) :
    gaussianMaxSeq g n ω ≤ gaussianMaxAbsSeq g n ω := by
  apply Finset.sup'_le
  intro i hi
  exact (le_abs_self (g i ω)).trans
    (Finset.le_sup' (fun j : Nat => |g j ω|) hi)

/-- Bounds the maximum of the Gaussian sequence quantity `integral` above by `abs`.

**Lean implementation helper.** -/
lemma gaussianMaxSeq_integral_le_abs {g : Nat → Ω → Real}
    (hgm : ∀ i, Measurable (g i))
    (hg : ∀ i, HasLaw (g i) (gaussianReal 0 1) μ) (n : Nat) :
    (∫ ω, gaussianMaxSeq g n ω ∂μ) ≤
      ∫ ω, gaussianMaxAbsSeq g n ω ∂μ := by
  exact integral_mono (gaussianMaxSeq_integrable hgm hg n)
    (gaussianMaxAbsSeq_integrable hgm hg n)
    (gaussianMaxSeq_le_gaussianMaxAbsSeq g n)

/-- `gaussianMaxSeq_expectation_lower` bounds the expected finite Gaussian maximum below by `t * (1 - μ{max < t}) - ∫ |g 0|`.

**Lean implementation helper.** -/
lemma gaussianMaxSeq_expectation_lower {g : Nat → Ω → Real}
    (hgm : ∀ i, Measurable (g i))
    (hg : ∀ i, HasLaw (g i) (gaussianReal 0 1) μ)
    (n : Nat) (t : Real) :
    t * (1 - μ.real {ω | gaussianMaxSeq g n ω < t}) -
        (∫ ω, |g 0 ω| ∂μ) ≤
      ∫ ω, gaussianMaxSeq g n ω ∂μ := by
  letI : IsProbabilityMeasure μ := (hg 0).isProbabilityMeasure
  let Z : Ω → Real := gaussianMaxSeq g n
  let A : Set Ω := {ω | t ≤ Z ω}
  have hZm : Measurable Z := gaussianMaxSeq_measurable hgm n
  have hA : MeasurableSet A := hZm measurableSet_Ici
  have hZint : Integrable Z μ := gaussianMaxSeq_integrable hgm hg n
  have hg0int : Integrable (fun ω => |g 0 ω|) μ :=
    (integrable_of_hasLaw_standardGaussian (hg 0)).abs
  have hIint : Integrable (A.indicator (fun _ => t)) μ :=
    (integrable_const t).indicator hA
  have hmono : (∫ ω, A.indicator (fun _ => t) ω - |g 0 ω| ∂μ) ≤
      ∫ ω, Z ω ∂μ := by
    apply integral_mono (hIint.sub hg0int) hZint
    intro ω
    have hg0Z : g 0 ω ≤ Z ω := by
      dsimp [Z]
      exact Finset.le_sup' (fun i : Nat => g i ω) (by simp)
    change A.indicator (fun _ => t) ω - |g 0 ω| ≤ Z ω
    by_cases hω : ω ∈ A
    · simp only [Set.indicator_of_mem hω]
      exact (sub_le_self t (abs_nonneg _)).trans hω
    · simp only [Set.indicator_of_notMem hω, zero_sub]
      exact (neg_abs_le (g 0 ω)).trans hg0Z
  rw [integral_sub hIint hg0int] at hmono
  have hIA : (∫ ω, A.indicator (fun _ => t) ω ∂μ) = t * μ.real A := by
    rw [integral_indicator hA]
    simp [mul_comm]
  rw [hIA] at hmono
  have hAc : Aᶜ = {ω | Z ω < t} := by
    ext ω
    simp [A]
  have hprob : μ.real A = 1 - μ.real {ω | Z ω < t} := by
    have h := probReal_add_probReal_compl (μ := μ) hA
    rw [hAc] at h
    linarith
  rw [hprob] at hmono
  simpa [Z] using hmono

/-- Proves the convergence statement for the maximum of the Gaussian sequence quantity `lower_ratio`.

**Lean implementation helper.** -/
lemma tendsto_gaussianMaxSeq_lower_ratio {g : Nat → Ω → Real}
    (_hgm : ∀ i, Measurable (g i))
    (hg : ∀ i, HasLaw (g i) (gaussianReal 0 1) μ)
    (hi : iIndepFun g μ) {c : Real} (hc0 : 0 < c) (hc1 : c < 1) :
    Tendsto (fun n : Nat =>
      c * (1 - μ.real
        {ω | gaussianMaxSeq g n ω < gaussianMaxThreshold c n}) -
        (∫ ω, |g 0 ω| ∂μ) / gaussianMaxScale n) atTop (𝓝 c) := by
  have hq := gaussianMaxSeq_lt_threshold_tendsto_zero hg hi hc0 hc1
  have hM : Tendsto (fun n : Nat =>
      (∫ ω, |g 0 ω| ∂μ) / gaussianMaxScale n) atTop (𝓝 0) :=
    tendsto_gaussianMaxScale.const_div_atTop _
  have hc : Tendsto (fun _ : Nat => c) atTop (𝓝 c) := tendsto_const_nhds
  have h1 : Tendsto (fun _ : Nat => (1 : Real)) atTop (𝓝 1) := tendsto_const_nhds
  simpa using (hc.mul (h1.sub hq)).sub hM

/-- The normalized lower bound for maxima of independent Gaussians is controlled uniformly along the chosen sequence.

**Lean implementation helper.** -/
lemma gaussianMaxSeq_lower_ratio_le {g : Nat → Ω → Real}
    (hgm : ∀ i, Measurable (g i))
    (hg : ∀ i, HasLaw (g i) (gaussianReal 0 1) μ)
    (c : Real) (n : Nat) :
    c * (1 - μ.real
        {ω | gaussianMaxSeq g n ω < gaussianMaxThreshold c n}) -
        (∫ ω, |g 0 ω| ∂μ) / gaussianMaxScale n ≤
      (∫ ω, gaussianMaxSeq g n ω ∂μ) / gaussianMaxScale n := by
  have hlower := gaussianMaxSeq_expectation_lower hgm hg n
    (gaussianMaxThreshold c n)
  have hs := gaussianMaxScale_pos n
  rw [show c * (1 - μ.real
          {ω | gaussianMaxSeq g n ω < gaussianMaxThreshold c n}) -
        (∫ ω, |g 0 ω| ∂μ) / gaussianMaxScale n =
      (gaussianMaxThreshold c n *
          (1 - μ.real
            {ω | gaussianMaxSeq g n ω < gaussianMaxThreshold c n}) -
        (∫ ω, |g 0 ω| ∂μ)) / gaussianMaxScale n by
    simp only [gaussianMaxThreshold]
    field_simp [hs.ne']]
  exact (div_le_div_iff_of_pos_right hs).mpr hlower

/-- Bounds the maximum of the Gaussian sequence quantity `ratio` above by `one`.

**Lean implementation helper.** -/
lemma gaussianMaxSeq_ratio_le_one {g : Nat → Ω → Real}
    (hgm : ∀ i, Measurable (g i))
    (hg : ∀ i, HasLaw (g i) (gaussianReal 0 1) μ) (n : Nat) :
    (∫ ω, gaussianMaxSeq g n ω ∂μ) / gaussianMaxScale n ≤ 1 := by
  rw [div_le_iff₀ (gaussianMaxScale_pos n)]
  have h := exercise_2_38a_max (n := n) (g := fun i => g i)
    (fun i => hgm i) (fun i => hg i)
  simpa only [gaussianMaxScale, one_mul, ← gaussianMaxSeq_eq_finSup] using h

/-- For
independent standard Gaussians, the expected maximum
of the first `n+2` variables is asymptotic to `sqrt (2 log (n+2))`.

**Book Remark 2.7.7.** -/
theorem exercise_2_38b_max {g : Nat → Ω → Real}
    (hgm : ∀ i, Measurable (g i))
    (hg : ∀ i, HasLaw (g i) (gaussianReal 0 1) μ)
    (hi : iIndepFun g μ) :
    Tendsto (fun n : Nat =>
      (∫ ω, gaussianMaxSeq g n ω ∂μ) / gaussianMaxScale n)
      atTop (𝓝 1) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    by_cases ha0 : a < 0
    · let c : Real := 1 / 2
      have hc0 : 0 < c := by norm_num [c]
      have hc1 : c < 1 := by norm_num [c]
      have hac : a < c := ha0.trans (by norm_num [c])
      have hcLim := tendsto_gaussianMaxSeq_lower_ratio hgm hg hi hc0 hc1
      filter_upwards [hcLim.eventually (Ioi_mem_nhds hac)] with n hn
      exact hn.trans_le (gaussianMaxSeq_lower_ratio_le hgm hg c n)
    · let c : Real := (a + 1) / 2
      have hc0 : 0 < c := by dsimp [c]; linarith
      have hc1 : c < 1 := by dsimp [c]; linarith
      have hac : a < c := by dsimp [c]; linarith
      have hcLim := tendsto_gaussianMaxSeq_lower_ratio hgm hg hi hc0 hc1
      filter_upwards [hcLim.eventually (Ioi_mem_nhds hac)] with n hn
      exact hn.trans_le (gaussianMaxSeq_lower_ratio_le hgm hg c n)
  · intro b hb
    filter_upwards with n
    exact (gaussianMaxSeq_ratio_le_one hgm hg n).trans_lt hb

/-- Defines `gaussianMaxAbsUpperScale`, the gaussian max abs upper scale used in the surrounding construction.

**Lean implementation helper.** -/
noncomputable def gaussianMaxAbsUpperScale (n : Nat) : Real :=
  Real.sqrt (2 * Real.log (2 * (n + 2 : Real)))

/-- Proves the convergence statement for `gaussianMaxAbsUpperScale_ratio`.

**Lean implementation helper.** -/
lemma tendsto_gaussianMaxAbsUpperScale_ratio :
    Tendsto (fun n : Nat =>
      gaussianMaxAbsUpperScale n / gaussianMaxScale n) atTop (𝓝 1) := by
  have hlogdiv : Tendsto (fun n : Nat =>
      Real.log 2 / Real.log (n + 2 : Real)) atTop (𝓝 0) :=
    tendsto_log_nat_add_two.const_div_atTop _
  have hinner : Tendsto (fun n : Nat =>
      (2 * Real.log (2 * (n + 2 : Real))) /
        (2 * Real.log (n + 2 : Real))) atTop (𝓝 1) := by
    have hsum : Tendsto (fun n : Nat =>
        (1 : Real) + Real.log 2 / Real.log (n + 2 : Real))
        atTop (𝓝 ((1 : Real) + 0)) := tendsto_const_nhds.add hlogdiv
    have hsum' : Tendsto (fun n : Nat =>
        (1 : Real) + Real.log 2 / Real.log (n + 2 : Real))
        atTop (𝓝 1) := by simpa using hsum
    refine hsum'.congr' ?_
    filter_upwards with n
    have hlogN : Real.log (n + 2 : Real) ≠ 0 := by
      apply ne_of_gt
      apply Real.log_pos
      have hn : (0 : Real) ≤ n := Nat.cast_nonneg n
      linarith
    symm
    apply (div_eq_iff (mul_ne_zero (by norm_num) hlogN)).mpr
    · rw [Real.log_mul (by norm_num) (by positivity : (n + 2 : Real) ≠ 0)]
      field_simp [hlogN]
      ring
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hinner
  have heq : (fun n : Nat =>
      gaussianMaxAbsUpperScale n / gaussianMaxScale n) =
      (fun n : Nat => Real.sqrt
        ((2 * Real.log (2 * (n + 2 : Real))) /
          (2 * Real.log (n + 2 : Real)))) := by
    funext n
    unfold gaussianMaxAbsUpperScale gaussianMaxScale
    have hn : (0 : Real) ≤ n := Nat.cast_nonneg n
    have harg : (1 : Real) ≤ 2 * (n + 2 : Real) := by linarith
    have hnum : 0 ≤ 2 * Real.log (2 * (n + 2 : Real)) :=
      mul_nonneg (by norm_num) (Real.log_nonneg harg)
    exact (Real.sqrt_div hnum _).symm
  rw [heq]
  simpa [Function.comp_def] using hsqrt

/-- Bounds the maximum absolute Gaussian coordinate quantity `ratio` above by `upper`.

**Lean implementation helper.** -/
lemma gaussianMaxAbsSeq_ratio_le_upper {g : Nat → Ω → Real}
    (hgm : ∀ i, Measurable (g i))
    (hg : ∀ i, HasLaw (g i) (gaussianReal 0 1) μ) (n : Nat) :
    (∫ ω, gaussianMaxAbsSeq g n ω ∂μ) / gaussianMaxScale n ≤
      gaussianMaxAbsUpperScale n / gaussianMaxScale n := by
  apply (div_le_div_iff_of_pos_right (gaussianMaxScale_pos n)).mpr
  have h := exercise_2_38a_max_abs (n := n) (g := fun i => g i)
    (fun i => hgm i) (fun i => hg i)
  simpa only [gaussianMaxAbsUpperScale, ← gaussianMaxAbsSeq_eq_finSup] using h

/-- Bounds the maximum of the Gaussian sequence quantity `ratio` above by `abs`.

**Lean implementation helper.** -/
lemma gaussianMaxSeq_ratio_le_abs {g : Nat → Ω → Real}
    (hgm : ∀ i, Measurable (g i))
    (hg : ∀ i, HasLaw (g i) (gaussianReal 0 1) μ) (n : Nat) :
    (∫ ω, gaussianMaxSeq g n ω ∂μ) / gaussianMaxScale n ≤
      (∫ ω, gaussianMaxAbsSeq g n ω ∂μ) / gaussianMaxScale n :=
  (div_le_div_iff_of_pos_right (gaussianMaxScale_pos n)).mpr
    (gaussianMaxSeq_integral_le_abs hgm hg n)

/-- For
independent standard Gaussians, the expected absolute
maximum of the first `n+2` variables is asymptotic to `sqrt (2 log (n+2))`.

**Book Remark 2.7.7.** -/
theorem exercise_2_38b_max_abs {g : Nat → Ω → Real}
    (hgm : ∀ i, Measurable (g i))
    (hg : ∀ i, HasLaw (g i) (gaussianReal 0 1) μ)
    (hi : iIndepFun g μ) :
    Tendsto (fun n : Nat =>
      (∫ ω, gaussianMaxAbsSeq g n ω ∂μ) / gaussianMaxScale n)
      atTop (𝓝 1) := by
  exact (exercise_2_38b_max hgm hg hi).squeeze
    tendsto_gaussianMaxAbsUpperScale_ratio
    (gaussianMaxSeq_ratio_le_abs hgm hg)
    (gaussianMaxAbsSeq_ratio_le_upper hgm hg)

end HDP.Chapter2

end Source_14_GaussianMaximaAsymptotic

/-! ## Material formerly in `15_SubExponential.lean` -/

section Source_15_SubExponential

/-
Book Chapter 2, Section 2.8 (part 1): subexponential distributions — the ψ₁
functional, the ψ₁ norm, and the two structure lemmas.

8 (PDF pages 51–53).

Contents:
* the ψ₁ functional `𝔼exp(|X|/K)` (in `∫⁻` form, mirroring `psi2MGF`),
  `SubExponential` (Book Definition 2.8.4, taking property (iii) of
  Proposition 2.8.1 as defining, exactly as the source does for ψ₂), and the
  subexponential norm `‖X‖_{ψ₁}` (Book (2.25));
* well-definedness mirrors of §2.6: antitonicity, attainment of the infimum,
  behaviour on a.e.-zero variables;
* **Book Lemma 2.8.5**: `X` subgaussian ⟺ `X²` subexponential, with
  `‖X²‖_{ψ₁} = ‖X‖²_{ψ₂}` exactly;
* **Book Lemma 2.8.6**: a product of subgaussians is subexponential, with
  `‖XY‖_{ψ₁} ≤ ‖X‖_{ψ₂}‖Y‖_{ψ₂}` (the source proof: Young's inequality
  `|ab| ≤ a²/2 + b²/2` plus the AM–GM step `e^{(u+v)/2} ≤ (e^u + e^v)/2`;
  no independence required).  The source's proof concludes with a ψ₂ norm by a
  typo — see `Chapter2_source_issues.md` §2.8.

Remaining §2.8 items (Prop 2.8.1's equivalences with constants, Example 2.8.7,
centering (2.26) = Ex 2.44(a)) are tracked in `Chapter2_checkpoint.md`.
-/

open MeasureTheory ProbabilityTheory Real Filter
open scoped ENNReal NNReal Topology

namespace HDP

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-! ## The ψ₁ functional, subexponential random variables, and the ψ₁ norm -/

/-- The ψ₁ functional `𝔼 exp(|X|/K)` of the source (2.25), in unconditional `∫⁻` form
(value in `[0,∞]`). Implicit source definition, mirroring `psi2MGF`.

**Book Definition 2.8.4.** -/
noncomputable def psi1MGF (X : Ω → ℝ) (μ : Measure Ω) (K : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (Real.exp (|X ω| / K)) ∂μ

/-- First half): `X` is *subexponential* if
`𝔼exp(|X|/K) ≤ 2` for some `K > 0` (property (iii) of Proposition 2.8.1, which
the source takes as defining). Explicit source declaration.

**Book Definition 2.8.4.** -/
def SubExponential (X : Ω → ℝ) (μ : Measure Ω) : Prop :=
  ∃ K : ℝ, 0 < K ∧ psi1MGF X μ K ≤ 2

/-- Second half): the subexponential norm
`‖X‖_{ψ₁} = inf {K > 0: 𝔼exp(|X|/K) ≤ 2}`. Explicit source declaration.

**Book Definition 2.8.4.** -/
noncomputable def psi1Norm (X : Ω → ℝ) (μ : Measure Ω) : ℝ :=
  sInf {K : ℝ | 0 < K ∧ psi1MGF X μ K ≤ 2}

/-- Shows that the ψ₁ norm is nonnegative.

**Lean implementation helper.** -/
lemma psi1Norm_nonneg (X : Ω → ℝ) (μ : Measure Ω) : 0 ≤ psi1Norm X μ :=
  Real.sInf_nonneg fun _ hx => hx.1.le

/-- Antitonicity of the ψ₁ functional in `K` (the defining set of (2.25) is
upward closed; implicit well-definedness fact).

**Lean implementation helper.** -/
lemma psi1MGF_anti (X : Ω → ℝ) {K K' : ℝ} (hK : 0 < K) (hKK' : K ≤ K') :
    psi1MGF X μ K' ≤ psi1MGF X μ K := by
  refine lintegral_mono fun ω => ?_
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  exact div_le_div_of_nonneg_left (abs_nonneg _) hK hKK'

/-- If `K > 0` and `psi1MGF X μ K ≤ 2`, then `psi1Norm X μ ≤ K`; this is the bound recorded by `psi1Norm_le`.

**Lean implementation helper.** -/
lemma psi1Norm_le (X : Ω → ℝ) {K : ℝ} (hK : 0 < K) (h : psi1MGF X μ K ≤ 2) :
    psi1Norm X μ ≤ K :=
  csInf_le ⟨0, fun _ hx => hx.1.le⟩ ⟨hK, h⟩

/-- Any `K` strictly above the ψ₁ norm of a subexponential variable satisfies
the defining bound.

**Lean implementation helper.** -/
lemma psi1MGF_le_two_of_gt {X : Ω → ℝ} (h : SubExponential X μ) {K : ℝ}
    (hK : psi1Norm X μ < K) : psi1MGF X μ K ≤ 2 := by
  have hne : {K : ℝ | 0 < K ∧ psi1MGF X μ K ≤ 2}.Nonempty := h
  obtain ⟨K', hK'mem, hK'lt⟩ := exists_lt_of_csInf_lt hne hK
  exact (psi1MGF_anti X hK'mem.1 hK'lt.le).trans hK'mem.2

/-- The ψ₁ functional at `K = 0` (junk value: `|X|/0 = 0`, so the integrand is
`exp 0 = 1`).

**Lean implementation helper.** -/
lemma psi1MGF_zero [IsProbabilityMeasure μ] (X : Ω → ℝ) : psi1MGF X μ 0 = 1 := by
  unfold psi1MGF
  simp

/-- **Attainment of the infimum in (2.25)** (hidden well-definedness obligation
of Definition 2.8.4): for subexponential `X`, `𝔼 exp(|X|/‖X‖_{ψ₁}) ≤ 2`.
Implicit source claim; proved by monotone convergence along `Kₙ ↓ ‖X‖_{ψ₁}`,
mirroring `psi2MGF_psi2Norm_le_two`.

**Book Definition 2.8.4.** -/
theorem psi1MGF_psi1Norm_le_two [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXm : AEMeasurable X μ) (h : SubExponential X μ) :
    psi1MGF X μ (psi1Norm X μ) ≤ 2 := by
  set K₀ := psi1Norm X μ with hK₀
  rcases eq_or_lt_of_le (psi1Norm_nonneg X μ) with h0 | h0
  · rw [show K₀ = 0 from hK₀.trans h0.symm, psi1MGF_zero]
    norm_num
  set f : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    ENNReal.ofReal (Real.exp (|X ω| / (K₀ + 1/(n+1)))) with hf
  have hbound : ∀ n, ∫⁻ ω, f n ω ∂μ ≤ 2 := by
    intro n
    refine psi1MGF_le_two_of_gt h ?_
    have : (0:ℝ) < 1/((n:ℝ)+1) := by positivity
    linarith
  have hmeas : ∀ n, AEMeasurable (f n) μ := fun n =>
    (measurable_exp.comp_aemeasurable
      ((continuous_abs.measurable.comp_aemeasurable hXm).div_const _)).ennreal_ofReal
  have hmono : ∀ᵐ ω ∂μ, Monotone fun n => f n ω := by
    refine Filter.Eventually.of_forall fun ω n m hnm => ?_
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have h1 : (1:ℝ)/((m:ℝ)+1) ≤ 1/((n:ℝ)+1) := by
      apply one_div_le_one_div_of_le (by positivity)
      have : ((n:ℝ)+1) ≤ ((m:ℝ)+1) := by
        exact_mod_cast Nat.succ_le_succ hnm
      linarith
    have hKm : (0:ℝ) < K₀ + 1/((m:ℝ)+1) := by positivity
    exact div_le_div_of_nonneg_left (abs_nonneg _) hKm (by linarith)
  have htends : ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop
      (𝓝 (ENNReal.ofReal (Real.exp (|X ω| / K₀)))) := by
    refine Filter.Eventually.of_forall fun ω => ?_
    have h1 : Tendsto (fun n : ℕ => K₀ + 1/((n:ℝ)+1)) atTop (𝓝 K₀) := by
      have h2 : Tendsto (fun n : ℕ => 1/((n:ℝ)+1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      simpa using tendsto_const_nhds.add h2
    have h2 : Tendsto (fun n : ℕ => |X ω| / (K₀ + 1/((n:ℝ)+1))) atTop
        (𝓝 (|X ω| / K₀)) :=
      Tendsto.div tendsto_const_nhds h1 (ne_of_gt h0)
    exact (ENNReal.continuous_ofReal.tendsto _).comp
      ((Real.continuous_exp.tendsto _).comp h2)
  exact le_of_tendsto (lintegral_tendsto_of_tendsto_of_monotone hmeas hmono htends)
    (Filter.Eventually.of_forall hbound)

/-- If `‖X‖_{ψ₁} ≤ K` for a subexponential `X` and `K > 0`, then
`𝔼exp(|X|/K) ≤ 2` (mirror of `psi2MGF_le_two_of_ge`).

**Lean implementation helper.** -/
lemma psi1MGF_le_two_of_ge [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXm : AEMeasurable X μ) (h : SubExponential X μ) {K : ℝ}
    (hK : psi1Norm X μ ≤ K) (_hK0 : 0 < K) : psi1MGF X μ K ≤ 2 := by
  rcases eq_or_lt_of_le hK with heq | hlt
  · rw [← heq]
    exact psi1MGF_psi1Norm_le_two hXm h
  · exact psi1MGF_le_two_of_gt h hlt

/-- The ψ₁ functional of an a.e.-zero variable (mirror of `psi2MGF_of_ae_zero`).

**Lean implementation helper.** -/
lemma psi1MGF_of_ae_zero [IsProbabilityMeasure μ] {X : Ω → ℝ} (hz : X =ᵐ[μ] 0)
    (K : ℝ) : psi1MGF X μ K = 1 := by
  unfold psi1MGF
  have h1 : (fun ω => ENNReal.ofReal (Real.exp (|X ω| / K)))
      =ᵐ[μ] fun _ => (1:ℝ≥0∞) := by
    filter_upwards [hz] with ω hω
    rw [hω]
    simp
  rw [lintegral_congr_ae h1]
  simp

/-- Ψ₁ norm of an a.e.-zero variable.

**Lean implementation helper.** -/
lemma psi1Norm_eq_zero_of_ae_zero [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hz : X =ᵐ[μ] 0) : psi1Norm X μ = 0 := by
  refine le_antisymm ?_ (psi1Norm_nonneg X μ)
  by_contra hpos
  push Not at hpos
  have h2 := psi1Norm_le X (K := psi1Norm X μ / 2) (by linarith)
    (by rw [psi1MGF_of_ae_zero hz]; norm_num)
  linarith

/-- An a.e.-zero variable is subexponential.

**Lean implementation helper.** -/
lemma subExponential_of_ae_zero [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hz : X =ᵐ[μ] 0) : SubExponential X μ :=
  ⟨1, one_pos, by rw [psi1MGF_of_ae_zero hz]; norm_num⟩

/-! ## Integrability, tails, and the ψ₁ vanishing lemma -/

/-- Elementary inequality `|x| ≤ K·e^{|x|/K}` for `K > 0` (implicit integrability
step: a subexponential variable is integrable).

**Lean implementation helper.** -/
lemma abs_le_mul_exp_abs_div {x K : ℝ} (hK : 0 < K) :
    |x| ≤ K * Real.exp (|x|/K) := by
  have h0 : (0:ℝ) ≤ |x|/K := by positivity
  have h1 : |x|/K ≤ Real.exp (|x|/K) := by
    have := Real.add_one_le_exp (|x|/K)
    linarith
  calc |x| = K * (|x|/K) := by field_simp
    _ ≤ K * Real.exp (|x|/K) := mul_le_mul_of_nonneg_left h1 hK.le

/-- Bochner-form corollary of ψ₁ property (iii): `exp(|X|/K)` is integrable with
expectation at most `2`.

**Lean implementation helper.** -/
lemma integrable_exp_abs_div {X : Ω → ℝ} (hXm : AEMeasurable X μ) {K : ℝ}
    (h : psi1MGF X μ K ≤ 2) :
    Integrable (fun ω => Real.exp (|X ω| / K)) μ ∧
      ∫ ω, Real.exp (|X ω| / K) ∂μ ≤ 2 := by
  have hmeas : AEStronglyMeasurable (fun ω => Real.exp (|X ω| / K)) μ :=
    (measurable_exp.comp_aemeasurable
      ((continuous_abs.measurable.comp_aemeasurable hXm).div_const _)).aestronglyMeasurable
  have hlin : ∫⁻ ω, ‖Real.exp (|X ω| / K)‖ₑ ∂μ = psi1MGF X μ K := by
    unfold psi1MGF
    refine lintegral_congr fun ω => ?_
    rw [Real.enorm_eq_ofReal_abs, abs_of_pos (Real.exp_pos _)]
  have hfin : HasFiniteIntegral (fun ω => Real.exp (|X ω| / K)) μ := by
    rw [hasFiniteIntegral_iff_enorm, hlin]
    exact lt_of_le_of_lt h (by norm_num)
  refine ⟨⟨hmeas, hfin⟩, ?_⟩
  have h1 : ∫ ω, Real.exp (|X ω| / K) ∂μ = (psi1MGF X μ K).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le) hmeas]
    rfl
  rw [h1]
  calc (psi1MGF X μ K).toReal ≤ (2:ℝ≥0∞).toReal :=
        ENNReal.toReal_mono (by norm_num) h
    _ = 2 := by norm_num

/-- With `K₁ = K₃`:
`ℙ{|X| ≥ t} ≤ 2e^{−t/K}`.

**Book Proposition 2.8.1.** -/
theorem subexponential_iii_to_i [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXm : AEMeasurable X μ) {K : ℝ} (hK : 0 < K) (h : psi1MGF X μ K ≤ 2)
    {t : ℝ} (_ht : 0 ≤ t) :
    μ {ω | t ≤ |X ω|} ≤ ENNReal.ofReal (2 * Real.exp (-t/K)) := by
  set c : ℝ≥0∞ := ENNReal.ofReal (Real.exp (t/K)) with hc
  have hc0 : c ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hctop : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hf : AEMeasurable (fun ω => ENNReal.ofReal (Real.exp (|X ω|/K))) μ :=
    (measurable_exp.comp_aemeasurable
      ((continuous_abs.measurable.comp_aemeasurable hXm).div_const _)).ennreal_ofReal
  have hsub : {ω | t ≤ |X ω|}
      ⊆ {ω | c ≤ ENNReal.ofReal (Real.exp (|X ω|/K))} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    rw [hc]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    gcongr
  calc μ {ω | t ≤ |X ω|}
      ≤ μ {ω | c ≤ ENNReal.ofReal (Real.exp (|X ω|/K))} := measure_mono hsub
    _ ≤ (∫⁻ ω, ENNReal.ofReal (Real.exp (|X ω|/K)) ∂μ) / c :=
        meas_ge_le_lintegral_div hf hc0 hctop
    _ ≤ 2 / c := by
        gcongr
        exact h
    _ = ENNReal.ofReal (2 * Real.exp (-t/K)) := by
        rw [hc, ENNReal.div_eq_inv_mul,
          ← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← Real.exp_neg]
        rw [show (2:ℝ≥0∞) = ENNReal.ofReal 2 from by norm_num,
          ← ENNReal.ofReal_mul (Real.exp_pos _).le]
        congr 1
        rw [neg_div]
        ring

/-- A variable with vanishing ψ₁ norm is a.e. zero.

**Lean implementation helper.** -/
theorem ae_eq_zero_of_psi1Norm_eq_zero [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXm : AEMeasurable X μ) (h : SubExponential X μ)
    (h0 : psi1Norm X μ = 0) : X =ᵐ[μ] 0 := by
  have htail : ∀ t : ℝ, 0 < t → μ {ω | t ≤ |X ω|} = 0 := by
    intro t ht
    have hb : ∀ n : ℕ, μ {ω | t ≤ |X ω|}
        ≤ ENNReal.ofReal (2 * Real.exp (-t * ((n:ℝ)+1))) := by
      intro n
      have hKpos : (0:ℝ) < 1/((n:ℝ)+1) := by positivity
      have hKn : psi1MGF X μ (1/((n:ℝ)+1)) ≤ 2 :=
        psi1MGF_le_two_of_gt h (by rw [h0]; exact hKpos)
      have hbase := subexponential_iii_to_i hXm hKpos hKn ht.le
      have harg : -t/(1/((n:ℝ)+1)) = -t * ((n:ℝ)+1) := by
        rw [div_div_eq_mul_div, div_one]
      rwa [harg] at hbase
    have hlim : Tendsto
        (fun n : ℕ => ENNReal.ofReal (2 * Real.exp (-t * ((n:ℝ)+1))))
        atTop (𝓝 0) := by
      rw [show (0:ℝ≥0∞) = ENNReal.ofReal 0 from by simp]
      apply ENNReal.tendsto_ofReal
      have hinner : Tendsto (fun n : ℕ => -t * ((n:ℝ)+1)) atTop atBot := by
        refine (tendsto_const_mul_atBot_of_neg (by nlinarith : -t < 0)).mpr ?_
        exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
      have := (Real.tendsto_exp_atBot.comp hinner).const_mul (2:ℝ)
      simpa using this
    have hle := ge_of_tendsto hlim (Filter.Eventually.of_forall hb)
    exact nonpos_iff_eq_zero.mp hle
  have hunion : {ω | X ω ≠ 0} ⊆ ⋃ n : ℕ, {ω | 1/((n:ℝ)+1) ≤ |X ω|} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    have habs : 0 < |X ω| := abs_pos.mpr hω
    obtain ⟨n, hn⟩ := exists_nat_gt (1/|X ω|)
    refine Set.mem_iUnion.mpr ⟨n, ?_⟩
    simp only [Set.mem_setOf_eq]
    have hn1 : 1/|X ω| < (n:ℝ)+1 := hn.trans (by linarith)
    rw [div_lt_iff₀ habs] at hn1
    rw [div_le_iff₀ (by positivity : (0:ℝ) < (n:ℝ)+1)]
    nlinarith [hn1]
  have hnull : μ {ω | X ω ≠ 0} = 0 :=
    measure_mono_null hunion (measure_iUnion_null fun n => htail _ (by positivity))
  exact (MeasureTheory.ae_iff).mpr hnull

/-! ## Book Lemma 2.8.5: subexponential = subgaussian squared -/

/-- The ψ₁ functional of `X²` is the ψ₂ functional of `X` at `√K` (definitional
bridge; the pointwise identity `|X²|/K = X²/(√K)²`).

**Lean implementation helper.** -/
lemma psi1MGF_sq (X : Ω → ℝ) {K : ℝ} (hK : 0 ≤ K) :
    psi1MGF (fun ω => (X ω)^2) μ K = psi2MGF X μ (Real.sqrt K) := by
  unfold psi1MGF psi2MGF
  refine lintegral_congr fun ω => ?_
  rw [abs_of_nonneg (sq_nonneg _), Real.sq_sqrt hK]

/-- First half): `X` is subgaussian if and only if `X²` is
subexponential. Explicit source declaration ("this is easy to check").

**Book Lemma 2.8.5.** -/
theorem subExponential_sq_iff (X : Ω → ℝ) :
    SubExponential (fun ω => (X ω)^2) μ ↔ SubGaussian X μ := by
  constructor
  · rintro ⟨K, hK, hKb⟩
    refine ⟨Real.sqrt K, Real.sqrt_pos.mpr hK, ?_⟩
    rw [← psi1MGF_sq X hK.le]
    exact hKb
  · rintro ⟨K, hK, hKb⟩
    refine ⟨K^2, by positivity, ?_⟩
    rw [psi1MGF_sq X (by positivity), Real.sqrt_sq hK.le]
    exact hKb

/-- Second half): `‖X²‖_{ψ₁} = ‖X‖²_{ψ₂}` — an exact
identity, not an equivalence of norms. Explicit source declaration. The Lean
proof compares the defining sets of the two infima through `K ↔ √K`.

**Book Lemma 2.8.5.** -/
theorem psi1Norm_sq [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXm : AEMeasurable X μ) (h : SubGaussian X μ) :
    psi1Norm (fun ω => (X ω)^2) μ = (psi2Norm X μ)^2 := by
  have hsubexp : SubExponential (fun ω => (X ω)^2) μ :=
    (subExponential_sq_iff X).mpr h
  have hs := psi2Norm_nonneg X μ
  refine le_antisymm ?_ ?_
  · -- `ψ₁(X²) ≤ ψ₂(X)²`, using attainment at `ψ₂(X)`
    rcases eq_or_lt_of_le hs with h0 | h0
    · -- degenerate case: `ψ₂(X) = 0` forces `X = 0` a.e.
      have hz := ae_eq_zero_of_psi2Norm_eq_zero hXm h h0.symm
      have hzsq : (fun ω => (X ω)^2) =ᵐ[μ] 0 := by
        filter_upwards [hz] with ω hω
        simp [hω]
      rw [psi1Norm_eq_zero_of_ae_zero hzsq, ← h0]
      norm_num
    · refine psi1Norm_le _ (by positivity) ?_
      rw [psi1MGF_sq X (by positivity), Real.sqrt_sq hs]
      exact psi2MGF_psi2Norm_le_two hXm h
  · -- `ψ₂(X)² ≤ ψ₁(X²)`: every `K` above `ψ₁(X²)` dominates `ψ₂(X)²`
    have hkey : ∀ K : ℝ, psi1Norm (fun ω => (X ω)^2) μ < K →
        (psi2Norm X μ)^2 ≤ K := by
      intro K hltK
      have hKpos : 0 < K :=
        lt_of_le_of_lt (psi1Norm_nonneg _ μ) hltK
      have h1 : psi2MGF X μ (Real.sqrt K) ≤ 2 := by
        rw [← psi1MGF_sq X hKpos.le]
        exact psi1MGF_le_two_of_gt hsubexp hltK
      have h2 : psi2Norm X μ ≤ Real.sqrt K :=
        psi2Norm_le X (Real.sqrt_pos.mpr hKpos) h1
      calc (psi2Norm X μ)^2 ≤ (Real.sqrt K)^2 := by
            exact pow_le_pow_left₀ hs h2 2
        _ = K := Real.sq_sqrt hKpos.le
    exact le_of_forall_gt_imp_ge_of_dense hkey

/-! ## Book Lemma 2.8.6: products of subgaussians -/

/-- Halved ψ₂-bound in `∫⁻` form: if `𝔼exp(W²/K²) ≤ 2` then
`∫⁻ exp(W²/K²)/2 ≤ 1` (implicit arithmetic step of Lemma 2.8.6's proof).

**Book Lemma 2.8.6.** -/
lemma lintegral_exp_sq_half_le_one {W : Ω → ℝ} {K : ℝ}
    (h : psi2MGF W μ K ≤ 2) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp ((W ω)^2 / K^2) / 2) ∂μ ≤ 1 := by
  have h2I : (2:ℝ≥0∞) * ∫⁻ ω, ENNReal.ofReal (Real.exp ((W ω)^2 / K^2) / 2) ∂μ
      = psi2MGF W μ K := by
    rw [← lintegral_const_mul' _ _ (by norm_num : (2:ℝ≥0∞) ≠ ⊤)]
    unfold psi2MGF
    refine lintegral_congr fun ω => ?_
    rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    ring
  have h2I' : (∫⁻ ω, ENNReal.ofReal (Real.exp ((W ω)^2 / K^2) / 2) ∂μ) * 2
      = psi2MGF W μ K := by
    rw [mul_comm]
    exact h2I
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp ((W ω)^2 / K^2) / 2) ∂μ
      = (∫⁻ ω, ENNReal.ofReal (Real.exp ((W ω)^2 / K^2) / 2) ∂μ) * 2 / 2 :=
        (ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)).symm
    _ = psi2MGF W μ K / 2 := by rw [h2I']
    _ ≤ 2 / 2 := ENNReal.div_le_div_right h 2
    _ = 1 := ENNReal.div_self (by norm_num) (by norm_num)

/-- If `X` and `Y` are subgaussian (no independence
assumed), then `XY` is subexponential and `‖XY‖_{ψ₁} ≤ ‖X‖_{ψ₂}·‖Y‖_{ψ₂}`.

Source location: Chapter 2, §2.8 (PDF page 52). Explicit source declaration.
The Lean proof is the source's: Young's inequality `|ab| ≤ a²/2 + b²/2` applied
to `a = X/‖X‖_{ψ₂}`, `b = Y/‖Y‖_{ψ₂}`, then `e^{(u+v)/2} ≤ (e^u+e^v)/2` (AM–GM)
and the attained ψ₂ bounds of both factors. (The source's proof states its
conclusion with a ψ₂ norm — a typo for ψ₁; see the source-issue report.)

**Book Lemma 2.8.6.** -/
theorem psi1Norm_mul_le [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hXm : AEMeasurable X μ) (hYm : AEMeasurable Y μ)
    (hX : SubGaussian X μ) (hY : SubGaussian Y μ) :
    SubExponential (fun ω => X ω * Y ω) μ ∧
    psi1Norm (fun ω => X ω * Y ω) μ ≤ psi2Norm X μ * psi2Norm Y μ := by
  have hs := psi2Norm_nonneg X μ
  have hr := psi2Norm_nonneg Y μ
  -- degenerate cases: a vanishing factor
  rcases eq_or_lt_of_le hs with h0 | h0
  · have hz := ae_eq_zero_of_psi2Norm_eq_zero hXm hX h0.symm
    have hzm : (fun ω => X ω * Y ω) =ᵐ[μ] 0 := by
      filter_upwards [hz] with ω hω
      simp [hω]
    refine ⟨subExponential_of_ae_zero hzm, ?_⟩
    rw [psi1Norm_eq_zero_of_ae_zero hzm, ← h0]
    nlinarith
  rcases eq_or_lt_of_le hr with h0' | h0'
  · have hz := ae_eq_zero_of_psi2Norm_eq_zero hYm hY h0'.symm
    have hzm : (fun ω => X ω * Y ω) =ᵐ[μ] 0 := by
      filter_upwards [hz] with ω hω
      simp [hω]
    refine ⟨subExponential_of_ae_zero hzm, ?_⟩
    rw [psi1Norm_eq_zero_of_ae_zero hzm, ← h0']
    nlinarith
  -- main case: both ψ₂ norms positive
  set s := psi2Norm X μ with hsdef
  set r := psi2Norm Y μ with hrdef
  -- the pointwise inequality of the source's proof
  have hptw : ∀ ω, ENNReal.ofReal (Real.exp (|X ω * Y ω| / (s*r)))
      ≤ ENNReal.ofReal (Real.exp ((X ω)^2 / s^2) / 2)
        + ENNReal.ofReal (Real.exp ((Y ω)^2 / r^2) / 2) := by
    intro ω
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    -- Young: `|XY|/(sr) ≤ (X²/s² + Y²/r²)/2`
    have hyoung : |X ω * Y ω| / (s*r)
        ≤ ((X ω)^2/s^2 + (Y ω)^2/r^2) / 2 := by
      have hab : |X ω * Y ω| / (s*r) = (|X ω|/s) * (|Y ω|/r) := by
        rw [abs_mul]
        field_simp
      have hasq : (|X ω|/s)^2 = (X ω)^2/s^2 := by
        rw [div_pow, sq_abs]
      have hbsq : (|Y ω|/r)^2 = (Y ω)^2/r^2 := by
        rw [div_pow, sq_abs]
      rw [hab, ← hasq, ← hbsq]
      nlinarith [sq_nonneg (|X ω|/s - |Y ω|/r)]
    -- AM–GM for exponentials: `e^{(u+v)/2} ≤ (e^u + e^v)/2`
    have hamgm : Real.exp (((X ω)^2/s^2 + (Y ω)^2/r^2) / 2)
        ≤ Real.exp ((X ω)^2/s^2) / 2 + Real.exp ((Y ω)^2/r^2) / 2 := by
      set u := (X ω)^2/s^2
      set v := (Y ω)^2/r^2
      have hA : Real.exp (u/2) * Real.exp (u/2) = Real.exp u := by
        rw [← Real.exp_add]
        ring_nf
      have hB : Real.exp (v/2) * Real.exp (v/2) = Real.exp v := by
        rw [← Real.exp_add]
        ring_nf
      have hAB : Real.exp (u/2) * Real.exp (v/2) = Real.exp ((u+v)/2) := by
        rw [← Real.exp_add]
        ring_nf
      nlinarith [sq_nonneg (Real.exp (u/2) - Real.exp (v/2)),
        Real.exp_pos (u/2), Real.exp_pos (v/2)]
    calc Real.exp (|X ω * Y ω| / (s*r))
        ≤ Real.exp (((X ω)^2/s^2 + (Y ω)^2/r^2) / 2) :=
          Real.exp_le_exp.mpr hyoung
      _ ≤ Real.exp ((X ω)^2/s^2) / 2 + Real.exp ((Y ω)^2/r^2) / 2 := hamgm
  -- integrate: each half contributes at most 1
  have hXhalf : ∫⁻ ω, ENNReal.ofReal (Real.exp ((X ω)^2 / s^2) / 2) ∂μ ≤ 1 :=
    lintegral_exp_sq_half_le_one (psi2MGF_psi2Norm_le_two hXm hX)
  have hYhalf : ∫⁻ ω, ENNReal.ofReal (Real.exp ((Y ω)^2 / r^2) / 2) ∂μ ≤ 1 :=
    lintegral_exp_sq_half_le_one (psi2MGF_psi2Norm_le_two hYm hY)
  have hXmeas : AEMeasurable
      (fun ω => ENNReal.ofReal (Real.exp ((X ω)^2 / s^2) / 2)) μ :=
    ((measurable_exp.comp_aemeasurable
      ((hXm.pow_const 2).div_const _)).div_const _).ennreal_ofReal
  have hmgf : psi1MGF (fun ω => X ω * Y ω) μ (s*r) ≤ 2 := by
    unfold psi1MGF
    calc ∫⁻ ω, ENNReal.ofReal (Real.exp (|X ω * Y ω| / (s*r))) ∂μ
        ≤ ∫⁻ ω, (ENNReal.ofReal (Real.exp ((X ω)^2 / s^2) / 2)
            + ENNReal.ofReal (Real.exp ((Y ω)^2 / r^2) / 2)) ∂μ :=
          lintegral_mono hptw
      _ = (∫⁻ ω, ENNReal.ofReal (Real.exp ((X ω)^2 / s^2) / 2) ∂μ)
            + ∫⁻ ω, ENNReal.ofReal (Real.exp ((Y ω)^2 / r^2) / 2) ∂μ :=
          lintegral_add_left' hXmeas _
      _ ≤ 1 + 1 := add_le_add hXhalf hYhalf
      _ = 2 := by norm_num
  exact ⟨⟨s*r, by positivity, hmgf⟩, psi1Norm_le _ (by positivity) hmgf⟩

end HDP

end Source_15_SubExponential

/-! ## Material formerly in `16_SubExponentialNorm.lean` -/

section Source_16_SubExponentialNorm

/-
Book Chapter 2, §2.8 (part 3): ψ₁ norm properties and centering.

8 (PDF pages 51–53).

Contents:
* the ψ₁ triangle inequality (Exercise 2.42, ψ₁ part — stated in the source's
  §2.8 narrative; simpler than the ψ₂ case: `|a+b| ≤ |a|+|b|` plus the convexity
  chord of `exp` with weights `K/(K+L)`, `L/(K+L)`), and closure of
  `SubExponential` under sums;
* the exact ψ₁ norm of a constant, `‖c‖_{ψ₁} = |c|/ln 2` (ψ₁ analogue of
  Exercise 2.24(a); defining-set computation);
* the ψ₁ first-moment bound `|𝔼X| ≤ ‖X‖_{ψ₁}` (from `u ≤ e^u − 1` at the
  attained norm — the `p = 1` instance of Proposition 2.8.1(ii));
* **Book (2.26) = Exercise 2.44(a) (ψ₁ centering)** with the explicit absolute
  constant `C = 1 + 1/ln 2`:
  `‖X − 𝔼X‖_{ψ₁} ≤ (1 + 1/ln 2)‖X‖_{ψ₁}` (mirror of Lemma 2.7.8's proof).
-/


open MeasureTheory ProbabilityTheory Real Filter
open scoped ENNReal NNReal Topology Pointwise

namespace HDP

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-! ## The ψ₁ triangle inequality (Exercise 2.42, ψ₁ part) -/

/-- Core estimate of the ψ₁ triangle inequality: if `𝔼exp(|X|/K) ≤ 2` and
`𝔼exp(|Y|/L) ≤ 2` with `K, L > 0`, then `𝔼exp(|X+Y|/(K+L)) ≤ 2`, by
`|a+b| ≤ |a|+|b|` and the convexity chord of `exp`.

**Lean implementation helper.** -/
lemma psi1MGF_add_le {X Y : Ω → ℝ} (hXm : AEMeasurable X μ)
    (_hYm : AEMeasurable Y μ) {K L : ℝ} (hK : 0 < K) (hL : 0 < L)
    (hX : psi1MGF X μ K ≤ 2) (hY : psi1MGF Y μ L ≤ 2) :
    psi1MGF (fun ω => X ω + Y ω) μ (K + L) ≤ 2 := by
  set w₁ : ℝ := K/(K+L) with hw₁
  set w₂ : ℝ := L/(K+L) with hw₂
  have hKL : (0:ℝ) < K + L := by linarith
  have hw₁0 : 0 ≤ w₁ := by positivity
  have hw₂0 : 0 ≤ w₂ := by positivity
  have hwsum : w₁ + w₂ = 1 := by
    rw [hw₁, hw₂]
    field_simp
  -- pointwise: `exp(|x+y|/(K+L)) ≤ w₁ exp(|x|/K) + w₂ exp(|y|/L)`
  have hptw : ∀ ω, Real.exp (|X ω + Y ω|/(K+L))
      ≤ w₁ * Real.exp (|X ω|/K) + w₂ * Real.exp (|Y ω|/L) := by
    intro ω
    have hcomb : (|X ω| + |Y ω|)/(K+L) = w₁ * (|X ω|/K) + w₂ * (|Y ω|/L) := by
      rw [hw₁, hw₂]
      field_simp
    have habs : |X ω + Y ω|/(K+L) ≤ (|X ω| + |Y ω|)/(K+L) := by
      gcongr
      exact abs_add_le _ _
    have hconv := convexOn_exp.2 (Set.mem_univ (|X ω|/K))
      (Set.mem_univ (|Y ω|/L)) hw₁0 hw₂0 hwsum
    rw [smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul] at hconv
    calc Real.exp (|X ω + Y ω|/(K+L))
        ≤ Real.exp ((|X ω| + |Y ω|)/(K+L)) := Real.exp_le_exp.mpr habs
      _ = Real.exp (w₁ * (|X ω|/K) + w₂ * (|Y ω|/L)) := by rw [hcomb]
      _ ≤ w₁ * Real.exp (|X ω|/K) + w₂ * Real.exp (|Y ω|/L) := hconv
  -- integrate
  unfold psi1MGF
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp (|X ω + Y ω|/(K+L))) ∂μ
      ≤ ∫⁻ ω, (ENNReal.ofReal (w₁ * Real.exp (|X ω|/K))
          + ENNReal.ofReal (w₂ * Real.exp (|Y ω|/L))) ∂μ := by
        refine lintegral_mono fun ω => ?_
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        exact ENNReal.ofReal_le_ofReal (hptw ω)
    _ = (∫⁻ ω, ENNReal.ofReal (w₁ * Real.exp (|X ω|/K)) ∂μ)
        + ∫⁻ ω, ENNReal.ofReal (w₂ * Real.exp (|Y ω|/L)) ∂μ := by
        refine lintegral_add_left' ?_ _
        exact ((measurable_exp.comp_aemeasurable
          ((continuous_abs.measurable.comp_aemeasurable hXm).div_const _)).const_mul
            w₁).ennreal_ofReal
    _ ≤ ENNReal.ofReal w₁ * 2 + ENNReal.ofReal w₂ * 2 := by
        gcongr
        · calc ∫⁻ ω, ENNReal.ofReal (w₁ * Real.exp (|X ω|/K)) ∂μ
              = ENNReal.ofReal w₁ * psi1MGF X μ K := by
                unfold psi1MGF
                rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
                refine lintegral_congr fun ω => ?_
                rw [← ENNReal.ofReal_mul hw₁0]
            _ ≤ ENNReal.ofReal w₁ * 2 := mul_le_mul_right hX _
        · calc ∫⁻ ω, ENNReal.ofReal (w₂ * Real.exp (|Y ω|/L)) ∂μ
              = ENNReal.ofReal w₂ * psi1MGF Y μ L := by
                unfold psi1MGF
                rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
                refine lintegral_congr fun ω => ?_
                rw [← ENNReal.ofReal_mul hw₂0]
            _ ≤ ENNReal.ofReal w₂ * 2 := mul_le_mul_right hY _
    _ = 2 := by
        rw [show (2:ℝ≥0∞) = ENNReal.ofReal 2 from by norm_num,
          ← ENNReal.ofReal_mul hw₁0, ← ENNReal.ofReal_mul hw₂0,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        nlinarith [hwsum]

/-- For any (not necessarily
independent) `X`, `Y`: `‖X+Y‖_{ψ₁} ≤ ‖X‖_{ψ₁} + ‖Y‖_{ψ₁}`. Load-bearing for
the centering bound (2.26).

**Book Exercise 2.42.** -/
theorem psi1Norm_add_le [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hXm : AEMeasurable X μ) (hYm : AEMeasurable Y μ)
    (hX : SubExponential X μ) (hY : SubExponential Y μ) :
    psi1Norm (fun ω => X ω + Y ω) μ ≤ psi1Norm X μ + psi1Norm Y μ := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hKb : psi1MGF X μ (psi1Norm X μ + ε/2) ≤ 2 :=
    psi1MGF_le_two_of_gt hX (by linarith)
  have hLb : psi1MGF Y μ (psi1Norm Y μ + ε/2) ≤ 2 :=
    psi1MGF_le_two_of_gt hY (by linarith)
  have hKpos : (0:ℝ) < psi1Norm X μ + ε/2 := by
    linarith [psi1Norm_nonneg X μ]
  have hLpos : (0:ℝ) < psi1Norm Y μ + ε/2 := by
    linarith [psi1Norm_nonneg Y μ]
  have hsum := psi1MGF_add_le hXm hYm hKpos hLpos hKb hLb
  have hle := psi1Norm_le (μ := μ) (fun ω => X ω + Y ω)
    (by linarith : (0:ℝ) < (psi1Norm X μ + ε/2) + (psi1Norm Y μ + ε/2)) hsum
  linarith

/-- `X + Y` is subexponential when `X` and `Y` are (closure property implicit in
the §2.8 narrative).

**Book Section 2.8.** -/
theorem SubExponential.add [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hXm : AEMeasurable X μ) (hYm : AEMeasurable Y μ)
    (hX : SubExponential X μ) (hY : SubExponential Y μ) :
    SubExponential (fun ω => X ω + Y ω) μ := by
  obtain ⟨K, hK, hKb⟩ := hX
  obtain ⟨L, hL, hLb⟩ := hY
  exact ⟨K + L, by linarith, psi1MGF_add_le hXm hYm hK hL hKb hLb⟩

/-! ## The ψ₁ norm of a constant -/

/-- Ψ₁ analogue of Exercise 2.24(a): `‖c‖_{ψ₁} = |c|/ln 2` exactly (defining-set
computation).

**Book Exercise 2.24(a).** -/
theorem psi1Norm_const [IsProbabilityMeasure μ] (c : ℝ) :
    psi1Norm (fun _ => c) μ = |c| / Real.log 2 := by
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hMGF : ∀ K : ℝ, psi1MGF (fun _ => c) μ K
      = ENNReal.ofReal (Real.exp (|c|/K)) := by
    intro K
    unfold psi1MGF
    simp
  rcases eq_or_ne c 0 with rfl | hc
  · simp only [abs_zero, zero_div]
    have hset : {K : ℝ | 0 < K ∧ psi1MGF (fun _ => (0:ℝ)) μ K ≤ 2}
        = Set.Ioi 0 := by
      ext K
      simp only [Set.mem_setOf_eq, Set.mem_Ioi]
      refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
      rw [hMGF]
      norm_num
    rw [psi1Norm, hset]
    exact csInf_Ioi
  · have hcpos : 0 < |c| := abs_pos.mpr hc
    have hgoalpos : (0:ℝ) < |c| / Real.log 2 := by positivity
    have hmem : ∀ K : ℝ, 0 < K →
        (psi1MGF (fun _ => c) μ K ≤ 2 ↔ |c| / Real.log 2 ≤ K) := by
      intro K hK
      rw [hMGF]
      rw [show (2:ℝ≥0∞) = ENNReal.ofReal 2 from by norm_num]
      rw [ENNReal.ofReal_le_ofReal_iff (by norm_num)]
      rw [← Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 2)]
      rw [div_le_iff₀ hK, div_le_iff₀ hlog2, mul_comm (Real.log 2) K]
    have hset : {K : ℝ | 0 < K ∧ psi1MGF (fun _ => c) μ K ≤ 2}
        = Set.Ici (|c| / Real.log 2) := by
      ext K
      simp only [Set.mem_setOf_eq, Set.mem_Ici]
      constructor
      · intro ⟨hK, hb⟩
        exact (hmem K hK).mp hb
      · intro hK
        have hKpos : 0 < K := lt_of_lt_of_le hgoalpos hK
        exact ⟨hKpos, (hmem K hKpos).mpr hK⟩
    rw [psi1Norm, hset]
    exact csInf_Ici

/-! ## ψ₁ homogeneity -/

/-- Rescaling identity for the ψ₁ functional: `𝔼exp(|cX|/(|c|K)) = 𝔼exp(|X|/K)`.

**Lean implementation helper.** -/
lemma psi1MGF_const_mul {X : Ω → ℝ} {c : ℝ} (hc : c ≠ 0) (K : ℝ) :
    psi1MGF (fun ω => c * X ω) μ (|c| * K) = psi1MGF X μ K := by
  unfold psi1MGF
  refine lintegral_congr fun ω => ?_
  congr 2
  rw [abs_mul]
  rcases eq_or_ne K 0 with rfl | hK
  · norm_num
  · have habs : |c| ≠ 0 := abs_ne_zero.mpr hc
    field_simp

/-- Absolute homogeneity of the ψ₁ norm, `‖cX‖_{ψ₁} = |c|·‖X‖_{ψ₁}`.

**Book Exercise 2.42.** -/
theorem psi1Norm_const_mul [IsProbabilityMeasure μ] (X : Ω → ℝ) (c : ℝ) :
    psi1Norm (fun ω => c * X ω) μ = |c| * psi1Norm X μ := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp only [zero_mul, abs_zero]
    have hz : (fun _ : Ω => (0:ℝ)) =ᵐ[μ] 0 :=
      Filter.Eventually.of_forall fun ω => rfl
    have hset : {K : ℝ | 0 < K ∧ psi1MGF (fun _ : Ω => (0:ℝ)) μ K ≤ 2}
        = Set.Ioi 0 := by
      ext K
      simp only [Set.mem_setOf_eq, Set.mem_Ioi]
      exact ⟨fun hK => hK.1, fun hK =>
        ⟨hK, by rw [psi1MGF_of_ae_zero hz]; norm_num⟩⟩
    rw [psi1Norm, hset]
    exact csInf_Ioi
  · have habs : 0 < |c| := abs_pos.mpr hc
    have hset : {K : ℝ | 0 < K ∧ psi1MGF (fun ω => c * X ω) μ K ≤ 2}
        = (fun K => |c| * K) '' {K : ℝ | 0 < K ∧ psi1MGF X μ K ≤ 2} := by
      ext K
      simp only [Set.mem_setOf_eq, Set.mem_image]
      constructor
      · intro ⟨hK, hb⟩
        refine ⟨K/|c|, ⟨by positivity, ?_⟩, by field_simp⟩
        have := psi1MGF_const_mul (μ := μ) (X := X) hc (K/|c|)
        rw [show |c| * (K/|c|) = K from by field_simp] at this
        rwa [this] at hb
      · rintro ⟨K', ⟨hK', hb'⟩, rfl⟩
        refine ⟨by positivity, ?_⟩
        rw [psi1MGF_const_mul hc K']
        exact hb'
    rw [psi1Norm, hset, psi1Norm]
    rw [show (fun K => |c| * K) '' {K : ℝ | 0 < K ∧ psi1MGF X μ K ≤ 2}
      = |c| • {K : ℝ | 0 < K ∧ psi1MGF X μ K ≤ 2} from by
        rw [← Set.image_smul]
        rfl]
    rw [Real.sInf_smul_of_nonneg (abs_nonneg c)]
    rfl

/-- Scalar multiples of subexponential random variables are subexponential.

**Lean implementation helper.** -/
lemma SubExponential.const_mul [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (h : SubExponential X μ) (c : ℝ) :
    SubExponential (fun ω => c * X ω) μ := by
  rcases eq_or_ne c 0 with rfl | hc
  · refine ⟨1, one_pos, ?_⟩
    have hz : (fun ω => (0:ℝ) * X ω) =ᵐ[μ] 0 :=
      Filter.Eventually.of_forall fun ω => by simp
    rw [psi1MGF_of_ae_zero hz]
    norm_num
  · obtain ⟨K, hK, hKb⟩ := h
    refine ⟨|c| * K, by positivity, ?_⟩
    rw [psi1MGF_const_mul hc K]
    exact hKb

/-! ## The ψ₁ first-moment bound and centering (2.26) -/

/-- Ψ₁ first-moment bound: `|𝔼X| ≤ ‖X‖_{ψ₁}` (the `p = 1` instance of
Proposition 2.8.1(ii), via `u ≤ e^u − 1` at the attained norm).

**Book Proposition 2.8.1(ii).** -/
lemma abs_integral_le_psi1Norm [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXm : AEMeasurable X μ) (h : SubExponential X μ) :
    |∫ ω, X ω ∂μ| ≤ psi1Norm X μ := by
  have hXint : Integrable X μ := by
    obtain ⟨K, hK, hKb⟩ := h
    obtain ⟨hEint, _⟩ := integrable_exp_abs_div hXm hKb
    refine (hEint.const_mul K).mono' hXm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    exact abs_le_mul_exp_abs_div hK
  rcases eq_or_lt_of_le (psi1Norm_nonneg X μ) with h0 | h0
  · have hz := ae_eq_zero_of_psi1Norm_eq_zero hXm h h0.symm
    rw [integral_congr_ae hz]
    simp [← h0]
  · obtain ⟨hEint, hEle⟩ :=
      integrable_exp_abs_div hXm (psi1MGF_psi1Norm_le_two hXm h)
    have habs_int : Integrable (fun ω => |X ω|) μ := by
      have h1 := hXint.norm
      simpa [Real.norm_eq_abs] using h1
    have h1 : |∫ ω, X ω ∂μ| ≤ ∫ ω, |X ω| ∂μ := abs_integral_le_integral_abs
    have hptw : ∀ ω, |X ω|
        ≤ psi1Norm X μ * (Real.exp (|X ω|/psi1Norm X μ) - 1) := by
      intro ω
      have hu := Real.add_one_le_exp (|X ω|/psi1Norm X μ)
      have h2 : psi1Norm X μ * (|X ω|/psi1Norm X μ) = |X ω| := by
        field_simp
      nlinarith [hu, h0, h2]
    have hint2 : Integrable
        (fun ω => psi1Norm X μ * (Real.exp (|X ω|/psi1Norm X μ) - 1)) μ :=
      (hEint.sub (integrable_const 1)).const_mul _
    calc |∫ ω, X ω ∂μ| ≤ ∫ ω, |X ω| ∂μ := h1
      _ ≤ ∫ ω, psi1Norm X μ * (Real.exp (|X ω|/psi1Norm X μ) - 1) ∂μ :=
          integral_mono habs_int hint2 hptw
      _ = psi1Norm X μ * ((∫ ω, Real.exp (|X ω|/psi1Norm X μ) ∂μ) - 1) := by
          rw [integral_const_mul,
            integral_sub hEint (integrable_const 1), integral_const]
          simp
      _ ≤ psi1Norm X μ * 1 := by nlinarith [hEle, h0.le]
      _ = psi1Norm X μ := mul_one _

/-- With the explicit absolute
constant `C = 1 + 1/ln 2`:
`‖X − 𝔼X‖_{ψ₁} ≤ (1 + 1/ln 2)·‖X‖_{ψ₁}` for subexponential `X`.

Source location: Chapter 2, §2.8, display (2.26) (PDF page 53). Explicit source
declaration; the Lean proof mirrors Lemma 2.7.8: ψ₁ triangle inequality, the
constant computation `‖a‖_{ψ₁} = |a|/ln 2`, and the first-moment bound.

**Book Equation (2.26).** -/
theorem psi1Norm_centering [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXm : AEMeasurable X μ) (hX : SubExponential X μ) :
    SubExponential (fun ω => X ω - ∫ ω', X ω' ∂μ) μ ∧
    psi1Norm (fun ω => X ω - ∫ ω', X ω' ∂μ) μ
      ≤ (1 + 1/Real.log 2) * psi1Norm X μ := by
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set m : ℝ := ∫ ω', X ω' ∂μ with hm
  -- the constant `−m` is subexponential with `ψ₁ = |m|/ln 2`
  have hconst_sub : SubExponential (fun _ : Ω => -m) μ := by
    refine ⟨(|m|+1)/Real.log 2, by positivity, ?_⟩
    have hMGF : psi1MGF (fun _ : Ω => -m) μ ((|m|+1)/Real.log 2)
        = ENNReal.ofReal (Real.exp (|(-m)| / ((|m|+1)/Real.log 2))) := by
      unfold psi1MGF
      simp
    rw [hMGF, abs_neg]
    rw [show (2:ℝ≥0∞) = ENNReal.ofReal 2 from by norm_num]
    apply ENNReal.ofReal_le_ofReal
    rw [← Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 2)]
    rw [div_le_iff₀ (by positivity : (0:ℝ) < (|m|+1)/Real.log 2)]
    rw [mul_comm, div_mul_eq_mul_div, mul_comm, ← div_mul_eq_mul_div,
      div_self (ne_of_gt hlog2), one_mul]
    linarith [abs_nonneg m]
  have hconst_norm : psi1Norm (fun _ : Ω => -m) μ = |m|/Real.log 2 := by
    rw [psi1Norm_const, abs_neg]
  have hdecomp : (fun ω => X ω - m) = fun ω => X ω + (fun _ : Ω => -m) ω := by
    funext ω
    ring
  have htri := psi1Norm_add_le hXm (aemeasurable_const (b := -m)) hX hconst_sub
  have hmean_le : |m| ≤ psi1Norm X μ := abs_integral_le_psi1Norm hXm hX
  constructor
  · rw [show (fun ω => X ω - ∫ ω', X ω' ∂μ)
        = fun ω => X ω + (fun _ : Ω => -m) ω from hdecomp]
    exact SubExponential.add hXm (aemeasurable_const (b := -m)) hX hconst_sub
  · calc psi1Norm (fun ω => X ω - ∫ ω', X ω' ∂μ) μ
        = psi1Norm (fun ω => X ω + (fun _ : Ω => -m) ω) μ := by rw [hdecomp]
      _ ≤ psi1Norm X μ + psi1Norm (fun _ : Ω => -m) μ := htri
      _ = psi1Norm X μ + |m|/Real.log 2 := by rw [hconst_norm]
      _ ≤ psi1Norm X μ + psi1Norm X μ/Real.log 2 := by gcongr
      _ = (1 + 1/Real.log 2) * psi1Norm X μ := by ring

end HDP

end Source_16_SubExponentialNorm

/-! ## Material formerly in `17_OrliczExamples.lean` -/

section Source_17_OrliczExamples

/-
Book Exercise 2.42(b): the standard Young functions and their identification
with the book's `Lᵖ`, ψ₂, and ψ₁ interfaces.
-/



open MeasureTheory ProbabilityTheory Real Filter
open scoped ENNReal NNReal Topology

namespace HDP

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The power Young function used for `Lᵖ`, on its nonnegative domain.

**Lean implementation helper.** -/
noncomputable def orliczLp (p t : ℝ) : ℝ := t ^ p

/-- The Young function defining the ψ₁ norm.

**Lean implementation helper.** -/
noncomputable def orliczPsi1 (t : ℝ) : ℝ := Real.exp t - 1

/-- The Young function defining the ψ₂ norm.

**Lean implementation helper.** -/
noncomputable def orliczPsi2 (t : ℝ) : ℝ := Real.exp (t ^ 2) - 1

/-- The power function `|x|ᵖ` is an Orlicz Young function for `p ≥ 1`.

**Lean implementation helper.** -/
theorem isOrliczYoungFunction_lp {p : ℝ} (hp : 1 ≤ p) :
    IsOrliczYoungFunction (orliczLp p) where
  measurable := (Real.continuous_rpow_const (by linarith : 0 ≤ p)).measurable
  zero := by simp [orliczLp, Real.zero_rpow (by linarith : p ≠ 0)]
  nonneg := fun ht => Real.rpow_nonneg ht p
  monotoneOn := Real.monotoneOn_rpow_Ici_of_exponent_nonneg (by linarith)
  convexOn := convexOn_rpow hp
  positive := fun ht => Real.rpow_pos_of_pos ht p

/-- The exponential function defining the `ψ₁` norm is an Orlicz Young function.

**Lean implementation helper.** -/
theorem isOrliczYoungFunction_psi1 : IsOrliczYoungFunction orliczPsi1 where
  measurable := by
    unfold orliczPsi1
    fun_prop
  zero := by simp [orliczPsi1]
  nonneg := by
    intro t ht
    exact sub_nonneg.mpr (Real.one_le_exp ht)
  monotoneOn := by
    intro x _ y _ hxy
    exact sub_le_sub_right (Real.exp_le_exp.mpr hxy) 1
  convexOn := by
    refine ⟨convex_Ici 0, ?_⟩
    intro x _ y _ a b ha hb hab
    have hconv := convexOn_exp.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
    simp only [smul_eq_mul] at hconv ⊢
    dsimp only [orliczPsi1]
    nlinarith
  positive := by
    intro t ht
    exact sub_pos.mpr (Real.one_lt_exp_iff.mpr ht)

/-- The exponential-square function defining the `ψ₂` norm is an Orlicz Young function.

**Lean implementation helper.** -/
theorem isOrliczYoungFunction_psi2 : IsOrliczYoungFunction orliczPsi2 where
  measurable := by
    unfold orliczPsi2
    fun_prop
  zero := by simp [orliczPsi2]
  nonneg := by
    intro t _
    exact sub_nonneg.mpr (Real.one_le_exp (sq_nonneg t))
  monotoneOn := by
    intro x hx y hy hxy
    apply sub_le_sub_right
    apply Real.exp_le_exp.mpr
    exact pow_le_pow_left₀ hx hxy 2
  convexOn := by
    refine ⟨convex_Ici 0, ?_⟩
    intro x hx y hy a b ha hb hab
    simp only [Set.mem_Ici] at hx hy
    simp only [smul_eq_mul]
    have hsq : (a * x + b * y) ^ 2 ≤ a * x ^ 2 + b * y ^ 2 := by
      nlinarith [sq_nonneg (x - y), mul_nonneg ha hb]
    have hexpmono := Real.exp_le_exp.mpr hsq
    have hexpconv := convexOn_exp.2 (Set.mem_univ (x ^ 2))
      (Set.mem_univ (y ^ 2)) ha hb hab
    simp only [smul_eq_mul] at hexpconv
    dsimp only [orliczPsi2]
    nlinarith
  positive := by
    intro t ht
    exact sub_pos.mpr (Real.one_lt_exp_iff.mpr (sq_pos_of_pos ht))

/-- The abstract Orlicz modular for the `ψ₁` Young function equals the exponential absolute-moment expression.

**Lean implementation helper.** -/
lemma orliczModular_psi1 [IsProbabilityMeasure μ] (X : Ω → ℝ) {K : ℝ}
    (hK : 0 < K) :
    orliczModular orliczPsi1 X μ K = psi1MGF X μ K - 1 := by
  unfold orliczModular orliczPsi1 psi1MGF
  simp_rw [ENNReal.ofReal_sub _ zero_le_one, ENNReal.ofReal_one]
  rw [lintegral_sub' aemeasurable_const (by simp)]
  · simp
  · exact Filter.Eventually.of_forall fun ω => by
      rw [ENNReal.one_le_ofReal]
      exact Real.one_le_exp (div_nonneg (abs_nonneg _) hK.le)

/-- The abstract Orlicz modular for the `ψ₂` Young function equals the exponential square-moment expression.

**Lean implementation helper.** -/
lemma orliczModular_psi2 [IsProbabilityMeasure μ] (X : Ω → ℝ) (K : ℝ) :
    orliczModular orliczPsi2 X μ K = psi2MGF X μ K - 1 := by
  unfold orliczModular orliczPsi2 psi2MGF
  simp_rw [ENNReal.ofReal_sub _ zero_le_one, ENNReal.ofReal_one]
  rw [lintegral_sub' aemeasurable_const (by simp)]
  · simp only [lintegral_const, measure_univ, one_mul]
    congr 1
    refine lintegral_congr fun ω => ?_
    congr 2
    rw [div_pow, sq_abs]
  · exact Filter.Eventually.of_forall fun ω => by
      rw [ENNReal.one_le_ofReal]
      exact Real.one_le_exp (sq_nonneg (|X ω| / K))

/-- The generic
Luxemburg norm is definitionally
the already exported ψ₁ norm after subtracting `ψ(0)=1` from the exponential
functional.

**Book Remark 2.8.9.** -/
theorem orliczNorm_psi1 [IsProbabilityMeasure μ] (X : Ω → ℝ) :
    orliczNorm orliczPsi1 X μ = psi1Norm X μ := by
  unfold orliczNorm psi1Norm
  congr 1
  ext K
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hK, hmod⟩
    exact ⟨hK, by simpa only [orliczModular_psi1 X hK,
      tsub_le_iff_right, one_add_one_eq_two] using hmod⟩
  · rintro ⟨hK, hmod⟩
    exact ⟨hK, by simpa only [orliczModular_psi1 X hK,
      tsub_le_iff_right, one_add_one_eq_two] using hmod⟩

/-- `psi_alpha`/Orlicz norms generalize `psi_1` and `psi_2`.

**Book Remark 2.8.9.** -/
theorem orliczNorm_psi2 [IsProbabilityMeasure μ] (X : Ω → ℝ) :
    orliczNorm orliczPsi2 X μ = psi2Norm X μ := by
  unfold orliczNorm psi2Norm
  congr 1
  ext K
  simp only [Set.mem_setOf_eq]
  rw [orliczModular_psi2]
  simp only [tsub_le_iff_right, one_add_one_eq_two]

/-- Membership in the `ψ₁` Orlicz class is equivalent to finiteness of the `ψ₁` norm.

**Lean implementation helper.** -/
theorem orliczMem_psi1_iff [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXm : AEMeasurable X μ) :
    OrliczMem orliczPsi1 X μ ↔ SubExponential X μ := by
  simp only [OrliczMem, SubExponential, hXm, true_and]
  constructor <;> rintro ⟨K, hK, hmod⟩ <;>
    exact ⟨K, hK, by simpa only [orliczModular_psi1 X hK,
      tsub_le_iff_right, one_add_one_eq_two] using hmod⟩

/-- Membership in the `ψ₂` Orlicz class is equivalent to finiteness of the `ψ₂` norm.

**Lean implementation helper.** -/
theorem orliczMem_psi2_iff [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXm : AEMeasurable X μ) :
    OrliczMem orliczPsi2 X μ ↔ SubGaussian X μ := by
  simp only [OrliczMem, SubGaussian, hXm, true_and]
  constructor <;> rintro ⟨K, hK, hmod⟩ <;>
    exact ⟨K, hK, by simpa only [orliczModular_psi2,
      tsub_le_iff_right, one_add_one_eq_two] using hmod⟩

/-! ## Exact identification with `Lᵖ` -/

/-- Scaling identity for the power Orlicz modular.

**Lean implementation helper.** -/
lemma lintegral_orliczLp_scale (X : Ω → ℝ) {p K : ℝ}
    (hK : 0 < K) :
    (∫⁻ ω, ENNReal.ofReal (|X ω| ^ p) ∂μ) =
      ENNReal.ofReal (K ^ p) * orliczModular (orliczLp p) X μ K := by
  unfold orliczModular orliczLp
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun ω => ?_
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hK.le p)]
  congr 1
  rw [Real.div_rpow (abs_nonneg _) hK.le]
  field_simp [ne_of_gt (Real.rpow_pos_of_pos hK p)]

/-- A power-modular bound at scale `K` bounds the corresponding finite
real-valued `Lᵖ` norm. The `MemLp` assumption records finiteness explicitly.

**Lean implementation helper.** -/
lemma lpNormRV_le_of_orliczModular_lp {X : Ω → ℝ} {p K : ℝ}
    (hp : 0 < p) (hX : MemLp X (ENNReal.ofReal p) μ)
    (hK : 0 < K) (hmod : orliczModular (orliczLp p) X μ K ≤ 1) :
    Chapter1.lpNormRV X p μ ≤ K := by
  have hlin : (∫⁻ ω, ENNReal.ofReal (|X ω| ^ p) ∂μ) ≤
      ENNReal.ofReal (K ^ p) := by
    rw [lintegral_orliczLp_scale X hK]
    simpa only [mul_one, mul_comm] using
      mul_le_mul_left hmod (ENNReal.ofReal (K ^ p))
  have hp0 : ENNReal.ofReal p ≠ 0 := by
    simpa [ENNReal.ofReal_eq_zero] using not_le.mpr hp
  have hlin' : (∫⁻ ω, ‖X ω‖ₑ ^ p ∂μ) ≤ ENNReal.ofReal (K ^ p) := by
    simpa only [Real.enorm_eq_ofReal_abs,
      ← ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp.le] using hlin
  have he : eLpNorm X (ENNReal.ofReal p) μ ≤ ENNReal.ofReal K := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hp.le]
    calc
      (∫⁻ ω, ‖X ω‖ₑ ^ p ∂μ) ^ (1 / p)
          ≤ (ENNReal.ofReal (K ^ p)) ^ (1 / p) :=
        ENNReal.rpow_le_rpow hlin' (by positivity)
      _ = ENNReal.ofReal K := by
        rw [← ENNReal.ofReal_rpow_of_nonneg hK.le hp.le, one_div,
          ENNReal.rpow_rpow_inv hp.ne']
  rw [Chapter1.lpNormRV_eq_toReal_eLpNorm hp hX]
  calc
    (eLpNorm X (ENNReal.ofReal p) μ).toReal
        ≤ (ENNReal.ofReal K).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top he
    _ = K := ENNReal.toReal_ofReal hK.le

/-- On the finite
`Lᵖ` class the Luxemburg
norm for `ψ(t) = tᵖ` is exactly the source's real-valued `Lᵖ` norm.

**Book Remark 2.8.9.** -/
theorem orliczNorm_lp [IsProbabilityMeasure μ] {X : Ω → ℝ}
    {p : ℝ} (hp : 1 ≤ p) (hX : MemLp X (ENNReal.ofReal p) μ) :
    orliczNorm (orliczLp p) X μ = Chapter1.lpNormRV X p μ := by
  have hp0 : 0 < p := lt_of_lt_of_le one_pos hp
  have hpENN : ENNReal.ofReal p ≠ 0 := by
    simpa [ENNReal.ofReal_eq_zero] using not_le.mpr hp0
  let A : ℝ := Chapter1.lpNormRV X p μ
  have hA0 : 0 ≤ A := by
    dsimp [A]
    rw [Chapter1.lpNormRV_eq_toReal_eLpNorm hp0 hX]
    exact ENNReal.toReal_nonneg
  rcases eq_or_lt_of_le hA0 with hAzero | hApos
  · have hto0 : (eLpNorm X (ENNReal.ofReal p) μ).toReal = 0 := by
      rw [← Chapter1.lpNormRV_eq_toReal_eLpNorm hp0 hX]
      exact hAzero.symm
    have he0 : eLpNorm X (ENNReal.ofReal p) μ = 0 := by
      rcases (ENNReal.toReal_eq_zero_iff _).mp hto0 with he | he
      · exact he
      · exact absurd he hX.eLpNorm_ne_top
    have hae : X =ᵐ[μ] 0 :=
      (eLpNorm_eq_zero_iff hX.1 hpENN).mp he0
    calc
      orliczNorm (orliczLp p) X μ =
          orliczNorm (orliczLp p) (fun _ : Ω => 0) μ :=
        orliczNorm_congr_ae (orliczLp p) hae
      _ = 0 := orliczNorm_zero (isOrliczYoungFunction_lp hp)
      _ = Chapter1.lpNormRV X p μ := hAzero
  · have hEA : eLpNorm X (ENNReal.ofReal p) μ = ENNReal.ofReal A := by
      calc
        eLpNorm X (ENNReal.ofReal p) μ
            = ENNReal.ofReal (eLpNorm X (ENNReal.ofReal p) μ).toReal :=
              (ENNReal.ofReal_toReal hX.eLpNorm_ne_top).symm
        _ = ENNReal.ofReal A := by
          rw [← Chapter1.lpNormRV_eq_toReal_eLpNorm hp0 hX]
    have hL : (∫⁻ ω, ENNReal.ofReal (|X ω| ^ p) ∂μ) =
        ENNReal.ofReal (A ^ p) := by
      have heq := eLpNorm_eq_lintegral_rpow_enorm_toReal hpENN
        ENNReal.ofReal_ne_top (f := X) (μ := μ)
      rw [ENNReal.toReal_ofReal hp0.le] at heq
      have hraw : (∫⁻ ω, ‖X ω‖ₑ ^ p ∂μ) =
          (eLpNorm X (ENNReal.ofReal p) μ) ^ p := by
        rw [heq, one_div]
        simp only [ENNReal.rpow_inv_rpow hp0.ne']
      calc
        (∫⁻ ω, ENNReal.ofReal (|X ω| ^ p) ∂μ)
            = ∫⁻ ω, ‖X ω‖ₑ ^ p ∂μ := by
              refine lintegral_congr fun ω => ?_
              rw [Real.enorm_eq_ofReal_abs,
                ← ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp0.le]
        _ = (eLpNorm X (ENNReal.ofReal p) μ) ^ p := hraw
        _ = ENNReal.ofReal (A ^ p) := by
          rw [hEA, ENNReal.ofReal_rpow_of_nonneg hA0 hp0.le]
    have hscale := lintegral_orliczLp_scale (μ := μ) (p := p) X hApos
    have hc0 : ENNReal.ofReal (A ^ p) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hApos p)).ne'
    have hmodA : orliczModular (orliczLp p) X μ A ≤ 1 := by
      rw [← ENNReal.mul_le_mul_iff_left hc0 ENNReal.ofReal_ne_top]
      rw [mul_comm (orliczModular (orliczLp p) X μ A), ← hscale, hL]
      simp
    have hset : {K : ℝ | 0 < K ∧
        orliczModular (orliczLp p) X μ K ≤ 1} = Set.Ici A := by
      ext K
      simp only [Set.mem_setOf_eq, Set.mem_Ici]
      constructor
      · rintro ⟨hK, hmod⟩
        exact lpNormRV_le_of_orliczModular_lp hp0 hX hK hmod
      · intro hAK
        have hK : 0 < K := hApos.trans_le hAK
        exact ⟨hK, (orliczModular_mono_scale
          (isOrliczYoungFunction_lp hp) X hApos hAK).trans hmodA⟩
    rw [orliczNorm, hset, csInf_Ici]

end HDP

end Source_17_OrliczExamples

/-! ## Material formerly in `18_SubExponentialProperties.lean` -/

section Source_18_SubExponentialProperties

open MeasureTheory ProbabilityTheory Real Filter
open scoped ENNReal NNReal Topology

namespace HDP

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- I) implies
(iii), with `K₃ = 3 K₁`.

**Book Proposition 2.8.1.** -/
theorem subexponential_i_to_iii [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXm : AEMeasurable X μ) {K₁ : ℝ} (hK₁ : 0 < K₁)
    (h : ∀ t : ℝ, 0 ≤ t →
      μ {ω | t ≤ |X ω|} ≤ ENNReal.ofReal (2 * Real.exp (-t / K₁))) :
    psi1MGF X μ (3 * K₁) ≤ 2 := by
  set K : ℝ := 3 * K₁ with hKdef
  have hK : 0 < K := by positivity
  have hlc : psi1MGF X μ K
      = ∫⁻ t in Set.Ioi (0 : ℝ), μ {ω | t < Real.exp (|X ω| / K)} := by
    unfold psi1MGF
    exact lintegral_eq_lintegral_meas_lt μ
      (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le)
      (measurable_exp.comp_aemeasurable
        ((continuous_abs.measurable.comp_aemeasurable hXm).div_const _))
  rw [hlc]
  have hsplit : Set.Ioi (0 : ℝ) = Set.Ioc 0 1 ∪ Set.Ioi 1 :=
    (Set.Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  rw [hsplit, lintegral_union measurableSet_Ioi Set.Ioc_disjoint_Ioi_same]
  have hpiece1 :
      ∫⁻ t in Set.Ioc (0 : ℝ) 1, μ {ω | t < Real.exp (|X ω| / K)} ≤ 1 := by
    calc
      ∫⁻ t in Set.Ioc (0 : ℝ) 1, μ {ω | t < Real.exp (|X ω| / K)}
          ≤ ∫⁻ _t in Set.Ioc (0 : ℝ) 1, 1 := lintegral_mono fun _ => prob_le_one
      _ = 1 := by simp [Real.volume_Ioc]
  have hpiece2 :
      ∫⁻ t in Set.Ioi (1 : ℝ), μ {ω | t < Real.exp (|X ω| / K)} ≤ 1 := by
    have hptw : ∀ t ∈ Set.Ioi (1 : ℝ),
        μ {ω | t < Real.exp (|X ω| / K)} ≤ ENNReal.ofReal (2 * t ^ (-3 : ℝ)) := by
      intro t ht
      rw [Set.mem_Ioi] at ht
      have ht0 : 0 < t := by linarith
      have hlog : 0 ≤ Real.log t := Real.log_nonneg ht.le
      have hsub : {ω | t < Real.exp (|X ω| / K)}
          ⊆ {ω | K * Real.log t ≤ |X ω|} := by
        intro ω hω
        simp only [Set.mem_setOf_eq] at hω ⊢
        have hlt : Real.log t < |X ω| / K := by
          have := Real.log_lt_log ht0 hω
          rwa [Real.log_exp] at this
        simpa [mul_comm] using (le_div_iff₀ hK).mp hlt.le
      calc
        μ {ω | t < Real.exp (|X ω| / K)}
            ≤ μ {ω | K * Real.log t ≤ |X ω|} := measure_mono hsub
        _ ≤ ENNReal.ofReal (2 * Real.exp (-(K * Real.log t) / K₁)) :=
          h _ (mul_nonneg hK.le hlog)
        _ = ENNReal.ofReal (2 * t ^ (-3 : ℝ)) := by
          congr 1
          rw [hKdef]
          have harg : -(3 * K₁ * Real.log t) / K₁ = -3 * Real.log t := by
            field_simp
          rw [harg, Real.rpow_def_of_pos ht0]
          ring_nf
    calc
      ∫⁻ t in Set.Ioi (1 : ℝ), μ {ω | t < Real.exp (|X ω| / K)}
          ≤ ∫⁻ t in Set.Ioi (1 : ℝ), ENNReal.ofReal (2 * t ^ (-3 : ℝ)) := by
            refine lintegral_mono_ae ?_
            filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
            exact hptw t ht
      _ = ENNReal.ofReal (∫ t in Set.Ioi (1 : ℝ), 2 * t ^ (-3 : ℝ)) := by
            rw [← ofReal_integral_eq_lintegral_ofReal]
            · exact ((integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).const_mul 2)
            · refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_)
              have ht' : (1 : ℝ) < t := ht
              exact mul_nonneg (by norm_num)
                (Real.rpow_nonneg (le_of_lt (lt_trans one_pos ht')) _)
      _ = 1 := by
            rw [MeasureTheory.integral_const_mul,
              integral_Ioi_rpow_of_lt (by norm_num) one_pos]
            norm_num
  calc
    (∫⁻ t in Set.Ioc (0 : ℝ) 1, μ {ω | t < Real.exp (|X ω| / K)})
        + ∫⁻ t in Set.Ioi (1 : ℝ), μ {ω | t < Real.exp (|X ω| / K)}
        ≤ 1 + 1 := add_le_add hpiece1 hpiece2
    _ = 2 := by norm_num

/-- Iii) implies
(ii), with `K₂ = 2 K₃`.

**Book Proposition 2.8.1.** -/
theorem subexponential_iii_to_ii [IsProbabilityMeasure μ] {X : Ω → ℝ}
    {K : ℝ} (hK : 0 < K) (h : psi1MGF X μ K ≤ 2)
    {p : ℝ} (hp : 1 ≤ p) :
    ∫⁻ ω, ENNReal.ofReal (|X ω| ^ p) ∂μ
      ≤ ENNReal.ofReal (((2 * K) * p) ^ p) := by
  have hp0 : 0 < p := lt_of_lt_of_le one_pos hp
  set C : ℝ := (K * p) ^ p with hC
  have hC0 : 0 ≤ C := by positivity
  have hptw : ∀ ω, |X ω| ^ p ≤ C * Real.exp (|X ω| / K) := by
    intro ω
    set u : ℝ := |X ω| / K with hu
    have hu0 : 0 ≤ u := by positivity
    have hbase : (p / Real.exp 1) ^ p ≤ p ^ p := by
      apply Real.rpow_le_rpow (by positivity) _ hp0.le
      have he2 : (2 : ℝ) ≤ Real.exp 1 := by
        simpa only [one_add_one_eq_two] using Real.add_one_le_exp (1 : ℝ)
      have he : 1 ≤ Real.exp 1 := le_trans (by norm_num) he2
      exact div_le_self (by positivity) he
    have hr := rpow_le_exp_of_pos hu0 hp0
    have hscale : |X ω| ^ p = K ^ p * u ^ p := by
      rw [hu, Real.div_rpow (abs_nonneg _) hK.le]
      field_simp [ne_of_gt (Real.rpow_pos_of_pos hK p)]
    rw [hscale, hC]
    calc
      K ^ p * u ^ p
          ≤ K ^ p * ((p / Real.exp 1) ^ p * Real.exp u) :=
            mul_le_mul_of_nonneg_left hr (by positivity)
      _ ≤ K ^ p * (p ^ p * Real.exp u) := by
            gcongr
      _ = (K * p) ^ p * Real.exp (|X ω| / K) := by
            rw [Real.mul_rpow hK.le hp0.le, hu]
            ring
  calc
    ∫⁻ ω, ENNReal.ofReal (|X ω| ^ p) ∂μ
        ≤ ∫⁻ ω, ENNReal.ofReal C * ENNReal.ofReal (Real.exp (|X ω| / K)) ∂μ := by
          refine lintegral_mono fun ω => ?_
          rw [← ENNReal.ofReal_mul hC0]
          exact ENNReal.ofReal_le_ofReal (hptw ω)
    _ = ENNReal.ofReal C * psi1MGF X μ K :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal C * 2 := by
      simpa only [mul_comm] using mul_le_mul_left h (ENNReal.ofReal C)
    _ ≤ ENNReal.ofReal (((2 * K) * p) ^ p) := by
          rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
            ← ENNReal.ofReal_mul hC0]
          apply ENNReal.ofReal_le_ofReal
          have h2pow : (2 : ℝ) ≤ 2 ^ p := by
            have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hp
            simpa using this
          have hout : ((2 * K) * p) ^ p = 2 ^ p * C := by
            rw [hC, show (2 * K) * p = 2 * (K * p) by ring,
              Real.mul_rpow (by norm_num) (mul_nonneg hK.le hp0.le)]
          rw [hout]
          nlinarith

/-- Ii) implies
(iii), with `K₃ = 2 e K₂`.

**Book Proposition 2.8.1.** -/
theorem subexponential_ii_to_iii [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXm : AEMeasurable X μ) {K₂ : ℝ} (hK₂ : 0 < K₂)
    (h : ∀ p : ℝ, 1 ≤ p →
      ∫⁻ ω, ENNReal.ofReal (|X ω| ^ p) ∂μ
        ≤ ENNReal.ofReal ((K₂ * p) ^ p)) :
    psi1MGF X μ (2 * Real.exp 1 * K₂) ≤ 2 := by
  set K : ℝ := 2 * Real.exp 1 * K₂ with hKdef
  have hK : 0 < K := by positivity
  have hexp_series : ∀ y : ℝ, 0 ≤ y →
      ENNReal.ofReal (Real.exp y) =
        ∑' n : ℕ, ENNReal.ofReal (y ^ n / Nat.factorial n) := by
    intro y hy
    rw [show Real.exp y = ∑' n : ℕ, y ^ n / Nat.factorial n from
      congrFun (Real.exp_eq_exp_ℝ.trans NormedSpace.exp_eq_tsum_div) y]
    exact ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
      (Real.summable_pow_div_factorial y)
  unfold psi1MGF
  have hrw : ∀ ω, ENNReal.ofReal (Real.exp (|X ω| / K))
      = ∑' n : ℕ, ENNReal.ofReal ((|X ω| / K) ^ n / Nat.factorial n) :=
    fun ω => hexp_series _ (by positivity)
  have hmeas : ∀ n : ℕ,
      AEMeasurable (fun ω => ENNReal.ofReal ((|X ω| / K) ^ n / Nat.factorial n)) μ := by
    intro n
    simpa only [Function.comp_apply] using
      (((((continuous_abs.measurable.comp_aemeasurable hXm).div_const K).pow_const n).div_const
        (Nat.factorial n)).ennreal_ofReal)
  rw [lintegral_congr hrw, lintegral_tsum hmeas]
  have hterm : ∀ n : ℕ,
      ∫⁻ ω, ENNReal.ofReal ((|X ω| / K) ^ n / Nat.factorial n) ∂μ
        ≤ ENNReal.ofReal ((1 / 2) ^ n) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have hrw2 : ∀ ω, (|X ω| / K) ^ n / Nat.factorial n
        = |X ω| ^ (n : ℝ) * (1 / (K ^ n * Nat.factorial n)) := by
      intro ω
      rw [Real.rpow_natCast, div_pow]
      field_simp
    have h1 : ∫⁻ ω, ENNReal.ofReal ((|X ω| / K) ^ n / Nat.factorial n) ∂μ
        = ENNReal.ofReal (1 / (K ^ n * Nat.factorial n))
          * ∫⁻ ω, ENNReal.ofReal (|X ω| ^ (n : ℝ)) ∂μ := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_congr fun ω => ?_
      rw [← ENNReal.ofReal_mul (by positivity), hrw2 ω]
      ring_nf
    rw [h1]
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hmom := h (n : ℝ) hn1
    calc
      ENNReal.ofReal (1 / (K ^ n * Nat.factorial n))
            * ∫⁻ ω, ENNReal.ofReal (|X ω| ^ (n : ℝ)) ∂μ
          ≤ ENNReal.ofReal (1 / (K ^ n * Nat.factorial n))
            * ENNReal.ofReal ((K₂ * (n : ℝ)) ^ (n : ℝ)) :=
              by
                simpa only [mul_comm] using
                  mul_le_mul_left hmom
                    (ENNReal.ofReal (1 / (K ^ n * Nat.factorial n)))
      _ ≤ ENNReal.ofReal ((1 / 2) ^ n) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          rw [Real.rpow_natCast]
          have hfact : (((n : ℝ) / Real.exp 1) ^ n) ≤ (Nat.factorial n : ℝ) :=
            Chapter1.factorial_lower_bound n
          have hnumpow : (K₂ * (n : ℝ)) ^ n = K₂ ^ n * (n : ℝ) ^ n :=
            mul_pow _ _ _
          have hKpow : K ^ n = (2 * Real.exp 1 * K₂) ^ n := by rw [hKdef]
          rw [hnumpow, hKpow, one_div, inv_mul_le_iff₀ (by positivity)]
          have hid : (n : ℝ) ^ n = (Real.exp 1) ^ n * ((n : ℝ) / Real.exp 1) ^ n := by
            rw [← mul_pow]
            congr 1
            field_simp
          rw [hid]
          calc
            K₂ ^ n * ((Real.exp 1) ^ n * ((n : ℝ) / Real.exp 1) ^ n)
                ≤ K₂ ^ n * ((Real.exp 1) ^ n * (Nat.factorial n : ℝ)) := by
                  apply mul_le_mul_of_nonneg_left _ (by positivity)
                  exact mul_le_mul_of_nonneg_left hfact (by positivity)
            _ = (2 * Real.exp 1 * K₂) ^ n * (Nat.factorial n : ℝ) * (1 / 2) ^ n := by
                  have hpow : K₂ ^ n * (Real.exp 1) ^ n
                      = (2 * Real.exp 1 * K₂) ^ n * (1 / 2) ^ n := by
                    rw [← mul_pow, ← mul_pow]
                    congr 1
                    ring
                  calc
                    K₂ ^ n * ((Real.exp 1) ^ n * (Nat.factorial n : ℝ))
                        = (K₂ ^ n * (Real.exp 1) ^ n) * (Nat.factorial n : ℝ) := by ring
                    _ = ((2 * Real.exp 1 * K₂) ^ n * (1 / 2) ^ n)
                          * (Nat.factorial n : ℝ) := by rw [hpow]
                    _ = (2 * Real.exp 1 * K₂) ^ n * (Nat.factorial n : ℝ)
                          * (1 / 2) ^ n := by ring
  calc
    ∑' n : ℕ, ∫⁻ ω, ENNReal.ofReal ((|X ω| / K) ^ n / Nat.factorial n) ∂μ
        ≤ ∑' n : ℕ, ENNReal.ofReal ((1 / 2) ^ n) := ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (∑' n : ℕ, (1 / 2) ^ n) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
            (summable_geometric_of_lt_one (by norm_num) (by norm_num))).symm
    _ = 2 := by
          rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
          norm_num

/-- Remark 2.8.3: the MGF of `Exp(1)` is infinite for `λ ≥ 1`.

**Book Remark 2.8.3.** -/
theorem exponential_mgf_diverges {lam : ℝ} (hlam : 1 ≤ lam) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (lam * x)) ∂(expMeasure 1) = ⊤ := by
  have hf : Measurable (gammaPDF 1 1) := by
    change Measurable (fun x => ENNReal.ofReal (gammaPDFReal 1 1 x))
    exact (measurable_gammaPDFReal 1 1).ennreal_ofReal
  have hg : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (lam * x))) := by
    fun_prop
  rw [expMeasure, gammaMeasure,
    lintegral_withDensity_eq_lintegral_mul volume hf hg]
  apply top_unique
  calc
    ⊤ = ∫⁻ _x : ℝ in Set.Ioi 0, (1 : ℝ≥0∞) := by
          rw [setLIntegral_const, Real.volume_Ioi]
          simp
    _ ≤ ∫⁻ x : ℝ in Set.Ioi 0,
        (gammaPDF 1 1 * fun x => ENNReal.ofReal (Real.exp (lam * x))) x := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
          rw [Set.mem_Ioi] at hx
          change 1 ≤ gammaPDF 1 1 x * ENNReal.ofReal (Real.exp (lam * x))
          rw [gammaPDF_of_nonneg hx.le]
          simp only [one_rpow, Gamma_one, div_one, sub_self, Real.rpow_zero,
            mul_one, one_mul]
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
          rw [← Real.exp_add]
          norm_num
          nlinarith
    _ ≤ ∫⁻ x : ℝ, (gammaPDF 1 1 * fun x =>
          ENNReal.ofReal (Real.exp (lam * x))) x :=
      setLIntegral_le_lintegral _ _

/-! ## Remark 2.8.8: the quantitative hierarchy of norms -/

/-- The raw-moment implication in Proposition 2.8.1, converted to the source's
finite real-valued `Lᵖ` norm.

**Book Proposition 2.8.1.** -/
theorem lpNormRV_le_of_psi1MGF [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXm : AEMeasurable X μ) {K : ℝ} (hK : 0 < K)
    (h : psi1MGF X μ K ≤ 2) {p : ℝ} (hp : 1 ≤ p) :
    Chapter1.lpNormRV X p μ ≤ (2 * K) * p := by
  have hp0 : 0 < p := lt_of_lt_of_le one_pos hp
  have hlin := subexponential_iii_to_ii (μ := μ) hK h hp
  have hmeas : AEStronglyMeasurable (fun ω => |X ω| ^ p) μ := by
    have h1 : AEStronglyMeasurable (fun ω => |X ω|) μ := by
      simpa [Real.norm_eq_abs] using hXm.aestronglyMeasurable.norm
    exact (Real.continuous_rpow_const hp0.le).comp_aestronglyMeasurable h1
  have hint : ∫ ω, |X ω| ^ p ∂μ ≤ ((2 * K) * p) ^ p := by
    rw [integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (abs_nonneg _) p) hmeas]
    calc
      (∫⁻ ω, ENNReal.ofReal (|X ω| ^ p) ∂μ).toReal
          ≤ (ENNReal.ofReal (((2 * K) * p) ^ p)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hlin
      _ = ((2 * K) * p) ^ p := ENNReal.toReal_ofReal (by positivity)
  rw [Chapter1.lpNormRV]
  calc
    (∫ ω, |X ω| ^ p ∂μ) ^ (1 / p)
        ≤ (((2 * K) * p) ^ p) ^ (1 / p) := by
      apply Real.rpow_le_rpow _ hint (by positivity)
      exact integral_nonneg fun ω => Real.rpow_nonneg (abs_nonneg _) p
    _ = (2 * K) * p := by
      rw [← Real.rpow_mul (by positivity), mul_one_div, div_self hp0.ne',
        Real.rpow_one]

/-- Every ψ₁ random variable has all finite moments, with the linear-in-`p`
constant displayed in Remark 2.8.8.

**Book Remark 2.8.8.** -/
theorem SubExponential.lpNormRV_le [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : SubExponential X μ) (hXm : AEMeasurable X μ)
    {p : ℝ} (hp : 1 ≤ p) :
    Chapter1.lpNormRV X p μ ≤ (2 * psi1Norm X μ) * p := by
  rcases eq_or_lt_of_le (psi1Norm_nonneg X μ) with hzero | hpos
  · have hz := ae_eq_zero_of_psi1Norm_eq_zero hXm hX hzero.symm
    have hp0 : 0 < p := lt_of_lt_of_le one_pos hp
    rw [Chapter1.lpNormRV]
    rw [integral_congr_ae (g := fun _ => (0 : ℝ)) (by
      filter_upwards [hz] with ω hω
      rw [Pi.zero_apply] at hω
      rw [hω, abs_zero, Real.zero_rpow hp0.ne'])]
    rw [integral_zero, Real.zero_rpow (by positivity), ← hzero]
    norm_num
  · exact lpNormRV_le_of_psi1MGF hXm hpos
      (psi1MGF_psi1Norm_le_two hXm hX) hp

/-- The quantitative subgaussian-to-subexponential implication in Remark
2.8.8.

**Book Remark 2.8.8.** -/
theorem subGaussian_to_subExponential [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXm : AEMeasurable X μ) (hX : SubGaussian X μ) :
    SubExponential X μ ∧
      psi1Norm X μ ≤ psi2Norm X μ / Real.sqrt (Real.log 2) := by
  have hOne : SubGaussian (fun _ : Ω => (1 : ℝ)) μ :=
    (psi2Norm_le_of_bounded (M := (1 : ℝ)) one_pos
      (Filter.Eventually.of_forall fun _ => by norm_num)).1
  have h := psi1Norm_mul_le hXm (aemeasurable_const (b := (1 : ℝ))) hX hOne
  have hfun : (fun ω => X ω * (fun _ : Ω => (1 : ℝ)) ω) = X := by
    funext ω
    simp
  constructor
  · simpa only [hfun] using h.1
  · rw [hfun, psi2Norm_const (μ := μ) 1] at h
    simpa only [abs_one, one_div, one_mul, div_eq_mul_inv] using h.2

/-- An essentially bounded random variable is subgaussian, with the explicit
ψ₂-to-`L∞` comparison in Remark 2.8.8.

**Book Remark 2.8.8.** -/
theorem bounded_to_subGaussian [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXtop : MemLp X ⊤ μ) :
    SubGaussian X μ ∧
      psi2Norm X μ ≤ (eLpNorm X ⊤ μ).toReal / Real.sqrt (Real.log 2) := by
  let M : ℝ := (eLpNorm X ⊤ μ).toReal
  have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
  have hXle : ∀ᵐ ω ∂μ, |X ω| ≤ M := by
    filter_upwards [MeasureTheory.ae_le_eLpNormEssSup (f := X) (μ := μ)] with ω hω
    have hle : ENNReal.ofReal |X ω| ≤ eLpNorm X ⊤ μ := by
      rw [eLpNorm_exponent_top, ← Real.enorm_eq_ofReal_abs]
      exact hω
    calc
      |X ω| = (ENNReal.ofReal |X ω|).toReal :=
        (ENNReal.toReal_ofReal (abs_nonneg _)).symm
      _ ≤ M := ENNReal.toReal_mono hXtop.eLpNorm_ne_top hle
  rcases eq_or_lt_of_le hM0 with hMzero | hMpos
  · have hz : X =ᵐ[μ] 0 := by
      filter_upwards [hXle] with ω hω
      rw [← hMzero] at hω
      have hx : X ω = 0 := abs_eq_zero.mp (le_antisymm hω (abs_nonneg _))
      simpa only [Pi.zero_apply] using hx
    have hsg : SubGaussian X μ := by
      refine ⟨1, one_pos, ?_⟩
      rw [psi2MGF_of_ae_zero hz]
      norm_num
    refine ⟨hsg, ?_⟩
    rw [(psi2Norm_eq_zero_iff hXtop.1.aemeasurable hsg).2 hz]
    positivity
  · exact psi2Norm_le_of_bounded hMpos hXle

/-- In one load-bearing statement. Potentially
infinite norms use `eLpNorm`; each real-valued `lpNormRV` occurrence is backed
by the corresponding `MemLp` fact.

**Book Remark 2.8.8.** -/
theorem remark_2_8_8 [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXtop : MemLp X ⊤ μ) {p : ℝ} (hp : 2 ≤ p) :
    SubGaussian X μ ∧ SubExponential X μ ∧
      MemLp X (ENNReal.ofReal p) μ ∧
      MemLp X (ENNReal.ofReal 2) μ ∧ Integrable X μ ∧
      Chapter1.lpNormRV X 1 μ ≤ Chapter1.lpNormRV X 2 μ ∧
      Chapter1.lpNormRV X 2 μ ≤ Chapter1.lpNormRV X p μ ∧
      Chapter1.lpNormRV X p μ ≤ (2 * psi1Norm X μ) * p ∧
      psi1Norm X μ ≤ psi2Norm X μ / Real.sqrt (Real.log 2) ∧
      psi2Norm X μ ≤ (eLpNorm X ⊤ μ).toReal / Real.sqrt (Real.log 2) := by
  have hsg := bounded_to_subGaussian hXtop
  have hse := subGaussian_to_subExponential hXtop.1.aemeasurable hsg.1
  have hXp : MemLp X (ENNReal.ofReal p) μ :=
    hXtop.mono_exponent (by simp)
  have hX2 : MemLp X (ENNReal.ofReal 2) μ :=
    hXtop.mono_exponent (by simp)
  have hXint : Integrable X μ := hXtop.integrable le_top
  have h12 : Chapter1.lpNormRV X 1 μ ≤ Chapter1.lpNormRV X 2 μ :=
    Chapter1.exercise_1_11a one_pos one_le_two hX2
  have h2p : Chapter1.lpNormRV X 2 μ ≤ Chapter1.lpNormRV X p μ :=
    Chapter1.exercise_1_11a (by norm_num) hp hXp
  have hppsi := hse.1.lpNormRV_le hXtop.1.aemeasurable
    (show 1 ≤ p by linarith)
  exact ⟨hsg.1, hse.1, hXp, hX2, hXint, h12, h2p, hppsi, hse.2, hsg.2⟩

end HDP

end Source_18_SubExponentialProperties

/-! ## Material formerly in `19_Bernstein.lean` -/

section Source_19_Bernstein

/-
Book Chapter 2, §2.8 (part 2) and §2.9: subexponential properties and Bernstein's
inequality.

8–2.9 (PDF pages 51–55).

Contents:
* the packaged tail bound at the attained norm (`SubExponential.tail_bound`);
* **Proposition 2.8.1, (iii)⇒(iv) — the display (2.24)** with explicit constants:
  for mean-zero `X` with `𝔼e^{|X|/K} ≤ 2` and `|λ| ≤ 1/(4K)`,
  `𝔼e^{λX} ≤ exp((16/9)K²λ²)` (the source's Taylor argument; the elementary
  pointwise steps replace the source's unspecified absolute constants by
  `C = 16/9`, `c = 1/4`);
* the packaged MGF bound `SubExponential.mgf_bound` at the attained ψ₁ norm,
  with the constraint in multiplicative form `|λ|·4‖X‖_{ψ₁} ≤ 1` (equivalent to
  `|λ| ≤ 1/(4‖X‖_{ψ₁})` and meaningful also when the norm vanishes);
* **Book Theorem 2.9.1 (Bernstein's inequality)** with the explicit absolute
  constant `c = 1/8`:
  `ℙ{|∑Xᵢ| ≥ t} ≤ 2exp(−(1/8)·min(t²/∑‖Xᵢ‖²_{ψ₁}, t/K))` for independent
  mean-zero subexponential `Xᵢ` with `‖Xᵢ‖_{ψ₁} ≤ K` (the source's `K` is
  `maxᵢ‖Xᵢ‖_{ψ₁}`, the least such bound).

Remaining §2.8–§2.9 items (moment equivalences of Prop 2.8.1, Example 2.8.7,
Ex 2.47, Thm 2.9.5) are tracked in
`Chapter2_checkpoint.md`.
-/


open MeasureTheory ProbabilityTheory Real Filter
open scoped ENNReal NNReal Topology

namespace HDP

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- With the explicit constant
`c = 1`: `ℙ{|X| ≥ t} ≤ 2exp(−t/‖X‖_{ψ₁})` for all `t ≥ 0`.

**Book Proposition 2.8.1(i).** -/
theorem SubExponential.tail_bound [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXm : AEMeasurable X μ) (h : SubExponential X μ) {t : ℝ} (ht : 0 ≤ t) :
    μ {ω | t ≤ |X ω|} ≤ ENNReal.ofReal (2 * Real.exp (-t/(psi1Norm X μ))) := by
  rcases eq_or_lt_of_le (psi1Norm_nonneg X μ) with h0 | h0
  · rw [← h0, show -t/(0:ℝ) = 0 from by norm_num, Real.exp_zero, mul_one]
    calc μ {ω | t ≤ |X ω|} ≤ 1 := prob_le_one
      _ ≤ ENNReal.ofReal 2 := by norm_num
  · exact subexponential_iii_to_i hXm h0 (psi1MGF_psi1Norm_le_two hXm h) ht

/-! ## Book Proposition 2.8.1, (iii)⇒(iv): the MGF bound (2.24) -/

/-- With the explicit
constants `C = 16/9` and `c = 1/4`: for mean-zero `X` with `𝔼e^{|X|/K} ≤ 2` and
`|λ| ≤ 1/(4K)`, `𝔼 e^{λX} ≤ exp((16/9)K²λ²)`.

The Lean proof is the source's Taylor argument
(`e^z ≤ 1 + z + (z²/2)e^{|z|}`), with the elementary pointwise bounds
`x² ≤ (16/9)K²e^{(3/4)|x|/K}` (from `u ≤ e^{u/2}`) and
`e^{|λx|} ≤ e^{|x|/(4K)}` making all constants explicit.

**Book Proposition 2.8.1.** -/
theorem subexponential_iii_to_iv [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXm : AEMeasurable X μ) {K : ℝ} (hK : 0 < K) (h : psi1MGF X μ K ≤ 2)
    (hmean : ∫ ω, X ω ∂μ = 0) {lam : ℝ} (hlam : |lam| ≤ 1 / (4 * K)) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * X ω)) ∂μ
      ≤ ENNReal.ofReal (Real.exp ((16/9) * K^2 * lam^2)) := by
  obtain ⟨hEint, hEle⟩ := integrable_exp_abs_div hXm h
  -- pointwise: `e^{λx} ≤ 1 + λx + (8/9)λ²K² e^{|x|/K}`
  have hptw : ∀ ω, Real.exp (lam * X ω)
      ≤ 1 + lam * X ω + (8/9)*lam^2*K^2 * Real.exp (|X ω|/K) := by
    intro ω
    have hA := HDP.exp_le_one_add_add_sq_exp_abs (lam * X ω)
    have hu0 : (0:ℝ) ≤ |X ω|/K := by positivity
    -- `u² ≤ (16/9)e^{3u/4}` for `u = |x|/K`
    have h38 : 3*(|X ω|/K)/4 ≤ Real.exp (3*(|X ω|/K)/8) := by
      have h1 := self_le_exp_half (u := 3*(|X ω|/K)/4) (by positivity)
      calc 3*(|X ω|/K)/4 ≤ Real.exp ((3*(|X ω|/K)/4)/2) := h1
        _ = Real.exp (3*(|X ω|/K)/8) := by
            congr 1
            ring
    have hee : Real.exp (3*(|X ω|/K)/8) * Real.exp (3*(|X ω|/K)/8)
        = Real.exp (3*(|X ω|/K)/4) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have husq : (|X ω|/K)^2 ≤ (16/9) * Real.exp (3*(|X ω|/K)/4) := by
      nlinarith [h38, hu0, Real.exp_pos (3*(|X ω|/K)/8)]
    have hx2 : (X ω)^2 ≤ (16/9)*K^2 * Real.exp (3*(|X ω|/K)/4) := by
      have h1 : (X ω)^2 = K^2 * (|X ω|/K)^2 := by
        rw [div_pow, sq_abs]
        field_simp
      rw [h1]
      calc K^2 * (|X ω|/K)^2
          ≤ K^2 * ((16/9) * Real.exp (3*(|X ω|/K)/4)) :=
            mul_le_mul_of_nonneg_left husq (by positivity)
        _ = (16/9)*K^2 * Real.exp (3*(|X ω|/K)/4) := by ring
    have habs : |lam * X ω| ≤ (|X ω|/K)/4 := by
      rw [abs_mul]
      calc |lam| * |X ω| ≤ (1/(4*K)) * |X ω| :=
            mul_le_mul_of_nonneg_right hlam (abs_nonneg _)
        _ = (|X ω|/K)/4 := by
            field_simp
    have hE : Real.exp |lam * X ω| ≤ Real.exp ((|X ω|/K)/4) :=
      Real.exp_le_exp.mpr habs
    have hmul : Real.exp (3*(|X ω|/K)/4) * Real.exp ((|X ω|/K)/4)
        = Real.exp (|X ω|/K) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hsq' : (lam * X ω)^2/2 = lam^2/2 * (X ω)^2 := by
      rw [mul_pow]
      ring
    have hB : (lam * X ω)^2/2 * Real.exp |lam * X ω|
        ≤ (8/9)*lam^2*K^2 * Real.exp (|X ω|/K) := by
      calc (lam * X ω)^2/2 * Real.exp |lam * X ω|
          = lam^2/2 * (X ω)^2 * Real.exp |lam * X ω| := by rw [hsq']
        _ ≤ lam^2/2 * ((16/9)*K^2 * Real.exp (3*(|X ω|/K)/4))
              * Real.exp ((|X ω|/K)/4) := by
            apply mul_le_mul _ hE (Real.exp_pos _).le (by positivity)
            exact mul_le_mul_of_nonneg_left hx2 (by positivity)
        _ = (8/9)*lam^2*K^2
              * (Real.exp (3*(|X ω|/K)/4) * Real.exp ((|X ω|/K)/4)) := by
            ring
        _ = (8/9)*lam^2*K^2 * Real.exp (|X ω|/K) := by rw [hmul]
    linarith [hA, hB]
  -- integrability
  have hXint : Integrable X μ := by
    refine (hEint.const_mul K).mono' hXm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    exact abs_le_mul_exp_abs_div hK
  have hg_int : Integrable
      (fun ω => 1 + lam * X ω + (8/9)*lam^2*K^2 * Real.exp (|X ω|/K)) μ :=
    ((integrable_const 1).add (hXint.const_mul lam)).add
      (hEint.const_mul ((8/9)*lam^2*K^2))
  have hexp_int : Integrable (fun ω => Real.exp (lam * X ω)) μ := by
    refine hg_int.mono'
      (measurable_exp.comp_aemeasurable (hXm.const_mul lam)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hptw ω
  -- take expectations
  have hint : ∫ ω, Real.exp (lam * X ω) ∂μ
      ≤ Real.exp ((16/9) * K^2 * lam^2) := by
    calc ∫ ω, Real.exp (lam * X ω) ∂μ
        ≤ ∫ ω, (1 + lam * X ω + (8/9)*lam^2*K^2 * Real.exp (|X ω|/K)) ∂μ :=
          integral_mono hexp_int hg_int hptw
      _ = 1 + lam * (∫ ω, X ω ∂μ)
            + (8/9)*lam^2*K^2 * ∫ ω, Real.exp (|X ω|/K) ∂μ := by
          have hi1 : Integrable (fun ω => 1 + lam * X ω) μ :=
            (integrable_const 1).add (hXint.const_mul lam)
          have hi2 : Integrable
              (fun ω => (8/9)*lam^2*K^2 * Real.exp (|X ω|/K)) μ :=
            hEint.const_mul _
          rw [integral_add hi1 hi2,
            integral_add (integrable_const 1) (hXint.const_mul lam),
            integral_const, integral_const_mul, integral_const_mul]
          simp
      _ = 1 + (8/9)*lam^2*K^2 * ∫ ω, Real.exp (|X ω|/K) ∂μ := by
          rw [hmean]
          ring
      _ ≤ 1 + (16/9)*K^2*lam^2 := by
          have hprod := mul_le_mul_of_nonneg_left hEle
            (show (0:ℝ) ≤ (8/9)*lam^2*K^2 by positivity)
          linarith
      _ ≤ Real.exp ((16/9) * K^2 * lam^2) := by
          have := Real.add_one_le_exp ((16/9) * K^2 * lam^2)
          linarith
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * X ω)) ∂μ
      = ENNReal.ofReal (∫ ω, Real.exp (lam * X ω) ∂μ) :=
        (ofReal_integral_eq_lintegral_ofReal hexp_int
          (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le)).symm
    _ ≤ ENNReal.ofReal (Real.exp ((16/9) * K^2 * lam^2)) :=
        ENNReal.ofReal_le_ofReal hint

/-- **Proposition 2.8.1(iv) at the attained norm** — the form used by
Theorem 2.9.1. The constraint is stated multiplicatively
(`|λ|·4‖X‖_{ψ₁} ≤ 1`), which is equivalent to `|λ| ≤ 1/(4‖X‖_{ψ₁})` for
positive norm and correctly degenerates to "no constraint" for an a.e.-zero
variable.

**Book Proposition 2.8.1(iv).** -/
theorem SubExponential.mgf_bound [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXm : AEMeasurable X μ) (h : SubExponential X μ)
    (hmean : ∫ ω, X ω ∂μ = 0) {lam : ℝ}
    (hlam : |lam| * (4 * psi1Norm X μ) ≤ 1) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * X ω)) ∂μ
      ≤ ENNReal.ofReal (Real.exp ((16/9) * (psi1Norm X μ)^2 * lam^2)) := by
  rcases eq_or_lt_of_le (psi1Norm_nonneg X μ) with h0 | h0
  · have hz := ae_eq_zero_of_psi1Norm_eq_zero hXm h h0.symm
    have hL : ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * X ω)) ∂μ = 1 := by
      have hcong : (fun ω => ENNReal.ofReal (Real.exp (lam * X ω)))
          =ᵐ[μ] fun _ => (1:ℝ≥0∞) := by
        filter_upwards [hz] with ω hω
        simp [hω]
      rw [lintegral_congr_ae hcong]
      simp
    rw [hL, ← h0]
    have harg : (16/9) * (0:ℝ)^2 * lam^2 = 0 := by ring
    rw [harg, Real.exp_zero]
    norm_num
  · refine subexponential_iii_to_iv hXm h0
      (psi1MGF_psi1Norm_le_two hXm h) hmean ?_
    rw [le_div_iff₀ (by linarith : (0:ℝ) < 4 * psi1Norm X μ)]
    exact hlam

/-! ## Book Theorem 2.9.1: Bernstein's inequality -/

/-- For independent mean-zero subexponential `X₁, …, X_N` with `‖Xᵢ‖_{ψ₁} ≤ K`
(the source's `K = maxᵢ‖Xᵢ‖_{ψ₁}` is the least such bound) and every `t ≥ 0`:
`ℙ{|∑ᵢXᵢ| ≥ t} ≤ 2exp(−c·min(t²/∑ᵢ‖Xᵢ‖²_{ψ₁}, t/K))`, with the absolute
constant produced explicitly as `c = 1/8`.

The Lean proof is the source's: the MGF product rule with the per-factor bound
(2.24) (valid for `|λ| ≤ 1/(4K) ≤ 1/(4‖Xᵢ‖_{ψ₁})`), the Chernoff step at
`λ = min(t/((32/9)σ²), 1/(4K))`, the two-regime optimization ("check!"), both
tails, and the union bound.

**Book Theorem 2.9.1.** -/
theorem bernstein_inequality [IsProbabilityMeasure μ] {N : ℕ}
    {X : Fin N → Ω → ℝ} (hXm : ∀ i, AEMeasurable (X i) μ)
    (hX : ∀ i, SubExponential (X i) μ) (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hindep : iIndepFun X μ) {K : ℝ} (hK : 0 < K)
    (hKb : ∀ i, psi1Norm (X i) μ ≤ K) {t : ℝ} (ht : 0 ≤ t) :
    μ {ω | t ≤ |∑ i, X i ω|}
      ≤ ENNReal.ofReal (2 * Real.exp (-(1/8) *
          min (t^2 / ∑ i, (psi1Norm (X i) μ)^2) (t / K))) := by
  classical
  set σsq : ℝ := ∑ i, (psi1Norm (X i) μ)^2 with hσsq
  have hσ0 : 0 ≤ σsq := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hSm : AEMeasurable (fun ω => ∑ i, X i ω) μ := by
    have h1 : AEMeasurable (∑ i, X i) μ :=
      Finset.aemeasurable_sum Finset.univ fun i _ => hXm i
    have h2 : (∑ i, X i) = fun ω => ∑ i, X i ω := by
      funext ω
      rw [Finset.sum_apply]
    rwa [h2] at h1
  rcases eq_or_lt_of_le hσ0 with hσzero | hσpos
  · -- degenerate case: the min vanishes and the bound is trivial
    rw [← hσzero, div_zero, min_eq_left (by positivity : (0:ℝ) ≤ t/K),
      mul_zero, Real.exp_zero, mul_one]
    calc μ {ω | t ≤ |∑ i, X i ω|} ≤ 1 := prob_le_one
      _ ≤ ENNReal.ofReal 2 := by norm_num
  · -- MGF bound for the sum, for constrained `λ`
    have hmgfS : ∀ lam : ℝ, |lam| ≤ 1/(4*K) →
        ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * ∑ i, X i ω)) ∂μ
          ≤ ENNReal.ofReal (Real.exp ((16/9)*lam^2*σsq)) := by
      intro lam hlam
      have hfac : ∀ i, Integrable (fun ω => Real.exp (lam * X i ω)) μ ∧
          mgf (X i) μ lam
            ≤ Real.exp ((16/9) * (psi1Norm (X i) μ)^2 * lam^2) := by
        intro i
        refine mgf_le_of_lintegral_exp_le (hXm i) (Real.exp_pos _).le ?_
        refine SubExponential.mgf_bound (hXm i) (hX i) (hmean i) ?_
        calc |lam| * (4 * psi1Norm (X i) μ) ≤ (1/(4*K)) * (4*K) := by
              apply mul_le_mul hlam _
                (by linarith [psi1Norm_nonneg (X i) μ]) (by positivity)
              linarith [hKb i]
          _ = 1 := by field_simp
      have hprod : mgf (fun ω => ∑ i, X i ω) μ lam = ∏ i, mgf (X i) μ lam := by
        have h2 : (fun ω => ∑ i, X i ω) = ∑ i, X i := by
          funext ω
          rw [Finset.sum_apply]
        rw [h2]
        exact iIndepFun.mgf_sum₀ hindep (fun i => hXm i) Finset.univ
      have hprod_le : mgf (fun ω => ∑ i, X i ω) μ lam
          ≤ Real.exp ((16/9)*lam^2*σsq) := by
        rw [hprod]
        calc ∏ i, mgf (X i) μ lam
            ≤ ∏ i, Real.exp ((16/9) * (psi1Norm (X i) μ)^2 * lam^2) :=
              Finset.prod_le_prod (fun i _ => mgf_nonneg) (fun i _ => (hfac i).2)
          _ = Real.exp (∑ i, (16/9) * (psi1Norm (X i) μ)^2 * lam^2) :=
              (Real.exp_sum _ _).symm
          _ = Real.exp ((16/9)*lam^2*σsq) := by
              congr 1
              rw [hσsq, Finset.mul_sum]
              exact Finset.sum_congr rfl fun i _ => by ring
      have hSexp_int : Integrable (fun ω => Real.exp (lam * ∑ i, X i ω)) μ := by
        by_contra hni
        have h0 : mgf (fun ω => ∑ i, X i ω) μ lam = 0 := by
          rw [mgf]
          exact integral_undef hni
        have hpos : 0 < ∏ i, mgf (X i) μ lam :=
          Finset.prod_pos fun i _ => mgf_pos' (NeZero.ne μ) (hfac i).1
        rw [hprod] at h0
        exact absurd h0 hpos.ne'
      calc ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * ∑ i, X i ω)) ∂μ
          = ENNReal.ofReal (mgf (fun ω => ∑ i, X i ω) μ lam) := by
            rw [mgf]
            exact (ofReal_integral_eq_lintegral_ofReal hSexp_int
              (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le)).symm
        _ ≤ ENNReal.ofReal (Real.exp ((16/9)*lam^2*σsq)) :=
            ENNReal.ofReal_le_ofReal hprod_le
    -- the optimizing `λ`
    set lamstar : ℝ := min (t/((32/9)*σsq)) (1/(4*K)) with hlamstar
    have hlnn : 0 ≤ lamstar := le_min (by positivity) (by positivity)
    have hlcon : |lamstar| ≤ 1/(4*K) := by
      rw [abs_of_nonneg hlnn]
      exact min_le_right _ _
    -- the optimization ("check!"): the exponent is at most `−(1/8)·min(...)`
    have hopt : -(lamstar*t) + (16/9)*lamstar^2*σsq
        ≤ -(1/8) * min (t^2/σsq) (t/K) := by
      rcases le_or_gt (t/((32/9)*σsq)) (1/(4*K)) with hcase | hcase
      · have hlmin : lamstar = t/((32/9)*σsq) := min_eq_left hcase
        have htK : t*K ≤ σsq := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)] at hcase
          nlinarith
        have hmin : min (t^2/σsq) (t/K) = t^2/σsq := by
          apply min_eq_left
          rw [div_le_div_iff₀ hσpos hK]
          nlinarith [ht]
        rw [hlmin, hmin]
        have hLexp : -(t/((32/9)*σsq)*t) + (16/9)*(t/((32/9)*σsq))^2*σsq
            = -(9/64)*(t^2/σsq) := by
          field_simp
          ring
        rw [hLexp]
        have hpos : (0:ℝ) ≤ t^2/σsq := by positivity
        linarith
      · have hlmin : lamstar = 1/(4*K) := min_eq_right hcase.le
        have h8 : 8*σsq < 9*(t*K) := by
          rw [div_lt_div_iff₀ (by positivity) (by positivity)] at hcase
          nlinarith
        have hL2 : -(1/(4*K)*t) + (16/9)*(1/(4*K))^2*σsq ≤ -(1/8)*(t/K) := by
          have h1 : (16/9)*(1/(4*K))^2*σsq = σsq/(9*K^2) := by
            field_simp
            ring
          have h2 : σsq/(9*K^2) ≤ t/(8*K) := by
            rw [div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith [hK, mul_lt_mul_of_pos_right h8 hK]
          have h3 : -(1/(4*K)*t) = -(t/(4*K)) := by ring
          have h4 : -(1/8)*(t/K) = -(t/(8*K)) := by ring
          have h5 : t/(4*K) - t/(8*K) = t/(8*K) := by ring
          rw [h1, h3, h4]
          linarith
        rw [hlmin]
        refine hL2.trans ?_
        have hminle : min (t^2/σsq) (t/K) ≤ t/K := min_le_right _ _
        linarith
    -- both tails via the Chernoff step
    have hright := meas_ge_le_of_exp_bound (t := t) hSm hlnn
      (hmgfS lamstar hlcon)
    have hmgfneg : ∫⁻ ω, ENNReal.ofReal
        (Real.exp (lamstar * (-(∑ i, X i ω)))) ∂μ
        ≤ ENNReal.ofReal (Real.exp ((16/9)*lamstar^2*σsq)) := by
      have h1 := hmgfS (-lamstar) (by rwa [abs_neg])
      calc ∫⁻ ω, ENNReal.ofReal (Real.exp (lamstar * (-(∑ i, X i ω)))) ∂μ
          = ∫⁻ ω, ENNReal.ofReal (Real.exp ((-lamstar) * ∑ i, X i ω)) ∂μ := by
            refine lintegral_congr fun ω => ?_
            congr 2
            ring
        _ ≤ ENNReal.ofReal (Real.exp ((16/9)*(-lamstar)^2*σsq)) := h1
        _ = ENNReal.ofReal (Real.exp ((16/9)*lamstar^2*σsq)) := by
            rw [neg_sq]
    have hleft := meas_ge_le_of_exp_bound
      (Y := fun ω => -(∑ i, X i ω)) (t := t) hSm.neg hlnn hmgfneg
    -- union bound
    have hsplit : {ω | t ≤ |∑ i, X i ω|}
        ⊆ {ω | t ≤ ∑ i, X i ω} ∪ {ω | t ≤ -(∑ i, X i ω)} := by
      intro ω hω
      simp only [Set.mem_setOf_eq, Set.mem_union] at hω ⊢
      rcases abs_cases (∑ i, X i ω) with ⟨heq, _⟩ | ⟨heq, _⟩
      · exact Or.inl (heq ▸ hω)
      · exact Or.inr (heq ▸ hω)
    have hB0 : (0:ℝ) ≤ Real.exp (-(lamstar*t))
        * Real.exp ((16/9)*lamstar^2*σsq) := by positivity
    calc μ {ω | t ≤ |∑ i, X i ω|}
        ≤ μ ({ω | t ≤ ∑ i, X i ω} ∪ {ω | t ≤ -(∑ i, X i ω)}) :=
          measure_mono hsplit
      _ ≤ μ {ω | t ≤ ∑ i, X i ω} + μ {ω | t ≤ -(∑ i, X i ω)} :=
          measure_union_le _ _
      _ ≤ ENNReal.ofReal (Real.exp (-(lamstar*t))
              * Real.exp ((16/9)*lamstar^2*σsq))
            + ENNReal.ofReal (Real.exp (-(lamstar*t))
              * Real.exp ((16/9)*lamstar^2*σsq)) := add_le_add hright hleft
      _ = ENNReal.ofReal (2 * (Real.exp (-(lamstar*t))
              * Real.exp ((16/9)*lamstar^2*σsq))) := by
          rw [← ENNReal.ofReal_add hB0 hB0]
          congr 1
          ring
      _ ≤ ENNReal.ofReal (2 * Real.exp (-(1/8) * min (t^2/σsq) (t/K))) := by
          apply ENNReal.ofReal_le_ofReal
          have hcomb : Real.exp (-(lamstar*t)) * Real.exp ((16/9)*lamstar^2*σsq)
              = Real.exp (-(lamstar*t) + (16/9)*lamstar^2*σsq) :=
            (Real.exp_add _ _).symm
          rw [hcomb]
          have hmono := Real.exp_le_exp.mpr hopt
          linarith

/-- Proposition 2.8.1, (iii) implies the source's local-MGF property (iv),
with `K₄ = 4 K₃`.

**Book Proposition 2.8.1.** -/
theorem subexponential_iii_to_iv_property [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hXm : AEMeasurable X μ) {K₃ : ℝ} (hK₃ : 0 < K₃)
    (hmgf : psi1MGF X μ K₃ ≤ 2) (hmean : ∫ ω, X ω ∂μ = 0) :
    ∀ lam : ℝ, |lam| ≤ 1 / (4 * K₃) →
      ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * X ω)) ∂μ
        ≤ ENNReal.ofReal (Real.exp ((4 * K₃) ^ 2 * lam ^ 2)) := by
  intro lam hlam
  refine (subexponential_iii_to_iv hXm hK₃ hmgf hmean hlam).trans ?_
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have hs : 0 ≤ K₃ ^ 2 * lam ^ 2 := by positivity
  nlinarith

/-- Proposition 2.8.1, (iv) implies (i), with `K₁ = 3 K₄`.

**Book Proposition 2.8.1.** -/
theorem subexponential_iv_to_i [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXm : AEMeasurable X μ) {K₄ : ℝ} (hK₄ : 0 < K₄)
    (h : ∀ lam : ℝ, |lam| ≤ 1 / K₄ →
      ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * X ω)) ∂μ
        ≤ ENNReal.ofReal (Real.exp (K₄ ^ 2 * lam ^ 2)))
    {t : ℝ} (_ht : 0 ≤ t) :
    μ {ω | t ≤ |X ω|} ≤ ENNReal.ofReal (2 * Real.exp (-t / (3 * K₄))) := by
  set lam : ℝ := 1 / K₄ with hlam
  have hlam0 : 0 ≤ lam := by positivity
  have hlam_abs : |lam| ≤ 1 / K₄ := by rw [abs_of_nonneg hlam0]
  have hmgf : ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * X ω)) ∂μ
      ≤ ENNReal.ofReal (Real.exp 1) := by
    have hb := h lam hlam_abs
    convert hb using 1
    congr 3
    rw [hlam]
    field_simp
  have hval : Real.exp (-(lam * t)) * Real.exp 1 = Real.exp (1 - t / K₄) := by
    rw [← Real.exp_add, hlam]
    congr 1
    ring
  have hright : μ {ω | t ≤ X ω} ≤ ENNReal.ofReal (Real.exp (1 - t / K₄)) := by
    have hb := meas_ge_le_of_exp_bound (t := t) hXm hlam0 hmgf
    rwa [hval] at hb
  have hleft : μ {ω | t ≤ -X ω} ≤ ENNReal.ofReal (Real.exp (1 - t / K₄)) := by
    have hmgfneg : ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * (-X ω))) ∂μ
        ≤ ENNReal.ofReal (Real.exp 1) := by
      have hneg : |-lam| ≤ lam := by rw [abs_neg, abs_of_nonneg hlam0]
      have hb := h (-lam) hneg
      have hb' : ∫⁻ ω, ENNReal.ofReal (Real.exp ((-lam) * X ω)) ∂μ
          ≤ ENNReal.ofReal (Real.exp 1) := by
        convert hb using 1
        congr 3
        rw [hlam]
        field_simp
      convert hb' using 1
      refine lintegral_congr fun ω => ?_
      congr 2
      ring
    have hb := meas_ge_le_of_exp_bound (t := t) hXm.neg hlam0 hmgfneg
    rwa [hval] at hb
  have hsub : {ω | t ≤ |X ω|} ⊆ {ω | t ≤ X ω} ∪ {ω | t ≤ -X ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, Set.mem_union] at hω ⊢
    rcases abs_cases (X ω) with ⟨he, _⟩ | ⟨he, _⟩
    · exact Or.inl (by linarith [hω, he.symm.le])
    · exact Or.inr (by linarith [hω, he.symm.le])
  have htwo : μ {ω | t ≤ |X ω|}
      ≤ ENNReal.ofReal (2 * Real.exp (1 - t / K₄)) := by
    calc
      μ {ω | t ≤ |X ω|}
          ≤ μ ({ω | t ≤ X ω} ∪ {ω | t ≤ -X ω}) := measure_mono hsub
      _ ≤ μ {ω | t ≤ X ω} + μ {ω | t ≤ -X ω} := measure_union_le _ _
      _ ≤ ENNReal.ofReal (Real.exp (1 - t / K₄))
            + ENNReal.ofReal (Real.exp (1 - t / K₄)) := add_le_add hright hleft
      _ = ENNReal.ofReal (2 * Real.exp (1 - t / K₄)) := by
            rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
            congr 1
            ring
  by_cases hlarge : (3 / 2 : ℝ) * K₄ ≤ t
  · exact htwo.trans (ENNReal.ofReal_le_ofReal (by
      gcongr
      field_simp
      nlinarith))
  · calc
      μ {ω | t ≤ |X ω|} ≤ 1 := prob_le_one
      _ ≤ ENNReal.ofReal (2 * Real.exp (-t / (3 * K₄))) := by
        rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by norm_num]
        apply ENNReal.ofReal_le_ofReal
        have ha : t / (3 * K₄) ≤ 1 / 2 := by
          rw [div_le_iff₀ (by positivity : (0 : ℝ) < 3 * K₄)]
          push Not at hlarge
          nlinarith
        have hehalf : Real.exp (1 / 2 : ℝ) ≤ 2 := by
          calc
            Real.exp (1 / 2 : ℝ) ≤ 1 / (1 - (1 / 2 : ℝ)) :=
              Real.exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num)
            _ = 2 := by norm_num
        have hea : Real.exp (t / (3 * K₄)) ≤ 2 :=
          (Real.exp_le_exp.mpr ha).trans hehalf
        calc
          1 = Real.exp (t / (3 * K₄)) * Real.exp (-t / (3 * K₄)) := by
                rw [← Real.exp_add]
                ring_nf
                simp
          _ ≤ 2 * Real.exp (-t / (3 * K₄)) :=
                mul_le_mul_of_nonneg_right hea (Real.exp_pos _).le



end HDP

end Source_19_Bernstein

/-! ## Material formerly in `20_BernsteinCorollaries.lean` -/

section Source_20_BernsteinCorollaries

open MeasureTheory ProbabilityTheory Real Filter
open scoped ENNReal NNReal Topology

namespace HDP

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Weighted/simplified Bernstein inequality.

**Book Corollary 2.9.2.** -/
theorem bernstein_weighted [IsProbabilityMeasure μ] {N : ℕ}
    {X : Fin N → Ω → ℝ} (a : Fin N → ℝ)
    (hXm : ∀ i, AEMeasurable (X i) μ)
    (hX : ∀ i, SubExponential (X i) μ) (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hindep : iIndepFun X μ) {K A : ℝ} (hK : 0 < K) (hA : 0 < A)
    (hKb : ∀ i, psi1Norm (X i) μ ≤ K) (ha : ∀ i, |a i| ≤ A)
    {t : ℝ} (ht : 0 ≤ t) :
    μ {ω | t ≤ |∑ i, a i * X i ω|}
      ≤ ENNReal.ofReal (2 * Real.exp (-(1/8) *
          min (t^2 / (K^2 * ∑ i, (a i)^2)) (t / (K * A)))) := by
  classical
  let Y : Fin N → Ω → ℝ := fun i ω => a i * X i ω
  have hYm : ∀ i, AEMeasurable (Y i) μ := fun i => (hXm i).const_mul (a i)
  have hY : ∀ i, SubExponential (Y i) μ := fun i => (hX i).const_mul (a i)
  have hYmean : ∀ i, ∫ ω, Y i ω ∂μ = 0 := by
    intro i
    simp only [Y]
    rw [integral_const_mul, hmean i, mul_zero]
  have hYindep : iIndepFun Y μ := by
    have hc := hindep.comp (fun i x => a i * x) (fun _ => by fun_prop)
    exact hc
  have hYnorm : ∀ i, psi1Norm (Y i) μ = |a i| * psi1Norm (X i) μ := by
    intro i
    exact psi1Norm_const_mul (X i) (a i)
  have hYbound : ∀ i, psi1Norm (Y i) μ ≤ K * A := by
    intro i
    rw [hYnorm i]
    have hmul := mul_le_mul (ha i) (hKb i) (psi1Norm_nonneg (X i) μ) hA.le
    nlinarith
  have hbase := bernstein_inequality hYm hY hYmean hYindep
    (mul_pos hK hA) hYbound ht
  let S : ℝ := ∑ i, (psi1Norm (Y i) μ)^2
  let V : ℝ := K^2 * ∑ i, (a i)^2
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hSV : S ≤ V := by
    dsimp only [S, V]
    calc ∑ i, (psi1Norm (Y i) μ)^2
        = ∑ i, (|a i| * psi1Norm (X i) μ)^2 := by
            apply Finset.sum_congr rfl
            intro i _
            rw [hYnorm i]
      _ ≤ ∑ i, (a i)^2 * K^2 := by
            apply Finset.sum_le_sum
            intro i _
            rw [mul_pow, sq_abs]
            exact mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (psi1Norm_nonneg (X i) μ) (hKb i) 2)
              (sq_nonneg (a i))
      _ = K^2 * ∑ i, (a i)^2 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
  rcases eq_or_lt_of_le hS0 with hSzero | hSpos
  · rcases eq_or_lt_of_le ht with rfl | htpos
    · simp
    · have hYnorm0 : ∀ i, psi1Norm (Y i) μ = 0 := by
        intro i
        have hi : (psi1Norm (Y i) μ)^2 ≤ S := by
          dsimp only [S]
          exact Finset.single_le_sum (fun j _ => sq_nonneg (psi1Norm (Y j) μ))
            (Finset.mem_univ i)
        rw [← hSzero] at hi
        nlinarith [sq_nonneg (psi1Norm (Y i) μ)]
      have hYzero : ∀ i, Y i =ᵐ[μ] 0 := fun i =>
        ae_eq_zero_of_psi1Norm_eq_zero (hYm i) (hY i) (hYnorm0 i)
      have hsumzero : (fun ω => ∑ i, Y i ω) =ᵐ[μ] 0 := by
        filter_upwards [ae_all_iff.mpr hYzero] with ω hω
        simp [hω]
      have hnull : μ {ω | t ≤ |∑ i, Y i ω|} = 0 := by
        have hsub : {ω | t ≤ |∑ i, Y i ω|} ⊆ {ω | (∑ i, Y i ω) ≠ 0} := by
          intro ω hω hz
          simp [hz] at hω
          linarith
        exact measure_mono_null hsub (MeasureTheory.ae_iff.mp hsumzero)
      rw [show {ω | t ≤ |∑ i, a i * X i ω|} = {ω | t ≤ |∑ i, Y i ω|} by rfl,
        hnull]
      positivity
  · have hVpos : 0 < V := lt_of_lt_of_le hSpos hSV
    have hfrac : t^2 / V ≤ t^2 / S :=
      div_le_div_of_nonneg_left (sq_nonneg t) hSpos hSV
    have hmin : min (t^2 / V) (t / (K*A))
        ≤ min (t^2 / S) (t / (K*A)) := min_le_min hfrac le_rfl
    calc μ {ω | t ≤ |∑ i, a i * X i ω|}
        ≤ ENNReal.ofReal (2 * Real.exp (-(1/8) *
            min (t^2 / S) (t / (K*A)))) := by simpa [Y, S] using hbase
      _ ≤ ENNReal.ofReal (2 * Real.exp (-(1/8) *
            min (t^2 / V) (t / (K*A)))) := by
          apply ENNReal.ofReal_le_ofReal
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply Real.exp_le_exp.mpr
          nlinarith [hmin]
      _ = ENNReal.ofReal (2 * Real.exp (-(1/8) *
            min (t^2 / (K^2 * ∑ i, (a i)^2)) (t / (K*A)))) := by rfl

/- Exercise 2.45 is not used by any main-line or later source result. Its proof
lives only in `Chapter2/Exercise/Sec09.lean`, keeping this core module free of
non-load-bearing exercise declarations. -/

/-- Normalized Bernstein has Gaussian small deviations and exponential large deviations.

**Book Remark 2.9.4.** -/
theorem remark_2_9_4 [IsProbabilityMeasure μ] {N : ℕ} (hN : 0 < N)
    {X : Fin N → Ω → ℝ} (hXm : ∀ i, AEMeasurable (X i) μ)
    (hX : ∀ i, SubExponential (X i) μ) (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hindep : iIndepFun X μ) {K : ℝ} (hK : 0 < K)
    (hKb : ∀ i, psi1Norm (X i) μ ≤ K) {t : ℝ} (ht : 0 ≤ t) :
    μ {ω | t ≤ |(∑ i, X i ω) / Real.sqrt N|}
      ≤ ENNReal.ofReal (2 * Real.exp (-(1/8) *
          min (t^2 / K^2) (t * Real.sqrt N / K))) := by
  classical
  set sN : ℝ := Real.sqrt N with hsN
  have hNreal : (0:ℝ) < N := by exact_mod_cast hN
  have hsNpos : 0 < sN := by simpa [hsN] using Real.sqrt_pos.mpr hNreal
  have hsNsq : sN^2 = (N:ℝ) := by
    rw [hsN, Real.sq_sqrt hNreal.le]
  have hsuma : ∑ _i : Fin N, ((1/sN : ℝ)^2) = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [hsNpos.ne']
    nlinarith
  have ha : ∀ i : Fin N, |(1/sN : ℝ)| ≤ 1/sN := by
    intro i
    rw [abs_of_pos (by positivity : (0:ℝ) < 1/sN)]
  have h := bernstein_weighted (μ := μ) (X := X) (fun _ : Fin N => 1/sN)
    hXm hX hmean hindep hK (by positivity : (0:ℝ) < 1/sN) hKb ha ht
  have hsum : ∀ ω, ∑ i, (1/sN) * X i ω = (∑ i, X i ω) / sN := by
    intro ω
    rw [← Finset.mul_sum]
    ring
  have hlin : t / (K * (1/sN)) = t*sN/K := by
    field_simp [hK.ne', hsNpos.ne']
  rw [hsuma, mul_one, hlin] at h
  have hevent : {ω | t ≤ |∑ i, (1/sN) * X i ω|} =
      {ω | t ≤ |(∑ i, X i ω) / sN|} := by
    ext ω
    simp only [Set.mem_setOf_eq, hsum]
  rw [hevent] at h
  simpa only [hsN] using h

end HDP

end Source_20_BernsteinCorollaries

/-! ## Material formerly in `21_BoundedBernstein.lean` -/

section Source_21_BoundedBernstein

/-!
# Bernstein inequality for bounded distributions

This file proves Hint 2.47, both parts of Exercise 2.47, and Theorem 2.9.5 with
the source constants. The main theorem handles the zero-variance case explicitly.
-/

open MeasureTheory ProbabilityTheory Real Filter
open scoped ENNReal NNReal Topology

namespace HDP

/-- The exact numeric inequality in Hint 2.47.

**Lean implementation helper.** -/
theorem exp_le_one_add_add_sq_div_one_sub_abs_third {z : ℝ} (hz : |z| < 3) :
    Real.exp z ≤ 1 + z + (z ^ 2 / 2) / (1 - |z| / 3) := by
  let f : ℕ → ℝ := fun n ↦ z ^ n / Nat.factorial n
  let g : ℕ → ℝ := fun n ↦ z ^ 2 / 2 * (|z| / 3) ^ n
  have hf : Summable f := by
    simpa [f] using Real.summable_pow_div_factorial z
  have hr0 : 0 ≤ |z| / 3 := by positivity
  have hr1 : |z| / 3 < 1 := by linarith
  have hg : Summable g := by
    exact (summable_geometric_of_lt_one hr0 hr1).mul_left (z ^ 2 / 2)
  have hterm : ∀ n, f (n + 2) ≤ g n := by
    intro n
    have hfacNat : 2 * 3 ^ n ≤ Nat.factorial (n + 2) := by
      simpa [Nat.add_comm] using (@Nat.factorial_mul_pow_le_factorial 2 n)
    have hfac : (2 : ℝ) * 3 ^ n ≤ (Nat.factorial (n + 2) : ℕ) := by
      exact_mod_cast hfacNat
    have hden : (0 : ℝ) < (Nat.factorial (n + 2) : ℕ) := by positivity
    have hsmall : (0 : ℝ) < 2 * 3 ^ n := by positivity
    calc
      f (n + 2) = z ^ (n + 2) / (Nat.factorial (n + 2) : ℕ) := by rfl
      _ ≤ |z| ^ (n + 2) / (Nat.factorial (n + 2) : ℕ) := by
        apply div_le_div_of_nonneg_right _ hden.le
        simpa only [abs_pow] using le_abs_self (z ^ (n + 2))
      _ ≤ |z| ^ (n + 2) / (2 * 3 ^ n) := by
        exact div_le_div_of_nonneg_left (by positivity) hsmall hfac
      _ = g n := by
        dsimp [g]
        rw [pow_add, sq_abs, div_pow]
        field_simp
  have htail : (∑' n, f (n + 2)) ≤ ∑' n, g n :=
    (hf.comp_injective (fun _ _ h ↦ Nat.add_right_cancel h)).tsum_le_tsum hterm hg
  have hsplit := hf.sum_add_tsum_nat_add 2
  have hgeom : (∑' n, g n) = (z ^ 2 / 2) / (1 - |z| / 3) := by
    rw [show (∑' n, g n) = (z ^ 2 / 2) * ∑' n : ℕ, (|z| / 3) ^ n by
      simp only [g, tsum_mul_left]]
    rw [tsum_geometric_of_lt_one hr0 hr1]
    ring
  have hinit : ∑ i ∈ Finset.range 2, f i = 1 + z := by
    norm_num [f, Finset.sum_range_succ, Nat.factorial]
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  change (∑' n, f n) ≤ _
  rw [hgeom] at htail
  calc
    (∑' n, f n) = (∑ i ∈ Finset.range 2, f i) + ∑' i, f (i + 2) := hsplit.symm
    _ ≤ (∑ i ∈ Finset.range 2, f i) + (z ^ 2 / 2) / (1 - |z| / 3) :=
      add_le_add_right htail _
    _ = 1 + z + (z ^ 2 / 2) / (1 - |z| / 3) := by rw [hinit]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- An almost-everywhere absolute bound by an `L²` random variable implies membership in `L²`.

**Lean implementation helper.** -/
theorem memLp_two_of_ae_abs_le [IsFiniteMeasure μ] {X : Ω → ℝ} {K : ℝ}
    (hXm : AEMeasurable X μ) (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ K) : MemLp X 2 μ := by
  exact MemLp.of_bound hXm.aestronglyMeasurable K (by
    filter_upwards [hbound] with ω hω
    simpa only [Real.norm_eq_abs] using hω)

/-- An almost-everywhere bound `|X| ≤ K` makes the `exp_mul_of_ae_abs_le` integrand `ω ↦ exp (lam * X ω)` integrable on every finite measure space.

**Lean implementation helper.** -/
theorem integrable_exp_mul_of_ae_abs_le [IsFiniteMeasure μ] {X : Ω → ℝ} {K lam : ℝ}
    (hXm : AEMeasurable X μ) (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ K) :
    Integrable (fun ω ↦ Real.exp (lam * X ω)) μ := by
  refine (memLp_top_of_bound
    (measurable_exp.comp_aemeasurable (hXm.const_mul lam)).aestronglyMeasurable
    (Real.exp (|lam| * K)) ?_).integrable le_top
  filter_upwards [hbound] with ω hω
  change |Real.exp (lam * X ω)| ≤ Real.exp (|lam| * K)
  rw [abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc
    lam * X ω ≤ |lam * X ω| := le_abs_self _
    _ = |lam| * |X ω| := abs_mul _ _
    _ ≤ |lam| * K := mul_le_mul_of_nonneg_left hω (abs_nonneg _)

/-- The
variance-sensitive MGF bound.

**Book Exercise 2.47(a).** -/
theorem exercise_2_47_a [IsProbabilityMeasure μ] {X : Ω → ℝ} {K lam : ℝ}
    (hK : 0 < K) (hXm : AEMeasurable X μ)
    (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ K)
    (hmean : ∫ ω, X ω ∂μ = 0) (hlam : |lam| < 3 / K) :
    mgf X μ lam ≤ Real.exp
      (((lam ^ 2 / 2) / (1 - |lam| * K / 3)) * ∫ ω, X ω ^ 2 ∂μ) := by
  have hmem : MemLp X 2 μ := memLp_two_of_ae_abs_le hXm hbound
  have hlamK : |lam| * K < 3 := (lt_div_iff₀ hK).mp hlam
  have hden : 0 < 1 - |lam| * K / 3 := by
    nlinarith
  have hptw : ∀ᵐ ω ∂μ, Real.exp (lam * X ω) ≤
      1 + lam * X ω + ((lam ^ 2 / 2) / (1 - |lam| * K / 3)) * X ω ^ 2 := by
    filter_upwards [hbound] with ω hω
    have hz : |lam * X ω| < 3 := by
      rw [abs_mul]
      calc
        |lam| * |X ω| ≤ |lam| * K :=
          mul_le_mul_of_nonneg_left hω (abs_nonneg _)
        _ < 3 := hlamK
    have hnum : 0 ≤ (lam * X ω) ^ 2 / 2 := by positivity
    have hdenω : 0 < 1 - |lam * X ω| / 3 := by
      nlinarith [abs_nonneg (lam * X ω)]
    have hdenle : 1 - |lam| * K / 3 ≤ 1 - |lam * X ω| / 3 := by
      rw [abs_mul]
      have := mul_le_mul_of_nonneg_left hω (abs_nonneg lam)
      linarith
    have hfrac : (lam * X ω) ^ 2 / 2 / (1 - |lam * X ω| / 3) ≤
        (lam * X ω) ^ 2 / 2 / (1 - |lam| * K / 3) :=
      div_le_div_of_nonneg_left hnum hden hdenle
    have hn := exp_le_one_add_add_sq_div_one_sub_abs_third hz
    calc
      Real.exp (lam * X ω) ≤
          1 + lam * X ω + (lam * X ω) ^ 2 / 2 / (1 - |lam * X ω| / 3) := hn
      _ ≤ 1 + lam * X ω + (lam * X ω) ^ 2 / 2 /
          (1 - |lam| * K / 3) := by linarith
      _ = 1 + lam * X ω + ((lam ^ 2 / 2) / (1 - |lam| * K / 3)) * X ω ^ 2 := by
        ring
  have hexp : Integrable (fun ω ↦ Real.exp (lam * X ω)) μ :=
    integrable_exp_mul_of_ae_abs_le hXm hbound
  have hpoly : Integrable (fun ω ↦
      1 + lam * X ω + ((lam ^ 2 / 2) / (1 - |lam| * K / 3)) * X ω ^ 2) μ :=
    ((integrable_const 1).add (hmem.integrable one_le_two |>.const_mul lam)).add
      (hmem.integrable_sq.const_mul _)
  have hint : mgf X μ lam ≤
      1 + ((lam ^ 2 / 2) / (1 - |lam| * K / 3)) * ∫ ω, X ω ^ 2 ∂μ := by
    rw [mgf]
    calc
      ∫ ω, Real.exp (lam * X ω) ∂μ ≤ ∫ ω,
          (1 + lam * X ω + ((lam ^ 2 / 2) /
            (1 - |lam| * K / 3)) * X ω ^ 2) ∂μ :=
        integral_mono_ae hexp hpoly hptw
      _ = 1 + lam * (∫ ω, X ω ∂μ) +
          ((lam ^ 2 / 2) / (1 - |lam| * K / 3)) * ∫ ω, X ω ^ 2 ∂μ := by
        rw [integral_add, integral_add, integral_const, integral_const_mul,
          integral_const_mul]
        · simp
        · exact integrable_const 1
        · exact hmem.integrable one_le_two |>.const_mul lam
        · exact (integrable_const 1).add (hmem.integrable one_le_two |>.const_mul lam)
        · exact hmem.integrable_sq.const_mul _
      _ = 1 + ((lam ^ 2 / 2) / (1 - |lam| * K / 3)) * ∫ ω, X ω ^ 2 ∂μ := by
        rw [hmean]
        ring
  let u : ℝ := ((lam ^ 2 / 2) / (1 - |lam| * K / 3)) *
    (∫ ω, X ω ^ 2 ∂μ)
  exact hint.trans (by simpa only [u, add_comm] using Real.add_one_le_exp u)

/-- `exercise_2_47_a_variance` gives the centered bounded-variable estimate `mgf X μ lam ≤ exp (((lam² / 2) / (1 - |lam|K / 3)) * Var[X; μ])` when `|lam| < 3 / K`.

**Lean implementation helper.** -/
theorem exercise_2_47_a_variance [IsProbabilityMeasure μ] {X : Ω → ℝ}
    {K lam : ℝ} (hK : 0 < K) (hXm : AEMeasurable X μ)
    (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ K)
    (hmean : ∫ ω, X ω ∂μ = 0) (hlam : |lam| < 3 / K) :
    mgf X μ lam ≤ Real.exp
      (((lam ^ 2 / 2) / (1 - |lam| * K / 3)) * Var[X; μ]) := by
  rw [variance_of_integral_eq_zero hXm hmean]
  exact exercise_2_47_a hK hXm hbound hmean hlam

/-- Variance form of Exercise 2.47(b), used to prove the source's second-moment form.

**Book Theorem 2.9.5.** -/
theorem bernstein_bounded_variance [IsProbabilityMeasure μ] {N : ℕ}
    {X : Fin N → Ω → ℝ} (hXm : ∀ i, Measurable (X i))
    (hindep : iIndepFun X μ) {K : ℝ} (hK : 0 < K)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ K)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |∑ i, X i ω|} ≤
      2 * Real.exp (-(t ^ 2 / 2) / (∑ i, Var[X i; μ] + K * t / 3)) := by
  classical
  let S : Ω → ℝ := fun ω => ∑ i, X i ω
  let σsq : ℝ := ∑ i, Var[X i; μ]
  have hmem : ∀ i, MemLp (X i) 2 μ := fun i =>
    memLp_two_of_ae_abs_le (hXm i).aemeasurable (hbound i)
  have hσ0 : 0 ≤ σsq := by
    dsimp only [σsq]
    exact Finset.sum_nonneg fun i _ => variance_nonneg (X i) μ
  have hmgfS : ∀ lam : ℝ, |lam| < 3 / K →
      Integrable (fun ω => Real.exp (lam * S ω)) μ ∧
      mgf S μ lam ≤ Real.exp
        (((lam ^ 2 / 2) / (1 - |lam| * K / 3)) * σsq) := by
    intro lam hlam
    have hint : Integrable (fun ω => Real.exp (lam * S ω)) μ := by
      have h := hindep.integrable_exp_mul_sum (t := lam) hXm
        (s := Finset.univ) (fun i _ =>
          integrable_exp_mul_of_ae_abs_le (lam := lam)
            (hXm i).aemeasurable (hbound i))
      simpa only [S, Finset.sum_apply] using h
    refine ⟨hint, ?_⟩
    have hprod : mgf S μ lam = ∏ i, mgf (X i) μ lam := by
      have hSfun : S = ∑ i, X i := by
        funext ω
        simp only [S, Finset.sum_apply]
      rw [hSfun]
      simpa using hindep.mgf_sum₀ (fun i => (hXm i).aemeasurable) Finset.univ
    rw [hprod]
    calc
      ∏ i, mgf (X i) μ lam ≤
          ∏ i, Real.exp
            (((lam ^ 2 / 2) / (1 - |lam| * K / 3)) * Var[X i; μ]) :=
        Finset.prod_le_prod (fun i _ => mgf_nonneg)
          (fun i _ => exercise_2_47_a_variance hK (hXm i).aemeasurable
            (hbound i) (hmean i) hlam)
      _ = Real.exp (∑ i,
          ((lam ^ 2 / 2) / (1 - |lam| * K / 3)) * Var[X i; μ]) :=
        (Real.exp_sum _ _).symm
      _ = Real.exp
          (((lam ^ 2 / 2) / (1 - |lam| * K / 3)) * σsq) := by
        congr 1
        simp only [σsq, Finset.mul_sum]
  rcases eq_or_lt_of_le ht with rfl | htpos
  · simp only [zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_div,
      neg_zero, Real.exp_zero, mul_one]
    exact measureReal_le_one.trans (by norm_num)
  rcases eq_or_lt_of_le hσ0 with hσzero | hσpos
  · have hXzero : ∀ i, ∀ᵐ ω ∂μ, X i ω = 0 := by
      intro i
      have hi_le : Var[X i; μ] ≤ σsq := by
        dsimp only [σsq]
        exact Finset.single_le_sum (fun j _ => variance_nonneg (X j) μ)
          (Finset.mem_univ i)
      have hi0 : Var[X i; μ] = 0 := by
        rw [← hσzero] at hi_le
        exact le_antisymm hi_le (variance_nonneg (X i) μ)
      filter_upwards [ae_eq_integral_of_variance_eq_zero (hmem i) hi0] with ω hω
      simpa only [hmean i] using hω
    have hSzero : ∀ᵐ ω ∂μ, S ω = 0 := by
      filter_upwards [ae_all_iff.mpr hXzero] with ω hω
      simp only [S, hω, Finset.sum_const_zero]
    have hsub : {ω | t ≤ |S ω|} ⊆ {ω | S ω ≠ 0} := by
      intro ω hω hz
      simp only [Set.mem_setOf_eq] at hω ⊢
      rw [hz, abs_zero] at hω
      linarith
    have hnull : μ {ω | t ≤ |S ω|} = 0 :=
      measure_mono_null hsub (MeasureTheory.ae_iff.mp hSzero)
    have hnull_real : μ.real {ω | t ≤ |S ω|} = 0 := by
      simp only [Measure.real, hnull, ENNReal.toReal_zero]
    rw [show {ω | t ≤ |∑ i, X i ω|} = {ω | t ≤ |S ω|} by rfl,
      hnull_real]
    positivity
  · let d : ℝ := σsq + K * t / 3
    let lam : ℝ := t / d
    have hdpos : 0 < d := by
      dsimp only [d]
      positivity
    have hlam0 : 0 ≤ lam := by
      dsimp only [lam]
      positivity
    have hlam : |lam| < 3 / K := by
      rw [abs_of_nonneg hlam0, lt_div_iff₀ hK]
      dsimp only [lam]
      rw [div_mul_eq_mul_div, div_lt_iff₀ hdpos]
      dsimp only [d]
      nlinarith
    have hmgfpos := hmgfS lam hlam
    have hmgfneg := hmgfS (-lam) (by simpa only [abs_neg] using hlam)
    have hopt :
        -(lam * t) + ((lam ^ 2 / 2) / (1 - lam * K / 3)) * σsq =
          -(t ^ 2 / 2) / d := by
      dsimp only [lam, d]
      field_simp [hσpos.ne']
      ring
    have hright : μ.real {ω | t ≤ S ω} ≤
        Real.exp (-(t ^ 2 / 2) / d) := by
      calc
        μ.real {ω | t ≤ S ω} ≤
            Real.exp (-lam * t) * mgf S μ lam :=
          measure_ge_le_exp_mul_mgf t hlam0 hmgfpos.1
        _ ≤ Real.exp (-lam * t) * Real.exp
            (((lam ^ 2 / 2) / (1 - |lam| * K / 3)) * σsq) :=
          mul_le_mul_of_nonneg_left hmgfpos.2 (Real.exp_pos _).le
        _ = Real.exp (-(t ^ 2 / 2) / d) := by
          rw [← Real.exp_add, abs_of_nonneg hlam0]
          congr 1
          have hoptnf := hopt
          ring_nf at hoptnf ⊢
          exact hoptnf
    have hleft : μ.real {ω | S ω ≤ -t} ≤
        Real.exp (-(t ^ 2 / 2) / d) := by
      calc
        μ.real {ω | S ω ≤ -t} ≤
            Real.exp (-(-lam) * (-t)) * mgf S μ (-lam) :=
          measure_le_le_exp_mul_mgf (-t) (by linarith) hmgfneg.1
        _ ≤ Real.exp (-(-lam) * (-t)) * Real.exp
            ((((-lam) ^ 2 / 2) / (1 - |-lam| * K / 3)) * σsq) :=
          mul_le_mul_of_nonneg_left hmgfneg.2 (Real.exp_pos _).le
        _ = Real.exp (-(t ^ 2 / 2) / d) := by
          rw [← Real.exp_add, abs_neg, abs_of_nonneg hlam0, neg_sq]
          congr 1
          have hoptnf := hopt
          ring_nf at hoptnf ⊢
          exact hoptnf
    have hsplit : {ω | t ≤ |S ω|} ⊆
        {ω | t ≤ S ω} ∪ {ω | S ω ≤ -t} := by
      intro ω hω
      simp only [Set.mem_setOf_eq, Set.mem_union] at hω ⊢
      rcases abs_cases (S ω) with ⟨heq, _⟩ | ⟨heq, _⟩
      · exact Or.inl (heq ▸ hω)
      · exact Or.inr (by nlinarith [heq ▸ hω])
    change μ.real {ω | t ≤ |S ω|} ≤ _
    change _ ≤ 2 * Real.exp (-(t ^ 2 / 2) / d)
    calc
      μ.real {ω | t ≤ |S ω|} ≤
          μ.real ({ω | t ≤ S ω} ∪ {ω | S ω ≤ -t}) :=
        measureReal_mono hsplit
      _ ≤ μ.real {ω | t ≤ S ω} + μ.real {ω | S ω ≤ -t} :=
        measureReal_union_le _ _
      _ ≤ Real.exp (-(t ^ 2 / 2) / d) + Real.exp (-(t ^ 2 / 2) / d) :=
        add_le_add hright hleft
      _ = 2 * Real.exp (-(t ^ 2 / 2) / d) := by ring

/-- With
`σ² = ∑ i, 𝔼(Xᵢ²)` as in the theorem.

**Book Exercise 2.47(b).** -/
theorem exercise_2_47_b [IsProbabilityMeasure μ] {N : ℕ}
    {X : Fin N → Ω → ℝ} (hXm : ∀ i, Measurable (X i))
    (hindep : iIndepFun X μ) {K : ℝ} (hK : 0 < K)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ K)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |∑ i, X i ω|} ≤
      2 * Real.exp (-(t ^ 2 / 2) /
        ((∑ i, ∫ ω, X i ω ^ 2 ∂μ) + K * t / 3)) := by
  have h := bernstein_bounded_variance hXm hindep hK hbound hmean ht
  have hvariance : (∑ i, Var[X i; μ]) = ∑ i, ∫ ω, X i ω ^ 2 ∂μ := by
    apply Finset.sum_congr rfl
    intro i _
    exact variance_of_integral_eq_zero (hXm i).aemeasurable (hmean i)
  rwa [hvariance] at h

/-- Theorem 2.9.5 (Bernstein inequality for bounded distributions).

**Book Theorem 2.9.5.** -/
theorem bernstein_bounded [IsProbabilityMeasure μ] {N : ℕ}
    {X : Fin N → Ω → ℝ} (hXm : ∀ i, Measurable (X i))
    (hindep : iIndepFun X μ) {K : ℝ} (hK : 0 < K)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ K)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |∑ i, X i ω|} ≤
      2 * Real.exp (-(t ^ 2 / 2) /
        ((∑ i, ∫ ω, X i ω ^ 2 ∂μ) + K * t / 3)) :=
  exercise_2_47_b hXm hindep hK hbound hmean ht

/-- Variance-sensitive Bernstein inequality for bounded variables.

**Book Theorem 2.9.5.** -/
theorem theorem_2_9_5 [IsProbabilityMeasure μ] {N : ℕ}
    {X : Fin N → Ω → ℝ} (hXm : ∀ i, Measurable (X i))
    (hindep : iIndepFun X μ) {K : ℝ} (hK : 0 < K)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ K)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |∑ i, X i ω|} ≤
      2 * Real.exp (-(t ^ 2 / 2) /
        ((∑ i, ∫ ω, X i ω ^ 2 ∂μ) + K * t / 3)) :=
  bernstein_bounded hXm hindep hK hbound hmean ht

namespace Chapter2

/-- The numerical estimate used in Exercise 2.47 converts the bounded-variable MGF denominator to the Bernstein form.

**Lean implementation helper.** -/
theorem hint_2_47_numeric {z : ℝ} (hz : |z| < 3) :
    Real.exp z ≤ 1 + z + (z ^ 2 / 2) / (1 - |z| / 3) :=
  HDP.exp_le_one_add_add_sq_div_one_sub_abs_third hz

/-- Variance-sensitive bounded MGF and Bernstein.

**Book Exercise 2.47(a,b).** -/
theorem exercise_2_47a [IsProbabilityMeasure μ] {X : Ω → ℝ} {K lam : ℝ}
    (hK : 0 < K) (hXm : AEMeasurable X μ)
    (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ K)
    (hmean : ∫ ω, X ω ∂μ = 0) (hlam : |lam| < 3 / K) :
    mgf X μ lam ≤ Real.exp
      (((lam ^ 2 / 2) / (1 - |lam| * K / 3)) * ∫ ω, X ω ^ 2 ∂μ) :=
  HDP.exercise_2_47_a hK hXm hbound hmean hlam

/-- Variance-sensitive bounded MGF and Bernstein.

**Book Exercise 2.47(a,b).** -/
theorem exercise_2_47b [IsProbabilityMeasure μ] {N : ℕ}
    {X : Fin N → Ω → ℝ} (hXm : ∀ i, Measurable (X i))
    (hindep : iIndepFun X μ) {K : ℝ} (hK : 0 < K)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ K)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |∑ i, X i ω|} ≤
      2 * Real.exp (-(t ^ 2 / 2) /
        ((∑ i, ∫ ω, X i ω ^ 2 ∂μ) + K * t / 3)) :=
  HDP.exercise_2_47_b hXm hindep hK hbound hmean ht

/-- Independent centered bounded variables satisfy the variance-sensitive Bernstein tail inequality.

**Book Theorem 2.9.5.** -/
theorem bernstein_bounded [IsProbabilityMeasure μ] {N : ℕ}
    {X : Fin N → Ω → ℝ} (hXm : ∀ i, Measurable (X i))
    (hindep : iIndepFun X μ) {K : ℝ} (hK : 0 < K)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ K)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |∑ i, X i ω|} ≤
      2 * Real.exp (-(t ^ 2 / 2) /
        ((∑ i, ∫ ω, X i ω ^ 2 ∂μ) + K * t / 3)) :=
  HDP.bernstein_bounded hXm hindep hK hbound hmean ht

/-- Source-numbered Chapter 2 alias for Theorem 2.9.5.

**Book Theorem 2.9.5.** -/
theorem theorem_2_9_5 [IsProbabilityMeasure μ] {N : ℕ}
    {X : Fin N → Ω → ℝ} (hXm : ∀ i, Measurable (X i))
    (hindep : iIndepFun X μ) {K : ℝ} (hK : 0 < K)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ K)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |∑ i, X i ω|} ≤
      2 * Real.exp (-(t ^ 2 / 2) /
        ((∑ i, ∫ ω, X i ω ^ 2 ∂μ) + K * t / 3)) :=
  bernstein_bounded hXm hindep hK hbound hmean ht

end Chapter2

end HDP

end Source_21_BoundedBernstein
