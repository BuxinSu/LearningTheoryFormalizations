/-
Copyright (c) 2026 Buxin Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Buxin Su
-/

import HighDimensionalProbability.Prelude.RandomVector
import HighDimensionalProbability.Chapter2_ConcentrationOfIndependentSums
import Mathlib.Analysis.Complex.ExponentialBounds
import HighDimensionalProbability.Chapter1_AnalysisAndProbabilityRefresher
import Mathlib.Probability.Independence.Integration
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import HighDimensionalProbability.Prelude.Sphere
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.Convex.Independent
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Probability.Distributions.Beta
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Probability.UniformOn
import Mathlib.Tactic.FinCases
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Convex.Basic
import HighDimensionalProbability.Prelude.Basic
import HighDimensionalProbability.Prelude.SimpleGraph
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.InnerProductSpace.Reproducing
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Chapter 3 — Random Vectors in High Dimensions

## Contents

- §3.1 Concentration of the norm
  - Independent subgaussian coordinates have a concentrated Euclidean norm.
    **Book Theorem 3.1.1; Equations (3.1)–(3.5).**
- §3.2 Covariance matrices and principal component analysis
  - Centered/uncentered covariance identities and operator properties.
    **Book Section 3.2; Proposition 3.2.1;
    Equations (3.6)–(3.7); Proposition 3.2.2.**
  - Principal components and effective rank. **Book Corollary 3.2.3;
    Definition 3.2.5.**
- §3.3 Examples of high-dimensional distributions
  - Product distributions. **Book Proposition 3.3.1; Corollaries 3.3.2–3.3.3.**
  - General Gaussian vectors as arbitrary rectangular affine images.
    **Book Definition 3.3.4.**
  - Spherical and Gaussian models. **Book Propositions 3.3.5–3.3.8;
    Equations (3.12)–(3.17).**
  - Concentration in the Euclidean ball and canonical examples.
    **Book Theorem 3.3.9; Examples 3.3.12–3.3.15.**
- §3.4 Subgaussian distributions in higher dimensions
  - Subgaussian random vectors and one-dimensional marginals.
    **Book Definition 3.4.1; Lemma 3.4.2; Examples 3.4.3–3.4.4.**
  - Norm concentration and standard examples. **Book Theorem 3.4.5;
    Equations (3.19)–(3.21); Examples 3.4.6–3.4.8.**
- §3.5 Grothendieck inequality and semidefinite programming
  - Semidefinite relaxation and randomized rounding. **Book Theorem 3.5.1;
    Equations (3.22)–(3.29); Proposition 3.5.6.**
  - Grothendieck's inequality. **Book Theorem 3.5.7.**
- §3.6 Maximum cut for graphs
  - Cut objectives and their semidefinite relaxation. **Book Definitions 3.6.1–3.6.2;
    Proposition 3.6.3; Theorem 3.6.4.**
  - The rounding identity and approximation ratio. **Book Lemma 3.6.5;
    Equation (3.35).**
- §3.7 Kernel trick and tightening of Grothendieck
  - General product-axis tensor spaces and their canonical inner product.
    **Book Definition 3.7.1; Equation (3.36).**
  - Positive-semidefinite kernels and feature maps. **Book Examples 3.7.2–3.7.3;
    Lemmas 3.7.4 and 3.7.7.**
  - Polynomial and Gaussian kernel embeddings. **Book Equations (3.37)–(3.38).**
-/

/-! ## Material formerly in `01_NormConcentration.lean` -/

section Source_01_NormConcentration

/-!
# Book Chapter 3, Section 3.1: concentration of the norm

The proof follows the book: square the coordinates, center, apply Bernstein,
and transfer the resulting two-level tail estimate through the square root.
-/

open MeasureTheory ProbabilityTheory Real Filter
open scoped BigOperators ENNReal NNReal Topology

namespace HDP.Chapter3

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The elementary square-root transfer inequality.

**Book Equation (3.4).** -/
lemma max_le_abs_sq_sub_one {z δ : ℝ} (hz : 0 ≤ z) (hδ : 0 ≤ δ)
    (h : δ ≤ |z - 1|) : max δ (δ ^ 2) ≤ |z ^ 2 - 1| := by
  by_cases hz1 : z ≤ 1
  · rw [abs_of_nonpos (sub_nonpos.mpr hz1)] at h
    rw [abs_of_nonpos (by nlinarith [sq_nonneg z])]
    apply max_le
    · nlinarith
    · have hδ1 : δ ≤ 1 := by nlinarith
      nlinarith [sq_nonneg (δ - 1), sq_nonneg z]
  · have hz1' : 1 ≤ z := le_of_not_ge hz1
    rw [abs_of_nonneg (sub_nonneg.mpr hz1')] at h
    rw [abs_of_nonneg (by nlinarith [sq_nonneg z])]
    apply max_le
    · nlinarith [mul_nonneg (sub_nonneg.mpr hz1') (by nlinarith : 0 ≤ z + 1)]
    · have hs : (z - 1) ^ 2 ≤ z ^ 2 - 1 := by nlinarith
      nlinarith [sq_le_sq₀ hδ (sub_nonneg.mpr hz1') |>.2 h]

/-- Unit second moment forces every uniform ψ₂ bound to be bounded away from
zero. This is the quantitative observation used after (3.3).

**Lean implementation helper.** -/
lemma one_le_two_mul_sq_of_secondMoment_one [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hXm : AEMeasurable X μ) (hX : HDP.SubGaussian X μ)
    (hsecond : ∫ ω, X ω ^ 2 ∂μ = 1) {K : ℝ} (hK : 0 < K)
    (hKb : HDP.psi2Norm X μ ≤ K) : 1 ≤ 2 * K ^ 2 := by
  have hlp : HDP.Chapter1.lpNormRV X 2 μ = 1 := by
    rw [HDP.Chapter1.lpNormRV]
    have habs : (∫ ω, |X ω| ^ (2 : ℝ) ∂μ) = 1 := by
      convert hsecond using 1
      · apply integral_congr_ae
        filter_upwards [] with ω
        norm_num [sq_abs]
    rw [habs]
    norm_num
  have hmom := hX.moment_bound hXm (p := (2 : ℝ)) (by norm_num)
  have hlow : 1 ≤ K * Real.sqrt 2 := by
    calc
      1 = HDP.Chapter1.lpNormRV X 2 μ := hlp.symm
      _ ≤ HDP.psi2Norm X μ * Real.sqrt 2 := hmom
      _ ≤ K * Real.sqrt 2 :=
        mul_le_mul_of_nonneg_right hKb (Real.sqrt_nonneg 2)
  have hsq : (1 : ℝ) ^ 2 ≤ (K * Real.sqrt 2) ^ 2 :=
    (sq_le_sq₀ (by norm_num) (mul_nonneg hK.le (Real.sqrt_nonneg 2))).2 hlow
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at hsq
  nlinarith

/-- The centered squares used in the proof of Theorem 3.1.1 have ψ₁ norm at
most `4 K²`.

**Book Theorem 3.1.1.** -/
lemma centered_sq_psi1Norm_le [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hXm : AEMeasurable X μ) (hX : HDP.SubGaussian X μ)
    (hsecond : ∫ ω, X ω ^ 2 ∂μ = 1) {K : ℝ} (hK : 0 < K)
    (hKb : HDP.psi2Norm X μ ≤ K) :
    HDP.SubExponential (fun ω => X ω ^ 2 - 1) μ ∧
      HDP.psi1Norm (fun ω => X ω ^ 2 - 1) μ ≤ 4 * K ^ 2 := by
  have hsqsub : HDP.SubExponential (fun ω => X ω ^ 2) μ :=
    (HDP.subExponential_sq_iff X).2 hX
  have hcenter := HDP.psi1Norm_centering (μ := μ) (hXm.pow_const 2) hsqsub
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc4 : 1 + 1 / Real.log 2 ≤ (4 : ℝ) := by
    have hone : (1 : ℝ) ≤ 3 * Real.log 2 := by
      nlinarith [Real.log_two_gt_d9]
    have hdiv : (1 : ℝ) / Real.log 2 ≤ 3 :=
      (div_le_iff₀ hlog).2 (by simpa [mul_comm] using hone)
    linarith
  have hsquares : HDP.psi2Norm X μ ^ 2 ≤ K ^ 2 :=
    (sq_le_sq₀ (HDP.psi2Norm_nonneg X μ) hK.le).2 hKb
  constructor
  · simpa [hsecond] using hcenter.1
  · calc
      HDP.psi1Norm (fun ω => X ω ^ 2 - 1) μ
          ≤ (1 + 1 / Real.log 2) * HDP.psi1Norm (fun ω => X ω ^ 2) μ := by
            simpa [hsecond] using hcenter.2
      _ = (1 + 1 / Real.log 2) * HDP.psi2Norm X μ ^ 2 := by
            rw [HDP.psi1Norm_sq hXm hX]
      _ ≤ 4 * HDP.psi2Norm X μ ^ 2 :=
            mul_le_mul_of_nonneg_right hc4 (sq_nonneg _)
      _ ≤ 4 * K ^ 2 := mul_le_mul_of_nonneg_left hsquares (by norm_num)

/-- Directly in the weighted-sum form supplied by Bernstein.

**Book Equation (3.3).** -/
theorem norm_sq_bernstein [IsProbabilityMeasure μ] {n : ℕ} (hn : 0 < n)
    {X : Fin n → Ω → ℝ} (hXm : ∀ i, AEMeasurable (X i) μ)
    (hX : ∀ i, HDP.SubGaussian (X i) μ)
    (hsecond : ∀ i, ∫ ω, X i ω ^ 2 ∂μ = 1)
    (hindep : iIndepFun X μ) {K : ℝ} (hK : 0 < K)
    (hKb : ∀ i, HDP.psi2Norm (X i) μ ≤ K) {u : ℝ} (hu : 0 ≤ u) :
    μ {ω | u ≤ |∑ i : Fin n, (1 / (n : ℝ)) * (X i ω ^ 2 - 1)|}
      ≤ ENNReal.ofReal (2 * Real.exp (-(1 / 8) *
          min (u ^ 2 / ((4 * K ^ 2) ^ 2 *
            ∑ _i : Fin n, (1 / (n : ℝ)) ^ 2))
            (u / ((4 * K ^ 2) * (1 / (n : ℝ)))))) := by
  let Y : Fin n → Ω → ℝ := fun i ω => X i ω ^ 2 - 1
  have hYm : ∀ i, AEMeasurable (Y i) μ := fun i =>
    (hXm i).pow_const 2 |>.sub aemeasurable_const
  have hY : ∀ i, HDP.SubExponential (Y i) μ := fun i =>
    (centered_sq_psi1Norm_le (hXm i) (hX i) (hsecond i) hK (hKb i)).1
  have hYnorm : ∀ i, HDP.psi1Norm (Y i) μ ≤ 4 * K ^ 2 := fun i =>
    (centered_sq_psi1Norm_le (hXm i) (hX i) (hsecond i) hK (hKb i)).2
  have hmem : ∀ i, MemLp (X i) 2 μ := fun i => by
    simpa using (hX i).memLp (hXm i) (p := (2 : ℝ)) (by norm_num)
  have hYmean : ∀ i, ∫ ω, Y i ω ∂μ = 0 := by
    intro i
    rw [show (fun ω => Y i ω) = fun ω => X i ω ^ 2 - 1 by rfl,
      integral_sub (hmem i).integrable_sq (integrable_const 1),
      hsecond i, integral_const]
    simp
  have hYindep : iIndepFun Y μ := by
    have hc := hindep.comp
      (fun _ : Fin n => fun x : ℝ => x ^ 2 - 1) (fun _ => by fun_prop)
    simpa [Y, Function.comp_def] using hc
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have ha : ∀ _i : Fin n, |(1 / (n : ℝ))| ≤ 1 / (n : ℝ) := by
    intro i
    rw [abs_of_pos (by positivity : (0 : ℝ) < 1 / (n : ℝ))]
  simpa [Y] using
    (HDP.bernstein_weighted (μ := μ) (X := Y)
      (fun _ : Fin n => 1 / (n : ℝ)) hYm hY hYmean hYindep
      (show 0 < 4 * K ^ 2 by positivity)
      (show 0 < 1 / (n : ℝ) by positivity) hYnorm ha hu)

/-- An explicit absolute constant for the source Theorem 3.1.1.

**Book Theorem 3.1.1.** -/
noncomputable def normConcentrationConstant : ℝ :=
  4 * Real.sqrt 5 * Real.sqrt 8

/-- Shows that `normConcentrationConstant` is positive.

**Lean implementation helper.** -/
lemma normConcentrationConstant_pos : 0 < normConcentrationConstant := by
  unfold normConcentrationConstant
  positivity

/-- The Euclidean norm is written as the square root of the coordinate-square
sum, which avoids introducing an artificial random-vector wrapper around the
coordinate family.

**Book Theorem 3.1.1.** -/
theorem concentration_norm [IsProbabilityMeasure μ] {n : ℕ} (hn : 0 < n)
    {X : Fin n → Ω → ℝ} (hXm : ∀ i, AEMeasurable (X i) μ)
    (hX : ∀ i, HDP.SubGaussian (X i) μ)
    (hsecond : ∀ i, ∫ ω, X i ω ^ 2 ∂μ = 1)
    (hindep : iIndepFun X μ) {K : ℝ} (hK : 0 < K)
    (hKb : ∀ i, HDP.psi2Norm (X i) μ ≤ K) :
    HDP.SubGaussian
        (fun ω => Real.sqrt (∑ i : Fin n, X i ω ^ 2) - Real.sqrt n) μ ∧
      HDP.psi2Norm
        (fun ω => Real.sqrt (∑ i : Fin n, X i ω ^ 2) - Real.sqrt n) μ
        ≤ normConcentrationConstant * K ^ 2 := by
  let R : Ω → ℝ := fun ω => Real.sqrt (∑ i : Fin n, X i ω ^ 2)
  let sn : ℝ := Real.sqrt n
  let L : ℝ := 4 * K ^ 2
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsn : 0 < sn := by simpa [sn] using Real.sqrt_pos.mpr hnR
  have hsnsq : sn ^ 2 = (n : ℝ) := by
    simp [sn, Real.sq_sqrt hnR.le]
  have hL : 0 < L := by
    dsimp only [L]
    positivity
  let i0 : Fin n := ⟨0, hn⟩
  have hKunit := one_le_two_mul_sq_of_secondMoment_one
    (hXm i0) (hX i0) (hsecond i0) hK (hKb i0)
  have hL1 : 1 ≤ L := by
    dsimp only [L]
    nlinarith
  have hsum_meas : AEMeasurable (fun ω => ∑ i : Fin n, X i ω ^ 2) μ := by
    have hs := Finset.aemeasurable_sum (s := (Finset.univ : Finset (Fin n)))
      (fun i hi => (hXm i).pow_const 2)
    convert hs using 1
    funext ω
    simp
  have hdev_meas : AEMeasurable (fun ω => R ω - sn) μ := by
    exact (Real.continuous_sqrt.measurable.comp_aemeasurable hsum_meas).sub
      aemeasurable_const
  have htail : ∀ t : ℝ, 0 ≤ t →
      μ {ω | t ≤ |R ω - sn|} ≤
        ENNReal.ofReal
          (2 * Real.exp (-t ^ 2 / (Real.sqrt 8 * L) ^ 2)) := by
    intro t ht
    let δ : ℝ := t / sn
    let u : ℝ := max δ (δ ^ 2)
    have hδ : 0 ≤ δ := div_nonneg ht hsn.le
    have hu : 0 ≤ u := le_trans hδ (le_max_left _ _)
    have hδu : δ ≤ u := le_max_left _ _
    have hδsqu : δ ^ 2 ≤ u := le_max_right _ _
    have hsum_nonneg : ∀ ω, 0 ≤ ∑ i : Fin n, X i ω ^ 2 := fun ω =>
      Finset.sum_nonneg fun i hi => sq_nonneg _
    have hRnonneg : ∀ ω, 0 ≤ R ω := fun ω => Real.sqrt_nonneg _
    have hRsq : ∀ ω, (R ω) ^ 2 = ∑ i : Fin n, X i ω ^ 2 := fun ω => by
      dsimp only [R]
      exact Real.sq_sqrt (hsum_nonneg ω)
    have hweighted : ∀ ω,
        (∑ i : Fin n, (1 / (n : ℝ)) * (X i ω ^ 2 - 1)) =
          (R ω) ^ 2 / (sn ^ 2) - 1 := by
      intro ω
      rw [hRsq, hsnsq]
      rw [← Finset.mul_sum]
      simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      field_simp
    have hsubset : {ω | t ≤ |R ω - sn|} ⊆
        {ω | u ≤ |∑ i : Fin n, (1 / (n : ℝ)) * (X i ω ^ 2 - 1)|} := by
      intro ω hω
      have hnorm : δ ≤ |R ω / sn - 1| := by
        dsimp only [δ]
        rw [div_sub_one hsn.ne', abs_div]
        rw [abs_of_pos hsn]
        exact (div_le_div_iff_of_pos_right hsn).2 hω
      have hsq := max_le_abs_sq_sub_one
        (div_nonneg (hRnonneg ω) hsn.le) hδ hnorm
      change u ≤ |∑ i : Fin n, (1 / (n : ℝ)) * (X i ω ^ 2 - 1)|
      rw [hweighted ω]
      convert hsq using 1
      field_simp [hsn.ne']
    have hbern := norm_sq_bernstein hn hXm hX hsecond hindep hK hKb hu
    have hsuma : ∑ _i : Fin n, (1 / (n : ℝ)) ^ 2 = 1 / (n : ℝ) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    have htdelta : (n : ℝ) * δ ^ 2 = t ^ 2 := by
      dsimp only [δ]
      rw [← hsnsq]
      field_simp [hsn.ne']
    have hu_sq : δ ^ 2 ≤ u ^ 2 :=
      (sq_le_sq₀ hδ hu).2 hδu
    have hterm1 :
        u ^ 2 / (L ^ 2 * (1 / (n : ℝ))) =
          (n : ℝ) * u ^ 2 / L ^ 2 := by
      field_simp [hL.ne', ne_of_gt hnR]
    have hterm2 :
        u / (L * (1 / (n : ℝ))) = (n : ℝ) * u / L := by
      field_simp [hL.ne', ne_of_gt hnR]
    have hfirst : t ^ 2 / L ^ 2 ≤
        u ^ 2 / (L ^ 2 * (1 / (n : ℝ))) := by
      rw [hterm1]
      apply (div_le_div_iff_of_pos_right (sq_pos_of_pos hL)).2
      calc
        t ^ 2 = (n : ℝ) * δ ^ 2 := htdelta.symm
        _ ≤ (n : ℝ) * u ^ 2 :=
          mul_le_mul_of_nonneg_left hu_sq hnR.le
    have huL : u ≤ u * L := by nlinarith [mul_nonneg hu (sub_nonneg.mpr hL1)]
    have hsecond' : t ^ 2 / L ^ 2 ≤
        u / (L * (1 / (n : ℝ))) := by
      rw [hterm2]
      have heq : (n : ℝ) * u / L = ((n : ℝ) * u * L) / L ^ 2 := by
        field_simp [hL.ne']
      rw [heq]
      apply (div_le_div_iff_of_pos_right (sq_pos_of_pos hL)).2
      calc
        t ^ 2 = (n : ℝ) * δ ^ 2 := htdelta.symm
        _ ≤ (n : ℝ) * u :=
          mul_le_mul_of_nonneg_left hδsqu hnR.le
        _ ≤ (n : ℝ) * (u * L) :=
          mul_le_mul_of_nonneg_left huL hnR.le
        _ = (n : ℝ) * u * L := by ring
    have hmin : t ^ 2 / L ^ 2 ≤
        min (u ^ 2 / (L ^ 2 * (1 / (n : ℝ))))
          (u / (L * (1 / (n : ℝ)))) := le_min hfirst hsecond'
    calc
      μ {ω | t ≤ |R ω - sn|}
          ≤ μ {ω | u ≤ |∑ i : Fin n,
              (1 / (n : ℝ)) * (X i ω ^ 2 - 1)|} := measure_mono hsubset
      _ ≤ ENNReal.ofReal (2 * Real.exp (-(1 / 8) *
          min (u ^ 2 / (L ^ 2 * ∑ _i : Fin n, (1 / (n : ℝ)) ^ 2))
            (u / (L * (1 / (n : ℝ)))))) := by
              simpa [L] using hbern
      _ = ENNReal.ofReal (2 * Real.exp (-(1 / 8) *
          min (u ^ 2 / (L ^ 2 * (1 / (n : ℝ))))
            (u / (L * (1 / (n : ℝ)))))) := by rw [hsuma]
      _ ≤ ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (Real.sqrt 8 * L) ^ 2)) := by
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Real.exp_le_exp.mpr
        calc
          -(1 / 8 : ℝ) *
              min (u ^ 2 / (L ^ 2 * (1 / (n : ℝ))))
                (u / (L * (1 / (n : ℝ))))
              ≤ -(1 / 8 : ℝ) * (t ^ 2 / L ^ 2) :=
            mul_le_mul_of_nonpos_left hmin (by norm_num)
          _ = -t ^ 2 / (Real.sqrt 8 * L) ^ 2 := by
            have hden : (Real.sqrt 8 * L) ^ 2 = 8 * L ^ 2 := by
              rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8)]
            rw [hden]
            field_simp [hL.ne']
  have htail' := HDP.psi2Norm_le_of_tail_bound hdev_meas
    (show 0 < Real.sqrt 8 * L by positivity) htail
  constructor
  · simpa [R, sn] using htail'.1
  · have hb := htail'.2
    change HDP.psi2Norm (fun ω => R ω - sn) μ ≤
      normConcentrationConstant * K ^ 2
    calc
      HDP.psi2Norm (fun ω => R ω - sn) μ
          ≤ Real.sqrt 5 * (Real.sqrt 8 * L) := hb
      _ = normConcentrationConstant * K ^ 2 := by
        simp [normConcentrationConstant, L]
        ring

end HDP.Chapter3

end Source_01_NormConcentration

/-! ## Material formerly in `02_ThinShell.lean` -/

section Source_02_ThinShell

/-!
# Thin-shell refinements

This thematic module contains the fourth-moment thin-shell refinement used in
later chapters, together with reusable proof infrastructure. Theorems whose
source exercises are not used downstream receive descriptive core names and
are exposed source-facing only from the exercise leaf.
-/

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators ENNReal NNReal RealInnerProductSpace

namespace HDP.Chapter3

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Defines `euclideanRadius`, the euclidean radius used in the surrounding construction.

**Lean implementation helper.** -/
noncomputable def euclideanRadius {n : ℕ}
    (X : Fin n → Ω → ℝ) (ω : Ω) : ℝ :=
  Real.sqrt (∑ i, X i ω ^ 2)

/-- Shows that the Euclidean radius is almost everywhere measurable.

**Lean implementation helper.** -/
private lemma euclideanRadius_aemeasurable {n : ℕ} {X : Fin n → Ω → ℝ}
    (hXm : ∀ i, AEMeasurable (X i) μ) :
    AEMeasurable (euclideanRadius X) μ := by
  change AEMeasurable (fun ω => Real.sqrt (∑ i : Fin n, X i ω ^ 2)) μ
  simpa only [Finset.sum_apply] using
    (Finset.aemeasurable_sum Finset.univ fun i _ => (hXm i).pow_const 2).sqrt

/-! ## A bounded fourth-moment helper for Exercise 3.3 -/

/-- A finite independent centered sum has fourth moment at most
`3 V² + L² V` when every summand is bounded in absolute value by `L`, where
`V` is the sum of the second moments. This elementary estimate is the
reverse-moment input used below; it is proved by adjoining one independent
summand at a time.

**Lean implementation helper.** -/
private theorem fourthMoment_finsetSum_le
    [IsProbabilityMeasure μ] {ι : Type*}
    {Z : ι → Ω → ℝ} (hZm : ∀ i, Measurable (Z i))
    (hindep : iIndepFun Z μ) (hmean : ∀ i, ∫ ω, Z i ω ∂μ = 0)
    {L : ℝ} (hL : 0 ≤ L) (hbound : ∀ i ω, |Z i ω| ≤ L)
    (s : Finset ι) :
    (∫ ω, (∑ i ∈ s, Z i ω) ^ 4 ∂μ) ≤
      3 * (∑ i ∈ s, ∫ ω, Z i ω ^ 2 ∂μ) ^ 2 +
        L ^ 2 * (∑ i ∈ s, ∫ ω, Z i ω ^ 2 ∂μ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      let S : Ω → ℝ := fun ω => ∑ i ∈ s, Z i ω
      let V : ℝ := ∑ i ∈ s, ∫ ω, Z i ω ^ 2 ∂μ
      let v : ℝ := ∫ ω, Z a ω ^ 2 ∂μ
      have hSm : Measurable S := by
        dsimp [S]
        exact Finset.measurable_sum s fun i _ => hZm i
      have hSbound : ∀ ω, |S ω| ≤ (s.card : ℝ) * L := by
        intro ω
        calc
          |S ω| ≤ ∑ i ∈ s, |Z i ω| := by
            dsimp [S]
            exact Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _i ∈ s, L :=
            Finset.sum_le_sum fun i _ => hbound i ω
          _ = (s.card : ℝ) * L := by simp
      have hC0 : 0 ≤ (s.card : ℝ) * L :=
        mul_nonneg (Nat.cast_nonneg _) hL
      have hpolyInt (p q : ℕ) :
          Integrable (fun ω => S ω ^ p * Z a ω ^ q) μ := by
        refine Integrable.of_bound
          (((hSm.pow_const p).mul ((hZm a).pow_const q)).aestronglyMeasurable)
          (((s.card : ℝ) * L) ^ p * L ^ q) ?_
        filter_upwards [] with ω
        rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_pow]
        exact mul_le_mul
          (pow_le_pow_left₀ (abs_nonneg _) (hSbound ω) p)
          (pow_le_pow_left₀ (abs_nonneg _) (hbound a ω) q)
          (pow_nonneg (abs_nonneg _) q) (pow_nonneg hC0 p)
      have hSint : Integrable S μ := by
        simpa using hpolyInt 1 0
      have hZint : Integrable (Z a) μ := by
        have h := hpolyInt 0 1
        simpa using h
      have hSmean : ∫ ω, S ω ∂μ = 0 := by
        dsimp [S]
        rw [integral_finsetSum]
        · exact Finset.sum_eq_zero fun i _ => hmean i
        · exact fun i _ => by
            refine Integrable.of_bound (hZm i).aestronglyMeasurable L ?_
            filter_upwards [] with ω
            simpa [Real.norm_eq_abs] using hbound i ω
      have hSZ : IndepFun S (Z a) μ := by
        have h := hindep.indepFun_finsetSum_of_notMem hZm ha
        have hfun : (∑ i ∈ s, Z i) = S := by
          funext ω
          simp [S, Finset.sum_apply]
        rwa [hfun] at h
      have hcross (p q : ℕ) :
          (∫ ω, S ω ^ p * Z a ω ^ q ∂μ) =
            (∫ ω, S ω ^ p ∂μ) * (∫ ω, Z a ω ^ q ∂μ) := by
        have hi := (hSZ.comp (measurable_id.pow_const p)
          (measurable_id.pow_const q)).integral_fun_mul_eq_mul_integral
            ((hSm.pow_const p).aestronglyMeasurable)
            (((hZm a).pow_const q).aestronglyMeasurable)
        simpa [Function.comp_def] using hi
      have hS2 : (∫ ω, S ω ^ 2 ∂μ) = V := by
        have hmem : ∀ i ∈ s, MemLp (Z i) 2 μ := by
          intro i hi
          exact (memLp_top_of_bound (hZm i).aestronglyMeasurable L
            (Filter.Eventually.of_forall fun ω => by
              simpa [Real.norm_eq_abs] using hbound i ω)).mono_exponent (by simp)
        have hvar := IndepFun.variance_sum hmem
          (fun i hi j hj hij => hindep.indepFun hij)
        have hsumFun : (∑ i ∈ s, Z i) = S := by
          funext ω
          simp [S, Finset.sum_apply]
        rw [hsumFun] at hvar
        have hSvar : Var[S; μ] = ∫ ω, S ω ^ 2 ∂μ := by
          have h := variance_eq_sub
            ((memLp_top_of_bound hSm.aestronglyMeasurable ((s.card : ℝ) * L)
              (Filter.Eventually.of_forall fun ω => by
                simpa [Real.norm_eq_abs] using hSbound ω)).mono_exponent (by simp) :
              MemLp S 2 μ)
          rw [hSmean] at h
          simpa using h
        have hZiVar : ∀ i ∈ s, Var[Z i; μ] = ∫ ω, Z i ω ^ 2 ∂μ := by
          intro i hi
          have h := variance_eq_sub (hmem i hi)
          rw [hmean i] at h
          simpa using h
        rw [hSvar] at hvar
        calc
          (∫ ω, S ω ^ 2 ∂μ) = ∑ i ∈ s, Var[Z i; μ] := hvar
          _ = ∑ i ∈ s, ∫ ω, Z i ω ^ 2 ∂μ :=
            Finset.sum_congr rfl fun i hi => hZiVar i hi
          _ = V := rfl
      have h31 : (∫ ω, S ω ^ 3 * Z a ω ∂μ) = 0 := by
        have h := hcross 3 1
        simp only [pow_one] at h
        rw [h, hmean a, mul_zero]
      have h13 : (∫ ω, S ω * Z a ω ^ 3 ∂μ) = 0 := by
        have h := hcross 1 3
        simp only [pow_one] at h
        rw [h, hSmean, zero_mul]
      have h22 : (∫ ω, S ω ^ 2 * Z a ω ^ 2 ∂μ) = V * v := by
        rw [hcross 2 2, hS2]
      have hZ4 : (∫ ω, Z a ω ^ 4 ∂μ) ≤ L ^ 2 * v := by
        have hpt : ∀ ω, Z a ω ^ 4 ≤ L ^ 2 * Z a ω ^ 2 := by
          intro ω
          have hs : Z a ω ^ 2 ≤ L ^ 2 := by
            have h := pow_le_pow_left₀ (abs_nonneg (Z a ω)) (hbound a ω) 2
            simpa [sq_abs] using h
          nlinarith [sq_nonneg (Z a ω)]
        have hleft : Integrable (fun ω => Z a ω ^ 4) μ := by
          simpa using hpolyInt 0 4
        have hright : Integrable (fun ω => L ^ 2 * Z a ω ^ 2) μ := by
          exact (by simpa using hpolyInt 0 2 : Integrable (fun ω => Z a ω ^ 2) μ).const_mul _
        calc
          (∫ ω, Z a ω ^ 4 ∂μ) ≤ ∫ ω, L ^ 2 * Z a ω ^ 2 ∂μ :=
            integral_mono hleft hright hpt
          _ = L ^ 2 * v := by rw [integral_const_mul]
      have hexpand : ∀ ω,
          (S ω + Z a ω) ^ 4 =
            S ω ^ 4 + 4 * (S ω ^ 3 * Z a ω) +
              6 * (S ω ^ 2 * Z a ω ^ 2) +
              4 * (S ω * Z a ω ^ 3) + Z a ω ^ 4 := by
        intro ω
        ring
      have hS4int : Integrable (fun ω => S ω ^ 4) μ := by
        simpa using hpolyInt 4 0
      have h31int : Integrable (fun ω => S ω ^ 3 * Z a ω) μ := by
        simpa only [pow_one] using hpolyInt 3 1
      have h22int : Integrable (fun ω => S ω ^ 2 * Z a ω ^ 2) μ := hpolyInt 2 2
      have h13int : Integrable (fun ω => S ω * Z a ω ^ 3) μ := by
        simpa only [pow_one] using hpolyInt 1 3
      have hZ4int : Integrable (fun ω => Z a ω ^ 4) μ := by
        simpa using hpolyInt 0 4
      have hintExpand :
          (∫ ω, (S ω + Z a ω) ^ 4 ∂μ) =
            (∫ ω, S ω ^ 4 ∂μ) + 4 * (∫ ω, S ω ^ 3 * Z a ω ∂μ) +
              6 * (∫ ω, S ω ^ 2 * Z a ω ^ 2 ∂μ) +
              4 * (∫ ω, S ω * Z a ω ^ 3 ∂μ) +
              (∫ ω, Z a ω ^ 4 ∂μ) := by
        rw [integral_congr_ae (Filter.Eventually.of_forall hexpand)]
        rw [integral_add, integral_add, integral_add, integral_add,
          integral_const_mul, integral_const_mul, integral_const_mul]
        all_goals fun_prop
      have hrec : (∫ ω, S ω ^ 4 ∂μ) ≤ 3 * V ^ 2 + L ^ 2 * V := by
        simpa [S, V] using ih
      have hlhs : (∫ ω, (∑ i ∈ insert a s, Z i ω) ^ 4 ∂μ) =
          ∫ ω, (S ω + Z a ω) ^ 4 ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with ω
        rw [Finset.sum_insert ha]
        dsimp [S]
        ring
      have hVinsert : (∑ i ∈ insert a s, ∫ ω, Z i ω ^ 2 ∂μ) = v + V := by
        rw [Finset.sum_insert ha]
      rw [hlhs, hVinsert]
      rw [hintExpand, h31, h22, h13]
      nlinarith [hrec, hZ4, sq_nonneg v]

/-- Paley--Zygmund plus the preceding fourth-moment estimate gives a uniform
`L¹` lower bound for a bounded independent centered sum.

**Lean implementation helper.** -/
private theorem integral_abs_sum_ge_of_bounded
    [IsProbabilityMeasure μ] {n : ℕ} (hn : 0 < n)
    {Z : Fin n → Ω → ℝ} (hZm : ∀ i, Measurable (Z i))
    (hindep : iIndepFun Z μ) (hmean : ∀ i, ∫ ω, Z i ω ∂μ = 0)
    {a L : ℝ} (ha : 0 < a) (hL : 0 ≤ L)
    (hbound : ∀ i ω, |Z i ω| ≤ L)
    (hsecond : ∀ i, a ≤ ∫ ω, Z i ω ^ 2 ∂μ)
    (hscale : L ^ 2 ≤ (n : ℝ) * a) :
    (1 / 32 : ℝ) * Real.sqrt ((n : ℝ) * a) ≤
      ∫ ω, |∑ i, Z i ω| ∂μ := by
  classical
  let S : Ω → ℝ := fun ω => ∑ i, Z i ω
  let V : ℝ := ∑ i, ∫ ω, Z i ω ^ 2 ∂μ
  let W : Ω → ℝ := fun ω => S ω ^ 2
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hna : 0 < (n : ℝ) * a := mul_pos hnR ha
  have hSm : Measurable S := by
    dsimp [S]
    exact Finset.measurable_sum Finset.univ fun i _ => hZm i
  have hSbound : ∀ ω, |S ω| ≤ (n : ℝ) * L := by
    intro ω
    calc
      |S ω| ≤ ∑ i, |Z i ω| := by
        dsimp [S]
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, L := Finset.sum_le_sum fun i _ => hbound i ω
      _ = (n : ℝ) * L := by simp
  have hZmem : ∀ i, MemLp (Z i) 2 μ := fun i =>
    (memLp_top_of_bound (hZm i).aestronglyMeasurable L
      (Filter.Eventually.of_forall fun ω => by
        simpa [Real.norm_eq_abs] using hbound i ω)).mono_exponent (by simp)
  have hS2 : (∫ ω, S ω ^ 2 ∂μ) = V := by
    have h := HDP.pythagorean_identity hZmem hmean
      (fun i _ j _ hij => hindep.indepFun hij)
    simpa [S, V] using h
  have hVlower : (n : ℝ) * a ≤ V := by
    calc
      (n : ℝ) * a = ∑ _i : Fin n, a := by simp
      _ ≤ ∑ i, ∫ ω, Z i ω ^ 2 ∂μ :=
        Finset.sum_le_sum fun i _ => hsecond i
      _ = V := rfl
  have hVpos : 0 < V := hna.trans_le hVlower
  have hS4 : (∫ ω, S ω ^ 4 ∂μ) ≤ 4 * V ^ 2 := by
    have hraw := fourthMoment_finsetSum_le hZm hindep hmean hL hbound Finset.univ
    have hLV : L ^ 2 ≤ V := hscale.trans hVlower
    have hV0 : 0 ≤ V := hVpos.le
    calc
      (∫ ω, S ω ^ 4 ∂μ) ≤ 3 * V ^ 2 + L ^ 2 * V := by
        simpa [S, V] using hraw
      _ ≤ 4 * V ^ 2 := by nlinarith
  have hWm : Measurable W := hSm.pow_const 2
  have hWbound : ∀ ω, |W ω| ≤ ((n : ℝ) * L) ^ 2 := by
    intro ω
    dsimp [W]
    rw [abs_of_nonneg (sq_nonneg _)]
    simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hSbound ω) 2
  have hW2 : MemLp W 2 μ :=
    (memLp_top_of_bound hWm.aestronglyMeasurable (((n : ℝ) * L) ^ 2)
      (Filter.Eventually.of_forall hWbound)).mono_exponent (by simp)
  have hWmean : (∫ ω, W ω ∂μ) = V := by simpa [W] using hS2
  have hWsq : (∫ ω, W ω ^ 2 ∂μ) = ∫ ω, S ω ^ 4 ∂μ := by
    apply integral_congr_ae
    filter_upwards [] with ω
    simp [W]
    ring
  have hE4pos : 0 < ∫ ω, S ω ^ 4 ∂μ := by
    have hvarW := variance_nonneg W μ
    rw [variance_eq_sub hW2] at hvarW
    change 0 ≤ (∫ ω, W ω ^ 2 ∂μ) - (∫ ω, W ω ∂μ) ^ 2 at hvarW
    rw [hWmean, hWsq] at hvarW
    nlinarith [sq_pos_of_pos hVpos]
  let ε : Set.Icc (0 : ℝ) 1 := ⟨1 / 2, by constructor <;> norm_num⟩
  let A : Set Ω := {ω | V / 2 < S ω ^ 2}
  have hAmeas : MeasurableSet A := by
    dsimp [A]
    exact measurableSet_lt measurable_const (hSm.pow_const 2)
  have hpz := HDP.Chapter1.exercise_1_16 hWm
    (Filter.Eventually.of_forall fun ω => sq_nonneg (S ω)) hW2 ε
  have hpz' : ((1 : ℝ) / 4) * V ^ 2 /
        (∫ ω, S ω ^ 4 ∂μ) ≤ μ.real A := by
    dsimp [ε] at hpz
    rw [hWmean, hWsq] at hpz
    norm_num at hpz
    simpa [A, W, div_eq_mul_inv, mul_comm] using hpz
  have hprob : (1 / 16 : ℝ) ≤ μ.real A := by
    apply le_trans ?_ hpz'
    rw [le_div_iff₀ hE4pos]
    nlinarith [hS4]
  have hsqrtV : 0 ≤ Real.sqrt (V / 2) := Real.sqrt_nonneg _
  have hSint : Integrable S μ := by
    refine Integrable.of_bound hSm.aestronglyMeasurable ((n : ℝ) * L) ?_
    filter_upwards [] with ω
    simpa [Real.norm_eq_abs] using hSbound ω
  have hleftInt : Integrable (A.indicator fun _ => Real.sqrt (V / 2)) μ :=
    (integrable_const _).indicator hAmeas
  have hpoint : ∀ ω, A.indicator (fun _ => Real.sqrt (V / 2)) ω ≤ |S ω| := by
    intro ω
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω]
      have hs : V / 2 < S ω ^ 2 := hω
      have hs0 : 0 ≤ V / 2 := by positivity
      calc
        Real.sqrt (V / 2) ≤ Real.sqrt (S ω ^ 2) :=
          (Real.sqrt_lt_sqrt hs0 hs).le
        _ = |S ω| := Real.sqrt_sq_eq_abs _
    · rw [Set.indicator_of_notMem hω]
      exact abs_nonneg _
  have hintLower : Real.sqrt (V / 2) * μ.real A ≤ ∫ ω, |S ω| ∂μ := by
    have hi := integral_mono hleftInt hSint.abs hpoint
    have hcind : (∫ ω, A.indicator (fun _ => Real.sqrt (V / 2)) ω ∂μ) =
        Real.sqrt (V / 2) * μ.real A := by
      rw [integral_indicator hAmeas]
      simp [Measure.real, mul_comm]
    rwa [hcind] at hi
  have hsqrtLower : (1 / 2 : ℝ) * Real.sqrt ((n : ℝ) * a) ≤
      Real.sqrt (V / 2) := by
    have hsq : ((n : ℝ) * a) / 4 ≤ V / 2 := by nlinarith [hVlower]
    have h := Real.sqrt_le_sqrt hsq
    calc
      (1 / 2 : ℝ) * Real.sqrt ((n : ℝ) * a) =
          Real.sqrt (((n : ℝ) * a) / 4) := by
            rw [Real.sqrt_div hna.le 4]
            have h4 : Real.sqrt (4 : ℝ) = 2 := by
              nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 4),
                Real.sqrt_nonneg 4]
            rw [h4]
            ring
      _ ≤ Real.sqrt (V / 2) := h
  calc
    (1 / 32 : ℝ) * Real.sqrt ((n : ℝ) * a)
        ≤ Real.sqrt (V / 2) * μ.real A := by
          have hμ0 : 0 ≤ μ.real A := measureReal_nonneg
          nlinarith [hprob, hsqrtLower]
    _ ≤ ∫ ω, |S ω| ∂μ := hintLower

/-- The sixth-moment hypothesis in Exercise 3.3 gives the required third
absolute moment bound for the centered square.

**Book Exercise 3.3.** -/
private theorem centeredSquare_abs_cube_integrable_le
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hXm : Measurable X)
    (h6int : Integrable (fun ω => X ω ^ 6) μ)
    {β : ℝ} (h6 : ∫ ω, X ω ^ 6 ∂μ ≤ β) :
    Integrable (fun ω => |X ω ^ 2 - 1| ^ 3) μ ∧
      (∫ ω, |X ω ^ 2 - 1| ^ 3 ∂μ) ≤ 4 * (β + 1) := by
  have hpoint : ∀ ω, |X ω ^ 2 - 1| ^ 3 ≤ 4 * (X ω ^ 6 + 1) := by
    intro ω
    let t : ℝ := X ω ^ 2
    have ht : 0 ≤ t := sq_nonneg _
    have habs : |t - 1| ≤ t + 1 := by
      calc
        |t - 1| ≤ |t| + |(1 : ℝ)| := abs_sub _ _
        _ = t + 1 := by rw [abs_of_nonneg ht]; norm_num
    have hp := pow_le_pow_left₀ (abs_nonneg (t - 1)) habs 3
    have hpoly : (t + 1) ^ 3 ≤ 4 * (t ^ 3 + 1) := by
      have hfac : 0 ≤ (t - 1) ^ 2 * (t + 1) :=
        mul_nonneg (sq_nonneg _) (by linarith)
      nlinarith
    calc
      |X ω ^ 2 - 1| ^ 3 = |t - 1| ^ 3 := rfl
      _ ≤ (t + 1) ^ 3 := hp
      _ ≤ 4 * (t ^ 3 + 1) := hpoly
      _ = 4 * (X ω ^ 6 + 1) := by dsimp [t]; ring
  have hright : Integrable (fun ω => 4 * (X ω ^ 6 + 1)) μ :=
    (h6int.add (integrable_const 1)).const_mul 4
  have hleft : Integrable (fun ω => |X ω ^ 2 - 1| ^ 3) μ := by
    refine hright.mono' (((hXm.pow_const 2).sub_const 1).abs.pow_const 3
      |>.aestronglyMeasurable) ?_
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) 3)]
    exact hpoint ω
  refine ⟨hleft, ?_⟩
  calc
    (∫ ω, |X ω ^ 2 - 1| ^ 3 ∂μ) ≤
        ∫ ω, 4 * (X ω ^ 6 + 1) ∂μ :=
      integral_mono hleft hright hpoint
    _ = 4 * ((∫ ω, X ω ^ 6 ∂μ) + 1) := by
      rw [integral_const_mul, integral_add h6int (integrable_const 1), integral_const]
      simp
    _ ≤ 4 * (β + 1) := by linarith

/-- Truncate centered summands, recenter them, and retain quantitative control
of both their second moments and the `L¹` error of the whole sum.

**Lean implementation helper.** -/
private theorem exists_bounded_centering
    [IsProbabilityMeasure μ] {n : ℕ}
    {Y : Fin n → Ω → ℝ} (hYm : ∀ i, Measurable (Y i))
    (hindep : iIndepFun Y μ) (hmean : ∀ i, ∫ ω, Y i ω ∂μ = 0)
    {a B L : ℝ} (hL : 0 < L)
    (hsecond : ∀ i, a ≤ ∫ ω, Y i ω ^ 2 ∂μ)
    (hY3int : ∀ i, Integrable (fun ω => |Y i ω| ^ 3) μ)
    (hY3 : ∀ i, ∫ ω, |Y i ω| ^ 3 ∂μ ≤ B) :
    ∃ Z : Fin n → Ω → ℝ,
      (∀ i, Measurable (Z i)) ∧ iIndepFun Z μ ∧
      (∀ i, ∫ ω, Z i ω ∂μ = 0) ∧
      (∀ i ω, |Z i ω| ≤ 2 * L) ∧
      (∀ i, a - B / L - (B / L ^ 2) ^ 2 ≤
        ∫ ω, Z i ω ^ 2 ∂μ) ∧
      ((∫ ω, |∑ i, Z i ω| ∂μ) -
          2 * (n : ℝ) * B / L ^ 2 ≤
        ∫ ω, |∑ i, Y i ω| ∂μ) := by
  classical
  let A : Fin n → Ω → ℝ := fun i ω =>
    if |Y i ω| ≤ L then Y i ω else 0
  let m : Fin n → ℝ := fun i => ∫ ω, A i ω ∂μ
  let Z : Fin n → Ω → ℝ := fun i ω => A i ω - m i
  let T : Fin n → Ω → ℝ := fun i ω => Y i ω - A i ω
  have hAmeas : ∀ i, Measurable (A i) := by
    intro i
    dsimp [A]
    exact Measurable.ite (measurableSet_le (hYm i).abs measurable_const)
      (hYm i) measurable_const
  have hAbound : ∀ i ω, |A i ω| ≤ L := by
    intro i ω
    dsimp [A]
    split_ifs with h
    · exact h
    · simpa using hL.le
  have hAint : ∀ i, Integrable (A i) μ := by
    intro i
    refine Integrable.of_bound (hAmeas i).aestronglyMeasurable L ?_
    filter_upwards [] with ω
    simpa [Real.norm_eq_abs] using hAbound i ω
  have hA2mem : ∀ i, MemLp (A i) 2 μ := fun i =>
    (memLp_top_of_bound (hAmeas i).aestronglyMeasurable L
      (Filter.Eventually.of_forall fun ω => by
        simpa [Real.norm_eq_abs] using hAbound i ω)).mono_exponent (by simp)
  have hYint : ∀ i, Integrable (Y i) μ := by
    intro i
    have hright : Integrable (fun ω => |Y i ω| ^ 3 + 1) μ :=
      (hY3int i).add (integrable_const 1)
    refine hright.mono' (hYm i).aestronglyMeasurable ?_
    filter_upwards [] with ω
    rw [Real.norm_eq_abs]
    let u := |Y i ω|
    have hu : 0 ≤ u := abs_nonneg _
    by_cases hu1 : u ≤ 1
    · dsimp [u] at hu1 ⊢
      nlinarith [pow_nonneg (abs_nonneg (Y i ω)) 3]
    · have hu' : 1 ≤ u := le_of_not_ge hu1
      have hpow : u ≤ u ^ 3 := by nlinarith [mul_nonneg hu (sq_nonneg (u - 1))]
      dsimp [u] at hpow ⊢
      linarith
  have hY2int : ∀ i, Integrable (fun ω => Y i ω ^ 2) μ := by
    intro i
    have hright : Integrable (fun ω => |Y i ω| ^ 3 + 1) μ :=
      (hY3int i).add (integrable_const 1)
    refine hright.mono' ((hYm i).pow_const 2).aestronglyMeasurable ?_
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    let u := |Y i ω|
    have hu : 0 ≤ u := abs_nonneg _
    have hy2 : Y i ω ^ 2 = u ^ 2 := by dsimp [u]; rw [sq_abs]
    rw [hy2]
    by_cases hu1 : u ≤ 1
    · nlinarith [pow_nonneg hu 3]
    · have hu' : 1 ≤ u := le_of_not_ge hu1
      nlinarith [mul_nonneg (sq_nonneg u) (sub_nonneg.mpr hu')]
  have hTint : ∀ i, Integrable (T i) μ := fun i => (hYint i).sub (hAint i)
  have hTabsInt : ∀ i, Integrable (fun ω => |T i ω|) μ := fun i => (hTint i).abs
  have hTbound : ∀ i, (∫ ω, |T i ω| ∂μ) ≤ B / L ^ 2 := by
    intro i
    have hpoint : ∀ ω, |T i ω| ≤ |Y i ω| ^ 3 / L ^ 2 := by
      intro ω
      dsimp [T, A]
      split_ifs with h
      · simp [div_nonneg, hL.le]
      · have hgt : L < |Y i ω| := lt_of_not_ge h
        have hsq : L ^ 2 ≤ |Y i ω| ^ 2 :=
          pow_le_pow_left₀ hL.le hgt.le 2
        rw [sub_zero]
        have hu : 0 ≤ |Y i ω| := abs_nonneg _
        apply (le_div_iff₀ (sq_pos_of_pos hL)).2
        nlinarith [mul_nonneg hu (sub_nonneg.mpr hsq)]
    have hright : Integrable (fun ω => |Y i ω| ^ 3 / L ^ 2) μ :=
      (hY3int i).div_const _
    calc
      (∫ ω, |T i ω| ∂μ) ≤ ∫ ω, |Y i ω| ^ 3 / L ^ 2 ∂μ :=
        integral_mono (hTabsInt i) hright hpoint
      _ = (∫ ω, |Y i ω| ^ 3 ∂μ) / L ^ 2 := by rw [integral_div]
      _ ≤ B / L ^ 2 := div_le_div_of_nonneg_right (hY3 i) (sq_nonneg L)
  have hmEq : ∀ i, m i = -(∫ ω, T i ω ∂μ) := by
    intro i
    have h := integral_sub (hYint i) (hAint i)
    dsimp [T, m] at h ⊢
    rw [hmean i] at h
    linarith
  have hmBound : ∀ i, |m i| ≤ B / L ^ 2 := by
    intro i
    rw [hmEq i, abs_neg]
    exact (abs_integral_le_integral_abs (μ := μ) (f := T i)).trans (hTbound i)
  have hmL : ∀ i, |m i| ≤ L := by
    intro i
    have habsA := abs_integral_le_integral_abs (μ := μ) (f := A i)
    have hconst : (∫ ω, |A i ω| ∂μ) ≤ L := by
      calc
        (∫ ω, |A i ω| ∂μ) ≤ ∫ _ω, L ∂μ :=
          integral_mono (hAint i).abs (integrable_const L) (hAbound i)
        _ = L := by simp
    exact habsA.trans hconst
  have hZmeas : ∀ i, Measurable (Z i) := fun i => (hAmeas i).sub_const _
  have hZbound : ∀ i ω, |Z i ω| ≤ 2 * L := by
    intro i ω
    calc
      |Z i ω| ≤ |A i ω| + |m i| := by
        dsimp [Z]
        exact abs_sub _ _
      _ ≤ L + L := add_le_add (hAbound i ω) (hmL i)
      _ = 2 * L := by ring
  have hZmem : ∀ i, MemLp (Z i) 2 μ := fun i =>
    (memLp_top_of_bound (hZmeas i).aestronglyMeasurable (2 * L)
      (Filter.Eventually.of_forall fun ω => by
        simpa [Real.norm_eq_abs] using hZbound i ω)).mono_exponent (by simp)
  have hZmean : ∀ i, ∫ ω, Z i ω ∂μ = 0 := by
    intro i
    dsimp [Z, m]
    rw [integral_sub (hAint i) (integrable_const _), integral_const]
    simp
  have hZindep : iIndepFun Z μ := by
    simpa [Z, A, Function.comp_def] using
      hindep.comp
        (fun i x => (if |x| ≤ L then x else 0) - m i)
        (fun _ => by
          exact (Measurable.ite
            (measurableSet_le measurable_id.abs measurable_const)
            measurable_id measurable_const).sub_const _)
  have hQbound : ∀ i,
      (∫ ω, (Y i ω ^ 2 - A i ω ^ 2) ∂μ) ≤ B / L := by
    intro i
    have hQint : Integrable (fun ω => Y i ω ^ 2 - A i ω ^ 2) μ :=
      (hY2int i).sub (hA2mem i).integrable_sq
    have hpoint : ∀ ω, Y i ω ^ 2 - A i ω ^ 2 ≤ |Y i ω| ^ 3 / L := by
      intro ω
      dsimp [A]
      split_ifs with h
      · simp [div_nonneg, hL.le]
      · have hgt : L < |Y i ω| := lt_of_not_ge h
        apply (le_div_iff₀ hL).2
        have hu : 0 ≤ |Y i ω| := abs_nonneg _
        rw [← sq_abs]
        nlinarith [mul_le_mul_of_nonneg_right hgt.le (sq_nonneg |Y i ω|)]
    have hright : Integrable (fun ω => |Y i ω| ^ 3 / L) μ :=
      (hY3int i).div_const _
    calc
      (∫ ω, Y i ω ^ 2 - A i ω ^ 2 ∂μ) ≤
          ∫ ω, |Y i ω| ^ 3 / L ∂μ :=
        integral_mono hQint hright hpoint
      _ = (∫ ω, |Y i ω| ^ 3 ∂μ) / L := by rw [integral_div]
      _ ≤ B / L := div_le_div_of_nonneg_right (hY3 i) hL.le
  have hZsecond : ∀ i, a - B / L - (B / L ^ 2) ^ 2 ≤
      ∫ ω, Z i ω ^ 2 ∂μ := by
    intro i
    have hAsecond : a - B / L ≤ ∫ ω, A i ω ^ 2 ∂μ := by
      have hsplit : (∫ ω, Y i ω ^ 2 ∂μ) - (∫ ω, A i ω ^ 2 ∂μ) =
          ∫ ω, (Y i ω ^ 2 - A i ω ^ 2) ∂μ := by
        rw [integral_sub (hY2int i) (hA2mem i).integrable_sq]
      linarith [hsecond i, hQbound i]
    have hvarZ : (∫ ω, Z i ω ^ 2 ∂μ) =
        (∫ ω, A i ω ^ 2 ∂μ) - (m i) ^ 2 := by
      have hz := variance_eq_sub (hZmem i)
      rw [hZmean i] at hz
      norm_num at hz
      have hshift := variance_sub_const (μ := μ)
        (hAmeas i).aestronglyMeasurable (m i)
      have haVar := variance_eq_sub (hA2mem i)
      calc
        (∫ ω, Z i ω ^ 2 ∂μ) = Var[Z i; μ] := by
          simpa only [Pi.pow_apply] using hz.symm
        _ = Var[A i; μ] := by simpa [Z] using hshift
        _ = (∫ ω, A i ω ^ 2 ∂μ) - (m i) ^ 2 := by
          simpa only [Pi.pow_apply, m] using haVar
    have hmSq : (m i) ^ 2 ≤ (B / L ^ 2) ^ 2 := by
      have h := pow_le_pow_left₀ (abs_nonneg (m i)) (hmBound i) 2
      simpa [sq_abs] using h
    rw [hvarZ]
    linarith
  have hDint : ∀ i, Integrable (fun ω => Y i ω - Z i ω) μ := by
    intro i
    exact (hYint i).sub ((hZmem i).integrable (by norm_num))
  have hDbound : ∀ i, (∫ ω, |Y i ω - Z i ω| ∂μ) ≤ 2 * B / L ^ 2 := by
    intro i
    have hpoint : ∀ ω, |Y i ω - Z i ω| ≤ |T i ω| + |m i| := by
      intro ω
      dsimp [T, Z]
      rw [show Y i ω - (A i ω - m i) = (Y i ω - A i ω) + m i by ring]
      exact abs_add_le _ _
    calc
      (∫ ω, |Y i ω - Z i ω| ∂μ) ≤
          ∫ ω, (|T i ω| + |m i|) ∂μ :=
        integral_mono (hDint i).abs ((hTabsInt i).add (integrable_const _)) hpoint
      _ = (∫ ω, |T i ω| ∂μ) + |m i| := by
        rw [integral_add (hTabsInt i) (integrable_const _), integral_const]
        simp
      _ ≤ B / L ^ 2 + B / L ^ 2 := add_le_add (hTbound i) (hmBound i)
      _ = 2 * B / L ^ 2 := by ring
  have hsumYint : Integrable (fun ω => ∑ i, Y i ω) μ :=
    integrable_finsetSum Finset.univ fun i _ => hYint i
  have hsumZint : Integrable (fun ω => ∑ i, Z i ω) μ :=
    integrable_finsetSum Finset.univ fun i _ => (hZmem i).integrable (by norm_num)
  have hcompare : (∫ ω, |∑ i, Z i ω| ∂μ) ≤
      (∫ ω, |∑ i, Y i ω| ∂μ) + ∑ i, ∫ ω, |Y i ω - Z i ω| ∂μ := by
    have hpoint : ∀ ω, |∑ i, Z i ω| ≤
        |∑ i, Y i ω| + ∑ i, |Y i ω - Z i ω| := by
      intro ω
      have heq : (∑ i, Z i ω) = (∑ i, Y i ω) - ∑ i, (Y i ω - Z i ω) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      rw [heq]
      exact (abs_sub _ _).trans
        (add_le_add le_rfl
          (Finset.abs_sum_le_sum_abs
            (s := Finset.univ) (f := fun i => Y i ω - Z i ω)))
    calc
      (∫ ω, |∑ i, Z i ω| ∂μ) ≤
          ∫ ω, (|∑ i, Y i ω| + ∑ i, |Y i ω - Z i ω|) ∂μ :=
        integral_mono hsumZint.abs
          (hsumYint.abs.add (integrable_finsetSum Finset.univ fun i _ => (hDint i).abs))
          hpoint
      _ = (∫ ω, |∑ i, Y i ω| ∂μ) +
          ∑ i, ∫ ω, |Y i ω - Z i ω| ∂μ := by
        rw [integral_add hsumYint.abs]
        · rw [integral_finsetSum]
          exact fun i _ => (hDint i).abs
        · exact integrable_finsetSum Finset.univ fun i _ => (hDint i).abs
  have hDsum : (∑ i, ∫ ω, |Y i ω - Z i ω| ∂μ) ≤
      2 * (n : ℝ) * B / L ^ 2 := by
    calc
      (∑ i, ∫ ω, |Y i ω - Z i ω| ∂μ) ≤ ∑ _i : Fin n, 2 * B / L ^ 2 :=
        Finset.sum_le_sum fun i _ => hDbound i
      _ = 2 * (n : ℝ) * B / L ^ 2 := by simp; ring
  refine ⟨Z, hZmeas, hZindep, hZmean, hZbound, hZsecond, ?_⟩
  linarith

/-- Thin-shell variance consequence of Theorem 3.1.1. This is the proved
core implementation used by the non-load-bearing Exercise 3.1 leaf.

**Book Remark 3.1.2.** -/
theorem thinShellVariance_subGaussian [IsProbabilityMeasure μ] {n : ℕ} (hn : 0 < n)
    {X : Fin n → Ω → ℝ} (hXm : ∀ i, AEMeasurable (X i) μ)
    (hX : ∀ i, HDP.SubGaussian (X i) μ)
    (hsecond : ∀ i, ∫ ω, X i ω ^ 2 ∂μ = 1)
    (hindep : iIndepFun X μ) {K : ℝ} (hK : 0 < K)
    (hKb : ∀ i, HDP.psi2Norm (X i) μ ≤ K) :
    Var[euclideanRadius X; μ] ≤
      2 * (normConcentrationConstant * K ^ 2) ^ 2 := by
  let R : Ω → ℝ := euclideanRadius X
  let Z : Ω → ℝ := fun ω => R ω - Real.sqrt n
  have hRm : AEMeasurable R μ := euclideanRadius_aemeasurable hXm
  have hZm : AEMeasurable Z μ := hRm.sub aemeasurable_const
  obtain ⟨hZsub, hZpsi⟩ := concentration_norm hn hXm hX hsecond hindep hK hKb
  have hZmem : MemLp Z 2 μ := by
    simpa using hZsub.memLp hZm (p := (2 : ℝ)) (by norm_num)
  have hmoment := hZsub.moment_bound hZm (p := (2 : ℝ)) (by norm_num)
  have hlp0 : 0 ≤ HDP.Chapter1.lpNormRV Z 2 μ := by
    unfold HDP.Chapter1.lpNormRV
    positivity
  have hpsi0 : 0 ≤ HDP.psi2Norm Z μ := HDP.psi2Norm_nonneg Z μ
  have hsqrt2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hlp_sq : HDP.Chapter1.lpNormRV Z 2 μ ^ 2 ≤
      (HDP.psi2Norm Z μ * Real.sqrt 2) ^ 2 :=
    (sq_le_sq₀ hlp0 (mul_nonneg hpsi0 hsqrt2)).2 hmoment
  have hint_sq : (∫ ω, Z ω ^ 2 ∂μ) =
      HDP.Chapter1.lpNormRV Z 2 μ ^ 2 := by
    have h := HDP.Chapter1.sq_lpNormRV_two_eq_l2InnerRV hZmem
    simpa [HDP.Chapter1.l2InnerRV, pow_two] using h.symm
  have hvarZ : Var[Z; μ] ≤
      (HDP.psi2Norm Z μ * Real.sqrt 2) ^ 2 := by
    calc
      Var[Z; μ] ≤ ∫ ω, Z ω ^ 2 ∂μ :=
        variance_le_expectation_sq hZm.aestronglyMeasurable
      _ = HDP.Chapter1.lpNormRV Z 2 μ ^ 2 := hint_sq
      _ ≤ (HDP.psi2Norm Z μ * Real.sqrt 2) ^ 2 := hlp_sq
  have hpsi_sq : (HDP.psi2Norm Z μ * Real.sqrt 2) ^ 2 ≤
      2 * (normConcentrationConstant * K ^ 2) ^ 2 := by
    have hC0 : 0 ≤ normConcentrationConstant * K ^ 2 :=
      mul_nonneg normConcentrationConstant_pos.le (sq_nonneg K)
    have hs := (sq_le_sq₀ hpsi0 hC0).2 hZpsi
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    Var[R; μ] = Var[Z; μ] :=
      (variance_sub_const hRm.aestronglyMeasurable (Real.sqrt n)).symm
    _ ≤ (HDP.psi2Norm Z μ * Real.sqrt 2) ^ 2 := hvarZ
    _ ≤ 2 * (normConcentrationConstant * K ^ 2) ^ 2 := hpsi_sq

/-- Fourth
moments alone give the sharp dimension-free variance bound and the two source
mean bounds. This is the unique authoritative source-numbered declaration.

**Book Remark 3.1.2.** -/
theorem exercise_3_2 [IsProbabilityMeasure μ] {n : ℕ} (hn : 0 < n)
    {X : Fin n → Ω → ℝ} (hXm : ∀ i, AEMeasurable (X i) μ)
    (hindep : iIndepFun X μ)
    (hsecond : ∀ i, ∫ ω, X i ω ^ 2 ∂μ = 1)
    {K : ℝ} (_hK : 0 ≤ K)
    (hfourthInt : ∀ i, Integrable (fun ω => X i ω ^ 4) μ)
    (hfourth : ∀ i, ∫ ω, X i ω ^ 4 ∂μ ≤ K ^ 4) :
    Var[euclideanRadius X; μ] ≤ K ^ 4 ∧
      Real.sqrt n - K ^ 4 / Real.sqrt n ≤
        ∫ ω, euclideanRadius X ω ∂μ ∧
      (∫ ω, euclideanRadius X ω ∂μ) ≤ Real.sqrt n := by
  let R : Ω → ℝ := euclideanRadius X
  let sn : ℝ := Real.sqrt n
  let Y : Fin n → Ω → ℝ := fun i ω => X i ω ^ 2 - 1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsn : 0 < sn := by simpa [sn] using Real.sqrt_pos.mpr hnR
  have hsnsq : sn ^ 2 = (n : ℝ) := by
    simp [sn, Real.sq_sqrt hnR.le]
  have hRm : AEMeasurable R μ := euclideanRadius_aemeasurable hXm
  have hR0 : ∀ ω, 0 ≤ R ω := fun ω => Real.sqrt_nonneg _
  have hsum0 : ∀ ω, 0 ≤ ∑ i : Fin n, X i ω ^ 2 := fun ω =>
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hRsq : ∀ ω, R ω ^ 2 = ∑ i : Fin n, X i ω ^ 2 := fun ω => by
    exact Real.sq_sqrt (hsum0 ω)
  have hXsqMem : ∀ i, MemLp (fun ω => X i ω ^ 2) 2 μ := by
    intro i
    apply (memLp_two_iff_integrable_sq ((hXm i).pow_const 2).aestronglyMeasurable).2
    convert hfourthInt i using 1
    ext ω
    ring
  have hYmem : ∀ i, MemLp (Y i) 2 μ := fun i => by
    exact (hXsqMem i).sub (memLp_const 1)
  have hYmean : ∀ i, ∫ ω, Y i ω ∂μ = 0 := by
    intro i
    rw [show Y i = fun ω => X i ω ^ 2 - 1 by rfl,
      integral_sub ((hXsqMem i).integrable (by norm_num)) (integrable_const 1),
      hsecond i, integral_const]
    simp
  have hYindep : iIndepFun Y μ := by
    simpa [Y, Function.comp_def] using
      hindep.comp (fun (_ : Fin n) (x : ℝ) => x ^ 2 - 1)
        (fun _ => (measurable_id.pow_const 2).sub_const 1)
  have hYpair : Set.Pairwise (Set.univ : Set (Fin n))
      (fun i j => IndepFun (Y i) (Y j) μ) := by
    intro i hi j hj hij
    exact hYindep.indepFun hij
  have hYiSq : ∀ i, (∫ ω, Y i ω ^ 2 ∂μ) ≤ K ^ 4 := by
    intro i
    have hvarY : Var[Y i; μ] = ∫ ω, Y i ω ^ 2 ∂μ := by
      have h := variance_eq_sub (hYmem i)
      rw [hYmean i] at h
      simpa using h
    have hshift : Var[Y i; μ] = Var[fun ω => X i ω ^ 2; μ] := by
      exact variance_sub_const ((hXm i).pow_const 2).aestronglyMeasurable 1
    have hvle := variance_le_expectation_sq ((hXm i).pow_const 2).aestronglyMeasurable
    calc
      (∫ ω, Y i ω ^ 2 ∂μ) = Var[Y i; μ] := hvarY.symm
      _ = Var[fun ω => X i ω ^ 2; μ] := hshift
      _ ≤ ∫ ω, (X i ω ^ 2) ^ 2 ∂μ := hvle
      _ = ∫ ω, X i ω ^ 4 ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with ω
        ring
      _ ≤ K ^ 4 := hfourth i
  have hpyth := HDP.pythagorean_identity hYmem hYmean hYpair
  have hsumY : (∫ ω, (∑ i, Y i ω) ^ 2 ∂μ) ≤ (n : ℝ) * K ^ 4 := by
    rw [hpyth]
    calc
      (∑ i : Fin n, ∫ ω, Y i ω ^ 2 ∂μ) ≤ ∑ _i : Fin n, K ^ 4 :=
        Finset.sum_le_sum fun i _ => hYiSq i
      _ = (n : ℝ) * K ^ 4 := by simp
  have hsumYeq : ∀ ω, (∑ i, Y i ω) = R ω ^ 2 - sn ^ 2 := by
    intro ω
    rw [hRsq, hsnsq]
    simp [Y, Finset.sum_sub_distrib]
  have hpoint : ∀ ω, (R ω - sn) ^ 2 ≤ (∑ i, Y i ω) ^ 2 / (n : ℝ) := by
    intro ω
    have hden : (n : ℝ) ≤ (R ω + sn) ^ 2 := by
      rw [← hsnsq]
      exact (sq_le_sq₀ hsn.le (add_nonneg (hR0 ω) hsn.le)).2 (by
        linarith [hR0 ω])
    have hmul : (n : ℝ) * (R ω - sn) ^ 2 ≤
        ((R ω - sn) * (R ω + sn)) ^ 2 := by
      calc
        (n : ℝ) * (R ω - sn) ^ 2
            ≤ (R ω + sn) ^ 2 * (R ω - sn) ^ 2 :=
          mul_le_mul_of_nonneg_right hden (sq_nonneg _)
        _ = ((R ω - sn) * (R ω + sn)) ^ 2 := by ring
    rw [hsumYeq]
    have hfactor : R ω ^ 2 - sn ^ 2 = (R ω - sn) * (R ω + sn) := by ring
    rw [hfactor]
    exact (le_div_iff₀ hnR).2 (by simpa [mul_comm] using hmul)
  have hsumMem : MemLp (fun ω => ∑ i, Y i ω) 2 μ := by
    have hfun : (fun ω => ∑ i, Y i ω) = ∑ i, Y i := by
      funext ω
      rw [Finset.sum_apply]
    rw [hfun]
    exact memLp_finsetSum' Finset.univ fun i _ => hYmem i
  have hrightInt : Integrable (fun ω => (∑ i, Y i ω) ^ 2 / (n : ℝ)) μ :=
    hsumMem.integrable_sq.div_const _
  have hleftInt : Integrable (fun ω => (R ω - sn) ^ 2) μ := by
    refine hrightInt.mono'
      ((hRm.sub aemeasurable_const).pow_const 2).aestronglyMeasurable ?_
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpoint ω
  have hdev : (∫ ω, (R ω - sn) ^ 2 ∂μ) ≤ K ^ 4 := by
    calc
      (∫ ω, (R ω - sn) ^ 2 ∂μ)
          ≤ ∫ ω, (∑ i, Y i ω) ^ 2 / (n : ℝ) ∂μ :=
        integral_mono hleftInt hrightInt hpoint
      _ = (∫ ω, (∑ i, Y i ω) ^ 2 ∂μ) / (n : ℝ) := by rw [integral_div]
      _ ≤ ((n : ℝ) * K ^ 4) / (n : ℝ) :=
        div_le_div_of_nonneg_right hsumY hnR.le
      _ = K ^ 4 := by field_simp
  have hR2int : Integrable (fun ω => R ω ^ 2) μ := by
    have hsumInt : Integrable (fun ω => ∑ i, X i ω ^ 2) μ := by
      exact integrable_finsetSum Finset.univ fun i _ =>
        (hXsqMem i).integrable (by norm_num)
    apply Integrable.congr hsumInt
    filter_upwards [] with ω
    exact (hRsq ω).symm
  have hRmem : MemLp R 2 μ :=
    (memLp_two_iff_integrable_sq hRm.aestronglyMeasurable).2 hR2int
  have hRsecond : (∫ ω, R ω ^ 2 ∂μ) = n := by
    calc
      (∫ ω, R ω ^ 2 ∂μ) = ∫ ω, ∑ i, X i ω ^ 2 ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall hRsq)
      _ = ∑ i, ∫ ω, X i ω ^ 2 ∂μ := by
        rw [integral_finsetSum]
        exact fun i _ => (hXsqMem i).integrable (by norm_num)
      _ = n := by simp [hsecond]
  have hvar : Var[R; μ] ≤ K ^ 4 :=
    (HDP.variance_le_integral_sq_sub hRmem sn).trans hdev
  let m : ℝ := ∫ ω, R ω ∂μ
  have hm0 : 0 ≤ m := integral_nonneg hR0
  have hvarEq : Var[R; μ] = (n : ℝ) - m ^ 2 := by
    have h := variance_eq_sub hRmem
    simpa only [Pi.pow_apply, hRsecond, m] using h
  have hmSq : m ^ 2 ≤ (n : ℝ) := by
    have := variance_nonneg R μ
    rw [hvarEq] at this
    linarith
  have hmle : m ≤ sn := by
    exact (sq_le_sq₀ hm0 hsn.le).mp (by simpa [hsnsq] using hmSq)
  have hlowerMul : sn * (sn - m) ≤ K ^ 4 := by
    have hmain : (n : ℝ) - m ^ 2 ≤ K ^ 4 := by
      rw [← hvarEq]
      exact hvar
    rw [← hsnsq] at hmain
    nlinarith [mul_nonneg hm0 (sub_nonneg.mpr hmle)]
  have hlower : sn - K ^ 4 / sn ≤ m := by
    have hdiv : sn - m ≤ K ^ 4 / sn :=
      (le_div_iff₀ hsn).2 (by simpa [mul_comm] using hlowerMul)
    linarith
  exact ⟨hvar, hlower, hmle⟩

/-- An explicit numerical reading of “`n` is large enough depending on
`α, β`” in Exercise 3.3. The witness is the truncation level used in the
proof; all four requirements involve only `n`, `α`, and `β`.

**Book Exercise 3.3.** -/
def ReverseThinShellLargeEnough (n : ℕ) (α β : ℝ) : Prop :=
  let B := 4 * (β + 1)
  ∃ L : ℝ, 0 < L ∧
    B / L + (B / L ^ 2) ^ 2 ≤ α / 2 ∧
    (2 * L) ^ 2 ≤ (n : ℝ) * (α / 2) ∧
    2 * (n : ℝ) * B / L ^ 2 ≤
      (1 / 128 : ℝ) * Real.sqrt ((n : ℝ) * α)

/-- Reverse thin-shell estimate proved for the source Exercise 3.3.

The source's “large enough” clause is exposed by
`ReverseThinShellLargeEnough`. The absolute constant is explicit and is
independent of `α`, `β`, and the coordinate laws.

**Book Exercise 3.3.** -/
theorem reverseThinShellVariance [IsProbabilityMeasure μ] {n : ℕ} (hn : 0 < n)
    {X : Fin n → Ω → ℝ} (hXm : ∀ i, Measurable (X i))
    (hindep : iIndepFun X μ)
    (hsecond : ∀ i, ∫ ω, X i ω ^ 2 ∂μ = 1)
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hvar : ∀ i, α < Var[fun ω => X i ω ^ 2; μ])
    (h6int : ∀ i, Integrable (fun ω => X i ω ^ 6) μ)
    (h6 : ∀ i, ∫ ω, X i ω ^ 6 ∂μ ≤ β)
    (hlarge : ReverseThinShellLargeEnough n α β) :
    (1 / 262144 : ℝ) * α ≤ Var[euclideanRadius X; μ] ∧
      (∫ ω, euclideanRadius X ω ∂μ) ≤
        Real.sqrt n - (1 / 262144 : ℝ) * α / Real.sqrt n := by
  classical
  let B : ℝ := 4 * (β + 1)
  let Y : Fin n → Ω → ℝ := fun i ω => X i ω ^ 2 - 1
  obtain ⟨L, hL, htrunc, hscale, herr⟩ := hlarge
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hna : 0 < (n : ℝ) * α := mul_pos hnR hα
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hYm : ∀ i, Measurable (Y i) := fun i =>
    ((hXm i).pow_const 2).sub_const 1
  have hX2int : ∀ i, Integrable (fun ω => X i ω ^ 2) μ := by
    intro i
    have hright : Integrable (fun ω => X i ω ^ 6 + 1) μ :=
      (h6int i).add (integrable_const 1)
    refine hright.mono' ((hXm i).pow_const 2).aestronglyMeasurable ?_
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    let u : ℝ := X i ω ^ 2
    have hu : 0 ≤ u := sq_nonneg _
    have hx6 : X i ω ^ 6 = u ^ 3 := by dsimp [u]; ring
    rw [hx6]
    by_cases hu1 : u ≤ 1
    · nlinarith [pow_nonneg hu 3]
    · have hu' : 1 ≤ u := le_of_not_ge hu1
      nlinarith [mul_nonneg hu (sq_nonneg (u - 1))]
  have hYmean : ∀ i, ∫ ω, Y i ω ∂μ = 0 := by
    intro i
    dsimp [Y]
    rw [integral_sub (hX2int i) (integrable_const 1), hsecond i, integral_const]
    simp
  have hYindep : iIndepFun Y μ := by
    simpa [Y, Function.comp_def] using
      hindep.comp (fun (_ : Fin n) (x : ℝ) => x ^ 2 - 1)
        (fun _ => (measurable_id.pow_const 2).sub_const 1)
  have hY3int : ∀ i, Integrable (fun ω => |Y i ω| ^ 3) μ := by
    intro i
    simpa [Y] using (centeredSquare_abs_cube_integrable_le
      (hXm i) (h6int i) (h6 i)).1
  have hY3 : ∀ i, (∫ ω, |Y i ω| ^ 3 ∂μ) ≤ B := by
    intro i
    simpa [Y, B] using (centeredSquare_abs_cube_integrable_le
      (hXm i) (h6int i) (h6 i)).2
  have hY2int : ∀ i, Integrable (fun ω => Y i ω ^ 2) μ := by
    intro i
    have hright : Integrable (fun ω => |Y i ω| ^ 3 + 1) μ :=
      (hY3int i).add (integrable_const 1)
    refine hright.mono' ((hYm i).pow_const 2).aestronglyMeasurable ?_
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    let u := |Y i ω|
    have hu : 0 ≤ u := abs_nonneg _
    have hy2 : Y i ω ^ 2 = u ^ 2 := by dsimp [u]; rw [sq_abs]
    rw [hy2]
    by_cases hu1 : u ≤ 1
    · nlinarith [pow_nonneg hu 3]
    · have hu' : 1 ≤ u := le_of_not_ge hu1
      nlinarith [mul_nonneg (sq_nonneg u) (sub_nonneg.mpr hu')]
  have hYmem : ∀ i, MemLp (Y i) 2 μ := fun i =>
    (memLp_two_iff_integrable_sq (hYm i).aestronglyMeasurable).2 (hY2int i)
  have hYsecond : ∀ i, α ≤ ∫ ω, Y i ω ^ 2 ∂μ := by
    intro i
    have hyVar := variance_eq_sub (hYmem i)
    rw [hYmean i] at hyVar
    have hshift := variance_sub_const (μ := μ)
      ((hXm i).pow_const 2).aestronglyMeasurable 1
    have heq : (∫ ω, Y i ω ^ 2 ∂μ) = Var[fun ω => X i ω ^ 2; μ] := by
      have : Var[Y i; μ] = Var[fun ω => X i ω ^ 2; μ] := by
        simpa [Y] using hshift
      norm_num at hyVar
      linarith
    rw [heq]
    exact (hvar i).le
  obtain ⟨Z, hZm, hZindep, hZmean, hZbound, hZsecond, hcompare⟩ :=
    exists_bounded_centering hYm hYindep hYmean hL hYsecond hY3int hY3
  have hZsecond' : ∀ i, α / 2 ≤ ∫ ω, Z i ω ^ 2 ∂μ := by
    intro i
    have htruncB : B / L + (B / L ^ 2) ^ 2 ≤ α / 2 := by
      simpa [B] using htrunc
    have : α / 2 ≤ α - B / L - (B / L ^ 2) ^ 2 := by
      linarith
    exact this.trans (hZsecond i)
  have hZlower := integral_abs_sum_ge_of_bounded hn hZm hZindep hZmean
    (a := α / 2) (L := 2 * L) (by linarith) (by positivity)
    hZbound hZsecond' hscale
  have hsqrtHalf : (1 / 64 : ℝ) * Real.sqrt ((n : ℝ) * α) ≤
      (1 / 32 : ℝ) * Real.sqrt ((n : ℝ) * (α / 2)) := by
    have hs : (1 / 2 : ℝ) * Real.sqrt ((n : ℝ) * α) ≤
        Real.sqrt ((n : ℝ) * (α / 2)) := by
      have hsq : ((n : ℝ) * α) / 4 ≤ (n : ℝ) * (α / 2) := by
        nlinarith [hna]
      have hsqrt := Real.sqrt_le_sqrt hsq
      calc
        (1 / 2 : ℝ) * Real.sqrt ((n : ℝ) * α) =
            Real.sqrt (((n : ℝ) * α) / 4) := by
          rw [Real.sqrt_div hna.le 4]
          have h4 : Real.sqrt (4 : ℝ) = 2 := by
            nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 4),
              Real.sqrt_nonneg 4]
          rw [h4]
          ring
        _ ≤ Real.sqrt ((n : ℝ) * (α / 2)) := hsqrt
    nlinarith
  have hYabsLower : (1 / 128 : ℝ) * Real.sqrt ((n : ℝ) * α) ≤
      ∫ ω, |∑ i, Y i ω| ∂μ := by
    have hZ64 := hsqrtHalf.trans hZlower
    linarith
  let R : Ω → ℝ := euclideanRadius X
  let sn : ℝ := Real.sqrt n
  let D : Ω → ℝ := fun ω => R ω - sn
  let G : Ω → ℝ := fun ω => R ω + sn
  have hsn : 0 < sn := by simpa [sn] using Real.sqrt_pos.mpr hnR
  have hsnsq : sn ^ 2 = (n : ℝ) := by
    simp [sn, Real.sq_sqrt hnR.le]
  have hRm : Measurable R := by
    dsimp [R, euclideanRadius]
    exact (Finset.measurable_sum Finset.univ fun i _ => (hXm i).pow_const 2).sqrt
  have hR0 : ∀ ω, 0 ≤ R ω := fun ω => Real.sqrt_nonneg _
  have hsum0 : ∀ ω, 0 ≤ ∑ i : Fin n, X i ω ^ 2 := fun ω =>
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hRsq : ∀ ω, R ω ^ 2 = ∑ i : Fin n, X i ω ^ 2 := fun ω => by
    exact Real.sq_sqrt (hsum0 ω)
  have hsumYeq : ∀ ω, (∑ i, Y i ω) = D ω * G ω := by
    intro ω
    calc
      (∑ i, Y i ω) = (∑ i, X i ω ^ 2) - (n : ℝ) := by
        simp [Y, Finset.sum_sub_distrib]
      _ = R ω ^ 2 - sn ^ 2 := by rw [hRsq, hsnsq]
      _ = D ω * G ω := by dsimp [D, G]; ring
  have hR2int : Integrable (fun ω => R ω ^ 2) μ := by
    have hsumInt : Integrable (fun ω => ∑ i, X i ω ^ 2) μ :=
      integrable_finsetSum Finset.univ fun i _ => hX2int i
    exact hsumInt.congr (Filter.Eventually.of_forall fun ω => (hRsq ω).symm)
  have hRmem : MemLp R 2 μ :=
    (memLp_two_iff_integrable_sq hRm.aestronglyMeasurable).2 hR2int
  have hRsecond : (∫ ω, R ω ^ 2 ∂μ) = n := by
    calc
      (∫ ω, R ω ^ 2 ∂μ) = ∫ ω, ∑ i, X i ω ^ 2 ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall hRsq)
      _ = ∑ i, ∫ ω, X i ω ^ 2 ∂μ := by
        rw [integral_finsetSum]
        exact fun i _ => hX2int i
      _ = n := by simp [hsecond]
  have hDmem : MemLp D 2 μ := hRmem.sub (memLp_const sn)
  have hGmem : MemLp G 2 μ := hRmem.add (memLp_const sn)
  have hDlp0 : 0 ≤ HDP.Chapter1.lpNormRV D 2 μ := by
    unfold HDP.Chapter1.lpNormRV
    positivity
  have hGlp0 : 0 ≤ HDP.Chapter1.lpNormRV G 2 μ := by
    unfold HDP.Chapter1.lpNormRV
    positivity
  have hDsq : HDP.Chapter1.lpNormRV D 2 μ ^ 2 =
      ∫ ω, D ω ^ 2 ∂μ := by
    have h := HDP.Chapter1.sq_lpNormRV_two_eq_l2InnerRV hDmem
    simpa [HDP.Chapter1.l2InnerRV, pow_two] using h
  have hGsq : HDP.Chapter1.lpNormRV G 2 μ ^ 2 =
      ∫ ω, G ω ^ 2 ∂μ := by
    have h := HDP.Chapter1.sq_lpNormRV_two_eq_l2InnerRV hGmem
    simpa [HDP.Chapter1.l2InnerRV, pow_two] using h
  have hGint : (∫ ω, G ω ^ 2 ∂μ) ≤ 4 * (n : ℝ) := by
    have hpoint : ∀ ω, G ω ^ 2 ≤ 2 * R ω ^ 2 + 2 * sn ^ 2 := by
      intro ω
      dsimp [G]
      nlinarith [sq_nonneg (R ω - sn)]
    have hright : Integrable (fun ω => 2 * R ω ^ 2 + 2 * sn ^ 2) μ :=
      hR2int.const_mul 2 |>.add (integrable_const _)
    calc
      (∫ ω, G ω ^ 2 ∂μ) ≤ ∫ ω, (2 * R ω ^ 2 + 2 * sn ^ 2) ∂μ :=
        integral_mono hGmem.integrable_sq hright hpoint
      _ = 4 * (n : ℝ) := by
        rw [integral_add, integral_const_mul, hRsecond, integral_const, hsnsq]
        · simp
          ring
        · exact hR2int.const_mul 2
        · exact integrable_const _
  have hGlp : HDP.Chapter1.lpNormRV G 2 μ ≤ 2 * sn := by
    have hsquare : HDP.Chapter1.lpNormRV G 2 μ ^ 2 ≤ (2 * sn) ^ 2 := by
      rw [hGsq]
      nlinarith [hGint, hsnsq]
    exact (sq_le_sq₀ hGlp0 (mul_nonneg (by norm_num) hsn.le)).mp hsquare
  have hCS := HDP.Chapter1.cauchy_schwarz_rv hDmem hGmem
  have hproduct : (1 / 128 : ℝ) * Real.sqrt ((n : ℝ) * α) ≤
      HDP.Chapter1.lpNormRV D 2 μ * (2 * sn) := by
    calc
      (1 / 128 : ℝ) * Real.sqrt ((n : ℝ) * α)
          ≤ ∫ ω, |∑ i, Y i ω| ∂μ := hYabsLower
      _ = ∫ ω, |D ω * G ω| ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with ω
        rw [hsumYeq]
      _ ≤ HDP.Chapter1.lpNormRV D 2 μ * HDP.Chapter1.lpNormRV G 2 μ := hCS
      _ ≤ HDP.Chapter1.lpNormRV D 2 μ * (2 * sn) :=
        mul_le_mul_of_nonneg_left hGlp hDlp0
  have hdev : α / 65536 ≤ ∫ ω, D ω ^ 2 ∂μ := by
    have hl0 : 0 ≤ (1 / 128 : ℝ) * Real.sqrt ((n : ℝ) * α) := by positivity
    have hr0 : 0 ≤ HDP.Chapter1.lpNormRV D 2 μ * (2 * sn) :=
      mul_nonneg hDlp0 (mul_nonneg (by norm_num) hsn.le)
    have hsquare := (sq_le_sq₀ hl0 hr0).2 hproduct
    simp only [mul_pow] at hsquare
    rw [Real.sq_sqrt hna.le, hDsq] at hsquare
    have hsquare' : (n : ℝ) * (α / 16384) ≤
        (n : ℝ) * (4 * ∫ ω, D ω ^ 2 ∂μ) := by
      calc
        (n : ℝ) * (α / 16384) =
            (1 / 128 : ℝ) ^ 2 * ((n : ℝ) * α) := by ring
        _ ≤ (∫ ω, D ω ^ 2 ∂μ) * (2 ^ 2 * sn ^ 2) := hsquare
        _ = (n : ℝ) * (4 * ∫ ω, D ω ^ 2 ∂μ) := by
          rw [hsnsq]
          ring
    have hcancel := le_of_mul_le_mul_left hsquare' hnR
    linarith
  let m : ℝ := ∫ ω, R ω ∂μ
  have hm0 : 0 ≤ m := integral_nonneg hR0
  have hvarEq : Var[R; μ] = (n : ℝ) - m ^ 2 := by
    have h := variance_eq_sub hRmem
    simpa only [Pi.pow_apply, hRsecond, m] using h
  have hmle : m ≤ sn := by
    have hv0 := variance_nonneg R μ
    rw [hvarEq] at hv0
    apply (sq_le_sq₀ hm0 hsn.le).mp
    rw [hsnsq]
    linarith
  have hdevEq : (∫ ω, D ω ^ 2 ∂μ) = 2 * sn * (sn - m) := by
    have hRint : Integrable R μ := hRmem.integrable (by norm_num)
    have hlinInt : Integrable (fun ω => 2 * sn * R ω) μ :=
      hRint.const_mul (2 * sn)
    have hconstInt : Integrable (fun _ : Ω => sn ^ 2) μ := integrable_const _
    calc
      (∫ ω, D ω ^ 2 ∂μ) =
          ∫ ω, (R ω ^ 2 - 2 * sn * R ω + sn ^ 2) ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with ω
        dsimp [D]
        ring
      _ = (∫ ω, R ω ^ 2 ∂μ) - (∫ ω, 2 * sn * R ω ∂μ) +
          ∫ _ : Ω, sn ^ 2 ∂μ := by
        have hadd := integral_add (hR2int.sub hlinInt) hconstInt
        have hsub := integral_sub hR2int hlinInt
        simpa only [Pi.add_apply, Pi.sub_apply, hsub] using hadd
      _ = (n : ℝ) - 2 * sn * m + sn ^ 2 := by
        rw [hRsecond, integral_const_mul, integral_const]
        simp [m]
      _ = 2 * sn * (sn - m) := by rw [← hsnsq]; ring
  have hdevVar : (∫ ω, D ω ^ 2 ∂μ) ≤ 2 * Var[R; μ] := by
    rw [hdevEq, hvarEq, ← hsnsq]
    calc
      2 * sn * (sn - m) = (sn - m) * (2 * sn) := by ring
      _ ≤ (sn - m) * (2 * (sn + m)) :=
        mul_le_mul_of_nonneg_left (by linarith) (sub_nonneg.mpr hmle)
      _ = 2 * (sn ^ 2 - m ^ 2) := by ring
  have hvarStrong : (1 / 131072 : ℝ) * α ≤ Var[R; μ] := by
    linarith [hdev, hdevVar]
  have hvarLower : (1 / 262144 : ℝ) * α ≤ Var[R; μ] := by
    linarith [hvarStrong, hα]
  have hmeanLower : (1 / 262144 : ℝ) * α / sn ≤ sn - m := by
    have hfactor : Var[R; μ] = (sn - m) * (sn + m) := by
      rw [hvarEq, ← hsnsq]
      ring
    have hsumle : sn + m ≤ 2 * sn := by linarith only [hmle]
    have hmul : (1 / 131072 : ℝ) * α ≤ 2 * sn * (sn - m) := by
      calc
        (1 / 131072 : ℝ) * α ≤ Var[R; μ] := hvarStrong
        _ = (sn - m) * (sn + m) := hfactor
        _ ≤ (sn - m) * (2 * sn) :=
          mul_le_mul_of_nonneg_left hsumle (sub_nonneg.mpr hmle)
        _ = 2 * sn * (sn - m) := by ring
    apply (div_le_iff₀ hsn).2
    calc
      (1 / 262144 : ℝ) * α =
          (1 / 2 : ℝ) * ((1 / 131072 : ℝ) * α) := by ring
      _ ≤ (1 / 2 : ℝ) * (2 * sn * (sn - m)) :=
        mul_le_mul_of_nonneg_left hmul (by norm_num)
      _ = (sn - m) * sn := by ring
  refine ⟨?_, ?_⟩
  · change (1 / 262144 : ℝ) * α ≤ Var[R; μ]
    exact hvarLower
  · change m ≤ sn - (1 / 262144 : ℝ) * α / sn
    linarith only [hmeanLower]

end HDP.Chapter3

end Source_02_ThinShell

/-! ## Material formerly in `03_Covariance.lean` -/

section Source_03_Covariance

/-!
# Book Chapter 3, Section 3.2: second moments and covariance
-/

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators ENNReal NNReal

namespace HDP.Chapter3

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Covariance-matrix entries are scalar covariances.

**Book Equation (3.5).** -/
theorem covarianceMatrix_apply {n : ℕ}
    (X : Ω → EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    HDP.covarianceMatrix X μ i j =
      cov[fun ω => X ω i, fun ω => X ω j; μ] := rfl

/-- The covariance matrix is symmetric.

**Book Section 3.2.** -/
theorem covarianceMatrix_transpose {n : ℕ}
    (X : Ω → EuclideanSpace ℝ (Fin n)) :
    (HDP.covarianceMatrix X μ).transpose = HDP.covarianceMatrix X μ := by
  ext i j
  simp [HDP.covarianceMatrix, HDP.Chapter1.covMatrix,
    mul_comm]

/-- The centered covariance is the uncentered second moment minus the outer
product of the mean:
`Cov(X) = E[XXᵀ] - (EX)(EX)ᵀ`.

**Book Section 3.2, covariance prose following equation (3.5).** -/
theorem covarianceMatrix_eq_secondMoment_sub_mean {n : ℕ}
    [IsProbabilityMeasure μ] {X : Ω → EuclideanSpace ℝ (Fin n)}
    (hX : MemLp X 2 μ) :
    HDP.covarianceMatrix X μ = HDP.secondMomentMatrix X μ -
      Matrix.vecMulVec (∫ ω, X ω ∂μ).ofLp (∫ ω, X ω ∂μ).ofLp := by
  ext i j
  have hi : MemLp (fun ω ↦ X ω i) 2 μ := by
    simpa only [Function.comp_apply, EuclideanSpace.coe_proj] using
      hX.continuousLinearMap_comp (EuclideanSpace.proj (𝕜 := ℝ) i)
  have hj : MemLp (fun ω ↦ X ω j) 2 μ := by
    simpa only [Function.comp_apply, EuclideanSpace.coe_proj] using
      hX.continuousLinearMap_comp (EuclideanSpace.proj (𝕜 := ℝ) j)
  have hmi := (EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_comm
    (hX.integrable one_le_two)
  have hmj := (EuclideanSpace.proj (𝕜 := ℝ) j).integral_comp_comm
    (hX.integrable one_le_two)
  have hmi' : (∫ ω, X ω i ∂μ) = (∫ ω, X ω ∂μ).ofLp i := by simpa using hmi
  have hmj' : (∫ ω, X ω j ∂μ) = (∫ ω, X ω ∂μ).ofLp j := by simpa using hmj
  rw [covarianceMatrix_apply, covariance_eq_sub hi hj]
  simp only [HDP.secondMomentMatrix_apply, Matrix.sub_apply,
    Matrix.vecMulVec_apply]
  rw [← hmi', ← hmj']
  rfl

/-- For a mean-zero random vector, covariance and the uncentered second moment
coincide.

**Book Section 3.2, covariance prose.** -/
theorem covarianceMatrix_eq_secondMoment_of_mean_zero {n : ℕ}
    [IsProbabilityMeasure μ] {X : Ω → EuclideanSpace ℝ (Fin n)}
    (hX : MemLp X 2 μ) (hmean : ∫ ω, X ω ∂μ = 0) :
    HDP.covarianceMatrix X μ = HDP.secondMomentMatrix X μ := by
  rw [covarianceMatrix_eq_secondMoment_sub_mean hX, hmean]
  simp

/-- A one-dimensional second moment is the
quadratic form of the second-moment matrix.

**Book Proposition 3.2.1(a).** -/
theorem secondMoment_inner_sq {n : ℕ}
    (X : Ω → EuclideanSpace ℝ (Fin n)) (v : EuclideanSpace ℝ (Fin n))
    (hX : ∀ i j, Integrable (fun ω => X ω i * X ω j) μ) :
    (∫ ω, inner ℝ (X ω) v ^ 2 ∂μ) =
      ∑ i : Fin n, ∑ j : Fin n,
        v i * HDP.secondMomentMatrix X μ i j * v j := by
  have hexpand : ∀ ω,
      inner ℝ (X ω) v ^ 2 =
        ∑ i : Fin n, ∑ j : Fin n, v i * (X ω i * X ω j) * v j := by
    intro ω
    simp only [PiLp.inner_apply, Real.inner_apply]
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  calc
    (∫ ω, inner ℝ (X ω) v ^ 2 ∂μ) =
        ∫ ω, ∑ i : Fin n, ∑ j : Fin n,
          v i * (X ω i * X ω j) * v j ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall hexpand)
    _ = ∑ i : Fin n, ∑ j : Fin n,
        ∫ ω, v i * (X ω i * X ω j) * v j ∂μ := by
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro i hi
        rw [integral_finsetSum]
        intro j hj
        exact ((hX i j).const_mul (v i)).mul_const (v j)
      · intro i hi
        exact integrable_finsetSum _ fun j hj =>
          ((hX i j).const_mul (v i)).mul_const (v j)
    _ = ∑ i : Fin n, ∑ j : Fin n,
        v i * HDP.secondMomentMatrix X μ i j * v j := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [integral_mul_const, integral_const_mul]
      rfl

/-- Operator form of Proposition 3.2.1(a): the quadratic form of the shared
second-moment operator is the second moment of the scalar projection.

**Book Proposition 3.2.1(a).** -/
theorem secondMomentOperator_reApplyInnerSelf {n : ℕ}
    (X : Ω → EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin n))
    (hX : ∀ i j, Integrable (fun ω => X ω i * X ω j) μ) :
    (HDP.secondMomentOperator X μ).reApplyInnerSelf v =
      ∫ ω, inner ℝ (X ω) v ^ 2 ∂μ := by
  rw [secondMoment_inner_sq X v hX]
  rw [ContinuousLinearMap.reApplyInnerSelf_apply]
  simp only [HDP.secondMomentOperator_apply, PiLp.inner_apply,
    Real.inner_apply, Matrix.mulVec, dotProduct, RCLike.re_to_real]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Expected squared norm equals the trace of the
second-moment matrix.

**Book Proposition 3.2.1(b).** -/
theorem secondMoment_norm_sq_eq_trace {n : ℕ}
    (X : Ω → EuclideanSpace ℝ (Fin n))
    (hX : ∀ i, Integrable (fun ω => (X ω i) ^ 2) μ) :
    (∫ ω, ‖X ω‖ ^ 2 ∂μ) = Matrix.trace (HDP.secondMomentMatrix X μ) := by
  calc
    (∫ ω, ‖X ω‖ ^ 2 ∂μ) =
        ∫ ω, ∑ i : Fin n, (X ω i) ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with ω
      exact EuclideanSpace.real_norm_sq_eq (X ω)
    _ = ∑ i : Fin n, ∫ ω, (X ω i) ^ 2 ∂μ := by
      rw [integral_finsetSum]
      exact fun i hi => hX i
    _ = Matrix.trace (HDP.secondMomentMatrix X μ) := by
      simp [Matrix.trace, HDP.secondMomentMatrix, pow_two]

/-- On the product probability space, the two
coordinate projections are independent copies of `X`; their squared inner
product has expectation equal to the sum of squares of all second-moment
entries (the squared Frobenius norm).

**Book Proposition 3.2.1(c).** -/
theorem secondMoment_independent_copy_inner_sq [SFinite μ] {n : ℕ}
    (X : Ω → EuclideanSpace ℝ (Fin n))
    (hX : ∀ i j, Integrable (fun ω => X ω i * X ω j) μ) :
    (∫ z : Ω × Ω, inner ℝ (X z.1) (X z.2) ^ 2 ∂μ.prod μ) =
      ∑ i : Fin n, ∑ j : Fin n,
        (HDP.secondMomentMatrix X μ i j) ^ 2 := by
  have hexpand : ∀ z : Ω × Ω,
      inner ℝ (X z.1) (X z.2) ^ 2 =
        ∑ i : Fin n, ∑ j : Fin n,
          (X z.1 i * X z.1 j) * (X z.2 i * X z.2 j) := by
    intro z
    simp only [PiLp.inner_apply, Real.inner_apply]
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  calc
    (∫ z : Ω × Ω, inner ℝ (X z.1) (X z.2) ^ 2 ∂μ.prod μ) =
        ∫ z : Ω × Ω, ∑ i : Fin n, ∑ j : Fin n,
          (X z.1 i * X z.1 j) * (X z.2 i * X z.2 j) ∂μ.prod μ :=
      integral_congr_ae (Filter.Eventually.of_forall hexpand)
    _ = ∑ i : Fin n, ∑ j : Fin n,
        ∫ z : Ω × Ω,
          (X z.1 i * X z.1 j) * (X z.2 i * X z.2 j) ∂μ.prod μ := by
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro i hi
        rw [integral_finsetSum]
        exact fun j hj => (hX i j).mul_prod (hX i j)
      · intro i hi
        exact integrable_finsetSum _ fun j hj =>
          (hX i j).mul_prod (hX i j)
    _ = ∑ i : Fin n, ∑ j : Fin n,
        (HDP.secondMomentMatrix X μ i j) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      change
        (∫ z : Ω × Ω,
          (fun ω => X ω i * X ω j) z.1 *
            (fun ω => X ω i * X ω j) z.2 ∂μ.prod μ) =
          (∫ ω, X ω i * X ω j ∂μ) ^ 2
      calc
        _ = (∫ ω, X ω i * X ω j ∂μ) *
              (∫ ω, X ω i * X ω j ∂μ) :=
          integral_prod_mul (μ := μ) (ν := μ) _ _
        _ = (∫ ω, X ω i * X ω j ∂μ) ^ 2 := by ring

/-- Equation (3.9), coordinate form: isotropy gives unit second moment in
every coordinate.

**Book Equation (3.9).** -/
theorem isotropic_coordinate_secondMoment {n : ℕ}
    {X : Ω → EuclideanSpace ℝ (Fin n)} (hX : HDP.IsIsotropic X μ) (i : Fin n) :
    ∫ ω, (X ω i) ^ 2 ∂μ = 1 :=
  hX.secondMoment_coord i

/-- Isotropy is invariant under almost-everywhere equality.

**Lean implementation helper.** -/
theorem isIsotropic_congr_ae {n : ℕ}
    {X Y : Ω → EuclideanSpace ℝ (Fin n)} (hXY : X =ᵐ[μ] Y)
    (hX : HDP.IsIsotropic X μ) : HDP.IsIsotropic Y μ := by
  rw [HDP.IsIsotropic] at hX ⊢
  ext i j
  change (∫ ω, Y ω i * Y ω j ∂μ) = (1 : Matrix (Fin n) (Fin n) ℝ) i j
  calc
    (∫ ω, Y ω i * Y ω j ∂μ) = ∫ ω, X ω i * X ω j ∂μ := by
      apply integral_congr_ae
      filter_upwards [hXY] with ω hω
      rw [hω]
    _ = HDP.secondMomentMatrix X μ i j := rfl
    _ = (1 : Matrix (Fin n) (Fin n) ℝ) i j := congrFun (congrFun hX i) j

end HDP.Chapter3

end Source_03_Covariance

/-! ## Material formerly in `04_PCA.lean` -/

section Source_04_PCA

/-!
# Book Chapter 3, Section 3.2: principal component analysis

This file exposes the optimization characterization through Mathlib's
Rayleigh quotient.  The source's `uᵢ`/`vᵢ` typo is avoided by using the
operator/eigenvector interface directly.
-/

open MeasureTheory ProbabilityTheory Real Metric
open scoped BigOperators NNReal

namespace HDP.Chapter3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The largest Rayleigh value of a continuous linear operator.

**Lean implementation helper.** -/
noncomputable def topRayleighValue (T : E →L[ℝ] E) : ℝ :=
  ⨆ x : {x : E // x ≠ 0}, inner ℝ (T x) x / ‖(x : E)‖ ^ 2

/-- Rayleigh quotients of a fixed self-adjoint operator are bounded above on the unit sphere.

**Lean implementation helper.** -/
lemma bddAbove_rayleigh (T : E →L[ℝ] E) :
    BddAbove (Set.range fun x : {x : E // x ≠ 0} =>
      inner ℝ (T x) x / ‖(x : E)‖ ^ 2) := by
  refine ⟨‖T‖, ?_⟩
  rintro y ⟨x, rfl⟩
  exact (le_abs_self _).trans (T.rayleighQuotient_le_norm x)

/-- Every Rayleigh quotient is at most the top Rayleigh value.

**Lean implementation helper.** -/
theorem rayleighQuotient_le_top (T : E →L[ℝ] E) (x : E) (hx : x ≠ 0) :
    T.rayleighQuotient x ≤ topRayleighValue T := by
  change inner ℝ (T x) x / ‖x‖ ^ 2 ≤ _
  exact le_ciSup (bddAbove_rayleigh T) (⟨x, hx⟩ : {x : E // x ≠ 0})

/-- For the top component: in finite dimensions the
maximum Rayleigh value is an eigenvalue. Repeating this theorem on successive
orthogonal complements gives the source's ordered `k`th formulation.

**Book Proposition 3.2.2.** -/
theorem topRayleighValue_is_eigenvalue [FiniteDimensional ℝ E] [Nontrivial E]
    {T : E →L[ℝ] E} (hT : IsSelfAdjoint T) :
    Module.End.HasEigenvalue (T : E →ₗ[ℝ] E) (topRayleighValue T) := by
  exact hT.isSymmetric.hasEigenvalue_iSup_of_finiteDimensional

/-- The top Rayleigh value can equivalently be computed on the unit sphere.

**Lean implementation helper.** -/
theorem topRayleighValue_eq_iSup_unitSphere (T : E →L[ℝ] E) :
    topRayleighValue T =
      ⨆ x : Metric.sphere (0 : E) 1, T.rayleighQuotient x := by
  change (⨆ x : {x : E // x ≠ 0}, T.rayleighQuotient x) = _
  exact T.iSup_rayleigh_eq_iSup_rayleigh_sphere (by norm_num)

/-- A unit eigenvector attains its eigenvalue as a quadratic form.

**Lean implementation helper.** -/
theorem quadraticForm_eq_eigenvalue {T : E →L[ℝ] E} {v : E} {lam : ℝ}
    (hv : ‖v‖ = 1) (heig : T v = lam • v) :
    T.reApplyInnerSelf v = lam := by
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, heig, inner_smul_left,
    real_inner_self_eq_norm_sq, hv]
  simp

/-- Source-facing PCA maximum principle for the first principal component.

**Book Section 3.2.** -/
theorem pca_top_component {T : E →L[ℝ] E} {v : E} {lam : ℝ}
    (hv : ‖v‖ = 1) (heig : T v = lam • v)
    (hmax : ∀ x : E, ‖x‖ = 1 → T.reApplyInnerSelf x ≤ lam) :
    IsGreatest (T.reApplyInnerSelf '' Metric.sphere (0 : E) 1) lam := by
  constructor
  · refine ⟨v, ?_, quadraticForm_eq_eigenvalue hv heig⟩
    simpa [Metric.mem_sphere] using hv
  · rintro y ⟨x, hx, rfl⟩
    apply hmax x
    simpa [Metric.mem_sphere] using hx

/-! ## The full ordered PCA maximum principle -/

/-- A decreasing diagonal quadratic form is bounded by its `k`th diagonal
entry on unit vectors whose earlier coordinates vanish. This is the scalar
inequality at the heart of the ordered PCA principle.

**Lean implementation helper.** -/
theorem antitone_weighted_sq_sum_le {n : ℕ}
    (lam : Fin n → ℝ) (hlam : Antitone lam) (k : Fin n)
    (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ = 1)
    (hzero : ∀ i, i < k → x i = 0) :
    (∑ i, lam i * x i ^ 2) ≤ lam k := by
  classical
  calc
    (∑ i, lam i * x i ^ 2) ≤ ∑ i, lam k * x i ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hik : i < k
      · rw [hzero i hik]
        simp
      · exact mul_le_mul_of_nonneg_right (hlam (le_of_not_gt hik)) (sq_nonneg _)
    _ = lam k * ∑ i, x i ^ 2 := by rw [Finset.mul_sum]
    _ = lam k * ‖x‖ ^ 2 := by rw [EuclideanSpace.real_norm_sq_eq]
    _ = lam k := by rw [hx]; ring

/-- Let the eigenvalues
of a self-adjoint operator be sorted in decreasing order. A unit vector
orthogonal to the first `k` eigenvectors has quadratic form at most the `k`th
eigenvalue.

**Book Proposition 3.2.2.** -/
theorem pca_kth_component_le [FiniteDimensional ℝ E] {n : ℕ}
    (T : E →L[ℝ] E) (hT : IsSelfAdjoint T)
    (hn : Module.finrank ℝ E = n) (k : Fin n) (x : E)
    (hx : ‖x‖ = 1)
    (horth : ∀ i : Fin n, i < k →
      inner ℝ (hT.isSymmetric.eigenvectorBasis hn i) x = 0) :
    T.reApplyInnerSelf x ≤ hT.isSymmetric.eigenvalues hn k := by
  classical
  let hS := hT.isSymmetric
  let b := hS.eigenvectorBasis hn
  let y : EuclideanSpace ℝ (Fin n) := b.repr x
  have hy : ‖y‖ = 1 := by
    simpa [y, b] using (b.repr.norm_map x).trans hx
  have hyzero : ∀ i : Fin n, i < k → y i = 0 := by
    intro i hik
    simpa [y, b, OrthonormalBasis.repr_apply_apply] using horth i hik
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, RCLike.re_to_real]
  rw [← b.repr.inner_map_map]
  simp only [PiLp.inner_apply, Real.inner_apply]
  have hcoord (i : Fin n) :
      b.repr (T x) i = hS.eigenvalues hn i * b.repr x i := by
    change (hS.eigenvectorBasis hn).repr ((T : E →ₗ[ℝ] E) x) i = _
    exact hS.eigenvectorBasis_apply_self_apply hn x i
  simp_rw [hcoord, mul_assoc, ← pow_two]
  simpa [y] using
    antitone_weighted_sq_sum_le (hS.eigenvalues hn)
      (hS.eigenvalues_antitone hn) k y hy hyzero

/-- The `k`th ordered eigenvector is a unit vector and attains the `k`th
eigenvalue in the quadratic form.

**Book Proposition 3.2.2.** -/
theorem pca_kth_eigenvector_attains [FiniteDimensional ℝ E] {n : ℕ}
    (T : E →L[ℝ] E) (hT : IsSelfAdjoint T)
    (hn : Module.finrank ℝ E = n) (k : Fin n) :
    ‖hT.isSymmetric.eigenvectorBasis hn k‖ = 1 ∧
      T.reApplyInnerSelf (hT.isSymmetric.eigenvectorBasis hn k) =
        hT.isSymmetric.eigenvalues hn k := by
  let hS := hT.isSymmetric
  let b := hS.eigenvectorBasis hn
  have hnorm : ‖b k‖ = 1 := b.norm_eq_one k
  refine ⟨hnorm, ?_⟩
  apply quadraticForm_eq_eigenvalue hnorm
  exact hS.apply_eigenvectorBasis hn k

/-- The maximum over
unit vectors orthogonal to the preceding eigenvectors is the `k`th eigenvalue,
and it is attained by the `k`th eigenvector.

**Book Proposition 3.2.2.** -/
theorem pca_kth_maximum_principle [FiniteDimensional ℝ E] {n : ℕ}
    (T : E →L[ℝ] E) (hT : IsSelfAdjoint T)
    (hn : Module.finrank ℝ E = n) (k : Fin n) :
    IsGreatest
      (T.reApplyInnerSelf '' {x : E | ‖x‖ = 1 ∧
        ∀ i : Fin n, i < k →
          inner ℝ (hT.isSymmetric.eigenvectorBasis hn i) x = 0})
      (hT.isSymmetric.eigenvalues hn k) := by
  classical
  let hS := hT.isSymmetric
  let b := hS.eigenvectorBasis hn
  have hattain := pca_kth_eigenvector_attains T hT hn k
  constructor
  · refine ⟨b k, ?_, hattain.2⟩
    refine ⟨hattain.1, ?_⟩
    intro i hik
    rw [b.inner_eq_ite]
    simp [ne_of_lt hik]
  · rintro y ⟨x, ⟨hx, horth⟩, rfl⟩
    exact pca_kth_component_le T hT hn k x hx horth

/-- Uncentered random-vector form of Proposition 3.2.2. The objective is the actual
second moment of the scalar projection and the spectral data are those of the
shared second-moment operator.

**Lean implementation helper for Book Proposition 3.2.2.** -/
theorem secondMoment_pca_kth_maximum
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n : ℕ}
    (X : Ω → EuclideanSpace ℝ (Fin n))
    (hX : ∀ i j, Integrable (fun ω => X ω i * X ω j) μ)
    (k : Fin n) :
    let hT := HDP.secondMomentOperator_isSelfAdjoint (μ := μ) X
    IsGreatest
      ((fun x => ∫ ω, inner ℝ (X ω) x ^ 2 ∂μ) ''
        {x : EuclideanSpace ℝ (Fin n) | ‖x‖ = 1 ∧
          ∀ i : Fin n, i < k →
            inner ℝ (hT.isSymmetric.eigenvectorBasis
              (finrank_euclideanSpace_fin (𝕜 := ℝ)) i) x = 0})
      (hT.isSymmetric.eigenvalues
        (finrank_euclideanSpace_fin (𝕜 := ℝ)) k) := by
  dsimp only
  have hmax := pca_kth_maximum_principle
    (HDP.secondMomentOperator X μ)
    (HDP.secondMomentOperator_isSelfAdjoint (μ := μ) X)
    (finrank_euclideanSpace_fin (𝕜 := ℝ)) k
  simpa only [secondMomentOperator_reApplyInnerSelf X _ hX] using hmax

/-- The quadratic form of the covariance operator is exactly the variance of
the corresponding scalar projection.

**Book Equation (3.8).** -/
theorem covarianceOperator_reApplyInnerSelf
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ}
    (X : Ω → EuclideanSpace ℝ (Fin n)) (hX : MemLp X 2 μ)
    (v : EuclideanSpace ℝ (Fin n)) :
    (HDP.covarianceOperator X μ).reApplyInnerSelf v =
      Var[fun ω => inner ℝ (X ω) v; μ] := by
  have hi (i : Fin n) : MemLp (fun ω => X ω i) 2 μ := by
    simpa only [Function.comp_apply, EuclideanSpace.coe_proj] using
      hX.continuousLinearMap_comp (EuclideanSpace.proj (𝕜 := ℝ) i)
  have hvi (i : Fin n) : MemLp (fun ω => v i * X ω i) 2 μ :=
    (hi i).const_mul (v i)
  rw [← covariance_self]
  rw [ContinuousLinearMap.reApplyInnerSelf_apply]
  simp only [HDP.covarianceOperator_apply, PiLp.inner_apply,
    Real.inner_apply, Matrix.mulVec, dotProduct, RCLike.re_to_real]
  have hinner : (fun ω => ∑ i, X ω i * v i) =
      (fun ω => ∑ i, v i * X ω i) := by
    funext ω
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hinner]
  have hsumfun : (∑ i, (fun ω => v i * X ω i)) =
      (fun ω => ∑ i, v i * X ω i) := by
    funext ω
    simp
  rw [← hsumfun]
  have hcov := covariance_sum_sum
    (X := fun i ω => v i * X ω i)
    (Y := fun j ω => v j * X ω j) hvi hvi
  rw [hcov]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [covariance_const_mul_left, covariance_const_mul_right]
  change Chapter1.covMatrix X μ i j * v j * v i =
    v i * (v j * cov[fun ω => X ω i, fun ω => X ω j; μ])
  rw [Chapter1.covMatrix_apply]
  ring
  exact (hX.inner_const (𝕜 := ℝ) v).1.aemeasurable

/-- Principal component analysis for an arbitrary square-integrable random
vector: the `k`th covariance eigenvalue is the maximum variance of a unit
projection orthogonal to the preceding covariance eigenvectors, and the
maximum is attained by the `k`th eigenvector.

**Book Corollary 3.2.3.** -/
theorem covariance_pca_kth_maximum
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ}
    (X : Ω → EuclideanSpace ℝ (Fin n)) (hX : MemLp X 2 μ)
    (k : Fin n) :
    let hT := HDP.covarianceOperator_isSelfAdjoint (μ := μ) X
    IsGreatest
      ((fun v => Var[fun ω => inner ℝ (X ω) v; μ]) ''
        {v : EuclideanSpace ℝ (Fin n) | ‖v‖ = 1 ∧
          ∀ i : Fin n, i < k →
            inner ℝ (hT.isSymmetric.eigenvectorBasis
              (finrank_euclideanSpace_fin (𝕜 := ℝ)) i) v = 0})
      (hT.isSymmetric.eigenvalues
        (finrank_euclideanSpace_fin (𝕜 := ℝ)) k) := by
  dsimp only
  have hmax := pca_kth_maximum_principle
    (HDP.covarianceOperator X μ)
    (HDP.covarianceOperator_isSelfAdjoint (μ := μ) X)
    (finrank_euclideanSpace_fin (𝕜 := ℝ)) k
  simpa only [covarianceOperator_reApplyInnerSelf X hX] using hmax

end HDP.Chapter3

end Source_04_PCA

/-! ## Material formerly in `05_MomentGeometry.lean` -/

section Source_05_MomentGeometry

/-!
# Moment geometry, small-ball bounds, and random-vector maxima

This thematic core module contains the load-bearing results originating in
Exercises 3.5--3.7, 3.9--3.10, and 3.13. Chapter 3 and later chapters use
these facts, so their unique authoritative declarations live in core rather
than in an exercise leaf.
-/

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators ENNReal NNReal RealInnerProductSpace

namespace HDP.Chapter3

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Defines `finiteFrameProjection`, the finite frame projection used in the surrounding construction.

**Lean implementation helper.** -/
noncomputable def finiteFrameProjection
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]
    (u : ι → E) (x : E) : E :=
  ∑ i, (inner ℝ (u i) x) • u i

/-- Defines `finiteLpRadius`, the finite lp radius used in the surrounding construction.

**Lean implementation helper.** -/
private noncomputable def finiteLpRadius {ι : Type*} [Fintype ι]
    (p : ℝ) (X : ι → Ω → ℝ) (ω : Ω) : ℝ :=
  HDP.Chapter1.lpNorm p (fun i => X i ω)

/-- Shows that `finiteLpRadius` is measurable.

**Lean implementation helper.** -/
private lemma finiteLpRadius_measurable {ι : Type*} [Fintype ι]
    {p : ℝ} (hp : 0 < p) {X : ι → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) :
    Measurable (finiteLpRadius p X) := by
  have hsum : Measurable (fun ω => ∑ i, |X i ω| ^ p) :=
    Finset.measurable_sum _ fun i _ =>
      (Real.continuous_rpow_const hp.le).measurable.comp (hXm i).abs
  have heq : finiteLpRadius p X =
      fun ω => (∑ i, |X i ω| ^ p) ^ (1 / p) := by
    funext ω
    exact HDP.Chapter1.lpNorm_eq_sum hp _
  rw [heq]
  exact (Real.continuous_rpow_const (by positivity)).measurable.comp hsum

/-- Shows that `finiteLpRadius` is nonnegative.

**Lean implementation helper.** -/
private lemma finiteLpRadius_nonneg {ι : Type*} [Fintype ι]
    {p : ℝ} (hp : 0 < p) (X : ι → Ω → ℝ) (ω : Ω) :
    0 ≤ finiteLpRadius p X ω :=
  HDP.Chapter1.lpNorm_nonneg hp _

/-- Raising the finite `Lᵖ` radius to the power `p` gives the supremum of the corresponding `p`th moments.

**Lean implementation helper.** -/
private lemma finiteLpRadius_rpow {ι : Type*} [Fintype ι]
    {p : ℝ} (hp : 0 < p) (X : ι → Ω → ℝ) (ω : Ω) :
    finiteLpRadius p X ω ^ p = ∑ i, |X i ω| ^ p := by
  rw [finiteLpRadius, HDP.Chapter1.lpNorm_eq_sum hp]
  have hsum : 0 ≤ ∑ i, |X i ω| ^ p :=
    Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg _) _
  simpa [one_div] using Real.rpow_inv_rpow hsum hp.ne'

/-- Every member of a finite family contributing to a finite `Lᵖ` radius belongs to `Lᵖ`.

**Lean implementation helper.** -/
private lemma finiteLpRadius_memLp [IsProbabilityMeasure μ]
    {ι : Type*} [Fintype ι] {p : ℝ} (hp : 1 ≤ p)
    {X : ι → Ω → ℝ} (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, HDP.SubGaussian (X i) μ) :
    MemLp (finiteLpRadius p X) (ENNReal.ofReal p) μ := by
  have hp0 : 0 < p := one_pos.trans_le hp
  have hZm := finiteLpRadius_measurable hp0 hXm
  have hXiMem : ∀ i, MemLp (X i) (ENNReal.ofReal p) μ := fun i =>
    (hX i).memLp (hXm i).aemeasurable hp
  have hXiInt : ∀ i, Integrable (fun ω => |X i ω| ^ p) μ := by
    intro i
    have h := (hXiMem i).integrable_norm_rpow
      (by simpa [ENNReal.ofReal_eq_zero] using not_le.mpr hp0) (by simp)
    simpa [ENNReal.toReal_ofReal hp0.le, Real.norm_eq_abs] using h
  have hsumInt : Integrable (fun ω => ∑ i, |X i ω| ^ p) μ :=
    integrable_finsetSum _ fun i _ => hXiInt i
  apply (MeasureTheory.integrable_norm_rpow_iff hZm.aestronglyMeasurable
    (by simpa [ENNReal.ofReal_eq_zero] using not_le.mpr hp0) (by simp)).1
  have hcong : (fun ω => ‖finiteLpRadius p X ω‖ ^
      (ENNReal.ofReal p).toReal) =ᵐ[μ]
      fun ω => ∑ i, |X i ω| ^ p := by
    filter_upwards [] with ω
    rw [ENNReal.toReal_ofReal hp0.le, Real.norm_eq_abs,
      abs_of_nonneg (finiteLpRadius_nonneg hp0 X ω)]
    exact finiteLpRadius_rpow hp0 X ω
  exact hsumInt.congr hcong.symm

/-- `integral_finiteLpRadius_le` bounds the expected finite `Lᵖ` radius by `(∑ i, ‖X i‖ₚ ^ p) ^ (1 / p)`.

**Lean implementation helper.** -/
private lemma integral_finiteLpRadius_le [IsProbabilityMeasure μ]
    {ι : Type*} [Fintype ι] {p : ℝ} (hp : 1 ≤ p)
    {X : ι → Ω → ℝ} (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, HDP.SubGaussian (X i) μ) :
    (∫ ω, finiteLpRadius p X ω ∂μ) ≤
      (∑ i, HDP.Chapter1.lpNormRV (X i) p μ ^ p) ^ (1 / p) := by
  have hp0 : 0 < p := one_pos.trans_le hp
  have hZmem := finiteLpRadius_memLp hp hXm hX
  have hZint : Integrable (finiteLpRadius p X) μ :=
    hZmem.integrable (by simpa using ENNReal.ofReal_le_ofReal hp)
  have hmono := HDP.Chapter1.exercise_1_11a
    (X := finiteLpRadius p X) (μ := μ) one_pos hp hZmem
  have hL1 : HDP.Chapter1.lpNormRV (finiteLpRadius p X) 1 μ =
      ∫ ω, finiteLpRadius p X ω ∂μ := by
    rw [HDP.Chapter1.lpNormRV]
    have hcong : (fun ω => |finiteLpRadius p X ω| ^ (1 : ℝ)) =ᵐ[μ]
        finiteLpRadius p X := by
      filter_upwards [] with ω
      rw [Real.rpow_one, abs_of_nonneg (finiteLpRadius_nonneg hp0 X ω)]
    rw [integral_congr_ae hcong]
    norm_num
  have hLp : HDP.Chapter1.lpNormRV (finiteLpRadius p X) p μ =
      (∑ i, HDP.Chapter1.lpNormRV (X i) p μ ^ p) ^ (1 / p) := by
    rw [HDP.Chapter1.lpNormRV]
    have hcong : (fun ω => |finiteLpRadius p X ω| ^ p) =ᵐ[μ]
        fun ω => ∑ i, |X i ω| ^ p := by
      filter_upwards [] with ω
      rw [abs_of_nonneg (finiteLpRadius_nonneg hp0 X ω)]
      exact finiteLpRadius_rpow hp0 X ω
    rw [integral_congr_ae hcong, integral_finsetSum]
    · congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [HDP.Chapter1.lpNormRV]
      have hint0 : 0 ≤ ∫ ω, |X i ω| ^ p ∂μ :=
        integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) _
      simpa [one_div] using (Real.rpow_inv_rpow hint0 hp0.ne').symm
    · intro i hi
      have himem := (hX i).memLp (hXm i).aemeasurable hp
      have hiint := himem.integrable_norm_rpow
        (by simpa [ENNReal.ofReal_eq_zero] using not_le.mpr hp0) (by simp)
      simpa [ENNReal.toReal_ofReal hp0.le, Real.norm_eq_abs] using hiint
  calc
    (∫ ω, finiteLpRadius p X ω ∂μ) =
        HDP.Chapter1.lpNormRV (finiteLpRadius p X) 1 μ := hL1.symm
    _ ≤ HDP.Chapter1.lpNormRV (finiteLpRadius p X) p μ := hmono
    _ = (∑ i, HDP.Chapter1.lpNormRV (X i) p μ ^ p) ^ (1 / p) := hLp

/-- We write the corrected
dimension as `N = n + 2`, so `log N > 0` automatically. Independence is not
needed for this upper bound. The absolute constant in the source can be
taken to be `1` in the range `p ≤ log N`.

**Book Exercise 3.5.** -/
theorem exercise_3_5_small {n : ℕ} [IsProbabilityMeasure μ]
    {X : Fin (n + 2) → Ω → ℝ} (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, HDP.SubGaussian (X i) μ) {K p : ℝ}
    (hK : 0 < K) (hKb : ∀ i, HDP.psi2Norm (X i) μ ≤ K)
    (hp : 1 ≤ p) (_hplog : p ≤ Real.log ((n : ℝ) + 2)) :
    (∫ ω, HDP.Chapter1.lpNorm p (fun i => X i ω) ∂μ) ≤
      K * Real.sqrt p * (((n : ℝ) + 2) ^ (1 / p)) := by
  have hp0 : 0 < p := one_pos.trans_le hp
  have hbase : 0 < (n : ℝ) + 2 := by positivity
  have hmoment : ∀ i, HDP.Chapter1.lpNormRV (X i) p μ ≤
      K * Real.sqrt p := fun i =>
    (hX i).moment_bound (hXm i).aemeasurable hp |>.trans
      (mul_le_mul_of_nonneg_right (hKb i) (Real.sqrt_nonneg p))
  have hlp0 : ∀ i, 0 ≤ HDP.Chapter1.lpNormRV (X i) p μ := by
    intro i
    unfold HDP.Chapter1.lpNormRV
    positivity
  have hagg := integral_finiteLpRadius_le hp hXm hX
  calc
    (∫ ω, HDP.Chapter1.lpNorm p (fun i => X i ω) ∂μ) =
        ∫ ω, finiteLpRadius p X ω ∂μ := rfl
    _ ≤ (∑ i, HDP.Chapter1.lpNormRV (X i) p μ ^ p) ^ (1 / p) := hagg
    _ ≤ (∑ _i : Fin (n + 2), (K * Real.sqrt p) ^ p) ^ (1 / p) := by
      exact Real.rpow_le_rpow
        (Finset.sum_nonneg fun i _ =>
          Real.rpow_nonneg (hlp0 i) _)
        (Finset.sum_le_sum fun i _ => Real.rpow_le_rpow
          (hlp0 i) (hmoment i) hp0.le)
        (by positivity)
    _ = K * Real.sqrt p * (((n : ℝ) + 2) ^ (1 / p)) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      have hc : 0 < K * Real.sqrt p := mul_pos hK (Real.sqrt_pos.2 hp0)
      rw [Real.mul_rpow hbase.le (Real.rpow_nonneg hc.le p),
        ← Real.rpow_mul hc.le]
      have hinv : p * (1 / p) = 1 := by field_simp
      rw [hinv, Real.rpow_one]
      ring

/-- Maximum absolute coordinate of a finite random vector.

**Lean implementation helper.** -/
noncomputable def maxAbsCoordinates {n : ℕ}
    (X : Fin (n + 2) → Ω → ℝ) (ω : Ω) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i => |X i ω|

/-- Shows that `maxAbsCoordinates` is measurable.

**Lean implementation helper.** -/
private lemma maxAbsCoordinates_measurable {n : ℕ}
    {X : Fin (n + 2) → Ω → ℝ} (hXm : ∀ i, Measurable (X i)) :
    Measurable (maxAbsCoordinates X) := by
  change Measurable (fun ω =>
    Finset.univ.sup' Finset.univ_nonempty fun i => |X i ω|)
  have h1 : Measurable (Finset.univ.sup' Finset.univ_nonempty
      fun i ω => |X i ω|) :=
    Finset.measurable_sup' _ fun i _ => (hXm i).abs
  have h2 : (Finset.univ.sup' Finset.univ_nonempty
      fun i ω => |X i ω|) =
      (fun ω => Finset.univ.sup' Finset.univ_nonempty fun i => |X i ω|) := by
    funext ω
    simp only [Finset.sup'_apply]
  rwa [h2] at h1

/-- Shows that `maxAbsCoordinates` is nonnegative.

**Lean implementation helper.** -/
private lemma maxAbsCoordinates_nonneg {n : ℕ}
    (X : Fin (n + 2) → Ω → ℝ) (ω : Ω) :
    0 ≤ maxAbsCoordinates X ω := by
  obtain ⟨i, hi⟩ := Finset.univ_nonempty (α := Fin (n + 2))
  exact (abs_nonneg (X i ω)).trans
    (Finset.le_sup' (fun j => |X j ω|) hi)

/-- `integral_maxAbsCoordinates_le` bounds the expected largest absolute coordinate by `2 * sqrt (log (n + 2)) * K`.

**Lean implementation helper.** -/
private lemma integral_maxAbsCoordinates_le {n : ℕ} [IsProbabilityMeasure μ]
    {X : Fin (n + 2) → Ω → ℝ} (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, HDP.SubGaussian (X i) μ) {K : ℝ} (hK : 0 < K)
    (hKb : ∀ i, HDP.psi2Norm (X i) μ ≤ K) :
    (∫ ω, maxAbsCoordinates X ω ∂μ) ≤
      2 * Real.sqrt (Real.log ((n : ℝ) + 2)) * K := by
  have hMm := maxAbsCoordinates_measurable hXm
  have hMsub : HDP.SubGaussian (maxAbsCoordinates X) μ := by
    change HDP.SubGaussian
      (fun ω => Finset.univ.sup' Finset.univ_nonempty fun i => |X i ω|) μ
    exact (HDP.psi2Norm_max_abs_le hXm hX hK hKb).1
  have hMpsi : HDP.psi2Norm (maxAbsCoordinates X) μ ≤
      2 * Real.sqrt (Real.log ((n : ℝ) + 2)) * K := by
    change HDP.psi2Norm
      (fun ω => Finset.univ.sup' Finset.univ_nonempty fun i => |X i ω|) μ ≤ _
    exact HDP.psi2Norm_max_abs_le' hXm hX hK hKb
  have hmoment := hMsub.moment_bound hMm.aemeasurable (le_refl (1 : ℝ))
  have hL1 : HDP.Chapter1.lpNormRV (maxAbsCoordinates X) 1 μ =
      ∫ ω, maxAbsCoordinates X ω ∂μ := by
    rw [HDP.Chapter1.lpNormRV]
    have hcong : (fun ω => |maxAbsCoordinates X ω| ^ (1 : ℝ)) =ᵐ[μ]
        maxAbsCoordinates X := by
      filter_upwards [] with ω
      rw [Real.rpow_one, abs_of_nonneg (maxAbsCoordinates_nonneg X ω)]
    rw [integral_congr_ae hcong]
    norm_num
  calc
    (∫ ω, maxAbsCoordinates X ω ∂μ) =
        HDP.Chapter1.lpNormRV (maxAbsCoordinates X) 1 μ := hL1.symm
    _ ≤ HDP.psi2Norm (maxAbsCoordinates X) μ * Real.sqrt 1 := hmoment
    _ = HDP.psi2Norm (maxAbsCoordinates X) μ := by norm_num
    _ ≤ 2 * Real.sqrt (Real.log ((n : ℝ) + 2)) * K := hMpsi

/-- Bounds `finiteLpRadius` above by `max`.

**Lean implementation helper.** -/
private lemma finiteLpRadius_le_max {n : ℕ} {p : ℝ} (hp : 1 ≤ p)
    (X : Fin (n + 2) → Ω → ℝ) (ω : Ω) :
    finiteLpRadius p X ω ≤
      (((n : ℝ) + 2) ^ (1 / p)) * maxAbsCoordinates X ω := by
  have hp0 : 0 < p := one_pos.trans_le hp
  have hN : 0 ≤ (n : ℝ) + 2 := by positivity
  have hM0 := maxAbsCoordinates_nonneg X ω
  rw [finiteLpRadius, HDP.Chapter1.lpNorm_eq_sum hp0]
  calc
    (∑ i, |X i ω| ^ p) ^ (1 / p) ≤
        (∑ _i : Fin (n + 2), maxAbsCoordinates X ω ^ p) ^ (1 / p) := by
      exact Real.rpow_le_rpow
        (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg _) _)
        (Finset.sum_le_sum fun i _ => Real.rpow_le_rpow (abs_nonneg _)
          (Finset.le_sup' (fun j => |X j ω|) (Finset.mem_univ i)) hp0.le)
        (by positivity)
    _ = (((n : ℝ) + 2) ^ (1 / p)) * maxAbsCoordinates X ω := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      rw [Real.mul_rpow hN (Real.rpow_nonneg hM0 p),
        ← Real.rpow_mul hM0]
      have hinv : p * (1 / p) = 1 := by field_simp
      rw [hinv, Real.rpow_one]

/-- The finite `p ≥ log N` branch, with the explicit
absolute constant `6`.

**Book Exercise 3.5.** -/
theorem exercise_3_5_large {n : ℕ} [IsProbabilityMeasure μ]
    {X : Fin (n + 2) → Ω → ℝ} (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, HDP.SubGaussian (X i) μ) {K p : ℝ}
    (hK : 0 < K) (hKb : ∀ i, HDP.psi2Norm (X i) μ ≤ K)
    (hp : 1 ≤ p) (hlogp : Real.log ((n : ℝ) + 2) ≤ p) :
    (∫ ω, HDP.Chapter1.lpNorm p (fun i => X i ω) ∂μ) ≤
      6 * K * Real.sqrt (Real.log ((n : ℝ) + 2)) := by
  have hp0 : 0 < p := one_pos.trans_le hp
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hN1 : 1 ≤ (n : ℝ) + 2 := by linarith
  have hlog0 : 0 < Real.log ((n : ℝ) + 2) :=
    Real.log_pos (by linarith)
  have hpow3 : ((n : ℝ) + 2) ^ (1 / p) ≤ 3 := by
    have hinv : 1 / p ≤ (Real.log ((n : ℝ) + 2))⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le hlog0 hlogp
    calc
      ((n : ℝ) + 2) ^ (1 / p) ≤
          ((n : ℝ) + 2) ^ (Real.log ((n : ℝ) + 2))⁻¹ :=
        Real.rpow_le_rpow_of_exponent_le hN1 hinv
      _ ≤ Real.exp 1 := Real.rpow_inv_log_le_exp_one
      _ ≤ 3 := Real.exp_one_lt_three.le
  have hZmem := finiteLpRadius_memLp hp hXm hX
  have hZint : Integrable (finiteLpRadius p X) μ :=
    hZmem.integrable (by simpa using ENNReal.ofReal_le_ofReal hp)
  have hMm := maxAbsCoordinates_measurable hXm
  have hMsub : HDP.SubGaussian (maxAbsCoordinates X) μ := by
    change HDP.SubGaussian
      (fun ω => Finset.univ.sup' Finset.univ_nonempty fun i => |X i ω|) μ
    exact (HDP.psi2Norm_max_abs_le hXm hX hK hKb).1
  have hMint : Integrable (maxAbsCoordinates X) μ :=
    (hMsub.memLp hMm.aemeasurable (le_refl (1 : ℝ))).integrable
      (by norm_num)
  have hmax := integral_maxAbsCoordinates_le hXm hX hK hKb
  calc
    (∫ ω, HDP.Chapter1.lpNorm p (fun i => X i ω) ∂μ) =
        ∫ ω, finiteLpRadius p X ω ∂μ := rfl
    _ ≤ ∫ ω, (((n : ℝ) + 2) ^ (1 / p)) * maxAbsCoordinates X ω ∂μ :=
      integral_mono hZint (hMint.const_mul _) fun ω => finiteLpRadius_le_max hp X ω
    _ = (((n : ℝ) + 2) ^ (1 / p)) *
        ∫ ω, maxAbsCoordinates X ω ∂μ := by rw [integral_const_mul]
    _ ≤ (((n : ℝ) + 2) ^ (1 / p)) *
        (2 * Real.sqrt (Real.log ((n : ℝ) + 2)) * K) :=
      mul_le_mul_of_nonneg_left hmax (Real.rpow_nonneg (by positivity) _)
    _ ≤ 3 * (2 * Real.sqrt (Real.log ((n : ℝ) + 2)) * K) :=
      mul_le_mul_of_nonneg_right hpow3 (by positivity)
    _ = 6 * K * Real.sqrt (Real.log ((n : ℝ) + 2)) := by ring

/-- Safe `p = ∞` branch.

**Book Exercise 3.5.** -/
theorem exercise_3_5_top {n : ℕ} [IsProbabilityMeasure μ]
    {X : Fin (n + 2) → Ω → ℝ} (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, HDP.SubGaussian (X i) μ) {K : ℝ}
    (hK : 0 < K) (hKb : ∀ i, HDP.psi2Norm (X i) μ ≤ K) :
    (∫ ω, maxAbsCoordinates X ω ∂μ) ≤
      2 * Real.sqrt (Real.log ((n : ℝ) + 2)) * K :=
  integral_maxAbsCoordinates_le hXm hX hK hKb

/-- Expected `ell^p` norm of an isotropic vector.

**Book Exercise 3.5.** -/
theorem exercise_3_5 {n : ℕ} [IsProbabilityMeasure μ]
    {X : Fin (n + 2) → Ω → ℝ} (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, HDP.SubGaussian (X i) μ) {K p : ℝ}
    (hK : 0 < K) (hKb : ∀ i, HDP.psi2Norm (X i) μ ≤ K)
    (hp : 1 ≤ p) :
    (p ≤ Real.log ((n : ℝ) + 2) →
      (∫ ω, HDP.Chapter1.lpNorm p (fun i => X i ω) ∂μ) ≤
        K * Real.sqrt p * (((n : ℝ) + 2) ^ (1 / p))) ∧
    (Real.log ((n : ℝ) + 2) ≤ p →
      (∫ ω, HDP.Chapter1.lpNorm p (fun i => X i ω) ∂μ) ≤
        6 * K * Real.sqrt (Real.log ((n : ℝ) + 2))) ∧
    (∫ ω, maxAbsCoordinates X ω ∂μ) ≤
      2 * Real.sqrt (Real.log ((n : ℝ) + 2)) * K := by
  exact ⟨fun hplog => exercise_3_5_small hXm hX hK hKb hp hplog,
    fun hlogp => exercise_3_5_large hXm hX hK hKb hp hlogp,
    exercise_3_5_top hXm hX hK hKb⟩

/-- For `p ≥ 1`, the standard Gaussian upper tail at `sqrt p / 4` is at least `exp (-p) / 100`, as stated by `gaussian_tail_exp_lower`.

**Lean implementation helper.** -/
private lemma gaussian_tail_exp_lower {p : ℝ} (hp : 1 ≤ p) :
    (1 / 100 : ℝ) * Real.exp (-p) ≤
      (gaussianReal 0 1).real
        (Set.Ici (Real.sqrt p / 4)) := by
  let s : ℝ := Real.sqrt p
  let t : ℝ := s / 4
  have hp0 : 0 < p := one_pos.trans_le hp
  have hs0 : 0 < s := by simpa [s] using Real.sqrt_pos.2 hp0
  have hsSq : s ^ 2 = p := by simpa [s] using Real.sq_sqrt hp0.le
  have ht0 : 0 < t := div_pos hs0 (by norm_num)
  have htSq : t ^ 2 = p / 16 := by dsimp [t]; rw [div_pow, hsSq]; norm_num
  have hratio : 4 / (17 * s) ≤ t / (t ^ 2 + 1) := by
    rw [div_le_div_iff₀ (mul_pos (by norm_num) hs0) (by positivity)]
    dsimp [t]
    nlinarith [hsSq]
  have hsqrtpi0 : 0 < Real.sqrt (2 * Real.pi) := by positivity
  have hsqrtpi3 : Real.sqrt (2 * Real.pi) ≤ 3 := by
    have hsquare := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
    have hsnonneg := Real.sqrt_nonneg (2 * Real.pi)
    nlinarith [Real.pi_lt_four]
  have hinvsqrt : (1 / 3 : ℝ) ≤ 1 / Real.sqrt (2 * Real.pi) :=
    one_div_le_one_div_of_le hsqrtpi0 hsqrtpi3
  have hlogle : Real.log p ≤ p := by
    exact (Real.log_le_sub_one_of_pos hp0).trans (by linarith)
  have hsExp : s ≤ Real.exp (31 * p / 32) := by
    have hsEq : s = Real.exp (Real.log p / 2) := by
      dsimp [s]
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hp0]
      congr 1
      ring
    rw [hsEq]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hexpdom : s * Real.exp (-p) ≤ Real.exp (-p / 32) := by
    calc
      s * Real.exp (-p) ≤ Real.exp (31 * p / 32) * Real.exp (-p) :=
        mul_le_mul_of_nonneg_right hsExp (Real.exp_pos _).le
      _ = Real.exp (-p / 32) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hexpdiv : Real.exp (-p) ≤ Real.exp (-p / 32) / s :=
    (le_div_iff₀ hs0).2 (by simpa [mul_comm] using hexpdom)
  have hdensity : HDP.Chapter2.stdGaussianDensity t =
      Real.exp (-p / 32) * (1 / Real.sqrt (2 * Real.pi)) := by
    rw [HDP.Chapter2.stdGaussianDensity, htSq]
    congr 2
    ring
  calc
    (1 / 100 : ℝ) * Real.exp (-p) ≤ (4 / 51 : ℝ) * Real.exp (-p) := by
      exact mul_le_mul_of_nonneg_right (by norm_num) (Real.exp_pos _).le
    _ ≤ (4 / 51 : ℝ) * (Real.exp (-p / 32) / s) :=
      mul_le_mul_of_nonneg_left hexpdiv (by norm_num)
    _ = (4 / (17 * s)) * (Real.exp (-p / 32) * (1 / 3)) := by
      field_simp
      ring
    _ ≤ (4 / (17 * s)) *
        (Real.exp (-p / 32) * (1 / Real.sqrt (2 * Real.pi))) := by
      gcongr
    _ = (4 / (17 * s)) * HDP.Chapter2.stdGaussianDensity t := by
      rw [hdensity]
    _ ≤ (t / (t ^ 2 + 1)) * HDP.Chapter2.stdGaussianDensity t :=
      mul_le_mul_of_nonneg_right hratio
        (HDP.Chapter2.stdGaussianDensity_pos t).le
    _ ≤ (gaussianReal 0 1).real (Set.Ici t) :=
      HDP.Chapter2.gaussian_tail_lower_measure ht0
    _ = (gaussianReal 0 1).real
        (Set.Ici (Real.sqrt p / 4)) := by rfl

/-- A concrete absolute constant for Exercise 3.6.

**Book Exercise 3.6.** -/
noncomputable def gaussianLpLowerConstant : ℝ :=
  1 / (643200 * Real.exp 1)

/-- Shows that `gaussianLpLowerConstant` is positive.

**Lean implementation helper.** -/
lemma gaussianLpLowerConstant_pos : 0 < gaussianLpLowerConstant := by
  unfold gaussianLpLowerConstant
  positivity

set_option maxHeartbeats 800000 in
-- The proof expands a finite independent sum through variance, a
-- Paley--Zygmund estimate, and two real-power normalizations.
/-- A Gaussian variable has an `Lᵖ` norm bounded below by a constant times its standard deviation and `sqrt p`.

**Lean implementation helper.** -/
private theorem gaussian_lp_lower_of_exp_scale {n : ℕ}
    [IsProbabilityMeasure μ] {X : Fin (n + 2) → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i))
    (hg : ∀ i, HasLaw (X i) (gaussianReal 0 1) μ)
    (hindep : iIndepFun X μ) {p : ℝ} (hp : 1 ≤ p)
    (hscale : (1 / 2 : ℝ) ≤ ((n : ℝ) + 2) * Real.exp (-p)) :
    gaussianLpLowerConstant * Real.sqrt p *
        (((n : ℝ) + 2) ^ (1 / p)) ≤
      ∫ ω, HDP.Chapter1.lpNorm p (fun i => X i ω) ∂μ := by
  classical
  let N : ℝ := (n : ℝ) + 2
  let t : ℝ := Real.sqrt p / 4
  let q : ℝ := (gaussianReal 0 1).real (Set.Ici t)
  let I : Fin (n + 2) → Ω → ℝ := fun i =>
    (fun x => if t ≤ x then 1 else 0) ∘ X i
  let C : Ω → ℝ := fun ω => ∑ i, I i ω
  let lam : ℝ := N * q
  have hp0 : 0 < p := one_pos.trans_le hp
  have hN0 : 0 < N := by dsimp [N]; positivity
  have ht0 : 0 < t := by dsimp [t]; positivity
  have hq0 : 0 ≤ q := measureReal_nonneg
  have hq1 : q ≤ 1 := by dsimp [q]; simp
  have hqlower : (1 / 100 : ℝ) * Real.exp (-p) ≤ q := by
    simpa [q, t] using gaussian_tail_exp_lower hp
  have hlam0 : (1 / 200 : ℝ) ≤ lam := by
    dsimp [lam]
    calc
      (1 / 200 : ℝ) ≤ N * ((1 / 100 : ℝ) * Real.exp (-p)) := by
        dsimp [N] at hscale ⊢
        nlinarith
      _ ≤ N * q := mul_le_mul_of_nonneg_left hqlower hN0.le
  have hlamPos : 0 < lam := (by norm_num : (0 : ℝ) < 1 / 200).trans_le hlam0
  have hIm : ∀ i, Measurable (I i) := by
    intro i
    exact (measurable_const.indicator measurableSet_Ici).comp (hXm i)
  have hIindep : iIndepFun I μ := by
    exact hindep.comp (fun _ x => if t ≤ x then (1 : ℝ) else 0)
      (fun _ => measurable_const.indicator measurableSet_Ici)
  have hIeq : ∀ i, I i = {ω | t ≤ X i ω}.indicator (fun _ => (1 : ℝ)) := by
    intro i
    funext ω
    simp [I, Function.comp_def, Set.indicator]
  have hImem : ∀ i, MemLp (I i) 2 μ := by
    intro i
    rw [hIeq i]
    exact memLp_indicator_const 2
      (measurableSet_le measurable_const (hXm i)) 1
      (Or.inr (measure_ne_top μ _))
  have hImean : ∀ i, ∫ ω, I i ω ∂μ = q := by
    intro i
    rw [hIeq i, HDP.Chapter1.expectation_indicator _
      (measurableSet_le measurable_const (hXm i))]
    exact (hg i).measureReal_eq measurableSet_Ici
  have hIsq : ∀ i, ∫ ω, I i ω ^ 2 ∂μ = q := by
    intro i
    rw [hIeq i]
    calc
      (∫ ω, ({ω | t ≤ X i ω}.indicator (fun _ => (1 : ℝ)) ω) ^ 2 ∂μ) =
          ∫ ω, {ω | t ≤ X i ω}.indicator (fun _ => (1 : ℝ)) ω ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with ω
        by_cases hω : t ≤ X i ω <;> simp [Set.indicator, hω]
      _ = q := by
        rw [HDP.Chapter1.expectation_indicator _
          (measurableSet_le measurable_const (hXm i))]
        exact (hg i).measureReal_eq measurableSet_Ici
  have hIvar : ∀ i, Var[I i; μ] ≤ q := by
    intro i
    have h := variance_eq_sub (hImem i)
    have h' : Var[I i; μ] = q - q ^ 2 := by
      simpa only [Pi.pow_apply, hIsq i, hImean i] using h
    rw [h']
    nlinarith [sq_nonneg q]
  have hCfun : C = ∑ i, I i := by
    funext ω
    simp [C]
  have hCm : Measurable C := by
    exact Finset.measurable_sum _ fun i _ => hIm i
  have hC0 : ∀ ω, 0 ≤ C ω := by
    intro ω
    apply Finset.sum_nonneg
    intro i hi
    by_cases h : t ≤ X i ω <;> simp [I, Function.comp_def, h]
  have hCmem : MemLp C 2 μ := by
    rw [hCfun]
    exact memLp_finsetSum' Finset.univ fun i _ => hImem i
  have hCmean : (∫ ω, C ω ∂μ) = lam := by
    change (∫ ω, ∑ i, I i ω ∂μ) = lam
    rw [integral_finsetSum]
    · simp [hImean, lam, N]
    · intro i hi
      exact (hImem i).integrable (by norm_num)
  have hCvar : Var[C; μ] ≤ lam := by
    have hvarEq : Var[C; μ] = ∑ i, Var[I i; μ] := by
      rw [hCfun]
      exact IndepFun.variance_sum (fun i _ => hImem i)
        (fun i _ j _ hij => hIindep.indepFun hij)
    rw [hvarEq]
    calc
      (∑ i, Var[I i; μ]) ≤ ∑ _i : Fin (n + 2), q :=
        Finset.sum_le_sum fun i _ => hIvar i
      _ = lam := by simp [lam, N]
  have hCsecond : (∫ ω, C ω ^ 2 ∂μ) ≤ lam ^ 2 + lam := by
    have hvarEq : Var[C; μ] = (∫ ω, C ω ^ 2 ∂μ) - lam ^ 2 := by
      simpa only [Pi.pow_apply, hCmean] using variance_eq_sub hCmem
    linarith
  have hCsecondPos : 0 < ∫ ω, C ω ^ 2 ∂μ := by
    have hvar0 := variance_nonneg C μ
    have hvarEq : Var[C; μ] = (∫ ω, C ω ^ 2 ∂μ) - lam ^ 2 := by
      simpa only [Pi.pow_apply, hCmean] using variance_eq_sub hCmem
    rw [hvarEq] at hvar0
    nlinarith [sq_pos_of_pos hlamPos]
  let eps : Set.Icc (0 : ℝ) 1 := ⟨1 / 2, by norm_num, by norm_num⟩
  have hPZ := HDP.Chapter1.exercise_1_16 hCm
    (Filter.Eventually.of_forall hC0) hCmem eps
  have hprob : (1 / 804 : ℝ) ≤
      μ.real {ω | lam / 2 < C ω} := by
    have hPZ' : lam ^ 2 / (4 * (∫ ω, C ω ^ 2 ∂μ)) ≤
        μ.real {ω | lam / 2 < C ω} := by
      dsimp [eps] at hPZ
      rw [hCmean] at hPZ
      convert hPZ using 1 <;> ring_nf
    have hden : 4 * (∫ ω, C ω ^ 2 ∂μ) ≤ 804 * lam ^ 2 := by
      calc
        4 * (∫ ω, C ω ^ 2 ∂μ) ≤ 4 * (lam ^ 2 + lam) :=
          mul_le_mul_of_nonneg_left hCsecond (by norm_num)
        _ ≤ 804 * lam ^ 2 := by nlinarith [hlam0]
    calc
      (1 / 804 : ℝ) ≤ lam ^ 2 / (4 * (∫ ω, C ω ^ 2 ∂μ)) := by
        rw [le_div_iff₀ (mul_pos (by norm_num) hCsecondPos)]
        nlinarith [hden]
      _ ≤ μ.real {ω | lam / 2 < C ω} := hPZ'
  have hCroot : N ^ (1 / p) / (200 * Real.exp 1) ≤
      (lam / 2) ^ (1 / p) := by
    have hbase : N * Real.exp (-p) / 200 ≤ lam / 2 := by
      dsimp [lam]
      calc
        N * Real.exp (-p) / 200 = N * ((1 / 100 : ℝ) * Real.exp (-p)) / 2 := by ring
        _ ≤ N * q / 2 := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hqlower hN0.le) (by norm_num)
    have hpow := Real.rpow_le_rpow (by positivity) hbase (by positivity : 0 ≤ 1 / p)
    have hcPow : (1 / 200 : ℝ) ≤ (1 / 200 : ℝ) ^ (1 / p) := by
      have hinv : 1 / p ≤ 1 := (div_le_one hp0).2 hp
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_ge (by norm_num : (0 : ℝ) < 1 / 200)
          (by norm_num) hinv
    have hexpPow : Real.exp (-p) ^ (1 / p) = 1 / Real.exp 1 := by
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      have hinv : -p * (1 / p) = -1 := by field_simp
      rw [hinv, Real.exp_neg]
      simp [one_div]
    calc
      N ^ (1 / p) / (200 * Real.exp 1) =
          N ^ (1 / p) * (1 / Real.exp 1) * (1 / 200 : ℝ) := by ring
      _ ≤ N ^ (1 / p) * (1 / Real.exp 1) *
          ((1 / 200 : ℝ) ^ (1 / p)) :=
        mul_le_mul_of_nonneg_left hcPow (by positivity)
      _ = (N * Real.exp (-p) / 200) ^ (1 / p) := by
        rw [show N * Real.exp (-p) / 200 =
          (N * Real.exp (-p)) * (1 / 200 : ℝ) by ring,
          Real.mul_rpow (by positivity) (by positivity),
          Real.mul_rpow (by positivity) (by positivity), hexpPow]
      _ ≤ (lam / 2) ^ (1 / p) := hpow
  have hZmem : MemLp (finiteLpRadius p X) (ENNReal.ofReal p) μ := by
    have hsub : ∀ i, HDP.SubGaussian (X i) μ := fun i => by
      refine ⟨2, by norm_num, ?_⟩
      rw [HDP.psi2MGF_eq_of_hasLaw_standardGaussian (hg i)]
      unfold HDP.psi2MGF
      calc
        (∫⁻ x, ENNReal.ofReal (Real.exp (x ^ 2 / (2 : ℝ) ^ 2))
            ∂gaussianReal 0 1) ≤
            ∫⁻ x, ENNReal.ofReal (Real.exp ((3 / 8 : ℝ) * x ^ 2))
              ∂gaussianReal 0 1 := by
          refine lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_
          apply Real.exp_le_exp.mpr
          nlinarith [sq_nonneg x]
        _ = 2 := HDP.Chapter2.lintegral_exp_three_eighths_sq_standardGaussian
    exact finiteLpRadius_memLp hp hXm hsub
  have hZint : Integrable (finiteLpRadius p X) μ :=
    hZmem.integrable (by simpa using ENNReal.ofReal_le_ofReal hp)
  let A : Set Ω := {ω | lam / 2 < C ω}
  have hA : MeasurableSet A := measurableSet_lt measurable_const hCm
  let r : ℝ := t * (lam / 2) ^ (1 / p)
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hpoint : ∀ ω, A.indicator (fun _ => r) ω ≤ finiteLpRadius p X ω := by
    intro ω
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω]
      have hsum : C ω * t ^ p ≤ ∑ i, |X i ω| ^ p := by
        dsimp [C]
        rw [Finset.sum_mul]
        apply Finset.sum_le_sum
        intro i hi
        by_cases hiX : t ≤ X i ω
        · simp only [I, Function.comp_def, if_pos hiX, one_mul]
          exact Real.rpow_le_rpow ht0.le (hiX.trans (le_abs_self _)) hp0.le
        · simp only [I, Function.comp_def, if_neg hiX, zero_mul]
          exact Real.rpow_nonneg (abs_nonneg (X i ω)) p
      have hroot : t * (C ω) ^ (1 / p) ≤ finiteLpRadius p X ω := by
        rw [finiteLpRadius, HDP.Chapter1.lpNorm_eq_sum hp0]
        calc
          t * (C ω) ^ (1 / p) = (C ω * t ^ p) ^ (1 / p) := by
            rw [Real.mul_rpow (hC0 ω) (Real.rpow_nonneg ht0.le p),
              ← Real.rpow_mul ht0.le]
            have hinv : p * (1 / p) = 1 := by field_simp
            rw [hinv, Real.rpow_one]
            ring
          _ ≤ (∑ i, |X i ω| ^ p) ^ (1 / p) :=
            Real.rpow_le_rpow (mul_nonneg (hC0 ω) (Real.rpow_nonneg ht0.le p))
              hsum (by positivity)
      have hcount : (lam / 2) ^ (1 / p) ≤ (C ω) ^ (1 / p) :=
        Real.rpow_le_rpow (by positivity) hω.le (by positivity)
      exact (mul_le_mul_of_nonneg_left hcount ht0.le).trans hroot
    · rw [Set.indicator_of_notMem hω]
      exact finiteLpRadius_nonneg hp0 X ω
  have hIndicatorInt : Integrable (A.indicator fun _ => r) μ :=
    (integrable_const r).indicator hA
  have hintegral : r * μ.real A ≤ ∫ ω, finiteLpRadius p X ω ∂μ := by
    calc
      r * μ.real A = ∫ ω, A.indicator (fun _ => r) ω ∂μ := by
        rw [integral_indicator hA]
        simp [mul_comm]
      _ ≤ ∫ ω, finiteLpRadius p X ω ∂μ :=
        integral_mono hIndicatorInt hZint hpoint
  calc
    gaussianLpLowerConstant * Real.sqrt p * (N ^ (1 / p)) =
        (t * (N ^ (1 / p) / (200 * Real.exp 1))) * (1 / 804) := by
      dsimp [gaussianLpLowerConstant, t]
      ring
    _ ≤ (t * (lam / 2) ^ (1 / p)) * (1 / 804) := by
      gcongr
    _ ≤ r * μ.real A := by
      dsimp [r]
      exact mul_le_mul_of_nonneg_left hprob (by positivity)
    _ ≤ ∫ ω, finiteLpRadius p X ω ∂μ := hintegral
    _ = ∫ ω, HDP.Chapter1.lpNorm p (fun i => X i ω) ∂μ := rfl

/-- The range `1 ≤ p ≤ log N`, with `N = n + 2`.
The displayed concrete constant is independent of both dimension and `p`.

**Book Exercise 3.6.** -/
theorem exercise_3_6_small {n : ℕ} [IsProbabilityMeasure μ]
    {X : Fin (n + 2) → Ω → ℝ} (hXm : ∀ i, Measurable (X i))
    (hg : ∀ i, HasLaw (X i) (gaussianReal 0 1) μ)
    (hindep : iIndepFun X μ) {p : ℝ} (hp : 1 ≤ p)
    (hplog : p ≤ Real.log ((n : ℝ) + 2)) :
    gaussianLpLowerConstant * Real.sqrt p *
        (((n : ℝ) + 2) ^ (1 / p)) ≤
      ∫ ω, HDP.Chapter1.lpNorm p (fun i => X i ω) ∂μ := by
  have hN0 : 0 < (n : ℝ) + 2 := by positivity
  have hexp : Real.exp p ≤ (n : ℝ) + 2 := by
    calc
      Real.exp p ≤ Real.exp (Real.log ((n : ℝ) + 2)) :=
        Real.exp_le_exp.mpr hplog
      _ = (n : ℝ) + 2 := Real.exp_log hN0
  have hprod : 1 ≤ ((n : ℝ) + 2) * Real.exp (-p) := by
    rw [Real.exp_neg, le_mul_inv_iff₀ (Real.exp_pos p)]
    simpa using hexp
  exact gaussian_lp_lower_of_exp_scale hXm hg hindep hp (by linarith)

/-- Any random variable with the standard Gaussian law is subgaussian.

**Lean implementation helper.** -/
private lemma subGaussian_of_hasLaw_standardGaussian [IsProbabilityMeasure μ]
    {Y : Ω → ℝ} (hY : HasLaw Y (gaussianReal 0 1) μ) :
    HDP.SubGaussian Y μ := by
  refine ⟨2, by norm_num, ?_⟩
  rw [HDP.psi2MGF_eq_of_hasLaw_standardGaussian hY]
  unfold HDP.psi2MGF
  calc
    (∫⁻ x, ENNReal.ofReal (Real.exp (x ^ 2 / (2 : ℝ) ^ 2))
        ∂gaussianReal 0 1) ≤
        ∫⁻ x, ENNReal.ofReal (Real.exp ((3 / 8 : ℝ) * x ^ 2))
          ∂gaussianReal 0 1 := by
      refine lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg x]
    _ = 2 := HDP.Chapter2.lintegral_exp_three_eighths_sq_standardGaussian

/-- Bounds `maxAbsCoordinates` above by `finiteLpRadius`.

**Lean implementation helper.** -/
private lemma maxAbsCoordinates_le_finiteLpRadius {n : ℕ} {p : ℝ}
    (hp : 1 ≤ p) (X : Fin (n + 2) → Ω → ℝ) (ω : Ω) :
    maxAbsCoordinates X ω ≤ finiteLpRadius p X ω := by
  apply Finset.sup'_le
  intro i hi
  exact HDP.Chapter1.abs_apply_le_lpNorm hp (fun j => X j ω) i

/-- The safe `p = ∞` branch.

**Book Exercise 3.6.** -/
theorem exercise_3_6_top {n : ℕ} [IsProbabilityMeasure μ]
    {X : Fin (n + 2) → Ω → ℝ} (hXm : ∀ i, Measurable (X i))
    (hg : ∀ i, HasLaw (X i) (gaussianReal 0 1) μ)
    (hindep : iIndepFun X μ) :
    gaussianLpLowerConstant * Real.sqrt (Real.log ((n : ℝ) + 2)) ≤
      ∫ ω, maxAbsCoordinates X ω ∂μ := by
  let N : ℝ := (n : ℝ) + 2
  let s : ℝ := Real.log (2 * N)
  have hN0 : 0 < N := by dsimp [N]; positivity
  have htwoN0 : 0 < 2 * N := mul_pos (by norm_num) hN0
  have hs1 : 1 ≤ s := by
    apply (Real.le_log_iff_exp_le htwoN0).2
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    exact Real.exp_one_lt_three.le.trans (by dsimp [N]; linarith)
  have hlogs : Real.log N ≤ s := by
    dsimp [s]
    exact (Real.log_le_log_iff hN0 htwoN0).2 (by nlinarith [hN0])
  have hscaleEq : N * Real.exp (-s) = 1 / 2 := by
    dsimp [s]
    rw [Real.exp_neg, Real.exp_log htwoN0]
    field_simp [hN0.ne']
  have hsub : ∀ i, HDP.SubGaussian (X i) μ := fun i =>
    subGaussian_of_hasLaw_standardGaussian (hg i)
  have hpsi : ∀ i, HDP.psi2Norm (X i) μ ≤ 2 := by
    intro i
    rw [HDP.psi2Norm_standardGaussian (hg i)]
    have hsqrt := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8 / 3)
    have hsqrt0 := Real.sqrt_nonneg (8 / 3 : ℝ)
    nlinarith
  have hMsub : HDP.SubGaussian (maxAbsCoordinates X) μ := by
    change HDP.SubGaussian
      (fun ω => Finset.univ.sup' Finset.univ_nonempty fun i => |X i ω|) μ
    exact (HDP.psi2Norm_max_abs_le hXm hsub (by norm_num) hpsi).1
  have hMm := maxAbsCoordinates_measurable hXm
  have hMint : Integrable (maxAbsCoordinates X) μ :=
    (hMsub.memLp hMm.aemeasurable (le_refl (1 : ℝ))).integrable (by norm_num)
  have hSmem := finiteLpRadius_memLp hs1 hXm hsub
  have hSint : Integrable (finiteLpRadius s X) μ :=
    hSmem.integrable (by simpa using ENNReal.ofReal_le_ofReal hs1)
  have hscale : (1 / 2 : ℝ) ≤ ((n : ℝ) + 2) * Real.exp (-s) := by
    change (1 / 2 : ℝ) ≤ N * Real.exp (-s)
    rw [hscaleEq]
  have hlower : gaussianLpLowerConstant * Real.sqrt s * (N ^ (1 / s)) ≤
      ∫ ω, finiteLpRadius s X ω ∂μ := by
    simpa [N, finiteLpRadius] using gaussian_lp_lower_of_exp_scale hXm hg hindep hs1
      hscale
  have hupper : (∫ ω, finiteLpRadius s X ω ∂μ) ≤
      (N ^ (1 / s)) * ∫ ω, maxAbsCoordinates X ω ∂μ := by
    calc
      (∫ ω, finiteLpRadius s X ω ∂μ) ≤
          ∫ ω, (N ^ (1 / s)) * maxAbsCoordinates X ω ∂μ := by
        apply integral_mono hSint (hMint.const_mul _)
        intro ω
        simpa [N] using finiteLpRadius_le_max hs1 X ω
      _ = (N ^ (1 / s)) * ∫ ω, maxAbsCoordinates X ω ∂μ := by
        rw [integral_const_mul]
  have hpowPos : 0 < N ^ (1 / s) := Real.rpow_pos_of_pos hN0 _
  have hcancel : gaussianLpLowerConstant * Real.sqrt s ≤
      ∫ ω, maxAbsCoordinates X ω ∂μ := by
    apply le_of_mul_le_mul_left _ hpowPos
    calc
      (N ^ (1 / s)) * (gaussianLpLowerConstant * Real.sqrt s) =
          gaussianLpLowerConstant * Real.sqrt s * (N ^ (1 / s)) := by ring
      _ ≤ ∫ ω, finiteLpRadius s X ω ∂μ := hlower
      _ ≤ (N ^ (1 / s)) * ∫ ω, maxAbsCoordinates X ω ∂μ := hupper
  calc
    gaussianLpLowerConstant * Real.sqrt (Real.log ((n : ℝ) + 2)) =
        gaussianLpLowerConstant * Real.sqrt (Real.log N) := by rfl
    _ ≤ gaussianLpLowerConstant * Real.sqrt s :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hlogs)
        gaussianLpLowerConstant_pos.le
    _ ≤ ∫ ω, maxAbsCoordinates X ω ∂μ := hcancel

/-- The finite `p ≥ log N` branch.

**Book Exercise 3.6.** -/
theorem exercise_3_6_large {n : ℕ} [IsProbabilityMeasure μ]
    {X : Fin (n + 2) → Ω → ℝ} (hXm : ∀ i, Measurable (X i))
    (hg : ∀ i, HasLaw (X i) (gaussianReal 0 1) μ)
    (hindep : iIndepFun X μ) {p : ℝ} (hp : 1 ≤ p)
    (_hlogp : Real.log ((n : ℝ) + 2) ≤ p) :
    gaussianLpLowerConstant * Real.sqrt (Real.log ((n : ℝ) + 2)) ≤
      ∫ ω, HDP.Chapter1.lpNorm p (fun i => X i ω) ∂μ := by
  have hsub : ∀ i, HDP.SubGaussian (X i) μ := fun i =>
    subGaussian_of_hasLaw_standardGaussian (hg i)
  have hMsub : HDP.SubGaussian (maxAbsCoordinates X) μ := by
    have hpsi : ∀ i, HDP.psi2Norm (X i) μ ≤ 2 := by
      intro i
      rw [HDP.psi2Norm_standardGaussian (hg i)]
      have hsqrt := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8 / 3)
      have hsqrt0 := Real.sqrt_nonneg (8 / 3 : ℝ)
      nlinarith
    change HDP.SubGaussian
      (fun ω => Finset.univ.sup' Finset.univ_nonempty fun i => |X i ω|) μ
    exact (HDP.psi2Norm_max_abs_le hXm hsub (by norm_num) hpsi).1
  have hMm := maxAbsCoordinates_measurable hXm
  have hMint : Integrable (maxAbsCoordinates X) μ :=
    (hMsub.memLp hMm.aemeasurable (le_refl (1 : ℝ))).integrable (by norm_num)
  have hPmem := finiteLpRadius_memLp hp hXm hsub
  have hPint : Integrable (finiteLpRadius p X) μ :=
    hPmem.integrable (by simpa using ENNReal.ofReal_le_ofReal hp)
  calc
    gaussianLpLowerConstant * Real.sqrt (Real.log ((n : ℝ) + 2)) ≤
        ∫ ω, maxAbsCoordinates X ω ∂μ := exercise_3_6_top hXm hg hindep
    _ ≤ ∫ ω, finiteLpRadius p X ω ∂μ :=
      integral_mono hMint hPint fun ω => maxAbsCoordinates_le_finiteLpRadius hp X ω
    _ = ∫ ω, HDP.Chapter1.lpNorm p (fun i => X i ω) ∂μ := rfl

/-- Matching expected Gaussian `ell^p` norm estimates.

**Book Exercise 3.6.** -/
theorem exercise_3_6 {n : ℕ} [IsProbabilityMeasure μ]
    {X : Fin (n + 2) → Ω → ℝ} (hXm : ∀ i, Measurable (X i))
    (hg : ∀ i, HasLaw (X i) (gaussianReal 0 1) μ)
    (hindep : iIndepFun X μ) {p : ℝ} (hp : 1 ≤ p) :
    (p ≤ Real.log ((n : ℝ) + 2) →
      gaussianLpLowerConstant * Real.sqrt p *
          (((n : ℝ) + 2) ^ (1 / p)) ≤
        ∫ ω, HDP.Chapter1.lpNorm p (fun i => X i ω) ∂μ) ∧
    (Real.log ((n : ℝ) + 2) ≤ p →
      gaussianLpLowerConstant * Real.sqrt (Real.log ((n : ℝ) + 2)) ≤
        ∫ ω, HDP.Chapter1.lpNorm p (fun i => X i ω) ∂μ) ∧
    gaussianLpLowerConstant * Real.sqrt (Real.log ((n : ℝ) + 2)) ≤
      ∫ ω, maxAbsCoordinates X ω ∂μ := by
  exact ⟨fun hplog => exercise_3_6_small hXm hg hindep hp hplog,
    fun hlogp => exercise_3_6_large hXm hg hindep hp hlogp,
    exercise_3_6_top hXm hg hindep⟩

/-! ## Exercise 3.7: small-ball probability -/

/-- For `b > 0`, the `radialGaussian` integrand `x ↦ exp (-b * ‖x‖²)` is integrable with respect to Lebesgue volume.

**Lean implementation helper.** -/
private lemma integrable_radialGaussian
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : E => Real.exp (-b * ‖x‖ ^ 2)) volume := by
  have hc := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := E) (b := (b : ℂ)) (by simpa using hb) 0 0
  have hn := hc.norm
  convert hn using 1
  funext x
  rw [Complex.norm_exp]
  congr 2
  norm_cast
  simp

/-- The elementary Gaussian-integral proof of the Euclidean-ball volume
bound used in Exercise 3.7.

**Book Exercise 3.7.** -/
private lemma standardEuclideanBall_volume_real_le {n : ℕ} (hn : 0 < n)
    {ε : ℝ} (hε : 0 < ε) :
    volume.real (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n))
      (ε * Real.sqrt n)) ≤
      (Real.sqrt (2 * Real.pi * Real.exp 1) * ε) ^ n := by
  let b : ℝ := 1 / (2 * ε ^ 2)
  let B : Set (EuclideanSpace ℝ (Fin n)) :=
    Metric.closedBall 0 (ε * Real.sqrt n)
  let f : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun x => Real.exp (-b * ‖x‖ ^ 2)
  let q : ℝ := Real.exp (-(n : ℝ) / 2)
  have hb : 0 < b := by dsimp [b]; positivity
  have hfInt : Integrable f volume := by
    simpa [f] using integrable_radialGaussian
      (E := EuclideanSpace ℝ (Fin n)) hb
  have hBfin : volume B ≠ ∞ := measure_closedBall_lt_top.ne
  have hconstInt : IntegrableOn
      (fun _ : EuclideanSpace ℝ (Fin n) => q) B volume :=
    integrableOn_const hBfin
  have hpoint : ∀ x ∈ B, q ≤ f x := by
    intro x hx
    apply Real.exp_le_exp.mpr
    have hnorm : ‖x‖ ≤ ε * Real.sqrt n := by
      simpa [B, Metric.mem_closedBall, dist_zero_right] using hx
    have hsq : ‖x‖ ^ 2 ≤ (ε * Real.sqrt n) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg x) (by positivity)).2 hnorm
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hsqrt : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt hnR.le
    dsimp [q, f, b]
    rw [mul_pow, hsqrt] at hsq
    have hdiv : ‖x‖ ^ 2 / (2 * ε ^ 2) ≤ (n : ℝ) / 2 := by
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * ε ^ 2)
        (by norm_num : (0 : ℝ) < 2)]
      nlinarith [hsq]
    have heq : (1 / (2 * ε ^ 2)) * ‖x‖ ^ 2 =
        ‖x‖ ^ 2 / (2 * ε ^ 2) := by ring
    calc
      -(n : ℝ) / 2 ≤ -(‖x‖ ^ 2 / (2 * ε ^ 2)) := by
        simpa only [neg_div] using neg_le_neg hdiv
      _ = -(1 / (2 * ε ^ 2)) * ‖x‖ ^ 2 := by rw [← heq]; ring
  have hlow : q * volume.real B ≤ ∫ x in B, f x := by
    calc
      q * volume.real B = ∫ _x in B, q := by
        rw [integral_const]
        simp [mul_comm]
      _ ≤ ∫ x in B, f x := setIntegral_mono_on hconstInt
        hfInt.integrableOn measurableSet_closedBall hpoint
  have hupp : (∫ x in B, f x) ≤ ∫ x, f x :=
    setIntegral_le_integral hfInt
      (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)
  have hint : (∫ x, f x) = (Real.pi / b) ^ ((n : ℝ) / 2) := by
    simpa [f, show Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n by simp]
      using GaussianFourier.integral_rexp_neg_mul_sq_norm
        (V := EuclideanSpace ℝ (Fin n)) hb
  have hmain : q * volume.real B ≤ (Real.pi / b) ^ ((n : ℝ) / 2) :=
    hlow.trans (hupp.trans_eq hint)
  have hsolve : volume.real B ≤ Real.exp ((n : ℝ) / 2) *
      (Real.pi / b) ^ ((n : ℝ) / 2) := by
    calc
      volume.real B = Real.exp ((n : ℝ) / 2) * (q * volume.real B) := by
        dsimp [q]
        rw [← mul_assoc, ← Real.exp_add]
        ring_nf
        simp
      _ ≤ Real.exp ((n : ℝ) / 2) *
          (Real.pi / b) ^ ((n : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left hmain (Real.exp_pos _).le
  change volume.real B ≤ _
  exact hsolve.trans_eq (by
    dsimp [b]
    let d : ℝ := n
    let Q : ℝ := 2 * Real.pi * Real.exp 1
    have hQ : 0 < Q := by dsimp [Q]; positivity
    have hbase : 0 < Real.sqrt Q * ε :=
      mul_pos (Real.sqrt_pos.2 hQ) hε
    have hinside : Real.exp 1 * (Real.pi / (1 / (2 * ε ^ 2))) =
        Q * ε ^ 2 := by
      dsimp [Q]
      field_simp [hε.ne']
    calc
      Real.exp ((n : ℝ) / 2) *
          (Real.pi / (1 / (2 * ε ^ 2))) ^ ((n : ℝ) / 2) =
          (Real.exp 1) ^ (d / 2) *
            (Real.pi / (1 / (2 * ε ^ 2))) ^ (d / 2) := by
              rw [Real.exp_one_rpow]
      _ = (Real.exp 1 * (Real.pi / (1 / (2 * ε ^ 2)))) ^ (d / 2) := by
        rw [Real.mul_rpow (Real.exp_pos 1).le (by positivity :
          0 ≤ Real.pi / (1 / (2 * ε ^ 2)))]
      _ = (Q * ε ^ 2) ^ (d / 2) := by rw [hinside]
      _ = ((Real.sqrt Q * ε) ^ (2 : ℝ)) ^ (d / 2) := by
        congr 1
        rw [Real.rpow_two, mul_pow, Real.sq_sqrt hQ.le]
      _ = (Real.sqrt Q * ε) ^ (2 * (d / 2)) :=
        (Real.rpow_mul hbase.le 2 (d / 2)).symm
      _ = (Real.sqrt Q * ε) ^ d := by congr 1; ring
      _ = (Real.sqrt Q * ε) ^ n := Real.rpow_natCast _ n
      _ = (Real.sqrt (2 * Real.pi * Real.exp 1) * ε) ^ n := by rfl)

/-- The volume of the Euclidean unit ball satisfies the stated dimension-dependent upper bound.

**Lean implementation helper.** -/
private lemma standardEuclideanBall_volume_le {n : ℕ} (hn : 0 < n)
    {ε : ℝ} (hε : 0 ≤ ε) (a : EuclideanSpace ℝ (Fin n)) :
    volume (Metric.closedBall a (ε * Real.sqrt n)) ≤
      (ENNReal.ofReal (Real.sqrt (2 * Real.pi * Real.exp 1) * ε)) ^ n := by
  have hr : 0 ≤ ε * Real.sqrt n :=
    mul_nonneg hε (Real.sqrt_nonneg _)
  have hcenter : volume (Metric.closedBall a (ε * Real.sqrt n)) =
      volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n))
        (ε * Real.sqrt n)) := by
    rw [Measure.addHaar_closedBall volume a hr,
      Measure.addHaar_closedBall volume 0 hr]
  rw [hcenter]
  by_cases he : ε = 0
  · subst ε
    rw [Measure.addHaar_closedBall volume 0 (by simp)]
    simp [zero_pow hn.ne']
  · have hepos : 0 < ε := lt_of_le_of_ne hε (Ne.symm he)
    have hreal := standardEuclideanBall_volume_real_le hn hepos
    have hfin : volume (Metric.closedBall
        (0 : EuclideanSpace ℝ (Fin n)) (ε * Real.sqrt n)) ≠ ∞ :=
      measure_closedBall_lt_top.ne
    rw [← ENNReal.ofReal_toReal hfin]
    rw [← ENNReal.ofReal_pow
      (mul_nonneg (Real.sqrt_nonneg _) hε)]
    exact ENNReal.ofReal_le_ofReal hreal

/-- Coordinatewise inclusion of measurable rectangles implies monotonicity of their product outer measures.

**Lean implementation helper.** -/
private lemma outerMeasure_pi_mono {ι : Type*} [Fintype ι]
    {α : ι → Type*} {m n : ∀ i, OuterMeasure (α i)}
    (h : ∀ i, m i ≤ n i) : OuterMeasure.pi m ≤ OuterMeasure.pi n := by
  rw [OuterMeasure.le_pi]
  intro s hs
  calc
    OuterMeasure.pi m (Set.pi Set.univ s) ≤ ∏ i, m i (s i) :=
      OuterMeasure.pi_pi_le m s
    _ ≤ ∏ i, n i (s i) :=
      Finset.prod_le_prod' fun i _ => h i (s i)

/-- Coordinatewise inclusion of measurable rectangles implies monotonicity of their product measures.

**Lean implementation helper.** -/
private lemma measure_pi_mono {ι : Type*} [Fintype ι]
    {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    {μ ν : ∀ i, Measure (α i)} (h : ∀ i, μ i ≤ ν i) :
    Measure.pi μ ≤ Measure.pi ν := by
  rw [Measure.le_iff]
  intro s hs
  rw [Measure.pi, Measure.pi, toMeasure_apply _ _ hs,
    toMeasure_apply _ _ hs]
  exact outerMeasure_pi_mono
    (fun i => Measure.toOuterMeasure_le.mpr (h i)) s

/-- The volume of a coordinate box scales as the product of its side-length factors.

**Lean implementation helper.** -/
private lemma pi_smul_volume {ι : Type*} [Fintype ι] (c : ℝ≥0) :
    Measure.pi (fun _ : ι => c • (volume : Measure ℝ)) =
      c ^ Fintype.card ι • (volume : Measure (ι → ℝ)) := by
  rw [volume_pi]
  apply Measure.pi_eq
  intro s hs
  rw [Measure.smul_apply, Measure.pi_pi]
  simp only [Measure.smul_apply]
  change (↑(c ^ Fintype.card ι) : ℝ≥0∞) * (∏ i, volume (s i)) =
    ∏ i, (↑c : ℝ≥0∞) * volume (s i)
  rw [Finset.prod_mul_distrib, Finset.prod_const]
  simp

/-- Defines `vectorOfCoordinates_density`, the vector of coordinates density used in the surrounding construction.

**Lean implementation helper.** -/
private noncomputable def vectorOfCoordinates_density {n : ℕ}
    (X : Fin n → Ω → ℝ) : Ω → EuclideanSpace ℝ (Fin n) :=
  fun ω => WithLp.toLp 2 (fun i => X i ω)

/-- Bounds `jointLaw` above by `of_independent_coordinates`.

**Lean implementation helper.** -/
private lemma jointLaw_le_of_independent_coordinates {n : ℕ}
    [IsProbabilityMeasure μ] {X : Fin n → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) (hindep : iIndepFun X μ)
    {K : ℝ} (hcoordDom : ∀ i, Measure.map (X i) μ ≤
      Real.toNNReal K • (volume : Measure ℝ)) :
    Measure.map (vectorOfCoordinates_density X) μ ≤
      (Real.toNNReal K) ^ n •
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  let Y : Ω → (Fin n → ℝ) := fun ω i => X i ω
  let T : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n) :=
    fun y => WithLp.toLp 2 y
  have hYm : Measurable Y := measurable_pi_lambda _ hXm
  have hTm : Measurable T := by
    simpa [T] using (PiLp.volume_preserving_toLp (Fin n)).measurable
  have hTvol : Measure.map T (volume : Measure (Fin n → ℝ)) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    simpa [T] using (PiLp.volume_preserving_toLp (Fin n)).map_eq
  have hmapY : Measure.map Y μ = Measure.pi (fun i => Measure.map (X i) μ) := by
    simpa [Y] using
      hindep.map_fun_eq_pi_map (fun i => (hXm i).aemeasurable)
  have hpi : Measure.pi (fun i => Measure.map (X i) μ) ≤
      Measure.pi
        (fun _ : Fin n => Real.toNNReal K • (volume : Measure ℝ)) :=
    measure_pi_mono hcoordDom
  have hto := Measure.map_mono hpi hTm
  rw [pi_smul_volume, Measure.map_smul, hTvol, ← hmapY,
    Measure.map_map hTm hYm] at hto
  have heq : vectorOfCoordinates_density X = T ∘ Y := by funext ω; rfl
  rw [heq]
  simpa only [Fintype.card_fin] using hto

/-- Bounds `jointLaw` above by `of_coordinate_densities`.

**Lean implementation helper.** -/
private lemma jointLaw_le_of_coordinate_densities {n : ℕ}
    [IsProbabilityMeasure μ] {X : Ω → EuclideanSpace ℝ (Fin n)}
    (hXm : ∀ i, Measurable (fun ω => X ω i))
    (hindep : iIndepFun (fun i ω => X ω i) μ) {K : ℝ}
    (hcoordDom : ∀ i, Measure.map (fun ω => X ω i) μ ≤
      Real.toNNReal K • (volume : Measure ℝ)) :
    Measure.map X μ ≤ (Real.toNNReal K) ^ n •
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  let C : Fin n → Ω → ℝ := fun i ω => X ω i
  have hC := jointLaw_le_of_independent_coordinates hXm hindep hcoordDom
  have heq : vectorOfCoordinates_density C = X := by
    funext ω
    ext i
    rfl
  rwa [heq] at hC

/-- The measure-theoretic core of Exercise 3.7(a). For independent
coordinates whose one-dimensional densities are bounded by `K`, the joint
law is dominated by `K^n` times Lebesgue measure; `hdom` records exactly this
standard product-density conclusion.

**Book Exercise 3.7(a).** -/
theorem exercise_3_7a_density_bound {n : ℕ}
    {X : Ω → EuclideanSpace ℝ (Fin n)} (hXm : AEMeasurable X μ)
    (K : ℝ≥0) (hdom : Measure.map X μ ≤
      K ^ n • (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (a : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    μ (X ⁻¹' Metric.closedBall a r) ≤
      (K : ℝ≥0∞) ^ n * volume (Metric.closedBall a r) := by
  calc
    μ (X ⁻¹' Metric.closedBall a r) =
        Measure.map X μ (Metric.closedBall a r) :=
      (Measure.map_apply_of_aemeasurable hXm measurableSet_closedBall).symm
    _ ≤ (K ^ n •
        (volume : Measure (EuclideanSpace ℝ (Fin n))))
          (Metric.closedBall a r) := hdom _
    _ = (K : ℝ≥0∞) ^ n * volume (Metric.closedBall a r) := by
      rw [Measure.smul_apply]
      simp

/-- Independent coordinates with densities bounded
by `K` satisfy the dimension-free small-ball estimate. Both the product-law
domination and the Euclidean-ball volume estimate are proved above.

**Book Exercise 3.7.** -/
theorem exercise_3_7a {n : ℕ} [IsProbabilityMeasure μ] (hn : 0 < n)
    {X : Ω → EuclideanSpace ℝ (Fin n)}
    (hXm : ∀ i, Measurable (fun ω => X ω i))
    (hindep : iIndepFun (fun i ω => X ω i) μ)
    {K ε : ℝ} (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hcoordDom : ∀ i, Measure.map (fun ω => X ω i) μ ≤
      Real.toNNReal K • (volume : Measure ℝ))
    (a : EuclideanSpace ℝ (Fin n)) :
    μ (X ⁻¹' Metric.closedBall a (ε * Real.sqrt n)) ≤
      (ENNReal.ofReal (Real.sqrt (2 * Real.pi * Real.exp 1) * K * ε)) ^ n := by
  have hXmeas : Measurable X := by
    let Y : Ω → (Fin n → ℝ) := fun ω i => X ω i
    let T : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n) :=
      fun y => WithLp.toLp 2 y
    have hY : Measurable Y := measurable_pi_lambda _ hXm
    have hT : Measurable T := by
      simpa [T] using (PiLp.volume_preserving_toLp (Fin n)).measurable
    have heq : T ∘ Y = X := by funext ω; ext i; rfl
    rw [← heq]
    exact hT.comp hY
  have hdom := jointLaw_le_of_coordinate_densities hXm hindep hcoordDom
  calc
    μ (X ⁻¹' Metric.closedBall a (ε * Real.sqrt n)) ≤
        (Real.toNNReal K : ℝ≥0∞) ^ n *
          volume (Metric.closedBall a (ε * Real.sqrt n)) :=
      exercise_3_7a_density_bound hXmeas.aemeasurable
        (Real.toNNReal K) hdom a _
    _ ≤ (Real.toNNReal K : ℝ≥0∞) ^ n *
        (ENNReal.ofReal (Real.sqrt (2 * Real.pi * Real.exp 1) * ε)) ^ n :=
      by
        simpa [mul_comm] using
          (mul_le_mul_left (standardEuclideanBall_volume_le hn hε a)
            ((Real.toNNReal K : ℝ≥0∞) ^ n))
    _ = (ENNReal.ofReal
        (Real.sqrt (2 * Real.pi * Real.exp 1) * K * ε)) ^ n := by
      change (ENNReal.ofReal K) ^ n *
        (ENNReal.ofReal (Real.sqrt (2 * Real.pi * Real.exp 1) * ε)) ^ n = _
      rw [← mul_pow, ← ENNReal.ofReal_mul hK]
      congr 2
      ring

/-- Reciprocal Euclidean radius, with Lean's totalized inverse at zero. Under
the density hypothesis of Exercise 3.7 the zero set is null, so this agrees
almost everywhere with the usual reciprocal.

**Book Exercise 3.7.** -/
noncomputable def reciprocalNorm {n : ℕ}
    (X : Ω → EuclideanSpace ℝ (Fin n)) (ω : Ω) : ℝ :=
  ‖X ω‖⁻¹

/-- Shows that `reciprocalNorm` is nonnegative.

**Lean implementation helper.** -/
private lemma reciprocalNorm_nonneg {n : ℕ}
    (X : Ω → EuclideanSpace ℝ (Fin n)) :
    0 ≤ reciprocalNorm X := fun _ => inv_nonneg.mpr (norm_nonneg _)

/-- Identifies `div_natPow` with `rpow`.

**Lean implementation helper.** -/
private lemma div_natPow_eq_rpow {n : ℕ} {A t : ℝ} (ht : 0 < t) :
    (A / t) ^ n = A ^ n * t ^ (-(n : ℝ)) := by
  rw [div_pow, Real.rpow_neg ht.le, Real.rpow_natCast]
  rfl

/-- The one-dimensional calculus estimate behind Exercise 3.7(b).

**Book Exercise 3.7(b).** -/
private lemma smallBallMajor_integrable_integral_le {n : ℕ} (hn : 2 ≤ n)
    {A : ℝ} (hA : 0 < A) :
    IntegrableOn (fun t : ℝ => min 1 ((A / t) ^ n)) (Set.Ioi 0) ∧
      (∫ t in Set.Ioi 0, min 1 ((A / t) ^ n)) ≤ 2 * A := by
  let f : ℝ → ℝ := fun t => min 1 ((A / t) ^ n)
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hn2R : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hexp : -(n : ℝ) < -1 := by linarith
  have hfIoc : Set.EqOn f (fun _ => 1) (Set.Ioc 0 A) := by
    intro t ht
    have hratio : 1 ≤ A / t :=
      (le_div_iff₀ ht.1).2 (by simpa using ht.2)
    exact min_eq_left (one_le_pow₀ hratio)
  have hfIoi : Set.EqOn f
      (fun t => A ^ n * t ^ (-(n : ℝ))) (Set.Ioi A) := by
    intro t ht
    have ht0 : 0 < t := hA.trans ht
    have hratio0 : 0 ≤ A / t := div_nonneg hA.le ht0.le
    have hratio : A / t ≤ 1 := (div_le_one₀ ht0).2 ht.le
    dsimp [f]
    rw [min_eq_right (pow_le_one₀ hratio0 hratio), div_natPow_eq_rpow ht0]
  have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc 0 A) :=
    integrableOn_const (by
      rw [Real.volume_Ioc]
      exact ENNReal.ofReal_ne_top)
  have hfIntIoc : IntegrableOn f (Set.Ioc 0 A) :=
    hconst.congr_fun hfIoc.symm measurableSet_Ioc
  have hrpow : IntegrableOn (fun t : ℝ => t ^ (-(n : ℝ))) (Set.Ioi A) :=
    integrableOn_Ioi_rpow_of_lt hexp hA
  have htailInt : IntegrableOn
      (fun t : ℝ => A ^ n * t ^ (-(n : ℝ))) (Set.Ioi A) :=
    hrpow.const_mul _
  have hfIntIoi : IntegrableOn f (Set.Ioi A) :=
    htailInt.congr_fun hfIoi.symm measurableSet_Ioi
  have hunion : Set.Ioc (0 : ℝ) A ∪ Set.Ioi A = Set.Ioi 0 := by
    ext t
    simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro (h | h)
      · exact h.1
      · exact hA.trans h
    · intro ht
      rcases le_total t A with h | h
      · exact Or.inl ⟨ht, h⟩
      · rcases lt_or_eq_of_le h with hlt | rfl
        · exact Or.inr hlt
        · exact Or.inl ⟨ht, le_rfl⟩
  have hfInt : IntegrableOn f (Set.Ioi 0) := by
    rw [← hunion]
    exact hfIntIoc.union hfIntIoi
  refine ⟨hfInt, ?_⟩
  have hsplit : (∫ t in Set.Ioi 0, f t) =
      (∫ t in Set.Ioc 0 A, f t) + ∫ t in Set.Ioi A, f t := by
    rw [← hunion]
    exact setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      hfIntIoc hfIntIoi
  have hhead : (∫ t in Set.Ioc 0 A, f t) = A := by
    rw [setIntegral_congr_fun measurableSet_Ioc hfIoc]
    simp [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal hA.le]
  have htail : (∫ t in Set.Ioi A, f t) ≤ A := by
    rw [setIntegral_congr_fun measurableSet_Ioi hfIoi]
    rw [integral_const_mul, integral_Ioi_rpow_of_lt hexp hA]
    have hprod : A ^ n * A ^ (-(n : ℝ) + 1) = A := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hA]
      have he : (n : ℝ) + (-(n : ℝ) + 1) = 1 := by ring
      rw [he, Real.rpow_one]
    have hden : 0 < (n : ℝ) - 1 := by linarith
    calc
      A ^ n * (-A ^ (-(n : ℝ) + 1) / (-(n : ℝ) + 1)) =
          (A ^ n * A ^ (-(n : ℝ) + 1)) / ((n : ℝ) - 1) := by
            have hne : -(n : ℝ) + 1 ≠ 0 := by linarith
            field_simp [hne, hden.ne']
            ring
      _ = A / ((n : ℝ) - 1) := by rw [hprod]
      _ ≤ A := (div_le_iff₀ hden).2 (by
        have hden1 : 1 ≤ (n : ℝ) - 1 := by linarith
        nlinarith)
  rw [hsplit, hhead]
  linarith

/-- `reciprocalNorm_tail_le` bounds `μ{t < reciprocalNorm X}` by `min 1 (((sqrt (2πe) * K / sqrt n) / t) ^ n)` for every `t > 0`.

**Lean implementation helper.** -/
private lemma reciprocalNorm_tail_le [IsProbabilityMeasure μ] {n : ℕ}
    (hn : 2 ≤ n) {X : Ω → EuclideanSpace ℝ (Fin n)}
    (hXm : ∀ i, Measurable (fun ω => X ω i))
    (hindep : iIndepFun (fun i ω => X ω i) μ)
    {K : ℝ} (hK : 0 ≤ K)
    (hcoordDom : ∀ i, Measure.map (fun ω => X ω i) μ ≤
      Real.toNNReal K • (volume : Measure ℝ)) :
    ∀ t, 0 < t → μ.real {ω | t < reciprocalNorm X ω} ≤
      min 1 (((Real.sqrt (2 * Real.pi * Real.exp 1) * K /
        Real.sqrt n) / t) ^ n) := by
  intro t ht
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 hnR
  let ε : ℝ := 1 / (t * Real.sqrt n)
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hsmall := exercise_3_7a (μ := μ) hn0 hXm hindep hK hε hcoordDom
    (0 : EuclideanSpace ℝ (Fin n))
  have hradius : ε * Real.sqrt n = 1 / t := by
    dsimp [ε]
    field_simp [ht.ne', hsqrt.ne']
  rw [hradius] at hsmall
  let S : Set Ω := {ω | t < reciprocalNorm X ω}
  let B : Set Ω := X ⁻¹' Metric.closedBall
    (0 : EuclideanSpace ℝ (Fin n)) (1 / t)
  have hSB : S ⊆ B := by
    intro ω hω
    have hnorm : 0 < ‖X ω‖ := by
      by_contra hnot
      have hz : ‖X ω‖ = 0 :=
        le_antisymm (le_of_not_gt hnot) (norm_nonneg _)
      have : t < 0 := by simpa [S, reciprocalNorm, hz] using hω
      linarith
    have hlt : ‖X ω‖ < t⁻¹ := (lt_inv_comm₀ ht hnorm).mp hω
    simpa [B, Metric.mem_closedBall, dist_zero_right] using hlt.le
  have hmeasure : μ S ≤
      (ENNReal.ofReal
        (Real.sqrt (2 * Real.pi * Real.exp 1) * K * ε)) ^ n :=
    (measure_mono hSB).trans hsmall
  have hfinite : (ENNReal.ofReal
      (Real.sqrt (2 * Real.pi * Real.exp 1) * K * ε)) ^ n ≠ ∞ := by
    finiteness
  have hreal : μ.real S ≤
      (Real.sqrt (2 * Real.pi * Real.exp 1) * K * ε) ^ n := by
    have hto := ENNReal.toReal_mono hfinite hmeasure
    simpa [Measure.real, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (mul_nonneg
        (mul_nonneg (Real.sqrt_nonneg _) hK) hε)] using hto
  have heq : Real.sqrt (2 * Real.pi * Real.exp 1) * K * ε =
      (Real.sqrt (2 * Real.pi * Real.exp 1) * K / Real.sqrt n) / t := by
    dsimp [ε]
    field_simp [ht.ne', hsqrt.ne']
  rw [heq] at hreal
  exact le_min measureReal_le_one hreal

/-- The layer-cake reduction used in Exercise 3.7(b). The two integrability
hypotheses and `hcalculus` are the one-variable calculus part of the argument;
`htail` is supplied by part (a) after substituting `r = 1/t`.

**Book Exercise 3.7.** -/
theorem exercise_3_7b_from_smallBall [IsProbabilityMeasure μ] {n : ℕ}
    {X : Ω → EuclideanSpace ℝ (Fin n)} {A : ℝ}
    (hrecip : Integrable (reciprocalNorm X) μ)
    (hmajorInt : IntegrableOn
      (fun t : ℝ => min 1 ((A / t) ^ n)) (Set.Ioi 0))
    (htail : ∀ t, 0 < t →
      μ.real {ω | t < reciprocalNorm X ω} ≤ min 1 ((A / t) ^ n))
    (hcalculus : (∫ t in Set.Ioi 0, min 1 ((A / t) ^ n)) ≤ 2 * A) :
    (∫ ω, reciprocalNorm X ω ∂μ) ≤ 2 * A := by
  have htailAnti : Antitone
      (fun t : ℝ => μ.real {ω | t < reciprocalNorm X ω}) := by
    intro s t hst
    exact measureReal_mono fun ω hω => hst.trans_lt hω
  have htailInt : IntegrableOn
      (fun t : ℝ => μ.real {ω | t < reciprocalNorm X ω}) (Set.Ioi 0) := by
    apply hmajorInt.mono'
    · exact htailAnti.measurable.aestronglyMeasurable.restrict
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact htail t ht
  rw [hrecip.integral_eq_integral_meas_lt
    (Filter.Eventually.of_forall (reciprocalNorm_nonneg X))]
  exact (setIntegral_mono_on htailInt hmajorInt measurableSet_Ioi
    (fun t ht => htail t ht)).trans hcalculus

/-- In the source normalization. Part (a) gives the
tail majorant with `A = √(2πe) K / √n`; the explicit factor `2` is a valid
absolute constant for every `n ≥ 2`.

**Book Exercise 3.7.** -/
theorem exercise_3_7b [IsProbabilityMeasure μ] {n : ℕ} (hn : 2 ≤ n)
    {X : Ω → EuclideanSpace ℝ (Fin n)}
    (hXm : ∀ i, Measurable (fun ω => X ω i))
    (hindep : iIndepFun (fun i ω => X ω i) μ)
    {K : ℝ} (hK : 0 < K)
    (hcoordDom : ∀ i, Measure.map (fun ω => X ω i) μ ≤
      Real.toNNReal K • (volume : Measure ℝ))
    (hrecip : Integrable (reciprocalNorm X) μ) :
    (∫ ω, reciprocalNorm X ω ∂μ) ≤
      (2 * Real.sqrt (2 * Real.pi * Real.exp 1)) * K / Real.sqrt n := by
  let A : ℝ := Real.sqrt (2 * Real.pi * Real.exp 1) * K / Real.sqrt n
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hcalculus := smallBallMajor_integrable_integral_le hn hA
  have htail := reciprocalNorm_tail_le hn hXm hindep hK.le hcoordDom
  have h := exercise_3_7b_from_smallBall (n := n) hrecip hcalculus.1
    htail hcalculus.2
  convert h using 1
  ring

/-- Isotropy means `E[XX^T]=I`, equivalently `E<X,v>^2=‖v‖^2`.

**Book Definition 3.2.5.** -/
theorem exercise_3_9_inner {n : ℕ}
    {X : Ω → EuclideanSpace ℝ (Fin n)} (hX : HDP.IsIsotropic X μ)
    (hprod : ∀ i j, Integrable (fun ω => X ω i * X ω j) μ)
    (u v : EuclideanSpace ℝ (Fin n)) :
    (∫ ω, inner ℝ (X ω) u * inner ℝ (X ω) v ∂μ) = inner ℝ u v := by
  have hexpand : ∀ ω,
      inner ℝ (X ω) u * inner ℝ (X ω) v =
        ∑ i : Fin n, ∑ j : Fin n, (u i * v j) * (X ω i * X ω j) := by
    intro ω
    simp only [PiLp.inner_apply, Real.inner_apply]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  calc
    (∫ ω, inner ℝ (X ω) u * inner ℝ (X ω) v ∂μ) =
        ∫ ω, ∑ i : Fin n, ∑ j : Fin n,
          (u i * v j) * (X ω i * X ω j) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall hexpand)
    _ = ∑ i : Fin n, ∑ j : Fin n,
        (u i * v j) * ∫ ω, X ω i * X ω j ∂μ := by
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro i hi
        rw [integral_finsetSum]
        · apply Finset.sum_congr rfl
          intro j hj
          rw [integral_const_mul]
        · intro j hj
          exact (hprod i j).const_mul (u i * v j)
      · intro i hi
        exact integrable_finsetSum _ fun j hj =>
          (hprod i j).const_mul (u i * v j)
    _ = ∑ i : Fin n, ∑ j : Fin n,
        (u i * v j) * (if i = j then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [(HDP.isIsotropic_iff.mp hX) i j]
    _ = inner ℝ u v := by
      simp [PiLp.inner_apply, mul_comm]

/-- Isotropic one-dimensional marginal identity.

**Book Exercise 3.9.** -/
theorem exercise_3_9 {n : ℕ}
    {X : Ω → EuclideanSpace ℝ (Fin n)} (hX : HDP.IsIsotropic X μ)
    (hprod : ∀ i j, Integrable (fun ω => X ω i * X ω j) μ)
    (u v : EuclideanSpace ℝ (Fin n)) :
    (∫ ω, inner ℝ (X ω) u * inner ℝ (X ω) v ∂μ) = inner ℝ u v ∧
      HDP.Chapter1.lpNormRV
        (fun ω => inner ℝ (X ω) u - inner ℝ (X ω) v) 2 μ = ‖u - v‖ := by
  refine ⟨exercise_3_9_inner hX hprod u v, ?_⟩
  let W : Ω → ℝ := fun ω => inner ℝ (X ω) u - inner ℝ (X ω) v
  have hW : ∀ ω, W ω = inner ℝ (X ω) (u - v) := by
    intro ω
    simp [W, inner_sub_right]
  have hsq : (∫ ω, W ω * W ω ∂μ) = inner ℝ (u - v) (u - v) := by
    convert exercise_3_9_inner hX hprod (u - v) (u - v) using 1
    simp only [hW]
  rw [HDP.Chapter1.lpNormRV]
  have habs : ∀ ω, |W ω| ^ (2 : ℝ) = W ω * W ω := by
    intro ω
    norm_num [sq_abs, pow_two]
  rw [integral_congr_ae (Filter.Eventually.of_forall habs), hsq,
    real_inner_self_eq_norm_sq]
  norm_num [← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg (u - v))]

/-! ## Exercise 3.10: standard scores -/

/-- The affine random vector `m + A Z` used in Exercise 3.10.

**Book Exercise 3.10.** -/
private noncomputable def affineRandomVector {n : ℕ}
    (m : EuclideanSpace ℝ (Fin n)) (A : Matrix (Fin n) (Fin n) ℝ)
    (Z : Ω → EuclideanSpace ℝ (Fin n)) :
    Ω → EuclideanSpace ℝ (Fin n) := fun ω =>
  m + WithLp.toLp 2 (A.mulVec fun j => Z ω j)

/-- If `Z` is centered and isotropic, then
`m + A Z` has mean `m` and covariance `A Aᵀ`. Taking `A = Σ^{1/2}` gives
the printed statement.

**Book Equation (3.10).** -/
theorem exercise_3_10a [IsProbabilityMeasure μ] {n : ℕ}
    (m : EuclideanSpace ℝ (Fin n)) (A : Matrix (Fin n) (Fin n) ℝ)
    {Z : Ω → EuclideanSpace ℝ (Fin n)}
    (hZint : ∀ j, Integrable (fun ω => Z ω j) μ)
    (hZprod : ∀ j k, Integrable (fun ω => Z ω j * Z ω k) μ)
    (hZ0 : ∀ j, ∫ ω, Z ω j ∂μ = 0)
    (hZiso : HDP.IsIsotropic Z μ) :
    (∀ i, ∫ ω, affineRandomVector m A Z ω i ∂μ = m i) ∧
      HDP.covarianceMatrix (affineRandomVector m A Z) μ = A * A.transpose := by
  classical
  have hmean : ∀ i, ∫ ω, affineRandomVector m A Z ω i ∂μ = m i := by
    intro i
    have hsumInt : Integrable (fun ω => ∑ j, A i j * Z ω j) μ :=
      integrable_finsetSum _ fun j _ => (hZint j).const_mul _
    change (∫ ω, m i + ∑ j, A i j * Z ω j ∂μ) = m i
    rw [integral_add (integrable_const _) hsumInt, integral_const,
      integral_finsetSum]
    · rw [probReal_univ, one_smul]
      apply add_eq_left.mpr
      apply Finset.sum_eq_zero
      intro j hj
      rw [integral_const_mul, hZ0 j, mul_zero]
    · intro j hj
      exact (hZint j).const_mul _
  refine ⟨hmean, ?_⟩
  ext i k
  change (∫ ω,
      (affineRandomVector m A Z ω i -
        ∫ ω', affineRandomVector m A Z ω' i ∂μ) *
      (affineRandomVector m A Z ω k -
        ∫ ω', affineRandomVector m A Z ω' k ∂μ) ∂μ) = _
  rw [hmean i, hmean k]
  have hexpand : ∀ ω,
      (affineRandomVector m A Z ω i - m i) *
          (affineRandomVector m A Z ω k - m k) =
        ∑ j : Fin n, ∑ l : Fin n,
          (A i j * A k l) * (Z ω j * Z ω l) := by
    intro ω
    change ((m i + ∑ j, A i j * Z ω j) - m i) *
        ((m k + ∑ l, A k l * Z ω l) - m k) = _
    simp only [add_sub_cancel_left]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    ring
  calc
    (∫ ω,
        (affineRandomVector m A Z ω i - m i) *
          (affineRandomVector m A Z ω k - m k) ∂μ) =
        ∫ ω, ∑ j : Fin n, ∑ l : Fin n,
          (A i j * A k l) * (Z ω j * Z ω l) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall hexpand)
    _ = ∑ j : Fin n, ∑ l : Fin n,
        (A i j * A k l) * ∫ ω, Z ω j * Z ω l ∂μ := by
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro j hj
        rw [integral_finsetSum]
        · apply Finset.sum_congr rfl
          intro l hl
          rw [integral_const_mul]
        · intro l hl
          exact (hZprod j l).const_mul _
      · intro j hj
        exact integrable_finsetSum _ fun l hl => (hZprod j l).const_mul _
    _ = ∑ j : Fin n, ∑ l : Fin n,
        (A i j * A k l) * (if j = l then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro l hl
      rw [(HDP.isIsotropic_iff.mp hZiso) j l]
    _ = (A * A.transpose) i k := by
      simp [Matrix.mul_apply]

/-- The standard
score may live on an enlarged product probability space. Coordinate second
moments verify isotropy, and `hfactor` verifies the almost-sure affine
reconstruction. This avoids the false same-space kernel-noise assertion in
the singular case.

**Book Equation (3.10).** -/
theorem exercise_3_10b
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {ν : Measure Ω'} {n : ℕ}
    (m : EuclideanSpace ℝ (Fin n)) (A : Matrix (Fin n) (Fin n) ℝ)
    (X : Ω → EuclideanSpace ℝ (Fin n))
    (Z : Ω × Ω' → EuclideanSpace ℝ (Fin n))
    (hZ0 : ∀ i, ∫ z, Z z i ∂μ.prod ν = 0)
    (hZsecond : ∀ i j, ∫ z, Z z i * Z z j ∂μ.prod ν =
      if i = j then 1 else 0)
    (hfactor : ∀ᵐ z ∂μ.prod ν,
      X z.1 = affineRandomVector m A Z z) :
    (∀ i, ∫ z, Z z i ∂μ.prod ν = 0) ∧
      HDP.IsIsotropic Z (μ.prod ν) ∧
      (∀ᵐ z ∂μ.prod ν, X z.1 = affineRandomVector m A Z z) := by
  refine ⟨hZ0, (HDP.isIsotropic_iff.mpr ?_), hfactor⟩
  exact hZsecond

/-- Defines `permutedVector`, the permuted vector used in the surrounding construction.

**Lean implementation helper.** -/
noncomputable def permutedVector {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) (σ : Equiv.Perm (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => x (σ i))

/-! ## Exercise 3.13: maximum norm of random vectors -/

/-- The finite maximum of Euclidean norms used in Exercise 3.13.

**Book Exercise 3.13.** -/
noncomputable def maxNormVectors {N n : ℕ}
    (X : Fin (N + 2) → Ω → EuclideanSpace ℝ (Fin n)) (ω : Ω) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i => ‖X i ω‖

/-- Shows that `maxNormVectors` is measurable.

**Lean implementation helper.** -/
private lemma maxNormVectors_measurable {N n : ℕ}
    {X : Fin (N + 2) → Ω → EuclideanSpace ℝ (Fin n)}
    (hXm : ∀ i, Measurable (X i)) : Measurable (maxNormVectors X) := by
  change Measurable (fun ω =>
    Finset.univ.sup' Finset.univ_nonempty fun i => ‖X i ω‖)
  have h := Finset.measurable_sup' Finset.univ_nonempty
    fun i hi => (hXm i).norm
  have heq : (Finset.univ.sup' Finset.univ_nonempty
      fun i ω => ‖X i ω‖) =
      (fun ω => Finset.univ.sup' Finset.univ_nonempty fun i => ‖X i ω‖) := by
    funext ω
    simp only [Finset.sup'_apply]
  rwa [heq] at h

/-- This is the high-dimensional maximal
inequality with fully explicit constant
`2 * normConcentrationConstant`. Independence is only required among the
coordinates of each vector; the vectors themselves may be dependent.

**Book Exercise 3.13.** -/
theorem exercise_3_13a [IsProbabilityMeasure μ] {N n : ℕ} (hn : 0 < n)
    {X : Fin (N + 2) → Ω → EuclideanSpace ℝ (Fin n)}
    (hXm : ∀ i, Measurable (X i))
    (hXsub : ∀ i j, HDP.SubGaussian (fun ω => X i ω j) μ)
    (hsecond : ∀ i j, ∫ ω, X i ω j ^ 2 ∂μ = 1)
    (hindep : ∀ i, iIndepFun (fun j ω => X i ω j) μ)
    {K : ℝ} (hK : 0 < K)
    (hKb : ∀ i j, HDP.psi2Norm (fun ω => X i ω j) μ ≤ K) :
    (∫ ω, maxNormVectors X ω ∂μ) ≤
      Real.sqrt n + 2 * Real.sqrt (Real.log ((N : ℝ) + 2)) *
        (normConcentrationConstant * K ^ 2) := by
  let D : Fin (N + 2) → Ω → ℝ := fun i ω => ‖X i ω‖ - Real.sqrt n
  have hcoordm : ∀ i j, AEMeasurable (fun ω => X i ω j) μ := by
    intro i j
    exact ((EuclideanSpace.proj j).measurable.comp (hXm i)).aemeasurable
  have hsqrtNorm : ∀ i ω,
      Real.sqrt (∑ j : Fin n, X i ω j ^ 2) = ‖X i ω‖ := by
    intro i ω
    rw [← EuclideanSpace.real_norm_sq_eq]
    exact Real.sqrt_sq (norm_nonneg (X i ω))
  have hDsub : ∀ i, HDP.SubGaussian (D i) μ := by
    intro i
    have h := concentration_norm hn (hcoordm i) (hXsub i) (hsecond i)
      (hindep i) hK (hKb i)
    simpa only [D, hsqrtNorm] using h.1
  have hDpsi : ∀ i, HDP.psi2Norm (D i) μ ≤
      normConcentrationConstant * K ^ 2 := by
    intro i
    have h := concentration_norm hn (hcoordm i) (hXsub i) (hsecond i)
      (hindep i) hK (hKb i)
    simpa only [D, hsqrtNorm] using h.2
  have hDm : ∀ i, Measurable (D i) := fun i => (hXm i).norm.sub_const _
  have hCpos : 0 < normConcentrationConstant * K ^ 2 := by
    exact mul_pos normConcentrationConstant_pos (sq_pos_of_pos hK)
  have hmax := HDP.expectation_max_le hDm hDsub hCpos hDpsi
  have hMaxDsub := (HDP.psi2Norm_max_le hDm hDsub hCpos hDpsi).1
  let MD : Ω → ℝ := fun ω =>
    Finset.univ.sup' Finset.univ_nonempty fun i => D i ω
  have hMDm : Measurable MD := by
    have h := Finset.measurable_sup' Finset.univ_nonempty
      fun i hi => hDm i
    have heq : (Finset.univ.sup' Finset.univ_nonempty D) = MD := by
      funext ω
      simp only [MD, Finset.sup'_apply]
    rwa [heq] at h
  have hMDint : Integrable MD μ :=
    (hMaxDsub.memLp hMDm.aemeasurable (le_refl (1 : ℝ))).integrable
      (by norm_num)
  have hpoint : maxNormVectors X = fun ω => Real.sqrt n + MD ω := by
    funext ω
    change (Finset.univ.sup' Finset.univ_nonempty fun i => ‖X i ω‖) = _
    rw [Finset.add_sup' (Finset.univ : Finset (Fin (N + 2)))
      (fun i => D i ω) (Real.sqrt n) Finset.univ_nonempty]
    apply congrArg
    funext i
    simp [D]
  calc
    (∫ ω, maxNormVectors X ω ∂μ) =
        ∫ ω, (Real.sqrt n + MD ω) ∂μ := by rw [hpoint]
    _ = Real.sqrt n + ∫ ω, MD ω ∂μ := by
      rw [integral_add (integrable_const _) hMDint, integral_const,
        probReal_univ, one_smul]
    _ ≤ Real.sqrt n +
        2 * Real.sqrt (Real.log ((N : ℝ) + 2)) *
          (normConcentrationConstant * K ^ 2) := by
      have hmaxMD : (∫ ω, MD ω ∂μ) ≤
          2 * Real.sqrt (Real.log ((N : ℝ) + 2)) *
            (normConcentrationConstant * K ^ 2) := by
        simpa only [MD] using hmax
      linarith

/-- Bounds `sum_abs` above by `sqrt_mul_norm`.

**Lean implementation helper.** -/
private lemma sum_abs_le_sqrt_mul_norm {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) :
    (∑ j, |x j|) ≤ Real.sqrt n * ‖x‖ := by
  have h := HDP.Chapter1.cauchy_schwarz_vector
    (fun j : Fin n => |x j|) (fun _ : Fin n => (1 : ℝ))
  rw [HDP.Chapter1.dotProduct, HDP.Chapter1.lpNorm_two,
    HDP.Chapter1.lpNorm_two] at h
  simp only [mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, one_pow] at h
  rw [abs_of_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _)] at h
  have hx : Real.sqrt (∑ j : Fin n, |x j| ^ 2) = ‖x‖ := by
    rw [show (∑ j : Fin n, |x j| ^ 2) = ∑ j : Fin n, x j ^ 2 by
      apply Finset.sum_congr rfl
      intro j hj
      exact sq_abs (x j)]
    rw [← EuclideanSpace.real_norm_sq_eq]
    exact Real.sqrt_sq (norm_nonneg x)
  rw [hx] at h
  simpa [mul_comm] using h

/-- A standard real Gaussian has first absolute moment `sqrt (2/π)`.

**Lean implementation helper.** -/
private lemma gaussian_first_absolute_moment
    {g : Ω → ℝ} (hg : HasLaw g (gaussianReal 0 1) μ) :
    (∫ ω, |g ω| ∂μ) = Real.sqrt 2 / Real.sqrt Real.pi := by
  have h := HDP.Chapter2.gaussian_absolute_moment hg (p := (1 : ℝ)) le_rfl
  have hs : (2 : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt 2 := by
    rw [← Real.sqrt_eq_rpow]
  rw [hs] at h
  simpa [Real.rpow_one, Real.Gamma_one] using h

/-- A dimension-uniform radial lower bound for a standard Gaussian vector,
proved from the exact first absolute moment and Cauchy--Schwarz.

**Lean implementation helper.** -/
theorem gaussian_norm_expectation_lower [IsProbabilityMeasure μ] {n : ℕ}
    {G : Ω → EuclideanSpace ℝ (Fin (n + 1))}
    (hGm : Measurable G)
    (hg : ∀ j, HasLaw (fun ω => G ω j) (gaussianReal 0 1) μ)
    (hGnorm : Integrable (fun ω => ‖G ω‖) μ) :
    (Real.sqrt 2 / Real.sqrt Real.pi) * Real.sqrt ((n : ℝ) + 1) ≤
      ∫ ω, ‖G ω‖ ∂μ := by
  have hcoordInt : ∀ j, Integrable (fun ω => |G ω j|) μ := by
    intro j
    have hsub := subGaussian_of_hasLaw_standardGaussian (hg j)
    have hm : Measurable (fun ω => G ω j) := by
      exact (EuclideanSpace.proj j).measurable.comp hGm
    exact ((hsub.memLp hm.aemeasurable (le_refl (1 : ℝ))).integrable
      (by norm_num)).abs
  have hsumInt : Integrable (fun ω => ∑ j, |G ω j|) μ :=
    integrable_finsetSum _ fun j _ => hcoordInt j
  have hsqrtInt : Integrable
      (fun ω => Real.sqrt ((n : ℝ) + 1) * ‖G ω‖) μ := hGnorm.const_mul _
  have hineq : ((n : ℝ) + 1) *
      (Real.sqrt 2 / Real.sqrt Real.pi) ≤
      Real.sqrt ((n : ℝ) + 1) * ∫ ω, ‖G ω‖ ∂μ := by
    calc
      ((n : ℝ) + 1) * (Real.sqrt 2 / Real.sqrt Real.pi) =
          ∑ j : Fin (n + 1), ∫ ω, |G ω j| ∂μ := by
        rw [show (∑ j : Fin (n + 1), ∫ ω, |G ω j| ∂μ) =
            ∑ _j : Fin (n + 1), (Real.sqrt 2 / Real.sqrt Real.pi) by
          apply Finset.sum_congr rfl
          intro j hj
          exact gaussian_first_absolute_moment (hg j)]
        simp
      _ = ∫ ω, ∑ j, |G ω j| ∂μ := by
        rw [integral_finsetSum]
        exact fun j hj => hcoordInt j
      _ ≤ ∫ ω, Real.sqrt ((n : ℝ) + 1) * ‖G ω‖ ∂μ :=
        integral_mono hsumInt hsqrtInt fun ω => by
          simpa only [Nat.cast_add, Nat.cast_one] using
            sum_abs_le_sqrt_mul_norm (G ω)
      _ = Real.sqrt ((n : ℝ) + 1) * ∫ ω, ‖G ω‖ ∂μ := by
        rw [integral_const_mul]
  have hdpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hspos : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr hdpos
  have hsq : Real.sqrt ((n : ℝ) + 1) ^ 2 = (n : ℝ) + 1 :=
    Real.sq_sqrt hdpos.le
  apply le_of_mul_le_mul_left (a := Real.sqrt ((n : ℝ) + 1))
  · calc
    Real.sqrt ((n : ℝ) + 1) *
        ((Real.sqrt 2 / Real.sqrt Real.pi) * Real.sqrt ((n : ℝ) + 1)) =
        ((n : ℝ) + 1) * (Real.sqrt 2 / Real.sqrt Real.pi) := by
      calc
        _ = (Real.sqrt 2 / Real.sqrt Real.pi) *
            (Real.sqrt ((n : ℝ) + 1) ^ 2) := by ring
        _ = (Real.sqrt 2 / Real.sqrt Real.pi) * ((n : ℝ) + 1) := by rw [hsq]
        _ = ((n : ℝ) + 1) * (Real.sqrt 2 / Real.sqrt Real.pi) := by ring
    _ ≤ Real.sqrt ((n : ℝ) + 1) * ∫ ω, ‖G ω‖ ∂μ := hineq
  · exact hspos

/-- The `√(log N)` half of Exercise 3.13(b), obtained by projecting every
Gaussian vector onto one coordinate and applying Exercise 3.6.

**Book Exercise 3.13.** -/
theorem exercise_3_13b_log [IsProbabilityMeasure μ] {N n : ℕ}
    {X : Fin (N + 2) → Ω → EuclideanSpace ℝ (Fin (n + 1))}
    (hXm : ∀ i, Measurable (X i))
    (hg : ∀ i j, HasLaw (fun ω => X i ω j) (gaussianReal 0 1) μ)
    (hindepFirst : iIndepFun (fun i ω => X i ω (0 : Fin (n + 1))) μ)
    (hmaxInt : Integrable (maxNormVectors X) μ) :
    gaussianLpLowerConstant * Real.sqrt (Real.log ((N : ℝ) + 2)) ≤
      ∫ ω, maxNormVectors X ω ∂μ := by
  let Y : Fin (N + 2) → Ω → ℝ := fun i ω => X i ω (0 : Fin (n + 1))
  have hYm : ∀ i, Measurable (Y i) := fun i =>
    by
      change Measurable (fun ω => (WithLp.ofLp (X i ω)) (0 : Fin (n + 1)))
      exact (EuclideanSpace.proj (0 : Fin (n + 1))).measurable.comp (hXm i)
  have hYlaw : ∀ i, HasLaw (Y i) (gaussianReal 0 1) μ := fun i => hg i 0
  have hYsub : ∀ i, HDP.SubGaussian (Y i) μ := fun i =>
    subGaussian_of_hasLaw_standardGaussian (hYlaw i)
  have hYpsi : ∀ i, HDP.psi2Norm (Y i) μ ≤ 2 := by
    intro i
    rw [HDP.psi2Norm_standardGaussian (hYlaw i)]
    have hsqrt := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8 / 3)
    have hsqrt0 := Real.sqrt_nonneg (8 / 3 : ℝ)
    nlinarith
  have hMsub : HDP.SubGaussian (maxAbsCoordinates Y) μ := by
    change HDP.SubGaussian
      (fun ω => Finset.univ.sup' Finset.univ_nonempty fun i => |Y i ω|) μ
    exact (HDP.psi2Norm_max_abs_le hYm hYsub (by norm_num) hYpsi).1
  have hMm := maxAbsCoordinates_measurable hYm
  have hMint : Integrable (maxAbsCoordinates Y) μ :=
    (hMsub.memLp hMm.aemeasurable (le_refl (1 : ℝ))).integrable (by norm_num)
  have hpoint : ∀ ω, maxAbsCoordinates Y ω ≤ maxNormVectors X ω := by
    intro ω
    apply Finset.sup'_le
    intro i hi
    calc
      |Y i ω| ≤ ‖X i ω‖ := by
        simpa [Y, Real.norm_eq_abs] using
          (PiLp.norm_apply_le (X i ω) (0 : Fin (n + 1)))
      _ ≤ maxNormVectors X ω :=
        Finset.le_sup' (fun k => ‖X k ω‖) (Finset.mem_univ i)
  calc
    gaussianLpLowerConstant * Real.sqrt (Real.log ((N : ℝ) + 2)) ≤
        ∫ ω, maxAbsCoordinates Y ω ∂μ := by
      exact exercise_3_6_top hYm hYlaw (by simpa [Y] using hindepFirst)
    _ ≤ ∫ ω, maxNormVectors X ω ∂μ :=
      integral_mono hMint hmaxInt hpoint

/-- For i.i.d. standard Gaussian vectors the
maximum norm has the matching `√n + √(log N)` lower scale. The proof only
uses coordinate Gaussian laws, independence of the first coordinates, and
integrability of the finite maximum (automatic for Gaussian vectors).

**Book Exercise 3.13.** -/
theorem exercise_3_13b [IsProbabilityMeasure μ] {N n : ℕ}
    {X : Fin (N + 2) → Ω → EuclideanSpace ℝ (Fin (n + 1))}
    (hXm : ∀ i, Measurable (X i))
    (hg : ∀ i j, HasLaw (fun ω => X i ω j) (gaussianReal 0 1) μ)
    (hindepFirst : iIndepFun (fun i ω => X i ω (0 : Fin (n + 1))) μ)
    (hmaxInt : Integrable (maxNormVectors X) μ) :
    (min gaussianLpLowerConstant
        (Real.sqrt 2 / Real.sqrt Real.pi) / 2) *
        (Real.sqrt ((n : ℝ) + 1) + Real.sqrt (Real.log ((N : ℝ) + 2))) ≤
      ∫ ω, maxNormVectors X ω ∂μ := by
  let i0 : Fin (N + 2) := ⟨0, by omega⟩
  have hnorm0m : AEStronglyMeasurable (fun ω => ‖X i0 ω‖) μ :=
    (hXm i0).norm.aestronglyMeasurable
  have hnorm0le : ∀ᵐ ω ∂μ, ‖(fun ω => ‖X i0 ω‖) ω‖ ≤ maxNormVectors X ω := by
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact Finset.le_sup' (fun i => ‖X i ω‖) (Finset.mem_univ i0)
  have hnorm0Int : Integrable (fun ω => ‖X i0 ω‖) μ :=
    hmaxInt.mono' hnorm0m hnorm0le
  have hradial0 := gaussian_norm_expectation_lower (hXm i0) (hg i0) hnorm0Int
  have hradial : (Real.sqrt 2 / Real.sqrt Real.pi) * Real.sqrt ((n : ℝ) + 1) ≤
      ∫ ω, maxNormVectors X ω ∂μ := by
    refine hradial0.trans (integral_mono hnorm0Int hmaxInt fun ω => ?_)
    exact Finset.le_sup' (fun i => ‖X i ω‖) (Finset.mem_univ i0)
  have hlog := exercise_3_13b_log hXm hg hindepFirst hmaxInt
  have hc1 : min gaussianLpLowerConstant
      (Real.sqrt 2 / Real.sqrt Real.pi) ≤ gaussianLpLowerConstant := min_le_left _ _
  have hc2 : min gaussianLpLowerConstant
      (Real.sqrt 2 / Real.sqrt Real.pi) ≤
        Real.sqrt 2 / Real.sqrt Real.pi := min_le_right _ _
  have hsqrtn : 0 ≤ Real.sqrt ((n : ℝ) + 1) := Real.sqrt_nonneg _
  have hsqrtlog : 0 ≤ Real.sqrt (Real.log ((N : ℝ) + 2)) := Real.sqrt_nonneg _
  have hminNonneg : 0 ≤ min gaussianLpLowerConstant
      (Real.sqrt 2 / Real.sqrt Real.pi) := by
    exact le_min gaussianLpLowerConstant_pos.le (by positivity)
  nlinarith

end HDP.Chapter3

end Source_05_MomentGeometry

/-! ## Material formerly in `08_GaussianVectors.lean` -/

section Source_08_GaussianVectors

/-!
# Book Chapter 3, Section 3.3: Gaussian vectors

This file gives the measure-theoretic forms of the Gaussian-vector results in
Book Section 3.3.  Mathlib's `ProbabilityTheory.stdGaussian` is the standard
Gaussian measure on a finite-dimensional real inner-product space, and
`ProbabilityTheory.multivariateGaussian` is the Gaussian measure with prescribed
mean and positive-semidefinite covariance matrix.
-/

open MeasureTheory ProbabilityTheory InnerProductSpace Matrix WithLp Module
open scoped ENNReal NNReal RealInnerProductSpace MatrixOrder

namespace HDP.Chapter3

noncomputable section

/-! ## Book Definition 3.3.4: affine Gaussian representations -/

/-- The continuous linear map represented by a rectangular real matrix on
Euclidean spaces.

**Lean implementation helper.** -/
def rectangularEuclideanCLM {n k : ℕ} (A : Matrix (Fin n) (Fin k) ℝ) :
    EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearMap.toContinuousLinearMap (Matrix.toLpLin 2 2 A)

/-- The law of the affine image `μ + AZ` of a standard Gaussian vector
`Z ∈ ℝᵏ`.

**Book Definition 3.3.4.** -/
def affineGaussianMeasure {n k : ℕ}
    (mu : EuclideanSpace ℝ (Fin n))
    (A : Matrix (Fin n) (Fin k) ℝ) :
    Measure (EuclideanSpace ℝ (Fin n)) :=
  (stdGaussian (EuclideanSpace ℝ (Fin k))).map
    (fun z => mu + rectangularEuclideanCLM A z)

/-- An affine image `μ + AZ` of a standard Gaussian has multivariate Gaussian
law with covariance `AAᵀ`, for an arbitrary rectangular matrix `A`.

**Book Definition 3.3.4.** -/
theorem affineGaussianMeasure_eq_multivariateGaussian {n k : ℕ}
    (mu : EuclideanSpace ℝ (Fin n))
    (A : Matrix (Fin n) (Fin k) ℝ) :
    affineGaussianMeasure mu A =
      multivariateGaussian mu (A * A.transpose) := by
  let nu := affineGaussianMeasure mu A
  have hnu : IsGaussian nu := by
    dsimp [nu, affineGaussianMeasure]
    rw [show (fun z => mu + rectangularEuclideanCLM A z) =
      (fun x => mu + x) ∘ rectangularEuclideanCLM A by rfl]
    rw [← Measure.map_map (measurable_const_add mu) (by fun_prop)]
    infer_instance
  letI : IsGaussian nu := hnu
  apply IsGaussian.ext
  · dsimp [nu, affineGaussianMeasure]
    rw [integral_map (by fun_prop) (by fun_prop)]
    rw [integral_add (integrable_const _) (by
      exact IsGaussian.integrable_id.comp_measurable (by fun_prop)),
      integral_const]
    have hLmean : ∫ a, rectangularEuclideanCLM A a ∂stdGaussian
        (EuclideanSpace ℝ (Fin k)) = 0 := by
      calc
        _ = rectangularEuclideanCLM A (∫ a, a ∂stdGaussian
            (EuclideanSpace ℝ (Fin k))) := by
          simpa using (rectangularEuclideanCLM A).integral_comp_comm
            (φ := fun a => a)
            (IsGaussian.integrable_id
              (μ := stdGaussian (EuclideanSpace ℝ (Fin k))))
        _ = 0 := by rw [integral_id_stdGaussian]; simp
    rw [hLmean, integral_id_multivariateGaussian]
    simp
  · ext x y
    dsimp [nu, affineGaussianMeasure]
    rw [show (fun z => mu + rectangularEuclideanCLM A z) =
      (fun x => mu + x) ∘ rectangularEuclideanCLM A by rfl]
    rw [← Measure.map_map (measurable_const_add mu) (by fun_prop),
      covarianceBilin_map_const_add,
      covarianceBilin_map IsGaussian.memLp_two_id,
      covarianceBilin_stdGaussian]
    rw [covarianceBilin_multivariateGaussian]
    · unfold rectangularEuclideanCLM
      change inner ℝ
          (A.toEuclideanLin.toContinuousLinearMap.adjoint x)
          (A.toEuclideanLin.toContinuousLinearMap.adjoint y) = _
      have hadj (z : EuclideanSpace ℝ (Fin n)) :
          A.toEuclideanLin.toContinuousLinearMap.adjoint z =
            A.transpose.toEuclideanLin z := by
        change A.toEuclideanLin.adjoint z = A.transpose.toEuclideanLin z
        rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
        simp only [Matrix.conjTranspose_eq_transpose_of_trivial]
      rw [ContinuousLinearMap.adjoint_inner_left, hadj]
      change inner ℝ x
        (A.toEuclideanLin (A.transpose.toEuclideanLin y)) = _
      simp [PiLp.inner_apply, Matrix.mulVec_mulVec]
      rw [dotProduct_comm]
      rfl
    · simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        Matrix.posSemidef_self_mul_conjTranspose A

/-- A random vector admits an affine Gaussian representation with the stated
mean and covariance when its law is the pushforward of a standard Gaussian
under some rectangular affine map `z ↦ μ + Az`.

**Book Definition 3.3.4.** -/
def HasAffineGaussianRepresentation
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (X : Ω → EuclideanSpace ℝ (Fin n)) (P : Measure Ω)
    (mu : EuclideanSpace ℝ (Fin n))
    (S : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  AEMeasurable X P ∧ ∃ k : ℕ, ∃ A : Matrix (Fin n) (Fin k) ℝ,
    S = A * A.transpose ∧
      Measure.map X P = affineGaussianMeasure mu A

/-- For positive-semidefinite covariance, the specified multivariate Gaussian
law is equivalent to the book's definition as an affine image `μ + AZ` of a
standard Gaussian vector of an arbitrary finite dimension.

**Book Definition 3.3.4.** -/
theorem hasGaussianVectorLaw_iff_affineRepresentation
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (X : Ω → EuclideanSpace ℝ (Fin n)) (P : Measure Ω)
    (mu : EuclideanSpace ℝ (Fin n))
    {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosSemidef) :
    HDP.HasGaussianVectorLaw X P mu S ↔
      HasAffineGaussianRepresentation X P mu S := by
  constructor
  · rintro ⟨hXm, hmap⟩
    refine ⟨hXm, n, CFC.sqrt S, ?_, ?_⟩
    · have hsqrtT : (CFC.sqrt S)ᵀ = CFC.sqrt S := by
        simpa only [Matrix.IsHermitian,
          Matrix.conjTranspose_eq_transpose_of_trivial, sub_zero] using
          (CFC.sqrt_nonneg S).isHermitian
      rw [hsqrtT]
      exact (CFC.sqrt_mul_sqrt_self S hS.nonneg).symm
    · rw [hmap, affineGaussianMeasure_eq_multivariateGaussian]
      congr 2
      have hsqrtT : (CFC.sqrt S)ᵀ = CFC.sqrt S := by
        simpa only [Matrix.IsHermitian,
          Matrix.conjTranspose_eq_transpose_of_trivial, sub_zero] using
          (CFC.sqrt_nonneg S).isHermitian
      rw [hsqrtT]
      exact (CFC.sqrt_mul_sqrt_self S hS.nonneg).symm
  · rintro ⟨hXm, k, A, hSA, hmap⟩
    refine ⟨hXm, ?_⟩
    rw [hmap, affineGaussianMeasure_eq_multivariateGaussian, hSA]

/-! ## Book Proposition 3.3.1: rotation invariance -/

/-- A linear isometry sends a
standard Gaussian vector to a standard Gaussian vector. Taking domain and
codomain equal gives the source's orthogonal-rotation statement.

**Book Proposition 3.3.1.** -/
theorem standardGaussian_rotation_invariant
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (U : E ≃ₗᵢ[ℝ] F) :
    (stdGaussian E).map U = stdGaussian F :=
  stdGaussian_map U

/-! ## Book Corollary 3.3.2: one-dimensional marginals -/

/-- A source-facing variance parameter for the one-dimensional marginal in
Corollary 3.3.2.

**Book Corollary 3.3.2.** -/
noncomputable def gaussianMarginalVariance
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (v : E) : ℝ≥0 :=
  (‖v‖ ^ 2).toNNReal

/-- If `Z` has the
standard Gaussian law, then `⟪v, Z⟫` has law `N(0, ‖v‖²)`.

**Book Corollary 3.3.2.** -/
theorem standardGaussian_inner_hasLaw
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (v : E) :
    HasLaw (fun z : E ↦ ⟪v, z⟫) (gaussianReal 0 (gaussianMarginalVariance v))
      (stdGaussian E) := by
  refine ⟨by fun_prop, ?_⟩
  have h :=
    (IsGaussian.map_eq_gaussianReal ((innerSL ℝ) v) :
      (stdGaussian E).map ((innerSL ℝ) v) =
        gaussianReal ((stdGaussian E)[(innerSL ℝ) v])
          Var[(innerSL ℝ) v; stdGaussian E].toNNReal)
  rw [integral_strongDual_stdGaussian, variance_dual_stdGaussian] at h
  simpa [gaussianMarginalVariance, innerSL_apply_apply ℝ, innerSL_apply_norm] using h

/-! ## Nondegenerate multivariate Gaussian densities -/

/-- Push-forward commutes with `withDensity` along a measurable equivalence,
with the density transported by the inverse equivalence.

**Lean implementation helper.** -/
lemma MeasurableEquiv.map_withDensity
    {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (e : E ≃ᵐ F) (m : Measure E) (f : E → ℝ≥0∞) (hf : Measurable f) :
    (m.withDensity f).map e =
      (m.map e).withDensity (f ∘ e.symm) := by
  ext s hs
  rw [e.map_apply, withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs,
    setLIntegral_map hs (hf.comp e.symm.measurable) e.measurable]
  simp

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- For positive-definite covariance `S`, the Euclidean linear map induced by `sqrt S` has nonzero determinant (`covarianceSqrtCLM_det_ne_zero`).

**Lean implementation helper.** -/
private lemma covarianceSqrtCLM_det_ne_zero
    {S : Matrix n n ℝ} (hS : S.PosDef) :
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)).det ≠ 0 := by
  rw [ContinuousLinearMap.det, Matrix.coe_toEuclideanCLM_eq_toEuclideanLin,
    LinearMap.det_toLpLin, hS.posSemidef.det_sqrt, RCLike.sqrt_real]
  exact ne_of_gt (Real.sqrt_pos.2 hS.det_pos)

/-- The invertible positive square root of a positive-definite covariance
matrix, as a continuous linear equivalence of Euclidean space.

**Lean implementation helper.** -/
def covarianceSqrtEquiv (S : Matrix n n ℝ) (hS : S.PosDef) :
    EuclideanSpace ℝ n ≃L[ℝ] EuclideanSpace ℝ n :=
  (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)).toContinuousLinearEquivOfDetNeZero
    (covarianceSqrtCLM_det_ne_zero hS)

/-- Gives the coordinatewise evaluation formula for `covarianceSqrtEquiv`.

**Lean implementation helper.** -/
@[simp] lemma covarianceSqrtEquiv_apply (S : Matrix n n ℝ) (hS : S.PosDef)
    (x : EuclideanSpace ℝ n) :
    covarianceSqrtEquiv S hS x =
      Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) x := by
  rfl

/-- The affine equivalence `z ↦ μ + S¹⁄² z` used to construct a
nondegenerate multivariate Gaussian from a standard Gaussian.

**Lean implementation helper.** -/
def covarianceAffineEquiv (mu : EuclideanSpace ℝ n) (S : Matrix n n ℝ)
    (hS : S.PosDef) : EuclideanSpace ℝ n ≃ᵐ EuclideanSpace ℝ n :=
  (covarianceSqrtEquiv S hS).toHomeomorph.toMeasurableEquiv.trans
    (Homeomorph.addLeft mu).toMeasurableEquiv

/-- Gives the coordinatewise evaluation formula for `covarianceAffineEquiv`.

**Lean implementation helper.** -/
@[simp] lemma covarianceAffineEquiv_apply
    (mu : EuclideanSpace ℝ n) (S : Matrix n n ℝ) (hS : S.PosDef)
    (x : EuclideanSpace ℝ n) :
    covarianceAffineEquiv mu S hS x =
      mu + Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) x := by
  rfl

/-- Gives the coordinatewise evaluation formula for `covarianceAffineEquiv_symm`.

**Lean implementation helper.** -/
@[simp] lemma covarianceAffineEquiv_symm_apply
    (mu : EuclideanSpace ℝ n) (S : Matrix n n ℝ) (hS : S.PosDef)
    (x : EuclideanSpace ℝ n) :
    (covarianceAffineEquiv mu S hS).symm x =
      (covarianceSqrtEquiv S hS).symm (x - mu) := by
  change (covarianceSqrtEquiv S hS).symm (-mu + x) =
    (covarianceSqrtEquiv S hS).symm (x - mu)
  congr 1
  abel

/-- The determinant factor `(det S)^{-1/2}` in the nondegenerate Gaussian
density, represented in `ℝ≥0∞`.

**Lean implementation helper.** -/
def covarianceDetSqrtInv (S : Matrix n n ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.sqrt S.det) ⁻¹

/-- For positive-definite `S`, `covarianceSqrtCLM_det_eq` identifies the determinant of the Euclidean square-root map with `sqrt (det S)`.

**Lean implementation helper.** -/
private lemma covarianceSqrtCLM_det_eq
    {S : Matrix n n ℝ} (hS : S.PosDef) :
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)).det = Real.sqrt S.det := by
  rw [ContinuousLinearMap.det, Matrix.coe_toEuclideanCLM_eq_toEuclideanLin,
    LinearMap.det_toLpLin, hS.posSemidef.det_sqrt, RCLike.sqrt_real]

/-- `map_covarianceSqrtCLM_volume` shows that the covariance square-root map sends volume to `covarianceDetSqrtInv S • volume`.

**Lean implementation helper.** -/
private lemma map_covarianceSqrtCLM_volume
    {S : Matrix n n ℝ} (hS : S.PosDef) :
    Measure.map (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)) volume =
      covarianceDetSqrtInv S • volume := by
  have h := (volume : Measure (EuclideanSpace ℝ n)).map_linearMap_addHaar_eq_smul_addHaar
    (covarianceSqrtCLM_det_ne_zero hS)
  have hdet : LinearMap.det
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) :
        EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ n) = Real.sqrt S.det := by
    rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin,
      LinearMap.det_toLpLin, hS.posSemidef.det_sqrt, RCLike.sqrt_real]
  rw [hdet] at h
  simpa [covarianceDetSqrtInv,
    abs_of_pos (inv_pos.mpr (Real.sqrt_pos.2 hS.det_pos))] using h

/-- `map_covarianceAffineEquiv_volume` shows that the covariance affine equivalence sends volume to `covarianceDetSqrtInv S • volume`.

**Lean implementation helper.** -/
private lemma map_covarianceAffineEquiv_volume
    (mu : EuclideanSpace ℝ n) {S : Matrix n n ℝ} (hS : S.PosDef) :
    Measure.map (covarianceAffineEquiv mu S hS) volume =
      covarianceDetSqrtInv S • volume := by
  change Measure.map
    (fun x ↦ mu + Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) x) volume = _
  have hfun : (fun x : EuclideanSpace ℝ n ↦
      mu + Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) x) =
      (fun x ↦ mu + x) ∘ Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) := rfl
  rw [hfun]
  rw [← Measure.map_map (measurable_const_add mu) (by fun_prop)]
  rw [map_covarianceSqrtCLM_volume hS, Measure.map_smul]
  exact congrArg (covarianceDetSqrtInv S • ·)
    (((MeasurePreserving.id volume).add_left volume mu).map_eq)

/-- The Lebesgue density of `N(μ,S)` when `S` is positive definite.
The standard radial density already contains the factor `(2π)^{-n/2}`;
`covarianceDetSqrtInv` supplies `(det S)^{-1/2}`.

**Book Proposition 3.3.6.** -/
def multivariateGaussianDensity
    (mu : EuclideanSpace ℝ n) (S : Matrix n n ℝ) (hS : S.PosDef)
    (x : EuclideanSpace ℝ n) : ℝ≥0∞ :=
  covarianceDetSqrtInv S *
    (HDP.gaussianRadialDensity (EuclideanSpace ℝ n)
      ((covarianceSqrtEquiv S hS).symm (x - mu)) : ℝ≥0∞)

/-- The density `multivariateGaussianDensity` at parameters `mu`, `S`, and `hS` is measurable; this is `measurable_multivariateGaussianDensity`.

**Lean implementation helper.** -/
lemma measurable_multivariateGaussianDensity
    (mu : EuclideanSpace ℝ n) (S : Matrix n n ℝ) (hS : S.PosDef) :
    Measurable (multivariateGaussianDensity mu S hS) := by
  unfold multivariateGaussianDensity
  apply Measurable.mul measurable_const
  exact ENNReal.continuous_coe.measurable.comp
    ((HDP.measurable_gaussianRadialDensity (EuclideanSpace ℝ n)).comp (by fun_prop))

/-- A nondegenerate multivariate Gaussian is exactly Lebesgue measure with
the determinant-normalized affine Gaussian density.

**Book Proposition 3.3.6.** -/
theorem multivariateGaussian_eq_withDensity
    (mu : EuclideanSpace ℝ n) (S : Matrix n n ℝ) (hS : S.PosDef) :
    multivariateGaussian mu S =
      volume.withDensity (multivariateGaussianDensity mu S hS) := by
  rw [multivariateGaussian]
  change Measure.map (covarianceAffineEquiv mu S hS)
      (stdGaussian (EuclideanSpace ℝ n)) = _
  rw [← HDP.gaussianRadialMeasure_eq_stdGaussian]
  rw [HDP.gaussianRadialMeasure]
  have hrad : Measurable (fun x : EuclideanSpace ℝ n ↦
      (HDP.gaussianRadialDensity (EuclideanSpace ℝ n) x : ℝ≥0∞)) :=
    ENNReal.continuous_coe.measurable.comp
      (HDP.measurable_gaussianRadialDensity (EuclideanSpace ℝ n))
  rw [MeasurableEquiv.map_withDensity
    (covarianceAffineEquiv mu S hS) volume _ hrad]
  rw [map_covarianceAffineEquiv_volume mu hS, withDensity_smul_measure]
  have htransport : Measurable
      ((fun x : EuclideanSpace ℝ n ↦
        (HDP.gaussianRadialDensity (EuclideanSpace ℝ n) x : ℝ≥0∞)) ∘
          (covarianceAffineEquiv mu S hS).symm) :=
    hrad.comp (covarianceAffineEquiv mu S hS).symm.measurable
  rw [← withDensity_smul (covarianceDetSqrtInv S) htransport]
  congr 1
  funext x
  simp [multivariateGaussianDensity, covarianceAffineEquiv_symm_apply,
    Pi.smul_apply, smul_eq_mul]

/-- A positive-definite multivariate Gaussian is absolutely continuous with
respect to Lebesgue measure.

**Lean implementation helper.** -/
theorem multivariateGaussian_absolutelyContinuous_volume
    (mu : EuclideanSpace ℝ n) (S : Matrix n n ℝ) (hS : S.PosDef) :
    multivariateGaussian mu S ≪ (volume : Measure (EuclideanSpace ℝ n)) := by
  rw [multivariateGaussian_eq_withDensity mu S hS]
  exact withDensity_absolutelyContinuous _ _

/-- Gives the coordinatewise evaluation formula for `covarianceSqrtEquiv_symm`.

**Lean implementation helper.** -/
private lemma covarianceSqrtEquiv_symm_apply
    (S : Matrix n n ℝ) (hS : S.PosDef) (y : EuclideanSpace ℝ n) :
    (covarianceSqrtEquiv S hS).symm y =
      Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)⁻¹ y := by
  apply (covarianceSqrtEquiv S hS).injective
  rw [(covarianceSqrtEquiv S hS).apply_symm_apply]
  symm
  change Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)⁻¹ y) = y
  have hu : IsUnit (CFC.sqrt S).det := by
    rw [hS.posSemidef.det_sqrt, RCLike.sqrt_real]
    exact isUnit_iff_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.2 hS.det_pos))
  rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def,
    ← map_mul, Matrix.mul_nonsing_inv _ hu, map_one,
    one_apply_eq_self]

/-- `norm_sq_covarianceSqrtEquiv_symm` identifies `‖(covarianceSqrtEquiv S hS).symm y‖²` with the quadratic form `yᵀ S⁻¹ y`.

**Lean implementation helper.** -/
private lemma norm_sq_covarianceSqrtEquiv_symm
    (S : Matrix n n ℝ) (hS : S.PosDef) (y : EuclideanSpace ℝ n) :
    ‖(covarianceSqrtEquiv S hS).symm y‖ ^ 2 = y ⬝ᵥ S⁻¹ *ᵥ y := by
  rw [covarianceSqrtEquiv_symm_apply, hS.posSemidef.inv_sqrt]
  rw [← real_inner_self_eq_norm_sq]
  rw [← ContinuousLinearMap.adjoint_inner_right, IsSelfAdjoint.adjoint_eq,
    ← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def,
    ← map_mul, CFC.sqrt_mul_sqrt_self _ hS.inv.posSemidef.nonneg,
    inner_toEuclideanCLM]
  exact (CFC.sqrt_nonneg S⁻¹).isSelfAdjoint.map _

/-- Source formula for the preceding density:
`(det S)^{-1/2} (2π)^{-n/2} exp(-⟨S⁻¹(x-μ),x-μ⟩/2)`.
`gaussianRadialNormalizer` is `(2π)^{n/2}`.

**Book Proposition 3.3.6.** -/
lemma multivariateGaussianDensity_eq_ofReal
    (mu x : EuclideanSpace ℝ n) (S : Matrix n n ℝ) (hS : S.PosDef) :
    multivariateGaussianDensity mu S hS x = ENNReal.ofReal
      ((Real.sqrt S.det)⁻¹ *
        (HDP.gaussianRadialNormalizer (EuclideanSpace ℝ n))⁻¹ *
        Real.exp (-(1 / 2 : ℝ) *
          ((x - mu) ⬝ᵥ S⁻¹ *ᵥ (x - mu)))) := by
  rw [multivariateGaussianDensity, covarianceDetSqrtInv]
  rw [← ENNReal.ofReal_coe_nnreal,
    HDP.coe_gaussianRadialDensity]
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  congr 1
  rw [norm_sq_covarianceSqrtEquiv_symm]
  simp only [WithLp.ofLp_sub]
  ring

/-- A positive-semidefinite multivariate Gaussian is degenerate exactly when
its covariance determinant vanishes, equivalently when it has a nonzero
zero-variance direction. This cleanly separates the singular case from the
Lebesgue-density theorem above.

**Lean implementation helper.** -/
theorem multivariateGaussian_degenerate_iff_det_eq_zero
    (mu : EuclideanSpace ℝ n) (S : Matrix n n ℝ) (hS : S.PosSemidef) :
    (∃ v : EuclideanSpace ℝ n, v ≠ 0 ∧
      covarianceBilin (multivariateGaussian mu S) v v = 0) ↔ S.det = 0 := by
  constructor
  · rintro ⟨v, hv, hvar⟩
    by_contra hdet
    have hpos : S.PosDef := hS.posDef_iff_det_ne_zero.mpr hdet
    rw [covarianceBilin_multivariateGaussian hS] at hvar
    have hv' : v.ofLp ≠ 0 := by simpa using hv
    exact (ne_of_gt (hpos.dotProduct_mulVec_pos hv')) hvar
  · intro hdet
    have hnotunit : ¬ IsUnit S := by
      rw [Matrix.isUnit_iff_isUnit_det]
      simpa [isUnit_iff_ne_zero]
    have hnoninj : ¬ Function.Injective S.mulVec := by
      simpa [Matrix.mulVec_injective_iff_isUnit] using hnotunit
    obtain ⟨a, b, heq, hab⟩ := Function.not_injective_iff.mp hnoninj
    refine ⟨WithLp.toLp 2 (a - b), ?_, ?_⟩
    · simpa [sub_ne_zero] using hab
    · rw [covarianceBilin_multivariateGaussian hS]
      change (a - b) ⬝ᵥ S *ᵥ (a - b) = 0
      have hker : S *ᵥ (a - b) = 0 := by
        rw [Matrix.mulVec_sub, heq, sub_self]
      simpa using (hS.dotProduct_mulVec_zero_iff (a - b)).2 hker

/-! ## Sums, uniqueness, and independence -/

/-- A finite sum of independent
Gaussian random vectors is Gaussian.

**Book Corollary 3.3.3.** -/
theorem sum_independent_gaussians_hasGaussianLaw
    {Ω E ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
    {X : ι → Ω → E}
    (hX : ∀ i, HasGaussianLaw (X i) P)
    (h_indep : iIndepFun X P) :
    HasGaussianLaw (fun ω => ∑ i, X i ω) P :=
  h_indep.hasGaussianLaw_fun_sum hX

/-- For independent real Gaussian variables, the sum is Gaussian and its
mean and variance are respectively the sums of the component means and
variances.

**Book Corollary 3.3.3.** -/
theorem sum_independent_gaussians_parameters
    {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [Fintype ι] [IsProbabilityMeasure P]
    {X : ι → Ω → ℝ}
    (hX : ∀ i, HasGaussianLaw (X i) P)
    (hindep : iIndepFun X P) :
    HasGaussianLaw (fun ω => ∑ i, X i ω) P ∧
      (∫ ω, ∑ i, X i ω ∂P) = ∑ i, ∫ ω, X i ω ∂P ∧
      Var[∑ i, X i; P] = ∑ i, Var[X i; P] := by
  refine ⟨sum_independent_gaussians_hasGaussianLaw hX hindep, ?_, ?_⟩
  · rw [integral_finsetSum Finset.univ]
    intro i _
    exact (hX i).integrable
  · exact IndepFun.variance_sum
      (fun i _ => (hX i).memLp_two)
      (fun i _ j _ hij => hindep.indepFun hij)

/-- Gaussian measures are determined
by their mean and covariance, including degenerate covariance operators.

**Book Proposition 3.3.5.** -/
theorem gaussianLaw_unique
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [CompleteSpace E]
    {μ ν : Measure E} [IsGaussian μ] [IsGaussian ν]
    (hmean : μ[id] = ν[id])
    (hcov : covarianceBilin μ = covarianceBilin ν) :
    μ = ν :=
  IsGaussian.ext hmean hcov

/-- Jointly Gaussian real
variables with zero covariance are independent. Mathlib proves this by
characteristic functions, so singular/degenerate Gaussian laws are covered.

**Book Corollary 3.3.7.** -/
theorem jointlyGaussian_independent_of_uncorrelated
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X Y : Ω → ℝ}
    (hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P)
    (hcov : cov[X, Y; P] = 0) :
    IndepFun X Y P :=
  hXY.indepFun_of_covariance_eq_zero hcov

/-- The full independence/uncorrelatedness equivalence for a jointly Gaussian
pair.

**Book Corollary 3.3.7.** -/
theorem jointlyGaussian_independent_iff_uncorrelated
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X Y : Ω → ℝ}
    (hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P) :
    IndepFun X Y P ↔ cov[X, Y; P] = 0 := by
  constructor
  · intro h
    exact h.covariance_eq_zero hXY.fst.memLp_two hXY.snd.memLp_two
  · exact hXY.indepFun_of_covariance_eq_zero

end

end HDP.Chapter3

end Source_08_GaussianVectors

/-! ## Material formerly in `07_IsotropicExamples.lean` -/

section Source_07_IsotropicExamples

/-!
# Isotropic examples from Chapter 3
-/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace MatrixOrder

namespace HDP.Chapter3

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Assemble scalar coordinates into a finite Euclidean random vector.

**Lean implementation helper.** -/
noncomputable def vectorOfCoordinates {n : ℕ} (X : Fin n → Ω → ℝ) :
    Ω → EuclideanSpace ℝ (Fin n) :=
  fun ω => WithLp.toLp 2 (fun i => X i ω)

/-- The standard Gaussian measure has identity uncentered second moment, and
is therefore isotropic in the source's sense.

**Book Section 3.3.** -/
theorem standardGaussian_isIsotropic (n : ℕ) :
    HDP.IsIsotropic (fun x : EuclideanSpace ℝ (Fin n) => x)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  apply HDP.isIsotropic_iff.mpr
  intro i j
  have hmem : MemLp (fun x : EuclideanSpace ℝ (Fin n) => x) 2
      (stdGaussian (EuclideanSpace ℝ (Fin n))) :=
    IsGaussian.memLp_two_id
  have hcoord (k : Fin n) :
      MemLp (fun x : EuclideanSpace ℝ (Fin n) => x k) 2
        (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
    simpa [Function.comp_def] using
      hmem.continuousLinearMap_comp (EuclideanSpace.proj (𝕜 := ℝ) k)
  have hmean (k : Fin n) :
      ∫ x : EuclideanSpace ℝ (Fin n), x k
        ∂stdGaussian (EuclideanSpace ℝ (Fin n)) = 0 := by
    simpa [EuclideanSpace.coe_proj] using
      (integral_strongDual_stdGaussian
        (E := EuclideanSpace ℝ (Fin n)) (EuclideanSpace.proj k))
  have hcov := covariance_eval_multivariateGaussian
    (μ := (0 : EuclideanSpace ℝ (Fin n)))
    (S := (1 : Matrix (Fin n) (Fin n) ℝ))
    Matrix.PosSemidef.one i j
  rw [multivariateGaussian_zero_one] at hcov
  calc
    (∫ x : EuclideanSpace ℝ (Fin n), x i * x j
        ∂stdGaussian (EuclideanSpace ℝ (Fin n))) =
        cov[fun x : EuclideanSpace ℝ (Fin n) => x i,
          fun x => x j; stdGaussian (EuclideanSpace ℝ (Fin n))] := by
      rw [covariance_eq_sub (hcoord i) (hcoord j), hmean i, hmean j]
      simp
    _ = if i = j then 1 else 0 := by
      simpa [Matrix.one_apply] using hcov

/-- Independent centered
coordinates with unit second moment form an isotropic random vector.

**Book Example 3.3.15.** -/
theorem independent_centered_unitVariance_isIsotropic {n : ℕ}
    {X : Fin n → Ω → ℝ}
    (hXm : ∀ i, AEMeasurable (X i) μ)
    (hindep : iIndepFun X μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hsecond : ∀ i, ∫ ω, X i ω ^ 2 ∂μ = 1) :
    HDP.IsIsotropic (vectorOfCoordinates X) μ := by
  apply HDP.isIsotropic_iff.mpr
  intro i j
  change (∫ ω, X i ω * X j ω ∂μ) = if i = j then 1 else 0
  by_cases hij : i = j
  · subst j
    simpa [pow_two] using hsecond i
  · have hprod := (hindep.indepFun hij).integral_fun_mul_eq_mul_integral
      (hXm i).aestronglyMeasurable (hXm j).aestronglyMeasurable
    rw [hprod, hmean i, hmean j]
    simp [hij]

/-- A vector with
independent Rademacher coordinates is isotropic.

**Book Example 3.3.14.** -/
theorem rademacherVector_isIsotropic {n : ℕ} {X : Fin n → Ω → ℝ}
    (hX : ∀ i, HDP.IsRademacher (X i) μ)
    (hindep : iIndepFun X μ) :
    HDP.IsIsotropic (vectorOfCoordinates X) μ := by
  apply independent_centered_unitVariance_isIsotropic
  · exact fun i => (hX i).aemeasurable
  · exact hindep
  · exact fun i => (hX i).integral_eq_zero
  · intro i
    have h := (hX i).integral_comp (fun x : ℝ => x ^ 2)
    norm_num at h
    exact h

end HDP.Chapter3

end Source_07_IsotropicExamples

/-! ## Material formerly in `09_SphericalDistributions.lean` -/

section Source_09_SphericalDistributions

/-!
# Spherical distributions

The probability space is the unit-sphere subtype itself, equipped with the
normalized surface-area measure from `Prelude.Sphere`.  This avoids an
informal "uniform" random variable with an unspecified base space.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace ENNReal NNReal Topology BigOperators

namespace HDP

/-- Canonical inclusion of the unit sphere into its ambient space.

**Lean implementation helper.** -/
def uniformSphereVector
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    Metric.sphere (0 : E) 1 → E :=
  fun x => x

/-- The inclusion `uniformSphereVector E x` of a unit-sphere point has norm one (`norm_uniformSphereVector`).

**Lean implementation helper.** -/
@[simp] theorem norm_uniformSphereVector
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x : Metric.sphere (0 : E) 1) :
    ‖uniformSphereVector E x‖ = 1 := by
  simpa only [uniformSphereVector, mem_sphere_zero_iff_norm, sub_zero] using x.property

/-- The isotropic scaling `√n θ` of a unit-sphere direction.

**Lean implementation helper.** -/
noncomputable def isotropicSphereVector (n : ℕ) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 →
      EuclideanSpace ℝ (Fin n) :=
  fun x => Real.sqrt n • (x : EuclideanSpace ℝ (Fin n))

/-- The isotropically scaled sphere vector has norm `sqrt n`, as stated by `norm_isotropicSphereVector`.

**Lean implementation helper.** -/
@[simp] theorem norm_isotropicSphereVector (n : ℕ)
  (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    ‖isotropicSphereVector n x‖ = Real.sqrt n := by
  have hx : ‖(x : EuclideanSpace ℝ (Fin n))‖ = 1 := by
    simpa only [mem_sphere_zero_iff_norm, sub_zero] using x.property
  simp [isotropicSphereVector, norm_smul, hx, Real.sqrt_nonneg]

end HDP

namespace HDP.Chapter3

noncomputable section

/-- **Uniform spherical distribution is rotation invariant.** This is the
exact measure statement, not merely equality of moments.

**Lean implementation helper.** -/
theorem uniformSphere_rotation_invariant
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (U : E ≃ₗᵢ[ℝ] E) :
    Measure.map (HDP.unitSphereHomeomorph U) (HDP.unitSphereMeasure E) =
      HDP.unitSphereMeasure E :=
  HDP.map_unitSphereMeasure U

/-- The canonical sphere rotation is measure preserving.

**Lean implementation helper.** -/
theorem uniformSphere_rotation_measurePreserving
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (U : E ≃ₗᵢ[ℝ] E) :
    MeasurePreserving (HDP.unitSphereHomeomorph U)
      (HDP.unitSphereMeasure E) (HDP.unitSphereMeasure E) :=
  HDP.measurePreserving_unitSphereHomeomorph U

/-! ## A common probability space for the projective central limit theorem -/

/-- A single product probability space carrying the entire sequence of
independent standard Gaussian coordinates. -/
abbrev ProjectiveOmega := ℕ → ℝ

/-- Defines `projectiveProbability`, the projective probability used in the surrounding construction.

**Lean implementation helper.** -/
def projectiveProbability : Measure ProjectiveOmega :=
  Measure.infinitePi (fun _ : ℕ ↦ gaussianReal 0 1)

local instance : IsProbabilityMeasure projectiveProbability := by
  dsimp [projectiveProbability]
  infer_instance

/-- Defines `projectiveGaussianCoordinate`, the projective gaussian coordinate used in the surrounding construction.

**Lean implementation helper.** -/
def projectiveGaussianCoordinate (i : ℕ) (w : ProjectiveOmega) : ℝ := w i

/-- Defines `projectiveGaussianSquare`, the projective gaussian square used in the surrounding construction.

**Lean implementation helper.** -/
def projectiveGaussianSquare (i : ℕ) (w : ProjectiveOmega) : ℝ := (w i) ^ 2

/-- A coordinate of the projective Gaussian representation has the corresponding scalar Gaussian law.

**Lean implementation helper.** -/
lemma hasLaw_projectiveGaussianCoordinate (i : ℕ) :
    HasLaw (projectiveGaussianCoordinate i) (gaussianReal 0 1)
      projectiveProbability := by
  exact (measurePreserving_eval_infinitePi
    (fun _ : ℕ ↦ gaussianReal 0 1) i).hasLaw

/-- The zeroth squared projective Gaussian coordinate `projectiveGaussianSquare_zero` is integrable under `projectiveProbability`.

**Lean implementation helper.** -/
lemma integrable_projectiveGaussianSquare_zero :
    Integrable (projectiveGaussianSquare 0) projectiveProbability := by
  have h : MemLp (projectiveGaussianCoordinate 0) 2 projectiveProbability :=
    (memLp_id_gaussianReal' 2 (by simp)).comp_measurePreserving
      (measurePreserving_eval_infinitePi
        (fun _ : ℕ ↦ gaussianReal 0 1) 0)
  exact h.integrable_sq

/-- The second moment of the zeroth projective Gaussian coordinate is one (`integral_projectiveGaussianSquare_zero`).

**Lean implementation helper.** -/
lemma integral_projectiveGaussianSquare_zero :
    ∫ w, projectiveGaussianSquare 0 w ∂projectiveProbability = 1 := by
  have hmem : MemLp (id : ℝ → ℝ) 2 (gaussianReal 0 1) :=
    memLp_id_gaussianReal' 2 (by simp)
  have hv := variance_eq_sub hmem
  have hs : ∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 1) = 1 := by
    simpa using hv.symm
  rw [show projectiveGaussianSquare 0 =
      (fun x : ℝ ↦ x ^ 2) ∘ projectiveGaussianCoordinate 0 by rfl,
    (hasLaw_projectiveGaussianCoordinate 0).integral_comp (by fun_prop)]
  exact hs

/-- The coordinate maps on the projective Gaussian product space are mutually independent (`iIndep_projectiveGaussianCoordinate`).

**Lean implementation helper.** -/
lemma iIndep_projectiveGaussianCoordinate :
    iIndepFun projectiveGaussianCoordinate projectiveProbability := by
  exact iIndepFun_infinitePi
    (P := fun _ : ℕ ↦ gaussianReal 0 1)
    (X := fun (_ : ℕ) (x : ℝ) ↦ x) (fun _ ↦ measurable_id)

/-- The squared coordinate maps on the projective Gaussian product space are mutually independent (`iIndep_projectiveGaussianSquare`).

**Lean implementation helper.** -/
lemma iIndep_projectiveGaussianSquare :
    iIndepFun projectiveGaussianSquare projectiveProbability := by
  exact iIndep_projectiveGaussianCoordinate.comp
    (fun _ : ℕ ↦ (fun x : ℝ ↦ x ^ 2)) (fun _ ↦ by fun_prop)

/-- The squared projective Gaussian coordinate has the stated ratio representation.

**Lean implementation helper.** -/
lemma ident_projectiveGaussianSquare (i : ℕ) :
    IdentDistrib (projectiveGaussianSquare i) (projectiveGaussianSquare 0)
      projectiveProbability projectiveProbability := by
  change IdentDistrib (fun w : ProjectiveOmega ↦ w i ^ 2)
    (fun w : ProjectiveOmega ↦ w 0 ^ 2)
      projectiveProbability projectiveProbability
  exact ((hasLaw_projectiveGaussianCoordinate i).identDistrib
    (hasLaw_projectiveGaussianCoordinate 0)).sq

/-- The empirical average of squared projective Gaussian coordinates has the required almost-everywhere identity.

**Lean implementation helper.** -/
lemma projective_average_sq_ae :
    ∀ᵐ w ∂projectiveProbability, Tendsto
      (fun n : ℕ ↦
        (∑ i ∈ Finset.range n, projectiveGaussianSquare i w) / (n : ℝ))
      atTop (nhds 1) := by
  have h := strong_law_ae_real projectiveGaussianSquare
    integrable_projectiveGaussianSquare_zero
    (fun _ _ hij ↦ iIndep_projectiveGaussianSquare.indepFun hij)
    ident_projectiveGaussianSquare
  simpa [integral_projectiveGaussianSquare_zero] using h

/-- Defines `projectiveDenominator`, the projective denominator used in the surrounding construction.

**Lean implementation helper.** -/
def projectiveDenominator (n : ℕ) (w : ProjectiveOmega) : ℝ :=
  Real.sqrt ((∑ i ∈ Finset.range n, projectiveGaussianSquare i w) / (n : ℝ))

/-- The projective Gaussian denominator agrees almost everywhere with the square root of the empirical square average.

**Lean implementation helper.** -/
lemma projectiveDenominator_ae :
    ∀ᵐ w ∂projectiveProbability,
      Tendsto (fun n ↦ projectiveDenominator n w) atTop (nhds 1) := by
  filter_upwards [projective_average_sq_ae] with w hw
  simpa [projectiveDenominator, Function.comp_def] using
    (Real.continuous_sqrt.tendsto 1).comp hw

/-- The self-normalized first Gaussian coordinate. Its law is the law of a
scaled coordinate of a uniform point on the sphere, proved below.

**Lean implementation helper.** -/
def projectiveRatio (n : ℕ) (w : ProjectiveOmega) : ℝ :=
  projectiveGaussianCoordinate 0 w / projectiveDenominator n w

/-- The normalized projective coordinate agrees almost everywhere with the ratio of one Gaussian coordinate to the empirical norm.

**Lean implementation helper.** -/
lemma projectiveRatio_ae :
    ∀ᵐ w ∂projectiveProbability,
      Tendsto (fun n ↦ projectiveRatio n w) atTop
        (nhds (projectiveGaussianCoordinate 0 w)) := by
  filter_upwards [projectiveDenominator_ae] with w hw
  change Tendsto
    ((fun _n : ℕ ↦ projectiveGaussianCoordinate 0 w) /
      fun n ↦ projectiveDenominator n w) atTop
        (nhds (projectiveGaussianCoordinate 0 w))
  have hconst : Tendsto
      (fun _n : ℕ ↦ projectiveGaussianCoordinate 0 w) atTop
        (nhds (projectiveGaussianCoordinate 0 w)) := tendsto_const_nhds
  simpa using hconst.div hw (by norm_num : (1 : ℝ) ≠ 0)

/-- Shows that `projectiveRatio` is almost everywhere measurable.

**Lean implementation helper.** -/
lemma projectiveRatio_aemeasurable (n : ℕ) :
    AEMeasurable (projectiveRatio n) projectiveProbability := by
  apply Measurable.aemeasurable
  change Measurable (fun w : ProjectiveOmega ↦ w 0 /
    Real.sqrt ((∑ i ∈ Finset.range n, (w i) ^ 2) / (n : ℝ)))
  fun_prop

/-- The normalized projective coordinate converges in distribution to a standard Gaussian.

**Lean implementation helper.** -/
theorem projectiveRatio_tendstoInDistribution :
    TendstoInDistribution projectiveRatio atTop
      (projectiveGaussianCoordinate 0) (fun _ ↦ projectiveProbability)
      projectiveProbability := by
  exact tendstoInDistribution_of_ae_tendsto projectiveRatio_aemeasurable
    (hasLaw_projectiveGaussianCoordinate 0).aemeasurable projectiveRatio_ae

/-- Bounds `standardGaussianPDF` above by `one`.

**Lean implementation helper.** -/
lemma standardGaussianPDF_le_one (x : ℝ) : gaussianPDFReal 0 1 x ≤ 1 := by
  change (Real.sqrt (2 * Real.pi * (1 : ℝ)))⁻¹ *
      Real.exp (-((x - 0) ^ 2) / (2 * (1 : ℝ))) ≤ 1
  have hsqrt : 1 ≤ Real.sqrt (2 * Real.pi * (1 : ℝ)) := by
    rw [mul_one, ← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by nlinarith [Real.pi_gt_three])
  have hfac : (Real.sqrt (2 * Real.pi * (1 : ℝ)))⁻¹ ≤ 1 := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hsqrt
  have hexp : Real.exp (-((x - 0) ^ 2) / (2 * (1 : ℝ))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    norm_num
    nlinarith [sq_nonneg x]
  calc
    (Real.sqrt (2 * Real.pi * (1 : ℝ)))⁻¹ *
        Real.exp (-((x - 0) ^ 2) / (2 * (1 : ℝ)))
      ≤ 1 * 1 := mul_le_mul hfac hexp (Real.exp_pos _).le (by positivity)
    _ = 1 := by ring

/-- Bounds `standardGaussian_Ioc_real` above by `sub`.

**Lean implementation helper.** -/
lemma standardGaussian_Ioc_real_le_sub {a b : ℝ} (hab : a ≤ b) :
    (gaussianReal 0 1).real (Set.Ioc a b) ≤ b - a := by
  rw [measureReal_def,
    gaussianReal_apply_eq_integral 0 (by norm_num) (Set.Ioc a b),
    ENNReal.toReal_ofReal]
  · calc
      ∫ x in Set.Ioc a b, gaussianPDFReal 0 1 x
          ≤ ∫ _x in Set.Ioc a b, (1 : ℝ) := by
            apply setIntegral_mono_on
            · exact (integrable_gaussianPDFReal 0 1).integrableOn
            · exact integrableOn_const (by simp)
            · exact measurableSet_Ioc
            · intro x _
              exact standardGaussianPDF_le_one x
      _ = b - a := by simp [hab]
  · exact integral_nonneg_of_ae
      (ae_restrict_of_ae (ae_of_all _ (gaussianPDFReal_nonneg 0 1)))

/-- Quantitative CDF error decomposition used in the projective-CLT proof.

**Book Equation (3.18).** -/
lemma standardGaussian_cdf_increment_le {a b : ℝ} (hab : a ≤ b) :
    (gaussianReal 0 1).real (Set.Iic b) -
        (gaussianReal 0 1).real (Set.Iic a) ≤ b - a := by
  have hu := measureReal_union
    (μ := gaussianReal 0 1) (s₁ := Set.Iic a) (s₂ := Set.Ioc a b)
    (Set.Iic_disjoint_Ioc le_rfl) measurableSet_Ioc
    (by finiteness) (by finiteness)
  rw [Set.Iic_union_Ioc_eq_Iic hab] at hu
  rw [hu]
  simpa using standardGaussian_Ioc_real_le_sub hab

/-- The metric thickening of a lower half-line is the lower half-line with its endpoint shifted by the radius.

**Lean implementation helper.** -/
lemma thickening_Iic (t δ : ℝ) (hδ : 0 < δ) :
    Metric.thickening δ (Set.Iic t) = Set.Iio (t + δ) := by
  ext x
  rw [Metric.mem_thickening_iff]
  constructor
  · rintro ⟨z, hz, hxz⟩
    rw [Set.mem_Iic] at hz
    rw [Real.dist_eq] at hxz
    have hxz' : x - z < δ := (le_abs_self (x - z)).trans_lt hxz
    exact Set.mem_Iio.mpr (by linarith)
  · intro hx
    rw [Set.mem_Iio] at hx
    by_cases hxt : x ≤ t
    · exact ⟨x, Set.mem_Iic.mpr hxt, by simpa using hδ⟩
    · refine ⟨t, Set.mem_Iic.mpr le_rfl, ?_⟩
      rw [Real.dist_eq, abs_of_pos (by linarith)]
      linarith

/-- Defines `projectiveRatioPM`, the projective ratio pm used in the surrounding construction.

**Lean implementation helper.** -/
def projectiveRatioPM (n : ℕ) : ProbabilityMeasure ℝ :=
  ⟨projectiveProbability.map (projectiveRatio n),
    Measure.isProbabilityMeasure_map (projectiveRatio_aemeasurable n)⟩

/-- Defines `standardGaussianPM`, the standard gaussian pm used in the surrounding construction.

**Lean implementation helper.** -/
def standardGaussianPM : ProbabilityMeasure ℝ :=
  ⟨gaussianReal 0 1, inferInstance⟩

/-- The positive/negative projective ratio converges in distribution to the standard Gaussian law.

**Lean implementation helper.** -/
lemma projectiveRatioPM_tendsto :
    Tendsto projectiveRatioPM atTop (nhds standardGaussianPM) := by
  convert projectiveRatio_tendstoInDistribution.tendsto using 1 <;>
    ext <;> simp [projectiveRatioPM, standardGaussianPM,
      (hasLaw_projectiveGaussianCoordinate 0).map_eq]

/-- The Lévy–Prokhorov distance from the projective ratio law to the standard Gaussian law tends to zero.

**Lean implementation helper.** -/
lemma projectiveRatioPM_levyProkhorovDist_tendsto_zero :
    Tendsto (fun n ↦ levyProkhorovDist
      (projectiveRatioPM n : Measure ℝ) (standardGaussianPM : Measure ℝ))
      atTop (nhds 0) := by
  have ht : Tendsto
      (fun n ↦ LevyProkhorov.ofMeasure (projectiveRatioPM n)) atTop
      (nhds (LevyProkhorov.ofMeasure standardGaussianPM)) :=
    LevyProkhorov.continuous_ofMeasure_probabilityMeasure.continuousAt.tendsto.comp
      projectiveRatioPM_tendsto
  have hconst : Tendsto
      (fun _n : ℕ ↦ LevyProkhorov.ofMeasure standardGaussianPM) atTop
      (nhds (LevyProkhorov.ofMeasure standardGaussianPM)) := tendsto_const_nhds
  have hd := ht.dist hconst
  simpa [LevyProkhorov.dist_probabilityMeasure_def] using hd

/-- Quantitative Portmanteau consequence: convergence of the projective ratio
is uniform over every real CDF threshold.

**Book Theorem 3.3.9.** -/
theorem projectiveRatio_uniform_cdf :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ t : ℝ,
      |(projectiveProbability.map (projectiveRatio n)).real (Set.Iic t) -
        (gaussianReal 0 1).real (Set.Iic t)| < ε := by
  intro ε hε
  let δ := ε / 3
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hevent : ∀ᶠ n in atTop,
      levyProkhorovDist (projectiveRatioPM n : Measure ℝ)
        (standardGaussianPM : Measure ℝ) < δ :=
    projectiveRatioPM_levyProkhorovDist_tendsto_zero.eventually_lt_const hδ
  filter_upwards [hevent] with n hn
  intro t
  have hED : levyProkhorovEDist
      (projectiveProbability.map (projectiveRatio n)) (gaussianReal 0 1) <
        ENNReal.ofReal δ := by
    calc
      levyProkhorovEDist
          (projectiveProbability.map (projectiveRatio n)) (gaussianReal 0 1) =
          ENNReal.ofReal (levyProkhorovEDist
            (projectiveProbability.map (projectiveRatio n))
            (gaussianReal 0 1)).toReal := by
              rw [ENNReal.ofReal_toReal (levyProkhorovEDist_ne_top _ _)]
      _ < ENNReal.ofReal δ := (ENNReal.ofReal_lt_ofReal_iff hδ).2 (by
        simpa [projectiveRatioPM, standardGaussianPM, levyProkhorovDist] using hn)
  have hupENN :
      (projectiveProbability.map (projectiveRatio n)) (Set.Iic t) ≤
        (gaussianReal 0 1) (Set.Iic (t + δ)) + ENNReal.ofReal δ := by
    have h := left_measure_le_of_levyProkhorovEDist_lt
      hED (B := Set.Iic t) measurableSet_Iic
    rw [ENNReal.toReal_ofReal hδ.le] at h
    rw [thickening_Iic t δ hδ] at h
    exact h.trans (add_le_add (measure_mono Set.Iio_subset_Iic_self) le_rfl)
  have hupReal := ENNReal.toReal_mono (by finiteness) hupENN
  rw [ENNReal.toReal_add (by finiteness) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hδ.le] at hupReal
  change (projectiveProbability.map (projectiveRatio n)).real (Set.Iic t) ≤
    (gaussianReal 0 1).real (Set.Iic (t + δ)) + δ at hupReal
  have hlowENN :
      (gaussianReal 0 1) (Set.Iic (t - δ)) ≤
        (projectiveProbability.map (projectiveRatio n)) (Set.Iic t) +
          ENNReal.ofReal δ := by
    have hED' : levyProkhorovEDist (gaussianReal 0 1)
        (projectiveProbability.map (projectiveRatio n)) < ENNReal.ofReal δ := by
      simpa [levyProkhorovEDist_comm] using hED
    have h := left_measure_le_of_levyProkhorovEDist_lt
      hED' (B := Set.Iic (t - δ)) measurableSet_Iic
    rw [ENNReal.toReal_ofReal hδ.le] at h
    rw [thickening_Iic (t - δ) δ hδ] at h
    have heq : t - δ + δ = t := by ring
    rw [heq] at h
    exact h.trans (add_le_add (measure_mono Set.Iio_subset_Iic_self) le_rfl)
  have hlowReal := ENNReal.toReal_mono (by finiteness) hlowENN
  rw [ENNReal.toReal_add (by finiteness) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hδ.le] at hlowReal
  change (gaussianReal 0 1).real (Set.Iic (t - δ)) ≤
    (projectiveProbability.map (projectiveRatio n)).real (Set.Iic t) + δ at hlowReal
  have hincUp := standardGaussian_cdf_increment_le
    (a := t) (b := t + δ) (by linarith)
  have hincLow := standardGaussian_cdf_increment_le
    (a := t - δ) (b := t) (by linarith)
  have hδeq : 3 * δ = ε := by
    dsimp [δ]
    ring
  rw [abs_lt]
  constructor <;> nlinarith

/-! ## Identification with uniform spherical marginals -/

/-- The vector formed by the first `n` coordinates on the common Gaussian
product space.

**Lean implementation helper.** -/
def projectiveGaussianVector (n : ℕ) (w : ProjectiveOmega) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i : Fin n ↦ w i)

/-- The vector `projectiveGaussianVector` of the first `n` projective Gaussian coordinates is measurable (`measurable_projectiveGaussianVector`).

**Lean implementation helper.** -/
lemma measurable_projectiveGaussianVector (n : ℕ) :
    Measurable (projectiveGaussianVector n) := by
  change Measurable (fun w : ProjectiveOmega ↦
    WithLp.toLp 2 (fun i : Fin n ↦ w i))
  fun_prop

/-- The first `n` coordinates have Mathlib's standard multivariate Gaussian
law.

**Lean implementation helper.** -/
theorem map_projectiveGaussianVector (n : ℕ) :
    Measure.map (projectiveGaussianVector n) projectiveProbability =
      stdGaussian (EuclideanSpace ℝ (Fin n)) := by
  rw [show projectiveGaussianVector n =
      (WithLp.toLp 2) ∘ (fun w : ProjectiveOmega ↦ fun i : Fin n ↦ w i) by rfl]
  rw [← Measure.map_map (by fun_prop) (by fun_prop)]
  rw [projectiveProbability]
  rw [Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective]
  rw [Measure.infinitePi_eq_pi, map_pi_eq_stdGaussian]

/-- The normalized Gaussian vector has the projective spherical law.

**Lean implementation helper.** -/
lemma hasLaw_projectiveGaussianVector (n : ℕ) :
    HasLaw (projectiveGaussianVector n)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) projectiveProbability :=
  ⟨(measurable_projectiveGaussianVector n).aemeasurable,
    map_projectiveGaussianVector n⟩

/-- A unit vector in the first coordinate of `ℝⁿ`.

**Lean implementation helper.** -/
def firstUnitDirection (n : ℕ) (hn : 0 < n) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
  ⟨EuclideanSpace.single ⟨0, hn⟩ 1, by
    simp⟩

/-- The `√n`-scaled projection of a sphere point onto a unit direction.

**Lean implementation helper.** -/
def sphericalProjection (n : ℕ)
    (v : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) : ℝ :=
  Real.sqrt n * inner ℝ (x : EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin n))

/-- For every unit direction `v`, the scaled spherical coordinate `sphericalProjection` at parameters `n` and `v` is measurable.

**Lean implementation helper.** -/
lemma measurable_sphericalProjection (n : ℕ)
    (v : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    Measurable (sphericalProjection n v) := by
  change Measurable (fun x : Metric.sphere
    (0 : EuclideanSpace ℝ (Fin n)) 1 ↦
      Real.sqrt n * inner ℝ (x : EuclideanSpace ℝ (Fin n))
        (v : EuclideanSpace ℝ (Fin n)))
  fun_prop

/-- Rotation invariance makes the distribution of a spherical projection
independent of the chosen unit direction.

**Lean implementation helper.** -/
theorem map_sphericalProjection_eq (n : ℕ)
    (v u : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    Measure.map (sphericalProjection n v)
        (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))) =
      Measure.map (sphericalProjection n u)
        (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))) := by
  let U : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
    Submodule.reflection
      (Submodule.orthogonal (ℝ ∙ ((v : EuclideanSpace ℝ (Fin n)) -
        (u : EuclideanSpace ℝ (Fin n)))))
  have hv : ‖(v : EuclideanSpace ℝ (Fin n))‖ = 1 := by
    simpa only [mem_sphere_zero_iff_norm, sub_zero] using v.property
  have hu : ‖(u : EuclideanSpace ℝ (Fin n))‖ = 1 := by
    simpa only [mem_sphere_zero_iff_norm, sub_zero] using u.property
  have hUvu : U (v : EuclideanSpace ℝ (Fin n)) =
      (u : EuclideanSpace ℝ (Fin n)) := by
    exact Submodule.reflection_sub (hv.trans hu.symm)
  have hfun : sphericalProjection n v =
      sphericalProjection n u ∘ HDP.unitSphereHomeomorph U := by
    funext x
    change Real.sqrt n * inner ℝ (x : EuclideanSpace ℝ (Fin n)) v =
      Real.sqrt n * inner ℝ (U (x : EuclideanSpace ℝ (Fin n))) u
    rw [← hUvu, U.inner_map_map]
  rw [hfun, ← Measure.map_map
    (measurable_sphericalProjection n u)
    (HDP.unitSphereHomeomorph U).measurable]
  rw [HDP.map_unitSphereMeasure U]

/-! ## Proposition 3.3.8: a sphere is isotropic -/

/-- The standard coordinate direction, regarded as a point of the unit
sphere.

**Lean implementation helper.** -/
def sphereCoordinateDirection {n : ℕ} (i : Fin n) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
  ⟨EuclideanSpace.single i 1, by simp⟩

/-- Defines `sphereCoordinateSignFlip`, the sphere coordinate sign flip used in the surrounding construction.

**Lean implementation helper.** -/
private def sphereCoordinateSignFlip {n : ℕ} (i : Fin n) :
    EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearIsometryEquiv.piLpCongrRight 2
    (fun j : Fin n ↦ if j = i then LinearIsometryEquiv.neg ℝ else
      LinearIsometryEquiv.refl ℝ ℝ)

/-- Each coordinate of the spherical projection is the corresponding Gaussian coordinate divided by the Gaussian norm.

**Lean implementation helper.** -/
@[simp] lemma sphericalProjection_coordinate {n : ℕ} (i : Fin n)
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    sphericalProjection n (sphereCoordinateDirection i) x =
      Real.sqrt n * (x : EuclideanSpace ℝ (Fin n)) i := by
  simp only [sphericalProjection, sphereCoordinateDirection]
  rw [EuclideanSpace.inner_single_right]
  simp

/-- Bounds `abs_sphericalProjection` above by `sqrt`.

**Lean implementation helper.** -/
lemma abs_sphericalProjection_le_sqrt {n : ℕ}
    (v x : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    |sphericalProjection n v x| ≤ Real.sqrt n := by
  rw [sphericalProjection, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hinner := abs_real_inner_le_norm
    (x : EuclideanSpace ℝ (Fin n)) (v : EuclideanSpace ℝ (Fin n))
  have hx : ‖(x : EuclideanSpace ℝ (Fin n))‖ = 1 := by
    simpa only [mem_sphere_zero_iff_norm, sub_zero] using x.property
  have hv : ‖(v : EuclideanSpace ℝ (Fin n))‖ = 1 := by
    simpa only [mem_sphere_zero_iff_norm, sub_zero] using v.property
  simpa [hx, hv] using
    mul_le_mul_of_nonneg_left hinner (Real.sqrt_nonneg n)

/-- For unit directions `u` and `v`, the product `sphericalProjection_mul` of their scaled spherical coordinates is integrable under uniform sphere measure.

**Lean implementation helper.** -/
private lemma integrable_sphericalProjection_mul {n : ℕ} (hn : 0 < n)
    (v u : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    Integrable (fun x => sphericalProjection n v x * sphericalProjection n u x)
      (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  apply Integrable.of_bound
    ((measurable_sphericalProjection n v).mul
      (measurable_sphericalProjection n u)).aestronglyMeasurable (n : ℝ)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_mul]
  calc
    |sphericalProjection n v x| * |sphericalProjection n u x|
        ≤ Real.sqrt n * Real.sqrt n :=
      mul_le_mul (abs_sphericalProjection_le_sqrt v x)
        (abs_sphericalProjection_le_sqrt u x) (abs_nonneg _)
        (Real.sqrt_nonneg _)
    _ = (n : ℝ) := by rw [← pow_two, Real.sq_sqrt]; positivity

/-- The squared spherical projections onto any two unit directions have the same integral (`integral_sphericalProjection_sq_eq`).

**Lean implementation helper.** -/
private lemma integral_sphericalProjection_sq_eq {n : ℕ}
    (v u : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    (∫ x, sphericalProjection n v x ^ 2
      ∂HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))) =
    ∫ x, sphericalProjection n u x ^ 2
      ∂HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)) := by
  let σ := HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
  calc
    (∫ x, sphericalProjection n v x ^ 2 ∂σ) =
        ∫ y, y ^ 2 ∂Measure.map (sphericalProjection n v) σ := by
      rw [integral_map (measurable_sphericalProjection n v).aemeasurable
        (by fun_prop)]
    _ = ∫ y, y ^ 2 ∂Measure.map (sphericalProjection n u) σ := by
      rw [map_sphericalProjection_eq n v u]
    _ = ∫ x, sphericalProjection n u x ^ 2 ∂σ := by
      rw [integral_map (measurable_sphericalProjection n u).aemeasurable
        (by fun_prop)]

/-- The squared coordinates of a spherical projection sum to one.

**Lean implementation helper.** -/
private lemma sum_sphericalProjection_coordinate_sq {n : ℕ}
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    (∑ i : Fin n, sphericalProjection n (sphereCoordinateDirection i) x ^ 2) = n := by
  simp_rw [sphericalProjection_coordinate, mul_pow]
  rw [← Finset.mul_sum, Real.sq_sqrt (Nat.cast_nonneg n)]
  rw [← EuclideanSpace.real_norm_sq_eq]
  have hx : ‖(x : EuclideanSpace ℝ (Fin n))‖ = 1 := by
    simpa only [mem_sphere_zero_iff_norm, sub_zero] using x.property
  rw [hx]
  simp

/-- Every coordinate of the `√n`-scaled uniform sphere vector has second
moment one.

**Book Proposition 3.3.8.** -/
theorem sphericalProjection_coordinate_secondMoment {n : ℕ} (hn : 0 < n)
    (i : Fin n) :
    (∫ x, sphericalProjection n (sphereCoordinateDirection i) x ^ 2
      ∂HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))) = 1 := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let σ := HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
  have hint (k : Fin n) : Integrable
      (fun x => sphericalProjection n (sphereCoordinateDirection k) x ^ 2) σ := by
    simpa only [pow_two] using
      (integrable_sphericalProjection_mul hn (sphereCoordinateDirection k)
        (sphereCoordinateDirection k))
  have hsum := integral_finsetSum (Finset.univ : Finset (Fin n))
    (fun k _ => hint k)
  have hsum' :
      (∑ k : Fin n, ∫ x, sphericalProjection n (sphereCoordinateDirection k) x ^ 2 ∂σ) =
        (n : ℝ) := by
    rw [← hsum]
    simp_rw [sum_sphericalProjection_coordinate_sq]
    simp [σ]
  have hall (k : Fin n) :
      (∫ x, sphericalProjection n (sphereCoordinateDirection k) x ^ 2 ∂σ) =
        ∫ x, sphericalProjection n (sphereCoordinateDirection i) x ^ 2 ∂σ :=
    integral_sphericalProjection_sq_eq _ _
  simp_rw [hall] at hsum'
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hsum'
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  apply mul_left_cancel₀ hn0
  simpa using hsum'

/-- Distinct coordinates of the isotropic sphere distribution have zero cross second moment.

**Lean implementation helper.** -/
private lemma isotropicSphere_cross_secondMoment {n : ℕ}
    (i j : Fin n) (hij : i ≠ j) :
    (∫ x, HDP.isotropicSphereVector n x i * HDP.isotropicSphereVector n x j
      ∂HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))) = 0 := by
  let U := sphereCoordinateSignFlip i
  let σ := HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
  let f := fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
    HDP.isotropicSphereVector n x i * HDP.isotropicSphereVector n x j
  have hpres := uniformSphere_rotation_measurePreserving U
  have hcomp := hpres.integral_comp
    (HDP.unitSphereHomeomorph U).measurableEmbedding f
  have hfun : f ∘ HDP.unitSphereHomeomorph U = fun x => -f x := by
    funext x
    have hiU : U (x : EuclideanSpace ℝ (Fin n)) i =
        -(x : EuclideanSpace ℝ (Fin n)) i := by
      simp [U, sphereCoordinateSignFlip,
        LinearIsometryEquiv.piLpCongrRight_apply]
    have hjU : U (x : EuclideanSpace ℝ (Fin n)) j =
        (x : EuclideanSpace ℝ (Fin n)) j := by
      simp [U, sphereCoordinateSignFlip,
        LinearIsometryEquiv.piLpCongrRight_apply, Ne.symm hij]
    simp only [Function.comp_apply, f, HDP.isotropicSphereVector,
      HDP.unitSphereHomeomorph]
    change (Real.sqrt n * U (x : EuclideanSpace ℝ (Fin n)) i) *
        (Real.sqrt n * U (x : EuclideanSpace ℝ (Fin n)) j) =
      -((Real.sqrt n * (x : EuclideanSpace ℝ (Fin n)) i) *
        (Real.sqrt n * (x : EuclideanSpace ℝ (Fin n)) j))
    rw [hiU, hjU]
    ring
  have hneg : (∫ x, -f x ∂σ) = ∫ x, f x ∂σ := by
    calc
      (∫ x, -f x ∂σ) =
          ∫ x, f (HDP.unitSphereHomeomorph U x) ∂σ := by
        apply integral_congr_ae
        exact ae_of_all _ fun x => (congrFun hfun x).symm
      _ = ∫ x, f x ∂σ := hcomp
  rw [integral_neg] at hneg
  change (∫ x, f x ∂σ) = 0
  linarith [hneg]

/-- In positive
dimension, the uniform vector on the sphere of radius `√n`, represented as
`√n • θ` with `θ` on the unit sphere, has second-moment matrix `I`.

**Book Proposition 3.3.8.** -/
theorem sphere_isIsotropic (n : ℕ) (hn : 0 < n) :
    HDP.IsIsotropic (HDP.isotropicSphereVector n)
      (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))) := by
  apply HDP.isIsotropic_iff.mpr
  intro i j
  by_cases hij : i = j
  · subst j
    have h := sphericalProjection_coordinate_secondMoment hn i
    simpa [sphericalProjection_coordinate, HDP.isotropicSphereVector,
      pow_two] using h
  · rw [if_neg hij]
    exact isotropicSphere_cross_secondMoment i j hij

/-- Two independent uniform directions on the unit sphere have exact squared
inner-product mean `1/n`.

**Book Equation (3.14), moment identity preceding the display.** -/
theorem uniformSphere_inner_sq_expectation (n : ℕ) (hn : 0 < n) :
    (∫ z : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ×
        Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      inner ℝ (HDP.uniformSphereVector _ z.1)
        (HDP.uniformSphereVector _ z.2) ^ 2
      ∂(HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))).prod
        (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)))) =
      1 / (n : ℝ) := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  let sigma := HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
  let X := HDP.isotropicSphereVector n
  have hcoord (i j : Fin n) :
      Integrable (fun x => X x i * X x j) sigma := by
    refine Integrable.of_bound ?_ (n : ℝ) ?_
    · apply Continuous.aestronglyMeasurable
      dsimp only [X, HDP.isotropicSphereVector, HDP.uniformSphereVector]
      fun_prop
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_mul]
    have hi : |X x i| ≤ Real.sqrt n := by
      calc
        |X x i| ≤ ‖X x‖ := by
          simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (X x) i
        _ = Real.sqrt n := HDP.norm_isotropicSphereVector n x
    have hj : |X x j| ≤ Real.sqrt n := by
      calc
        |X x j| ≤ ‖X x‖ := by
          simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (X x) j
        _ = Real.sqrt n := HDP.norm_isotropicSphereVector n x
    calc
      |X x i| * |X x j| ≤ Real.sqrt n * Real.sqrt n :=
        mul_le_mul hi hj (abs_nonneg _) (Real.sqrt_nonneg _)
      _ = (n : ℝ) := by rw [← pow_two, Real.sq_sqrt]; positivity
  have hscaled := secondMoment_independent_copy_inner_sq
    (μ := sigma) X hcoord
  have hmatrix : HDP.secondMomentMatrix X sigma = 1 := by
    ext i j
    exact HDP.isIsotropic_iff.mp (sphere_isIsotropic n hn) i j
  rw [hmatrix] at hscaled
  have hscaled' :
      (∫ z : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ×
          Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        inner ℝ (X z.1) (X z.2) ^ 2 ∂sigma.prod sigma) = (n : ℝ) := by
    simpa [Matrix.one_apply] using hscaled
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hpoint (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ×
      Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
      inner ℝ (X z.1) (X z.2) ^ 2 =
        (n : ℝ) ^ 2 *
          inner ℝ (HDP.uniformSphereVector _ z.1)
            (HDP.uniformSphereVector _ z.2) ^ 2 := by
    simp only [X, HDP.isotropicSphereVector, HDP.uniformSphereVector,
      inner_smul_left, inner_smul_right]
    simp only [starRingEnd_apply, star_trivial]
    rw [← mul_assoc, Real.mul_self_sqrt hnR.le]
    ring
  rw [integral_congr_ae (ae_of_all _ hpoint), integral_const_mul] at hscaled'
  change (∫ z, inner ℝ (HDP.uniformSphereVector _ z.1)
      (HDP.uniformSphereVector _ z.2) ^ 2 ∂sigma.prod sigma) = _
  apply mul_left_cancel₀ (pow_ne_zero 2 hnR.ne')
  rw [hscaled']
  field_simp

/-- Quantitative high-probability form of almost orthogonality: for every
`C>0`, two independent uniform unit directions satisfy
`|⟨X,Y⟩| < C/√n` outside a set of probability at most `1/C²`.

**Book Equation (3.14).** -/
theorem uniformSphere_almost_orthogonal (n : ℕ) (hn : 0 < n)
    {C : ℝ} (hC : 0 < C) :
    let sigma := HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
    (sigma.prod sigma).real
      {z | C / Real.sqrt n ≤
        |inner ℝ (HDP.uniformSphereVector _ z.1)
          (HDP.uniformSphereVector _ z.2)|} ≤ 1 / C ^ 2 := by
  dsimp only
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  let sigma := HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
  let f : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ×
      Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 → ℝ :=
    fun z => inner ℝ (HDP.uniformSphereVector _ z.1)
      (HDP.uniformSphereVector _ z.2) ^ 2
  have hfint : Integrable f (sigma.prod sigma) := by
    refine Integrable.of_bound ?_ 1 ?_
    · exact (by fun_prop : Continuous f).aestronglyMeasurable
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hinner : |inner ℝ (z.1 : EuclideanSpace ℝ (Fin n)) z.2| ≤ 1 := by
      calc
        _ ≤ ‖(z.1 : EuclideanSpace ℝ (Fin n))‖ *
            ‖(z.2 : EuclideanSpace ℝ (Fin n))‖ := abs_real_inner_le_norm _ _
        _ = 1 := by simp
    change inner ℝ (z.1 : EuclideanSpace ℝ (Fin n)) z.2 ^ 2 ≤ 1
    simpa only [sq_abs, one_pow] using
      (sq_le_sq₀ (abs_nonneg
        (inner ℝ (z.1 : EuclideanSpace ℝ (Fin n)) z.2)) zero_le_one).mpr hinner
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsqrtn : 0 < Real.sqrt n := Real.sqrt_pos.2 hnR
  have ht : 0 < (C / Real.sqrt n) ^ 2 := sq_pos_of_pos (div_pos hC hsqrtn)
  have hmarkov := HDP.Chapter1.markov_inequality
    (μ := sigma.prod sigma) (X := f)
    (Filter.Eventually.of_forall fun _ => sq_nonneg _) hfint ht
  have hset : {z | C / Real.sqrt n ≤
      |inner ℝ (HDP.uniformSphereVector _ z.1)
        (HDP.uniformSphereVector _ z.2)|} =
      {z | (C / Real.sqrt n) ^ 2 ≤ f z} := by
    ext z
    simp only [Set.mem_setOf_eq, f]
    simpa only [sq_abs] using
      (sq_le_sq₀ (div_nonneg hC.le hsqrtn.le) (abs_nonneg _)).symm
  rw [hset]
  calc
    (sigma.prod sigma).real {z | (C / Real.sqrt n) ^ 2 ≤ f z} ≤
        (∫ z, f z ∂sigma.prod sigma) / (C / Real.sqrt n) ^ 2 := hmarkov
    _ = (1 / (n : ℝ)) / (C / Real.sqrt n) ^ 2 := by
      rw [uniformSphere_inner_sq_expectation n hn]
    _ = 1 / C ^ 2 := by
      rw [div_pow, Real.sq_sqrt hnR.le]
      field_simp [hnR.ne', hC.ne']

/-- Identifies `projectiveDenominator` with `norm_div_sqrt`.

**Lean implementation helper.** -/
lemma projectiveDenominator_eq_norm_div_sqrt (n : ℕ) (hn : 0 < n)
    (w : ProjectiveOmega) :
    projectiveDenominator n w =
      ‖projectiveGaussianVector n w‖ / Real.sqrt n := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  have hrhs : 0 ≤ ‖projectiveGaussianVector n w‖ / Real.sqrt n :=
    div_nonneg (norm_nonneg _) hsqrt.le
  rw [projectiveDenominator, ← Real.sqrt_sq hrhs]
  congr 1
  rw [div_pow, Real.sq_sqrt hnR.le]
  simp only [projectiveGaussianSquare, projectiveGaussianVector]
  rw [EuclideanSpace.real_norm_sq_eq]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ w i ^ 2)]

/-- A normalized standard Gaussian direction is uniform on the sphere.

**Book Equation (3.15).** -/
theorem map_projectiveGaussianDirection (n : ℕ) [Nonempty (Fin n)] :
    Measure.map
        (HDP.gaussianDirection ∘ projectiveGaussianVector n)
        projectiveProbability =
      HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)) := by
  rw [← Measure.map_map (HDP.measurable_gaussianDirection
    (E := EuclideanSpace ℝ (Fin n))) (measurable_projectiveGaussianVector n)]
  rw [map_projectiveGaussianVector,
    HDP.map_gaussianDirection_stdGaussian (E := EuclideanSpace ℝ (Fin n))]

/-- A real Gaussian assigns zero mass to the singleton at the origin.

**Lean implementation helper.** -/
lemma gaussianReal_zero_singleton : (gaussianReal 0 1) ({0} : Set ℝ) = 0 := by
  rw [gaussianReal_apply_eq_integral 0 (by norm_num) ({0} : Set ℝ)]
  simp

/-- A projective Gaussian coordinate is almost surely nonzero.

**Lean implementation helper.** -/
lemma projectiveGaussianCoordinate_zero_ae_ne :
    ∀ᵐ w ∂projectiveProbability, projectiveGaussianCoordinate 0 w ≠ 0 := by
  rw [ae_iff]
  have h := (hasLaw_projectiveGaussianCoordinate 0).measure_eq
    (p := fun x : ℝ ↦ x = 0)
      (show MeasurableSet {x : ℝ | x = 0} by simp)
  simpa [gaussianReal_zero_singleton] using h

/-- The projective Gaussian vector is almost surely nonzero.

**Lean implementation helper.** -/
lemma projectiveGaussianVector_ae_ne_zero (n : ℕ) (hn : 0 < n) :
    ∀ᵐ w ∂projectiveProbability, projectiveGaussianVector n w ≠ 0 := by
  filter_upwards [projectiveGaussianCoordinate_zero_ae_ne] with w hw
  intro hzero
  apply hw
  have hcoord := congrArg
    (fun x : EuclideanSpace ℝ (Fin n) ↦ x ⟨0, hn⟩) hzero
  simpa [projectiveGaussianVector, projectiveGaussianCoordinate] using hcoord

/-- Identifies `coe_gaussianDirection` with `inv_norm_smul`.

**Lean implementation helper.** -/
lemma coe_gaussianDirection_eq_inv_norm_smul
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [Nontrivial E] (x : E) (hx : x ≠ 0) :
    ((HDP.gaussianDirection x : Metric.sphere (0 : E) 1) : E) =
      ‖x‖⁻¹ • x := by
  let y : ({0}ᶜ : Set E) := ⟨x, by simpa⟩
  have h := congrArg Subtype.val (HDP.gaussianDirection_coe (E := E) y)
  simpa [y, homeomorphUnitSphereProd_apply_fst_coe] using h

/-- Identifies `sphericalProjection_first_comp_direction` with `ratio`.

**Lean implementation helper.** -/
lemma sphericalProjection_first_comp_direction_eq_ratio
    (n : ℕ) [Nonempty (Fin n)] (hn : 0 < n) (w : ProjectiveOmega)
    (hw : projectiveGaussianVector n w ≠ 0) :
    sphericalProjection n (firstUnitDirection n hn)
        (HDP.gaussianDirection (projectiveGaussianVector n w)) =
      projectiveRatio n w := by
  let x := projectiveGaussianVector n w
  have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have hsqrt : Real.sqrt (n : ℝ) ≠ 0 :=
    (Real.sqrt_pos.2 (by exact_mod_cast hn)).ne'
  rw [sphericalProjection, projectiveRatio,
    projectiveDenominator_eq_norm_div_sqrt n hn w]
  rw [coe_gaussianDirection_eq_inv_norm_smul x hw]
  change Real.sqrt n * inner ℝ (‖x‖⁻¹ • x)
      (EuclideanSpace.single ⟨0, hn⟩ 1) =
    w 0 / (‖x‖ / Real.sqrt n)
  rw [inner_smul_left, EuclideanSpace.inner_single_right]
  simp only [starRingEnd_apply, star_id_of_comm, one_mul]
  change Real.sqrt n * (‖x‖⁻¹ * w 0) =
    w 0 / (‖x‖ / Real.sqrt n)
  field_simp

/-- The canonical spherical coordinate has exactly the self-normalized
Gaussian law used in the common-space limit proof.

**Lean implementation helper.** -/
theorem map_sphericalProjection_first_eq_projectiveRatio
    (n : ℕ) (hn : 0 < n) :
    Measure.map (sphericalProjection n (firstUnitDirection n hn))
        (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))) =
      Measure.map (projectiveRatio n) projectiveProbability := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [← map_projectiveGaussianDirection n]
  rw [Measure.map_map (measurable_sphericalProjection n (firstUnitDirection n hn))
    ((HDP.measurable_gaussianDirection
      (E := EuclideanSpace ℝ (Fin n))).comp
        (measurable_projectiveGaussianVector n))]
  apply Measure.map_congr
  filter_upwards [projectiveGaussianVector_ae_ne_zero n hn] with w hw
  exact sphericalProjection_first_comp_direction_eq_ratio n hn w hw

/-- Uniformly over all unit directions and all
CDF thresholds, the `√n`-scaled marginal of normalized surface area on
`Sⁿ⁻¹` converges to the standard Gaussian CDF.

**Book Theorem 3.3.9.** -/
theorem projectiveCentralLimitTheorem :
    ∀ ε > 0, ∀ᶠ n in atTop,
      ∀ v : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1, ∀ t : ℝ,
        |(Measure.map (sphericalProjection n v)
            (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)))).real
              (Set.Iic t) -
          (gaussianReal 0 1).real (Set.Iic t)| < ε := by
  intro ε hε
  filter_upwards [projectiveRatio_uniform_cdf ε hε,
    eventually_gt_atTop (0 : ℕ)] with n hnCDF hn
  intro v t
  rw [map_sphericalProjection_eq n v (firstUnitDirection n hn),
    map_sphericalProjection_first_eq_projectiveRatio n hn]
  exact hnCDF t

end

end HDP.Chapter3

end Source_09_SphericalDistributions

/-! ## Material formerly in `10_SphericalMarginals.lean` -/

section Source_10_SphericalMarginals

/-!
# One-dimensional marginals of Euclidean balls and spheres

This file contains the geometric measure statements used by Book Exercise
3.27.  In particular, the measures below are genuine push-forwards of
normalized volume/surface area; the power-profile densities are not merely
postulated models.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace

namespace HDP

noncomputable section

/-- Normalized Lebesgue measure on the closed Euclidean unit ball.

**Lean implementation helper.** -/
def unitBallMeasure
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] : Measure E :=
  (volume (Metric.closedBall (0 : E) 1))⁻¹ •
    volume.restrict (Metric.closedBall (0 : E) 1)

/-- The first coordinate on an `L²` product `ℝ ⊕₂ E`.

**Lean implementation helper.** -/
def firstL2Coordinate
    (E : Type*) [NormedAddCommGroup E] : WithLp 2 (ℝ × E) → ℝ :=
  fun z ↦ (WithLp.ofLp z).1

/-- The first-coordinate map `firstL2Coordinate` on an `L²` product is measurable.

**Lean implementation helper.** -/
lemma measurable_firstL2Coordinate
    (E : Type*) [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] :
    Measurable (firstL2Coordinate E) := by
  exact measurable_fst.comp (WithLp.measurable_ofLp 2 (ℝ × E))

/-- Unnormalized density of the first coordinate of the Euclidean unit ball
in `ℝ ⊕₂ E`: it is exactly the volume of the orthogonal slice.

**Lean implementation helper.** -/
def unitBallSliceDensity
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (x : ℝ) : ℝ≥0∞ :=
  if x ∈ Set.Icc (-1 : ℝ) 1 then
    volume (Metric.closedBall (0 : E) (Real.sqrt (1 - x ^ 2)))
  else 0

/-- The compactly supported power profile used for Euclidean ball and
sphere marginals, as an `ℝ≥0∞`-valued density.

**Lean implementation helper.** -/
def marginalPowerDensity (a : ℝ) (x : ℝ) : ℝ≥0∞ :=
  if x ∈ Set.Icc (-1 : ℝ) 1 then ENNReal.ofReal ((1 - x ^ 2) ^ a) else 0

/-- For every exponent `a`, the compactly supported profile `marginalPowerDensity` is measurable.

**Lean implementation helper.** -/
lemma measurable_marginalPowerDensity (a : ℝ) :
    Measurable (marginalPowerDensity a) := by
  unfold marginalPowerDensity
  apply Measurable.ite measurableSet_Icc
  · fun_prop
  · exact measurable_const

/-- The unit-ball slice-volume function `unitBallSliceDensity` is measurable.

**Lean implementation helper.** -/
lemma measurable_unitBallSliceDensity
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [Nontrivial E] : Measurable (unitBallSliceDensity E) := by
  unfold unitBallSliceDensity
  apply Measurable.ite measurableSet_Icc
  · rw [show (fun x : ℝ ↦
        volume (Metric.closedBall (0 : E) (Real.sqrt (1 - x ^ 2)))) =
      fun x : ℝ ↦
        ENNReal.ofReal (Real.sqrt (1 - x ^ 2)) ^ Module.finrank ℝ E *
          ENNReal.ofReal
            (Real.sqrt Real.pi ^ Module.finrank ℝ E /
              Real.Gamma ((Module.finrank ℝ E : ℝ) / 2 + 1)) by
        funext x
        rw [InnerProductSpace.volume_closedBall]]
    fun_prop
  · exact measurable_const

/-- The geometric slice density is exactly a constant multiple of the
power profile with exponent `dim(E)/2`.

**Lean implementation helper.** -/
theorem unitBallSliceDensity_eq_power
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [Nontrivial E] (x : ℝ) :
    unitBallSliceDensity E x =
      volume (Metric.closedBall (0 : E) 1) *
        marginalPowerDensity ((Module.finrank ℝ E : ℝ) / 2) x := by
  by_cases hx : x ∈ Set.Icc (-1 : ℝ) 1
  · have hrad : 0 ≤ 1 - x ^ 2 := by
      rcases hx with ⟨hxlow, hxhigh⟩
      nlinarith
    rw [unitBallSliceDensity, if_pos hx, marginalPowerDensity, if_pos hx,
      InnerProductSpace.volume_closedBall, InnerProductSpace.volume_closedBall]
    simp only [ENNReal.ofReal_one, one_pow]
    have hsqrtpow : Real.sqrt (1 - x ^ 2) ^ Module.finrank ℝ E =
        (1 - x ^ 2) ^ ((Module.finrank ℝ E : ℝ) / 2) := by
      calc
        Real.sqrt (1 - x ^ 2) ^ Module.finrank ℝ E =
            Real.sqrt (1 - x ^ 2) ^ (Module.finrank ℝ E : ℝ) := by
              rw [Real.rpow_natCast]
        _ = (1 - x ^ 2) ^ ((Module.finrank ℝ E : ℝ) / 2) :=
          (Real.rpow_div_two_eq_sqrt (Module.finrank ℝ E : ℝ) hrad).symm
    rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _) (Module.finrank ℝ E),
      hsqrtpow]
    ac_rfl
  · rw [unitBallSliceDensity, if_neg hx, marginalPowerDensity, if_neg hx,
      mul_zero]

/-- Characterizes membership in `l2_closedBall_iff`.

**Lean implementation helper.** -/
private lemma mem_l2_closedBall_iff
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x : ℝ) (y : E) :
    WithLp.toLp 2 (x, y) ∈
        Metric.closedBall (0 : WithLp 2 (ℝ × E)) 1 ↔
      x ∈ Set.Icc (-1 : ℝ) 1 ∧
        y ∈ Metric.closedBall (0 : E) (Real.sqrt (1 - x ^ 2)) := by
  rw [Metric.mem_closedBall, dist_zero_right,
    Metric.mem_closedBall, dist_zero_right]
  constructor
  · intro h
    have hsquare' : ‖WithLp.toLp 2 (x, y)‖ ^ 2 ≤ (1 : ℝ) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by norm_num)).2 h
    have hsquare : ‖WithLp.toLp 2 (x, y)‖ ^ 2 ≤ 1 := by
      simpa using hsquare'
    rw [WithLp.prod_norm_sq_eq_of_L2] at hsquare
    simp only [WithLp.toLp_fst, WithLp.toLp_snd, Real.norm_eq_abs,
      sq_abs] at hsquare
    have hx : x ∈ Set.Icc (-1 : ℝ) 1 := by
      constructor <;> nlinarith [sq_nonneg x, sq_nonneg ‖y‖]
    refine ⟨hx, ?_⟩
    have hrad : 0 ≤ 1 - x ^ 2 := by nlinarith
    rw [← sq_le_sq₀ (norm_nonneg y) (Real.sqrt_nonneg _),
      Real.sq_sqrt hrad]
    linarith
  · rintro ⟨hx, hy⟩
    have hrad : 0 ≤ 1 - x ^ 2 := by
      rcases hx with ⟨hxlow, hxhigh⟩
      nlinarith
    have hysquare : ‖y‖ ^ 2 ≤ 1 - x ^ 2 := by
      rw [← Real.sq_sqrt hrad]
      exact (sq_le_sq₀ (norm_nonneg y) (Real.sqrt_nonneg _)).2 hy
    have hsquare : ‖WithLp.toLp 2 (x, y)‖ ^ 2 ≤ 1 := by
      rw [WithLp.prod_norm_sq_eq_of_L2]
      simp only [WithLp.toLp_fst, WithLp.toLp_snd, Real.norm_eq_abs,
        sq_abs]
      linarith
    apply (sq_le_sq₀ (norm_nonneg _) (by norm_num)).1
    simpa using hsquare

/-- A diagonal linear image of a Euclidean closed ball is the corresponding coordinate ellipsoid.

**Lean implementation helper.** -/
private lemma image_l2_closedBall
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    WithLp.ofLp '' Metric.closedBall (0 : WithLp 2 (ℝ × E)) 1 =
      {p : ℝ × E | WithLp.toLp 2 p ∈
        Metric.closedBall (0 : WithLp 2 (ℝ × E)) 1} := by
  ext p
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨z, hz, rfl⟩
    simpa [Metric.mem_closedBall, dist_zero_right] using hz
  · intro hp
    exact ⟨WithLp.toLp 2 p, hp, by simp⟩

/-- Slicing formula: pushing unnormalized Lebesgue measure on an `L²` unit
ball through the first coordinate gives Lebesgue measure weighted by the
actual volumes of the orthogonal slices.

**Lean implementation helper.** -/
theorem map_firstL2Coordinate_restrict_closedBall
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [Nontrivial E] :
    Measure.map (firstL2Coordinate E)
        (volume.restrict
          (Metric.closedBall (0 : WithLp 2 (ℝ × E)) 1)) =
      volume.withDensity (unitBallSliceDensity E) := by
  classical
  let B : Set (WithLp 2 (ℝ × E)) := Metric.closedBall 0 1
  let S : Set (ℝ × E) := {p | WithLp.toLp 2 p ∈ B}
  have hS : MeasurableSet S := by
    exact Metric.isClosed_closedBall.measurableSet.preimage (by fun_prop)
  have hrest := (WithLp.volume_preserving_ofLp ℝ E).restrict_image_emb
    (MeasurableEquiv.toLp 2 (ℝ × E)).symm.measurableEmbedding B
  have hmapRest : Measure.map WithLp.ofLp (volume.restrict B) =
      volume.restrict S := by
    rw [show S = WithLp.ofLp '' B by
      simpa [S, B] using (image_l2_closedBall (E := E)).symm]
    exact hrest.map_eq
  rw [show firstL2Coordinate E = Prod.fst ∘ WithLp.ofLp by rfl,
    ← Measure.map_map measurable_fst (by fun_prop), hmapRest]
  rw [Measure.volume_eq_prod ℝ E]
  ext A hA
  rw [Measure.map_apply measurable_fst hA,
    Measure.restrict_apply (hA.preimage measurable_fst),
    Measure.prod_apply ((hA.preimage measurable_fst).inter hS),
    withDensity_apply _ hA]
  rw [← lintegral_indicator hA]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ Set.Icc (-1 : ℝ) 1
  · have hfiber : Prod.mk x ⁻¹' ((Prod.fst ⁻¹' A) ∩ S) =
        if x ∈ A then Metric.closedBall (0 : E)
          (Real.sqrt (1 - x ^ 2)) else ∅ := by
      ext y
      simp only [Set.mem_preimage, Set.mem_inter_iff]
      change (x ∈ A ∧ WithLp.toLp 2 (x, y) ∈ B) ↔ _
      dsimp only [B]
      rw [mem_l2_closedBall_iff]
      simp [hx]
    rw [hfiber]
    by_cases hxA : x ∈ A
    · simp [hxA, unitBallSliceDensity, hx]
    · simp [hxA]
  · have hfiber : Prod.mk x ⁻¹' ((Prod.fst ⁻¹' A) ∩ S) = ∅ := by
      ext y
      simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_empty_iff_false]
      change (x ∈ A ∧ WithLp.toLp 2 (x, y) ∈ B) ↔ False
      dsimp only [B]
      constructor
      · rintro ⟨_, hy⟩
        exact hx (mem_l2_closedBall_iff x y |>.mp hy).1
      · intro hfalse
        exact hfalse.elim
    rw [hfiber]
    have hx' : ¬ (-1 ≤ x ∧ x ≤ 1) := by
      simpa only [Set.mem_Icc] using hx
    change volume (∅ : Set E) = A.indicator
      (fun z : ℝ ↦ if z ∈ Set.Icc (-1 : ℝ) 1 then
        volume (Metric.closedBall (0 : E) (Real.sqrt (1 - z ^ 2))) else 0) x
    by_cases hxA : x ∈ A
    · simp [Set.indicator, hxA, hx']
    · simp [Set.indicator, hxA]

/-- Genuine density law for the first coordinate of normalized volume on an
`L²` Euclidean unit ball.

**Lean implementation helper.** -/
theorem map_firstL2Coordinate_unitBallMeasure
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [Nontrivial E] :
    Measure.map (firstL2Coordinate E)
        (unitBallMeasure (WithLp 2 (ℝ × E))) =
      volume.withDensity (fun x ↦
        (volume (Metric.closedBall (0 : WithLp 2 (ℝ × E)) 1))⁻¹ *
          unitBallSliceDensity E x) := by
  have hdens : Measurable (unitBallSliceDensity E) :=
    measurable_unitBallSliceDensity E
  rw [unitBallMeasure, Measure.map_smul,
    map_firstL2Coordinate_restrict_closedBall]
  ext A hA
  simp only [Measure.smul_apply, withDensity_apply _ hA]
  change (volume (Metric.closedBall (0 : WithLp 2 (ℝ × E)) 1))⁻¹ *
      (∫⁻ x in A, unitBallSliceDensity E x ∂volume) = _
  exact (MeasureTheory.lintegral_const_mul
    (μ := volume.restrict A)
    (volume (Metric.closedBall (0 : WithLp 2 (ℝ × E)) 1))⁻¹ hdens).symm

/-- Source-ready normalized power-density form of the unit-ball marginal
law. The ambient dimension is `1 + dim(E)`, hence the exponent is
`(n-1)/2 = dim(E)/2`.

**Book Remark 3.3.10.** -/
theorem map_firstL2Coordinate_unitBallMeasure_eq_power
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [Nontrivial E] :
    Measure.map (firstL2Coordinate E)
        (unitBallMeasure (WithLp 2 (ℝ × E))) =
      volume.withDensity (fun x ↦
        ((volume (Metric.closedBall (0 : WithLp 2 (ℝ × E)) 1))⁻¹ *
          volume (Metric.closedBall (0 : E) 1)) *
            marginalPowerDensity ((Module.finrank ℝ E : ℝ) / 2) x) := by
  rw [map_firstL2Coordinate_unitBallMeasure]
  congr 1
  funext x
  rw [unitBallSliceDensity_eq_power]
  ac_rfl

end

end HDP

end Source_10_SphericalMarginals

/-! ## Material formerly in `11_SphereCoordinateMarginals.lean` -/

section Source_11_SphereCoordinateMarginals

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace

namespace HDP
noncomputable section

/-- `lintegral_radial_volume` expresses `∫⁻ x, f ‖x‖` as sphere area times the radial `volumeIoiPow` integral.

**Lean implementation helper.** -/
lemma lintegral_radial_volume
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [Nontrivial E] (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x : E, f ‖x‖ ∂volume) =
      (volume : Measure E).toSphere Set.univ *
        ∫⁻ r : Set.Ioi (0 : ℝ), f r
          ∂Measure.volumeIoiPow (Module.finrank ℝ E - 1) := by
  let S : Set E := {0}ᶜ
  calc
    (∫⁻ x : E, f ‖x‖ ∂volume) =
        ∫⁻ x in S, f ‖x‖ ∂volume := by
      rw [show (volume : Measure E).restrict S = volume by
        exact restrict_compl_singleton 0]
    _ = ∫⁻ x : S, f ‖(x : E)‖ ∂((volume : Measure E).comap ((↑) : S → E)) := by
      dsimp only [S]
      exact (lintegral_subtype_comap
        (μ := (volume : Measure E))
        (measurableSet_singleton (0 : E)).compl
        (fun x : E ↦ f ‖x‖)).symm
    _ = ∫⁻ p : Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ), f p.2
        ∂((volume : Measure E).toSphere.prod
          (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) := by
      have h := (volume : Measure E).measurePreserving_homeomorphUnitSphereProd.lintegral_comp_emb
        (homeomorphUnitSphereProd E).measurableEmbedding (fun p => f p.2)
      simpa [S, homeomorphUnitSphereProd_apply_snd_coe] using h
    _ = (volume : Measure E).toSphere Set.univ *
        ∫⁻ r : Set.Ioi (0 : ℝ), f r ∂Measure.volumeIoiPow (Module.finrank ℝ E - 1) := by
      rw [lintegral_prod (fun p : Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ) ↦
        f (p.2 : ℝ))
        ((hf.comp measurable_subtype_coe).comp measurable_snd).aemeasurable]
      simp [mul_comm]

/-- Defines `firstL2SphereCoordinate`, the first l2 sphere coordinate used in the surrounding construction.

**Lean implementation helper.** -/
def firstL2SphereCoordinate
    (E : Type*) [NormedAddCommGroup E]
    (z : Metric.sphere (0 : WithLp 2 (ℝ × E)) 1) : ℝ :=
  firstL2Coordinate E z

/-- Characterizes membership in `unitSphereSector_first_iff`.

**Lean implementation helper.** -/
lemma mem_unitSphereSector_first_iff
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : Set ℝ) (p : WithLp 2 (ℝ × E)) :
    p ∈ unitSphereSector
        (firstL2SphereCoordinate E ⁻¹' A) ↔
      0 < ‖p‖ ∧ ‖p‖ < 1 ∧
        (WithLp.ofLp p).1 / ‖p‖ ∈ A := by
  constructor
  · rintro ⟨r, hr, y, ⟨z, hzA, rfl⟩, hry⟩
    have hzNorm : ‖(z : WithLp 2 (ℝ × E))‖ = 1 := by
      have hz := z.property
      change dist (z : WithLp 2 (ℝ × E)) 0 = 1 at hz
      rw [dist_zero_right] at hz
      exact hz
    have hrNorm : ‖r • (z : WithLp 2 (ℝ × E))‖ = r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr.1, hzNorm, mul_one]
    subst p
    refine ⟨by simpa [hrNorm] using hr.1, by simpa [hrNorm] using hr.2, ?_⟩
    change (WithLp.ofLp (r • (z : WithLp 2 (ℝ × E)))).1 /
      ‖r • (z : WithLp 2 (ℝ × E))‖ ∈ A
    rw [hrNorm]
    change (r * (WithLp.ofLp (z : WithLp 2 (ℝ × E))).1) / r ∈ A
    simpa [hr.1.ne', firstL2SphereCoordinate, firstL2Coordinate] using hzA
  · rintro ⟨hp0, hp1, hpA⟩
    let r := ‖p‖
    have hr : r ∈ Set.Ioo (0 : ℝ) 1 := ⟨hp0, hp1⟩
    let z0 : WithLp 2 (ℝ × E) := r⁻¹ • p
    have hzNorm : ‖z0‖ = 1 := by
      dsimp [z0, r]
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hp0,
        inv_mul_cancel₀ hp0.ne']
    let z : Metric.sphere (0 : WithLp 2 (ℝ × E)) 1 :=
      ⟨z0, by simpa [Metric.mem_sphere, dist_zero_right] using hzNorm⟩
    refine ⟨r, hr, z0, ⟨z, ?_, rfl⟩, ?_⟩
    · change (WithLp.ofLp z0).1 ∈ A
      dsimp [z0, r]
      change ‖p‖⁻¹ * (WithLp.ofLp p).1 ∈ A
      simpa [div_eq_inv_mul] using hpA
    · dsimp [z0, r]
      rw [smul_smul, mul_inv_cancel₀ hp0.ne', one_smul]

/-- Defines `planeSectorDensity`, the plane sector density used in the surrounding construction.

**Lean implementation helper.** -/
def planeSectorDensity (d : ℕ) (A : Set ℝ) (p : ℝ × ℝ) : ℝ≥0∞ :=
  by classical exact if 0 < p.2 ∧
      0 < Real.sqrt (p.1 ^ 2 + p.2 ^ 2) ∧
      Real.sqrt (p.1 ^ 2 + p.2 ^ 2) < 1 ∧
      p.1 / Real.sqrt (p.1 ^ 2 + p.2 ^ 2) ∈ A then
    ENNReal.ofReal (p.2 ^ (d - 1))
  else 0

/-- If `A` is measurable, then the planar sector weight `planeSectorDensity` at dimension `d` is measurable.

**Lean implementation helper.** -/
lemma measurable_planeSectorDensity (d : ℕ) {A : Set ℝ}
    (hA : MeasurableSet A) : Measurable (planeSectorDensity d A) := by
  classical
  unfold planeSectorDensity
  have hnorm : Measurable (fun p : ℝ × ℝ ↦
      Real.sqrt (p.1 ^ 2 + p.2 ^ 2)) := by fun_prop
  have hratio : Measurable (fun p : ℝ × ℝ ↦
      p.1 / Real.sqrt (p.1 ^ 2 + p.2 ^ 2)) := by fun_prop
  have hcond : MeasurableSet {p : ℝ × ℝ |
      0 < p.2 ∧ 0 < Real.sqrt (p.1 ^ 2 + p.2 ^ 2) ∧
      Real.sqrt (p.1 ^ 2 + p.2 ^ 2) < 1 ∧
      p.1 / Real.sqrt (p.1 ^ 2 + p.2 ^ 2) ∈ A} := by
    rw [measurableSet_setOf]
    exact (measurable_const.lt measurable_snd).and <|
      (measurable_const.lt hnorm).and <|
        (hnorm.lt measurable_const).and <|
          measurableSet_setOf.mp (hA.preimage hratio)
  exact Measurable.ite hcond (by fun_prop) measurable_const

/-- Defines `polarSectorDensity`, the polar sector density used in the surrounding construction.

**Lean implementation helper.** -/
def polarSectorDensity (d : ℕ) (A : Set ℝ) (r θ : ℝ) : ℝ≥0∞ := by
  classical
  exact if r < 1 ∧ 0 < θ ∧ Real.cos θ ∈ A then
    ENNReal.ofReal (r ^ d) * ENNReal.ofReal (Real.sin θ ^ (d - 1))
  else 0

/-- Integrating the planar Gaussian density over a sector reduces to its polar-coordinate angular integral.

**Lean implementation helper.** -/
lemma planeSectorDensity_polar (d : ℕ) (hd : 0 < d) (A : Set ℝ)
    (r θ : ℝ) (hr : 0 < r) (hθ : θ ∈ Set.Ioo (-Real.pi) Real.pi) :
    ENNReal.ofReal r * planeSectorDensity d A
        (r * Real.cos θ, r * Real.sin θ) =
      polarSectorDensity d A r θ := by
  classical
  unfold polarSectorDensity
  have hrad : Real.sqrt ((r * Real.cos θ) ^ 2 +
      (r * Real.sin θ) ^ 2) = r := by
    rw [show (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 by
      rw [mul_pow, mul_pow, ← mul_add]
      rw [Real.cos_sq_add_sin_sq]
      ring]
    exact Real.sqrt_sq hr.le
  have hsinpos : 0 < Real.sin θ ↔ 0 < θ := by
    constructor
    · intro hs
      by_contra hn
      have hle : θ ≤ 0 := not_lt.mp hn
      rcases hle.lt_or_eq with hlt | rfl
      · exact (not_lt_of_ge (Real.sin_neg_of_neg_of_neg_pi_lt hlt hθ.1).le) hs
      · simp at hs
    · intro ht
      exact Real.sin_pos_of_pos_of_lt_pi ht hθ.2
  have hcond :
      (0 < (r * Real.sin θ) ∧ 0 < r ∧ r < 1 ∧
        (r * Real.cos θ) / r ∈ A) ↔
      (r < 1 ∧ 0 < θ ∧ Real.cos θ ∈ A) := by
    have hratio : r * Real.cos θ / r = Real.cos θ := by
      field_simp
    simp only [mul_pos_iff_of_pos_left hr, hsinpos, hr, true_and, hratio]
    aesop
  rw [planeSectorDensity, hrad]
  rw [if_congr hcond (by rfl) (by rfl)]
  split_ifs with hc
  · have hs : 0 ≤ Real.sin θ :=
      (Real.sin_pos_of_pos_of_lt_pi hc.2.1 hθ.2).le
    rw [mul_pow, ENNReal.ofReal_mul (pow_nonneg hr.le _)]
    rw [← mul_assoc, ← ENNReal.ofReal_mul hr.le]
    rw [← pow_succ', Nat.sub_add_cancel hd]
  · simp

/-- `lintegral_ofReal_pow_Ioo_zero_one` evaluates `∫⁻ r in (0,1), r ^ d` as `1 / (d + 1)`.

**Lean implementation helper.** -/
lemma lintegral_ofReal_pow_Ioo_zero_one (d : ℕ) :
    (∫⁻ r : ℝ in Set.Ioo 0 1, ENNReal.ofReal (r ^ d) ∂volume) =
      ENNReal.ofReal ((1 : ℝ) / (d + 1)) := by
  have h := Measure.volumeIoiPow_apply_Iio d
    (⟨1, by norm_num⟩ : Set.Ioi (0 : ℝ))
  rw [Measure.volumeIoiPow] at h
  rw [withDensity_apply _ measurableSet_Iio] at h
  rw [setLIntegral_subtype measurableSet_Ioi _
    (fun a : ℝ ↦ ENNReal.ofReal (a ^ d))] at h
  rw [Set.image_subtype_val_Ioi_Iio] at h
  simpa using h

/-- `lintegral_planeSectorDensity` factors the planar sector integral into `1 / (d + 1)` times its sine-power angular integral.

**Lean implementation helper.** -/
lemma lintegral_planeSectorDensity (d : ℕ) (hd : 0 < d)
    {A : Set ℝ} (hA : MeasurableSet A) :
    (∫⁻ p : ℝ × ℝ, planeSectorDensity d A p ∂volume) =
      ENNReal.ofReal ((1 : ℝ) / (d + 1)) *
        ∫⁻ θ : ℝ in Set.Ioo 0 Real.pi ∩ Real.cos ⁻¹' A,
          ENNReal.ofReal (Real.sin θ ^ (d - 1)) ∂volume := by
  classical
  let R : Set ℝ := Set.Ioo 0 1
  let T : Set ℝ := Set.Ioo 0 Real.pi ∩ Real.cos ⁻¹' A
  have hR : MeasurableSet R := measurableSet_Ioo
  have hT : MeasurableSet T :=
    measurableSet_Ioo.inter (hA.preimage Real.measurable_cos)
  have htarget : MeasurableSet (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi) :=
    measurableSet_Ioi.prod measurableSet_Ioo
  have hRT : MeasurableSet (R ×ˢ T) := hR.prod hT
  have hsubset : R ×ˢ T ⊆ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi := by
    rintro ⟨r, θ⟩ hp
    rcases hp with ⟨hr, hθ, hAθ⟩
    change r ∈ R at hr
    change θ ∈ Set.Ioo 0 Real.pi at hθ
    exact ⟨hr.1, ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩⟩
  calc
    (∫⁻ p : ℝ × ℝ, planeSectorDensity d A p ∂volume) =
        ∫⁻ p : ℝ × ℝ in
            Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
          ENNReal.ofReal p.1 * planeSectorDensity d A
            (p.1 * Real.cos p.2, p.1 * Real.sin p.2) ∂volume := by
      rw [← polarCoord_target]
      simpa only [polarCoord_symm_apply, smul_eq_mul] using
        (lintegral_comp_polarCoord_symm (planeSectorDensity d A)).symm
    _ = ∫⁻ p : ℝ × ℝ in R ×ˢ T,
          ENNReal.ofReal (p.1 ^ d) *
            ENNReal.ofReal (Real.sin p.2 ^ (d - 1)) ∂volume := by
      rw [← lintegral_indicator htarget, ← lintegral_indicator hRT]
      apply lintegral_congr
      intro p
      by_cases hp : p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi
      · have hpol := planeSectorDensity_polar d hd A p.1 p.2 hp.1 hp.2
        rw [Set.indicator_of_mem hp, hpol]
        by_cases hpRT : p ∈ R ×ˢ T
        · rw [Set.indicator_of_mem hpRT]
          have hr1 : p.1 < 1 := hpRT.1.2
          have hθpos : 0 < p.2 := hpRT.2.1.1
          have hcos : Real.cos p.2 ∈ A := hpRT.2.2
          simp [polarSectorDensity, hr1, hθpos, hcos]
        · simp only [Set.indicator, hpRT, if_false]
          have hnot : ¬ (p.1 < 1 ∧ 0 < p.2 ∧ Real.cos p.2 ∈ A) := by
            intro h
            apply hpRT
            exact ⟨⟨hp.1, h.1⟩, ⟨⟨h.2.1, hp.2.2⟩, h.2.2⟩⟩
          simp [polarSectorDensity, hnot]
      · simp only [Set.indicator, hp, if_false]
        have hpRT : p ∉ R ×ˢ T := fun h ↦ hp (hsubset h)
        simp only [hpRT, if_false]
    _ = (∫⁻ r : ℝ in R, ENNReal.ofReal (r ^ d) ∂volume) *
          ∫⁻ θ : ℝ in T,
            ENNReal.ofReal (Real.sin θ ^ (d - 1)) ∂volume := by
      rw [Measure.volume_eq_prod ℝ ℝ, ← Measure.prod_restrict R T]
      rw [lintegral_prod _ ((by fun_prop : Measurable (fun p : ℝ × ℝ ↦
        ENNReal.ofReal (p.1 ^ d) *
          ENNReal.ofReal (Real.sin p.2 ^ (d - 1)))).aemeasurable)]
      simp_rw [lintegral_const_mul _ (by fun_prop : Measurable (fun θ : ℝ ↦
        ENNReal.ofReal (Real.sin θ ^ (d - 1))))]
      rw [lintegral_mul_const _ (by fun_prop : Measurable (fun r : ℝ ↦
        ENNReal.ofReal (r ^ d)))]
    _ = _ := by
      rw [lintegral_ofReal_pow_Ioo_zero_one]

/-- Defines `sectorRadiusIndicator`, the sector radius indicator used in the surrounding construction.

**Lean implementation helper.** -/
def sectorRadiusIndicator (A : Set ℝ) (x s : ℝ) : ℝ≥0∞ := by
  classical
  exact if 0 < Real.sqrt (x ^ 2 + s ^ 2) ∧
      Real.sqrt (x ^ 2 + s ^ 2) < 1 ∧
      x / Real.sqrt (x ^ 2 + s ^ 2) ∈ A then 1 else 0

/-- For measurable `A`, the two-variable indicator `sectorRadiusIndicator` is measurable.

**Lean implementation helper.** -/
lemma measurable_sectorRadiusIndicator {A : Set ℝ} (hA : MeasurableSet A) :
    Measurable (fun p : ℝ × ℝ ↦ sectorRadiusIndicator A p.1 p.2) := by
  classical
  unfold sectorRadiusIndicator
  have hnorm : Measurable (fun p : ℝ × ℝ ↦
      Real.sqrt (p.1 ^ 2 + p.2 ^ 2)) := by fun_prop
  have hratio : Measurable (fun p : ℝ × ℝ ↦
      p.1 / Real.sqrt (p.1 ^ 2 + p.2 ^ 2)) := by fun_prop
  apply Measurable.ite
  · rw [measurableSet_setOf]
    exact (measurable_const.lt hnorm).and <|
      (hnorm.lt measurable_const).and
        (measurableSet_setOf.mp (hA.preimage hratio))
  · exact measurable_const
  · exact measurable_const

/-- `lintegral_volumeIoiPow_sectorRadiusIndicator` identifies the iterated weighted-radius integral of the sector indicator with the planar `planeSectorDensity` integral.

**Lean implementation helper.** -/
lemma lintegral_volumeIoiPow_sectorRadiusIndicator (d : ℕ)
    {A : Set ℝ} (hA : MeasurableSet A) :
    (∫⁻ x : ℝ, ∫⁻ s : Set.Ioi (0 : ℝ),
        sectorRadiusIndicator A x s ∂Measure.volumeIoiPow (d - 1) ∂volume) =
      ∫⁻ p : ℝ × ℝ, planeSectorDensity d A p ∂volume := by
  classical
  have hsector := measurable_sectorRadiusIndicator hA
  have hsection (x : ℝ) : Measurable (fun s : ℝ ↦ sectorRadiusIndicator A x s) := by
    exact hsector.comp (measurable_const.prodMk measurable_id)
  have hinner (x : ℝ) :
      (∫⁻ s : Set.Ioi (0 : ℝ), sectorRadiusIndicator A x s
          ∂Measure.volumeIoiPow (d - 1)) =
        ∫⁻ s : ℝ in Set.Ioi 0,
          ENNReal.ofReal (s ^ (d - 1)) * sectorRadiusIndicator A x s ∂volume := by
    rw [Measure.volumeIoiPow]
    change (∫⁻ s : Set.Ioi (0 : ℝ),
      ((fun t : ℝ ↦ sectorRadiusIndicator A x t) ∘ Subtype.val) s
        ∂(Measure.comap ((↑) : Set.Ioi (0 : ℝ) → ℝ) (volume : Measure ℝ)).withDensity
          (fun s : Set.Ioi (0 : ℝ) ↦ ENNReal.ofReal ((s : ℝ) ^ (d - 1)))) = _
    rw [lintegral_withDensity_eq_lintegral_mul
        (Measure.comap ((↑) : Set.Ioi (0 : ℝ) → ℝ) (volume : Measure ℝ))
        (by fun_prop : Measurable (fun s : Set.Ioi (0 : ℝ) ↦
          ENNReal.ofReal ((s : ℝ) ^ (d - 1))))
        ((hsection x).comp measurable_subtype_coe)]
    simpa using (lintegral_subtype_comap (μ := (volume : Measure ℝ))
      measurableSet_Ioi
      (fun s : ℝ ↦ ENNReal.ofReal (s ^ (d - 1)) *
        sectorRadiusIndicator A x s))
  simp_rw [hinner]
  simp_rw [← lintegral_indicator measurableSet_Ioi]
  have hupper : MeasurableSet {p : ℝ × ℝ | p.2 ∈ Set.Ioi (0 : ℝ)} :=
    measurableSet_Ioi.preimage measurable_snd
  have hinter : Measurable (fun p : ℝ × ℝ ↦
      (Set.Ioi (0 : ℝ)).indicator
        (fun q : ℝ ↦ ENNReal.ofReal (q ^ (d - 1)) *
          sectorRadiusIndicator A p.1 q) p.2) := by
    have hm : Measurable (fun p : ℝ × ℝ ↦
        ENNReal.ofReal (p.2 ^ (d - 1)) * sectorRadiusIndicator A p.1 p.2) := by
      fun_prop
    change Measurable ({p : ℝ × ℝ | p.2 ∈ Set.Ioi (0 : ℝ)}.indicator
      (fun p : ℝ × ℝ ↦ ENNReal.ofReal (p.2 ^ (d - 1)) *
        sectorRadiusIndicator A p.1 p.2))
    exact hm.indicator hupper
  rw [← lintegral_prod _ hinter.aemeasurable]
  rw [← Measure.volume_eq_prod ℝ ℝ]
  apply lintegral_congr
  intro p
  by_cases hs : 0 < p.2
  · have hs' : p.2 ∈ Set.Ioi (0 : ℝ) := hs
    rw [Set.indicator_of_mem hs']
    simp only [planeSectorDensity, sectorRadiusIndicator]
    by_cases hc : 0 < Real.sqrt (p.1 ^ 2 + p.2 ^ 2) ∧
        Real.sqrt (p.1 ^ 2 + p.2 ^ 2) < 1 ∧
        p.1 / Real.sqrt (p.1 ^ 2 + p.2 ^ 2) ∈ A
    · simp [hs, hc, mul_one]
    · simp [hs]
  · simp [Set.indicator, hs, planeSectorDensity]

/-- Defines `productSphereSectorFirst`, the product sphere sector first used in the surrounding construction.

**Lean implementation helper.** -/
def productSphereSectorFirst
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : Set ℝ) : Set (ℝ × E) :=
  {p | 0 < ‖WithLp.toLp 2 p‖ ∧ ‖WithLp.toLp 2 p‖ < 1 ∧
    p.1 / ‖WithLp.toLp 2 p‖ ∈ A}

/-- The product-sphere sector determined by the first two coordinates is measurable.

**Lean implementation helper.** -/
lemma measurableSet_productSphereSectorFirst
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {A : Set ℝ} (hA : MeasurableSet A) :
    MeasurableSet (productSphereSectorFirst E A) := by
  unfold productSphereSectorFirst
  rw [measurableSet_setOf]
  have hn : Measurable (fun p : ℝ × E ↦ ‖WithLp.toLp 2 p‖) := by fun_prop
  have hr : Measurable (fun p : ℝ × E ↦ p.1 / ‖WithLp.toLp 2 p‖) := by fun_prop
  exact (measurable_const.lt hn).and <|
    (hn.lt measurable_const).and
      (measurableSet_setOf.mp (hA.preimage hr))

/-- Identifies `norm_toLp_prod` with `sqrt`.

**Lean implementation helper.** -/
lemma norm_toLp_prod_eq_sqrt
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x : ℝ) (y : E) :
    ‖WithLp.toLp 2 (x, y)‖ = Real.sqrt (x ^ 2 + ‖y‖ ^ 2) := by
  rw [WithLp.prod_norm_eq_of_L2]
  simp only [WithLp.toLp_fst, WithLp.toLp_snd, Real.norm_eq_abs, sq_abs]

/-- The spherical volume of a first-coordinate planar sector is proportional to its opening angle.

**Lean implementation helper.** -/
lemma volume_unitSphereSector_first
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [Nontrivial E] {A : Set ℝ} (hA : MeasurableSet A) :
    (volume : Measure (WithLp 2 (ℝ × E)))
        (unitSphereSector (firstL2SphereCoordinate E ⁻¹' A)) =
      (volume : Measure E).toSphere Set.univ *
        ∫⁻ p : ℝ × ℝ,
          planeSectorDensity (Module.finrank ℝ E) A p ∂volume := by
  classical
  let T : Set (ℝ × E) := productSphereSectorFirst E A
  have hT : MeasurableSet T := measurableSet_productSphereSectorFirst E hA
  have hpre : WithLp.ofLp ⁻¹' T =
      unitSphereSector (firstL2SphereCoordinate E ⁻¹' A) := by
    ext p
    rw [mem_unitSphereSector_first_iff E A p]
    simp only [Set.mem_preimage, T, productSphereSectorFirst,
      Set.mem_setOf_eq, WithLp.toLp_ofLp]
  calc
    (volume : Measure (WithLp 2 (ℝ × E)))
        (unitSphereSector (firstL2SphereCoordinate E ⁻¹' A)) =
        (volume : Measure (ℝ × E)) T := by
      rw [← hpre]
      have hmp := WithLp.volume_preserving_ofLp ℝ E
      have hm := congrArg (fun μ : Measure (ℝ × E) ↦ μ T) hmp.map_eq
      rw [Measure.map_apply hmp.measurable hT] at hm
      exact hm
    _ = ∫⁻ x : ℝ, (volume : Measure E) (Prod.mk x ⁻¹' T) ∂volume := by
      rw [Measure.volume_eq_prod ℝ E, Measure.prod_apply hT]
    _ = ∫⁻ x : ℝ,
          (volume : Measure E).toSphere Set.univ *
            (∫⁻ s : Set.Ioi (0 : ℝ), sectorRadiusIndicator A x s
              ∂Measure.volumeIoiPow (Module.finrank ℝ E - 1)) ∂volume := by
      apply lintegral_congr
      intro x
      have hTx : MeasurableSet (Prod.mk x ⁻¹' T) :=
        hT.preimage (measurable_const.prodMk measurable_id)
      rw [← lintegral_indicator_one hTx]
      calc
        (∫⁻ y : E, (Prod.mk x ⁻¹' T).indicator 1 y ∂volume) =
            ∫⁻ y : E, sectorRadiusIndicator A x ‖y‖ ∂volume := by
          apply lintegral_congr
          intro y
          simp only [Set.indicator, Set.mem_preimage, T,
            productSphereSectorFirst, Set.mem_setOf_eq,
            sectorRadiusIndicator]
          rw [norm_toLp_prod_eq_sqrt]
          split_ifs <;> rfl
        _ = _ := lintegral_radial_volume E
          (sectorRadiusIndicator A x) ((measurable_sectorRadiusIndicator hA).comp
            (measurable_const.prodMk measurable_id))
    _ = (volume : Measure E).toSphere Set.univ *
          ∫⁻ x : ℝ, ∫⁻ s : Set.Ioi (0 : ℝ),
            sectorRadiusIndicator A x s
              ∂Measure.volumeIoiPow (Module.finrank ℝ E - 1) ∂volume := by
      have hjoint : Measurable (fun p : ℝ × Set.Ioi (0 : ℝ) ↦
          sectorRadiusIndicator A p.1 (p.2 : ℝ)) :=
        (measurable_sectorRadiusIndicator hA).comp
          (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd))
      exact lintegral_const_mul _ hjoint.lintegral_prod_right'
    _ = _ := by
      rw [lintegral_volumeIoiPow_sectorRadiusIndicator (hA := hA)]

/-- The first coordinate `firstL2SphereCoordinate` on the unit sphere of an `L²` product is measurable.

**Lean implementation helper.** -/
lemma measurable_firstL2SphereCoordinate
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] :
    Measurable (firstL2SphereCoordinate E) := by
  exact (measurable_firstL2Coordinate E).comp measurable_subtype_coe

/-- Defines `sphereAngularDensity`, the sphere angular density used in the surrounding construction.

**Lean implementation helper.** -/
def sphereAngularDensity (m : ℕ) (θ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.sin θ ^ ((m : ℝ) - 1))

/-- The sine-power angular weight `sphereAngularDensity` is measurable for every `m`.

**Lean implementation helper.** -/
lemma measurable_sphereAngularDensity (m : ℕ) :
    Measurable (sphereAngularDensity m) := by
  unfold sphereAngularDensity
  fun_prop

/-- Defines `sphereAngularMeasure`, the sphere angular measure used in the surrounding construction.

**Lean implementation helper.** -/
def sphereAngularMeasure (m : ℕ) : Measure ℝ :=
  (volume.restrict (Set.Ioo 0 Real.pi)).withDensity (sphereAngularDensity m)

/-- Identifies `sphereAngularDensity` with `natPow`.

**Lean implementation helper.** -/
lemma sphereAngularDensity_eq_natPow (m : ℕ) (hm : 0 < m)
    {θ : ℝ} (_hθ : θ ∈ Set.Ioo 0 Real.pi) :
    sphereAngularDensity m θ = ENNReal.ofReal (Real.sin θ ^ (m - 1)) := by
  unfold sphereAngularDensity
  rw [← Real.rpow_natCast, Nat.cast_pred hm]

/-- The preimage of a cosine interval under the angular coordinate has the corresponding angular-measure interval.

**Lean implementation helper.** -/
lemma sphereAngularMeasure_preimage_cos
    (m : ℕ) (hm : 0 < m) {A : Set ℝ} (hA : MeasurableSet A) :
    sphereAngularMeasure m (Real.cos ⁻¹' A) =
      ∫⁻ θ : ℝ in Set.Ioo 0 Real.pi ∩ Real.cos ⁻¹' A,
        ENNReal.ofReal (Real.sin θ ^ (m - 1)) ∂volume := by
  rw [sphereAngularMeasure, withDensity_apply _
    (hA.preimage Real.measurable_cos)]
  change (∫⁻ θ : ℝ, sphereAngularDensity m θ
      ∂((volume.restrict (Set.Ioo 0 Real.pi)).restrict (Real.cos ⁻¹' A))) = _
  rw [Measure.restrict_restrict (hA.preimage Real.measurable_cos), Set.inter_comm]
  apply setLIntegral_congr_fun
    (measurableSet_Ioo.inter (hA.preimage Real.measurable_cos))
  intro θ hθ
  exact sphereAngularDensity_eq_natPow m hm hθ.1

/-- The first coordinate of the two-dimensional sphere pushes uniform spherical measure to the arcsine law.

**Lean implementation helper.** -/
theorem map_firstL2SphereCoordinate_toSphere
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [Nontrivial E] :
    Measure.map (firstL2SphereCoordinate E)
        ((volume : Measure (WithLp 2 (ℝ × E))).toSphere) =
      (volume : Measure E).toSphere Set.univ •
        Measure.map Real.cos (sphereAngularMeasure (Module.finrank ℝ E)) := by
  classical
  let d := Module.finrank ℝ E
  have hd : 0 < d := Module.finrank_pos
  have hdim : Module.finrank ℝ (WithLp 2 (ℝ × E)) = d + 1 := by
    calc
      Module.finrank ℝ (WithLp 2 (ℝ × E)) = Module.finrank ℝ (ℝ × E) :=
        (WithLp.linearEquiv 2 ℝ (ℝ × E)).finrank_eq
      _ = Module.finrank ℝ ℝ + Module.finrank ℝ E := Module.finrank_prod
      _ = d + 1 := by simp [d, add_comm]
  have hcancel : (d + 1 : ℝ≥0∞) * ENNReal.ofReal ((1 : ℝ) / (d + 1)) = 1 := by
    rw [ENNReal.ofReal_div_of_pos (by positivity)]
    simp only [ENNReal.ofReal_one, one_div]
    have hc : (d + 1 : ℝ≥0∞) = ENNReal.ofReal ((d : ℝ) + 1) := by
      rw [show (d : ℝ) + 1 = ((d + 1 : ℕ) : ℝ) by norm_cast,
        ENNReal.ofReal_natCast]
      push_cast
      rfl
    rw [hc]
    exact ENNReal.mul_inv_cancel
      (ENNReal.ofReal_ne_zero_iff.mpr (by positivity)) ENNReal.ofReal_ne_top
  ext A hA
  rw [Measure.map_apply (measurable_firstL2SphereCoordinate E) hA,
    Measure.toSphere_apply' _ (hA.preimage (measurable_firstL2SphereCoordinate E))]
  change (Module.finrank ℝ (WithLp 2 (ℝ × E)) : ℝ≥0∞) *
      (volume : Measure (WithLp 2 (ℝ × E)))
        (unitSphereSector (firstL2SphereCoordinate E ⁻¹' A)) = _
  rw [volume_unitSphereSector_first E hA,
    lintegral_planeSectorDensity d hd hA]
  rw [Measure.smul_apply, Measure.map_apply Real.measurable_cos hA,
    sphereAngularMeasure_preimage_cos d hd hA]
  rw [hdim]
  simp only [smul_eq_mul]
  have hcastNat : ((d + 1 : ℕ) : ℝ≥0∞) = (d : ℝ≥0∞) + 1 := by
    push_cast
    rfl
  rw [hcastNat]
  let J : ℝ≥0∞ := ∫⁻ θ : ℝ in Set.Ioo 0 Real.pi ∩ Real.cos ⁻¹' A,
    ENNReal.ofReal (Real.sin θ ^ (d - 1)) ∂volume
  change ((d : ℝ≥0∞) + 1) *
      ((volume : Measure E).toSphere Set.univ *
        (ENNReal.ofReal ((1 : ℝ) / (d + 1)) * J)) =
    (volume : Measure E).toSphere Set.univ * J
  calc
    ((d : ℝ≥0∞) + 1) *
        ((volume : Measure E).toSphere Set.univ *
          (ENNReal.ofReal ((1 : ℝ) / (d + 1)) * J)) =
      (volume : Measure E).toSphere Set.univ *
        (((d : ℝ≥0∞) + 1) * ENNReal.ofReal ((1 : ℝ) / (d + 1))) * J := by
          ac_rfl
    _ = _ := by rw [hcancel, mul_one]

/-- Pushing a density through a measurable equivalence transforms it by composition with the inverse map.

**Book Section 3.3.** -/
lemma map_withDensity_comp_hdp
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (f : α → β) (g : β → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) :
    Measure.map f (μ.withDensity (g ∘ f)) =
      (Measure.map f μ).withDensity g := by
  ext s hs
  rw [Measure.map_apply_of_aemeasurable
      (hf.aemeasurable.mono_ac (withDensity_absolutelyContinuous μ _)) hs,
    withDensity_apply _ (hs.preimage hf), withDensity_apply _ hs]
  exact (setLIntegral_map hs hg hf).symm

/-- The cosine map transforms angular Lebesgue measure with the reciprocal square-root Jacobian.

**Lean implementation helper.** -/
lemma map_cos_jacobian :
    Measure.map Real.cos
        ((volume.restrict (Set.Ioo 0 Real.pi)).withDensity
          (fun θ ↦ ENNReal.ofReal |(-Real.sin θ)|)) =
      volume.restrict (Set.Ioo (-1) 1) := by
  have h := map_withDensity_abs_det_fderiv_eq_addHaar
    (μ := (volume : Measure ℝ)) (s := Set.Ioo 0 Real.pi)
    (f := Real.cos)
    (f' := fun θ ↦ ContinuousLinearMap.toSpanSingleton ℝ (-Real.sin θ))
    measurableSet_Ioo.nullMeasurableSet
    (fun θ _ ↦ (Real.hasDerivAt_cos θ).hasFDerivAt.hasFDerivWithinAt)
    Real.cosPartialHomeomorph.injOn
  have him := Real.cosPartialHomeomorph.image_source_eq_target
  change Real.cos '' Set.Ioo 0 Real.pi = Set.Ioo (-1) 1 at him
  rw [him] at h
  simpa only [ContinuousLinearMap.det_toSpanSingleton] using h

/-- Defines `sphereCoordinateDensity`, the sphere coordinate density used in the surrounding construction.

**Lean implementation helper.** -/
def sphereCoordinateDensity (m : ℕ) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((1 - x ^ 2) ^ (((m : ℝ) - 2) / 2))

/-- The power profile `sphereCoordinateDensity` for one spherical coordinate is measurable.

**Lean implementation helper.** -/
lemma measurable_sphereCoordinateDensity (m : ℕ) :
    Measurable (sphereCoordinateDensity m) := by
  unfold sphereCoordinateDensity
  fun_prop

/-- The cosine-map Jacobian density `cosJacobian`, namely `θ ↦ ENNReal.ofReal | -sin θ |`, is measurable.

**Lean implementation helper.** -/
lemma measurable_cosJacobian :
    Measurable (fun θ : ℝ ↦ ENNReal.ofReal |(-Real.sin θ)|) := by
  fun_prop

/-- The spherical angular density factors into its normalization constant and the appropriate power of `1-t²`.

**Lean implementation helper.** -/
lemma sphereAngularDensity_factor (m : ℕ) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    sphereAngularDensity m θ =
      ENNReal.ofReal |(-Real.sin θ)| *
        sphereCoordinateDensity m (Real.cos θ) := by
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have htrig : 1 - Real.cos θ ^ 2 = Real.sin θ ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hsq :
      (Real.sin θ ^ 2) ^ (((m : ℝ) - 2) / 2) =
        Real.sin θ ^ ((m : ℝ) - 2) := by
    calc
      (Real.sin θ ^ 2) ^ (((m : ℝ) - 2) / 2) =
          (Real.sin θ ^ (2 : ℝ)) ^ (((m : ℝ) - 2) / 2) := by
            rw [Real.rpow_two]
      _ = Real.sin θ ^ ((2 : ℝ) * (((m : ℝ) - 2) / 2)) :=
        (Real.rpow_mul hs.le _ _).symm
      _ = Real.sin θ ^ ((m : ℝ) - 2) := by ring_nf
  have hmul :
      Real.sin θ * Real.sin θ ^ ((m : ℝ) - 2) =
        Real.sin θ ^ ((m : ℝ) - 1) := by
    calc
      Real.sin θ * Real.sin θ ^ ((m : ℝ) - 2) =
          Real.sin θ ^ (1 : ℝ) * Real.sin θ ^ ((m : ℝ) - 2) := by
            rw [Real.rpow_one]
      _ = Real.sin θ ^ ((1 : ℝ) + ((m : ℝ) - 2)) :=
        (Real.rpow_add hs _ _).symm
      _ = Real.sin θ ^ ((m : ℝ) - 1) := by ring_nf
  rw [sphereAngularDensity, sphereCoordinateDensity, abs_neg, abs_of_pos hs,
    ← ENNReal.ofReal_mul hs.le, htrig, hsq, hmul]

/-- Pushing spherical angular measure through cosine gives the one-coordinate spherical marginal law.

**Lean implementation helper.** -/
theorem map_cos_sphereAngularMeasure (m : ℕ) :
    Measure.map Real.cos (sphereAngularMeasure m) =
      (volume.restrict (Set.Ioo (-1) 1)).withDensity
        (sphereCoordinateDensity m) := by
  have hdens : sphereAngularDensity m =ᵐ[volume.restrict (Set.Ioo 0 Real.pi)]
      (fun θ ↦ ENNReal.ofReal |(-Real.sin θ)| *
        sphereCoordinateDensity m (Real.cos θ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
    exact sphereAngularDensity_factor m hθ
  have hwd :
      (volume.restrict (Set.Ioo 0 Real.pi)).withDensity
          (fun θ ↦ ENNReal.ofReal |(-Real.sin θ)| *
            sphereCoordinateDensity m (Real.cos θ)) =
        ((volume.restrict (Set.Ioo 0 Real.pi)).withDensity
            (fun θ ↦ ENNReal.ofReal |(-Real.sin θ)|)).withDensity
          (sphereCoordinateDensity m ∘ Real.cos) := by
    exact withDensity_mul (volume.restrict (Set.Ioo 0 Real.pi))
      measurable_cosJacobian
      ((measurable_sphereCoordinateDensity m).comp Real.measurable_cos)
  rw [sphereAngularMeasure, withDensity_congr_ae hdens, hwd,
    map_withDensity_comp_hdp _ _ _ Real.measurable_cos
      (measurable_sphereCoordinateDensity m), map_cos_jacobian]

/-- Exact one-dimensional marginal densities for uniform sphere/ball laws.

**Book Remark 3.3.10.** -/
def sphereMarginalDensity (m : ℕ) : ℝ → ℝ≥0∞ :=
  (Set.Ioo (-1 : ℝ) 1).indicator (sphereCoordinateDensity m)

/-- The interval-supported one-coordinate density `sphereMarginalDensity` is measurable.

**Lean implementation helper.** -/
lemma measurable_sphereMarginalDensity (m : ℕ) :
    Measurable (sphereMarginalDensity m) := by
  exact (measurable_sphereCoordinateDensity m).indicator measurableSet_Ioo

/-- The spherical marginal measure is Lebesgue measure weighted by the explicit spherical marginal density.

**Lean implementation helper.** -/
lemma withDensity_sphereMarginalDensity (m : ℕ) :
    volume.withDensity (sphereMarginalDensity m) =
      (volume.restrict (Set.Ioo (-1 : ℝ) 1)).withDensity
        (sphereCoordinateDensity m) := by
  exact withDensity_indicator measurableSet_Ioo (sphereCoordinateDensity m)

/-- Identifies `smul_withDensity` with `withDensity_const_mul`.

**Lean implementation helper.** -/
lemma smul_withDensity_eq_withDensity_const_mul
    (c : ℝ≥0∞) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    c • volume.withDensity f = volume.withDensity (fun x ↦ c * f x) := by
  ext A hA
  rw [Measure.smul_apply, withDensity_apply _ hA, withDensity_apply _ hA]
  change c * (∫⁻ x in A, f x ∂volume) = ∫⁻ x in A, c * f x ∂volume
  exact (lintegral_const_mul c hf).symm

/-- Exact one-dimensional marginal densities for uniform sphere/ball laws.

**Book Remark 3.3.10.** -/
theorem map_firstL2SphereCoordinate_unitSphereMeasure
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [Nontrivial E] :
    Measure.map (firstL2SphereCoordinate E)
        (unitSphereMeasure (WithLp 2 (ℝ × E))) =
      volume.withDensity (fun x ↦
        (((volume : Measure (WithLp 2 (ℝ × E))).toSphere Set.univ)⁻¹ *
          (volume : Measure E).toSphere Set.univ) *
            sphereMarginalDensity (Module.finrank ℝ E) x) := by
  simp only [unitSphereMeasure, ProbabilityTheory.cond, Measure.restrict_univ]
  rw [Measure.map_smul, map_firstL2SphereCoordinate_toSphere,
    smul_smul, map_cos_sphereAngularMeasure,
    ← withDensity_sphereMarginalDensity,
    smul_withDensity_eq_withDensity_const_mul
      (((volume : Measure (WithLp 2 (ℝ × E))).toSphere Set.univ)⁻¹ *
        (volume : Measure E).toSphere Set.univ)
      (measurable_sphereMarginalDensity _)]

namespace Chapter3

/-- In the
orthogonal decomposition `ℝ ⊕₂ E`, the first coordinate of normalized
volume on the Euclidean unit ball has density proportional to
`(1 - x²)^(dim(E)/2)`. Since the ambient dimension is `1 + dim(E)`, this is
the source exponent `(n-1)/2`. This is a genuine push-forward identity.

This source-numbered endpoint lives in the core module because later text
uses the marginal density; the exercise tree contains no authoritative copy.

**Book Exercise 3.27.** -/
theorem exercise_3_27a
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [Nontrivial E] :
    Measure.map (HDP.firstL2Coordinate E)
        (HDP.unitBallMeasure (WithLp 2 (ℝ × E))) =
      volume.withDensity (fun x ↦
        ((volume (Metric.closedBall (0 : WithLp 2 (ℝ × E)) 1))⁻¹ *
          volume (Metric.closedBall (0 : E) 1)) *
            HDP.marginalPowerDensity ((Module.finrank ℝ E : ℝ) / 2) x) := by
  exact HDP.map_firstL2Coordinate_unitBallMeasure_eq_power E

/-- In the
orthogonal decomposition `ℝ ⊕₂ E`, the first coordinate of normalized
surface measure on the Euclidean unit sphere has density proportional to
`(1 - x²)^((dim(E)-2)/2)` on `(-1,1)`. Since the ambient dimension is
`1 + dim(E)`, this is exactly `(n-3)/2`. The proof derives the push-forward
from Mathlib's `volume.toSphere`, polar decomposition, and the cosine
Jacobian, including the singular ambient two-dimensional case.

This source-numbered endpoint lives in the core module because later text
uses the marginal density; the exercise tree contains no authoritative copy.

**Book Exercise 3.27.** -/
theorem exercise_3_27b
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [Nontrivial E] :
    Measure.map (HDP.firstL2SphereCoordinate E)
        (HDP.unitSphereMeasure (WithLp 2 (ℝ × E))) =
      volume.withDensity (fun x ↦
        (((volume : Measure (WithLp 2 (ℝ × E))).toSphere Set.univ)⁻¹ *
          (volume : Measure E).toSphere Set.univ) *
            HDP.sphereMarginalDensity (Module.finrank ℝ E) x) := by
  exact HDP.map_firstL2SphereCoordinate_unitSphereMeasure E

end Chapter3

end
end HDP

end Source_11_SphereCoordinateMarginals

/-! ## Material formerly in `12_Frames.lean` -/

section Source_12_Frames

/-!
# Book Chapter 3, Section 3.3.5: Parseval frames

This module proves all four equivalences in Book Proposition 3.3.11.  The
probabilistic clause is represented on the finite probability space `Fin N`
with its uniform measure, so the random vector really is uniform on the
indexed family `√N • uᵢ` (with repetitions retained, as in sampling an index
uniformly).
-/

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators ENNReal NNReal RealInnerProductSpace

namespace HDP

/-! ## Book-wide frame predicates -/

variable {E ι : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Parseval identity for a finite family of vectors.

**Book Proposition 3.3.11.** -/
def IsParsevalFrame (u : ι → E) : Prop :=
  ∀ x : E, ‖x‖ ^ 2 = ∑ i, (inner ℝ (u i) x) ^ 2

/-- Pointwise frame expansion.

**Lean implementation helper.** -/
def HasFrameExpansion (u : ι → E) : Prop :=
  ∀ x : E, x = ∑ i, (inner ℝ (u i) x) • u i

/-- Extensional form of `I = ∑ᵢ uᵢuᵢᵀ`.

Writing the operator identity pointwise avoids choosing coordinates and is
definitionally the same assertion as frame expansion.

**Lean implementation helper.** -/
def HasIdentityDecomposition (u : ι → E) : Prop :=
  ∀ x : E, x = ∑ i, (inner ℝ (u i) x) • u i

/-- The inner product with a finite sum in the left argument equals the sum of the individual inner products.

**Lean implementation helper.** -/
lemma inner_univ_sum_left (f : ι → E) (y : E) :
    inner ℝ (∑ i, f i) y = ∑ i, inner ℝ (f i) y := by
  change (innerSLFlip ℝ y) (∑ i, f i) = _
  rw [map_sum]
  simp

/-- Polarization of the Parseval identity.

**Lean implementation helper.** -/
theorem IsParsevalFrame.inner_identity {u : ι → E} (h : IsParsevalFrame u)
    (x y : E) :
    inner ℝ x y = ∑ i, inner ℝ (u i) x * inner ℝ (u i) y := by
  have hp := h (x + y)
  have hx := h x
  have hy := h y
  rw [norm_add_sq_real] at hp
  rw [hx, hy] at hp
  simp_rw [inner_add_right] at hp
  have hsq : ∀ i,
      (inner ℝ (u i) x + inner ℝ (u i) y) ^ 2 =
        (inner ℝ (u i) x) ^ 2 + (inner ℝ (u i) y) ^ 2 +
          2 * (inner ℝ (u i) x * inner ℝ (u i) y) := by
    intro i
    ring
  simp_rw [hsq, Finset.sum_add_distrib] at hp
  rw [← Finset.mul_sum] at hp
  linarith

/-- Parseval identity is equivalent to frame expansion.

**Lean implementation helper.** -/
theorem isParsevalFrame_iff_hasFrameExpansion (u : ι → E) :
    IsParsevalFrame u ↔ HasFrameExpansion u := by
  constructor
  · intro h x
    let z : E := x - ∑ i, (inner ℝ (u i) x) • u i
    have hzy : ∀ y : E, inner ℝ z y = 0 := by
      intro y
      calc
        inner ℝ z y = inner ℝ x y -
            inner ℝ (∑ i, (inner ℝ (u i) x) • u i) y := by
          simp [z, inner_sub_left]
        _ = inner ℝ x y -
            ∑ i, inner ℝ (u i) x * inner ℝ (u i) y := by
          rw [inner_univ_sum_left]
          simp_rw [inner_smul_left]
          simp
        _ = 0 := by rw [h.inner_identity x y]; ring
    have hz : z = 0 := inner_self_eq_zero.mp (hzy z)
    simpa [z] using sub_eq_zero.mp hz
  · intro h x
    calc
      ‖x‖ ^ 2 = inner ℝ x x := (real_inner_self_eq_norm_sq x).symm
      _ = inner ℝ (∑ i, (inner ℝ (u i) x) • u i) x :=
        congrArg (fun z : E => inner ℝ z x) (h x)
      _ = ∑ i, (inner ℝ (u i) x) ^ 2 := by
        rw [inner_univ_sum_left]
        simp_rw [inner_smul_left]
        simp [pow_two]

/-- Characterizes `hasFrameExpansion` by the equivalent condition `hasIdentityDecomposition`.

**Lean implementation helper.** -/
@[simp]
theorem hasFrameExpansion_iff_hasIdentityDecomposition (u : ι → E) :
    HasFrameExpansion u ↔ HasIdentityDecomposition u := Iff.rfl

/-! ## The finite uniform frame law -/

variable {n N : ℕ} [NeZero N]

/-- Sampling the indexed family `√N • uᵢ` uniformly.

**Lean implementation helper.** -/
noncomputable def frameRandomVector
    (u : Fin N → EuclideanSpace ℝ (Fin n)) :
    Fin N → EuclideanSpace ℝ (Fin n) :=
  fun i => Real.sqrt N • u i

/-- The second moments of the uniform frame law are the entries of
`∑ᵢ uᵢuᵢᵀ`; the factors `N` and `1/N` cancel.

**Lean implementation helper.** -/
theorem frame_secondMomentMatrix_apply
    (u : Fin N → EuclideanSpace ℝ (Fin n)) (a b : Fin n) :
    secondMomentMatrix (frameRandomVector u)
        (uniformOn (Set.univ : Set (Fin N))) a b =
      ∑ i, u i a * u i b := by
  change (∫ i, (frameRandomVector u i) a * (frameRandomVector u i) b
      ∂uniformOn (Set.univ : Set (Fin N))) = _
  unfold uniformOn ProbabilityTheory.cond
  rw [Measure.restrict_univ, integral_smul_measure, integral_count]
  simp only [frameRandomVector, PiLp.smul_apply, smul_eq_mul]
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hterm : ∀ i : Fin N,
      Real.sqrt N * u i a * (Real.sqrt N * u i b) =
        N * (u i a * u i b) := by
    intro i
    calc
      Real.sqrt N * u i a * (Real.sqrt N * u i b) =
          (Real.sqrt N) ^ 2 * (u i a * u i b) := by ring
      _ = N * (u i a * u i b) := by
        rw [Real.sq_sqrt (Nat.cast_nonneg N)]
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  simp [Measure.count_univ, ENat.card_eq_coe_fintype_card, hN]

/-- Parseval identity is equivalent to isotropy of the associated discrete
uniform random vector.

**Book Proposition 3.3.11.** -/
theorem isParsevalFrame_iff_frame_isIsotropic
    (u : Fin N → EuclideanSpace ℝ (Fin n)) :
    IsParsevalFrame u ↔
      IsIsotropic (frameRandomVector u)
        (uniformOn (Set.univ : Set (Fin N))) := by
  constructor
  · intro h
    apply isIsotropic_iff.mpr
    intro a b
    change secondMomentMatrix (frameRandomVector u)
      (uniformOn (Set.univ : Set (Fin N))) a b = _
    rw [frame_secondMomentMatrix_apply]
    have hab := h.inner_identity
      (EuclideanSpace.single a 1) (EuclideanSpace.single b 1)
    simpa [PiLp.inner_apply, Real.inner_apply, Matrix.one_apply,
      Finset.mul_sum, Finset.sum_mul] using hab.symm
  · intro h x
    have hinner : ∀ a b : Fin n,
        ∑ i, u i a * u i b = if a = b then 1 else 0 := by
      intro a b
      have hab := isIsotropic_iff.mp h a b
      change secondMomentMatrix (frameRandomVector u)
        (uniformOn (Set.univ : Set (Fin N))) a b = _ at hab
      rwa [frame_secondMomentMatrix_apply] at hab
    apply (isParsevalFrame_iff_hasFrameExpansion u).mpr
    intro x
    ext a
    have hsum_apply :
        (∑ i, (inner ℝ (u i) x) • u i) a =
          ∑ i, ((inner ℝ (u i) x) • u i) a := by
      exact map_sum
        (PiLp.projₗ (𝕜 := ℝ) (β := fun _ : Fin n => ℝ) 2 a)
        (fun i => (inner ℝ (u i) x) • u i) Finset.univ
    rw [hsum_apply]
    simp only [PiLp.smul_apply, smul_eq_mul, PiLp.inner_apply, Real.inner_apply]
    change x a = ∑ i, (∑ b, u i b * x b) * u i a
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    symm
    calc
      ∑ b, ∑ i, u i b * x b * u i a =
          ∑ b, x b * ∑ i, u i b * u i a := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = ∑ b, x b * (if b = a then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [hinner]
      _ = x a := by simp

end HDP

namespace HDP.Chapter3

open HDP

/-- Parseval identity, frame
expansion, decomposition of the identity, and isotropy of the corresponding
finite uniform distribution are equivalent.

**Book Proposition 3.3.11.** -/
theorem proposition_3_3_11 {n N : ℕ} [NeZero N]
    (u : Fin N → EuclideanSpace ℝ (Fin n)) :
    (IsParsevalFrame u ↔ HasFrameExpansion u) ∧
    (HasFrameExpansion u ↔ HasIdentityDecomposition u) ∧
    (HasIdentityDecomposition u ↔
      IsIsotropic (frameRandomVector u)
        (uniformOn (Set.univ : Set (Fin N)))) := by
  refine ⟨isParsevalFrame_iff_hasFrameExpansion u,
    hasFrameExpansion_iff_hasIdentityDecomposition u, ?_⟩
  rw [← hasFrameExpansion_iff_hasIdentityDecomposition]
  exact (isParsevalFrame_iff_hasFrameExpansion u).symm.trans
    (isParsevalFrame_iff_frame_isIsotropic u)

/-- The canonical coordinate frame in `ℝⁿ`.

**Book Example 3.3.12.** -/
noncomputable def coordinateParsevalFrame (n : ℕ) :
    Fin n → EuclideanSpace ℝ (Fin n) :=
  fun i => EuclideanSpace.single i 1

/-- The standard basis is a Parseval frame.

**Book Example 3.3.12.** -/
theorem coordinate_parsevalFrame (n : ℕ) :
    HDP.IsParsevalFrame (coordinateParsevalFrame n) := by
  intro x
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [coordinateParsevalFrame, EuclideanSpace.inner_single_left]

/-- The coordinate distribution `Unif {√n eᵢ}` is isotropic.

**Book Example 3.3.12.** -/
theorem coordinateDistribution_isIsotropic (n : ℕ) [NeZero n] :
    HDP.IsIsotropic (HDP.frameRandomVector (coordinateParsevalFrame n))
      (uniformOn (Set.univ : Set (Fin n))) :=
  (HDP.isParsevalFrame_iff_frame_isIsotropic
    (coordinateParsevalFrame n)).mp (coordinate_parsevalFrame n)

/-! ## Example 3.3.13: the Mercedes-Benz frame -/

/-- The three equispaced radius-`sqrt (2/3)` vectors in the plane.

**Book Example 3.3.13.** -/
noncomputable def mercedesBenzFrame :
    Fin 3 → EuclideanSpace ℝ (Fin 2) :=
  ![WithLp.toLp 2 ![√(2 / 3 : ℝ), 0],
    WithLp.toLp 2 ![-√(1 / 6 : ℝ), √(1 / 2 : ℝ)],
    WithLp.toLp 2 ![-√(1 / 6 : ℝ), -√(1 / 2 : ℝ)]]

/-- The Mercedes-Benz vectors reconstruct every vector in `R^2`.

**Book Example 3.3.13.** -/
theorem mercedesBenz_hasFrameExpansion :
    HDP.HasFrameExpansion mercedesBenzFrame := by
  have ha : (√(2 / 3 : ℝ)) ^ 2 = 2 / 3 :=
    Real.sq_sqrt (by norm_num)
  have hb : (√(1 / 6 : ℝ)) ^ 2 = 1 / 6 :=
    Real.sq_sqrt (by norm_num)
  have hc : (√(1 / 2 : ℝ)) ^ 2 = 1 / 2 :=
    Real.sq_sqrt (by norm_num)
  have hs2 : (√(2 : ℝ)) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hs3 : (√(3 : ℝ)) ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  have hs6 : (√(6 : ℝ)) ^ 2 = 6 :=
    Real.sq_sqrt (by norm_num)
  have hi2 : (√(2 : ℝ))⁻¹ ^ 2 = 1 / 2 := by
    rw [inv_pow, hs2]
    norm_num
  have hi3 : (√(3 : ℝ))⁻¹ ^ 2 = 1 / 3 := by
    rw [inv_pow, hs3]
    norm_num
  have hi6 : (√(6 : ℝ))⁻¹ ^ 2 = 1 / 6 := by
    rw [inv_pow, hs6]
    norm_num
  intro x
  ext k
  fin_cases k
  · simp [mercedesBenzFrame, PiLp.inner_apply, Fin.sum_univ_succ]
    ring_nf
    rw [hs2, hi3, hi6]
    ring
  · simp [mercedesBenzFrame, PiLp.inner_apply, Fin.sum_univ_succ]
    ring_nf
    rw [hi2]
    ring

/-- Three equispaced points on the circle of radius
`sqrt (2/3)` form a Parseval frame in `R^2`.

**Book Example 3.3.13.** -/
theorem mercedesBenz_parsevalFrame :
    HDP.IsParsevalFrame mercedesBenzFrame :=
  (HDP.isParsevalFrame_iff_hasFrameExpansion mercedesBenzFrame).2
    mercedesBenz_hasFrameExpansion

end HDP.Chapter3

end Source_12_Frames

/-! ## Material formerly in `13_SubGaussianVectors.lean` -/

section Source_13_SubGaussianVectors

/-!
# Subgaussian random vectors
-/

open MeasureTheory ProbabilityTheory Real Filter
open scoped RealInnerProductSpace ENNReal NNReal Topology BigOperators

namespace HDP.Chapter3

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Independent centered
subgaussian coordinates form a subgaussian random vector.

**Book Lemma 3.4.2.** -/
theorem subGaussianVector_of_independent_coordinates
    [IsProbabilityMeasure μ] {n : ℕ} {X : Fin n → Ω → ℝ}
    (hXm : ∀ i, AEMeasurable (X i) μ)
    (hX : ∀ i, HDP.SubGaussian (X i) μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hindep : iIndepFun X μ) :
    HDP.SubGaussianVector (vectorOfCoordinates X) μ := by
  intro u
  let Y : Fin n → Ω → ℝ := fun i ω => u i * X i ω
  have hYm : ∀ i, AEMeasurable (Y i) μ := fun i =>
    (hXm i).const_mul (u i)
  have hY : ∀ i, HDP.SubGaussian (Y i) μ := fun i =>
    (hX i).const_mul (u i)
  have hYmean : ∀ i, ∫ ω, Y i ω ∂μ = 0 := by
    intro i
    rw [show Y i = fun ω => u i * X i ω by rfl,
      integral_const_mul, hmean i, mul_zero]
  have hYindep : iIndepFun Y μ :=
    hindep.comp (fun i x => u i * x) (fun i => measurable_const_mul (u i))
  have hsum := (HDP.psi2Norm_sum_sq_le hYm hY hYmean hYindep).1
  simpa [Y, vectorOfCoordinates, PiLp.inner_apply, Real.inner_apply,
    mul_comm] using hsum

/-- The explicit absolute
constant supplied by Chapter 2 is `√30`.

**Book Lemma 3.4.2.** -/
theorem psi2NormVector_independent_coordinates_le
    [IsProbabilityMeasure μ] {n : ℕ} [NeZero n]
    {X : Fin n → Ω → ℝ}
    (hXm : ∀ i, AEMeasurable (X i) μ)
    (hX : ∀ i, HDP.SubGaussian (X i) μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hindep : iIndepFun X μ) {K : ℝ} (hK : 0 ≤ K)
    (hKb : ∀ i, HDP.psi2Norm (X i) μ ≤ K) :
    HDP.psi2NormVector (vectorOfCoordinates X) μ ≤ Real.sqrt 30 * K := by
  let B : ℝ := Real.sqrt 30 * K
  have hB : 0 ≤ B := mul_nonneg (Real.sqrt_nonneg _) hK
  have hpoint : ∀ u : EuclideanSpace ℝ (Fin n), ‖u‖ = 1 →
      HDP.psi2Norm
        (fun ω => inner ℝ (vectorOfCoordinates X ω) u) μ ≤ B := by
    intro u hu
    let Y : Fin n → Ω → ℝ := fun i ω => u i * X i ω
    have hYm : ∀ i, AEMeasurable (Y i) μ := fun i =>
      (hXm i).const_mul (u i)
    have hY : ∀ i, HDP.SubGaussian (Y i) μ := fun i =>
      (hX i).const_mul (u i)
    have hYmean : ∀ i, ∫ ω, Y i ω ∂μ = 0 := by
      intro i
      rw [show Y i = fun ω => u i * X i ω by rfl,
        integral_const_mul, hmean i, mul_zero]
    have hYindep : iIndepFun Y μ :=
      hindep.comp (fun i x => u i * x) (fun i => measurable_const_mul (u i))
    have hs := (HDP.psi2Norm_sum_sq_le hYm hY hYmean hYindep).2
    have hpsiSq : ∀ i, HDP.psi2Norm (X i) μ ^ 2 ≤ K ^ 2 := fun i =>
      (sq_le_sq₀ (HDP.psi2Norm_nonneg (X i) μ) hK).2 (hKb i)
    have hsum : ∑ i, HDP.psi2Norm (Y i) μ ^ 2 ≤ K ^ 2 := by
      calc
        ∑ i, HDP.psi2Norm (Y i) μ ^ 2
            ≤ ∑ i, (u i) ^ 2 * K ^ 2 := by
              apply Finset.sum_le_sum
              intro i hi
              rw [show Y i = fun ω => u i * X i ω by rfl,
                HDP.psi2Norm_const_mul]
              rw [mul_pow, sq_abs]
              exact mul_le_mul_of_nonneg_left (hpsiSq i) (sq_nonneg (u i))
        _ = K ^ 2 * ∑ i, (u i) ^ 2 := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i hi
              ring
        _ = K ^ 2 := by
              rw [← EuclideanSpace.real_norm_sq_eq, hu]
              norm_num
    have hs' : HDP.psi2Norm (fun ω => ∑ i, Y i ω) μ ^ 2 ≤ 30 * K ^ 2 :=
      hs.trans (mul_le_mul_of_nonneg_left hsum (by norm_num))
    have hsumEq : (fun ω => ∑ i, Y i ω) =
        fun ω => inner ℝ (vectorOfCoordinates X ω) u := by
      funext ω
      simp [Y, vectorOfCoordinates, PiLp.inner_apply,
        mul_comm]
    rw [hsumEq] at hs'
    apply (sq_le_sq₀ (HDP.psi2Norm_nonneg _ μ) hB).1
    calc
      HDP.psi2Norm
          (fun ω => inner ℝ (vectorOfCoordinates X ω) u) μ ^ 2
          ≤ 30 * K ^ 2 := hs'
      _ = B ^ 2 := by
        dsimp [B]
        rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 30)]
  rw [HDP.psi2NormVector]
  apply csSup_le
  · let e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single 0 1
    exact ⟨HDP.psi2Norm
      (fun ω => inner ℝ (vectorOfCoordinates X ω) e) μ, e, by simp [e], rfl⟩
  · intro r hr
    rcases hr with ⟨u, hu, rfl⟩
    exact hpoint u hu

/-- A vector with independent Rademacher coordinates
is subgaussian, with an explicit dimension-free vector psi-two bound.

**Book Example 3.4.3.** -/
theorem rademacherVector_subGaussian
    [IsProbabilityMeasure μ] {n : ℕ} [NeZero n]
    {X : Fin n → Ω → ℝ}
    (hX : ∀ i, HDP.IsRademacher (X i) μ)
    (hindep : iIndepFun X μ) :
    HDP.SubGaussianVector (vectorOfCoordinates X) μ ∧
      HDP.psi2NormVector (vectorOfCoordinates X) μ ≤
        Real.sqrt 30 / Real.sqrt (Real.log 2) := by
  have hsub : ∀ i, HDP.SubGaussian (X i) μ := by
    intro i
    exact (HDP.psi2Norm_le_of_bounded (M := (1 : ℝ)) one_pos (by
      filter_upwards [(hX i).ae_mem] with ω hω
      rcases hω with hω | hω <;> rw [hω] <;> norm_num)).1
  constructor
  · exact subGaussianVector_of_independent_coordinates
      (fun i => (hX i).aemeasurable) hsub
      (fun i => (hX i).integral_eq_zero) hindep
  · have hK : 0 ≤ 1 / Real.sqrt (Real.log 2) := by
      positivity
    have h := psi2NormVector_independent_coordinates_le
      (fun i => (hX i).aemeasurable) hsub
      (fun i => (hX i).integral_eq_zero) hindep hK
      (fun i => (HDP.psi2Norm_rademacher (hX i)).le)
    simpa [div_eq_mul_inv] using h

/-- The coordinate lower bound in the source Lemma 3.4.2.

**Book Lemma 3.4.2.** -/
theorem psi2Norm_coordinate_le_vector
    [IsProbabilityMeasure μ] {n : ℕ} [NeZero n]
    {X : Fin n → Ω → ℝ}
    (hbounded : BddAbove {r : ℝ |
      ∃ u : EuclideanSpace ℝ (Fin n), ‖u‖ = 1 ∧
        r = HDP.psi2Norm
          (fun ω => inner ℝ (vectorOfCoordinates X ω) u) μ})
    (i : Fin n) :
    HDP.psi2Norm (X i) μ ≤
      HDP.psi2NormVector (vectorOfCoordinates X) μ := by
  let e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i 1
  have h := HDP.psi2Norm_marginal_le_vector hbounded
    (u := e) (by simp [e])
  simpa [e, vectorOfCoordinates, EuclideanSpace.inner_single_right] using h

/-- The vector ψ₂ norm controls
every marginal with the correct homogeneous factor. The explicit boundedness
hypothesis is required because `psi2NormVector` is a real-valued `sSup`.

**Book Exercise 3.32.** -/
theorem psi2Norm_marginal_le_norm_mul_vector
    [IsProbabilityMeasure μ]
    {n : ℕ} {X : Ω → EuclideanSpace ℝ (Fin n)}
    (hbounded : BddAbove {r : ℝ |
      ∃ u : EuclideanSpace ℝ (Fin n), ‖u‖ = 1 ∧
        r = HDP.psi2Norm (fun ω => inner ℝ (X ω) u) μ})
    (v : EuclideanSpace ℝ (Fin n)) :
    HDP.psi2Norm (fun ω => inner ℝ (X ω) v) μ ≤
      ‖v‖ * HDP.psi2NormVector X μ := by
  by_cases hv : v = 0
  · subst v
    have hz := HDP.psi2Norm_const_mul
      (μ := μ) (fun _ : Ω => (0 : ℝ)) 0
    simpa using hz.le
  · let u : EuclideanSpace ℝ (Fin n) := ‖v‖⁻¹ • v
    have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hu : ‖u‖ = 1 := by
      simp [u, norm_smul, hvpos.ne']
    have hunit := HDP.psi2Norm_marginal_le_vector hbounded hu
    have hfun : (fun ω => inner ℝ (X ω) v) =
        fun ω => ‖v‖ * inner ℝ (X ω) u := by
      funext ω
      simp [u, inner_smul_right, hvpos.ne']
    rw [hfun, HDP.psi2Norm_const_mul, abs_of_pos hvpos]
    exact mul_le_mul_of_nonneg_left hunit hvpos.le

/-- Every one-dimensional marginal of the standard Gaussian vector has the
book's exact ψ₂ norm `‖u‖ √(8/3)`.

**Book Example 3.4.4.** -/
theorem psi2Norm_standardGaussian_marginal
    {n : ℕ} (u : EuclideanSpace ℝ (Fin n)) :
    HDP.psi2Norm
      (fun z : EuclideanSpace ℝ (Fin n) => inner ℝ z u)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) =
      ‖u‖ * Real.sqrt (8 / 3) := by
  have hLaw := standardGaussian_inner_hasLaw u
  have hLaw' : HasLaw
      (fun z : EuclideanSpace ℝ (Fin n) => inner ℝ z u)
      (gaussianReal 0 ⟨‖u‖ ^ 2, sq_nonneg ‖u‖⟩)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
    convert hLaw using 1
    · ext z
      exact real_inner_comm _ _
    · congr 2
      exact (max_eq_left (sq_nonneg ‖u‖)).symm
  simpa [abs_of_nonneg (norm_nonneg u)] using
    (HDP.psi2Norm_gaussian
      (μ := stdGaussian (EuclideanSpace ℝ (Fin n))) ‖u‖ hLaw')

/-- **Gaussian vector ψ₂ calculation.** In every positive dimension, the
standard Gaussian vector has vector ψ₂ norm `√(8/3)`.

**Book Example 3.4.4.** -/
theorem psi2NormVector_standardGaussian (n : ℕ) [NeZero n] :
    HDP.psi2NormVector
      (fun z : EuclideanSpace ℝ (Fin n) => z)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) =
      Real.sqrt (8 / 3) := by
  let c : ℝ := Real.sqrt (8 / 3)
  have hset :
      {r : ℝ | ∃ u : EuclideanSpace ℝ (Fin n), ‖u‖ = 1 ∧
        r = HDP.psi2Norm
          (fun z : EuclideanSpace ℝ (Fin n) => inner ℝ z u)
          (stdGaussian (EuclideanSpace ℝ (Fin n)))} = {c} := by
    ext r
    constructor
    · rintro ⟨u, hu, rfl⟩
      simp [psi2Norm_standardGaussian_marginal, hu, c]
    · intro hr
      have hr' : r = c := by simpa using hr
      subst r
      let u : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single 0 1
      refine ⟨u, ?_, ?_⟩
      · simp [u]
      · simp [psi2Norm_standardGaussian_marginal, u, c]
  rw [HDP.psi2NormVector, hset, csSup_singleton]

/-! ## Theorem 3.4.5: the uniform distribution on the sphere is subgaussian -/

noncomputable section

local instance : IsProbabilityMeasure projectiveProbability := by
  dsimp [projectiveProbability]
  infer_instance

/-- A coordinate of the projective Gaussian sphere model is subgaussian at the dimension-normalized scale.

**Lean implementation helper.** -/
lemma projectiveGaussianCoordinate_subGaussian (i : ℕ) :
    HDP.SubGaussian (projectiveGaussianCoordinate i) projectiveProbability := by
  refine ⟨Real.sqrt (8 / 3), by positivity, ?_⟩
  rw [HDP.psi2MGF_eq_of_hasLaw_standardGaussian
    (hasLaw_projectiveGaussianCoordinate i)]
  exact le_of_eq HDP.psi2MGF_id_standardGaussian_at_scale

/-- Each projective Gaussian coordinate has `psi2Norm` exactly `sqrt (8 / 3)`, as recorded by `psi2Norm_projectiveGaussianCoordinate`.

**Lean implementation helper.** -/
lemma psi2Norm_projectiveGaussianCoordinate (i : ℕ) :
    HDP.psi2Norm (projectiveGaussianCoordinate i) projectiveProbability =
      Real.sqrt (8 / 3) :=
  HDP.psi2Norm_standardGaussian (hasLaw_projectiveGaussianCoordinate i)

/-- Every projective Gaussian coordinate has second moment one (`integral_projectiveGaussianSquare`).

**Lean implementation helper.** -/
lemma integral_projectiveGaussianSquare (i : ℕ) :
    (∫ w, projectiveGaussianCoordinate i w ^ 2 ∂projectiveProbability) = 1 := by
  change (∫ w, projectiveGaussianSquare i w ∂projectiveProbability) = 1
  rw [(ident_projectiveGaussianSquare i).integral_eq,
    integral_projectiveGaussianSquare_zero]

/-- Shows that `sqrt_eight_thirds` is strictly smaller than `two`.

**Lean implementation helper.** -/
lemma sqrt_eight_thirds_lt_two : Real.sqrt (8 / 3) < 2 := by
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8 / 3)
  have hsnonneg := Real.sqrt_nonneg (8 / 3)
  nlinarith

/-- Standard-Gaussian norm concentrates around `sqrt(n)`.

**Book Equation (3.16).** -/
theorem projectiveGaussianNorm_concentration (n : ℕ) (hn : 0 < n) :
    HDP.SubGaussian
        (fun w => ‖projectiveGaussianVector n w‖ - Real.sqrt n)
        projectiveProbability ∧
      HDP.psi2Norm
        (fun w => ‖projectiveGaussianVector n w‖ - Real.sqrt n)
        projectiveProbability ≤ normConcentrationConstant * 2 ^ 2 := by
  have h := concentration_norm (μ := projectiveProbability) hn
    (X := fun i w => projectiveGaussianCoordinate i.val w)
    (fun i => (hasLaw_projectiveGaussianCoordinate i.val).aemeasurable)
    (fun i => projectiveGaussianCoordinate_subGaussian i.val)
    (fun i => integral_projectiveGaussianSquare i.val)
    (iIndep_projectiveGaussianCoordinate.precomp Fin.val_injective)
    (K := 2) (by norm_num)
    (fun i => by
      rw [psi2Norm_projectiveGaussianCoordinate]
      exact sqrt_eight_thirds_lt_two.le)
  have hfun :
      (fun w => Real.sqrt
          (∑ i : Fin n, projectiveGaussianCoordinate i.val w ^ 2) -
            Real.sqrt n) =
        fun w => ‖projectiveGaussianVector n w‖ - Real.sqrt n := by
    funext w
    congr 1
    rw [EuclideanSpace.norm_eq]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    simp [projectiveGaussianVector, projectiveGaussianCoordinate, sq_abs]
  rw [hfun] at h
  exact h

/-- Shows that `normConcentration_two` is strictly smaller than `256`.

**Lean implementation helper.** -/
lemma normConcentration_two_lt_256 :
    normConcentrationConstant * 2 ^ 2 < 256 := by
  have hs5 : Real.sqrt 5 < 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
  have hs8 : Real.sqrt 8 < 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8)]
  calc
    normConcentrationConstant * 2 ^ 2 =
        16 * Real.sqrt 5 * Real.sqrt 8 := by
      unfold normConcentrationConstant
      ring
    _ < 16 * 3 * Real.sqrt 8 := by gcongr
    _ < 16 * 3 * 3 := by gcongr
    _ < 256 := by norm_num

/-- Identifies `projectiveRatio` with `scaled_coordinate_div_norm`.

**Lean implementation helper.** -/
lemma projectiveRatio_eq_scaled_coordinate_div_norm (n : ℕ) (hn : 0 < n)
    (w : ProjectiveOmega) (hw : projectiveGaussianVector n w ≠ 0) :
    projectiveRatio n w = Real.sqrt n * projectiveGaussianCoordinate 0 w /
      ‖projectiveGaussianVector n w‖ := by
  have hnorm : ‖projectiveGaussianVector n w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have hsqrt : Real.sqrt (n : ℝ) ≠ 0 :=
    (Real.sqrt_pos.2 (by exact_mod_cast hn)).ne'
  rw [projectiveRatio, projectiveDenominator_eq_norm_div_sqrt n hn w]
  change projectiveGaussianCoordinate 0 w /
      (‖projectiveGaussianVector n w‖ / Real.sqrt n) = _
  field_simp

/-- `projectiveRatio_tail_subset` places the event `{t ≤ |projectiveRatio n|}` inside the union of a large-coordinate event and a large Gaussian-norm-deviation event.

**Lean implementation helper.** -/
lemma projectiveRatio_tail_subset (n : ℕ) (hn : 0 < n)
    {t : ℝ} (ht : 0 ≤ t) :
    {w | t ≤ |projectiveRatio n w|} ⊆
      {w | t / 2 ≤ |projectiveGaussianCoordinate 0 w|} ∪
      {w | Real.sqrt n / 2 ≤
        |‖projectiveGaussianVector n w‖ - Real.sqrt n|} := by
  intro w hw
  by_cases hb : t / 2 ≤ |projectiveGaussianCoordinate 0 w|
  · exact Set.mem_union_left _ hb
  · apply Set.mem_union_right
    by_contra hc
    have hc' : |‖projectiveGaussianVector n w‖ - Real.sqrt n| <
        Real.sqrt n / 2 := lt_of_not_ge hc
    have hsqrt : 0 < Real.sqrt (n : ℝ) :=
      Real.sqrt_pos.2 (by exact_mod_cast hn)
    have hRlower : Real.sqrt n / 2 < ‖projectiveGaussianVector n w‖ := by
      have hleft := neg_lt_of_abs_lt hc'
      linarith
    have hRpos : 0 < ‖projectiveGaussianVector n w‖ :=
      lt_of_lt_of_le (half_pos hsqrt) hRlower.le
    have hG : projectiveGaussianVector n w ≠ 0 := norm_ne_zero_iff.mp hRpos.ne'
    have htpos : 0 < t := by
      apply lt_of_le_of_ne ht
      intro ht0
      have htzero : t = 0 := ht0.symm
      apply hb
      rw [htzero]
      simpa only [zero_div] using
        (abs_nonneg (projectiveGaussianCoordinate 0 w))
    have hb' : |projectiveGaussianCoordinate 0 w| < t / 2 := lt_of_not_ge hb
    have hfacpos : 0 < Real.sqrt n / ‖projectiveGaussianVector n w‖ :=
      div_pos hsqrt hRpos
    have hfaclt : Real.sqrt n / ‖projectiveGaussianVector n w‖ < 2 := by
      rw [div_lt_iff₀ hRpos]
      linarith
    have habs : |projectiveRatio n w| < t := by
      rw [projectiveRatio_eq_scaled_coordinate_div_norm n hn w hG]
      have heq : |Real.sqrt n * projectiveGaussianCoordinate 0 w /
          ‖projectiveGaussianVector n w‖| =
          (Real.sqrt n / ‖projectiveGaussianVector n w‖) *
            |projectiveGaussianCoordinate 0 w| := by
        rw [abs_div, abs_mul, abs_of_pos hsqrt,
          abs_of_nonneg (norm_nonneg _)]
        field_simp [hRpos.ne']
      rw [heq]
      calc
        (Real.sqrt n / ‖projectiveGaussianVector n w‖) *
            |projectiveGaussianCoordinate 0 w|
            < (Real.sqrt n / ‖projectiveGaussianVector n w‖) * (t / 2) :=
          mul_lt_mul_of_pos_left hb' hfacpos
        _ < 2 * (t / 2) :=
          mul_lt_mul_of_pos_right hfaclt (half_pos htpos)
        _ = t := by ring
    exact (not_lt_of_ge hw) habs

/-- For `0 ≤ t ≤ sqrt n`, `projectiveRatio_tail_four` bounds the ratio tail by `4 * exp (-t² / 512²)`.

**Lean implementation helper.** -/
lemma projectiveRatio_tail_four (n : ℕ) (hn : 0 < n)
    {t : ℝ} (ht : 0 ≤ t) (htn : t ≤ Real.sqrt n) :
    projectiveProbability {w | t ≤ |projectiveRatio n w|} ≤
      ENNReal.ofReal (4 * Real.exp (-t ^ 2 / (512 : ℝ) ^ 2)) := by
  let B : Set ProjectiveOmega :=
    {w | t / 2 ≤ |projectiveGaussianCoordinate 0 w|}
  let C : Set ProjectiveOmega :=
    {w | Real.sqrt n / 2 ≤
      |‖projectiveGaussianVector n w‖ - Real.sqrt n|}
  have hcoordSub := projectiveGaussianCoordinate_subGaussian 0
  have hcoordMGF :
      HDP.psi2MGF (projectiveGaussianCoordinate 0) projectiveProbability 2 ≤ 2 :=
    HDP.psi2MGF_le_two_of_gt hcoordSub (by
      rw [psi2Norm_projectiveGaussianCoordinate]
      exact sqrt_eight_thirds_lt_two)
  have hcoordTail := HDP.subgaussian_iii_to_i
    (X := projectiveGaussianCoordinate 0) (K := 2) (t := t / 2)
    (hasLaw_projectiveGaussianCoordinate 0).aemeasurable
    (by norm_num : (0 : ℝ) < 2) hcoordMGF
    (div_nonneg ht (by norm_num : (0 : ℝ) ≤ 2))
  have hB : projectiveProbability B ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (512 : ℝ) ^ 2)) := by
    change projectiveProbability
      {w | t / 2 ≤ |projectiveGaussianCoordinate 0 w|} ≤ _
    refine hcoordTail.trans ?_
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
    norm_num
    nlinarith [sq_nonneg t]
  have hconc := projectiveGaussianNorm_concentration n hn
  have hdevMGF : HDP.psi2MGF
      (fun w => ‖projectiveGaussianVector n w‖ - Real.sqrt n)
      projectiveProbability 256 ≤ 2 :=
    HDP.psi2MGF_le_two_of_gt hconc.1
      (lt_of_le_of_lt hconc.2 normConcentration_two_lt_256)
  have hdevMeas : AEMeasurable
      (fun w => ‖projectiveGaussianVector n w‖ - Real.sqrt n)
      projectiveProbability :=
    ((measurable_projectiveGaussianVector n).norm.sub_const
      (Real.sqrt n)).aemeasurable
  have hdevTail := HDP.subgaussian_iii_to_i
    (X := fun w => ‖projectiveGaussianVector n w‖ - Real.sqrt n)
    (K := 256) (t := Real.sqrt n / 2) hdevMeas
    (by norm_num : (0 : ℝ) < 256) hdevMGF
    (div_nonneg (Real.sqrt_nonneg _) (by norm_num))
  have htsq : t ^ 2 ≤ (n : ℝ) := by
    have h := (sq_le_sq₀ ht (Real.sqrt_nonneg n)).2 htn
    rwa [Real.sq_sqrt (Nat.cast_nonneg n)] at h
  have hC : projectiveProbability C ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (512 : ℝ) ^ 2)) := by
    change projectiveProbability
      {w | Real.sqrt n / 2 ≤
        |‖projectiveGaussianVector n w‖ - Real.sqrt n|} ≤ _
    refine hdevTail.trans ?_
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    norm_num
    nlinarith
  calc
    projectiveProbability {w | t ≤ |projectiveRatio n w|}
        ≤ projectiveProbability (B ∪ C) :=
      measure_mono (projectiveRatio_tail_subset n hn ht)
    _ ≤ projectiveProbability B + projectiveProbability C := measure_union_le _ _
    _ ≤ ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (512 : ℝ) ^ 2)) +
        ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (512 : ℝ) ^ 2)) :=
      add_le_add hB hC
    _ = ENNReal.ofReal (4 * Real.exp (-t ^ 2 / (512 : ℝ) ^ 2)) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 2
      ring

/-- A deliberately generous absolute scale; its size keeps the proof fully
elementary while remaining dimension-free.

**Lean implementation helper.** -/
noncomputable def sphereProjectionTailScale : ℝ := 512 * Real.sqrt 2

/-- Shows that `sphereProjectionTailScale` is positive.

**Lean implementation helper.** -/
lemma sphereProjectionTailScale_pos : 0 < sphereProjectionTailScale := by
  unfold sphereProjectionTailScale
  positivity

/-- The identity `sphereProjectionTailScale_sq` states that the chosen `sphereProjectionTailScale` satisfies `sphereProjectionTailScale² = 2 * 512²`.

**Lean implementation helper.** -/
lemma sphereProjectionTailScale_sq :
    sphereProjectionTailScale ^ 2 = 2 * (512 : ℝ) ^ 2 := by
  unfold sphereProjectionTailScale
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/-- For `0 ≤ t ≤ sqrt n`, `projectiveRatio_tail_bound` bounds the ratio tail by `2 * exp (-t² / sphereProjectionTailScale²)`.

**Lean implementation helper.** -/
lemma projectiveRatio_tail_bound (n : ℕ) (hn : 0 < n)
    {t : ℝ} (ht : 0 ≤ t) (htn : t ≤ Real.sqrt n) :
    projectiveProbability {w | t ≤ |projectiveRatio n w|} ≤
      ENNReal.ofReal
        (2 * Real.exp (-t ^ 2 / sphereProjectionTailScale ^ 2)) := by
  by_cases hsmall : t ^ 2 ≤ 2 * (512 : ℝ) ^ 2 * Real.log 2
  · calc
      projectiveProbability {w | t ≤ |projectiveRatio n w|} ≤ 1 := prob_le_one
      _ ≤ ENNReal.ofReal
          (2 * Real.exp (-t ^ 2 / sphereProjectionTailScale ^ 2)) := by
        rw [← ENNReal.ofReal_one]
        apply ENNReal.ofReal_le_ofReal
        have hdiv : t ^ 2 / sphereProjectionTailScale ^ 2 ≤ Real.log 2 := by
          rw [sphereProjectionTailScale_sq]
          exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 2 * 512 ^ 2)).2
            (by nlinarith [hsmall])
        calc
          (1 : ℝ) = 2 * Real.exp (-Real.log 2) := by
            rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
            norm_num
          _ ≤ 2 * Real.exp (-t ^ 2 / sphereProjectionTailScale ^ 2) := by
            apply mul_le_mul_of_nonneg_left
              (Real.exp_le_exp.mpr (by
                calc
                  -Real.log 2 ≤ -(t ^ 2 / sphereProjectionTailScale ^ 2) :=
                    neg_le_neg hdiv
                  _ = -t ^ 2 / sphereProjectionTailScale ^ 2 := by ring))
              (by norm_num)
  · have hlarge : 2 * Real.log 2 < t ^ 2 / (512 : ℝ) ^ 2 := by
      rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < (512 : ℝ) ^ 2)]
      nlinarith [lt_of_not_ge hsmall]
    refine (projectiveRatio_tail_four n hn ht htn).trans ?_
    apply ENNReal.ofReal_le_ofReal
    have hexp :
        4 * Real.exp (-t ^ 2 / (512 : ℝ) ^ 2) ≤
          2 * Real.exp (-t ^ 2 / sphereProjectionTailScale ^ 2) := by
      calc
        4 * Real.exp (-t ^ 2 / (512 : ℝ) ^ 2) =
            Real.exp ((Real.log 2 + Real.log 2) +
              (-t ^ 2 / (512 : ℝ) ^ 2)) := by
          rw [Real.exp_add, Real.exp_add,
            Real.exp_log (by norm_num : (0 : ℝ) < 2)]
          ring
        _ ≤ Real.exp (Real.log 2 +
              (-t ^ 2 / sphereProjectionTailScale ^ 2)) := by
          apply Real.exp_le_exp.mpr
          rw [sphereProjectionTailScale_sq]
          nlinarith
        _ = 2 * Real.exp (-t ^ 2 / sphereProjectionTailScale ^ 2) := by
          rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact hexp

/-- Identifies `sphericalProjection_tail_measure` with `projective`.

**Lean implementation helper.** -/
lemma sphericalProjection_tail_measure_eq_projective (n : ℕ) (hn : 0 < n)
    (v : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) (t : ℝ) :
    (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)))
        {x | t ≤ |sphericalProjection n v x|} =
      projectiveProbability {w | t ≤ |projectiveRatio n w|} := by
  let σ := HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
  let A : Set ℝ := {y | t ≤ |y|}
  have hA : MeasurableSet A := by
    dsimp [A]
    exact measurableSet_le measurable_const measurable_abs
  have hmap : Measure.map (sphericalProjection n v) σ =
      Measure.map (projectiveRatio n) projectiveProbability :=
    (map_sphericalProjection_eq n v (firstUnitDirection n hn)).trans
      (map_sphericalProjection_first_eq_projectiveRatio n hn)
  calc
    σ {x | t ≤ |sphericalProjection n v x|} =
        (Measure.map (sphericalProjection n v) σ) A := by
      rw [Measure.map_apply (measurable_sphericalProjection n v) hA]
      rfl
    _ = (Measure.map (projectiveRatio n) projectiveProbability) A := by rw [hmap]
    _ = projectiveProbability {w | t ≤ |projectiveRatio n w|} := by
      rw [Measure.map_apply_of_aemeasurable
        (projectiveRatio_aemeasurable n) hA]
      rfl

/-- Dimension-free two-sided tail for the `√n`-scaled spherical marginal.

**Lean implementation helper.** -/
theorem sphericalProjection_tail (n : ℕ) (hn : 0 < n)
    (v : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
    {t : ℝ} (ht : 0 ≤ t) :
    (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)))
        {x | t ≤ |sphericalProjection n v x|} ≤
      ENNReal.ofReal
        (2 * Real.exp (-t ^ 2 / sphereProjectionTailScale ^ 2)) := by
  rw [sphericalProjection_tail_measure_eq_projective n hn v t]
  by_cases htn : t ≤ Real.sqrt n
  · exact projectiveRatio_tail_bound n hn ht htn
  · have hzero : projectiveProbability {w | t ≤ |projectiveRatio n w|} = 0 := by
      rw [← sphericalProjection_tail_measure_eq_projective n hn v t]
      have hempty : {x | t ≤ |sphericalProjection n v x|} = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro x hx
        exact (not_le_of_gt (lt_of_le_of_lt
          (abs_sphericalProjection_le_sqrt v x) (lt_of_not_ge htn))) hx
      rw [hempty]
      simp
    rw [hzero]
    positivity

/-- Every fixed directional projection of the uniform sphere distribution is subgaussian.

**Lean implementation helper.** -/
theorem sphericalProjection_subGaussian (n : ℕ) (hn : 0 < n)
    (v : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    HDP.SubGaussian (sphericalProjection n v)
        (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))) ∧
      HDP.psi2Norm (sphericalProjection n v)
        (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))) ≤
          Real.sqrt 5 * sphereProjectionTailScale := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact HDP.psi2Norm_le_of_tail_bound
    (measurable_sphericalProjection n v).aemeasurable
    sphereProjectionTailScale_pos
    (fun t ht => sphericalProjection_tail n hn v ht)

/-- The source-scale form for an unscaled unit-sphere marginal.

**Book Theorem 3.4.5.** -/
theorem unitSphere_marginal_tail (n : ℕ) (hn : 0 < n)
    (v : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
    {t : ℝ} (ht : 0 ≤ t) :
    (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)))
        {x | t ≤ |inner ℝ (x : EuclideanSpace ℝ (Fin n))
          (v : EuclideanSpace ℝ (Fin n))|} ≤
      ENNReal.ofReal
        (2 * Real.exp (-(n : ℝ) * t ^ 2 / sphereProjectionTailScale ^ 2)) := by
  have hsqrt : 0 < Real.sqrt (n : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hn)
  have h := sphericalProjection_tail n hn v
    (t := Real.sqrt n * t) (mul_nonneg hsqrt.le ht)
  convert h using 1
  · congr 1
    ext x
    simp only [Set.mem_setOf_eq, sphericalProjection, abs_mul,
      abs_of_pos hsqrt]
    constructor <;> intro h <;> nlinarith
  · congr 3
    rw [mul_pow, Real.sq_sqrt (by exact_mod_cast hn.le)]
    ring

/-- This source-facing one-sided
bound follows from the stronger two-sided estimate above.

**Book Theorem 3.4.5.** -/
theorem sphere_tail (n : ℕ) (hn : 0 < n)
    (v : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
    {t : ℝ} (ht : 0 ≤ t) :
    (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)))
        {x | t ≤ inner ℝ (x : EuclideanSpace ℝ (Fin n))
          (v : EuclideanSpace ℝ (Fin n))} ≤
      ENNReal.ofReal
        (2 * Real.exp (-(n : ℝ) * t ^ 2 / sphereProjectionTailScale ^ 2)) := by
  calc
    (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)))
        {x | t ≤ inner ℝ (x : EuclideanSpace ℝ (Fin n)) v}
        ≤ (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)))
          {x | t ≤ |inner ℝ (x : EuclideanSpace ℝ (Fin n)) v|} := by
      apply measure_mono
      intro x hx
      change t ≤ inner ℝ (x : EuclideanSpace ℝ (Fin n)) v at hx
      exact hx.trans (le_abs_self _)
    _ ≤ _ := unitSphere_marginal_tail n hn v ht

/-- The dimension-rescaled uniform unit-sphere vector is a subgaussian random vector.

**Lean implementation helper.** -/
theorem unitSphere_subGaussianVector (n : ℕ) (hn : 0 < n) :
    HDP.SubGaussianVector
      (HDP.uniformSphereVector (EuclideanSpace ℝ (Fin n)))
      (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  intro u
  have hmeas : AEMeasurable
      (fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
        inner ℝ (HDP.uniformSphereVector (EuclideanSpace ℝ (Fin n)) x) u)
      (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))) := by
    apply Measurable.aemeasurable
    change Measurable (fun x : Metric.sphere
      (0 : EuclideanSpace ℝ (Fin n)) 1 => inner ℝ (x : EuclideanSpace ℝ (Fin n)) u)
    fun_prop
  have hbound : ∀ᵐ x ∂HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)),
      |inner ℝ (HDP.uniformSphereVector (EuclideanSpace ℝ (Fin n)) x) u| ≤
        ‖u‖ + 1 := by
    filter_upwards [] with x
    have hx : ‖(x : EuclideanSpace ℝ (Fin n))‖ = 1 := by
      simpa only [mem_sphere_zero_iff_norm, sub_zero] using x.property
    change |inner ℝ (x : EuclideanSpace ℝ (Fin n)) u| ≤ ‖u‖ + 1
    calc
      |inner ℝ (x : EuclideanSpace ℝ (Fin n)) u|
          ≤ ‖(x : EuclideanSpace ℝ (Fin n))‖ * ‖u‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ ‖u‖ + 1 := by rw [hx, one_mul]; linarith
  exact (HDP.psi2Norm_le_of_bounded (X := fun x =>
    inner ℝ (HDP.uniformSphereVector (EuclideanSpace ℝ (Fin n)) x) u)
    (M := ‖u‖ + 1) (by positivity) hbound).1

/-- Sphere marginal tail `P(<X,v>>=t) <= 2 exp(-n t^2/2)` and hence the sphere is subgaussian at scale `1/sqrt(n)`.

**Book Theorem 3.4.5.** -/
theorem psi2NormVector_unitSphere_le (n : ℕ) (hn : 0 < n) :
    HDP.psi2NormVector
      (HDP.uniformSphereVector (EuclideanSpace ℝ (Fin n)))
      (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))) ≤
        Real.sqrt 5 * sphereProjectionTailScale / Real.sqrt n := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hsqrt : 0 < Real.sqrt (n : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hn)
  let σ := HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
  let B : ℝ := Real.sqrt 5 * sphereProjectionTailScale / Real.sqrt n
  have hpoint : ∀ u : EuclideanSpace ℝ (Fin n), ‖u‖ = 1 →
      HDP.psi2Norm
        (fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
          inner ℝ (HDP.uniformSphereVector (EuclideanSpace ℝ (Fin n)) x) u) σ ≤ B := by
    intro u hu
    let v : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
      ⟨u, by simpa only [mem_sphere_zero_iff_norm, sub_zero]⟩
    have hfun :
        (fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
          inner ℝ (HDP.uniformSphereVector (EuclideanSpace ℝ (Fin n)) x) u) =
        fun x => (Real.sqrt n)⁻¹ * sphericalProjection n v x := by
      funext x
      simp only [HDP.uniformSphereVector, sphericalProjection, v]
      field_simp [hsqrt.ne']
    rw [hfun, HDP.psi2Norm_const_mul]
    have hproj := (sphericalProjection_subGaussian n hn v).2
    calc
      |(Real.sqrt n)⁻¹| * HDP.psi2Norm (sphericalProjection n v) σ
          ≤ |(Real.sqrt n)⁻¹| *
              (Real.sqrt 5 * sphereProjectionTailScale) :=
        mul_le_mul_of_nonneg_left hproj (abs_nonneg _)
      _ = B := by
        rw [abs_inv, abs_of_pos hsqrt]
        dsimp [B]
        field_simp [hsqrt.ne']
  rw [HDP.psi2NormVector]
  apply csSup_le
  · let e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single ⟨0, hn⟩ 1
    exact ⟨HDP.psi2Norm
      (fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
        inner ℝ (HDP.uniformSphereVector (EuclideanSpace ℝ (Fin n)) x) e) σ,
      e, by simp [e], rfl⟩
  · intro r hr
    rcases hr with ⟨u, hu, rfl⟩
    exact hpoint u hu

/-- The vector statement uses the safe real supremum interface and
an explicit absolute constant.

**Book Theorem 3.4.5.** -/
theorem unitSphere_subGaussian (n : ℕ) (hn : 0 < n) :
    HDP.SubGaussianVector
        (HDP.uniformSphereVector (EuclideanSpace ℝ (Fin n)))
        (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))) ∧
      HDP.psi2NormVector
        (HDP.uniformSphereVector (EuclideanSpace ℝ (Fin n)))
        (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))) ≤
          Real.sqrt 5 * sphereProjectionTailScale / Real.sqrt n :=
  ⟨unitSphere_subGaussianVector n hn, psi2NormVector_unitSphere_le n hn⟩

end

end HDP.Chapter3

end Source_13_SubGaussianVectors

/-! ## Material formerly in `06_GaussianClouds.lean` -/

section Source_06_GaussianClouds

/-!
# Gaussian characterizations, invariant ensembles, and Gaussian clouds

This thematic core module contains the results originating in Exercises
3.15--3.20, 3.22--3.23, and the auxiliary ball/frame definitions needed by
the surrounding development. These results are used by Chapter 3 itself or
later chapters, so their source-numbered declarations live here and no core
module imports an exercise leaf.
-/

open MeasureTheory ProbabilityTheory InnerProductSpace Real Matrix WithLp Module
open scoped BigOperators ENNReal NNReal RealInnerProductSpace MatrixOrder

namespace HDP.Chapter3

noncomputable section

/-! ## Exercises 3.15--3.16: Gaussian density and characterization -/

/-- The standard
multivariate Gaussian is Lebesgue measure with the normalized radial density.
This is the exact measure identity underlying the change-of-variables proof.

**Book Equation (3.11).** -/
theorem exercise_3_15_standardDensity
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] :
    volume.withDensity (fun x : E ↦
        ((HDP.gaussianRadialDensity E x : ℝ≥0) : ℝ≥0∞)) =
      stdGaussian E := by
  exact HDP.gaussianRadialMeasure_eq_stdGaussian E

/-- For a positive-definite
covariance, the multivariate Gaussian is Lebesgue measure with the usual
determinant-normalized density, and that density has the source's explicit
inverse-covariance formula.

**Book Exercise 3.15.** -/
theorem exercise_3_15
    {n : Type*} [Fintype n] [DecidableEq n]
    (mu : EuclideanSpace ℝ n) (S : Matrix n n ℝ) (hS : S.PosDef) :
    multivariateGaussian mu S =
        volume.withDensity (multivariateGaussianDensity mu S hS) ∧
      ∀ x, multivariateGaussianDensity mu S hS x = ENNReal.ofReal
        ((Real.sqrt S.det)⁻¹ *
          (HDP.gaussianRadialNormalizer (EuclideanSpace ℝ n))⁻¹ *
          Real.exp (-(1 / 2 : ℝ) *
            ((x - mu) ⬝ᵥ S⁻¹ *ᵥ (x - mu)))) := by
  exact ⟨multivariateGaussian_eq_withDensity mu S hS,
    fun x ↦ multivariateGaussianDensity_eq_ofReal mu x S hS⟩

/-- A measure is Gaussian exactly when every
continuous one-dimensional linear marginal is Gaussian (the
Cramér--Wold characterization used by the book).

**Book Exercise 3.16.** -/
theorem exercise_3_16a
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] (ν : Measure E) :
    IsGaussian ν ↔ ∀ L : E →L[ℝ] ℝ, IsGaussian (ν.map L) := by
  constructor
  · intro h
    letI : IsGaussian ν := h
    intro L
    infer_instance
  · exact isGaussian_of_isGaussian_map

/-- A finite random vector is jointly Gaussian
exactly when all its fixed linear combinations are Gaussian. Continuous
linear forms on a finite-dimensional coordinate space are precisely those
linear combinations.

**Book Exercise 3.16.** -/
theorem exercise_3_16b
    {Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (X : Ω → E) (hX : AEMeasurable X P) :
    HasGaussianLaw X P ↔
      ∀ L : E →L[ℝ] ℝ, HasGaussianLaw (fun ω ↦ L (X ω)) P := by
  constructor
  · intro h L
    exact h.map_fun L
  · intro h
    refine ⟨?_⟩
    apply isGaussian_of_isGaussian_map
    intro L
    rw [AEMeasurable.map_map_of_aemeasurable
      L.measurable.aemeasurable hX]
    exact (h L).isGaussian_map

/- Exercise 3.17 is a pure witness/counterexample request (normal marginals,
zero covariance, but dependence).  It is intentionally recorded and skipped
under the constructive-witness policy; there is no deferred declaration. -/

/-! ## Exercises 3.18--3.21: invariant Gaussian matrix laws -/

/-- The coordinate-free Ginibre law is a standard
Gaussian on its Hilbert matrix space. Hence the two isometries induced by
left and right multiplication by fixed orthogonal matrices preserve its law.

**Book Exercise 3.18.** -/
theorem exercise_3_18
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (leftMul rightMul : E ≃ₗᵢ[ℝ] E) :
    Measure.map leftMul (stdGaussian E) = stdGaussian E ∧
      Measure.map rightMul (stdGaussian E) = stdGaussian E := by
  exact ⟨standardGaussian_rotation_invariant leftMul,
    standardGaussian_rotation_invariant rightMul⟩

/-- The Gaussian image measure used for the coordinate-free GOE
representation. For matrices, `S G = (G + Gᵀ)/√2`.

**Lean implementation helper.** -/
def gaussianSymmetrizedLaw
    (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F]
    (S : E →L[ℝ] F) : Measure F :=
  Measure.map S (stdGaussian E)

/-- GOE is the symmetrized image of a Ginibre
matrix. This theorem exposes the defining representation as a measure
identity, so subsequent results do not depend on matrix entries.

**Book Exercise 3.19.** -/
theorem exercise_3_19a
    (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F]
    (S : E →L[ℝ] F) :
    gaussianSymmetrizedLaw E F S = Measure.map S (stdGaussian E) := rfl

/-- Orthogonal conjugation preserves the GOE
law. The commuting square is the coordinate-free identity
`U (G+Gᵀ) Uᵀ = UG Uᵀ + (UG Uᵀ)ᵀ`.

**Book Exercise 3.19.** -/
theorem exercise_3_19b
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (S : E →L[ℝ] F) (conjugate : F ≃ₗᵢ[ℝ] F)
    (ginibreConjugate : E ≃ₗᵢ[ℝ] E)
    (hcomm : ∀ x, conjugate (S x) = S (ginibreConjugate x)) :
    Measure.map conjugate (gaussianSymmetrizedLaw E F S) =
      gaussianSymmetrizedLaw E F S := by
  unfold gaussianSymmetrizedLaw
  calc
    Measure.map conjugate (Measure.map S (stdGaussian E)) =
        Measure.map (fun x ↦ conjugate (S x)) (stdGaussian E) := by
          rw [Measure.map_map]
          · rfl
          · fun_prop
          · fun_prop
    _ = Measure.map (fun x ↦ S (ginibreConjugate x)) (stdGaussian E) := by
      congr 1
      funext x
      exact hcomm x
    _ = Measure.map S (Measure.map ginibreConjugate (stdGaussian E)) := by
      rw [Measure.map_map]
      · rfl
      · fun_prop
      · fun_prop
    _ = Measure.map S (stdGaussian E) := by
      rw [standardGaussian_rotation_invariant ginibreConjugate]

/-- After extending two fixed orthogonal unit vectors
to an orthonormal basis, `(Gu,Gv)` has the canonical product law below.
Consequently its components are independent standard Gaussian vectors.

**Book Exercise 3.20.** -/
theorem exercise_3_20
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F] :
    (Prod.fst : F × F → F) ⟂ᵢ[(stdGaussian F).prod (stdGaussian F)] Prod.snd ∧
      HasLaw (Prod.fst : F × F → F) (stdGaussian F)
        ((stdGaussian F).prod (stdGaussian F)) ∧
      HasLaw (Prod.snd : F × F → F) (stdGaussian F)
        ((stdGaussian F).prod (stdGaussian F)) := by
  refine ⟨indepFun_prod (X := id) (Y := id) measurable_id measurable_id, ?_, ?_⟩
  · simpa only [id_eq] using
      (measurePreserving_fst (μ := stdGaussian F) (ν := stdGaussian F)).hasLaw
  · simpa only [id_eq] using
      (measurePreserving_snd (μ := stdGaussian F) (ν := stdGaussian F)).hasLaw

/-! ## Exercise 3.23: separation and convex position -/

/-- A finite indexed family is in convex position when no member lies in the
convex hull of all the other indexed members.

**Lean implementation helper.** -/
def PointsInConvexPosition
    {ι E : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E]
    (g : ι → E) : Prop :=
  ∀ i, g i ∉ convexHull ℝ (g '' {j | j ≠ i})

/-- Strict linear
separation of every point from all the others implies convex position.

**Book Exercise 3.23.** -/
theorem exercise_3_23
    {ι E : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E]
    (g : ι → E)
    (hsep : ∀ i, ∃ L : E →ₗ[ℝ] ℝ, ∀ j, j ≠ i → L (g j) < L (g i)) :
    PointsInConvexPosition g := by
  intro i
  obtain ⟨L, hL⟩ := hsep i
  have hsubset : g '' {j | j ≠ i} ⊆ {x | L x < L (g i)} := by
    rintro x ⟨j, hj, rfl⟩
    exact hL j hj
  have hhull : convexHull ℝ (g '' {j | j ≠ i}) ⊆
      {x | L x < L (g i)} :=
    convexHull_min hsubset (convex_halfSpace_lt L.isLinear (L (g i)))
  intro hi
  exact (lt_irrefl (L (g i))) (hhull hi)

/-- This is the probability
step used after proving the Gaussian separation estimate for one point.

**Book Exercise 3.23.** -/
theorem exercise_3_23_unionBound
    {Ω ι : Type*} {mΩ : MeasurableSpace Ω} [Fintype ι]
    (P : Measure Ω) (bad : ι → Set Ω) :
    P (⋃ i, bad i) ≤ ∑ i, P (bad i) := by
  exact measure_iUnion_fintype_le P bad

/-! ### The actual i.i.d. Gaussian cloud -/

/-- The canonical probability space carrying `N` independent standard
Gaussian points in `ℝⁿ`. -/
abbrev GaussianCloud (N n : ℕ) :=
  Fin N → EuclideanSpace ℝ (Fin n)

/-- Defines `gaussianCloudMeasure`, the gaussian cloud measure used in the surrounding construction.

**Lean implementation helper.** -/
def gaussianCloudMeasure (N n : ℕ) : Measure (GaussianCloud N n) :=
  Measure.pi (fun _ : Fin N ↦ stdGaussian (EuclideanSpace ℝ (Fin n)))

instance (N n : ℕ) : IsProbabilityMeasure (gaussianCloudMeasure N n) := by
  unfold gaussianCloudMeasure
  infer_instance

/-- Evaluating the Gaussian-cloud process at a fixed index has the standard Gaussian vector law.

**Lean implementation helper.** -/
lemma hasLaw_gaussianCloud_eval (N n : ℕ) (i : Fin N) :
    HasLaw (fun g : GaussianCloud N n ↦ g i)
      (stdGaussian (EuclideanSpace ℝ (Fin n)))
      (gaussianCloudMeasure N n) := by
  exact (measurePreserving_eval
    (fun _ : Fin N ↦ stdGaussian (EuclideanSpace ℝ (Fin n))) i).hasLaw

/-- The point-evaluation maps of the canonical Gaussian cloud are mutually independent (`iIndepFun_gaussianCloud_eval`).

**Lean implementation helper.** -/
lemma iIndepFun_gaussianCloud_eval (N n : ℕ) :
    iIndepFun (fun i (g : GaussianCloud N n) ↦ g i)
      (gaussianCloudMeasure N n) := by
  unfold gaussianCloudMeasure
  simpa only [id_eq] using
    (iIndepFun_pi (X := fun _ : Fin N ↦ id)
      (fun _ ↦ aemeasurable_id))

/-- A reusable explicit norm-deviation bound for the standard Gaussian.
The deliberately large constant is inherited from the proved Chapter 3 norm
concentration theorem.

**Book Equation (3.16).** -/
theorem stdGaussian_norm_deviation_tail (n : ℕ) (hn : 0 < n)
    {t : ℝ} (ht : 0 ≤ t) :
    (stdGaussian (EuclideanSpace ℝ (Fin n)))
        {x | t ≤ |‖x‖ - Real.sqrt n|} ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (256 : ℝ) ^ 2)) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  letI : IsProbabilityMeasure projectiveProbability := by
    dsimp [projectiveProbability]
    infer_instance
  have hconc := projectiveGaussianNorm_concentration n hn
  have hmgf : HDP.psi2MGF
      (fun w ↦ ‖projectiveGaussianVector n w‖ - Real.sqrt n)
      projectiveProbability 256 ≤ 2 :=
    HDP.psi2MGF_le_two_of_gt hconc.1
      (lt_of_le_of_lt hconc.2 normConcentration_two_lt_256)
  have hmeas : AEMeasurable
      (fun w ↦ ‖projectiveGaussianVector n w‖ - Real.sqrt n)
      projectiveProbability :=
    ((measurable_projectiveGaussianVector n).norm.sub_const
      (Real.sqrt n)).aemeasurable
  have htail := HDP.subgaussian_iii_to_i
    (X := fun w ↦ ‖projectiveGaussianVector n w‖ - Real.sqrt n)
    (K := 256) (t := t) hmeas (by norm_num) hmgf ht
  have hset : MeasurableSet
      {x : EuclideanSpace ℝ (Fin n) | t ≤ |‖x‖ - Real.sqrt n|} := by
    exact measurableSet_le measurable_const
      ((measurable_norm.sub_const (Real.sqrt n)).abs)
  rw [← (hasLaw_projectiveGaussianVector n).measure_eq hset]
  exact htail

/-- Safe normalized direction of the `i`-th point in the canonical Gaussian
cloud.

**Lean implementation helper.** -/
def gaussianCloudDirection (N n : ℕ) (hn : 0 < n) (i : Fin N) :
    GaussianCloud N n →
      Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact fun g ↦ HDP.gaussianDirection (g i)

/-- The normalized direction `gaussianCloudDirection` of each Gaussian-cloud point is measurable.

**Lean implementation helper.** -/
lemma measurable_gaussianCloudDirection (N n : ℕ) (hn : 0 < n)
    (i : Fin N) : Measurable (gaussianCloudDirection N n hn i) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  change Measurable (fun g : GaussianCloud N n ↦
    HDP.gaussianDirection (g i))
  exact (HDP.measurable_gaussianDirection
    (E := EuclideanSpace ℝ (Fin n))).comp (measurable_pi_apply i)

/-- Normalizing each Gaussian-cloud point pushes its law to independent uniform sphere directions.

**Lean implementation helper.** -/
lemma map_gaussianCloudDirection (N n : ℕ) (hn : 0 < n)
    (i : Fin N) :
    Measure.map (gaussianCloudDirection N n hn i)
        (gaussianCloudMeasure N n) =
      HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  change Measure.map
      (fun g : GaussianCloud N n ↦ HDP.gaussianDirection (g i))
      (gaussianCloudMeasure N n) = _
  rw [show (fun g : GaussianCloud N n ↦ HDP.gaussianDirection (g i)) =
      HDP.gaussianDirection ∘ Function.eval i by rfl]
  rw [← Measure.map_map
      (HDP.measurable_gaussianDirection
        (E := EuclideanSpace ℝ (Fin n))) (measurable_pi_apply i)]
  rw [(hasLaw_gaussianCloud_eval N n i).map_eq,
    HDP.map_gaussianDirection_stdGaussian]

/-- A pair of distinct Gaussian directions is unlikely to have correlation
at least `1/4`.

**Lean implementation helper.** -/
theorem gaussianCloud_angle_bad_le (N n : ℕ) (hn : 0 < n)
    (i j : Fin N) (hij : i ≠ j) :
    (gaussianCloudMeasure N n)
        {g | (1 / 4 : ℝ) ≤
          |inner ℝ
            ((gaussianCloudDirection N n hn i g :
              Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
                EuclideanSpace ℝ (Fin n))
            ((gaussianCloudDirection N n hn j g :
              Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
                EuclideanSpace ℝ (Fin n))|} ≤
      ENNReal.ofReal (2 * Real.exp
        (-(n : ℝ) * (1 / 4 : ℝ) ^ 2 /
          sphereProjectionTailScale ^ 2)) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let E := EuclideanSpace ℝ (Fin n)
  let S := Metric.sphere (0 : E) 1
  let σ := HDP.unitSphereMeasure E
  let D := gaussianCloudDirection N n hn
  let B : Set (S × S) :=
    {p | (1 / 4 : ℝ) ≤ |inner ℝ (p.1 : E) (p.2 : E)|}
  have hB : MeasurableSet B := by
    dsimp [B, S, E]
    exact measurableSet_le measurable_const
      ((by fun_prop : Measurable
        (fun p : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ×
            Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ↦
          inner ℝ (p.1 : EuclideanSpace ℝ (Fin n))
            (p.2 : EuclideanSpace ℝ (Fin n)))).abs)
  have heval := (iIndepFun_gaussianCloud_eval N n).indepFun hij
  have hdir := heval.comp
    (HDP.measurable_gaussianDirection
      (E := EuclideanSpace ℝ (Fin n)))
    (HDP.measurable_gaussianDirection
      (E := EuclideanSpace ℝ (Fin n)))
  have hpair := hdir.map_prod_eq_prod_map_map
      (measurable_gaussianCloudDirection N n hn i).aemeasurable
      (measurable_gaussianCloudDirection N n hn j).aemeasurable
  rw [map_gaussianCloudDirection N n hn i,
    map_gaussianCloudDirection N n hn j] at hpair
  have hfiber : ∀ x : S,
      σ (Prod.mk x ⁻¹' B) ≤
        ENNReal.ofReal (2 * Real.exp
          (-(n : ℝ) * (1 / 4 : ℝ) ^ 2 /
            sphereProjectionTailScale ^ 2)) := by
    intro x
    have h := unitSphere_marginal_tail n hn x
      (t := (1 / 4 : ℝ)) (by norm_num)
    change (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)))
      {y | (1 / 4 : ℝ) ≤
        |inner ℝ (x : EuclideanSpace ℝ (Fin n))
          (y : EuclideanSpace ℝ (Fin n))|} ≤ _
    simpa only [real_inner_comm] using h
  calc
    (gaussianCloudMeasure N n)
        {g | (1 / 4 : ℝ) ≤
          |inner ℝ (D i g : E) (D j g : E)|} =
        Measure.map (fun g ↦ (D i g, D j g))
          (gaussianCloudMeasure N n) B := by
            rw [Measure.map_apply]
            · rfl
            · exact (measurable_gaussianCloudDirection N n hn i).prodMk
                (measurable_gaussianCloudDirection N n hn j)
            · exact hB
    _ = σ.prod σ B := by rw [hpair]
    _ = ∫⁻ x, σ (Prod.mk x ⁻¹' B) ∂σ := Measure.prod_apply hB
    _ ≤ ∫⁻ _x : S,
        ENNReal.ofReal (2 * Real.exp
          (-(n : ℝ) * (1 / 4 : ℝ) ^ 2 /
            sphereProjectionTailScale ^ 2)) ∂σ := by
      exact lintegral_mono hfiber
    _ = ENNReal.ofReal (2 * Real.exp
          (-(n : ℝ) * (1 / 4 : ℝ) ^ 2 /
            sphereProjectionTailScale ^ 2)) := by
      rw [lintegral_const, measure_univ, mul_one]

/-- Radius failure event in the Gaussian cloud.

**Lean implementation helper.** -/
def gaussianCloudRadiusBad (N n : ℕ) (i : Fin N) : Set (GaussianCloud N n) :=
  {g | Real.sqrt n / 2 ≤ |‖g i‖ - Real.sqrt n|}

/-- Pairwise angular failure event. The diagonal is set to the empty event,
so finite unions can run over all ordered pairs.

**Lean implementation helper.** -/
def gaussianCloudAngleBad (N n : ℕ) (hn : 0 < n)
    (i j : Fin N) : Set (GaussianCloud N n) :=
  if i = j then ∅ else
    {g | (1 / 4 : ℝ) ≤
      |inner ℝ
        ((gaussianCloudDirection N n hn i g :
          Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
            EuclideanSpace ℝ (Fin n))
        ((gaussianCloudDirection N n hn j g :
          Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
            EuclideanSpace ℝ (Fin n))|}

/-- Defines `gaussianCloudBad`, the gaussian cloud bad used in the surrounding construction.

**Lean implementation helper.** -/
def gaussianCloudBad (N n : ℕ) (hn : 0 < n) : Set (GaussianCloud N n) :=
  (⋃ i, gaussianCloudRadiusBad N n i) ∪
    (⋃ i, ⋃ j, gaussianCloudAngleBad N n hn i j)

/-- The event that some Gaussian-cloud point has an atypical radius is measurable.

**Lean implementation helper.** -/
lemma measurableSet_gaussianCloudRadiusBad (N n : ℕ) (i : Fin N) :
    MeasurableSet (gaussianCloudRadiusBad N n i) := by
  unfold gaussianCloudRadiusBad
  exact measurableSet_le measurable_const
    (((measurable_pi_apply i).norm.sub_const (Real.sqrt n)).abs)

/-- The event that some pair of Gaussian-cloud directions has excessive correlation is measurable.

**Lean implementation helper.** -/
lemma measurableSet_gaussianCloudAngleBad (N n : ℕ) (hn : 0 < n)
    (i j : Fin N) : MeasurableSet (gaussianCloudAngleBad N n hn i j) := by
  unfold gaussianCloudAngleBad
  split_ifs
  · exact MeasurableSet.empty
  · exact measurableSet_le measurable_const
      ((by
        have hi := measurable_gaussianCloudDirection N n hn i
        have hj := measurable_gaussianCloudDirection N n hn j
        fun_prop : Measurable (fun g : GaussianCloud N n ↦
          inner ℝ
            ((gaussianCloudDirection N n hn i g :
              Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
                EuclideanSpace ℝ (Fin n))
            ((gaussianCloudDirection N n hn j g :
              Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
                EuclideanSpace ℝ (Fin n)))).abs)

/-- The union of the bad-radius and bad-angle Gaussian-cloud events is measurable.

**Lean implementation helper.** -/
lemma measurableSet_gaussianCloudBad (N n : ℕ) (hn : 0 < n) :
    MeasurableSet (gaussianCloudBad N n hn) := by
  apply MeasurableSet.union
  · exact MeasurableSet.iUnion (fun i ↦
      measurableSet_gaussianCloudRadiusBad N n i)
  · exact MeasurableSet.iUnion (fun i ↦ MeasurableSet.iUnion (fun j ↦
      measurableSet_gaussianCloudAngleBad N n hn i j))

/-- The bad-radius probability for a Gaussian cloud is bounded by the union of the individual radial tails.

**Lean implementation helper.** -/
lemma gaussianCloud_radius_bad_le (N n : ℕ) (hn : 0 < n) (i : Fin N) :
    (gaussianCloudMeasure N n) (gaussianCloudRadiusBad N n i) ≤
      ENNReal.ofReal (2 * Real.exp
        (-(Real.sqrt n / 2) ^ 2 / (256 : ℝ) ^ 2)) := by
  have hset : MeasurableSet
      {x : EuclideanSpace ℝ (Fin n) |
        Real.sqrt n / 2 ≤ |‖x‖ - Real.sqrt n|} := by
    exact measurableSet_le measurable_const
      ((measurable_norm.sub_const (Real.sqrt n)).abs)
  change (gaussianCloudMeasure N n)
      {g | Real.sqrt n / 2 ≤ |‖g i‖ - Real.sqrt n|} ≤ _
  rw [(hasLaw_gaussianCloud_eval N n i).measure_eq hset]
  exact stdGaussian_norm_deviation_tail n hn
    (div_nonneg (Real.sqrt_nonneg _) (by norm_num))

/-- Bounds `gaussianCloud_angle_bad` above by `all`.

**Lean implementation helper.** -/
lemma gaussianCloud_angle_bad_le_all (N n : ℕ) (hn : 0 < n)
    (i j : Fin N) :
    (gaussianCloudMeasure N n) (gaussianCloudAngleBad N n hn i j) ≤
      ENNReal.ofReal (2 * Real.exp
        (-(n : ℝ) * (1 / 4 : ℝ) ^ 2 /
          sphereProjectionTailScale ^ 2)) := by
  by_cases hij : i = j
  · simp [gaussianCloudAngleBad, hij]
  · simpa [gaussianCloudAngleBad, hij] using
      gaussianCloud_angle_bad_le N n hn i j hij

/-- Union-bound estimate for every radius and pairwise-angle failure in an
i.i.d. Gaussian cloud.

**Lean implementation helper.** -/
theorem gaussianCloud_bad_probability (N n : ℕ) (hn : 0 < n) :
    (gaussianCloudMeasure N n) (gaussianCloudBad N n hn) ≤
      (∑ _i : Fin N, ENNReal.ofReal (2 * Real.exp
        (-(Real.sqrt n / 2) ^ 2 / (256 : ℝ) ^ 2))) +
      ∑ _i : Fin N, ∑ _j : Fin N, ENNReal.ofReal (2 * Real.exp
        (-(n : ℝ) * (1 / 4 : ℝ) ^ 2 /
          sphereProjectionTailScale ^ 2)) := by
  unfold gaussianCloudBad
  calc
    (gaussianCloudMeasure N n)
        ((⋃ i, gaussianCloudRadiusBad N n i) ∪
          (⋃ i, ⋃ j, gaussianCloudAngleBad N n hn i j)) ≤
        (gaussianCloudMeasure N n) (⋃ i, gaussianCloudRadiusBad N n i) +
          (gaussianCloudMeasure N n)
            (⋃ i, ⋃ j, gaussianCloudAngleBad N n hn i j) :=
      measure_union_le _ _
    _ ≤ (∑ i, (gaussianCloudMeasure N n)
          (gaussianCloudRadiusBad N n i)) +
        ∑ i, ∑ j, (gaussianCloudMeasure N n)
          (gaussianCloudAngleBad N n hn i j) := by
      gcongr
      · exact measure_iUnion_fintype_le _ _
      · refine (measure_iUnion_fintype_le _ _).trans ?_
        gcongr with i
        exact measure_iUnion_fintype_le _ _
    _ ≤ _ := by
      apply add_le_add
      · apply Finset.sum_le_sum
        intro i hi
        exact gaussianCloud_radius_bad_le N n hn i
      · apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact gaussianCloud_angle_bad_le_all N n hn i j

/-- For nonzero `x`, multiplying its unit `gaussianDirection` by `‖x‖` recovers `x`, as stated by `norm_smul_gaussianDirection`.

**Lean implementation helper.** -/
lemma norm_smul_gaussianDirection
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [Nontrivial E] (x : E) (hx : x ≠ 0) :
    ‖x‖ • ((HDP.gaussianDirection x : Metric.sphere (0 : E) 1) : E) = x := by
  rw [HDP.Chapter3.coe_gaussianDirection_eq_inv_norm_smul x hx]
  rw [smul_smul]
  simp [norm_ne_zero_iff.mpr hx]

/-- The inner product of a normalized Gaussian direction with itself is one.

**Lean implementation helper.** -/
lemma inner_gaussianDirection_self
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [Nontrivial E] (x : E) (hx : x ≠ 0) :
    inner ℝ
      (((HDP.gaussianDirection x : Metric.sphere (0 : E) 1) : E)) x = ‖x‖ := by
  let d := HDP.gaussianDirection x
  have hrec := norm_smul_gaussianDirection x hx
  have hd : ‖(d : E)‖ = 1 := by
    simpa only [mem_sphere_zero_iff_norm, sub_zero] using d.property
  calc
    inner ℝ (d : E) x = inner ℝ (d : E) (‖x‖ • (d : E)) := by rw [hrec]
    _ = ‖x‖ * inner ℝ (d : E) (d : E) := by
      rw [inner_smul_right]
    _ = ‖x‖ := by rw [real_inner_self_eq_norm_sq, hd]; ring

/-- Outside the explicit union of radius and angular failures, every cloud
point is strictly separated from all the others by its own Gaussian
direction.

**Lean implementation helper.** -/
theorem gaussianCloud_good_implies_convexPosition (N n : ℕ) (hn : 0 < n)
    {g : GaussianCloud N n} (hg : g ∉ gaussianCloudBad N n hn) :
    PointsInConvexPosition g := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hsqrt : 0 < Real.sqrt (n : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hradius : ∀ i : Fin N,
      Real.sqrt n / 2 < ‖g i‖ ∧ ‖g i‖ < 3 * Real.sqrt n / 2 := by
    intro i
    have hnot : g ∉ gaussianCloudRadiusBad N n i := by
      intro hi
      apply hg
      exact Or.inl (Set.mem_iUnion.2 ⟨i, hi⟩)
    have habs : |‖g i‖ - Real.sqrt n| < Real.sqrt n / 2 := by
      exact lt_of_not_ge hnot
    constructor
    · have hleft := neg_lt_of_abs_lt habs
      linarith
    · have hright := lt_of_abs_lt habs
      linarith
  have hangle : ∀ i j : Fin N, i ≠ j →
      |inner ℝ
        ((gaussianCloudDirection N n hn i g :
          Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
            EuclideanSpace ℝ (Fin n))
        ((gaussianCloudDirection N n hn j g :
          Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
            EuclideanSpace ℝ (Fin n))| < (1 / 4 : ℝ) := by
    intro i j hij
    have hnot : g ∉ gaussianCloudAngleBad N n hn i j := by
      intro hbad
      apply hg
      exact Or.inr (Set.mem_iUnion.2 ⟨i,
        Set.mem_iUnion.2 ⟨j, hbad⟩⟩)
    rw [gaussianCloudAngleBad, if_neg hij] at hnot
    exact lt_of_not_ge hnot
  apply exercise_3_23 g
  intro i
  let d : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
    gaussianCloudDirection N n hn i g
  refine ⟨((innerSL ℝ) (d : EuclideanSpace ℝ (Fin n))).toLinearMap, ?_⟩
  intro j hij
  have hi0 : g i ≠ 0 := by
    exact norm_ne_zero_iff.mp
      (ne_of_gt ((half_pos hsqrt).trans (hradius i).1))
  have hj0 : g j ≠ 0 := by
    exact norm_ne_zero_iff.mp
      (ne_of_gt ((half_pos hsqrt).trans (hradius j).1))
  let e : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
    gaussianCloudDirection N n hn j g
  have hrecj : ‖g j‖ • (e : EuclideanSpace ℝ (Fin n)) = g j := by
    simpa [e, gaussianCloudDirection] using
      norm_smul_gaussianDirection (g j) hj0
  have hcrossAbs :
      |inner ℝ (d : EuclideanSpace ℝ (Fin n)) (g j)| =
        ‖g j‖ * |inner ℝ (d : EuclideanSpace ℝ (Fin n))
          (e : EuclideanSpace ℝ (Fin n))| := by
    calc
      |inner ℝ (d : EuclideanSpace ℝ (Fin n)) (g j)| =
          |inner ℝ (d : EuclideanSpace ℝ (Fin n))
            (‖g j‖ • (e : EuclideanSpace ℝ (Fin n)))| := by rw [hrecj]
      _ = _ := by
        rw [inner_smul_right, abs_mul, abs_of_nonneg (norm_nonneg _)]
  have hcross :
      inner ℝ (d : EuclideanSpace ℝ (Fin n)) (g j) <
        Real.sqrt n / 2 := by
    calc
      inner ℝ (d : EuclideanSpace ℝ (Fin n)) (g j)
          ≤ |inner ℝ (d : EuclideanSpace ℝ (Fin n)) (g j)| :=
        le_abs_self _
      _ = ‖g j‖ * |inner ℝ (d : EuclideanSpace ℝ (Fin n))
          (e : EuclideanSpace ℝ (Fin n))| := hcrossAbs
      _ < ‖g j‖ * (1 / 4 : ℝ) :=
        mul_lt_mul_of_pos_left (hangle i j (Ne.symm hij))
          (norm_pos_iff.mpr hj0)
      _ ≤ (3 * Real.sqrt n / 2) * (1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_right (le_of_lt (hradius j).2) (by positivity)
      _ < Real.sqrt n / 2 := by nlinarith
  have hself : Real.sqrt n / 2 <
      inner ℝ (d : EuclideanSpace ℝ (Fin n)) (g i) := by
    have hselfEq : inner ℝ (d : EuclideanSpace ℝ (Fin n)) (g i) =
        ‖g i‖ := by
      simpa [d, gaussianCloudDirection] using
        inner_gaussianDirection_self (g i) hi0
    rw [hselfEq]
    exact (hradius i).1
  exact hcross.trans hself

/-- **Exercise 3.23 (quantitative Gaussian form).** The probability that an
`N`-point standard Gaussian cloud fails to be in convex position is bounded
by the explicit radius-and-angle union bound below. In particular, this is a
genuine probability statement about the product Gaussian law, rather than
only the deterministic separating-hyperplane implication.

**Book Exercise 3.23.** -/
def gaussianCloudFailureBound (N n : ℕ) : ℝ≥0∞ :=
  (∑ _i : Fin N, ENNReal.ofReal (2 * Real.exp
    (-(Real.sqrt n / 2) ^ 2 / (256 : ℝ) ^ 2))) +
  ∑ _i : Fin N, ∑ _j : Fin N, ENNReal.ofReal (2 * Real.exp
    (-(n : ℝ) * (1 / 4 : ℝ) ^ 2 /
      sphereProjectionTailScale ^ 2))

/-- Random Gaussian points are in convex position with quantitative/exponential probability.

**Book Exercise 3.23.** -/
theorem exercise_3_23_gaussian_quantitative (N n : ℕ) (hn : 0 < n) :
    1 - gaussianCloudFailureBound N n ≤
      (gaussianCloudMeasure N n) {g | PointsInConvexPosition g} := by
  let B := gaussianCloudBad N n hn
  have hB : MeasurableSet B := measurableSet_gaussianCloudBad N n hn
  have hbound := gaussianCloud_bad_probability N n hn
  have hgood : Bᶜ ⊆ {g | PointsInConvexPosition g} := by
    intro g hg
    exact gaussianCloud_good_implies_convexPosition N n hn hg
  calc
    1 - gaussianCloudFailureBound N n ≤
        1 - (gaussianCloudMeasure N n) B := by
      exact tsub_le_tsub_left hbound 1
    _ = (gaussianCloudMeasure N n) Bᶜ := by
      rw [measure_compl hB (by finiteness), measure_univ]
    _ ≤ (gaussianCloudMeasure N n) {g | PointsInConvexPosition g} :=
      measure_mono hgood

/-- The radial tail exponent for the Gaussian cloud simplifies to the displayed dimension-dependent form.

**Lean implementation helper.** -/
private lemma gaussianCloud_radius_exponent (n : ℕ) :
    -(Real.sqrt n / 2) ^ 2 / (256 : ℝ) ^ 2 =
      -(n : ℝ) / (4 * (256 : ℝ) ^ 2) := by
  rw [div_pow, Real.sq_sqrt (by positivity)]
  ring

/-- The angular tail exponent for Gaussian-cloud pairs simplifies to the displayed dimension-dependent form.

**Lean implementation helper.** -/
private lemma gaussianCloud_angle_exponent (n : ℕ) :
    -(n : ℝ) * (1 / 4 : ℝ) ^ 2 / sphereProjectionTailScale ^ 2 =
      -(n : ℝ) / (32 * (512 : ℝ) ^ 2) := by
  rw [sphereProjectionTailScale_sq]
  ring

/-- Identifies `gaussianCloudFailureBound` with `ofReal`.

**Lean implementation helper.** -/
lemma gaussianCloudFailureBound_eq_ofReal (N n : ℕ) :
    gaussianCloudFailureBound N n = ENNReal.ofReal
      (2 * N * Real.exp (-(n : ℝ) / (4 * (256 : ℝ) ^ 2)) +
       2 * N ^ 2 * Real.exp (-(n : ℝ) / (32 * (512 : ℝ) ^ 2))) := by
  rw [gaussianCloudFailureBound]
  simp only [gaussianCloud_radius_exponent, gaussianCloud_angle_exponent,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp_rw [← ENNReal.ofReal_natCast]
  repeat rw [← ENNReal.ofReal_mul (by positivity)]
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  norm_num
  ring

/-- One explicit absolute rate that witnesses the source's exponential
regime in Exercise 3.23. The deliberately conservative value comes from the
constants in the Chapter 2 concentration bounds used above.

**Book Exercise 3.23.** -/
def gaussianConvexPositionRate : ℝ := 1 / (160 * (512 : ℝ) ^ 2)

/-- Shows that `gaussianConvexPositionRate` is positive.

**Lean implementation helper.** -/
lemma gaussianConvexPositionRate_pos : 0 < gaussianConvexPositionRate := by
  norm_num [gaussianConvexPositionRate]

/-- Bounds `gaussianConvexPositionRate` above by `radius`.

**Lean implementation helper.** -/
private lemma gaussianConvexPositionRate_le_radius :
    gaussianConvexPositionRate ≤
      (1 / (4 * (256 : ℝ) ^ 2)) / 4 := by
  norm_num [gaussianConvexPositionRate]

/-- Bounds `gaussianConvexPositionRate` above by `angle`.

**Lean implementation helper.** -/
private lemma gaussianConvexPositionRate_le_angle :
    gaussianConvexPositionRate ≤
      (1 / (32 * (512 : ℝ) ^ 2)) / 5 := by
  norm_num [gaussianConvexPositionRate]

/-- A union bound over exponentially many events remains small when each event has a stronger exponential tail.

**Lean implementation helper.** -/
private lemma exponential_union_bound (N n : ℕ) (a b c : ℝ)
    (hca : c ≤ a / 4) (hcb : c ≤ b / 5)
    (hNtwo : 2 ≤ N) (hNexp : (N : ℝ) ≤ Real.exp (c * n)) :
    2 * (N : ℝ) * Real.exp (-a * n) +
        2 * (N : ℝ) ^ 2 * Real.exp (-b * n) ≤
      Real.exp (-c * n) := by
  have hNtwoR : (2 : ℝ) ≤ N := by exact_mod_cast hNtwo
  have hexpTwo : (2 : ℝ) ≤ Real.exp (c * n) := hNtwoR.trans hNexp
  have hfour : (4 : ℝ) ≤ Real.exp (2 * c * n) := by
    calc
      (4 : ℝ) ≤ (Real.exp (c * n)) ^ 2 := by
        nlinarith [Real.exp_pos (c * n)]
      _ = Real.exp (2 * c * n) := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
  have hac : 2 * c ≤ a - 2 * c := by linarith
  have hbc : 2 * c ≤ b - 3 * c := by linarith
  have hfourA : (4 : ℝ) ≤ Real.exp ((a - 2 * c) * n) :=
    hfour.trans (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right hac (by positivity)))
  have hfourB : (4 : ℝ) ≤ Real.exp ((b - 3 * c) * n) :=
    hfour.trans (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right hbc (by positivity)))
  have hfirstExp :
      4 * Real.exp ((c - a) * n) ≤ Real.exp (-c * n) := by
    calc
      4 * Real.exp ((c - a) * n) ≤
          Real.exp ((a - 2 * c) * n) * Real.exp ((c - a) * n) :=
        mul_le_mul_of_nonneg_right hfourA (Real.exp_pos _).le
      _ = Real.exp (-c * n) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hsecondExp :
      4 * Real.exp ((2 * c - b) * n) ≤ Real.exp (-c * n) := by
    calc
      4 * Real.exp ((2 * c - b) * n) ≤
          Real.exp ((b - 3 * c) * n) * Real.exp ((2 * c - b) * n) :=
        mul_le_mul_of_nonneg_right hfourB (Real.exp_pos _).le
      _ = Real.exp (-c * n) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hfirst :
      2 * N * Real.exp (-a * n) ≤
        (1 / 2 : ℝ) * Real.exp (-c * n) := by
    calc
      2 * N * Real.exp (-a * n) ≤
          2 * Real.exp (c * n) * Real.exp (-a * n) := by
        gcongr
      _ = 2 * (Real.exp (c * n) * Real.exp (-a * n)) := by ring
      _ = 2 * Real.exp (c * n + -a * n) := by rw [← Real.exp_add]
      _ = 2 * Real.exp ((c - a) * n) := by
        congr 2
        ring
      _ ≤ (1 / 2 : ℝ) * Real.exp (-c * n) := by
        linarith
  have hNsq : (N : ℝ) ^ 2 ≤ (Real.exp (c * n)) ^ 2 := by
    gcongr
  have hsecond :
      2 * (N : ℝ) ^ 2 * Real.exp (-b * n) ≤
        (1 / 2 : ℝ) * Real.exp (-c * n) := by
    calc
      2 * (N : ℝ) ^ 2 * Real.exp (-b * n) ≤
          2 * (Real.exp (c * n)) ^ 2 * Real.exp (-b * n) := by
        gcongr
      _ = 2 * (Real.exp (c * n) * Real.exp (c * n)) *
          Real.exp (-b * n) := by rw [pow_two]
      _ = 2 * Real.exp (c * n + c * n) * Real.exp (-b * n) := by
        rw [← Real.exp_add]
      _ = 2 * (Real.exp (c * n + c * n) * Real.exp (-b * n)) := by ring
      _ = 2 * Real.exp ((c * n + c * n) + -b * n) := by
        rw [← Real.exp_add]
      _ = 2 * Real.exp ((2 * c - b) * n) := by
        congr 2
        ring
      _ ≤ (1 / 2 : ℝ) * Real.exp (-c * n) := by
        linarith
  linarith

/-- Bounds `gaussianCloudFailureBound` above by `exp`.

**Lean implementation helper.** -/
lemma gaussianCloudFailureBound_le_exp (N n : ℕ) (hNtwo : 2 ≤ N)
    (hNexp : (N : ℝ) ≤ Real.exp (gaussianConvexPositionRate * n)) :
    gaussianCloudFailureBound N n ≤
      ENNReal.ofReal (Real.exp (-gaussianConvexPositionRate * n)) := by
  rw [gaussianCloudFailureBound_eq_ofReal]
  apply ENNReal.ofReal_le_ofReal
  have h := exponential_union_bound N n
    (1 / (4 * (256 : ℝ) ^ 2))
    (1 / (32 * (512 : ℝ) ^ 2)) gaussianConvexPositionRate
    gaussianConvexPositionRate_le_radius
    gaussianConvexPositionRate_le_angle hNtwo hNexp
  convert h using 1
  all_goals ring_nf

/-- Bounds `pointsInConvexPosition_of_card` above by `one`.

**Lean implementation helper.** -/
private lemma pointsInConvexPosition_of_card_le_one
    (N n : ℕ) (hN : N ≤ 1) (g : GaussianCloud N n) :
    PointsInConvexPosition g := by
  apply exercise_3_23 g
  intro i
  refine ⟨0, ?_⟩
  intro j hji
  exfalso
  apply hji
  apply Fin.ext
  omega

/-- **Exercise 3.23, source-facing exponential form.** There is an absolute
constant `c > 0` such that, for `N ≤ exp(c n)`, `N` independent standard
Gaussian vectors in `ℝⁿ` are in convex position with probability at least
`1 - exp(-c n)`. The theorem also handles the exceptional `N ≤ 1` cases
directly, rather than forcing the coarse union bound through them.

**Book Exercise 3.23.** -/
theorem exercise_3_23_gaussian_exponential :
    ∃ c : ℝ, 0 < c ∧ ∀ (N n : ℕ), 0 < n →
      (N : ℝ) ≤ Real.exp (c * n) →
      1 - ENNReal.ofReal (Real.exp (-c * n)) ≤
        (gaussianCloudMeasure N n) {g | PointsInConvexPosition g} := by
  refine ⟨gaussianConvexPositionRate, gaussianConvexPositionRate_pos, ?_⟩
  intro N n hn hNexp
  by_cases hNtwo : 2 ≤ N
  · have hfail := gaussianCloudFailureBound_le_exp N n hNtwo hNexp
    exact (tsub_le_tsub_left hfail 1).trans
      (exercise_3_23_gaussian_quantitative N n hn)
  · have hNle : N ≤ 1 := by omega
    have hset : {g : GaussianCloud N n | PointsInConvexPosition g} = Set.univ :=
      Set.eq_univ_of_forall (pointsInConvexPosition_of_card_le_one N n hNle)
    rw [hset, measure_univ]
    exact tsub_le_self

/-! ## Exercises 3.24--3.31: balls, spherical marginals, and frames -/

/-- Normalized Lebesgue measure on the closed Euclidean unit ball. The
positive-dimensional exercise below supplies the hypotheses under which the
normalizing mass is finite and nonzero.

**Lean implementation helper.** -/
def unitBallMeasure
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] : Measure E :=
  (volume (Metric.closedBall (0 : E) 1))⁻¹ •
    volume.restrict (Metric.closedBall (0 : E) 1)

/-- The radius law in the unit ball in dimension `n`, with density
`n r^(n-1)` on `[0,1]`.

**Lean implementation helper.** -/
def unitBallRadiusMeasure (n : ℕ) : Measure ℝ :=
  volume.withDensity (fun r ↦ ENNReal.ofReal
    (if r ∈ Set.Icc (0 : ℝ) 1 then n * r ^ (n - 1) else 0))

/-- The coordinate supremum used in Exercise 3.26; `sSup` is safe even in
zero dimension, while the theorem itself assumes `2 ≤ n`.

**Book Exercise 3.26.** -/
def finSupNorm {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  sSup (Set.range fun i : Fin n ↦ |x i|)

/-- The coordinatewise clipping map onto `[-a,a]ⁿ`.

**Lean implementation helper.** -/
def cubeClip {n : ℕ} (a : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i ↦ max (-a) (min a (x i)))

/-- The closed coordinate cube.

**Lean implementation helper.** -/
def coordinateCube {n : ℕ} (a : ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ i, |x i| ≤ a}

/-- Rows of the synthesis matrix whose columns are the frame vectors.

**Lean implementation helper.** -/
def frameRow {n N : ℕ}
    (u : Fin N → EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    EuclideanSpace ℝ (Fin N) :=
  WithLp.toLp 2 (fun j ↦ u j i)

/-- The source-corrected `N`-point Mercedes--Benz family.

**Lean implementation helper.** -/
def regularPolygonFrame (N : ℕ) : Fin N → EuclideanSpace ℝ (Fin 2) :=
  fun i ↦ WithLp.toLp 2 (fun j ↦
    Real.sqrt (2 / N) *
      if j = 0 then Real.cos (2 * Real.pi * i / N)
      else Real.sin (2 * Real.pi * i / N))

end

end HDP.Chapter3

end Source_06_GaussianClouds

/-! ## Material formerly in `16_GramSDP.lean` -/

section Source_16_GramSDP

/-!
# Book Chapter 3, Section 3.5: Gram matrices and SDP relaxation
-/

open scoped BigOperators RealInnerProductSpace

namespace HDP

/-- The quadratic objective `xᵀ A x`.

**Book Equation (3.28).** -/
def quadraticObjective {n : Type*} [Fintype n]
    (A : Matrix n n ℝ) (x : n → ℝ) : ℝ :=
  ∑ i, ∑ j, A i j * x i * x j

/-- The vector relaxation of a quadratic objective.

**Book Equation (3.29).** -/
noncomputable def vectorSDPObjective {n κ : Type*} [Fintype n] [Fintype κ]
    (A : Matrix n n ℝ) (v : n → EuclideanSpace ℝ κ) : ℝ :=
  ∑ i, ∑ j, A i j * inner ℝ (v i) (v j)

/-- Embedding scalar labels along one unit direction preserves the quadratic
objective, so the vector program is a genuine relaxation.

**Lean implementation helper.** -/
theorem vectorSDPObjective_scalarEmbedding
    {n κ : Type*} [Fintype n] [Fintype κ]
    (A : Matrix n n ℝ) (x : n → ℝ)
    (e : EuclideanSpace ℝ κ) (he : ‖e‖ = 1) :
    vectorSDPObjective A (fun i => x i • e) = quadraticObjective A x := by
  simp only [vectorSDPObjective, quadraticObjective, inner_smul_left,
    inner_smul_right, real_inner_self_eq_norm_sq, he, one_pow, mul_one]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp
  ring

/-- The matrix inner product used in semidefinite programs.

**Book Equation (3.27).** -/
def matrixInner {n : Type*} [Fintype n] (A Z : Matrix n n ℝ) : ℝ :=
  ∑ i, ∑ j, A i j * Z i j

/-! ## Generic finite semidefinite programs -/

/-- Data of the finite semidefinite program in Definition 3.5.4.  The matrix
variable is positive semidefinite, and every member of `constraintIndex`
supplies one affine half-space constraint. -/
structure SemidefiniteProgram (n constraintIndex : Type*)
    [Fintype n] [Fintype constraintIndex] where
  objective : Matrix n n ℝ
  constraint : constraintIndex → Matrix n n ℝ
  bound : constraintIndex → ℝ

/-- Feasible matrices of a semidefinite program.

**Lean implementation helper.** -/
def SemidefiniteProgram.feasible
    {n constraintIndex : Type*} [Fintype n] [Fintype constraintIndex]
    (P : SemidefiniteProgram n constraintIndex) : Set (Matrix n n ℝ) :=
  {X | X.PosSemidef ∧ ∀ i, matrixInner (P.constraint i) X ≤ P.bound i}

/-- Objective value of a generic semidefinite program.

**Lean implementation helper.** -/
def SemidefiniteProgram.value
    {n constraintIndex : Type*} [Fintype n] [Fintype constraintIndex]
    (P : SemidefiniteProgram n constraintIndex) (X : Matrix n n ℝ) : ℝ :=
  matrixInner P.objective X

/-- The cone of real positive-semidefinite matrices is convex.

**Book Remark 3.5.5.** -/
theorem convex_posSemidefiniteMatrices {n : Type*} :
    Convex ℝ {X : Matrix n n ℝ | X.PosSemidef} := by
  intro X hX Y hY a b ha hb hab
  exact (hX.smul ha).add (hY.smul hb)

/-- The Frobenius matrix inner product is additive in its right argument.

**Lean implementation helper.** -/
lemma matrixInner_add_right {n : Type*} [Fintype n]
    (A X Y : Matrix n n ℝ) :
    matrixInner A (X + Y) = matrixInner A X + matrixInner A Y := by
  simp only [matrixInner, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

/-- The Frobenius matrix inner product is homogeneous in its right argument.

**Lean implementation helper.** -/
lemma matrixInner_smul_right {n : Type*} [Fintype n]
    (A X : Matrix n n ℝ) (c : ℝ) :
    matrixInner A (c • X) = c * matrixInner A X := by
  simp only [matrixInner, Matrix.smul_apply, smul_eq_mul]
  calc
    (∑ i, ∑ j, A i j * (c * X i j)) =
        ∑ i, ∑ j, c * (A i j * X i j) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = c * ∑ i, ∑ j, A i j * X i j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]

/-- The feasible set of every finite SDP is convex:
the PSD constraint is a convex cone and the remaining constraints are affine
half-spaces.

**Book Remark 3.5.5.** -/
theorem SemidefiniteProgram.convex_feasible
    {n constraintIndex : Type*} [Fintype n] [Fintype constraintIndex]
    (P : SemidefiniteProgram n constraintIndex) :
    Convex ℝ P.feasible := by
  intro X hX Y hY a b ha hb hab
  constructor
  · exact (hX.1.smul ha).add (hY.1.smul hb)
  · intro i
    rw [matrixInner_add_right, matrixInner_smul_right,
      matrixInner_smul_right]
    calc
      a * matrixInner (P.constraint i) X +
          b * matrixInner (P.constraint i) Y ≤
          a * P.bound i + b * P.bound i :=
        add_le_add (mul_le_mul_of_nonneg_left (hX.2 i) ha)
          (mul_le_mul_of_nonneg_left (hY.2 i) hb)
      _ = P.bound i := by rw [← add_mul, hab, one_mul]

/-- The bilinear objective associated with a rectangular matrix. We keep the
row index first throughout Chapter 3.

**Lean implementation helper.** -/
def bilinearObjective {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (x : m → ℝ) (y : n → ℝ) : ℝ :=
  ∑ i, ∑ j, A i j * x i * y j

/-- The unit-vector relaxation of a rectangular bilinear objective.

**Lean implementation helper.** -/
noncomputable def bilinearVectorObjective
    {m n κ : Type*} [Fintype m] [Fintype n] [Fintype κ]
    (A : Matrix m n ℝ)
    (X : m → EuclideanSpace ℝ κ) (Y : n → EuclideanSpace ℝ κ) : ℝ :=
  ∑ i, ∑ j, A i j * inner ℝ (X i) (Y j)

/-- The symmetric block matrix that turns a rectangular bilinear program into
a quadratic semidefinite program. The factor `1/2` prevents double counting
the two off-diagonal blocks.

**Book Exercise 3.52.** -/
noncomputable def bilinearSDPMatrix {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) : Matrix (m ⊕ n) (m ⊕ n) ℝ
  | Sum.inl i, Sum.inr j => A i j / 2
  | Sum.inr j, Sum.inl i => A i j / 2
  | _, _ => 0

/-- The block matrix encoding the bilinear semidefinite program is symmetric.

**Lean implementation helper.** -/
theorem bilinearSDPMatrix_isSymm {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) : (bilinearSDPMatrix A).IsSymm := by
  rw [Matrix.IsSymm.ext_iff]
  rintro (i | j) (i' | j') <;> simp [bilinearSDPMatrix]

/-- The block-SDP objective is exactly the rectangular vector objective.

**Book Exercise 3.52.** -/
theorem vectorSDPObjective_bilinearSDPMatrix
    {m n κ : Type*} [Fintype m] [Fintype n] [Fintype κ]
    (A : Matrix m n ℝ)
    (X : m → EuclideanSpace ℝ κ) (Y : n → EuclideanSpace ℝ κ) :
    vectorSDPObjective (bilinearSDPMatrix A) (Sum.elim X Y) =
      bilinearVectorObjective A X Y := by
  classical
  simp only [vectorSDPObjective, bilinearVectorObjective,
    Fintype.sum_sum_type, bilinearSDPMatrix, Sum.elim_inl, Sum.elim_inr,
    zero_mul, Finset.sum_const_zero, zero_add, add_zero]
  have hswap :
      (∑ j : n, ∑ i : m, A i j / 2 * inner ℝ (Y j) (X i)) =
        ∑ i : m, ∑ j : n, A i j / 2 * inner ℝ (X i) (Y j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [real_inner_comm]
  rw [hswap, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

end HDP

namespace HDP.Chapter3

/-- Exercise 3.51(a): every Gram matrix is positive semidefinite.

**Book Proposition 3.5.6.** -/
theorem gram_posSemidef {n κ : Type*} [Finite n] [Fintype κ]
    (v : n → EuclideanSpace ℝ κ) :
    (Matrix.gram ℝ v).PosSemidef := by
  classical
  letI := Fintype.ofFinite n
  exact Matrix.posSemidef_gram ℝ v

/-- Unit vectors give a Gram matrix with diagonal one.

**Book Proposition 3.5.6.** -/
theorem gram_diagonal_one {n κ : Type*} [Fintype κ]
    {v : n → EuclideanSpace ℝ κ}
    (hv : ∀ i, ‖v i‖ = 1) : ∀ i, Matrix.gram ℝ v i i = 1 := by
  intro i
  simp [Matrix.gram_apply, hv i]

/-- Exercise 3.51(b): every finite real positive-semidefinite matrix is a
Gram matrix in a finite-dimensional Euclidean space.

**Book Proposition 3.5.6.** -/
theorem exists_gram_of_posSemidef {n : Type*} [Finite n]
    {M : Matrix n n ℝ} (hM : M.PosSemidef) :
    ∃ (m : ℕ) (v : n → EuclideanSpace ℝ (Fin m)), Matrix.gram ℝ v = M := by
  classical
  letI := Fintype.ofFinite n
  rcases (Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hM) with ⟨m, w, hw⟩
  let v : n → EuclideanSpace ℝ (Fin m) := fun i =>
    WithLp.toLp 2 (fun k => w k i)
  refine ⟨m, v, ?_⟩
  ext i j
  rw [Matrix.gram_apply]
  simp only [PiLp.inner_apply, Real.inner_apply, v]
  have hij := congrFun (congrFun hw i) j
  rw [Matrix.sum_apply] at hij
  simpa [Matrix.vecMulVec_apply] using hij.symm

/-- The Gram substitution preserves the SDP objective.

**Book Proposition 3.5.6.** -/
theorem vectorSDPObjective_eq_matrixInner
    {n κ : Type*} [Fintype n] [Fintype κ]
    (A : Matrix n n ℝ) (v : n → EuclideanSpace ℝ κ) :
    HDP.vectorSDPObjective A v = HDP.matrixInner A (Matrix.gram ℝ v) := by
  simp [HDP.vectorSDPObjective, HDP.matrixInner, Matrix.gram_apply]

/-- The unit-vector relaxation and the PSD-matrix
formulation have the same feasible objective values.

**Book Proposition 3.5.6.** -/
theorem relaxation_is_sdp {n : Type*} [Fintype n] (A : Matrix n n ℝ) :
    (∀ (v : n → EuclideanSpace ℝ n), (∀ i, ‖v i‖ = 1) →
      ∃ Z : Matrix n n ℝ, Z.PosSemidef ∧ (∀ i, Z i i = 1) ∧
        HDP.vectorSDPObjective A v = HDP.matrixInner A Z) ∧
    (∀ Z : Matrix n n ℝ, Z.PosSemidef → (∀ i, Z i i = 1) →
      ∃ (m : ℕ) (v : n → EuclideanSpace ℝ (Fin m)),
        (∀ i, ‖v i‖ = 1) ∧
        HDP.matrixInner A Z = HDP.vectorSDPObjective A v) := by
  constructor
  · intro v hv
    refine ⟨Matrix.gram ℝ v, gram_posSemidef v, gram_diagonal_one hv, ?_⟩
    exact vectorSDPObjective_eq_matrixInner A v
  · intro Z hZ hdiag
    rcases exists_gram_of_posSemidef hZ with ⟨m, v, hvZ⟩
    refine ⟨m, v, ?_, ?_⟩
    · intro i
      have hi : Matrix.gram ℝ v i i = 1 := by
        rw [hvZ]
        exact hdiag i
      rw [Matrix.gram_apply] at hi
      rw [real_inner_self_eq_norm_sq] at hi
      have hn := norm_nonneg (v i)
      nlinarith
    · rw [← hvZ]
      exact (vectorSDPObjective_eq_matrixInner A v).symm

end HDP.Chapter3

end Source_16_GramSDP

/-! ## Material formerly in `17_SDPAttainment.lean` -/

section Source_17_SDPAttainment

/-!
# Compactness and attainment for finite vector SDPs

The feasible unit-vector assignments form a finite product of compact
spheres.  Consequently every finite continuous Gram objective attains its
maximum.  This supplies the existence premise used by the Chapter 3 rounding
algorithms.
-/

open scoped BigOperators RealInnerProductSpace

namespace HDP

/-- Convert a Boolean choice to a sign.

**Lean implementation helper.** -/
def boolSign (b : Bool) : ℝ := if b then 1 else -1

/-- The Boolean sign associated with `true` is `1`.

**Lean implementation helper.** -/
@[simp] theorem boolSign_true : boolSign true = 1 := rfl
/-- The Boolean sign associated with `false` is `-1`.

**Lean implementation helper.** -/
@[simp] theorem boolSign_false : boolSign false = -1 := rfl

/-- Identifies `boolSign` with `one_or_neg_one`.

**Lean implementation helper.** -/
theorem boolSign_eq_one_or_neg_one (b : Bool) :
    boolSign b = 1 ∨ boolSign b = -1 := by
  cases b <;> simp

/-- The finite integer quadratic program always attains its maximum.

**Book Equation (3.28).** -/
theorem exists_integerObjective_maximizer
    {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) :
    ∃ x : ι → ℝ,
      (∀ i, x i = 1 ∨ x i = -1) ∧
      ∀ y : ι → ℝ, (∀ i, y i = 1 ∨ y i = -1) →
        quadraticObjective A y ≤ quadraticObjective A x := by
  classical
  let f : (ι → Bool) → ℝ := fun b =>
    quadraticObjective A (fun i => boolSign (b i))
  obtain ⟨b, hb, hmax⟩ := Finset.exists_mem_eq_sup'
    (H := Finset.univ_nonempty (α := ι → Bool)) f
  let x : ι → ℝ := fun i => boolSign (b i)
  refine ⟨x, fun i => boolSign_eq_one_or_neg_one (b i), ?_⟩
  intro y hy
  let encode : ι → Bool := fun i => if y i = 1 then true else false
  have hdecode : (fun i => boolSign (encode i)) = y := by
    funext i
    rcases hy i with hi | hi
    · norm_num [encode, hi, boolSign]
    · norm_num [encode, hi, boolSign]
  have hle := Finset.le_sup' f (Finset.mem_univ encode)
  rw [hmax] at hle
  simpa [f, x, hdecode] using hle

/-- Unit-vector assignments for a finite vector SDP.

**Lean implementation helper.** -/
def unitVectorAssignments (ι κ : Type*) [Fintype ι] [Fintype κ] :
    Set (ι → EuclideanSpace ℝ κ) :=
  {X | ∀ i, ‖X i‖ = 1}

/-- The feasible set is compact as a finite product of Euclidean spheres.

**Lean implementation helper.** -/
theorem isCompact_unitVectorAssignments
    (ι κ : Type*) [Fintype ι] [Fintype κ] :
    IsCompact (unitVectorAssignments ι κ) := by
  have h := isCompact_pi_infinite
    (s := fun _ : ι => Metric.sphere (0 : EuclideanSpace ℝ κ) 1)
    (fun _ => isCompact_sphere _ _)
  simpa [unitVectorAssignments, Metric.mem_sphere] using h

/-- A finite vector-SDP objective is continuous in all assigned vectors.

**Lean implementation helper.** -/
theorem continuous_vectorSDPObjective
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι ι ℝ) :
    Continuous (HDP.vectorSDPObjective (κ := κ) A) := by
  unfold HDP.vectorSDPObjective
  fun_prop

/-- Every fixed finite-dimensional vector SDP with a nontrivial target
dimension attains its optimum.

**Book Equation (3.29).** -/
theorem vectorSDPObjective_attains
    {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty κ]
    (A : Matrix ι ι ℝ) :
    ∃ X : ι → EuclideanSpace ℝ κ,
      (∀ i, ‖X i‖ = 1) ∧
      ∀ Y : ι → EuclideanSpace ℝ κ, (∀ i, ‖Y i‖ = 1) →
        HDP.vectorSDPObjective A Y ≤ HDP.vectorSDPObjective A X := by
  classical
  let i0 : κ := Classical.choice inferInstance
  let e : EuclideanSpace ℝ κ := EuclideanSpace.single i0 1
  have he : ‖e‖ = 1 := by simp [e]
  have hne : (unitVectorAssignments ι κ).Nonempty :=
    ⟨fun _ => e, fun _ => he⟩
  obtain ⟨X, hX, hmax⟩ :=
    (isCompact_unitVectorAssignments ι κ).exists_isMaxOn hne
      (continuous_vectorSDPObjective A).continuousOn
  exact ⟨X, hX, fun Y hY => hmax hY⟩

end HDP

namespace HDP.Chapter3

/-- Source-facing attainment statement for the SDP in (3.29).

**Book Section 3.5.** -/
theorem sdp_attains
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (A : Matrix ι ι ℝ) :
    ∃ X : ι → EuclideanSpace ℝ ι,
      (∀ i, ‖X i‖ = 1) ∧
      ∀ Y : ι → EuclideanSpace ℝ ι, (∀ i, ‖Y i‖ = 1) →
        HDP.vectorSDPObjective A Y ≤ HDP.vectorSDPObjective A X :=
  HDP.vectorSDPObjective_attains A

end HDP.Chapter3

end Source_17_SDPAttainment

/-! ## Material formerly in `20_SignArcsin.lean` -/

section Source_20_SignArcsin

open Set Real MeasureTheory intervalIntegral Filter ProbabilityTheory InnerProductSpace

/-!
# Gaussian sign--arcsine identity

This source-neutral helper proves the exact sign correlation formula for two
standard Gaussian projections.  It is separated from the source-numbered
Chapter 3 interfaces so both Gaussian rounding and Grothendieck arguments can
reuse the same theorem without an import cycle.
-/

namespace HDP

noncomputable section

/-- The source's `±1` sign convention. We choose `+1` at zero; centered
nondegenerate Gaussian marginals hit zero with probability zero.

**Book Section 3.5.** -/
def pmSign (x : ℝ) : ℝ := if 0 ≤ x then 1 else -1

/-- Shows that `pmSign_of` is nonnegative.

**Lean implementation helper.** -/
@[simp] lemma pmSign_of_nonneg {x : ℝ} (hx : 0 ≤ x) : pmSign x = 1 := by
  simp [pmSign, hx]

/-- The plus/minus sign function equals `-1` on negative inputs.

**Lean implementation helper.** -/
@[simp] lemma pmSign_of_neg {x : ℝ} (hx : x < 0) : pmSign x = -1 := by
  simp [pmSign, not_le.mpr hx]

/-- The absolute value of the plus/minus sign is one.

**Lean implementation helper.** -/
lemma abs_pmSign (x : ℝ) : |pmSign x| = 1 := by
  by_cases hx : 0 ≤ x <;> simp [pmSign, hx]

/-- The square of the plus/minus sign is one.

**Lean implementation helper.** -/
@[simp] lemma pmSign_sq (x : ℝ) : pmSign x ^ 2 = 1 := by
  by_cases hx : 0 ≤ x <;> simp [pmSign, hx]

/-- Multiplying the input by `-1` negates the plus/minus sign away from zero.

**Lean implementation helper.** -/
private lemma pmSign_mul_neg {x : ℝ} (hx : x ≠ 0) :
    pmSign x * pmSign (-x) = -1 := by
  rcases lt_or_gt_of_ne hx with hxneg | hxpos
  · rw [pmSign_of_neg hxneg, pmSign_of_nonneg (neg_nonneg.mpr hxneg.le)]
    norm_num
  · rw [pmSign_of_nonneg hxpos.le, pmSign_of_neg (neg_neg_of_pos hxpos)]
    norm_num

/-- The `±1` sign convention is Borel measurable.

**Lean implementation helper.** -/
theorem measurable_pmSign : Measurable pmSign := by
  unfold pmSign
  exact Measurable.ite measurableSet_Ici measurable_const measurable_const

/-- For `0 ≤ a ≤ π`, `angular_sign_integral` evaluates the cosine-sign correlation over a full period as `2π - 4a`.

**Lean implementation helper.** -/
private lemma angular_sign_integral (a : ℝ) (ha : a ∈ Icc (0 : ℝ) Real.pi) :
    (∫ θ in (-Real.pi)..Real.pi,
      pmSign (Real.cos θ) * pmSign (Real.cos (θ - a))) =
      2 * Real.pi - 4 * a := by
  let f : ℝ → ℝ := fun θ ↦ pmSign (Real.cos θ) * pmSign (Real.cos (θ - a))
  have hper : Function.Periodic f (2 * Real.pi) := by
    intro θ
    dsimp [f]
    rw [show θ + 2 * Real.pi - a = (θ - a) + 2 * Real.pi by ring]
    simp
  have hfmeas : Measurable f := by
    dsimp [f]
    exact (measurable_pmSign.comp Real.measurable_cos).mul
      (measurable_pmSign.comp (Real.measurable_cos.comp (measurable_id.sub measurable_const)))
  have hfint (u v : ℝ) : IntervalIntegrable f volume u v := by
    refine (intervalIntegral.intervalIntegrable_const
      (a := u) (b := v) (c := (1 : ℝ))).mono_fun ?_ ?_
    · exact hfmeas.aestronglyMeasurable
    · filter_upwards [] with θ
      simp only [norm_eq_abs, norm_one, f]
      rw [abs_mul, abs_pmSign, abs_pmSign, one_mul]
  have hpi : 0 < Real.pi := Real.pi_pos
  let x₀ : ℝ := -(Real.pi / 2)
  let x₁ : ℝ := a - Real.pi / 2
  let x₂ : ℝ := Real.pi / 2
  let x₃ : ℝ := a + Real.pi / 2
  let x₄ : ℝ := 3 * Real.pi / 2
  have h₀₁ : x₀ ≤ x₁ := by dsimp [x₀, x₁]; linarith [ha.1]
  have h₁₂ : x₁ ≤ x₂ := by dsimp [x₁, x₂]; linarith [ha.2]
  have h₂₃ : x₂ ≤ x₃ := by dsimp [x₂, x₃]; linarith [ha.1]
  have h₃₄ : x₃ ≤ x₄ := by dsimp [x₃, x₄]; linarith [ha.2]
  have hseg₀ : (∫ θ in x₀..x₁, f θ) = -(a : ℝ) := by
    calc
      (∫ θ in x₀..x₁, f θ) = ∫ _ in x₀..x₁, (-1 : ℝ) := by
        apply integral_congr_Ioo_of_le h₀₁
        intro θ hθ
        have hc₁ : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by
          dsimp [x₀] at hθ ⊢; exact hθ.1.le, by
          dsimp [x₁] at hθ
          linarith [hθ.2, ha.2]⟩
        have hc₂ : Real.cos (θ - a) < 0 := by
          rw [← Real.cos_add_two_pi (θ - a)]
          apply Real.cos_neg_of_pi_div_two_lt_of_lt
          · dsimp [x₀] at hθ
            linarith [hθ.1, ha.2]
          · dsimp [x₁] at hθ
            linarith [hθ.2]
        simp [f, pmSign_of_nonneg hc₁, pmSign_of_neg hc₂]
      _ = -(a : ℝ) := by simp [x₀, x₁]
  have hseg₁ : (∫ θ in x₁..x₂, f θ) = Real.pi - a := by
    calc
      (∫ θ in x₁..x₂, f θ) = ∫ _ in x₁..x₂, (1 : ℝ) := by
        apply integral_congr_Ioo_of_le h₁₂
        intro θ hθ
        have hc₁ : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by
          dsimp [x₁] at hθ
          linarith [hθ.1, ha.1], by
          dsimp [x₂] at hθ ⊢
          exact hθ.2⟩
        have hc₂ : 0 < Real.cos (θ - a) := Real.cos_pos_of_mem_Ioo ⟨by
          dsimp [x₁] at hθ
          linarith [hθ.1], by
          dsimp [x₂] at hθ
          linarith [hθ.2, ha.1]⟩
        simp [f, pmSign_of_nonneg hc₁.le, pmSign_of_nonneg hc₂.le]
      _ = Real.pi - a := by simp [x₁, x₂]; ring_nf
  have hseg₂ : (∫ θ in x₂..x₃, f θ) = -(a : ℝ) := by
    calc
      (∫ θ in x₂..x₃, f θ) = ∫ _ in x₂..x₃, (-1 : ℝ) := by
        apply integral_congr_Ioo_of_le h₂₃
        intro θ hθ
        have hc₁ : Real.cos θ < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt (by
          dsimp [x₂] at hθ ⊢
          exact hθ.1) (by
          dsimp [x₃] at hθ
          linarith [hθ.2, ha.2])
        have hc₂ : 0 < Real.cos (θ - a) := Real.cos_pos_of_mem_Ioo ⟨by
          dsimp [x₂] at hθ
          linarith [hθ.1, ha.2], by
          dsimp [x₃] at hθ
          linarith [hθ.2]⟩
        simp [f, pmSign_of_neg hc₁, pmSign_of_nonneg hc₂.le]
      _ = -(a : ℝ) := by simp [x₂, x₃]
  have hseg₃ : (∫ θ in x₃..x₄, f θ) = Real.pi - a := by
    calc
      (∫ θ in x₃..x₄, f θ) = ∫ _ in x₃..x₄, (1 : ℝ) := by
        apply integral_congr_Ioo_of_le h₃₄
        intro θ hθ
        have hc₁ : Real.cos θ < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt (by
          dsimp [x₃] at hθ
          linarith [hθ.1, ha.1]) (by
          dsimp [x₄] at hθ
          linarith [hθ.2])
        have hc₂ : Real.cos (θ - a) < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt (by
          dsimp [x₃] at hθ
          linarith [hθ.1]) (by
          dsimp [x₄] at hθ
          linarith [hθ.2, ha.1])
        simp [f, pmSign_of_neg hc₁, pmSign_of_neg hc₂]
      _ = Real.pi - a := by simp [x₃, x₄]; ring_nf
  have hchosen : (∫ θ in x₀..x₄, f θ) = 2 * Real.pi - 4 * a := by
    rw [← integral_add_adjacent_intervals (hfint x₀ x₁) (hfint x₁ x₄),
      ← integral_add_adjacent_intervals (hfint x₁ x₂) (hfint x₂ x₄),
      ← integral_add_adjacent_intervals (hfint x₂ x₃) (hfint x₃ x₄),
      hseg₀, hseg₁, hseg₂, hseg₃]
    ring_nf
  change (∫ θ in (-Real.pi)..Real.pi, f θ) = _
  calc
    (∫ θ in (-Real.pi)..Real.pi, f θ) = ∫ θ in x₀..x₄, f θ := by
      have hshift := hper.intervalIntegral_add_eq (-Real.pi) x₀
      have hleft : -Real.pi + 2 * Real.pi = Real.pi := by ring_nf
      have hright : x₀ + 2 * Real.pi = x₄ := by dsimp [x₀, x₄]; ring_nf
      rwa [hleft, hright] at hshift
    _ = 2 * Real.pi - 4 * a := hchosen

/-- `radial_gaussian_integral` evaluates `∫₀^∞ r * exp (-(1 / 2) * r²) dr` as `1`.

**Lean implementation helper.** -/
private lemma radial_gaussian_integral :
    ∫ r : ℝ in Ioi 0, r * Real.exp (-(1 / 2 : ℝ) * r ^ 2) = 1 := by
  have hderiv (r : ℝ) :
      HasDerivAt (fun x : ℝ ↦ -Real.exp (-(1 / 2 : ℝ) * x ^ 2))
        (r * Real.exp (-(1 / 2 : ℝ) * r ^ 2)) r := by
    convert (((hasDerivAt_pow 2 r).const_mul (-(1 / 2 : ℝ))).exp.neg) using 1
    · rfl
    · rfl
    · funext x
      simp
    · ring_nf
  have hint : IntegrableOn (fun r : ℝ ↦ r * Real.exp (-(1 / 2 : ℝ) * r ^ 2)) (Ioi 0) :=
    (integrable_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).integrableOn
  have ht : Tendsto (fun r : ℝ ↦ -Real.exp (-(1 / 2 : ℝ) * r ^ 2))
      atTop (nhds 0) := by
    have hpow : Tendsto (fun r : ℝ ↦ r ^ 2) atTop atTop :=
      tendsto_pow_atTop two_ne_zero
    have hneg : Tendsto (fun r : ℝ ↦ -(1 / 2 : ℝ) * r ^ 2) atTop atBot :=
      hpow.const_mul_atTop_of_neg (by norm_num)
    simpa using (tendsto_exp_atBot.comp hneg).neg
  convert integral_Ioi_of_hasDerivAt_of_tendsto' (fun r _ ↦ hderiv r) hint ht using 1
  all_goals norm_num

/-- The product of two standard one-dimensional Gaussian densities is the standard planar Gaussian density.

**Lean implementation helper.** -/
private lemma gaussianPDFReal_zero_one_mul (x y : ℝ) :
    ProbabilityTheory.gaussianPDFReal 0 1 x *
        ProbabilityTheory.gaussianPDFReal 0 1 y =
      (2 * Real.pi)⁻¹ * Real.exp (-(x ^ 2 + y ^ 2) / 2) := by
  simp only [ProbabilityTheory.gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  have hp : 0 < Real.pi := Real.pi_pos
  have hs : (√(2 * Real.pi)) ^ 2 = 2 * Real.pi := Real.sq_sqrt (by positivity)
  have hconst : (√(2 * Real.pi))⁻¹ ^ 2 = (2 * Real.pi)⁻¹ := by
    rw [inv_pow, hs]
  rw [show (√(2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) *
      ((√(2 * Real.pi))⁻¹ * Real.exp (-y ^ 2 / 2)) =
      (√(2 * Real.pi))⁻¹ ^ 2 *
        (Real.exp (-x ^ 2 / 2) * Real.exp (-y ^ 2 / 2)) by ring,
    ← Real.exp_add, hconst]
  congr 1
  ring_nf

/-- Multiplication by a positive scalar does not change the plus/minus sign.

**Lean implementation helper.** -/
private lemma pmSign_pos_mul {r : ℝ} (hr : 0 < r) (x : ℝ) :
    pmSign (r * x) = pmSign x := by
  by_cases hx : 0 ≤ x
  · rw [pmSign_of_nonneg hx, pmSign_of_nonneg (mul_nonneg hr.le hx)]
  · have hx' : x < 0 := lt_of_not_ge hx
    rw [pmSign_of_neg hx', pmSign_of_neg (mul_neg_of_pos_of_neg hr hx')]

/-- For `0 ≤ a ≤ π`, `gaussian_pair_angle_integral` gives the Gaussian sign correlation `1 - 2a / π`.

**Lean implementation helper.** -/
private lemma gaussian_pair_angle_integral (a : ℝ) (ha : a ∈ Icc (0 : ℝ) Real.pi) :
    (∫ p : ℝ × ℝ,
      pmSign p.1 * pmSign (Real.cos a * p.1 + Real.sin a * p.2)
        ∂((ProbabilityTheory.gaussianReal 0 1).prod
          (ProbabilityTheory.gaussianReal 0 1))) =
      1 - 2 * a / Real.pi := by
  let A : ℝ → ℝ := fun θ ↦ pmSign (Real.cos θ) * pmSign (Real.cos (θ - a))
  let R : ℝ → ℝ := fun r ↦
    (2 * Real.pi)⁻¹ * (r * Real.exp (-(1 / 2 : ℝ) * r ^ 2))
  have hangle : ∫ θ in Ioo (-Real.pi) Real.pi, A θ = 2 * Real.pi - 4 * a := by
    rw [← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
    exact angular_sign_integral a ha
  have hradial : ∫ r in Ioi (0 : ℝ), R r = (2 * Real.pi)⁻¹ := by
    dsimp [R]
    rw [MeasureTheory.integral_const_mul, radial_gaussian_integral, mul_one]
  rw [ProbabilityTheory.gaussianReal_of_var_ne_zero 0
      (by norm_num : (1 : NNReal) ≠ 0),
    prod_withDensity (ProbabilityTheory.measurable_gaussianPDF 0 1)
      (ProbabilityTheory.measurable_gaussianPDF 0 1)]
  rw [integral_withDensity_eq_integral_toReal_smul
    (by fun_prop)
    (ae_of_all _ fun p ↦ ENNReal.mul_lt_top
      ProbabilityTheory.gaussianPDF_lt_top ProbabilityTheory.gaussianPDF_lt_top)]
  simp only [ENNReal.toReal_mul, ProbabilityTheory.toReal_gaussianPDF, smul_eq_mul]
  calc
    (∫ p : ℝ × ℝ,
        (ProbabilityTheory.gaussianPDFReal 0 1 p.1 *
          ProbabilityTheory.gaussianPDFReal 0 1 p.2) *
            (pmSign p.1 * pmSign (Real.cos a * p.1 + Real.sin a * p.2))) =
        ∫ p in polarCoord.target, p.1 •
          ((ProbabilityTheory.gaussianPDFReal 0 1 (polarCoord.symm p).1 *
            ProbabilityTheory.gaussianPDFReal 0 1 (polarCoord.symm p).2) *
              (pmSign (polarCoord.symm p).1 *
                pmSign (Real.cos a * (polarCoord.symm p).1 +
                  Real.sin a * (polarCoord.symm p).2))) := by
          rw [← integral_comp_polarCoord_symm]
    _ = (∫ r in Ioi (0 : ℝ), R r) * ∫ θ in Ioo (-Real.pi) Real.pi, A θ := by
      rw [← setIntegral_prod_mul]
      apply setIntegral_congr_fun polarCoord.open_target.measurableSet
      intro p hp
      have hr : 0 < p.1 := hp.1
      simp only [polarCoord_symm_apply]
      rw [gaussianPDFReal_zero_one_mul]
      have hsquares :
          (p.1 * Real.cos p.2) ^ 2 + (p.1 * Real.sin p.2) ^ 2 = p.1 ^ 2 := by
        nlinarith [Real.sin_sq_add_cos_sq p.2]
      have hlinear :
          Real.cos a * (p.1 * Real.cos p.2) + Real.sin a * (p.1 * Real.sin p.2) =
            p.1 * Real.cos (p.2 - a) := by
        rw [Real.cos_sub]
        ring_nf
      rw [hsquares, hlinear, pmSign_pos_mul hr, pmSign_pos_mul hr]
      simp only [smul_eq_mul, R, A]
      ring_nf
    _ = 1 - 2 * a / Real.pi := by
      rw [hradial, hangle]
      field_simp [Real.pi_ne_zero]
      ring_nf

/-- Sheppard's formula for the coordinate representation of a correlated
standard Gaussian pair.

**Book Lemma 3.6.5.** -/
theorem gaussian_pair_sign_arcsin (rho : ℝ) (hrho : rho ∈ Icc (-1 : ℝ) 1) :
    (∫ p : ℝ × ℝ,
      pmSign p.1 * pmSign (rho * p.1 + √(1 - rho ^ 2) * p.2)
        ∂((ProbabilityTheory.gaussianReal 0 1).prod
          (ProbabilityTheory.gaussianReal 0 1))) =
      (2 / Real.pi) * Real.arcsin rho := by
  have ha : Real.arccos rho ∈ Icc (0 : ℝ) Real.pi :=
    ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
  have h := gaussian_pair_angle_integral (Real.arccos rho) ha
  rw [Real.cos_arccos hrho.1 hrho.2, Real.sin_arccos] at h
  calc
    _ = 1 - 2 * Real.arccos rho / Real.pi := h
    _ = (2 / Real.pi) * Real.arcsin rho := by
      rw [Real.arcsin_eq_pi_div_two_sub_arccos]
      field_simp [Real.pi_ne_zero]

/-- The sign--arcsine identity in an orthonormal two-dimensional Gaussian
subspace.

**Lean implementation helper.** -/
theorem stdGaussian_orthonormal_sign_arcsin
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (u w : E) (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (huw : inner ℝ u w = 0)
    (rho : ℝ) (hrho : rho ∈ Icc (-1 : ℝ) 1) :
    (∫ g : E,
      pmSign (inner ℝ u g) *
        pmSign (inner ℝ (rho • u + √(1 - rho ^ 2) • w) g)
          ∂(ProbabilityTheory.stdGaussian E)) =
      (2 / Real.pi) * Real.arcsin rho := by
  let X : E → ℝ := fun g ↦ inner ℝ u g
  let Y : E → ℝ := fun g ↦ inner ℝ w g
  let L : E →L[ℝ] (ℝ × ℝ) :=
    ((innerSL ℝ) u).prod ((innerSL ℝ) w)
  have hpair : ProbabilityTheory.HasGaussianLaw (fun g : E ↦ (X g, Y g))
      (ProbabilityTheory.stdGaussian E) := by
    have hid : HasGaussianLaw (id : E → E) (stdGaussian E) :=
      IsGaussian.hasGaussianLaw_id
    have h := HasGaussianLaw.map_of_measurable L hid (by fun_prop)
    exact h.congr (ae_of_all _ fun g ↦ by
      change L (id g) = (X g, Y g)
      simp [L, X, Y, innerSL_apply_apply])
  have hcov : cov[X, Y; stdGaussian E] = 0 := by
    rw [← ProbabilityTheory.covarianceBilin_apply_eq_cov
      (ProbabilityTheory.IsGaussian.memLp_two_id :
        MemLp id 2 (ProbabilityTheory.stdGaussian E)) u w,
      ProbabilityTheory.covarianceBilin_stdGaussian]
    change inner ℝ u w = 0
    exact huw
  have hind : ProbabilityTheory.IndepFun X Y (ProbabilityTheory.stdGaussian E) :=
    hpair.indepFun_of_covariance_eq_zero hcov
  have hXlaw :
      (ProbabilityTheory.stdGaussian E).map X = ProbabilityTheory.gaussianReal 0 1 := by
    have h := (ProbabilityTheory.IsGaussian.map_eq_gaussianReal
      ((innerSL ℝ) u) :
        (ProbabilityTheory.stdGaussian E).map ((innerSL ℝ) u) =
          ProbabilityTheory.gaussianReal
            ((ProbabilityTheory.stdGaussian E)[(innerSL ℝ) u])
            Var[(innerSL ℝ) u; ProbabilityTheory.stdGaussian E].toNNReal)
    rw [ProbabilityTheory.integral_strongDual_stdGaussian,
      ProbabilityTheory.variance_dual_stdGaussian, innerSL_apply_norm, hu] at h
    simpa [X, innerSL_apply_apply] using h
  have hYlaw :
      (ProbabilityTheory.stdGaussian E).map Y = ProbabilityTheory.gaussianReal 0 1 := by
    have h := (ProbabilityTheory.IsGaussian.map_eq_gaussianReal
      ((innerSL ℝ) w) :
        (ProbabilityTheory.stdGaussian E).map ((innerSL ℝ) w) =
          ProbabilityTheory.gaussianReal
            ((ProbabilityTheory.stdGaussian E)[(innerSL ℝ) w])
            Var[(innerSL ℝ) w; ProbabilityTheory.stdGaussian E].toNNReal)
    rw [ProbabilityTheory.integral_strongDual_stdGaussian,
      ProbabilityTheory.variance_dual_stdGaussian, innerSL_apply_norm, hw] at h
    simpa [Y, innerSL_apply_apply] using h
  have hjoint :
      (ProbabilityTheory.stdGaussian E).map (fun g : E ↦ (X g, Y g)) =
        (ProbabilityTheory.gaussianReal 0 1).prod
          (ProbabilityTheory.gaussianReal 0 1) := by
    rw [hind.map_prod_eq_prod_map_map (by fun_prop) (by fun_prop), hXlaw, hYlaw]
  calc
    (∫ g : E,
      pmSign (inner ℝ u g) *
        pmSign (inner ℝ (rho • u + √(1 - rho ^ 2) • w) g)
          ∂(ProbabilityTheory.stdGaussian E)) =
        ∫ g : E, pmSign (X g) *
          pmSign (rho * X g + √(1 - rho ^ 2) * Y g)
          ∂(ProbabilityTheory.stdGaussian E) := by
          congr with g
          simp [X, Y, inner_add_left, real_inner_smul_left]
    _ = ∫ p : ℝ × ℝ,
        pmSign p.1 * pmSign (rho * p.1 + √(1 - rho ^ 2) * p.2)
          ∂((ProbabilityTheory.stdGaussian E).map (fun g : E ↦ (X g, Y g))) := by
      have hF : Measurable (fun p : ℝ × ℝ ↦
          pmSign p.1 * pmSign (rho * p.1 + √(1 - rho ^ 2) * p.2)) :=
        (measurable_pmSign.comp measurable_fst).mul
          (measurable_pmSign.comp
            ((measurable_const.mul measurable_fst).add
              (measurable_const.mul measurable_snd)))
      rw [MeasureTheory.integral_map (by fun_prop) hF.aestronglyMeasurable]
    _ = ∫ p : ℝ × ℝ,
        pmSign p.1 * pmSign (rho * p.1 + √(1 - rho ^ 2) * p.2)
          ∂((ProbabilityTheory.gaussianReal 0 1).prod
            (ProbabilityTheory.gaussianReal 0 1)) := by rw [hjoint]
    _ = (2 / Real.pi) * Real.arcsin rho := gaussian_pair_sign_arcsin rho hrho

/-- The exact Gaussian sign correlation identity for arbitrary unit vectors.

**Book Lemma 3.6.5.** -/
theorem stdGaussian_unit_sign_arcsin
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    (∫ g : E, pmSign (inner ℝ u g) * pmSign (inner ℝ v g)
      ∂(ProbabilityTheory.stdGaussian E)) =
      (2 / Real.pi) * Real.arcsin (inner ℝ u v) := by
  let rho : ℝ := inner ℝ u v
  let s : ℝ := √(1 - rho ^ 2)
  change _ = (2 / Real.pi) * Real.arcsin rho
  have habs : |rho| ≤ 1 := by
    dsimp [rho]
    simpa [hu, hv] using abs_real_inner_le_norm u v
  have hrho : rho ∈ Icc (-1 : ℝ) 1 :=
    ⟨neg_le_of_abs_le habs, le_of_abs_le habs⟩
  have hq : 0 ≤ 1 - rho ^ 2 :=
    sub_nonneg.mpr ((sq_le_one_iff_abs_le_one rho).2 habs)
  have hsq : s ^ 2 = 1 - rho ^ 2 := by
    dsimp [s]
    exact Real.sq_sqrt hq
  have hnormsq : ‖v - rho • u‖ ^ 2 = 1 - rho ^ 2 := by
    rw [norm_sub_sq_real, hv, norm_smul, hu, mul_one, real_inner_smul_right]
    have hcomm : inner ℝ v u = rho := by
      dsimp [rho]
      rw [real_inner_comm]
    rw [hcomm]
    simp only [Real.norm_eq_abs, sq_abs]
    ring_nf
  by_cases hs0 : s = 0
  · have hqzero : 1 - rho ^ 2 = 0 := by nlinarith [hsq]
    have hrhosq : rho ^ 2 = 1 := by nlinarith
    have hvrel : v = rho • u := by
      have hnzero : ‖v - rho • u‖ = 0 := by
        nlinarith [hnormsq, norm_nonneg (v - rho • u)]
      exact sub_eq_zero.mp (norm_eq_zero.mp hnzero)
    rcases sq_eq_one_iff.mp hrhosq with hrho_one | hrho_neg_one
    · have hvu : v = u := by simpa [hrho_one] using hvrel
      calc
        (∫ g : E, pmSign (inner ℝ u g) * pmSign (inner ℝ v g)
          ∂(ProbabilityTheory.stdGaussian E)) = ∫ _ : E, (1 : ℝ)
            ∂(ProbabilityTheory.stdGaussian E) := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards [] with g
              rw [hvu, ← pow_two, pmSign_sq]
        _ = 1 := by simp
        _ = (2 / Real.pi) * Real.arcsin rho := by
          rw [hrho_one, Real.arcsin_one]
          field_simp [Real.pi_ne_zero]
    · have hvu : v = -u := by simpa [hrho_neg_one] using hvrel
      let X : E → ℝ := fun g ↦ inner ℝ u g
      have hXlaw :
          (ProbabilityTheory.stdGaussian E).map X = ProbabilityTheory.gaussianReal 0 1 := by
        have h := (ProbabilityTheory.IsGaussian.map_eq_gaussianReal ((innerSL ℝ) u) :
          (ProbabilityTheory.stdGaussian E).map ((innerSL ℝ) u) =
            ProbabilityTheory.gaussianReal
              ((ProbabilityTheory.stdGaussian E)[(innerSL ℝ) u])
              Var[(innerSL ℝ) u; ProbabilityTheory.stdGaussian E].toNNReal)
        rw [ProbabilityTheory.integral_strongDual_stdGaussian,
          ProbabilityTheory.variance_dual_stdGaussian, innerSL_apply_norm, hu] at h
        simpa [X, innerSL_apply_apply] using h
      have hXhas : HasLaw X (ProbabilityTheory.gaussianReal 0 1)
          (ProbabilityTheory.stdGaussian E) := ⟨by fun_prop, hXlaw⟩
      letI : NoAtoms (ProbabilityTheory.gaussianReal 0 1) :=
        ProbabilityTheory.noAtoms_gaussianReal (by norm_num)
      have hne : ∀ᵐ g ∂(ProbabilityTheory.stdGaussian E), X g ≠ 0 :=
        (hXhas.ae_iff (by fun_prop)).2
          ((ProbabilityTheory.gaussianReal 0 1).ae_ne 0)
      calc
        (∫ g : E, pmSign (inner ℝ u g) * pmSign (inner ℝ v g)
          ∂(ProbabilityTheory.stdGaussian E)) = ∫ _ : E, (-1 : ℝ)
            ∂(ProbabilityTheory.stdGaussian E) := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards [hne] with g hg
              change pmSign (X g) * pmSign (inner ℝ v g) = -1
              rw [hvu, inner_neg_left]
              exact pmSign_mul_neg hg
        _ = -1 := by simp
        _ = (2 / Real.pi) * Real.arcsin rho := by
          rw [hrho_neg_one, Real.arcsin_neg_one]
          field_simp [Real.pi_ne_zero]
  · have hspos : 0 < s := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hs0)
    let w : E := s⁻¹ • (v - rho • u)
    have hnorm : ‖v - rho • u‖ = s := by
      nlinarith [hnormsq, hsq, norm_nonneg (v - rho • u)]
    have hw : ‖w‖ = 1 := by
      dsimp [w]
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hspos, hnorm]
      exact inv_mul_cancel₀ hs0
    have huw : inner ℝ u w = 0 := by
      dsimp [w]
      rw [real_inner_smul_right, inner_sub_right, real_inner_smul_right,
        real_inner_self_eq_norm_sq, hu]
      change s⁻¹ * (rho - rho * 1 ^ 2) = 0
      ring_nf
    have hdecomp : rho • u + s • w = v := by
      dsimp [w]
      rw [smul_smul, mul_inv_cancel₀ hs0, one_smul]
      abel
    have h := stdGaussian_orthonormal_sign_arcsin u w hu hw huw rho hrho
    rw [hdecomp] at h
    simpa [rho] using h

end
end HDP

end Source_20_SignArcsin

/-! ## Material formerly in `19_GaussianRounding.lean` -/

section Source_19_GaussianRounding

/-!
# Gaussian hyperplane rounding

This file contains the deterministic rounding interface.  Distributional
identities for the rounded labels live in `21_Grothendieck.lean`, so the construction
can also be reused with any rotation-invariant direction law.
-/

open scoped BigOperators RealInnerProductSpace

namespace HDP

/-- Random-hyperplane label associated with a direction `g`.

**Book Equation (3.34).** -/
noncomputable def hyperplaneLabel
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g u : E) : ℝ :=
  pmSign (inner ℝ u g)

/-- Every random-hyperplane label has square one.

**Lean implementation helper.** -/
@[simp] theorem hyperplaneLabel_sq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g u : E) : hyperplaneLabel g u ^ 2 = 1 :=
  pmSign_sq _

/-- Every random-hyperplane label is either `1` or `-1`.

**Lean implementation helper.** -/
theorem hyperplaneLabel_mem
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g u : E) : hyperplaneLabel g u = 1 ∨ hyperplaneLabel g u = -1 := by
  by_cases h : 0 ≤ inner ℝ u g
  · exact Or.inl (pmSign_of_nonneg h)
  · exact Or.inr (pmSign_of_neg (lt_of_not_ge h))

end HDP

namespace HDP.Chapter3

/-- Equation (3.34), exposed with a source-facing name. -/
noncomputable abbrev gaussianRoundingLabel
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g u : E) : ℝ :=
  HDP.hyperplaneLabel g u

end HDP.Chapter3

end Source_19_GaussianRounding

/-! ## Material formerly in `21_Grothendieck.lean` -/

section Source_21_Grothendieck

/-!
# Book Chapter 3: the analytic Goemans--Williamson inequality

This file proves the exact rational version of the numerical inequality used in
Section 3.6.  The probabilistic sign--arcsine identity is kept separate: the
analytic estimate below has no probabilistic assumptions.
-/

open Set Real MeasureTheory ProbabilityTheory InnerProductSpace

namespace HDP

noncomputable section

/-- The arccosine function is convex on the interval from `-1` to `0`.

**Lean implementation helper.** -/
private theorem convexOn_arccos_Icc_neg_one_zero :
    ConvexOn ℝ (Icc (-1 : ℝ) 0) Real.arccos := by
  let f' : ℝ → ℝ := fun x ↦ -(1 / √(1 - x ^ 2))
  let f'' : ℝ → ℝ := fun x ↦
    ((-2 * x) / (2 * √(1 - x ^ 2))) / (√(1 - x ^ 2)) ^ 2
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
      Real.continuous_arccos.continuousOn
      (f' := f') (f'' := f'')
  · intro x hx
    rw [interior_Icc] at hx
    rcases hx with ⟨hxlow, hxhigh⟩
    exact (Real.hasDerivAt_arccos (by linarith) (by linarith)).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rcases hx with ⟨hxlow, hxhigh⟩
    have hq : HasDerivAt (fun y : ℝ ↦ 1 - y ^ 2) (-2 * x) x := by
      convert (hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2) using 1
      · rfl
      · rfl
      · funext y
        simp [Pi.sub_apply, pow_two]
      · simp [id_eq, mul_comm]
    have hqpos : 0 < 1 - x ^ 2 := by nlinarith
    have hs := hq.sqrt (ne_of_gt hqpos)
    have hi := hs.inv (Real.sqrt_ne_zero'.2 hqpos)
    have hn := hi.neg
    convert hn.hasDerivWithinAt using 1
    · rfl
    · rfl
    · funext y
      simp [f', one_div, Pi.neg_apply, Pi.inv_apply]
    · dsimp [f'']
      ring
  · intro x hx
    rw [interior_Icc] at hx
    rcases hx with ⟨hxlow, hxhigh⟩
    dsimp [f'']
    have hqpos : 0 < 1 - x ^ 2 := by nlinarith
    have hspos : 0 < √(1 - x ^ 2) := Real.sqrt_pos.2 hqpos
    apply div_nonneg
    · apply div_nonneg
      · linarith
      · positivity
    · positivity

/-- On the negative half interval, arccosine lies above its tangent line at the chosen point.

**Lean implementation helper.** -/
private theorem arccos_tangent_lower {x a : ℝ}
    (hx : x ∈ Icc (-1 : ℝ) 0) (ha : a ∈ Ioo (-1 : ℝ) 0) :
    Real.arccos a - (1 / √(1 - a ^ 2)) * (x - a) ≤ Real.arccos x := by
  have ha' : a ∈ Icc (-1 : ℝ) 0 := ⟨ha.1.le, ha.2.le⟩
  have hder : HasDerivAt Real.arccos (-(1 / √(1 - a ^ 2))) a :=
    Real.hasDerivAt_arccos (ne_of_gt ha.1) (by nlinarith [ha.2])
  rcases lt_trichotomy x a with hxa | rfl | hax
  · have hs := convexOn_arccos_Icc_neg_one_zero.slope_le_of_hasDerivAt
        hx ha' hxa hder
    rw [slope_def_field] at hs
    have hpos : 0 < a - x := sub_pos.mpr hxa
    apply (div_le_iff₀ hpos).mp at hs
    nlinarith
  · simp
  · have hs := convexOn_arccos_Icc_neg_one_zero.le_slope_of_hasDerivAt
        ha' hx hax hder
    rw [slope_def_field] at hs
    have hpos : 0 < x - a := sub_pos.mpr hax
    apply (le_div_iff₀ hpos).mp at hs
    nlinarith

/-- The arccosine of `-sqrt 2 / 2` is `3π/4`.

**Lean implementation helper.** -/
private lemma arccos_neg_sqrt_two_div_two :
    Real.arccos (-(√2 / 2)) = 3 * Real.pi / 4 := by
  apply Real.arccos_eq_of_eq_cos (by positivity) (by nlinarith [Real.pi_pos])
  rw [show 3 * Real.pi / 4 = Real.pi - Real.pi / 4 by ring,
    Real.cos_pi_sub, Real.cos_pi_div_four]

/-- The reciprocal square-root derivative factor at `-sqrt 2 / 2` equals `sqrt 2`.

**Lean implementation helper.** -/
private lemma inv_sqrt_one_sub_neg_sqrt_two_div_two_sq :
    1 / √(1 - (-(√2 / 2)) ^ 2) = √2 := by
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  have hs2 : (√2) ^ 2 = 2 := Real.sq_sqrt h2
  have hs2pos : 0 < √2 := Real.sqrt_pos.2 (by norm_num)
  rw [show 1 - (-(√2 / 2)) ^ 2 = (1 : ℝ) / 2 by nlinarith]
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1)]
  simp only [Real.sqrt_one]
  field_simp

/-- The square root of two exceeds the stated rational decimal lower bound.

**Lean implementation helper.** -/
private lemma sqrt_two_lower_decimal : (14142 : ℝ) / 10000 ≤ √2 := by
  exact Real.le_sqrt_of_sq_le (by norm_num)

/-- Bounds `gw_constant` above by `sqrt_two`.

**Lean implementation helper.** -/
private lemma gw_constant_le_sqrt_two :
    (439 / 1000 : ℝ) * Real.pi ≤ √2 := by
  have hp := Real.pi_lt_d6.le
  have hs := sqrt_two_lower_decimal
  calc
    (439 / 1000 : ℝ) * Real.pi ≤
        (439 / 1000 : ℝ) * 3.141593 :=
      mul_le_mul_of_nonneg_left hp (by norm_num)
    _ ≤ (14142 : ℝ) / 10000 := by norm_num
    _ ≤ √2 := hs

/-- The Goemans–Williamson comparison function has the displayed tangent line at `-2/3`.

**Lean implementation helper.** -/
private lemma gw_tangent_line_at_neg_two_thirds :
    (439 / 1000 : ℝ) * Real.pi * (1 - (-2 / 3 : ℝ)) ≤
      3 * Real.pi / 4 - √2 * ((-2 / 3 : ℝ) - (-(√2 / 2))) := by
  have hp := Real.pi_gt_d6.le
  have hs := sqrt_two_lower_decimal
  have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  norm_num at hp hs ⊢
  nlinarith [hs2]

/-- The Goemans–Williamson comparison function satisfies the stated numerical bound at `-2/3`.

**Lean implementation helper.** -/
private lemma gw_at_neg_two_thirds :
    (439 / 1000 : ℝ) * Real.pi * (1 - (-2 / 3 : ℝ)) ≤
      Real.arccos (-2 / 3 : ℝ) := by
  have ha : (-(√2 / 2) : ℝ) ∈ Ioo (-1 : ℝ) 0 := by
    have hs0 : 0 < √2 := Real.sqrt_pos.2 (by norm_num)
    have hslt : √2 < 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    constructor <;> nlinarith
  have hx : (-2 / 3 : ℝ) ∈ Icc (-1 : ℝ) 0 := by norm_num
  have ht := arccos_tangent_lower hx ha
  rw [arccos_neg_sqrt_two_div_two,
    inv_sqrt_one_sub_neg_sqrt_two_div_two_sq] at ht
  exact gw_tangent_line_at_neg_two_thirds.trans ht

/-- Bounds `inv_sqrt_at_neg_two_thirds` above by `gw_constant`.

**Lean implementation helper.** -/
private lemma inv_sqrt_at_neg_two_thirds_le_gw_constant :
    1 / √(1 - (-2 / 3 : ℝ) ^ 2) ≤
      (439 / 1000 : ℝ) * Real.pi := by
  have hq : 1 - (-2 / 3 : ℝ) ^ 2 = 5 / 9 := by norm_num
  have hqpos : 0 < (5 / 9 : ℝ) := by norm_num
  have hspos : 0 < √(5 / 9 : ℝ) := Real.sqrt_pos.2 hqpos
  have hs : (37 / 50 : ℝ) ≤ √(5 / 9 : ℝ) := by
    exact Real.le_sqrt_of_sq_le (by norm_num)
  have hd : 1 / √(5 / 9 : ℝ) ≤ (50 / 37 : ℝ) := by
    apply (div_le_iff₀ hspos).2
    nlinarith
  have hp := Real.pi_gt_d2.le
  rw [hq]
  calc
    1 / √(5 / 9 : ℝ) ≤ (50 / 37 : ℝ) := hd
    _ ≤ (439 / 1000 : ℝ) * (3.14 : ℝ) := by norm_num
    _ ≤ (439 / 1000 : ℝ) * Real.pi :=
      mul_le_mul_of_nonneg_left hp (by norm_num)

/-- The Goemans–Williamson arccosine inequality holds on the negative half interval.

**Lean implementation helper.** -/
private lemma gw_arccos_negative {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 0) :
    (439 / 1000 : ℝ) * Real.pi * (1 - x) ≤ Real.arccos x := by
  by_cases hcut : x ≤ (-2 / 3 : ℝ)
  · have ha : (-(√2 / 2) : ℝ) ∈ Ioo (-1 : ℝ) 0 := by
      have hs0 : 0 < √2 := Real.sqrt_pos.2 (by norm_num)
      have hslt : √2 < 2 := by
        nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      constructor <;> nlinarith
    have ht := arccos_tangent_lower hx ha
    rw [arccos_neg_sqrt_two_div_two,
      inv_sqrt_one_sub_neg_sqrt_two_div_two_sq] at ht
    have hb := gw_tangent_line_at_neg_two_thirds
    have hc := gw_constant_le_sqrt_two
    nlinarith
  · have hxlow : (-2 / 3 : ℝ) ≤ x := le_of_not_ge hcut
    have ha : (-2 / 3 : ℝ) ∈ Ioo (-1 : ℝ) 0 := by norm_num
    have ht := arccos_tangent_lower hx ha
    have hb := gw_at_neg_two_thirds
    have hd := inv_sqrt_at_neg_two_thirds_le_gw_constant
    nlinarith

/-- On the nonnegative half interval, arccosine lies above the chord used in the rounding estimate.

**Lean implementation helper.** -/
private lemma arccos_chord_nonnegative {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    Real.pi / 2 * (1 - x) ≤ Real.arccos x := by
  have hc := convexOn_arccos_Icc_neg_one_zero
  have hconv := hc.2
      (by norm_num : (-1 : ℝ) ∈ Icc (-1 : ℝ) 0)
      (by norm_num : (0 : ℝ) ∈ Icc (-1 : ℝ) 0)
      hx.1 (sub_nonneg.mpr hx.2) (by ring)
  simp only [smul_eq_mul, Real.arccos_neg_one, Real.arccos_zero] at hconv
  rw [show x * (-1 : ℝ) + (1 - x) * 0 = -x by ring,
    Real.arccos_neg] at hconv
  nlinarith

/-- The exact rational Goemans--Williamson analytic inequality.

The rational `439 / 500` is the source's decimal `0.878`. The statement is
source-neutral so it can be reused independently of graph and rounding APIs.

**Book Equation (3.35).** -/
theorem goemansWilliamsonArccos439_500 {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    (2 / Real.pi) * Real.arccos x ≥ (439 / 500 : ℝ) * (1 - x) := by
  have hp : 0 < Real.pi := Real.pi_pos
  have hraw : (439 / 500 : ℝ) * Real.pi * (1 - x) ≤ 2 * Real.arccos x := by
    rcases le_total x 0 with hxneg | hxpos
    · have h := gw_arccos_negative ⟨hx.1, hxneg⟩
      nlinarith
    · have hchord := arccos_chord_nonnegative ⟨hxpos, hx.2⟩
      have hcoef : (439 / 500 : ℝ) * Real.pi ≤ 1 * Real.pi :=
        mul_le_mul_of_nonneg_right (by norm_num) hp.le
      calc
        (439 / 500 : ℝ) * Real.pi * (1 - x) ≤
            1 * Real.pi * (1 - x) :=
          mul_le_mul_of_nonneg_right hcoef (sub_nonneg.mpr hx.2)
        _ ≤ 2 * Real.arccos x := by nlinarith
  have hdiv : (439 / 500 : ℝ) * (1 - x) ≤
      (2 * Real.arccos x) / Real.pi := by
    apply (le_div_iff₀ hp).2
    nlinarith
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv

namespace Chapter3

/-- The Gaussian sign--arcsine
(Grothendieck) identity for unit vectors. Chapter 3's rounding arguments use
this result, so this is its unique authoritative declaration.

**Book Lemma 3.6.5.** -/
theorem grothendieckSignArcsin
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    (∫ g : E, HDP.pmSign (inner ℝ u g) * HDP.pmSign (inner ℝ v g)
      ∂stdGaussian E) =
      (2 / Real.pi) * Real.arcsin (inner ℝ u v) :=
  HDP.stdGaussian_unit_sign_arcsin u v hu hv

/-- Equation (3.35), with the printed decimal `0.878` represented exactly as
`439 / 500`.

**Book Equation (3.35).** -/
theorem arccos_439_500 {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    (2 / Real.pi) * Real.arccos t ≥ (439 / 500 : ℝ) * (1 - t) :=
  goemansWilliamsonArccos439_500 ht

end Chapter3
end
end HDP

end Source_21_Grothendieck

/-! ## Material formerly in `18_MaxCut.lean` -/

section Source_18_MaxCut

/-!
# Maximum cut and SDP rounding

The graph-level cardinality definitions are shared in `Prelude.SimpleGraph`.
Here we record the matrix objectives and the order-preserving summation lemma
used by Goemans--Williamson rounding.
-/

open MeasureTheory ProbabilityTheory Real InnerProductSpace
open scoped BigOperators RealInnerProductSpace

namespace HDP

/-- Equation (3.31), written for a matrix and real labels.

**Book Equation (3.31).** -/
noncomputable def cutMatrixObjective {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ :=
  (1 / 4 : ℝ) * ∑ i, ∑ j, A i j * (1 - x i * x j)

/-- Equation (3.33), before maximization over unit-vector assignments.

**Book Equation (3.33).** -/
noncomputable def sdpCutObjective {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι ι ℝ) (X : ι → EuclideanSpace ℝ κ) : ℝ :=
  (1 / 4 : ℝ) * ∑ i, ∑ j, A i j * (1 - inner ℝ (X i) (X j))

end HDP

namespace HDP.Chapter3

/-- The plus-or-minus sign map `pmSign` is Borel measurable.

**Lean implementation helper.** -/
private lemma measurable_pmSign : Measurable HDP.pmSign := by
  unfold HDP.pmSign
  exact Measurable.ite measurableSet_Ici measurable_const measurable_const

/-- The Gaussian hyperplane-label `rounding_product` for two fixed vectors is integrable.

**Lean implementation helper.** -/
private lemma integrable_rounding_product
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (u v : E) :
    Integrable (fun g : E =>
      HDP.hyperplaneLabel g u * HDP.hyperplaneLabel g v) (stdGaussian E) := by
  refine Integrable.of_bound ?_ 1 ?_
  · have hmeas : Measurable (fun g : E =>
        HDP.hyperplaneLabel g u * HDP.hyperplaneLabel g v) := by
      unfold HDP.hyperplaneLabel
      apply Measurable.mul
      · exact measurable_pmSign.comp (by fun_prop)
      · exact measurable_pmSign.comp (by fun_prop)
    exact hmeas.aestronglyMeasurable
  · filter_upwards with g
    simp [HDP.hyperplaneLabel, Real.norm_eq_abs, HDP.abs_pmSign]

/-- The product `rademacher_product` of any two Rademacher variables is integrable.

**Lean implementation helper.** -/
private lemma integrable_rademacher_product
    {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {R : ι → Ω → ℝ} (hR : ∀ i, HDP.IsRademacher (R i) μ)
    (i j : ι) : Integrable (fun ω => R i ω * R j ω) μ := by
  refine Integrable.of_bound
    ((hR i).aemeasurable.mul (hR j).aemeasurable).aestronglyMeasurable 1 ?_
  filter_upwards [(hR i).ae_mem, (hR j).ae_mem] with ω hi hj
  rcases hi with hi | hi <;> rcases hj with hj | hj <;>
    simp [hi, hj]

/-- Distinct independent Rademacher variables have product expectation zero (`integral_rademacher_product_of_ne`).

**Lean implementation helper.** -/
private lemma integral_rademacher_product_of_ne
    {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {R : ι → Ω → ℝ} (hR : ∀ i, HDP.IsRademacher (R i) μ)
    (hindep : iIndepFun R μ) {i j : ι} (hij : i ≠ j) :
    (∫ ω, R i ω * R j ω ∂μ) = 0 := by
  have hp := (hindep.indepFun hij).integral_fun_mul_eq_mul_integral
    (hR i).aemeasurable.aestronglyMeasurable
    (hR j).aemeasurable.aestronglyMeasurable
  rw [hp, (hR i).integral_eq_zero, (hR j).integral_eq_zero, mul_zero]

/-- Every `±1` labeling embeds isometrically into the vector SDP, so the SDP
is indeed a relaxation of the integer cut problem.

**Book Theorem 3.6.4.** -/
theorem cut_embedding_preserves_objective
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι ι ℝ) (x : ι → ℝ)
    (e : EuclideanSpace ℝ κ) (he : ‖e‖ = 1) :
    HDP.sdpCutObjective A (fun i => x i • e) =
      HDP.cutMatrixObjective A x := by
  simp [HDP.sdpCutObjective, HDP.cutMatrixObjective,
    inner_smul_left, inner_smul_right, he, mul_comm]

/-- A pointwise correlation bound transfers to the full nonnegative weighted
cut objective. This is the linearity/order step in the proof of Theorem
3.6.4.

**Book Theorem 3.6.4.** -/
theorem cut_objective_lower_bound_of_pairwise
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι ι ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (X : ι → EuclideanSpace ℝ κ) (corr : ι → ι → ℝ)
    (α : ℝ)
    (hpair : ∀ i j,
      α * (1 - inner ℝ (X i) (X j)) ≤ 1 - corr i j) :
    α * HDP.sdpCutObjective A X ≤
      (1 / 4 : ℝ) * ∑ i, ∑ j, A i j * (1 - corr i j) := by
  unfold HDP.sdpCutObjective
  have hsum :
      ∑ i, ∑ j, A i j * (α * (1 - inner ℝ (X i) (X j))) ≤
        ∑ i, ∑ j, A i j * (1 - corr i j) := by
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    exact mul_le_mul_of_nonneg_left (hpair i j) (hA i j)
  calc
    α * ((1 / 4 : ℝ) * ∑ i, ∑ j,
        A i j * (1 - inner ℝ (X i) (X j))) =
        (1 / 4 : ℝ) * ∑ i, ∑ j,
          A i j * (α * (1 - inner ℝ (X i) (X j))) := by
      simp_rw [Finset.mul_sum]
      ring_nf
    _ ≤ (1 / 4 : ℝ) * ∑ i, ∑ j, A i j * (1 - corr i j) := by
      exact mul_le_mul_of_nonneg_left hsum (by norm_num)

/-- The exact rational constant used in the formalized `0.878` guarantee.

**Book Equation (3.35).** -/
theorem goemansWilliamson_pairwise_bound {t : ℝ}
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    (439 / 500 : ℝ) * (1 - t) ≤
      (2 / Real.pi) * Real.arccos t := by
  exact HDP.goemansWilliamsonArccos439_500 ht

/-- Independent
Rademacher vertex labels give the actual expected cut value
`(1/4) * ∑ i,j, A i j` for a loop-free weight matrix.

**Book Proposition 3.6.3.** -/
theorem randomCut_expected_objective
    {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] [Fintype ι]
    (A : Matrix ι ι ℝ) (hdiag : ∀ i, A i i = 0)
    (R : ι → Ω → ℝ) (hR : ∀ i, HDP.IsRademacher (R i) μ)
    (hindep : iIndepFun R μ) :
    (∫ ω, HDP.cutMatrixObjective A (fun i => R i ω) ∂μ) =
      (1 / 4 : ℝ) * ∑ i, ∑ j, A i j := by
  classical
  unfold HDP.cutMatrixObjective
  rw [integral_const_mul]
  apply congrArg (fun z : ℝ => (1 / 4 : ℝ) * z)
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j hj
      rw [integral_const_mul,
        integral_sub (integrable_const 1) (integrable_rademacher_product hR i j)]
      by_cases hij : i = j
      · subst j
        rw [show (∫ ω, R i ω * R i ω ∂μ) = 1 by
          simpa using (hR i).integral_comp (fun z => z * z)]
        simp [hdiag]
      · rw [integral_rademacher_product_of_ne hR hindep hij]
        simp
    · intro j hj
      exact ((integrable_const 1).sub
        (integrable_rademacher_product hR i j)).const_mul (A i j)
  · intro i hi
    exact integrable_finsetSum _ fun j hj =>
      ((integrable_const 1).sub
        (integrable_rademacher_product hR i j)).const_mul (A i j)

/-- The expected random cut
is at least one half of every deterministic cut, hence in particular one half
of a maximizing cut.

**Book Proposition 3.6.3.** -/
theorem randomCut_halfApproximation
    {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] [Fintype ι]
    (A : Matrix ι ι ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hdiag : ∀ i, A i i = 0)
    (R : ι → Ω → ℝ) (hR : ∀ i, HDP.IsRademacher (R i) μ)
    (hindep : iIndepFun R μ)
    (x : ι → ℝ) (hx : ∀ i, x i = 1 ∨ x i = -1) :
    (1 / 2 : ℝ) * HDP.cutMatrixObjective A x ≤
      ∫ ω, HDP.cutMatrixObjective A (fun i => R i ω) ∂μ := by
  classical
  rw [randomCut_expected_objective A hdiag R hR hindep]
  unfold HDP.cutMatrixObjective
  have hpair : ∀ i j, 1 - x i * x j ≤ 2 := by
    intro i j
    rcases hx i with hi | hi <;> rcases hx j with hj | hj <;>
      norm_num [hi, hj]
  have hsum : ∑ i, ∑ j, A i j * (1 - x i * x j) ≤
      2 * ∑ i, ∑ j, A i j := by
    calc
      ∑ i, ∑ j, A i j * (1 - x i * x j) ≤
          ∑ i, ∑ j, A i j * 2 := by
            apply Finset.sum_le_sum
            intro i hi
            apply Finset.sum_le_sum
            intro j hj
            exact mul_le_mul_of_nonneg_left (hpair i j) (hA i j)
      _ = 2 * ∑ i, ∑ j, A i j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [mul_comm, Finset.sum_mul]
  nlinarith

/-- The expected cut objective after Gaussian hyperplane rounding. This is
the integral form of the Grothendieck sign--arcsine identity, summed over all
weighted pairs.

**Book Theorem 3.6.4.** -/
theorem gaussian_rounding_expected_objective
    {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (A : Matrix ι ι ℝ) (X : ι → E) (hX : ∀ i, ‖X i‖ = 1) :
    (∫ g : E, HDP.cutMatrixObjective A
        (fun i => HDP.hyperplaneLabel g (X i)) ∂stdGaussian E) =
      (1 / 4 : ℝ) * ∑ i, ∑ j, A i j *
        (1 - (2 / Real.pi) * Real.arcsin (inner ℝ (X i) (X j))) := by
  unfold HDP.cutMatrixObjective
  rw [integral_const_mul]
  apply congrArg (fun z : ℝ => (1 / 4 : ℝ) * z)
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j hj
      rw [integral_const_mul]
      rw [integral_sub (integrable_const 1) (integrable_rounding_product (X i) (X j))]
      rw [show (∫ a : E,
          HDP.hyperplaneLabel a (X i) * HDP.hyperplaneLabel a (X j)
            ∂stdGaussian E) =
          (2 / Real.pi) * Real.arcsin (inner ℝ (X i) (X j)) by
        simpa [HDP.hyperplaneLabel] using
          (HDP.Chapter3.grothendieckSignArcsin
            (X i) (X j) (hX i) (hX j))]
      simp
    · intro j hj
      exact ((integrable_const 1).sub
        (integrable_rounding_product (X i) (X j))).const_mul (A i j)
  · intro i hi
    exact integrable_finsetSum _ fun j hj =>
      ((integrable_const 1).sub
        (integrable_rounding_product (X i) (X j))).const_mul (A i j)

/-- For nonnegative edge weights, Gaussian hyperplane rounding retains at least
the exact rational factor `439 / 500` of every feasible vector-SDP objective.
The conclusion is an actual expectation with respect to the standard
Gaussian measure, rather than an abstract correlation surrogate.

**Book Theorem 3.6.4.** -/
theorem goemans_williamson_expected_guarantee
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι ι ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (X : ι → EuclideanSpace ℝ κ) (hX : ∀ i, ‖X i‖ = 1) :
    (439 / 500 : ℝ) * HDP.sdpCutObjective A X ≤
      ∫ g : EuclideanSpace ℝ κ, HDP.cutMatrixObjective A
        (fun i => HDP.hyperplaneLabel g (X i))
          ∂stdGaussian (EuclideanSpace ℝ κ) := by
  rw [gaussian_rounding_expected_objective A X hX]
  apply cut_objective_lower_bound_of_pairwise A hA X
      (fun i j => (2 / Real.pi) * Real.arcsin (inner ℝ (X i) (X j)))
      (439 / 500)
  · intro i j
    have hij : inner ℝ (X i) (X j) ∈ Set.Icc (-1 : ℝ) 1 := by
      constructor
      · have h := abs_real_inner_le_norm (X i) (X j)
        rw [hX i, hX j, one_mul] at h
        exact neg_le_of_abs_le h
      · have h := abs_real_inner_le_norm (X i) (X j)
        rw [hX i, hX j, one_mul] at h
        exact le_of_abs_le h
    have hp : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    have hb := goemansWilliamson_pairwise_bound hij
    calc
      (439 / 500 : ℝ) * (1 - inner ℝ (X i) (X j)) ≤
          (2 / Real.pi) * Real.arccos (inner ℝ (X i) (X j)) := hb
      _ = 1 - (2 / Real.pi) * Real.arcsin (inner ℝ (X i) (X j)) := by
        rw [Real.arccos_eq_pi_div_two_sub_arcsin]
        field_simp

end HDP.Chapter3

end Source_18_MaxCut

/-! ## Material formerly in `22_TensorFeatures.lean` -/

section Source_22_TensorFeatures

/-!
# Tensor and polynomial feature maps

This source-neutral helper layer contains the finite tensor construction used
in Book Sections 3.5--3.7.  Keeping it independent of Gaussian rounding avoids
the circular dependency that results if the Grothendieck proof defines tensor
powers locally.
-/

open scoped BigOperators RealInnerProductSpace

namespace HDP

variable {ι : Type*} [Fintype ι]

/-- The Hilbert space of real order-`k` tensors whose `r`th coordinate axis
has index type `axis r`. Thus an element is the multidimensional array
`(a_{i₁...iₖ})` with independently sized finite axes.

**Book Definition 3.7.1.** -/
abbrev TensorSpace {k : ℕ} (axis : Fin k → Type*)
    [∀ r, Fintype (axis r)] :=
  EuclideanSpace ℝ (∀ r, axis r)

/-- The canonical tensor inner product, written as the sum of entrywise
products over every multi-index.

**Book Equation (3.36).** -/
noncomputable def tensorInner {k : ℕ} {axis : Fin k → Type*}
    [∀ r, Fintype (axis r)]
    (A B : TensorSpace axis) : ℝ :=
  ∑ p, A p * B p

/-- The coordinate formula (3.36) is exactly the ambient Euclidean inner
product on the general product-axis tensor space.

**Book Definition 3.7.1; Equation (3.36).** -/
theorem tensorInner_eq_inner {k : ℕ} {axis : Fin k → Type*}
    [∀ r, Fintype (axis r)]
    (A B : TensorSpace axis) :
    tensorInner A B = inner ℝ A B := by
  simp [tensorInner, PiLp.inner_apply, mul_comm]

/-- The concrete finite-dimensional Hilbert space containing `k`-fold pure
tensors over `EuclideanSpace ℝ ι`. -/
abbrev TensorPowerSpace (ι : Type*) [Fintype ι] (k : ℕ) :=
  EuclideanSpace ℝ (Fin k → ι)

/-- The equal-axis tensor-power space used below is the specialization of
Definition 3.7.1 in which all `k` axes have the same index type.

**Book Definition 3.7.1; Example 3.7.3.** -/
theorem tensorPowerSpace_eq_tensorSpace (k : ℕ) :
    TensorPowerSpace ι k = TensorSpace (fun _ : Fin k ↦ ι) := rfl

/-- The `k`-fold pure tensor `u^{⊗k}`, in coordinates.

**Book Example 3.7.3.** -/
noncomputable def tensorPowerFeature
    (k : ℕ) (u : EuclideanSpace ℝ ι) : TensorPowerSpace ι k :=
  WithLp.toLp 2 (fun p => ∏ r, u (p r))

/-- Inner products of pure tensor powers are powers of inner products.

**Book Lemma 3.7.4.** -/
theorem inner_tensorPowerFeature
    (k : ℕ) (u v : EuclideanSpace ℝ ι) :
    inner ℝ (tensorPowerFeature k u) (tensorPowerFeature k v) =
      (inner ℝ u v) ^ k := by
  simp only [tensorPowerFeature, PiLp.inner_apply, Real.inner_apply]
  rw [Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← Finset.prod_mul_distrib]

/-- A nonnegative scalar coefficient can be absorbed into a tensor feature.

**Lean implementation helper.** -/
noncomputable def scaledTensorPowerFeature
    (a : ℝ) (k : ℕ) (u : EuclideanSpace ℝ ι) : TensorPowerSpace ι k :=
  Real.sqrt a • tensorPowerFeature k u

/-- A polynomial with nonnegative coefficients has a Hilbert feature map.

**Book Example 3.7.5.** -/
theorem inner_scaledTensorPowerFeature {a : ℝ} (ha : 0 ≤ a)
    (k : ℕ) (u v : EuclideanSpace ℝ ι) :
    inner ℝ (scaledTensorPowerFeature a k u)
        (scaledTensorPowerFeature a k v) =
      a * (inner ℝ u v) ^ k := by
  simp only [scaledTensorPowerFeature]
  rw [inner_smul_left, inner_smul_right,
    inner_tensorPowerFeature, RCLike.conj_to_real]
  rw [← mul_assoc, Real.mul_self_sqrt ha]

end HDP

namespace HDP.Chapter3

/-- The inner product of tensor-power feature maps is the corresponding power of the original inner product.

**Book Section 3.7.** -/
theorem tensor_feature_identity {ι : Type*} [Fintype ι]
    (k : ℕ) (u v : EuclideanSpace ℝ ι) :
    inner ℝ (HDP.tensorPowerFeature k u) (HDP.tensorPowerFeature k v) =
      (inner ℝ u v) ^ k :=
  HDP.inner_tensorPowerFeature k u v

end HDP.Chapter3

end Source_22_TensorFeatures

/-! ## Material formerly in `23_AnalyticFeatures.lean` -/

section Source_23_AnalyticFeatures

/-!
# Infinite analytic feature maps

This module completes the finite tensor construction from `22_TensorFeatures.lean` in
the genuine Hilbert sum of all tensor degrees.  It provides both the
nonnegative-coefficient kernel map and the signed pair used by Krivine's
argument.
-/

open scoped BigOperators RealInnerProductSpace lp ENNReal

namespace HDP

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- Coefficients whose absolute power series converges at every real radius.

**Book Lemma 3.7.7.** -/
def AbsolutePowerSummable (a : ℕ → ℝ) : Prop :=
  ∀ r : ℝ, Summable (fun k : ℕ ↦ |a k| * |r| ^ k)

/-- A real power series that converges at every real input is absolutely
convergent at every radius. This supplies the analytic bridge implicit in the
source's hypothesis for Lemma 3.7.7.

**Book Lemma 3.7.7.** -/
theorem absolutePowerSummable_of_entire (a : ℕ → ℝ)
    (h : ∀ x : ℝ, Summable (fun k : ℕ ↦ a k * x ^ k)) :
    AbsolutePowerSummable a := by
  intro r
  by_cases hr : r = 0
  · subst r
    refine summable_of_hasFiniteSupport ((Set.finite_singleton 0).subset ?_)
    intro k hk
    simp only [Set.mem_singleton_iff]
    by_contra hk0
    apply hk
    simp [hk0]
  · have hR := h (2 * |r|)
    have ht : Filter.Tendsto (fun k : ℕ ↦ a k * (2 * |r|) ^ k)
        Filter.atTop (nhds 0) := hR.tendsto_atTop_zero
    have hev : ∀ᶠ k : ℕ in Filter.atTop,
        |a k * (2 * |r|) ^ k| ≤ 1 := by
      have hlt : ∀ᶠ k : ℕ in Filter.atTop,
          |a k * (2 * |r|) ^ k| < 1 := by
        have he := ht.eventually
          (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1))
        filter_upwards [he] with k hk
        simpa [Metric.mem_ball, Real.dist_eq] using hk
      exact hlt.mono fun _ hk ↦ hk.le
    refine Summable.of_norm_bounded_eventually_nat
      (f := fun k : ℕ ↦ |a k| * |r| ^ k)
      (g := fun k : ℕ ↦ (1 / 2 : ℝ) ^ k)
      (summable_geometric_of_norm_lt_one (by norm_num)) ?_
    filter_upwards [hev] with k hk
    rw [Real.norm_of_nonneg
      (mul_nonneg (abs_nonneg _) (pow_nonneg (abs_nonneg _) _))]
    rw [one_div, inv_pow, inv_eq_one_div]
    apply (le_div_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) k)).2
    have hid :
        |a k| * |r| ^ k * 2 ^ k =
          |a k * (2 * |r|) ^ k| := by
      rw [abs_mul, abs_pow,
        abs_of_nonneg (mul_nonneg (by norm_num) (abs_nonneg r)), mul_pow]
      ring
    rw [hid]
    exact hk

/-- The Hilbert sum of every finite tensor power. -/
abbrev AnalyticFeatureSpace (ι : Type*) [Fintype ι] :=
  lp (fun k : ℕ ↦ TensorPowerSpace ι k) 2

/-- `norm_scaledTensorPowerFeature_sq` gives `‖scaledTensorPowerFeature a k u‖² = a * (‖u‖²)^k` for `a ≥ 0`.

**Lean implementation helper.** -/
private lemma norm_scaledTensorPowerFeature_sq (a : ℝ) (ha : 0 ≤ a)
    (k : ℕ) (u : EuclideanSpace ℝ ι) :
    ‖scaledTensorPowerFeature a k u‖ ^ 2 =
      a * (‖u‖ ^ 2) ^ k := by
  rw [← real_inner_self_eq_norm_sq,
    inner_scaledTensorPowerFeature ha, real_inner_self_eq_norm_sq]

/-- The scaled tensor-power feature blocks form a summable sequence.

**Lean implementation helper.** -/
private lemma summable_scaledTensorPowerFeature (a : ℕ → ℝ)
    (ha : AbsolutePowerSummable a) (u : EuclideanSpace ℝ ι) :
    Summable (fun k : ℕ ↦ ‖scaledTensorPowerFeature |a k| k u‖ ^
      (2 : ℝ≥0∞).toReal) := by
  have h := ha (‖u‖ ^ 2)
  rw [abs_of_nonneg (sq_nonneg ‖u‖)] at h
  convert h using 1
  ext k
  norm_num
  exact norm_scaledTensorPowerFeature_sq |a k| (abs_nonneg _) k u

/-- The positive square-root feature associated with an absolutely convergent
real power series.

**Lean implementation helper.** -/
def analyticFeature (a : ℕ → ℝ) (ha : AbsolutePowerSummable a)
    (u : EuclideanSpace ℝ ι) : AnalyticFeatureSpace ι :=
  ⟨fun k ↦ scaledTensorPowerFeature |a k| k u,
    memℓp_gen (summable_scaledTensorPowerFeature a ha u)⟩

/-- `norm_sign_smul_scaled_sq` gives the squared norm of the signed tensor block as `|a| * (‖u‖²)^k`.

**Lean implementation helper.** -/
private lemma norm_sign_smul_scaled_sq (a : ℝ) (k : ℕ)
    (u : EuclideanSpace ℝ ι) :
    ‖(SignType.sign a : ℝ) • scaledTensorPowerFeature |a| k u‖ ^ 2 =
      |a| * (‖u‖ ^ 2) ^ k := by
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · rw [sign_neg ha]
    norm_num
    exact norm_scaledTensorPowerFeature_sq |a| (abs_nonneg _) k u
  · simp
  · rw [sign_pos ha]
    norm_num
    exact norm_scaledTensorPowerFeature_sq |a| (abs_nonneg _) k u

/-- The signed scaled tensor-power feature blocks form a summable sequence.

**Lean implementation helper.** -/
private lemma summable_signedScaledTensorPowerFeature (a : ℕ → ℝ)
    (ha : AbsolutePowerSummable a) (u : EuclideanSpace ℝ ι) :
    Summable (fun k : ℕ ↦
      ‖(SignType.sign (a k) : ℝ) • scaledTensorPowerFeature |a k| k u‖ ^
        (2 : ℝ≥0∞).toReal) := by
  have h := ha (‖u‖ ^ 2)
  rw [abs_of_nonneg (sq_nonneg ‖u‖)] at h
  convert h using 1
  ext k
  norm_num
  exact norm_sign_smul_scaled_sq (a k) k u

/-- The signed companion feature; its `k`th block carries the sign of `a k`.

**Lean implementation helper.** -/
def signedAnalyticFeature (a : ℕ → ℝ) (ha : AbsolutePowerSummable a)
    (u : EuclideanSpace ℝ ι) : AnalyticFeatureSpace ι :=
  ⟨fun k ↦ (SignType.sign (a k) : ℝ) • scaledTensorPowerFeature |a k| k u,
    memℓp_gen (summable_signedScaledTensorPowerFeature a ha u)⟩

/-- The two infinite feature maps realize the signed power-series kernel.

**Book Example 3.7.6.** -/
theorem inner_analyticFeature_signedAnalyticFeature
    (a : ℕ → ℝ) (ha : AbsolutePowerSummable a)
    (u v : EuclideanSpace ℝ ι) :
    inner ℝ (analyticFeature a ha u) (signedAnalyticFeature a ha v) =
      ∑' k : ℕ, a k * (inner ℝ u v) ^ k := by
  rw [lp.inner_eq_tsum]
  apply tsum_congr
  intro k
  change inner ℝ (scaledTensorPowerFeature |a k| k u)
      ((SignType.sign (a k) : ℝ) • scaledTensorPowerFeature |a k| k v) = _
  rw [inner_smul_right, inner_scaledTensorPowerFeature (abs_nonneg _)]
  rw [← mul_assoc, sign_mul_abs]

/-- For nonnegative coefficients one feature map realizes the positive kernel.

**Book Example 3.7.5.** -/
theorem inner_analyticFeature_of_nonneg
    (a : ℕ → ℝ) (ha : AbsolutePowerSummable a) (ha0 : ∀ k, 0 ≤ a k)
    (u v : EuclideanSpace ℝ ι) :
    inner ℝ (analyticFeature a ha u) (analyticFeature a ha v) =
      ∑' k : ℕ, a k * (inner ℝ u v) ^ k := by
  rw [lp.inner_eq_tsum]
  apply tsum_congr
  intro k
  change inner ℝ (scaledTensorPowerFeature |a k| k u)
      (scaledTensorPowerFeature |a k| k v) = _
  rw [inner_scaledTensorPowerFeature (abs_nonneg _), abs_of_nonneg (ha0 k)]

/-- `norm_sq_analyticFeature` expands `‖analyticFeature a ha u‖²` as `∑' k, |a k| * (‖u‖²)^k`.

**Lean implementation helper.** -/
private lemma norm_sq_analyticFeature (a : ℕ → ℝ)
    (ha : AbsolutePowerSummable a) (u : EuclideanSpace ℝ ι) :
    ‖analyticFeature a ha u‖ ^ 2 =
      ∑' k : ℕ, |a k| * (‖u‖ ^ 2) ^ k := by
  have h := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num)
      (analyticFeature a ha u)
  norm_num at h
  rw [h]
  apply tsum_congr
  intro k
  exact norm_scaledTensorPowerFeature_sq |a k| (abs_nonneg _) k u

/-- `norm_sq_signedAnalyticFeature` expands the signed feature's squared norm as `∑' k, |a k| * (‖u‖²)^k`.

**Lean implementation helper.** -/
private lemma norm_sq_signedAnalyticFeature (a : ℕ → ℝ)
    (ha : AbsolutePowerSummable a) (u : EuclideanSpace ℝ ι) :
    ‖signedAnalyticFeature a ha u‖ ^ 2 =
      ∑' k : ℕ, |a k| * (‖u‖ ^ 2) ^ k := by
  have h := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num)
      (signedAnalyticFeature a ha u)
  norm_num at h
  rw [h]
  apply tsum_congr
  intro k
  exact norm_sign_smul_scaled_sq (a k) k u

/-- On unit vectors the squared norm is exactly the absolute coefficient sum.

**Lean implementation helper.** -/
theorem norm_sq_analyticFeature_of_unit (a : ℕ → ℝ)
    (ha : AbsolutePowerSummable a) (u : EuclideanSpace ℝ ι) (hu : ‖u‖ = 1) :
    ‖analyticFeature a ha u‖ ^ 2 = ∑' k : ℕ, |a k| := by
  rw [norm_sq_analyticFeature, hu]
  simp

/-- The signed companion has the same unit-vector norm.

**Lean implementation helper.** -/
theorem norm_sq_signedAnalyticFeature_of_unit (a : ℕ → ℝ)
    (ha : AbsolutePowerSummable a) (u : EuclideanSpace ℝ ι) (hu : ‖u‖ = 1) :
    ‖signedAnalyticFeature a ha u‖ ^ 2 = ∑' k : ℕ, |a k| := by
  rw [norm_sq_signedAnalyticFeature, hu]
  simp

end
end HDP

namespace HDP.Chapter3

/-- **Lemma 3.7.7 / Exercise 3.55.** The explicit ℓ² feature maps realize
the power series with coefficients `a`.

**Book Lemma 3.7.7.** -/
theorem realAnalytic_featureMap {ι : Type*} [Fintype ι]
    (a : ℕ → ℝ) (ha : HDP.AbsolutePowerSummable a)
    (u v : EuclideanSpace ℝ ι) :
    inner ℝ (HDP.analyticFeature a ha u) (HDP.signedAnalyticFeature a ha v) =
      ∑' k : ℕ, a k * (inner ℝ u v) ^ k :=
  HDP.inner_analyticFeature_signedAnalyticFeature a ha u v

/-- The feature-map conclusion of Lemma 3.7.7 under the source's literal
hypothesis that the real power series converges at every real input.

**Book Lemma 3.7.7.** -/
theorem realAnalytic_featureMap_of_entire {ι : Type*} [Fintype ι]
    (a : ℕ → ℝ)
    (h : ∀ x : ℝ, Summable (fun k : ℕ ↦ a k * x ^ k))
    (u v : EuclideanSpace ℝ ι) :
    let ha := HDP.absolutePowerSummable_of_entire a h
    inner ℝ (HDP.analyticFeature a ha u)
        (HDP.signedAnalyticFeature a ha v) =
      ∑' k : ℕ, a k * (inner ℝ u v) ^ k := by
  dsimp only
  exact HDP.inner_analyticFeature_signedAnalyticFeature
    a (HDP.absolutePowerSummable_of_entire a h) u v

/-- The two feature maps in Lemma 3.7.7 have the source's exact squared norm
on unit vectors.

**Book Lemma 3.7.7.** -/
theorem realAnalytic_featureMap_norm {ι : Type*} [Fintype ι]
    (a : ℕ → ℝ) (ha : HDP.AbsolutePowerSummable a)
    (u : EuclideanSpace ℝ ι) (hu : ‖u‖ = 1) :
    ‖HDP.analyticFeature a ha u‖ ^ 2 = ∑' k : ℕ, |a k| ∧
      ‖HDP.signedAnalyticFeature a ha u‖ ^ 2 = ∑' k : ℕ, |a k| :=
  ⟨HDP.norm_sq_analyticFeature_of_unit a ha u hu,
    HDP.norm_sq_signedAnalyticFeature_of_unit a ha u hu⟩

end HDP.Chapter3

end Source_23_AnalyticFeatures

/-! ## Material formerly in `24_Krivine.lean` -/

section Source_24_Krivine

/-!
# Sine features and Krivine's constant

This module specializes the infinite tensor construction to the sine series,
proves the corrected normalization `sinh c = 1`, and certifies the exact
rational upper bound `1783 / 1000` for Krivine's constant.
-/

open scoped BigOperators RealInnerProductSpace lp ENNReal
open Real

namespace HDP

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- Hilbert sum of the odd tensor powers used for the sine feature map. -/
abbrev SineFeatureSpace (ι : Type*) [Fintype ι] :=
  lp (fun n : ℕ ↦ TensorPowerSpace ι (2 * n + 1)) 2

/-- Absolute coefficient of the `n`th odd term of `sin (c x)`.

**Lean implementation helper.** -/
def sineMagnitude (c : ℝ) (n : ℕ) : ℝ :=
  c ^ (2 * n + 1) / (2 * n + 1).factorial

/-- Shows that `sineMagnitude` is nonnegative.

**Lean implementation helper.** -/
private lemma sineMagnitude_nonneg {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    0 ≤ sineMagnitude c n := by
  exact div_nonneg (pow_nonneg hc _) (Nat.cast_nonneg _)

/-- `norm_sine_block_sq` gives the squared norm of the `n`th sine tensor block as `sineMagnitude c n * (‖u‖²)^(2n+1)`.

**Lean implementation helper.** -/
private lemma norm_sine_block_sq {c : ℝ} (hc : 0 ≤ c) (n : ℕ)
    (u : EuclideanSpace ℝ ι) :
    ‖scaledTensorPowerFeature (sineMagnitude c n) (2 * n + 1) u‖ ^ 2 =
      sineMagnitude c n * (‖u‖ ^ 2) ^ (2 * n + 1) := by
  rw [← real_inner_self_eq_norm_sq,
    inner_scaledTensorPowerFeature (sineMagnitude_nonneg hc n),
    real_inner_self_eq_norm_sq]

/-- The feature blocks in the sine-series construction are summable.

**Lean implementation helper.** -/
private lemma summable_sine_blocks {c : ℝ} (hc : 0 ≤ c)
    (u : EuclideanSpace ℝ ι) :
    Summable (fun n : ℕ ↦
      ‖scaledTensorPowerFeature (sineMagnitude c n) (2 * n + 1) u‖ ^
        (2 : ℝ≥0∞).toReal) := by
  have hs := (Real.hasSum_sinh (c * ‖u‖ ^ 2)).summable
  convert hs using 1
  ext n
  norm_num
  rw [norm_sine_block_sq hc, sineMagnitude, mul_pow]
  ring

/-- Positive odd-tensor feature map for the sine series.

**Book Example 3.7.8.** -/
def sineFeature (c : ℝ) (hc : 0 ≤ c) (u : EuclideanSpace ℝ ι) :
    SineFeatureSpace ι :=
  ⟨fun n ↦ scaledTensorPowerFeature (sineMagnitude c n) (2 * n + 1) u,
    memℓp_gen (summable_sine_blocks hc u)⟩

/-- The signed feature blocks in the sine-series construction are summable.

**Lean implementation helper.** -/
private lemma summable_signed_sine_blocks {c : ℝ} (hc : 0 ≤ c)
    (u : EuclideanSpace ℝ ι) :
    Summable (fun n : ℕ ↦
      ‖((-1 : ℝ) ^ n) •
        scaledTensorPowerFeature (sineMagnitude c n) (2 * n + 1) u‖ ^
          (2 : ℝ≥0∞).toReal) := by
  convert summable_sine_blocks hc u using 1
  ext n
  rw [norm_smul, Real.norm_eq_abs, abs_pow, abs_neg, abs_one, one_pow, one_mul]

/-- Alternating-sign companion feature map for the sine series.

**Book Example 3.7.8.** -/
def signedSineFeature (c : ℝ) (hc : 0 ≤ c) (u : EuclideanSpace ℝ ι) :
    SineFeatureSpace ι :=
  ⟨fun n ↦ ((-1 : ℝ) ^ n) •
      scaledTensorPowerFeature (sineMagnitude c n) (2 * n + 1) u,
    memℓp_gen (summable_signed_sine_blocks hc u)⟩

/-- Infinite tensor realization of the kernel `sin (c ⟪u,v⟫)`.

**Book Example 3.7.8.** -/
theorem inner_sineFeature_signedSineFeature {c : ℝ} (hc : 0 ≤ c)
    (u v : EuclideanSpace ℝ ι) :
    inner ℝ (sineFeature c hc u) (signedSineFeature c hc v) =
      Real.sin (c * inner ℝ u v) := by
  rw [lp.inner_eq_tsum]
  rw [← (Real.hasSum_sin (c * inner ℝ u v)).tsum_eq]
  apply tsum_congr
  intro n
  change inner ℝ
    (scaledTensorPowerFeature (sineMagnitude c n) (2 * n + 1) u)
    (((-1 : ℝ) ^ n) •
      scaledTensorPowerFeature (sineMagnitude c n) (2 * n + 1) v) = _
  rw [inner_smul_right,
    inner_scaledTensorPowerFeature (sineMagnitude_nonneg hc n)]
  simp only [sineMagnitude, mul_pow]
  ring

/-- `norm_sq_sineFeature` expands the sine feature's squared norm as the sum of its `sineMagnitude`-weighted odd tensor powers.

**Lean implementation helper.** -/
private lemma norm_sq_sineFeature {c : ℝ} (hc : 0 ≤ c)
    (u : EuclideanSpace ℝ ι) :
    ‖sineFeature c hc u‖ ^ 2 =
      ∑' n : ℕ, sineMagnitude c n * (‖u‖ ^ 2) ^ (2 * n + 1) := by
  have h := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num)
    (sineFeature c hc u)
  norm_num at h
  rw [h]
  apply tsum_congr
  intro n
  exact norm_sine_block_sq hc n u

/-- `norm_sq_signedSineFeature` expands the signed sine feature's squared norm as the same `sineMagnitude`-weighted odd-power series.

**Lean implementation helper.** -/
private lemma norm_sq_signedSineFeature {c : ℝ} (hc : 0 ≤ c)
    (u : EuclideanSpace ℝ ι) :
    ‖signedSineFeature c hc u‖ ^ 2 =
      ∑' n : ℕ, sineMagnitude c n * (‖u‖ ^ 2) ^ (2 * n + 1) := by
  have h := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num)
    (signedSineFeature c hc u)
  norm_num at h
  rw [h]
  apply tsum_congr
  intro n
  change ‖((-1 : ℝ) ^ n) •
      scaledTensorPowerFeature (sineMagnitude c n) (2 * n + 1) u‖ ^ 2 = _
  rw [norm_smul, Real.norm_eq_abs, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  exact norm_sine_block_sq hc n u

/-- The unit-vector squared norm of each sine feature is `sinh c`.

**Lean implementation helper.** -/
theorem norm_sq_sineFeatures_of_unit {c : ℝ} (hc : 0 ≤ c)
    (u : EuclideanSpace ℝ ι) (hu : ‖u‖ = 1) :
    ‖sineFeature c hc u‖ ^ 2 = Real.sinh c ∧
      ‖signedSineFeature c hc u‖ ^ 2 = Real.sinh c := by
  constructor
  · rw [norm_sq_sineFeature, hu]
    simpa [sineMagnitude] using (Real.hasSum_sinh c).tsum_eq
  · rw [norm_sq_signedSineFeature, hu]
    simpa [sineMagnitude] using (Real.hasSum_sinh c).tsum_eq

/-- Krivine's normalization parameter.

**Lean implementation helper.** -/
def krivineC : ℝ := Real.log (1 + √2)

/-- The explicit Krivine constant used in Theorem 3.5.1.

**Book Theorem 3.5.1.** -/
def krivineConstant : ℝ := Real.pi / (2 * krivineC)

/-- The Krivine constant is equal to the explicit reciprocal arcsine expression.

**Lean implementation helper.** -/
theorem krivineConstant_eq :
    krivineConstant = Real.pi / (2 * Real.log (1 + √2)) := rfl

/-- Shows that `krivineC` is positive.

**Lean implementation helper.** -/
theorem krivineC_pos : 0 < krivineC := by
  apply Real.log_pos
  linarith [Real.one_lt_sqrt_two]

/-- Corrected Example 3.7.8: the absolute coefficient sum is `sinh c`, not
`cosh c`, and Krivine's parameter makes it exactly one.

**Book Example 3.7.8.** -/
theorem sinh_krivineC : Real.sinh krivineC = 1 := by
  have hx : 0 < 1 + √2 := by positivity
  have hinv : (1 + √2)⁻¹ = √2 - 1 := by
    apply (inv_eq_iff_eq_inv).2
    simpa [add_comm] using Real.inv_sqrt_two_sub_one.symm
  rw [krivineC, Real.sinh_log hx, hinv]
  ring

/-- The rational approximation used for `sqrt 2` gives the stated lower ratio bound.

**Lean implementation helper.** -/
private lemma sqrt_two_ratio_lower :
    (2071 / 5000 : ℝ) ≤ √2 / (√2 + 2) := by
  have hs : (7071 / 5000 : ℝ) ≤ √2 :=
    Real.le_sqrt_of_sq_le (by norm_num)
  have hd : 0 < √2 + 2 := by positivity
  rw [le_div_iff₀ hd]
  nlinarith

/-- The explicit Krivine constant exceeds the stated rational lower bound.

**Lean implementation helper.** -/
private lemma krivineC_explicit_lower :
    (3.1416 : ℝ) / (2 * (1783 / 1000 : ℝ)) ≤ krivineC := by
  let q : ℝ := 2071 / 5000
  let y : ℝ := √2 / (√2 + 2)
  let term : ℕ → ℝ := fun k ↦
    2 * (1 / (2 * (k : ℝ) + 1)) * y ^ (2 * k + 1)
  let qterm : ℕ → ℝ := fun k ↦
    2 * (1 / (2 * (k : ℝ) + 1)) * q ^ (2 * k + 1)
  have hy : q ≤ y := sqrt_two_ratio_lower
  have hy0 : 0 ≤ y := by dsimp [y]; positivity
  have hq0 : 0 ≤ q := by norm_num [q]
  have hlog := Real.hasSum_log_one_add (Real.sqrt_nonneg 2)
  have hterm0 (k : ℕ) : 0 ≤ term k := by
    dsimp [term]
    positivity
  have hpartial : (∑ k ∈ Finset.range 4, term k) ≤ krivineC := by
    have h := hlog.summable.sum_le_tsum (Finset.range 4)
      (fun k hk ↦ hterm0 k)
    have htsum : (∑' k : ℕ, term k) = krivineC := by
      simpa [term, y, krivineC] using hlog.tsum_eq
    rw [htsum] at h
    exact h
  have hmono : (∑ k ∈ Finset.range 4, qterm k) ≤
      ∑ k ∈ Finset.range 4, term k := by
    apply Finset.sum_le_sum
    intro k hk
    dsimp [qterm, term]
    gcongr
  have hcalc : (3.1416 : ℝ) / (2 * (1783 / 1000 : ℝ)) ≤
      ∑ k ∈ Finset.range 4, qterm k := by
    norm_num [qterm, q, Finset.sum_range_succ]
  exact hcalc.trans (hmono.trans hpartial)

/-- Krivine's explicit constant is at most the exact decimal `1.783`.

**Book Theorem 3.5.1.** -/
theorem krivineConstant_le_1783_1000 :
    krivineConstant ≤ (1783 / 1000 : ℝ) := by
  rw [krivineConstant]
  have hden : 0 < 2 * krivineC := mul_pos (by norm_num) krivineC_pos
  apply (div_le_iff₀ hden).2
  calc
    Real.pi ≤ (3.1416 : ℝ) := Real.pi_lt_d4.le
    _ ≤ (1783 / 1000 : ℝ) * (2 * krivineC) := by
      have h := krivineC_explicit_lower
      nlinarith

/-- At Krivine's parameter both feature maps send unit vectors to unit vectors.

**Lean implementation helper.** -/
theorem norm_sineFeatures_krivineC_of_unit
    (u : EuclideanSpace ℝ ι) (hu : ‖u‖ = 1) :
    ‖sineFeature krivineC krivineC_pos.le u‖ = 1 ∧
      ‖signedSineFeature krivineC krivineC_pos.le u‖ = 1 := by
  have hsq := norm_sq_sineFeatures_of_unit krivineC_pos.le u hu
  rw [sinh_krivineC] at hsq
  constructor <;> nlinarith [norm_nonneg (sineFeature krivineC krivineC_pos.le u),
    norm_nonneg (signedSineFeature krivineC krivineC_pos.le u)]

end
end HDP

namespace HDP.Chapter3

/-- **Example 3.7.8 (corrected).** The infinite odd-tensor maps realize
`sin (c ⟪u,v⟫)`.

**Book Example 3.7.8.** -/
theorem sine_feature_identity {ι : Type*} [Fintype ι]
    {c : ℝ} (hc : 0 ≤ c) (u v : EuclideanSpace ℝ ι) :
    inner ℝ (HDP.sineFeature c hc u) (HDP.signedSineFeature c hc v) =
      Real.sin (c * inner ℝ u v) :=
  HDP.inner_sineFeature_signedSineFeature hc u v

/-- Correct normalization for Example 3.7.8: `sinh c = 1` at
`c = log (1 + √2)`.

**Book Example 3.7.8.** -/
theorem krivine_sinh_normalization :
    Real.sinh (Real.log (1 + √2)) = 1 :=
  HDP.sinh_krivineC

/-- The explicit constant delivered by Krivine's proof of Theorem 3.5.1.

**Book Theorem 3.5.1.** -/
theorem krivine_constant_bound :
    Real.pi / (2 * Real.log (1 + √2)) ≤ (1783 / 1000 : ℝ) := by
  simpa [HDP.krivineConstant_eq] using HDP.krivineConstant_le_1783_1000

end HDP.Chapter3

end Source_24_Krivine

/-! ## Material formerly in `14_BilinearGrothendieck.lean` -/

section Source_14_BilinearGrothendieck

/-!
# Bilinear Grothendieck inequality via Krivine rounding

This source-neutral layer implements the complete rounding argument: the
infinite sine features are compressed to a finite Gram representation, a
standard Gaussian supplies simultaneous signs, and the exact sign--arcsine
identity computes their expectation.
-/

open scoped BigOperators RealInnerProductSpace lp ENNReal
open MeasureTheory ProbabilityTheory

namespace HDP.Chapter3

/-- Shows that `krivineC` is strictly smaller than `pi_div_two`.

**Lean implementation helper.** -/
lemma krivineC_lt_pi_div_two : HDP.krivineC < Real.pi / 2 := by
  have hlog : HDP.krivineC < √2 := by
    have h := Real.log_lt_sub_one_of_pos (x := (1 + √2 : ℝ)) (by positivity)
      (by nlinarith [Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)])
    simpa [HDP.krivineC] using h
  linarith [Real.sqrt_two_lt_three_halves, Real.pi_gt_three]

/-- Applying arcsine to the Krivine-transformed sine inner product recovers the scaled original inner product.

**Lean implementation helper.** -/
lemma arcsin_sin_krivine_inner
    {κ : Type*} [Fintype κ]
    (u v : EuclideanSpace ℝ κ) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    Real.arcsin (Real.sin (HDP.krivineC * inner ℝ u v)) =
      HDP.krivineC * inner ℝ u v := by
  have ht : |inner ℝ u v| ≤ 1 := by
    simpa [hu, hv] using abs_real_inner_le_norm u v
  have hc : |HDP.krivineC * inner ℝ u v| ≤ HDP.krivineC := by
    rw [abs_mul, abs_of_pos HDP.krivineC_pos]
    nlinarith [mul_nonneg HDP.krivineC_pos.le (sub_nonneg.mpr ht)]
  apply Real.arcsin_sin
  · linarith [krivineC_lt_pi_div_two, neg_le_of_abs_le hc]
  · linarith [krivineC_lt_pi_div_two, le_of_abs_le hc]

/-- The Gaussian `sign_pair` formed from two fixed inner products is integrable.

**Lean implementation helper.** -/
private lemma integrable_sign_pair {q : ℕ}
    (u v : EuclideanSpace ℝ (Fin q)) :
    Integrable (fun g : EuclideanSpace ℝ (Fin q) =>
      HDP.pmSign (inner ℝ u g) * HDP.pmSign (inner ℝ v g))
      (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin q))) := by
  refine Integrable.of_bound ?_ 1 ?_
  · exact ((HDP.measurable_pmSign.comp (by fun_prop)).mul
      (HDP.measurable_pmSign.comp (by fun_prop))).aestronglyMeasurable
  · filter_upwards [] with g
    simp [Real.norm_eq_abs, HDP.abs_pmSign]

/-- `integral_bilinear_sign` evaluates the expected randomly signed bilinear objective as `∑ i j, A i j * (2 / π) * arcsin ⟨U i, V j⟩`.

**Lean implementation helper.** -/
private lemma integral_bilinear_sign
    {m n : Type*} [Fintype m] [Fintype n] {q : ℕ}
    (A : Matrix m n ℝ)
    (U : m → EuclideanSpace ℝ (Fin q))
    (V : n → EuclideanSpace ℝ (Fin q))
    (hU : ∀ i, ‖U i‖ = 1) (hV : ∀ j, ‖V j‖ = 1) :
    (∫ g : EuclideanSpace ℝ (Fin q),
      HDP.bilinearObjective A
        (fun i => HDP.pmSign (inner ℝ (U i) g))
        (fun j => HDP.pmSign (inner ℝ (V j) g))
      ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin q)))) =
      ∑ i, ∑ j, A i j * ((2 / Real.pi) * Real.arcsin (inner ℝ (U i) (V j))) := by
  classical
  let μ := ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin q))
  have hterm (i : m) (j : n) : Integrable
      (fun g : EuclideanSpace ℝ (Fin q) =>
        A i j * (HDP.pmSign (inner ℝ (U i) g) *
          HDP.pmSign (inner ℝ (V j) g))) μ :=
    (integrable_sign_pair (U i) (V j)).const_mul (A i j)
  simp only [HDP.bilinearObjective, mul_assoc]
  rw [integral_finsetSum Finset.univ]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [integral_finsetSum Finset.univ]
    · apply Finset.sum_congr rfl
      intro j hj
      rw [integral_const_mul,
        HDP.stdGaussian_unit_sign_arcsin (U i) (V j) (hU i) (hV j)]
    · intro j hj
      exact hterm i j
  · intro i hi
    exact integrable_finsetSum Finset.univ (fun j hj => hterm i j)

/-- Identifies `pmSign` with `one_or_neg_one`.

**Lean implementation helper.** -/
lemma pmSign_eq_one_or_neg_one (x : ℝ) :
    HDP.pmSign x = 1 ∨ HDP.pmSign x = -1 := by
  by_cases hx : 0 ≤ x
  · exact Or.inl (HDP.pmSign_of_nonneg hx)
  · exact Or.inr (HDP.pmSign_of_neg (lt_of_not_ge hx))

/-- Krivine's proof gives a randomized rounding algorithm with an expected bilinear guarantee.

**Book Remark 3.7.9.** -/
private lemma integral_krivine_rounding
    {m n κ : Type*} [Fintype m] [Fintype n] [Fintype κ] {q : ℕ}
    (A : Matrix m n ℝ)
    (X : m → EuclideanSpace ℝ κ) (Y : n → EuclideanSpace ℝ κ)
    (hX : ∀ i, ‖X i‖ = 1) (hY : ∀ j, ‖Y j‖ = 1)
    (U : m → EuclideanSpace ℝ (Fin q))
    (V : n → EuclideanSpace ℝ (Fin q))
    (hU : ∀ i, ‖U i‖ = 1) (hV : ∀ j, ‖V j‖ = 1)
    (hUV : ∀ i j, inner ℝ (U i) (V j) =
      Real.sin (HDP.krivineC * inner ℝ (X i) (Y j))) :
    (∫ g : EuclideanSpace ℝ (Fin q),
      HDP.bilinearObjective A
        (fun i => HDP.pmSign (inner ℝ (U i) g))
        (fun j => HDP.pmSign (inner ℝ (V j) g))
      ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin q)))) =
      (2 * HDP.krivineC / Real.pi) * HDP.bilinearVectorObjective A X Y := by
  rw [integral_bilinear_sign A U V hU hV]
  simp_rw [hUV, arcsin_sin_krivine_inner _ _ (hX _) (hY _)]
  simp only [HDP.bilinearVectorObjective]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Krivine's infinite sine features for two finite unit-vector families have
a simultaneous finite Gram realization.

**Book Equation (3.37).** -/
theorem exists_krivine_vectors
    {m n κ : Type*} [Finite m] [Finite n] [Fintype κ]
    (X : m → EuclideanSpace ℝ κ) (Y : n → EuclideanSpace ℝ κ)
    (hX : ∀ i, ‖X i‖ = 1) (hY : ∀ j, ‖Y j‖ = 1) :
    ∃ (q : ℕ) (U : m → EuclideanSpace ℝ (Fin q))
        (V : n → EuclideanSpace ℝ (Fin q)),
      (∀ i, ‖U i‖ = 1) ∧ (∀ j, ‖V j‖ = 1) ∧
        ∀ i j, inner ℝ (U i) (V j) =
          Real.sin (HDP.krivineC * inner ℝ (X i) (Y j)) := by
  classical
  letI := Fintype.ofFinite m
  letI := Fintype.ofFinite n
  let W : m ⊕ n → HDP.SineFeatureSpace κ :=
    Sum.elim
      (fun i => HDP.sineFeature HDP.krivineC HDP.krivineC_pos.le (X i))
      (fun j => HDP.signedSineFeature HDP.krivineC HDP.krivineC_pos.le (Y j))
  have hpsd : (Matrix.gram ℝ W).PosSemidef := Matrix.posSemidef_gram ℝ W
  rcases exists_gram_of_posSemidef hpsd with ⟨q, z, hz⟩
  let U : m → EuclideanSpace ℝ (Fin q) := fun i => z (Sum.inl i)
  let V : n → EuclideanSpace ℝ (Fin q) := fun j => z (Sum.inr j)
  refine ⟨q, U, V, ?_, ?_, ?_⟩
  · intro i
    have hsine := (HDP.norm_sineFeatures_krivineC_of_unit (X i) (hX i)).1
    have hii : inner ℝ (U i) (U i) = 1 := by
      calc
        inner ℝ (U i) (U i) = Matrix.gram ℝ z (Sum.inl i) (Sum.inl i) := by
          simp [Matrix.gram_apply, U]
        _ = Matrix.gram ℝ W (Sum.inl i) (Sum.inl i) := by rw [hz]
        _ = inner ℝ
            (HDP.sineFeature HDP.krivineC HDP.krivineC_pos.le (X i))
            (HDP.sineFeature HDP.krivineC HDP.krivineC_pos.le (X i)) := by
          simp [Matrix.gram_apply, W]
        _ = 1 := by rw [real_inner_self_eq_norm_sq, hsine]; norm_num
    rw [real_inner_self_eq_norm_sq] at hii
    nlinarith [norm_nonneg (U i)]
  · intro j
    have hsine := (HDP.norm_sineFeatures_krivineC_of_unit (Y j) (hY j)).2
    have hjj : inner ℝ (V j) (V j) = 1 := by
      calc
        inner ℝ (V j) (V j) = Matrix.gram ℝ z (Sum.inr j) (Sum.inr j) := by
          simp [Matrix.gram_apply, V]
        _ = Matrix.gram ℝ W (Sum.inr j) (Sum.inr j) := by rw [hz]
        _ = inner ℝ
            (HDP.signedSineFeature HDP.krivineC HDP.krivineC_pos.le (Y j))
            (HDP.signedSineFeature HDP.krivineC HDP.krivineC_pos.le (Y j)) := by
          simp [Matrix.gram_apply, W]
        _ = 1 := by rw [real_inner_self_eq_norm_sq, hsine]; norm_num
    rw [real_inner_self_eq_norm_sq] at hjj
    nlinarith [norm_nonneg (V j)]
  · intro i j
    calc
      inner ℝ (U i) (V j) = Matrix.gram ℝ z (Sum.inl i) (Sum.inr j) := by
        simp [Matrix.gram_apply, U, V]
      _ = Matrix.gram ℝ W (Sum.inl i) (Sum.inr j) := by rw [hz]
      _ = inner ℝ
          (HDP.sineFeature HDP.krivineC HDP.krivineC_pos.le (X i))
          (HDP.signedSineFeature HDP.krivineC HDP.krivineC_pos.le (Y j)) := by
        simp [Matrix.gram_apply, W]
      _ = Real.sin (HDP.krivineC * inner ℝ (X i) (Y j)) :=
        HDP.inner_sineFeature_signedSineFeature HDP.krivineC_pos.le (X i) (Y j)

/-- The complete finite-dimensional real Grothendieck inequality with
Krivine's explicit constant. The scalar hypothesis is quantified only over
sign vectors; Gaussian rounding produces such vectors pointwise.

**Book Theorem 3.5.1.** -/
theorem grothendieck_inequality
    {m n κ : Type*} [Fintype m] [Fintype n] [Fintype κ]
    (A : Matrix m n ℝ) (C : ℝ)
    (hA : ∀ (x : m → ℝ) (y : n → ℝ),
      (∀ i, x i = 1 ∨ x i = -1) → (∀ j, y j = 1 ∨ y j = -1) →
        |HDP.bilinearObjective A x y| ≤ C)
    (X : m → EuclideanSpace ℝ κ) (Y : n → EuclideanSpace ℝ κ)
    (hX : ∀ i, ‖X i‖ = 1) (hY : ∀ j, ‖Y j‖ = 1) :
    |HDP.bilinearVectorObjective A X Y| ≤ HDP.krivineConstant * C := by
  classical
  rcases exists_krivine_vectors X Y hX hY with
    ⟨q, U, V, hU, hV, hUV⟩
  let F : EuclideanSpace ℝ (Fin q) → ℝ := fun g =>
    HDP.bilinearObjective A
      (fun i => HDP.pmSign (inner ℝ (U i) g))
      (fun j => HDP.pmSign (inner ℝ (V j) g))
  have hpoint (g : EuclideanSpace ℝ (Fin q)) : |F g| ≤ C := by
    apply hA
    · intro i
      exact pmSign_eq_one_or_neg_one _
    · intro j
      exact pmSign_eq_one_or_neg_one _
  have hint :
      (∫ g : EuclideanSpace ℝ (Fin q), F g
        ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin q)))) =
        (2 * HDP.krivineC / Real.pi) *
          HDP.bilinearVectorObjective A X Y := by
    exact integral_krivine_rounding A X Y hX hY U V hU hV hUV
  have hb := MeasureTheory.norm_integral_le_of_norm_le_const
    (μ := ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin q)))
    (f := F) (C := C)
    (ae_of_all _ fun g => (by simpa [Real.norm_eq_abs] using hpoint g))
  have hb' :
      |(2 * HDP.krivineC / Real.pi) * HDP.bilinearVectorObjective A X Y| ≤ C := by
    rw [← hint]
    simpa [Real.norm_eq_abs] using hb
  have ha : 0 < 2 * HDP.krivineC / Real.pi :=
    div_pos (mul_pos (by norm_num) HDP.krivineC_pos) Real.pi_pos
  rw [abs_mul, abs_of_pos ha] at hb'
  have hK : 0 ≤ HDP.krivineConstant := by
    exact (div_pos Real.pi_pos (mul_pos (by norm_num) HDP.krivineC_pos)).le
  calc
    |HDP.bilinearVectorObjective A X Y| =
        HDP.krivineConstant *
          ((2 * HDP.krivineC / Real.pi) *
            |HDP.bilinearVectorObjective A X Y|) := by
      rw [HDP.krivineConstant]
      field_simp [Real.pi_ne_zero, ne_of_gt HDP.krivineC_pos]
    _ ≤ HDP.krivineConstant * C := mul_le_mul_of_nonneg_left hb' hK

/-- The real Grothendieck inequality, with the explicit
Krivine constant and the source's one-sided sign hypothesis. Negating the
left sign vector turns that hypothesis into the absolute-value hypothesis
needed by the rounding theorem.

**Book Theorem 3.5.1.** -/
theorem grothendieck_inequality_krivine
    {m n κ : Type*} [Fintype m] [Fintype n] [Fintype κ]
    (A : Matrix m n ℝ)
    (hA : ∀ (x : m → ℝ) (y : n → ℝ),
      (∀ i, x i = 1 ∨ x i = -1) → (∀ j, y j = 1 ∨ y j = -1) →
        HDP.bilinearObjective A x y ≤ 1)
    (X : m → EuclideanSpace ℝ κ) (Y : n → EuclideanSpace ℝ κ)
    (hX : ∀ i, ‖X i‖ = 1) (hY : ∀ j, ‖Y j‖ = 1) :
    |HDP.bilinearVectorObjective A X Y| ≤ HDP.krivineConstant := by
  apply (grothendieck_inequality A 1 ?_ X Y hX hY).trans_eq (mul_one _)
  intro x y hx hy
  rw [abs_le]
  constructor
  · have hn := hA (-x) y (by
      intro i
      rcases hx i with hi | hi
      · right; simp [hi]
      · left; simp [hi]) hy
    have hneg : HDP.bilinearObjective A (-x) y =
        -HDP.bilinearObjective A x y := by
      simp [HDP.bilinearObjective, Finset.sum_neg_distrib]
    rw [hneg] at hn
    linarith
  · exact hA x y hx hy

/-- Numerical form of Theorem 3.5.1 with the exact rational encoding of
`1.783`.

**Book Theorem 3.5.1.** -/
theorem grothendieck_inequality_1783_1000
    {m n κ : Type*} [Fintype m] [Fintype n] [Fintype κ]
    (A : Matrix m n ℝ)
    (hA : ∀ (x : m → ℝ) (y : n → ℝ),
      (∀ i, x i = 1 ∨ x i = -1) → (∀ j, y j = 1 ∨ y j = -1) →
        HDP.bilinearObjective A x y ≤ 1)
    (X : m → EuclideanSpace ℝ κ) (Y : n → EuclideanSpace ℝ κ)
    (hX : ∀ i, ‖X i‖ = 1) (hY : ∀ j, ‖Y j‖ = 1) :
    |HDP.bilinearVectorObjective A X Y| ≤ (1783 / 1000 : ℝ) :=
  (grothendieck_inequality_krivine A hA X Y hX hY).trans
    HDP.krivineConstant_le_1783_1000

/-- Homogeneous form (3.23). The scalar assumption is the homogeneous
`ℓ∞` form (3.22); arbitrary finite vector families are reduced to unit
directions by absorbing their lengths into the matrix coefficients. A
nonempty coordinate type is the corrected positive-dimension hypothesis.

**Book Remark 3.5.2.** -/
theorem grothendieck_homogeneous
    {m n κ : Type*} [Fintype m] [Fintype n] [Fintype κ] [Nonempty κ]
    (A : Matrix m n ℝ) (C : ℝ)
    (hA : ∀ (x : m → ℝ) (y : n → ℝ),
      |HDP.bilinearObjective A x y| ≤
        C * HDP.Chapter1.linftyNorm x * HDP.Chapter1.linftyNorm y)
    (X : m → EuclideanSpace ℝ κ) (Y : n → EuclideanSpace ℝ κ) :
    |HDP.bilinearVectorObjective A X Y| ≤
      HDP.krivineConstant * C *
        HDP.Chapter1.linftyNorm (fun i ↦ ‖X i‖) *
        HDP.Chapter1.linftyNorm (fun j ↦ ‖Y j‖) := by
  classical
  let nx : m → ℝ := fun i ↦ ‖X i‖
  let ny : n → ℝ := fun j ↦ ‖Y j‖
  let e : EuclideanSpace ℝ κ := EuclideanSpace.single (Classical.choice inferInstance) 1
  have he : ‖e‖ = 1 := by simp [e]
  let U : m → EuclideanSpace ℝ κ := fun i ↦
    if h : nx i = 0 then e else (nx i)⁻¹ • X i
  let V : n → EuclideanSpace ℝ κ := fun j ↦
    if h : ny j = 0 then e else (ny j)⁻¹ • Y j
  have hU : ∀ i, ‖U i‖ = 1 := by
    intro i
    dsimp [U]
    split_ifs with hi
    · exact he
    · have hpos : 0 < nx i := (norm_nonneg (X i)).lt_of_ne (Ne.symm hi)
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hpos]
      change (nx i)⁻¹ * nx i = 1
      exact inv_mul_cancel₀ hi
  have hV : ∀ j, ‖V j‖ = 1 := by
    intro j
    dsimp [V]
    split_ifs with hj
    · exact he
    · have hpos : 0 < ny j := (norm_nonneg (Y j)).lt_of_ne (Ne.symm hj)
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hpos]
      change (ny j)⁻¹ * ny j = 1
      exact inv_mul_cancel₀ hj
  let A' : Matrix m n ℝ := fun i j ↦ A i j * nx i * ny j
  have hscalar (x : m → ℝ) (y : n → ℝ) :
      HDP.bilinearObjective A' x y =
        HDP.bilinearObjective A (fun i ↦ nx i * x i) (fun j ↦ ny j * y j) := by
    simp only [HDP.bilinearObjective, A']
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hlinfty_x (x : m → ℝ) (hx : ∀ i, |x i| = 1) :
      HDP.Chapter1.linftyNorm (fun i ↦ nx i * x i) =
        HDP.Chapter1.linftyNorm nx := by
    apply le_antisymm
    · rw [HDP.Chapter1.linftyNorm_le_iff
        (HDP.Chapter1.linftyNorm_nonneg nx)]
      intro i
      have hi := (HDP.Chapter1.linftyNorm_le_iff
        (HDP.Chapter1.linftyNorm_nonneg nx)).1 le_rfl i
      simpa [abs_mul, hx i, nx, abs_of_nonneg (norm_nonneg (X i))] using hi
    · rw [HDP.Chapter1.linftyNorm_le_iff
        (HDP.Chapter1.linftyNorm_nonneg (fun i ↦ nx i * x i))]
      intro i
      have hi := (HDP.Chapter1.linftyNorm_le_iff
        (HDP.Chapter1.linftyNorm_nonneg (fun i ↦ nx i * x i))).1 le_rfl i
      simpa [abs_mul, hx i, nx, abs_of_nonneg (norm_nonneg (X i))] using hi
  have hlinfty_y (y : n → ℝ) (hy : ∀ j, |y j| = 1) :
      HDP.Chapter1.linftyNorm (fun j ↦ ny j * y j) =
        HDP.Chapter1.linftyNorm ny := by
    apply le_antisymm
    · rw [HDP.Chapter1.linftyNorm_le_iff
        (HDP.Chapter1.linftyNorm_nonneg ny)]
      intro j
      have hj := (HDP.Chapter1.linftyNorm_le_iff
        (HDP.Chapter1.linftyNorm_nonneg ny)).1 le_rfl j
      simpa [abs_mul, hy j, ny, abs_of_nonneg (norm_nonneg (Y j))] using hj
    · rw [HDP.Chapter1.linftyNorm_le_iff
        (HDP.Chapter1.linftyNorm_nonneg (fun j ↦ ny j * y j))]
      intro j
      have hj := (HDP.Chapter1.linftyNorm_le_iff
        (HDP.Chapter1.linftyNorm_nonneg (fun j ↦ ny j * y j))).1 le_rfl j
      simpa [abs_mul, hy j, ny, abs_of_nonneg (norm_nonneg (Y j))] using hj
  have hsign : ∀ (x : m → ℝ) (y : n → ℝ),
      (∀ i, x i = 1 ∨ x i = -1) → (∀ j, y j = 1 ∨ y j = -1) →
        |HDP.bilinearObjective A' x y| ≤
          C * HDP.Chapter1.linftyNorm nx * HDP.Chapter1.linftyNorm ny := by
    intro x y hx hy
    have hxabs : ∀ i, |x i| = 1 := by intro i; rcases hx i with hi | hi <;> simp [hi]
    have hyabs : ∀ j, |y j| = 1 := by intro j; rcases hy j with hj | hj <;> simp [hj]
    rw [hscalar, ← hlinfty_x x hxabs, ← hlinfty_y y hyabs]
    exact hA _ _
  have hobjective : HDP.bilinearVectorObjective A' U V =
      HDP.bilinearVectorObjective A X Y := by
    simp only [HDP.bilinearVectorObjective]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hxi : nx i = 0
    · have hX0 : X i = 0 := norm_eq_zero.mp (by simpa [nx] using hxi)
      simp [A', U, hxi, hX0]
    · by_cases hyj : ny j = 0
      · have hY0 : Y j = 0 := norm_eq_zero.mp (by simpa [ny] using hyj)
        simp [A', V, hyj, hY0]
      · simp only [A', U, V, dif_neg hxi, dif_neg hyj, real_inner_smul_left,
          real_inner_smul_right]
        field_simp [hxi, hyj]
  have hround := grothendieck_inequality A'
    (C * HDP.Chapter1.linftyNorm nx * HDP.Chapter1.linftyNorm ny)
    hsign U V hU hV
  rw [hobjective] at hround
  simpa [nx, ny, mul_assoc] using hround

/-- Source-facing approximation guarantee for the bilinear vector SDP: an
absolute bound for all integer sign assignments controls every feasible SDP
assignment within Krivine's constant.

**Book Section 3.5.** -/
theorem bilinear_sdp_relaxation_approximation
    {m n κ : Type*} [Fintype m] [Fintype n] [Fintype κ]
    (A : Matrix m n ℝ) (C : ℝ)
    (hinteger : ∀ (x : m → ℝ) (y : n → ℝ),
      (∀ i, x i = 1 ∨ x i = -1) → (∀ j, y j = 1 ∨ y j = -1) →
        |HDP.bilinearObjective A x y| ≤ C)
    (X : m → EuclideanSpace ℝ κ) (Y : n → EuclideanSpace ℝ κ)
    (hX : ∀ i, ‖X i‖ = 1) (hY : ∀ j, ‖Y j‖ = 1) :
    |HDP.bilinearVectorObjective A X Y| ≤ HDP.krivineConstant * C :=
  grothendieck_inequality A C hinteger X Y hX hY

/-- The core bilinear form is additive in its left vector argument.

**Lean implementation helper.** -/
private lemma bilinear_add_left_core
    {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (x z : m → ℝ) (y : n → ℝ) :
    HDP.bilinearObjective A (x + z) y =
      HDP.bilinearObjective A x y + HDP.bilinearObjective A z y := by
  simp only [HDP.bilinearObjective, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The core bilinear form is additive in its right vector argument.

**Lean implementation helper.** -/
private lemma bilinear_add_right_core
    {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (x : m → ℝ) (y z : n → ℝ) :
    HDP.bilinearObjective A x (y + z) =
      HDP.bilinearObjective A x y + HDP.bilinearObjective A x z := by
  simp only [HDP.bilinearObjective, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Scaling both arguments of the core bilinear form multiplies its value by the product of the scalars.

**Lean implementation helper.** -/
private lemma bilinear_smul_smul_core
    {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (a b : ℝ) (x : m → ℝ) (y : n → ℝ) :
    HDP.bilinearObjective A (a • x) (b • y) =
      (a * b) * HDP.bilinearObjective A x y := by
  simp only [HDP.bilinearObjective, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The core bilinear form is homogeneous in its left argument.

**Lean implementation helper.** -/
private lemma bilinear_smul_left_core
    {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (a : ℝ) (x : m → ℝ) (y : n → ℝ) :
    HDP.bilinearObjective A (a • x) y = a * HDP.bilinearObjective A x y := by
  simpa using bilinear_smul_smul_core A a 1 x y

/-- The core bilinear form is homogeneous in its right argument.

**Lean implementation helper.** -/
private lemma bilinear_smul_right_core
    {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (a : ℝ) (x : m → ℝ) (y : n → ℝ) :
    HDP.bilinearObjective A x (a • y) = a * HDP.bilinearObjective A x y := by
  simpa [mul_comm] using bilinear_smul_smul_core A 1 a x y

/-- Identifies `quadraticObjective` with `bilinear`.

**Lean implementation helper.** -/
theorem quadraticObjective_eq_bilinear
    {n : Type*} [Fintype n] (A : Matrix n n ℝ) (x : n → ℝ) :
    HDP.quadraticObjective A x = HDP.bilinearObjective A x x := rfl

/-- Swapping the two vector families transposes the coefficient matrix in the bilinear objective.

**Lean implementation helper.** -/
private lemma bilinearObjective_swap
    {n : Type*} [Fintype n] (A : Matrix n n ℝ) (hA : A.IsSymm)
    (x y : n → ℝ) :
    HDP.bilinearObjective A x y = HDP.bilinearObjective A y x := by
  classical
  simp only [HDP.bilinearObjective]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hA.apply]
  ring

/-- Polarization for the matrix quadratic form, used by both quadratic
Grothendieck variants.

**Lean implementation helper.** -/
theorem quadratic_polarization
    {n : Type*} [Fintype n] (A : Matrix n n ℝ) (hA : A.IsSymm)
    (x y : n → ℝ) :
    HDP.bilinearObjective A x y =
      HDP.quadraticObjective A ((2 : ℝ)⁻¹ • (x + y)) -
        HDP.quadraticObjective A ((2 : ℝ)⁻¹ • (x - y)) := by
  rw [quadraticObjective_eq_bilinear, quadraticObjective_eq_bilinear]
  rw [bilinear_smul_smul_core, bilinear_smul_smul_core]
  rw [bilinear_add_left_core, bilinear_add_right_core,
    bilinear_add_right_core]
  have hsub : x - y = x + (-y) := sub_eq_add_neg x y
  rw [hsub, bilinear_add_left_core,
    bilinear_add_right_core, bilinear_add_right_core]
  have hxy := bilinearObjective_swap A hA x y
  have h1 : HDP.bilinearObjective A x (-y) =
      -HDP.bilinearObjective A x y := by
    simpa using bilinear_smul_right_core A (-1 : ℝ) x y
  have h2 : HDP.bilinearObjective A (-y) x =
      -HDP.bilinearObjective A y x := by
    simpa using bilinear_smul_left_core A (-1 : ℝ) y x
  have h3 : HDP.bilinearObjective A (-y) (-y) =
      HDP.bilinearObjective A y y := by
    simpa using bilinear_smul_smul_core A (-1 : ℝ) (-1 : ℝ) y y
  rw [h1, h2, h3, ← hxy]
  ring

/-- Shows that `quadraticObjective` is nonnegative.

**Lean implementation helper.** -/
private lemma quadraticObjective_nonneg
    {n : Type*} [Fintype n] (A : Matrix n n ℝ) (hA : A.PosSemidef)
    (x : n → ℝ) : 0 ≤ HDP.quadraticObjective A x := by
  have h := hA.dotProduct_mulVec_nonneg x
  calc
    0 ≤ ∑ i, x i * ∑ j, A i j * x j := by
      simpa [dotProduct, Matrix.mulVec] using h
    _ = HDP.quadraticObjective A x := by
      simp only [HDP.quadraticObjective]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring

/-- Source-facing positive-semidefinite quadratic Grothendieck inequality
(Remark 3.5.3 / Exercise 3.49).

**Book Remark 3.5.3.** -/
theorem quadratic_grothendieck_psd
    {n κ : Type*} [Fintype n] [Fintype κ]
    (A : Matrix n n ℝ) (hA : A.PosSemidef)
    (hsign : ∀ x : n → ℝ, (∀ i, x i = 1 ∨ x i = -1) →
      HDP.quadraticObjective A x ≤ 1)
    (U V : n → EuclideanSpace ℝ κ)
    (hU : ∀ i, ‖U i‖ = 1) (hV : ∀ j, ‖V j‖ = 1) :
    |HDP.bilinearVectorObjective A U V| ≤ 2 * HDP.krivineConstant := by
  have hsym : A.IsSymm := Matrix.isHermitian_iff_isSymm.mp hA.isHermitian
  have hbilin : ∀ (x : n → ℝ) (y : n → ℝ),
      (∀ i, x i = 1 ∨ x i = -1) → (∀ j, y j = 1 ∨ y j = -1) →
        HDP.bilinearObjective A x y ≤ 1 := by
    intro x y hx hy
    have hn := quadraticObjective_nonneg A hA (x - y)
    have hqx := hsign x hx
    have hqy := hsign y hy
    have hexpand : HDP.quadraticObjective A (x - y) =
        HDP.quadraticObjective A x + HDP.quadraticObjective A y -
          2 * HDP.bilinearObjective A x y := by
      rw [quadraticObjective_eq_bilinear]
      have hsub : x - y = x + (-y) := sub_eq_add_neg x y
      rw [hsub, bilinear_add_left_core,
        bilinear_add_right_core, bilinear_add_right_core]
      have hxy := bilinearObjective_swap A hsym x y
      have h1 : HDP.bilinearObjective A x (-y) =
          -HDP.bilinearObjective A x y := by
        simpa using bilinear_smul_right_core A (-1 : ℝ) x y
      have h2 : HDP.bilinearObjective A (-y) x =
          -HDP.bilinearObjective A y x := by
        simpa using bilinear_smul_left_core A (-1 : ℝ) y x
      have h3 : HDP.bilinearObjective A (-y) (-y) =
          HDP.bilinearObjective A y y := by
        simpa using bilinear_smul_smul_core A (-1 : ℝ) (-1 : ℝ) y y
      rw [h1, h2, h3, ← hxy,
        ← quadraticObjective_eq_bilinear A x,
        ← quadraticObjective_eq_bilinear A y]
      ring
    rw [hexpand] at hn
    linarith
  have hK := grothendieck_inequality_krivine A hbilin U V hU hV
  have hK0 : 0 ≤ HDP.krivineConstant :=
    (div_pos Real.pi_pos (mul_pos (by norm_num) HDP.krivineC_pos)).le
  exact hK.trans (by linarith)

/-- Homogeneous positive-semidefinite quadratic Grothendieck bound. If every
sign-vector quadratic value is at most `C`, then every bilinear unit-vector
relaxation is bounded by `K * C` (and therefore by the source's stated
`2 K C`).

**Book Remark 3.5.3.** -/
theorem quadratic_grothendieck_psd_bound
    {n κ : Type*} [Fintype n] [Fintype κ]
    (A : Matrix n n ℝ) (hA : A.PosSemidef) (C : ℝ)
    (hsign : ∀ x : n → ℝ, (∀ i, x i = 1 ∨ x i = -1) →
      HDP.quadraticObjective A x ≤ C)
    (U V : n → EuclideanSpace ℝ κ)
    (hU : ∀ i, ‖U i‖ = 1) (hV : ∀ j, ‖V j‖ = 1) :
    |HDP.bilinearVectorObjective A U V| ≤ HDP.krivineConstant * C := by
  have hsym : A.IsSymm := Matrix.isHermitian_iff_isSymm.mp hA.isHermitian
  have hupp : ∀ (x : n → ℝ) (y : n → ℝ),
      (∀ i, x i = 1 ∨ x i = -1) → (∀ j, y j = 1 ∨ y j = -1) →
        HDP.bilinearObjective A x y ≤ C := by
    intro x y hx hy
    have hn := quadraticObjective_nonneg A hA (x - y)
    have hqx := hsign x hx
    have hqy := hsign y hy
    have hexpand : HDP.quadraticObjective A (x - y) =
        HDP.quadraticObjective A x + HDP.quadraticObjective A y -
          2 * HDP.bilinearObjective A x y := by
      rw [quadraticObjective_eq_bilinear]
      have hsub : x - y = x + (-y) := sub_eq_add_neg x y
      rw [hsub, bilinear_add_left_core,
        bilinear_add_right_core, bilinear_add_right_core]
      have hxy := bilinearObjective_swap A hsym x y
      have h1 : HDP.bilinearObjective A x (-y) =
          -HDP.bilinearObjective A x y := by
        simpa using bilinear_smul_right_core A (-1 : ℝ) x y
      have h2 : HDP.bilinearObjective A (-y) x =
          -HDP.bilinearObjective A y x := by
        simpa using bilinear_smul_left_core A (-1 : ℝ) y x
      have h3 : HDP.bilinearObjective A (-y) (-y) =
          HDP.bilinearObjective A y y := by
        simpa using bilinear_smul_smul_core A (-1 : ℝ) (-1 : ℝ) y y
      rw [h1, h2, h3, ← hxy,
        ← quadraticObjective_eq_bilinear A x,
        ← quadraticObjective_eq_bilinear A y]
      ring
    rw [hexpand] at hn
    linarith
  apply grothendieck_inequality A C ?_ U V hU hV
  intro x y hx hy
  rw [abs_le]
  constructor
  · have hneg := hupp (-x) y (by
      intro i
      rcases hx i with hi | hi
      · right; simp [hi]
      · left; simp [hi]) hy
    have heq : HDP.bilinearObjective A (-x) y =
        -HDP.bilinearObjective A x y := by
      simpa using bilinear_smul_left_core A (-1 : ℝ) x y
    rw [heq] at hneg
    linarith
  · exact hupp x y hx hy

/-- Quadratic Grothendieck in the continuous-cube form. Exercise 3.50 proves
that a symmetric diagonal-free sign hypothesis supplies `hcube`.

**Book Remark 3.5.3.** -/
theorem quadratic_grothendieck_of_cube
    {n κ : Type*} [Fintype n] [Fintype κ]
    (A : Matrix n n ℝ) (hA : A.IsSymm)
    (hcube : ∀ x : n → ℝ, (∀ i, |x i| ≤ 1) →
      |HDP.quadraticObjective A x| ≤ 1)
    (U V : n → EuclideanSpace ℝ κ)
    (hU : ∀ i, ‖U i‖ = 1) (hV : ∀ j, ‖V j‖ = 1) :
    |HDP.bilinearVectorObjective A U V| ≤ 2 * HDP.krivineConstant := by
  have hbilin : ∀ (x : n → ℝ) (y : n → ℝ),
      (∀ i, x i = 1 ∨ x i = -1) → (∀ j, y j = 1 ∨ y j = -1) →
        |HDP.bilinearObjective A x y| ≤ 2 := by
    intro x y hx hy
    let xp : n → ℝ := (2 : ℝ)⁻¹ • (x + y)
    let xm : n → ℝ := (2 : ℝ)⁻¹ • (x - y)
    have hxp : ∀ i, |xp i| ≤ 1 := by
      intro i
      dsimp [xp]
      rw [abs_mul]
      have ht := abs_add_le (x i) (y i)
      have hxi : |x i| = 1 := by rcases hx i with hi | hi <;> simp [hi]
      have hyi : |y i| = 1 := by rcases hy i with hi | hi <;> simp [hi]
      norm_num at ht ⊢
      linarith
    have hxm : ∀ i, |xm i| ≤ 1 := by
      intro i
      dsimp [xm]
      rw [abs_mul]
      have ht := abs_sub (x i) (y i)
      have hxi : |x i| = 1 := by rcases hx i with hi | hi <;> simp [hi]
      have hyi : |y i| = 1 := by rcases hy i with hi | hi <;> simp [hi]
      norm_num at ht ⊢
      linarith
    have hp := hcube xp hxp
    have hm := hcube xm hxm
    have hpol := quadratic_polarization A hA x y
    change HDP.bilinearObjective A x y =
      HDP.quadraticObjective A xp - HDP.quadraticObjective A xm at hpol
    rw [hpol]
    exact (abs_sub _ _).trans (by linarith)
  have h := grothendieck_inequality A 2 hbilin U V hU hV
  simpa [mul_comm] using h

/-! ## The attained quadratic SDP guarantee -/

/-- The two inequalities in Theorem 3.5.7 for specified maximizers of the
integer and vector programs.

**Book Theorem 3.5.7.** -/
theorem sdp_relaxation_guarantee_at_maximizers
    {n : Type*} [Fintype n] [Nonempty n]
    (A : Matrix n n ℝ) (hA : A.PosSemidef)
    (x : n → ℝ) (hx : ∀ i, x i = 1 ∨ x i = -1)
    (hxmax : ∀ y : n → ℝ, (∀ i, y i = 1 ∨ y i = -1) →
      HDP.quadraticObjective A y ≤ HDP.quadraticObjective A x)
    (X : n → EuclideanSpace ℝ n) (hX : ∀ i, ‖X i‖ = 1)
    (hXmax : ∀ Y : n → EuclideanSpace ℝ n, (∀ i, ‖Y i‖ = 1) →
      HDP.vectorSDPObjective A Y ≤ HDP.vectorSDPObjective A X) :
    HDP.quadraticObjective A x ≤ HDP.vectorSDPObjective A X ∧
      HDP.vectorSDPObjective A X ≤
        (2 * HDP.krivineConstant) * HDP.quadraticObjective A x := by
  classical
  let i0 : n := Classical.choice inferInstance
  let e : EuclideanSpace ℝ n := EuclideanSpace.single i0 1
  have he : ‖e‖ = 1 := by simp [e]
  have hembUnit : ∀ i, ‖x i • e‖ = 1 := by
    intro i
    have hxi : |x i| = 1 := by
      rcases hx i with hi | hi <;> simp [hi]
    simp [norm_smul, he, hxi]
  have hlower := hXmax (fun i => x i • e) hembUnit
  rw [HDP.vectorSDPObjective_scalarEmbedding A x e he] at hlower
  refine ⟨hlower, ?_⟩
  have hgro := quadratic_grothendieck_psd_bound A hA
    (HDP.quadraticObjective A x) hxmax X X hX hX
  have hC : 0 ≤ HDP.quadraticObjective A x := quadraticObjective_nonneg A hA x
  have hK : 0 ≤ HDP.krivineConstant :=
    (div_pos Real.pi_pos (mul_pos (by norm_num) HDP.krivineC_pos)).le
  calc
    HDP.vectorSDPObjective A X ≤ |HDP.vectorSDPObjective A X| := le_abs_self _
    _ ≤ HDP.krivineConstant * HDP.quadraticObjective A x := by
      simpa [HDP.bilinearVectorObjective, HDP.vectorSDPObjective] using hgro
    _ ≤ (2 * HDP.krivineConstant) * HDP.quadraticObjective A x := by
      nlinarith

/-- Both finite programs
attain their maxima, and their maximizing values satisfy
`int(A) ≤ sdp(A) ≤ 2 K int(A)`. The existential maximizers make attainment
part of the theorem instead of hiding it behind an unsafe real supremum.

**Book Theorem 3.5.7.** -/
theorem sdp_relaxation_guarantee
    {n : Type*} [Fintype n] [Nonempty n]
    (A : Matrix n n ℝ) (hA : A.PosSemidef) :
    ∃ (x : n → ℝ) (X : n → EuclideanSpace ℝ n),
      (∀ i, x i = 1 ∨ x i = -1) ∧
      (∀ i, ‖X i‖ = 1) ∧
      (∀ y : n → ℝ, (∀ i, y i = 1 ∨ y i = -1) →
        HDP.quadraticObjective A y ≤ HDP.quadraticObjective A x) ∧
      (∀ Y : n → EuclideanSpace ℝ n, (∀ i, ‖Y i‖ = 1) →
        HDP.vectorSDPObjective A Y ≤ HDP.vectorSDPObjective A X) ∧
      HDP.quadraticObjective A x ≤ HDP.vectorSDPObjective A X ∧
      HDP.vectorSDPObjective A X ≤
        (2 * HDP.krivineConstant) * HDP.quadraticObjective A x := by
  obtain ⟨x, hx, hxmax⟩ := HDP.exists_integerObjective_maximizer A
  obtain ⟨X, hX, hXmax⟩ := HDP.vectorSDPObjective_attains
    (κ := n) A
  have hbound := sdp_relaxation_guarantee_at_maximizers
    A hA x hx hxmax X hX hXmax
  exact ⟨x, X, hx, hX, hxmax, hXmax, hbound⟩

end HDP.Chapter3

end Source_14_BilinearGrothendieck

/-! ## Material formerly in `15_GrothendieckConsequences.lean` -/

section Source_15_GrothendieckConsequences

/-!
# Grothendieck consequences and finite-dimensional reductions

These load-bearing exercise results are part of the core import graph because
Chapter 3 itself and later chapters use them. Rectangular matrices consistently
use the row index first and the column index second. Each source-numbered
declaration is authoritative here; no exercise-leaf wrapper is provided.
 -/

open scoped BigOperators RealInnerProductSpace
open Set

namespace HDP

/-- The sign-cube hypothesis for a rectangular bilinear form.

**Lean implementation helper.** -/
def BilinearSignBound {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) : Prop :=
  ∀ (x : m → ℝ) (y : n → ℝ),
    (∀ i, |x i| = 1) → (∀ j, |y j| = 1) →
      bilinearObjective A x y ≤ 1

/-- The continuous-cube hypothesis for a rectangular bilinear form.

**Lean implementation helper.** -/
def BilinearCubeBound {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) : Prop :=
  ∀ (x : m → ℝ) (y : n → ℝ),
    (∀ i, |x i| ≤ 1) → (∀ j, |y j| ≤ 1) →
      bilinearObjective A x y ≤ 1

/-- The homogeneous `ℓ∞` hypothesis in Remark 3.5.2.

**Book Remark 3.5.2.** -/
def BilinearHomogeneousBound {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) : Prop :=
  ∀ (x : m → ℝ) (y : n → ℝ),
    bilinearObjective A x y ≤
      Chapter1.linftyNorm x * Chapter1.linftyNorm y

/-- Absolute-value version of the sign-cube hypothesis.

**Lean implementation helper.** -/
def BilinearAbsSignBound {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) : Prop :=
  ∀ (x : m → ℝ) (y : n → ℝ),
    (∀ i, |x i| = 1) → (∀ j, |y j| = 1) →
      |bilinearObjective A x y| ≤ 1

/-- Absolute-value version of the continuous-cube hypothesis.

**Lean implementation helper.** -/
def BilinearAbsCubeBound {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) : Prop :=
  ∀ (x : m → ℝ) (y : n → ℝ),
    (∀ i, |x i| ≤ 1) → (∀ j, |y j| ≤ 1) →
      |bilinearObjective A x y| ≤ 1

/-- Absolute-value version of the homogeneous hypothesis.

**Lean implementation helper.** -/
def BilinearAbsHomogeneousBound {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) : Prop :=
  ∀ (x : m → ℝ) (y : n → ℝ),
    |bilinearObjective A x y| ≤
      Chapter1.linftyNorm x * Chapter1.linftyNorm y

/-- Negating the left vector family negates the bilinear objective.

**Lean implementation helper.** -/
private lemma bilinearObjective_neg_left
    {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (x : m → ℝ) (y : n → ℝ) :
    bilinearObjective A (-x) y = -bilinearObjective A x y := by
  simp [bilinearObjective, Finset.sum_neg_distrib]

/-- Scaling both vector families scales the bilinear objective by the product of the scalars.

**Lean implementation helper.** -/
private lemma bilinearObjective_smul_smul
    {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (a b : ℝ) (x : m → ℝ) (y : n → ℝ) :
    bilinearObjective A (a • x) (b • y) =
      (a * b) * bilinearObjective A x y := by
  simp only [bilinearObjective, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The bilinear objective is additive in the left vector family.

**Lean implementation helper.** -/
private lemma bilinearObjective_add_left
    {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (x z : m → ℝ) (y : n → ℝ) :
    bilinearObjective A (x + z) y =
      bilinearObjective A x y + bilinearObjective A z y := by
  simp only [bilinearObjective, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The bilinear objective is additive in the right vector family.

**Lean implementation helper.** -/
private lemma bilinearObjective_add_right
    {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (x : m → ℝ) (y z : n → ℝ) :
    bilinearObjective A x (y + z) =
      bilinearObjective A x y + bilinearObjective A x z := by
  simp only [bilinearObjective, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The bilinear objective is homogeneous in the left vector family.

**Lean implementation helper.** -/
private lemma bilinearObjective_smul_left
    {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (a : ℝ) (x : m → ℝ) (y : n → ℝ) :
    bilinearObjective A (a • x) y = a * bilinearObjective A x y := by
  simpa using bilinearObjective_smul_smul A a 1 x y

/-- The bilinear objective is homogeneous in the right vector family.

**Lean implementation helper.** -/
private lemma bilinearObjective_smul_right
    {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (a : ℝ) (x : m → ℝ) (y : n → ℝ) :
    bilinearObjective A x (a • y) = a * bilinearObjective A x y := by
  simpa [mul_comm] using bilinearObjective_smul_smul A 1 a x y

/-- With the right family fixed, the bilinear objective is convex in the left family.

**Lean implementation helper.** -/
private lemma convexOn_bilinear_left
    {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (y : n → ℝ) :
    ConvexOn ℝ univ (fun x : m → ℝ ↦ bilinearObjective A x y) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx z hz a b ha hb hab
  change bilinearObjective A (a • x + b • z) y ≤
    a * bilinearObjective A x y + b * bilinearObjective A z y
  rw [bilinearObjective_add_left, bilinearObjective_smul_left,
    bilinearObjective_smul_left]

/-- With the left family fixed, the bilinear objective is convex in the right family.

**Lean implementation helper.** -/
private lemma convexOn_bilinear_right
    {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (x : m → ℝ) :
    ConvexOn ℝ univ (fun y : n → ℝ ↦ bilinearObjective A x y) := by
  refine ⟨convex_univ, ?_⟩
  intro y hy z hz a b ha hb hab
  change bilinearObjective A x (a • y + b • z) ≤
    a * bilinearObjective A x y + b * bilinearObjective A x z
  rw [bilinearObjective_add_right, bilinearObjective_smul_right,
    bilinearObjective_smul_right]

/-- Characterizes `bilinear_sign` by the equivalent condition `cube`.

**Lean implementation helper.** -/
private lemma bilinear_sign_iff_cube
    {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) : BilinearSignBound A ↔ BilinearCubeBound A := by
  classical
  constructor
  · intro h x y hx hy
    have hxcube : x ∈ Chapter1.linftyUnitBall (ι := m) := by
      rw [Chapter1.linftyUnitBall_eq_cube]
      exact fun i _ ↦ (abs_le.mp (show |x i| ≤ 1 from hx i))
    have hxch : x ∈ convexHull ℝ (Chapter1.cubeVertices (ι := m)) := by
      rw [← Chapter1.linftyUnitBall_eq_convexHull_cubeVertices]
      exact hxcube
    rcases (convexOn_bilinear_left A y).exists_ge_of_mem_convexHull
        (fun _ hz ↦ Set.mem_univ _) hxch with ⟨sx, hsx, hxsx⟩
    have hycube : y ∈ Chapter1.linftyUnitBall (ι := n) := by
      rw [Chapter1.linftyUnitBall_eq_cube]
      exact fun j _ ↦ (abs_le.mp (show |y j| ≤ 1 from hy j))
    have hych : y ∈ convexHull ℝ (Chapter1.cubeVertices (ι := n)) := by
      rw [← Chapter1.linftyUnitBall_eq_convexHull_cubeVertices]
      exact hycube
    rcases (convexOn_bilinear_right A sx).exists_ge_of_mem_convexHull
        (fun _ hz ↦ Set.mem_univ _) hych with ⟨sy, hsy, hysy⟩
    have hsx' : ∀ i, sx i = -1 ∨ sx i = 1 := by
      simpa [Chapter1.cubeVertices] using hsx
    have hsy' : ∀ j, sy j = -1 ∨ sy j = 1 := by
      simpa [Chapter1.cubeVertices] using hsy
    exact hxsx.trans (hysy.trans (h sx sy (fun i ↦ by rcases hsx' i with hi | hi <;> simp [hi])
      (fun j ↦ by rcases hsy' j with hj | hj <;> simp [hj])))
  · intro h x y hx hy
    exact h x y (fun i ↦ (hx i).le) (fun j ↦ (hy j).le)

/-- Characterizes `bilinear_cube` by the equivalent condition `homogeneous`.

**Lean implementation helper.** -/
private lemma bilinear_cube_iff_homogeneous
    {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) : BilinearCubeBound A ↔ BilinearHomogeneousBound A := by
  classical
  constructor
  · intro h x y
    let nx := Chapter1.linftyNorm x
    let ny := Chapter1.linftyNorm y
    by_cases hx0 : nx = 0
    · have hx : x = 0 := Chapter1.linftyNorm_eq_zero_iff.mp hx0
      subst x
      simp [bilinearObjective, nx, hx0]
    by_cases hy0 : ny = 0
    · have hy : y = 0 := Chapter1.linftyNorm_eq_zero_iff.mp hy0
      subst y
      simp [bilinearObjective, ny, hy0]
    let xn : m → ℝ := nx⁻¹ • x
    let yn : n → ℝ := ny⁻¹ • y
    have hnx : 0 < nx := lt_of_le_of_ne (Chapter1.linftyNorm_nonneg x) (Ne.symm hx0)
    have hny : 0 < ny := lt_of_le_of_ne (Chapter1.linftyNorm_nonneg y) (Ne.symm hy0)
    have hxn : ∀ i, |xn i| ≤ 1 := by
      intro i
      simp only [xn, Pi.smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hnx]
      apply (inv_mul_le_one₀ hnx).2
      exact (Chapter1.linftyNorm_le_iff hnx.le).1 le_rfl i
    have hyn : ∀ j, |yn j| ≤ 1 := by
      intro j
      simp only [yn, Pi.smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hny]
      apply (inv_mul_le_one₀ hny).2
      exact (Chapter1.linftyNorm_le_iff hny.le).1 le_rfl j
    have hnorm := h xn yn hxn hyn
    have hscale := bilinearObjective_smul_smul A nx ny xn yn
    have hxx : nx • xn = x := by
      funext i
      simp [xn, hx0]
    have hyy : ny • yn = y := by
      funext j
      simp [yn, hy0]
    rw [hxx, hyy] at hscale
    rw [hscale]
    simpa [nx, ny] using
      (mul_le_mul_of_nonneg_left hnorm (mul_nonneg hnx.le hny.le))
  · intro h x y hx hy
    calc
      bilinearObjective A x y ≤
          Chapter1.linftyNorm x * Chapter1.linftyNorm y := h x y
      _ ≤ 1 * 1 := mul_le_mul (by
          rw [Chapter1.linftyNorm_le_iff zero_le_one]
          exact hx) (by
          rw [Chapter1.linftyNorm_le_iff zero_le_one]
          exact hy) (Chapter1.linftyNorm_nonneg y) zero_le_one
      _ = 1 := by ring

/-- Characterizes `bilinear_sign` by the equivalent condition `absSign`.

**Lean implementation helper.** -/
private lemma bilinear_sign_iff_absSign
    {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) : BilinearSignBound A ↔ BilinearAbsSignBound A := by
  constructor
  · intro h x y hx hy
    rw [abs_le]
    constructor
    · have hn := h (-x) y (by simpa using hx) hy
      rw [bilinearObjective_neg_left] at hn
      linarith
    · exact h x y hx hy
  · intro h x y hx hy
    exact (le_abs_self _).trans (h x y hx hy)

/-- Characterizes `bilinear_cube` by the equivalent condition `absCube`.

**Lean implementation helper.** -/
private lemma bilinear_cube_iff_absCube
    {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) : BilinearCubeBound A ↔ BilinearAbsCubeBound A := by
  constructor
  · intro h x y hx hy
    rw [abs_le]
    constructor
    · have hn := h (-x) y (by simpa using hx) hy
      rw [bilinearObjective_neg_left] at hn
      linarith
    · exact h x y hx hy
  · intro h x y hx hy
    exact (le_abs_self _).trans (h x y hx hy)

/-- Characterizes `bilinear_homogeneous` by the equivalent condition `absHomogeneous`.

**Lean implementation helper.** -/
private lemma bilinear_homogeneous_iff_absHomogeneous
    {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) :
    BilinearHomogeneousBound A ↔ BilinearAbsHomogeneousBound A := by
  constructor
  · intro h x y
    rw [abs_le]
    constructor
    · have hn := h (-x) y
      have hnormneg : Chapter1.linftyNorm (-x) = Chapter1.linftyNorm x := by
        simpa using Chapter1.linftyNorm_smul (-1 : ℝ) x
      rw [bilinearObjective_neg_left, hnormneg] at hn
      linarith
    · exact h x y
  · intro h x y
    exact (le_abs_self _).trans (h x y)

end HDP

namespace HDP.Chapter3

/-- The sign-cube,
continuous-cube, homogeneous, and their absolute-value formulations are all
equivalent.

**Book Exercise 3.47--3.48.** -/
theorem exercise_3_47 {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) :
    (HDP.BilinearSignBound A ↔ HDP.BilinearCubeBound A) ∧
    (HDP.BilinearCubeBound A ↔ HDP.BilinearHomogeneousBound A) ∧
    (HDP.BilinearSignBound A ↔ HDP.BilinearAbsSignBound A) ∧
    (HDP.BilinearCubeBound A ↔ HDP.BilinearAbsCubeBound A) ∧
    (HDP.BilinearHomogeneousBound A ↔ HDP.BilinearAbsHomogeneousBound A) := by
  exact ⟨HDP.bilinear_sign_iff_cube A, HDP.bilinear_cube_iff_homogeneous A,
    HDP.bilinear_sign_iff_absSign A, HDP.bilinear_cube_iff_absCube A,
    HDP.bilinear_homogeneous_iff_absHomogeneous A⟩

/-- The sharpened truncation conclusion `K ≤ 14.1`.
The formal proof uses the stronger Krivine estimate `K ≤ 1.783`, already
proved by the complete rounding chain.

**Book Exercise 3.47--3.48.** -/
theorem exercise_3_48
    {m n κ : Type*} [Fintype m] [Fintype n] [Fintype κ]
    (A : Matrix m n ℝ)
    (hA : ∀ (x : m → ℝ) (y : n → ℝ),
      (∀ i, x i = 1 ∨ x i = -1) → (∀ j, y j = 1 ∨ y j = -1) →
        HDP.bilinearObjective A x y ≤ 1)
    (X : m → EuclideanSpace ℝ κ) (Y : n → EuclideanSpace ℝ κ)
    (hX : ∀ i, ‖X i‖ = 1) (hY : ∀ j, ‖Y j‖ = 1) :
    |HDP.bilinearVectorObjective A X Y| ≤ (141 / 10 : ℝ) := by
  exact (grothendieck_inequality_1783_1000 A hA X Y hX hY).trans (by norm_num)

/-- For a symmetric coefficient matrix, swapping the two vector families leaves the bilinear objective unchanged.

**Lean implementation helper.** -/
private lemma bilinearObjective_swap_of_isSymm
    {n : Type*} [Fintype n] (A : Matrix n n ℝ) (hA : A.IsSymm)
    (x y : n → ℝ) :
    HDP.bilinearObjective A x y = HDP.bilinearObjective A y x := by
  classical
  simp only [HDP.bilinearObjective]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hA.apply]
  ring

/-- Identifies `quadraticObjective` with `bilinearObjective`.

**Lean implementation helper.** -/
private lemma quadraticObjective_eq_bilinearObjective
    {n : Type*} [Fintype n] (A : Matrix n n ℝ) (x : n → ℝ) :
    HDP.quadraticObjective A x = HDP.bilinearObjective A x x := rfl

/-- PSD quadratic Grothendieck consequences.

**Book Exercise 3.49.** -/
theorem exercise_3_49a
    {n : Type*} [Fintype n] (A : Matrix n n ℝ) (hA : A.IsSymm)
    (x y : n → ℝ) :
    HDP.bilinearObjective A x y =
      HDP.quadraticObjective A ((2 : ℝ)⁻¹ • (x + y)) -
        HDP.quadraticObjective A ((2 : ℝ)⁻¹ • (x - y)) := by
  rw [quadraticObjective_eq_bilinearObjective,
    quadraticObjective_eq_bilinearObjective]
  rw [HDP.bilinearObjective_smul_smul, HDP.bilinearObjective_smul_smul]
  rw [HDP.bilinearObjective_add_left, HDP.bilinearObjective_add_right,
    HDP.bilinearObjective_add_right]
  have hsub : x - y = x + (-y) := sub_eq_add_neg x y
  rw [hsub, HDP.bilinearObjective_add_left,
    HDP.bilinearObjective_add_right, HDP.bilinearObjective_add_right]
  have hswap := bilinearObjective_swap_of_isSymm A hA x y
  have hnegright : HDP.bilinearObjective A x (-y) =
      -HDP.bilinearObjective A x y := by
    simpa using HDP.bilinearObjective_smul_right A (-1 : ℝ) x y
  have hnegneg : HDP.bilinearObjective A (-y) (-y) =
      HDP.bilinearObjective A y y := by
    simpa using HDP.bilinearObjective_smul_smul A (-1 : ℝ) (-1 : ℝ) y y
  rw [hnegright, hnegneg]
  have hnegl : HDP.bilinearObjective A (-y) x =
      -HDP.bilinearObjective A y x := by
    simpa using HDP.bilinearObjective_smul_left A (-1 : ℝ) y x
  rw [hnegl, ← hswap]
  ring

/-- A positive-semidefinite coefficient matrix gives a nonnegative quadratic objective.

**Lean implementation helper.** -/
private lemma quadraticObjective_nonneg_of_posSemidef
    {n : Type*} [Fintype n] (A : Matrix n n ℝ) (hA : A.PosSemidef)
    (x : n → ℝ) : 0 ≤ HDP.quadraticObjective A x := by
  have h := hA.dotProduct_mulVec_nonneg x
  calc
    0 ≤ ∑ i, x i * ∑ j, A i j * x j := by
      simpa [dotProduct, Matrix.mulVec] using h
    _ = HDP.quadraticObjective A x := by
      simp only [HDP.quadraticObjective]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring

/-- Quadratic Grothendieck for a positive
semidefinite matrix. The proved constant is in fact `K`, hence implies the
source's stated `2K`.

**Book Exercise 3.49.** -/
theorem exercise_3_49b
    {n κ : Type*} [Fintype n] [Fintype κ]
    (A : Matrix n n ℝ) (hA : A.PosSemidef)
    (hsign : ∀ x : n → ℝ, (∀ i, x i = 1 ∨ x i = -1) →
      HDP.quadraticObjective A x ≤ 1)
    (U V : n → EuclideanSpace ℝ κ)
    (hU : ∀ i, ‖U i‖ = 1) (hV : ∀ j, ‖V j‖ = 1) :
    |HDP.bilinearVectorObjective A U V| ≤ 2 * HDP.krivineConstant := by
  have hbilin : ∀ (x : n → ℝ) (y : n → ℝ),
      (∀ i, x i = 1 ∨ x i = -1) → (∀ j, y j = 1 ∨ y j = -1) →
        HDP.bilinearObjective A x y ≤ 1 := by
    intro x y hx hy
    have hnonneg := quadraticObjective_nonneg_of_posSemidef A hA (x - y)
    have hpolar := exercise_3_49a A
      (Matrix.isHermitian_iff_isSymm.mp hA.isHermitian) x y
    have hqx := hsign x hx
    have hqy := hsign y hy
    have hexpand : HDP.quadraticObjective A (x - y) =
        HDP.quadraticObjective A x + HDP.quadraticObjective A y -
          2 * HDP.bilinearObjective A x y := by
      rw [quadraticObjective_eq_bilinearObjective]
      have hsub : x - y = x + (-y) := sub_eq_add_neg x y
      rw [hsub, HDP.bilinearObjective_add_left,
        HDP.bilinearObjective_add_right, HDP.bilinearObjective_add_right]
      have hsym := bilinearObjective_swap_of_isSymm A
        (Matrix.isHermitian_iff_isSymm.mp hA.isHermitian) x y
      have h1 : HDP.bilinearObjective A x (-y) =
          -HDP.bilinearObjective A x y := by
        simpa using HDP.bilinearObjective_smul_right A (-1 : ℝ) x y
      have h2 : HDP.bilinearObjective A (-y) x =
          -HDP.bilinearObjective A y x := by
        simpa using HDP.bilinearObjective_smul_left A (-1 : ℝ) y x
      have h3 : HDP.bilinearObjective A (-y) (-y) =
          HDP.bilinearObjective A y y := by
        simpa using HDP.bilinearObjective_smul_smul A (-1 : ℝ) (-1 : ℝ) y y
      rw [h1, h2, h3, ← hsym,
        ← quadraticObjective_eq_bilinearObjective A x,
        ← quadraticObjective_eq_bilinearObjective A y]
      ring
    rw [hexpand] at hnonneg
    linarith
  have hK := grothendieck_inequality_krivine A hbilin U V hU hV
  have hK0 : 0 ≤ HDP.krivineConstant := by
    exact (div_pos Real.pi_pos (mul_pos (by norm_num) HDP.krivineC_pos)).le
  exact hK.trans (by linarith)

/-- Defines `exercise349Unit`, the exercise349 unit used in the surrounding construction.

**Lean implementation helper.** -/
private noncomputable def exercise349Unit : EuclideanSpace ℝ (Fin 1) :=
  WithLp.toLp 2 (fun _ ↦ (1 : ℝ))

/-- The identity `norm_exercise349Unit` states that the one-dimensional vector `exercise349Unit` has norm one.

**Lean implementation helper.** -/
private lemma norm_exercise349Unit : ‖exercise349Unit‖ = 1 := by
  rw [exercise349Unit, PiLp.norm_eq_sum]
  · norm_num
  · norm_num

/-- The inner product with the negated Exercise 3.49 unit vector is the negative of the original inner product.

**Lean implementation helper.** -/
private lemma inner_exercise349Unit_neg :
    inner ℝ exercise349Unit (-exercise349Unit) = -1 := by
  rw [inner_neg_right, real_inner_self_eq_norm_sq, norm_exercise349Unit]
  norm_num

/-- Without positive semidefiniteness the quadratic
sign hypothesis need not control the bilinear vector relaxation. A negative
one-dimensional quadratic form gives an explicit counterexample.

**Book Exercise 3.49.** -/
theorem exercise_3_49c :
    ∃ A : Matrix (Fin 1) (Fin 1) ℝ,
      A.IsSymm ∧ ¬ A.PosSemidef ∧
      (∀ x : Fin 1 → ℝ, (∀ i, x i = 1 ∨ x i = -1) →
        HDP.quadraticObjective A x ≤ 1) ∧
      ∃ (U V : Fin 1 → EuclideanSpace ℝ (Fin 1)),
        (∀ i, ‖U i‖ = 1) ∧ (∀ i, ‖V i‖ = 1) ∧
          2 * HDP.krivineConstant < |HDP.bilinearVectorObjective A U V| := by
  let A : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ ↦ -4
  let U : Fin 1 → EuclideanSpace ℝ (Fin 1) := fun _ ↦ exercise349Unit
  let V : Fin 1 → EuclideanSpace ℝ (Fin 1) := fun _ ↦ -exercise349Unit
  refine ⟨A, ?_, ?_, ?_, U, V, ?_, ?_, ?_⟩
  · rw [Matrix.IsSymm.ext_iff]
    intro i j
    rfl
  · intro hpsd
    have hn := hpsd.dotProduct_mulVec_nonneg (fun _ : Fin 1 ↦ (1 : ℝ))
    norm_num [A, dotProduct, Matrix.mulVec] at hn
  · intro x hx
    have hq : HDP.quadraticObjective A x = -4 * x 0 ^ 2 := by
      simp [HDP.quadraticObjective, A]
      ring
    rw [hq]
    nlinarith [sq_nonneg (x 0)]
  · intro i
    exact norm_exercise349Unit
  · intro i
    simp [V, norm_exercise349Unit]
  · have hobj : HDP.bilinearVectorObjective A U V = 4 := by
      rw [HDP.bilinearVectorObjective, Fin.sum_univ_one, Fin.sum_univ_one,
        inner_exercise349Unit_neg]
      norm_num [A, U, V]
    rw [hobj, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    nlinarith [HDP.krivineConstant_le_1783_1000]

/-- Coordinatewise convexity on the finite cube, the hypothesis in Exercise
3.50(a).

**Book Exercise 3.50(a).** -/
noncomputable def SeparatelyConvexOnCube {n : Type*} [Fintype n]
    (f : (n → ℝ) → ℝ) : Prop := by
  classical
  exact ∀ (x : n → ℝ), (∀ i, |x i| ≤ 1) → ∀ i,
    ConvexOn ℝ (Icc (-1 : ℝ) 1) (fun t ↦ f (Function.update x i t))

/-- A separately convex function on a finite cube attains at least any given value at some cube vertex.

**Lean implementation helper.** -/
private theorem separatelyConvexOnCube_exists_vertex_on_finset
    {n : Type*} [Fintype n] (f : (n → ℝ) → ℝ)
    (hf : SeparatelyConvexOnCube f)
    (x : n → ℝ) (hx : ∀ i, |x i| ≤ 1) (s : Finset n) :
    ∃ y : n → ℝ,
      (∀ i ∈ s, |y i| = 1) ∧
      (∀ i ∉ s, y i = x i) ∧
      (∀ i, |y i| ≤ 1) ∧ f x ≤ f y := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨x, by simp, by simp, hx, le_rfl⟩
  | @insert i s his ih =>
      rcases ih with ⟨y, hysign, hyoutside, hycube, hxy⟩
      let ym : n → ℝ := Function.update y i (-1)
      let yp : n → ℝ := Function.update y i 1
      have hyIcc : y i ∈ Icc (-1 : ℝ) 1 := abs_le.mp (hycube i)
      have hsection := (hf y hycube i).le_max_of_mem_Icc
        (by norm_num : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1)
        (by norm_num : (1 : ℝ) ∈ Icc (-1 : ℝ) 1) hyIcc
      have hself : Function.update y i (y i) = y := by
        funext j
        by_cases hji : j = i
        · subst j; simp
        · simp [hji]
      rw [hself] at hsection
      change f y ≤ max (f ym) (f yp) at hsection
      rcases le_total (f ym) (f yp) with hmp | hpm
      · have hyz : f y ≤ f yp := by simpa [max_eq_right hmp] using hsection
        refine ⟨yp, ?_, ?_, ?_, hxy.trans hyz⟩
        · intro j hj
          rcases Finset.mem_insert.mp hj with rfl | hjs
          · simp [yp]
          · have hji : j ≠ i := fun h ↦ his (h ▸ hjs)
            simpa [yp, hji] using hysign j hjs
        · intro j hj
          have hji : j ≠ i := fun h ↦ by subst j; simp at hj
          have hjs : j ∉ s := fun h ↦ hj (Finset.mem_insert_of_mem h)
          simpa [yp, hji] using hyoutside j hjs
        · intro j
          by_cases hji : j = i
          · subst j; simp [yp]
          · simpa [yp, hji] using hycube j
      · have hyz : f y ≤ f ym := by simpa [max_eq_left hpm] using hsection
        refine ⟨ym, ?_, ?_, ?_, hxy.trans hyz⟩
        · intro j hj
          rcases Finset.mem_insert.mp hj with rfl | hjs
          · simp [ym]
          · have hji : j ≠ i := fun h ↦ his (h ▸ hjs)
            simpa [ym, hji] using hysign j hjs
        · intro j hj
          have hji : j ≠ i := fun h ↦ by subst j; simp at hj
          have hjs : j ∉ s := fun h ↦ hj (Finset.mem_insert_of_mem h)
          simpa [ym, hji] using hyoutside j hjs
        · intro j
          by_cases hji : j = i
          · subst j; simp [ym]
          · simpa [ym, hji] using hycube j

/-- Every value of a separately convex function on
the cube is dominated by its value at a vertex. Since the vertex set is
finite, this is the maximum-attainment statement in a supremum-safe form.

**Book Exercise 3.50.** -/
theorem exercise_3_50a
    {n : Type*} [Fintype n] (f : (n → ℝ) → ℝ)
    (hf : SeparatelyConvexOnCube f)
    (x : n → ℝ) (hx : ∀ i, |x i| ≤ 1) :
    ∃ y : n → ℝ, (∀ i, |y i| = 1) ∧ f x ≤ f y := by
  classical
  rcases separatelyConvexOnCube_exists_vertex_on_finset f hf x hx Finset.univ with
    ⟨y, hy, hout, hycube, hxy⟩
  exact ⟨y, fun i ↦ hy i (Finset.mem_univ i), hxy⟩

/-- Updating one coordinate of the quadratic objective produces an affine function of that coordinate.

**Lean implementation helper.** -/
private lemma quadraticObjective_update_affine
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hdiag : ∀ i, A i i = 0)
    (x : n → ℝ) (i : n) (t : ℝ) :
    let z := Function.update x i 0
    let e : n → ℝ := fun j ↦ if j = i then 1 else 0
    HDP.quadraticObjective A (Function.update x i t) =
      HDP.quadraticObjective A z +
        t * (HDP.bilinearObjective A z e + HDP.bilinearObjective A e z) := by
  classical
  dsimp only
  let z := Function.update x i 0
  let e : n → ℝ := fun j ↦ if j = i then 1 else 0
  have hup : Function.update x i t = z + t • e := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [z, e]
    · simp [z, e, hji]
  have hezero : HDP.bilinearObjective A e e = 0 := by
    classical
    simp [HDP.bilinearObjective, e, hdiag i]
  rw [quadraticObjective_eq_bilinearObjective, hup,
    HDP.bilinearObjective_add_left, HDP.bilinearObjective_add_right,
    HDP.bilinearObjective_add_right, HDP.bilinearObjective_smul_right,
    HDP.bilinearObjective_smul_left, HDP.bilinearObjective_smul_left,
    HDP.bilinearObjective_smul_right, hezero,
    ← quadraticObjective_eq_bilinearObjective A z]
  ring

/-- The absolute quadratic objective is separately convex on the coordinate cube.

**Lean implementation helper.** -/
private theorem abs_quadratic_separatelyConvexOnCube
    {n : Type*} [Fintype n]
    (A : Matrix n n ℝ) (hdiag : ∀ i, A i i = 0) :
    SeparatelyConvexOnCube (fun x ↦ |HDP.quadraticObjective A x|) := by
  classical
  intro x hx i
  let z := Function.update x i 0
  let e : n → ℝ := fun j ↦ if j = i then 1 else 0
  let c := HDP.quadraticObjective A z
  let d := HDP.bilinearObjective A z e + HDP.bilinearObjective A e z
  have hform (t : ℝ) : HDP.quadraticObjective A (Function.update x i t) = c + t * d := by
    simpa [z, e, c, d] using quadraticObjective_update_affine A hdiag x i t
  refine ⟨convex_Icc _ _, ?_⟩
  intro a ha b hb p q hp hq hpq
  change |HDP.quadraticObjective A (Function.update x i (p * a + q * b))| ≤
    p * |HDP.quadraticObjective A (Function.update x i a)| +
      q * |HDP.quadraticObjective A (Function.update x i b)|
  rw [hform, hform, hform]
  calc
    |c + (p * a + q * b) * d| =
        |p * (c + a * d) + q * (c + b * d)| := by
          congr 1
          rw [show q = 1 - p by linarith]
          ring
    _ ≤ |p * (c + a * d)| + |q * (c + b * d)| := abs_add_le _ _
    _ = p * |c + a * d| + q * |c + b * d| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hp, abs_of_nonneg hq]

/-- The printed nonsymmetric statement
is false. For a symmetric diagonal-free matrix, the absolute quadratic form
is separately convex, so the sign hypothesis extends to the whole cube and
polarization reduces the result to bilinear Grothendieck.

**Book Exercise 3.50.** -/
theorem exercise_3_50b
    {n κ : Type*} [Fintype n] [Fintype κ]
    (A : Matrix n n ℝ) (hA : A.IsSymm) (hdiag : ∀ i, A i i = 0)
    (hsign : ∀ x : n → ℝ, (∀ i, x i = 1 ∨ x i = -1) →
      |HDP.quadraticObjective A x| ≤ 1)
    (U V : n → EuclideanSpace ℝ κ)
    (hU : ∀ i, ‖U i‖ = 1) (hV : ∀ j, ‖V j‖ = 1) :
    |HDP.bilinearVectorObjective A U V| ≤ 2 * HDP.krivineConstant := by
  have hcube : ∀ x : n → ℝ, (∀ i, |x i| ≤ 1) →
      |HDP.quadraticObjective A x| ≤ 1 := by
    intro x hx
    rcases exercise_3_50a (fun z ↦ |HDP.quadraticObjective A z|)
        (abs_quadratic_separatelyConvexOnCube A hdiag) x hx with ⟨s, hs, hxs⟩
    apply hxs.trans
    apply hsign s
    intro i
    rcases ((abs_eq zero_le_one).mp (hs i)) with hi | hi
    · exact Or.inl hi
    · exact Or.inr hi
  have hbilin : ∀ (x : n → ℝ) (y : n → ℝ),
      (∀ i, x i = 1 ∨ x i = -1) → (∀ j, y j = 1 ∨ y j = -1) →
        |HDP.bilinearObjective A x y| ≤ 2 := by
    intro x y hx hy
    let xp : n → ℝ := (2 : ℝ)⁻¹ • (x + y)
    let xm : n → ℝ := (2 : ℝ)⁻¹ • (x - y)
    have hxp : ∀ i, |xp i| ≤ 1 := by
      intro i
      dsimp [xp]
      rw [abs_mul]
      have htri := abs_add_le (x i) (y i)
      have hxi : |x i| = 1 := by rcases hx i with hi | hi <;> simp [hi]
      have hyi : |y i| = 1 := by rcases hy i with hi | hi <;> simp [hi]
      norm_num at htri ⊢
      linarith
    have hxm : ∀ i, |xm i| ≤ 1 := by
      intro i
      dsimp [xm]
      rw [abs_mul]
      have htri := abs_sub (x i) (y i)
      have hxi : |x i| = 1 := by rcases hx i with hi | hi <;> simp [hi]
      have hyi : |y i| = 1 := by rcases hy i with hi | hi <;> simp [hi]
      norm_num at htri ⊢
      linarith
    have hp := hcube xp hxp
    have hm := hcube xm hxm
    have hpol := exercise_3_49a A hA x y
    change HDP.bilinearObjective A x y =
      HDP.quadraticObjective A xp - HDP.quadraticObjective A xm at hpol
    rw [hpol]
    exact (abs_sub _ _).trans (by linarith)
  have h := grothendieck_inequality A 2 hbilin U V hU hV
  simpa [mul_comm] using h

/-- A finite real Gram matrix is symmetric and
positive semidefinite.

**Book Exercise 3.51.** -/
theorem exercise_3_51a {n κ : Type*} [Finite n] [Fintype κ]
    (v : n → EuclideanSpace ℝ κ) :
    (Matrix.gram ℝ v).IsSymm ∧ (Matrix.gram ℝ v).PosSemidef := by
  classical
  letI := Fintype.ofFinite n
  have hpsd := gram_posSemidef v
  exact ⟨Matrix.isHermitian_iff_isSymm.mp hpsd.isHermitian, hpsd⟩

/-- Conversely, every finite real symmetric positive
semidefinite matrix is a Gram matrix in a finite-dimensional Euclidean space.

**Book Exercise 3.51.** -/
theorem exercise_3_51b {n : Type*} [Finite n]
    {M : Matrix n n ℝ} (hM : M.IsSymm ∧ M.PosSemidef) :
    ∃ (k : ℕ) (v : n → EuclideanSpace ℝ (Fin k)), Matrix.gram ℝ v = M := by
  classical
  letI := Fintype.ofFinite n
  exact exists_gram_of_posSemidef hM.2

/-- The
unit-vector program for an `m × n` matrix and its block-matrix SDP have
exactly the same feasible objective values. In the forward direction the
ambient space `m ⊕ n` is already large enough; in the reverse direction the
Gram factorization supplies a finite Euclidean space.

**Book Exercise 3.52.** -/
theorem exercise_3_52a {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) :
    (∀ (X : m → EuclideanSpace ℝ (m ⊕ n))
        (Y : n → EuclideanSpace ℝ (m ⊕ n)),
      (∀ i, ‖X i‖ = 1) → (∀ j, ‖Y j‖ = 1) →
      ∃ Z : Matrix (m ⊕ n) (m ⊕ n) ℝ,
        Z.PosSemidef ∧ (∀ p, Z p p = 1) ∧
          HDP.bilinearVectorObjective A X Y =
            HDP.matrixInner (HDP.bilinearSDPMatrix A) Z) ∧
    (∀ Z : Matrix (m ⊕ n) (m ⊕ n) ℝ,
      Z.PosSemidef → (∀ p, Z p p = 1) →
      ∃ (k : ℕ) (X : m → EuclideanSpace ℝ (Fin k))
          (Y : n → EuclideanSpace ℝ (Fin k)),
        (∀ i, ‖X i‖ = 1) ∧ (∀ j, ‖Y j‖ = 1) ∧
          HDP.matrixInner (HDP.bilinearSDPMatrix A) Z =
            HDP.bilinearVectorObjective A X Y) := by
  classical
  constructor
  · intro X Y hX hY
    have hw : ∀ p : m ⊕ n, ‖Sum.elim X Y p‖ = 1 := by
      rintro (i | j)
      · exact hX i
      · exact hY j
    rcases (relaxation_is_sdp (HDP.bilinearSDPMatrix A)).1
        (Sum.elim X Y) hw with ⟨Z, hZ, hdiag, hobj⟩
    refine ⟨Z, hZ, hdiag, ?_⟩
    rw [← HDP.vectorSDPObjective_bilinearSDPMatrix A X Y]
    exact hobj
  · intro Z hZ hdiag
    rcases (relaxation_is_sdp (HDP.bilinearSDPMatrix A)).2 Z hZ hdiag with
      ⟨k, w, hw, hobj⟩
    let X : m → EuclideanSpace ℝ (Fin k) := fun i => w (Sum.inl i)
    let Y : n → EuclideanSpace ℝ (Fin k) := fun j => w (Sum.inr j)
    refine ⟨k, X, Y, ?_, ?_, ?_⟩
    · intro i
      exact hw (Sum.inl i)
    · intro j
      exact hw (Sum.inr j)
    · rw [← HDP.vectorSDPObjective_bilinearSDPMatrix A X Y]
      have hXY : Sum.elim X Y = w := by
        funext p
        cases p <;> rfl
      rw [hXY]
      exact hobj

/-- Any bound
`C` for the bilinear integer program controls every feasible vector-SDP value
within Krivine's absolute constant.

**Book Exercise 3.52.** -/
theorem exercise_3_52b
    {m n κ : Type*} [Fintype m] [Fintype n] [Fintype κ]
    (A : Matrix m n ℝ) (C : ℝ)
    (hinteger : ∀ (x : m → ℝ) (y : n → ℝ),
      (∀ i, x i = 1 ∨ x i = -1) → (∀ j, y j = 1 ∨ y j = -1) →
        |HDP.bilinearObjective A x y| ≤ C)
    (X : m → EuclideanSpace ℝ κ) (Y : n → EuclideanSpace ℝ κ)
    (hX : ∀ i, ‖X i‖ = 1) (hY : ∀ j, ‖Y j‖ = 1) :
    |HDP.bilinearVectorObjective A X Y| ≤ HDP.krivineConstant * C :=
  bilinear_sdp_relaxation_approximation A C hinteger X Y hX hY

end HDP.Chapter3

end Source_15_GrothendieckConsequences

/-! ## Material formerly in `25_Kernels.lean` -/

section Source_25_Kernels

/-!
# Kernels and reproducing kernel Hilbert spaces

The central interface is Mathlib's `RKHS.OfKernel`: an operator-valued
positive-semidefinite kernel generates a complete RKHS whose reproducing
kernel is definitionally the input kernel.
-/

open scoped BigOperators RealInnerProductSpace

namespace HDP

variable {ι : Type*} [Fintype ι]

/-- Add a constant coordinate to a finite-dimensional feature vector.

**Lean implementation helper.** -/
noncomputable def affineFeature (c : ℝ) (x : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ (Option ι) :=
  WithLp.toLp 2 fun i => i.elim (Real.sqrt c) x

/-- The affine feature map realizes the kernel consisting of a constant plus the original inner product.

**Lean implementation helper.** -/
theorem inner_affineFeature {c : ℝ} (hc : 0 ≤ c)
    (x y : EuclideanSpace ℝ ι) :
    inner ℝ (affineFeature c x) (affineFeature c y) =
      c + inner ℝ x y := by
  simp only [affineFeature, PiLp.inner_apply]
  simp [Real.mul_self_sqrt hc]

/-- Feature map for the inhomogeneous polynomial kernel
`(c + ⟪x,y⟫)^d`, valid for `c ≥ 0`.

**Book Section 3.5.** -/
noncomputable def polynomialFeature
    (c : ℝ) (d : ℕ) (x : EuclideanSpace ℝ ι) :
    TensorPowerSpace (Option ι) d :=
  tensorPowerFeature d (affineFeature c x)

/-- The polynomial feature map realizes the corresponding polynomial kernel.

**Lean implementation helper.** -/
theorem inner_polynomialFeature {c : ℝ} (hc : 0 ≤ c) (d : ℕ)
    (x y : EuclideanSpace ℝ ι) :
    inner ℝ (polynomialFeature c d x) (polynomialFeature c d y) =
      (c + inner ℝ x y) ^ d := by
  simp only [polynomialFeature]
  rw [inner_tensorPowerFeature, inner_affineFeature hc]

/-- Coefficients of the exponential tensor feature used for the Gaussian
kernel with bandwidth `σ`.

**Lean implementation helper.** -/
noncomputable def gaussianKernelCoefficients (σ : ℝ) (k : ℕ) : ℝ :=
  (1 / σ ^ 2) ^ k / k.factorial

/-- The absolute power series formed from the Gaussian-kernel coefficients is summable.

**Lean implementation helper.** -/
lemma gaussianKernelCoefficients_absolutePowerSummable {σ : ℝ} (hσ : σ ≠ 0) :
    AbsolutePowerSummable (gaussianKernelCoefficients σ) := by
  intro r
  have hσ2 : 0 < σ ^ 2 := sq_pos_of_ne_zero hσ
  have hsum := Real.summable_pow_div_factorial (|r| / σ ^ 2)
  convert hsum using 1
  ext k
  rw [gaussianKernelCoefficients]
  have ha : 0 ≤ (1 / σ ^ 2) ^ k / (k.factorial : ℝ) := by positivity
  rw [abs_of_nonneg ha]
  field_simp
  ring

/-- Explicit Hilbert-space feature map for the Gaussian kernel.

**Book Section 3.5.** -/
noncomputable def gaussianKernelFeature (σ : ℝ) (hσ : σ ≠ 0)
    (x : EuclideanSpace ℝ ι) : AnalyticFeatureSpace ι :=
  Real.exp (-‖x‖ ^ 2 / (2 * σ ^ 2)) •
    analyticFeature (gaussianKernelCoefficients σ)
      (gaussianKernelCoefficients_absolutePowerSummable hσ) x

/-- The Gaussian-kernel coefficient series sums to the exponential normalization used by the feature map.

**Lean implementation helper.** -/
lemma tsum_gaussianKernelCoefficients (σ t : ℝ) :
    ∑' k : ℕ, gaussianKernelCoefficients σ k * t ^ k =
      Real.exp (t / σ ^ 2) := by
  have h := NormedSpace.expSeries_div_hasSum_exp (t / σ ^ 2)
  rw [Real.exp_eq_exp_ℝ, ← h.tsum_eq]
  apply tsum_congr
  intro k
  simp only [gaussianKernelCoefficients, div_eq_mul_inv, one_mul]
  rw [mul_pow]
  ring

/-- Inner products of Gaussian-kernel features are the Gaussian radial
kernel, with the exact bandwidth normalization used in the source.

**Lean implementation helper.** -/
theorem inner_gaussianKernelFeature {σ : ℝ} (hσ : σ ≠ 0)
    (x y : EuclideanSpace ℝ ι) :
    inner ℝ (gaussianKernelFeature σ hσ x) (gaussianKernelFeature σ hσ y) =
      Real.exp (-‖x - y‖ ^ 2 / (2 * σ ^ 2)) := by
  unfold gaussianKernelFeature
  rw [inner_smul_left, inner_smul_right, RCLike.conj_to_real]
  rw [inner_analyticFeature_of_nonneg]
  · rw [tsum_gaussianKernelCoefficients]
    rw [← Real.exp_add, ← Real.exp_add]
    rw [norm_sub_sq_real]
    congr 1
    field_simp
    ring
  · intro k
    dsimp [gaussianKernelCoefficients]
    positivity

end HDP

namespace HDP.Chapter3

/-- A positive-semidefinite operator-valued kernel generates a completed
reproducing-kernel Hilbert space whose kernel is exactly the original one.
The `Fact` argument is Mathlib's packaging of the required positive
semidefiniteness.

**Book Equation (3.38).** -/
theorem moore_aronszajn
    {𝕜 X V : Type*} [RCLike 𝕜]
    [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]
    (K : Matrix X X (V →L[𝕜] V)) [Fact K.PosSemidef] :
    RKHS.kernel (RKHS.OfKernel K) = K :=
  RKHS.OfKernel.kernel_ofKernel

/-- The source's polynomial kernel is realized by an explicit finite tensor
feature map.

**Book Section 3.5.** -/
theorem polynomial_kernel_feature
    {ι : Type*} [Fintype ι] {c : ℝ} (hc : 0 ≤ c) (d : ℕ)
    (x y : EuclideanSpace ℝ ι) :
    inner ℝ (HDP.polynomialFeature c d x) (HDP.polynomialFeature c d y) =
      (c + inner ℝ x y) ^ d :=
  HDP.inner_polynomialFeature hc d x y

/-- The source's Gaussian kernel is realized by the explicit infinite tensor
feature map.

**Book Section 3.5.** -/
theorem gaussian_kernel_feature
    {ι : Type*} [Fintype ι] {σ : ℝ} (hσ : σ ≠ 0)
    (x y : EuclideanSpace ℝ ι) :
    inner ℝ (HDP.gaussianKernelFeature σ hσ x)
        (HDP.gaussianKernelFeature σ hσ y) =
      Real.exp (-‖x - y‖ ^ 2 / (2 * σ ^ 2)) :=
  HDP.inner_gaussianKernelFeature hσ x y

end HDP.Chapter3

end Source_25_Kernels

/-! ## Material formerly in `26_SubGaussianMatrices.lean` -/

section Source_26_SubGaussianMatrices

/-!
# Fixed bilinear forms of subgaussian random matrices

This core module contains the row-wise subgaussian estimate needed in later
chapters. Its source is Book Exercise 3.34; it lives here so no core module ever
imports an exercise leaf.
-/

open MeasureTheory ProbabilityTheory Real Filter
open scoped BigOperators ENNReal NNReal RealInnerProductSpace

namespace HDP.Chapter3

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- For
independent centered subgaussian rows, every fixed bilinear form is
subgaussian. The explicit absolute constant inherited from Chapter 2 is
`√30`. This is the unique authoritative declaration.

**Book Exercise 3.34.** -/
theorem exercise_3_34 [IsProbabilityMeasure μ]
    {m n : ℕ}
    (A : Fin m → Ω → EuclideanSpace ℝ (Fin n))
    (hAm : ∀ i v, AEMeasurable (fun ω => inner ℝ (A i ω) v) μ)
    (hsub : ∀ i, HDP.SubGaussianVector (A i) μ)
    (hmean : ∀ i v, ∫ ω, inner ℝ (A i ω) v ∂μ = 0)
    (hindep : iIndepFun A μ)
    (hbounded : ∀ i, BddAbove {r : ℝ |
      ∃ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 ∧
        r = HDP.psi2Norm (fun ω => inner ℝ (A i ω) w) μ})
    {K : ℝ} (hK : 0 ≤ K)
    (hpsi : ∀ i, HDP.psi2NormVector (A i) μ ≤ K)
    (u : EuclideanSpace ℝ (Fin m))
    (v : EuclideanSpace ℝ (Fin n)) :
    let S : Ω → ℝ := fun ω => ∑ i, u i * inner ℝ (A i ω) v
    HDP.SubGaussian S μ ∧
      HDP.psi2Norm S μ ≤ Real.sqrt 30 * ‖u‖ * ‖v‖ * K := by
  let Y : Fin m → Ω → ℝ := fun i ω => u i * inner ℝ (A i ω) v
  have hYm : ∀ i, AEMeasurable (Y i) μ := fun i =>
    (hAm i v).const_mul (u i)
  have hYsub : ∀ i, HDP.SubGaussian (Y i) μ := fun i =>
    (hsub i v).const_mul (u i)
  have hYmean : ∀ i, ∫ ω, Y i ω ∂μ = 0 := by
    intro i
    rw [show Y i = fun ω => u i * inner ℝ (A i ω) v by rfl,
      integral_const_mul, hmean i v, mul_zero]
  have hYindep : iIndepFun Y μ :=
    hindep.comp (fun i x => u i * inner ℝ x v) (fun i => by fun_prop)
  have hs := HDP.psi2Norm_sum_sq_le hYm hYsub hYmean hYindep
  refine ⟨hs.1, ?_⟩
  have hYi : ∀ i, HDP.psi2Norm (Y i) μ ≤ |u i| * ‖v‖ * K := by
    intro i
    calc
      HDP.psi2Norm (Y i) μ =
          |u i| * HDP.psi2Norm (fun ω => inner ℝ (A i ω) v) μ := by
            exact HDP.psi2Norm_const_mul
              (fun ω => inner ℝ (A i ω) v) (u i)
      _ ≤ |u i| * (‖v‖ * HDP.psi2NormVector (A i) μ) :=
        mul_le_mul_of_nonneg_left
          (psi2Norm_marginal_le_norm_mul_vector (hbounded i) v)
          (abs_nonneg _)
      _ ≤ |u i| * ‖v‖ * K := by
        have h := mul_le_mul_of_nonneg_left (hpsi i) (norm_nonneg v)
        nlinarith [abs_nonneg (u i)]
  have hsum : ∑ i, HDP.psi2Norm (Y i) μ ^ 2 ≤
      ‖u‖ ^ 2 * (‖v‖ * K) ^ 2 := by
    calc
      ∑ i, HDP.psi2Norm (Y i) μ ^ 2 ≤
          ∑ i, (|u i| * ‖v‖ * K) ^ 2 := by
            apply Finset.sum_le_sum
            intro i hi
            exact (sq_le_sq₀ (HDP.psi2Norm_nonneg _ μ)
              (mul_nonneg (mul_nonneg (abs_nonneg _) (norm_nonneg v)) hK)).2 (hYi i)
      _ = (∑ i, (u i) ^ 2) * (‖v‖ * K) ^ 2 := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        ring_nf
        rw [sq_abs]
        ring
      _ = ‖u‖ ^ 2 * (‖v‖ * K) ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq]
  have hsquare : HDP.psi2Norm (fun ω => ∑ i, Y i ω) μ ^ 2 ≤
      30 * (‖u‖ ^ 2 * (‖v‖ * K) ^ 2) :=
    hs.2.trans (mul_le_mul_of_nonneg_left hsum (by norm_num))
  have hR : 0 ≤ Real.sqrt 30 * ‖u‖ * ‖v‖ * K := by positivity
  apply (sq_le_sq₀ (HDP.psi2Norm_nonneg _ μ) hR).1
  calc
    HDP.psi2Norm (fun ω => ∑ i, Y i ω) μ ^ 2 ≤
        30 * (‖u‖ ^ 2 * (‖v‖ * K) ^ 2) := hsquare
    _ = (Real.sqrt 30 * ‖u‖ * ‖v‖ * K) ^ 2 := by
      ring_nf
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 30)]

end HDP.Chapter3

end Source_26_SubGaussianMatrices

/-! ## Material formerly in `27_SubGaussianCounterexample.lean` -/

section Source_27_SubGaussianCounterexample

/-!
# An isotropic subgaussian vector whose norm does not concentrate

This module is the authoritative core implementation of **Book Exercise 3.37**,
promoted because Chapter 6 uses its counterexample. No duplicate declaration
is kept in the exercise folder.
Start with the isotropic sphere vector `sqrt n * theta`, independently keep it
with probability `1/2`, and otherwise replace it by zero.  Multiplying the
kept copy by `sqrt 2` restores isotropy.  The one-dimensional marginals retain
a dimension-free psi-two bound, while the norm is zero with probability one
half.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal RealInnerProductSpace

namespace HDP.Chapter3

noncomputable section

/-- The parameter `1/2`, packaged in Mathlib's unit interval.

**Lean implementation helper.** -/
def maskHalf : Set.Icc (0 : ℝ) 1 :=
  ⟨1 / 2, by constructor <;> norm_num⟩

/-- The fair Boolean law used by the masked-sphere construction.

**Lean implementation helper.** -/
def bernoulliMaskMeasure : Measure Bool :=
  bernoulliMeasure true false maskHalf

instance : IsProbabilityMeasure bernoulliMaskMeasure := by
  unfold bernoulliMaskMeasure
  infer_instance

/-- Product of the fair Boolean mask with an arbitrary probability law.

**Lean implementation helper.** -/
def bernoulliProductMeasure {S : Type*} [MeasurableSpace S]
    (mu : Measure S) : Measure (Bool × S) :=
  bernoulliMaskMeasure.prod mu

instance {S : Type*} [MeasurableSpace S] (mu : Measure S)
    [IsProbabilityMeasure mu] :
    IsProbabilityMeasure (bernoulliProductMeasure mu) := by
  unfold bernoulliProductMeasure bernoulliMaskMeasure
  infer_instance

/-- The mask is `sqrt 2` on the kept branch and zero otherwise.

**Lean implementation helper.** -/
def bernoulliMask (b : Bool) : ℝ :=
  if b then Real.sqrt 2 else 0

/-- The fair `0/sqrt 2` mask has second moment one (`integral_bernoulliMask_sq`).

**Lean implementation helper.** -/
lemma integral_bernoulliMask_sq :
    ∫ b, bernoulliMask b ^ 2 ∂bernoulliMaskMeasure = 1 := by
  unfold bernoulliMaskMeasure
  rw [ProbabilityTheory.integral_bernoulliMeasure]
  norm_num [maskHalf, bernoulliMask,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

variable {S : Type*} [MeasurableSpace S] {mu : Measure S}
  [IsProbabilityMeasure mu]

/-- A fair `0/sqrt 2` mask preserves every admissible psi-two MGF scale up
to the factor `sqrt 2`.

**Lean implementation helper.** -/
lemma psi2MGF_bernoulliMask_le {X : S → ℝ} {K : ℝ}
    (hXm : AEMeasurable X mu) (hK : 0 < K)
    (hmgf : HDP.psi2MGF X mu K ≤ 2) :
    HDP.psi2MGF (fun z : Bool × S => bernoulliMask z.1 * X z.2)
      (bernoulliProductMeasure mu) (Real.sqrt 2 * K) ≤ 2 := by
  unfold HDP.psi2MGF bernoulliProductMeasure
  rw [MeasureTheory.lintegral_prod]
  · calc
      (∫⁻ b, ∫⁻ s, ENNReal.ofReal
          (Real.exp ((bernoulliMask b * X s) ^ 2 /
            (Real.sqrt 2 * K) ^ 2)) ∂mu ∂bernoulliMaskMeasure) ≤
          ∫⁻ _b : Bool, (2 : ℝ≥0∞) ∂bernoulliMaskMeasure := by
        apply lintegral_mono
        intro b
        cases b with
        | false => simp [bernoulliMask]
        | true =>
            have hsqrt : 0 < Real.sqrt 2 :=
              Real.sqrt_pos.2 (by norm_num)
            have hfun : (fun s => ENNReal.ofReal
                  (Real.exp (((Real.sqrt 2) * X s) ^ 2 /
                    ((Real.sqrt 2) * K) ^ 2))) =
                fun s => ENNReal.ofReal
                  (Real.exp ((X s) ^ 2 / K ^ 2)) := by
              funext s
              congr 2
              field_simp [hsqrt.ne']
            simpa [bernoulliMask, hfun, HDP.psi2MGF] using hmgf
      _ = 2 := by
        simp only [lintegral_const, measure_univ, mul_one]
  · have hb : AEMeasurable
        (fun z : Bool × S => bernoulliMask z.1 * X z.2)
        (bernoulliMaskMeasure.prod mu) := by
      exact (by
        fun_prop : Measurable
          (fun z : Bool × S => bernoulliMask z.1)).aemeasurable.mul
        hXm.comp_snd
    fun_prop

/-- Concrete sample space for the Exercise 3.37 counterexample. -/
abbrev MaskedSphereSample (n : ℕ) :=
  Bool × Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1

/-- Product law of the fair mask and normalized surface measure.

**Lean implementation helper.** -/
def maskedSphereMeasure (n : ℕ) : Measure (MaskedSphereSample n) :=
  bernoulliProductMeasure
    (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)))

instance (n : ℕ) [NeZero n] :
    IsProbabilityMeasure (maskedSphereMeasure n) := by
  unfold maskedSphereMeasure
  infer_instance

/-- The isotropic masked-sphere random vector.

**Lean implementation helper.** -/
def maskedSphereVector (n : ℕ) :
    MaskedSphereSample n → EuclideanSpace ℝ (Fin n) :=
  fun z => bernoulliMask z.1 • HDP.isotropicSphereVector n z.2

/-- `norm_maskedSphereVector` gives `‖maskedSphereVector n z‖ = bernoulliMask z.1 * sqrt n`.

**Lean implementation helper.** -/
@[simp] lemma norm_maskedSphereVector (n : ℕ)
    (z : MaskedSphereSample n) :
    ‖maskedSphereVector n z‖ = bernoulliMask z.1 * Real.sqrt n := by
  rw [maskedSphereVector, norm_smul, HDP.norm_isotropicSphereVector]
  congr 1
  unfold bernoulliMask
  split <;> simp [Real.sqrt_nonneg]

/-- **Exercise 3.37, isotropy.** The `sqrt 2` active-branch scaling exactly
compensates for the probability-one-half mask.

**Book Exercise 3.37.** -/
theorem maskedSphere_isIsotropic (n : ℕ) (hn : 0 < n) :
    HDP.IsIsotropic (maskedSphereVector n) (maskedSphereMeasure n) := by
  letI : NeZero n := ⟨hn.ne'⟩
  apply HDP.isIsotropic_iff.mpr
  intro i j
  change (∫ z,
      (bernoulliMask z.1 * HDP.isotropicSphereVector n z.2 i) *
        (bernoulliMask z.1 * HDP.isotropicSphereVector n z.2 j)
      ∂(bernoulliMaskMeasure.prod
        (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))))) = _
  rw [show (fun z : MaskedSphereSample n =>
        (bernoulliMask z.1 * HDP.isotropicSphereVector n z.2 i) *
          (bernoulliMask z.1 * HDP.isotropicSphereVector n z.2 j)) =
      fun z => bernoulliMask z.1 ^ 2 *
        (HDP.isotropicSphereVector n z.2 i *
          HDP.isotropicSphereVector n z.2 j) by
        funext z
        ring]
  calc
    (∫ z : Bool × Metric.sphere
          (0 : EuclideanSpace ℝ (Fin n)) 1,
        bernoulliMask z.1 ^ 2 *
          (HDP.isotropicSphereVector n z.2 i *
            HDP.isotropicSphereVector n z.2 j)
        ∂(bernoulliMaskMeasure.prod
          (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))))) =
        (∫ b, bernoulliMask b ^ 2 ∂bernoulliMaskMeasure) *
          (∫ x, HDP.isotropicSphereVector n x i *
            HDP.isotropicSphereVector n x j
            ∂HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))) :=
      MeasureTheory.integral_prod_mul (L := ℝ)
        (μ := bernoulliMaskMeasure)
        (ν := HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)))
        (fun b : Bool => bernoulliMask b ^ 2)
        (fun x : Metric.sphere
            (0 : EuclideanSpace ℝ (Fin n)) 1 =>
          HDP.isotropicSphereVector n x i *
            HDP.isotropicSphereVector n x j)
    _ = _ := by
      rw [integral_bernoulliMask_sq,
        (HDP.isIsotropic_iff.mp (sphere_isIsotropic n hn) i j), one_mul]

/-- Each coordinate of the randomly masked sphere vector has the stated symmetric marginal law.

**Lean implementation helper.** -/
lemma maskedSphere_marginal_eq (n : ℕ)
    (u : EuclideanSpace ℝ (Fin n)) :
    (fun z : MaskedSphereSample n =>
      inner ℝ (maskedSphereVector n z) u) =
      fun z => bernoulliMask z.1 *
        inner ℝ (HDP.isotropicSphereVector n z.2) u := by
  funext z
  simp [maskedSphereVector, inner_smul_left]

/-- **Exercise 3.37, qualitative part.** The masked vector is subgaussian.

**Book Exercise 3.37.** -/
theorem maskedSphere_subGaussianVector (n : ℕ) (hn : 0 < n) :
    HDP.SubGaussianVector (maskedSphereVector n)
      (maskedSphereMeasure n) := by
  letI : NeZero n := ⟨hn.ne'⟩
  intro u
  let M : ℝ := Real.sqrt 2 * Real.sqrt n * ‖u‖ + 1
  have hM : 0 < M := by
    dsimp [M]
    positivity
  exact (HDP.psi2Norm_le_of_bounded (M := M) hM (by
    filter_upwards [] with z
    calc
      |inner ℝ (maskedSphereVector n z) u| ≤
          ‖maskedSphereVector n z‖ * ‖u‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ M := by
        rw [norm_maskedSphereVector]
        cases z.1 with
        | false =>
            simpa [bernoulliMask] using hM.le
        | true =>
            dsimp [bernoulliMask, M]
            linarith)).1

/-- Every unit marginal of the masked vector has a dimension-free psi-two
bound.

**Lean implementation helper.** -/
theorem psi2Norm_maskedSphere_marginal_le (n : ℕ) (hn : 0 < n)
    (u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1) :
    HDP.psi2Norm
        (fun z : MaskedSphereSample n =>
          inner ℝ (maskedSphereVector n z) u)
        (maskedSphereMeasure n) ≤
      Real.sqrt 2 * (Real.sqrt 5 * sphereProjectionTailScale) := by
  letI : NeZero n := ⟨hn.ne'⟩
  let v : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
    ⟨u, by simpa only [mem_sphere_zero_iff_norm, sub_zero]⟩
  let X := sphericalProjection n v
  have hXmeas : AEMeasurable X
      (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))) :=
    (measurable_sphericalProjection n v).aemeasurable
  have hX := sphericalProjection_subGaussian n hn v
  let K : ℝ := Real.sqrt 5 * sphereProjectionTailScale
  have hK : 0 < K :=
    mul_pos (Real.sqrt_pos.2 (by norm_num))
      sphereProjectionTailScale_pos
  have hmgf : HDP.psi2MGF X
      (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))) K ≤ 2 :=
    HDP.psi2MGF_le_two_of_ge hXmeas hX.1 hX.2 hK
  have hmasked := psi2MGF_bernoulliMask_le hXmeas hK hmgf
  have hfun :
      (fun z : MaskedSphereSample n =>
        inner ℝ (maskedSphereVector n z) u) =
        fun z => bernoulliMask z.1 * X z.2 := by
    rw [maskedSphere_marginal_eq]
    funext z
    simp [X, sphericalProjection, v, HDP.isotropicSphereVector,
      inner_smul_left]
  rw [hfun]
  exact HDP.psi2Norm_le _
    (mul_pos (Real.sqrt_pos.2 (by norm_num)) hK) hmasked

/-- **Exercise 3.37, uniform psi-two bound.** The bound is independent of
the ambient dimension.

**Book Exercise 3.37.** -/
theorem psi2NormVector_maskedSphere_le (n : ℕ) (hn : 0 < n) :
    HDP.psi2NormVector (maskedSphereVector n) (maskedSphereMeasure n) ≤
      Real.sqrt 2 * (Real.sqrt 5 * sphereProjectionTailScale) := by
  letI : NeZero n := ⟨hn.ne'⟩
  rw [HDP.psi2NormVector]
  apply csSup_le
  · let e : EuclideanSpace ℝ (Fin n) :=
      EuclideanSpace.single ⟨0, hn⟩ 1
    exact ⟨HDP.psi2Norm
      (fun z : MaskedSphereSample n =>
        inner ℝ (maskedSphereVector n z) e)
      (maskedSphereMeasure n), e, by simp [e], rfl⟩
  · intro r hr
    rcases hr with ⟨u, hu, rfl⟩
    exact psi2Norm_maskedSphere_marginal_le n hn u hu

/-- The Bernoulli mask assigns the advertised probability to the `false` outcome.

**Lean implementation helper.** -/
lemma bernoulliMaskMeasure_false :
    bernoulliMaskMeasure ({false} : Set Bool) = 1 / 2 := by
  unfold bernoulliMaskMeasure
  rw [bernoulliMeasure_apply_of_notMem_of_mem maskHalf
    (measurableSet_singleton false) (by simp) (by simp)]
  have hsymm : unitInterval.toNNReal (unitInterval.symm maskHalf) =
      (1 / 2 : NNReal) := by
    apply NNReal.eq
    change ((unitInterval.symm maskHalf : Set.Icc (0 : ℝ) 1) : ℝ) =
      ((1 / 2 : NNReal) : ℝ)
    norm_num [maskHalf]
  rw [hsymm]
  norm_num

/-- **Exercise 3.37, failure of norm concentration.** With probability at
least one half, the deviation from the isotropic radius `sqrt n` is itself
at least `sqrt n`.

**Book Exercise 3.37.** -/
theorem maskedSphere_norm_fails_concentration (n : ℕ) (hn : 0 < n) :
    (1 / 2 : ℝ≥0∞) ≤
      maskedSphereMeasure n {z |
        Real.sqrt n ≤
          |‖maskedSphereVector n z‖ - Real.sqrt n|} := by
  letI : NeZero n := ⟨hn.ne'⟩
  let A : Set (MaskedSphereSample n) :=
    ({false} : Set Bool) ×ˢ Set.univ
  have hsub : A ⊆ {z |
      Real.sqrt n ≤
        |‖maskedSphereVector n z‖ - Real.sqrt n|} := by
    intro z hz
    have hb : z.1 = false := hz.1
    change Real.sqrt n ≤
      |‖maskedSphereVector n z‖ - Real.sqrt n|
    rw [norm_maskedSphereVector, hb]
    simpa only [bernoulliMask, Bool.false_eq_true, reduceIte,
      zero_mul, zero_sub, abs_neg] using
      (le_abs_self (Real.sqrt n))
  calc
    (1 / 2 : ℝ≥0∞) = maskedSphereMeasure n A := by
      dsimp [A]
      rw [maskedSphereMeasure, bernoulliProductMeasure,
        Measure.prod_prod, bernoulliMaskMeasure_false,
        measure_univ, mul_one]
    _ ≤ _ := measure_mono hsub

end

end HDP.Chapter3

end Source_27_SubGaussianCounterexample
