import Mathlib.Probability.CDF
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Quantitative smoothing for distribution functions

This file develops the measure-theoretic part of Esseen smoothing.  Fourier
estimates for a concrete band-limited kernel are kept separate from the order
argument for cumulative distribution functions.
-/

open MeasureTheory ProbabilityTheory Real Set

namespace HDP.Appendix

/-- Pointwise discrepancy of two cumulative distribution functions. -/
noncomputable def cdfGap (μ ν : Measure ℝ) (x : ℝ) : ℝ :=
  cdf μ x - cdf ν x

/-- Uniform distance between the cumulative distribution functions of two
finite real measures. -/
noncomputable def kolmogorovDistance (μ ν : Measure ℝ) : ℝ :=
  sSup (Set.range fun x => |cdfGap μ ν x|)

lemma measurable_cdfGap (μ ν : Measure ℝ) :
    Measurable (cdfGap μ ν) := by
  exact (monotone_cdf μ).measurable.sub (monotone_cdf ν).measurable

lemma abs_cdfGap_le_one (μ ν : Measure ℝ) (x : ℝ) :
    |cdfGap μ ν x| ≤ 1 := by
  have hμ0 := cdf_nonneg μ x
  have hμ1 := cdf_le_one μ x
  have hν0 := cdf_nonneg ν x
  have hν1 := cdf_le_one ν x
  simp only [cdfGap]
  rw [abs_le]
  constructor <;> linarith

lemma kolmogorovDistance_nonneg (μ ν : Measure ℝ) :
    0 ≤ kolmogorovDistance μ ν := by
  calc
    0 ≤ |cdfGap μ ν 0| := abs_nonneg _
    _ ≤ kolmogorovDistance μ ν := by
      apply le_csSup
      · exact ⟨1, by rintro _ ⟨x, rfl⟩; exact abs_cdfGap_le_one μ ν x⟩
      · exact ⟨0, rfl⟩

lemma kolmogorovDistance_le_one (μ ν : Measure ℝ) :
    kolmogorovDistance μ ν ≤ 1 := by
  apply csSup_le
  · exact Set.range_nonempty _
  · rintro _ ⟨x, rfl⟩
    exact abs_cdfGap_le_one μ ν x

lemma abs_cdfGap_le_kolmogorovDistance (μ ν : Measure ℝ) (x : ℝ) :
    |cdfGap μ ν x| ≤ kolmogorovDistance μ ν := by
  apply le_csSup
  · exact ⟨1, by rintro _ ⟨y, rfl⟩; exact abs_cdfGap_le_one μ ν y⟩
  · exact ⟨x, rfl⟩

lemma exists_cdfGap_near_kolmogorovDistance
    (μ ν : Measure ℝ) {c : ℝ} (hc : c < 1)
    (hD : 0 < kolmogorovDistance μ ν) :
    ∃ x, c * kolmogorovDistance μ ν <
      |cdfGap μ ν x| := by
  have hlt : c * kolmogorovDistance μ ν <
      kolmogorovDistance μ ν := by
    nlinarith
  obtain ⟨z, ⟨x, rfl⟩, hx⟩ :=
    exists_lt_of_lt_csSup (Set.range_nonempty _) hlt
  exact ⟨x, hx⟩

/-- If the reference cdf has increment at most `M` times interval length, then
the cdf discrepancy cannot fall faster than that rate to the right. -/
lemma cdfGap_sub_le_cdfGap_add_of_reference_lipschitz
    (μ ν : Measure ℝ) {M a s : ℝ} (hs : 0 ≤ s)
    (hν : cdf ν (a + s) - cdf ν a ≤ M * s) :
    cdfGap μ ν a - M * s ≤ cdfGap μ ν (a + s) := by
  have hμ : cdf μ a ≤ cdf μ (a + s) :=
    monotone_cdf μ (le_add_of_nonneg_right hs)
  simp only [cdfGap]
  linarith

/-- Left-hand counterpart of
`cdfGap_sub_le_cdfGap_add_of_reference_lipschitz`. -/
lemma cdfGap_sub_le_cdfGap_add_of_reference_lipschitz_left
    (μ ν : Measure ℝ) {M a s : ℝ} (hs : 0 ≤ s)
    (hν : cdf ν a - cdf ν (a - s) ≤ M * s) :
    cdfGap μ ν (a - s) ≤ cdfGap μ ν a + M * s := by
  have hμ := monotone_cdf μ (sub_le_self a hs)
  simp only [cdfGap]
  linarith

/-- Cdf discrepancy averaged against a smoothing probability measure. -/
noncomputable def smoothedCdfGap (κ μ ν : Measure ℝ) (ε a : ℝ) : ℝ :=
  ∫ y, cdfGap μ ν (a + ε * y) ∂κ

lemma integrable_cdfGap_affine
    (κ μ ν : Measure ℝ) (ε a : ℝ) [IsFiniteMeasure κ] :
    Integrable (fun y => cdfGap μ ν (a + ε * y)) κ := by
  refine Integrable.mono' (integrable_const (1 : ℝ)) ?_ ?_
  · exact ((measurable_cdfGap μ ν).comp (by fun_prop)).aestronglyMeasurable
  · filter_upwards with y
    simpa only [Real.norm_eq_abs, norm_one] using
      abs_cdfGap_le_one μ ν (a + ε * y)

/-- A near-positive maximizer of the cdf gap stays positive throughout the
central smoothing window. -/
lemma cdfGap_ge_half_on_smoothing_window
    (μ ν : Measure ℝ) {M D ε T x : ℝ}
    (hM : 0 ≤ M) (hD : 0 ≤ D) (hε : 0 ≤ ε) (hT : 0 ≤ T)
    (hν : ∀ ⦃a b : ℝ⦄, a ≤ b →
      cdf ν b - cdf ν a ≤ M * (b - a))
    (hx : 9 * D / 10 ≤ cdfGap μ ν x)
    (hwidth : M * (2 * ε * T) ≤ 2 * D / 5) :
    ∀ y ∈ Icc (-T) T,
      D / 2 ≤ cdfGap μ ν (x + ε * T + ε * y) := by
  intro y hy
  have hTy0 : 0 ≤ T + y := by linarith [hy.1]
  have hs0 : 0 ≤ ε * (T + y) := by
    exact mul_nonneg hε hTy0
  have hTyT : T + y ≤ 2 * T := by linarith [hy.2]
  have hsT : ε * (T + y) ≤ 2 * ε * T := by
    nlinarith [mul_le_mul_of_nonneg_left hTyT hε]
  have href : cdf ν (x + ε * (T + y)) - cdf ν x ≤
      M * (ε * (T + y)) := by
    convert hν (show x ≤ x + ε * (T + y) by linarith) using 1 <;> ring
  have hgap := cdfGap_sub_le_cdfGap_add_of_reference_lipschitz
    μ ν hs0 href
  rw [show x + ε * (T + y) = x + ε * T + ε * y by ring] at hgap
  calc
    D / 2 ≤ 9 * D / 10 - 2 * D / 5 := by ring_nf; linarith
    _ ≤ cdfGap μ ν x - M * (2 * ε * T) := by linarith
    _ ≤ cdfGap μ ν x - M * (ε * (T + y)) := by
      exact sub_le_sub_left (mul_le_mul_of_nonneg_left hsT hM) _
    _ ≤ cdfGap μ ν (x + ε * T + ε * y) := hgap

/-- A near-negative maximizer of the cdf gap stays negative throughout the
central smoothing window. -/
lemma cdfGap_le_neg_half_on_smoothing_window
    (μ ν : Measure ℝ) {M D ε T x : ℝ}
    (hM : 0 ≤ M) (hD : 0 ≤ D) (hε : 0 ≤ ε) (hT : 0 ≤ T)
    (hν : ∀ ⦃a b : ℝ⦄, a ≤ b →
      cdf ν b - cdf ν a ≤ M * (b - a))
    (hx : cdfGap μ ν x ≤ -(9 * D / 10))
    (hwidth : M * (2 * ε * T) ≤ 2 * D / 5) :
    ∀ y ∈ Icc (-T) T,
      cdfGap μ ν (x - ε * T + ε * y) ≤ -(D / 2) := by
  intro y hy
  let s : ℝ := ε * (T - y)
  have hTy0 : 0 ≤ T - y := by linarith [hy.2]
  have hs0 : 0 ≤ s := by
    dsimp [s]
    exact mul_nonneg hε hTy0
  have hTyT : T - y ≤ 2 * T := by linarith [hy.1]
  have hsT : s ≤ 2 * ε * T := by
    dsimp [s]
    nlinarith [mul_le_mul_of_nonneg_left hTyT hε]
  have href : cdf ν x - cdf ν (x - s) ≤ M * s := by
    convert hν (show x - s ≤ x by linarith) using 1 <;> ring
  have hgap := cdfGap_sub_le_cdfGap_add_of_reference_lipschitz_left
    μ ν hs0 href
  rw [show x - s = x - ε * T + ε * y by simp [s]; ring] at hgap
  calc
    cdfGap μ ν (x - ε * T + ε * y)
        ≤ cdfGap μ ν x + M * s := hgap
    _ ≤ -(9 * D / 10) + M * (2 * ε * T) := by
      exact add_le_add hx (mul_le_mul_of_nonneg_left hsT hM)
    _ ≤ -(9 * D / 10) + 2 * D / 5 := by linarith
    _ ≤ -(D / 2) := by ring_nf; linarith

/-- Integrating a positive central-window bound and a global absolute bound. -/
lemma smoothedCdfGap_ge_of_window
    (κ μ ν : Measure ℝ) [IsProbabilityMeasure κ]
    {D ε T a : ℝ} (_hD : 0 ≤ D)
    (hbound : ∀ z, |cdfGap μ ν z| ≤ D)
    (hwindow : ∀ y ∈ Icc (-T) T,
      D / 2 ≤ cdfGap μ ν (a + ε * y)) :
    D / 2 - (3 * D / 2) * κ.real (Icc (-T) T)ᶜ ≤
      smoothedCdfGap κ μ ν ε a := by
  let S : Set ℝ := Icc (-T) T
  let f : ℝ → ℝ := fun y => cdfGap μ ν (a + ε * y)
  have hS : MeasurableSet S := measurableSet_Icc
  have hf : Integrable f κ := integrable_cdfGap_affine κ μ ν ε a
  have hcentral :
      (∫ _ in S, D / 2 ∂κ) ≤ ∫ y in S, f y ∂κ := by
    apply integral_mono_ae (integrable_const _) hf.integrableOn
    filter_upwards [ae_restrict_mem hS] with y hy
    exact hwindow y hy
  have houtside :
      (∫ _ in Sᶜ, -D ∂κ) ≤ ∫ y in Sᶜ, f y ∂κ := by
    apply integral_mono_ae (integrable_const _) hf.integrableOn
    filter_upwards with y
    exact (abs_le.mp (hbound (a + ε * y))).1
  change D / 2 - (3 * D / 2) * κ.real Sᶜ ≤ ∫ y, f y ∂κ
  calc
    D / 2 - (3 * D / 2) * κ.real Sᶜ =
        κ.real S * (D / 2) + κ.real Sᶜ * (-D) := by
      rw [measureReal_compl hS]
      simp only [probReal_univ]
      ring
    _ = (∫ _ in S, D / 2 ∂κ) + ∫ _ in Sᶜ, -D ∂κ := by
      simp only [setIntegral_const, smul_eq_mul]
    _ ≤ (∫ y in S, f y ∂κ) + ∫ y in Sᶜ, f y ∂κ :=
      add_le_add hcentral houtside
    _ = ∫ y, f y ∂κ := integral_add_compl hS hf

/-- Integrating a negative central-window bound and a global absolute bound. -/
lemma smoothedCdfGap_le_of_window
    (κ μ ν : Measure ℝ) [IsProbabilityMeasure κ]
    {D ε T a : ℝ} (_hD : 0 ≤ D)
    (hbound : ∀ z, |cdfGap μ ν z| ≤ D)
    (hwindow : ∀ y ∈ Icc (-T) T,
      cdfGap μ ν (a + ε * y) ≤ -(D / 2)) :
    smoothedCdfGap κ μ ν ε a ≤
      -(D / 2) + (3 * D / 2) * κ.real (Icc (-T) T)ᶜ := by
  let S : Set ℝ := Icc (-T) T
  let f : ℝ → ℝ := fun y => cdfGap μ ν (a + ε * y)
  have hS : MeasurableSet S := measurableSet_Icc
  have hf : Integrable f κ := integrable_cdfGap_affine κ μ ν ε a
  have hcentral :
      (∫ y in S, f y ∂κ) ≤ ∫ _ in S, -(D / 2) ∂κ := by
    apply integral_mono_ae hf.integrableOn (integrable_const _)
    filter_upwards [ae_restrict_mem hS] with y hy
    exact hwindow y hy
  have houtside :
      (∫ y in Sᶜ, f y ∂κ) ≤ ∫ _ in Sᶜ, D ∂κ := by
    apply integral_mono_ae hf.integrableOn (integrable_const _)
    filter_upwards with y
    exact (abs_le.mp (hbound (a + ε * y))).2
  change (∫ y, f y ∂κ) ≤ -(D / 2) + (3 * D / 2) * κ.real Sᶜ
  calc
    (∫ y, f y ∂κ) =
        (∫ y in S, f y ∂κ) + ∫ y in Sᶜ, f y ∂κ :=
      (integral_add_compl hS hf).symm
    _ ≤ (∫ _ in S, -(D / 2) ∂κ) + ∫ _ in Sᶜ, D ∂κ :=
      add_le_add hcentral houtside
    _ = κ.real S * (-(D / 2)) + κ.real Sᶜ * D := by
      simp only [setIntegral_const, smul_eq_mul]
    _ = -(D / 2) + (3 * D / 2) * κ.real Sᶜ := by
      rw [measureReal_compl hS]
      simp only [probReal_univ]
      ring

/-- Abstract Esseen order argument.  A smoothing probability with `C / T`
tails converts a uniform estimate for the smoothed cdf gap into a uniform
estimate for the original cdf gap. -/
lemma kolmogorovDistance_le_of_smoothing
    (κ μ ν : Measure ℝ) [IsProbabilityMeasure κ]
    {M C ε S : ℝ}
    (hM : 0 < M) (hC : 0 ≤ C) (hε : 0 < ε) (hS : 0 ≤ S)
    (hν : ∀ ⦃a b : ℝ⦄, a ≤ b →
      cdf ν b - cdf ν a ≤ M * (b - a))
    (htail : ∀ ⦃T : ℝ⦄, 0 < T →
      κ.real (Icc (-T) T)ᶜ ≤ C / T)
    (hsmooth : ∀ a, |smoothedCdfGap κ μ ν ε a| ≤ S) :
    kolmogorovDistance μ ν ≤ 2 * S + 18 * C * M * ε := by
  let D : ℝ := kolmogorovDistance μ ν
  change D ≤ 2 * S + 18 * C * M * ε
  have hD0 : 0 ≤ D := kolmogorovDistance_nonneg μ ν
  by_cases hDz : D = 0
  · rw [hDz]
    positivity
  have hD : 0 < D := lt_of_le_of_ne hD0 (Ne.symm hDz)
  obtain ⟨x, hx⟩ :=
    exists_cdfGap_near_kolmogorovDistance μ ν
      (show (9 : ℝ) / 10 < 1 by norm_num) hD
  change (9 : ℝ) / 10 * D < |cdfGap μ ν x| at hx
  let T : ℝ := D / (6 * M * ε)
  have hT : 0 < T := by
    dsimp [T]
    positivity
  have hwidth : M * (2 * ε * T) ≤ 2 * D / 5 := by
    have hMe : M * ε ≠ 0 := mul_ne_zero (ne_of_gt hM) (ne_of_gt hε)
    dsimp [T]
    field_simp
    nlinarith [hD]
  have hbound : ∀ z, |cdfGap μ ν z| ≤ D := by
    intro z
    exact abs_cdfGap_le_kolmogorovDistance μ ν z
  have htailT : κ.real (Icc (-T) T)ᶜ ≤ C / T := htail hT
  have htailTerm :
      (3 * D / 2) * κ.real (Icc (-T) T)ᶜ ≤ 9 * C * M * ε := by
    calc
      (3 * D / 2) * κ.real (Icc (-T) T)ᶜ
          ≤ (3 * D / 2) * (C / T) := by
            exact mul_le_mul_of_nonneg_left htailT (by positivity)
      _ = 9 * C * M * ε := by
        have hDne : D ≠ 0 := ne_of_gt hD
        have hMne : M ≠ 0 := ne_of_gt hM
        have hεne : ε ≠ 0 := ne_of_gt hε
        dsimp [T]
        field_simp
        ring
  rcases le_total 0 (cdfGap μ ν x) with hxsign | hxsign
  · have hxpos : 9 * D / 10 ≤ cdfGap μ ν x := by
      rw [abs_of_nonneg hxsign] at hx
      nlinarith
    have hwindow := cdfGap_ge_half_on_smoothing_window
      μ ν (le_of_lt hM) hD0 (le_of_lt hε) (le_of_lt hT)
      hν hxpos hwidth
    have hint := smoothedCdfGap_ge_of_window
      κ μ ν hD0 hbound hwindow
    have hs := hsmooth (x + ε * T)
    have hsupper : smoothedCdfGap κ μ ν ε (x + ε * T) ≤ S :=
      (abs_le.mp hs).2
    linarith
  · have hxneg : cdfGap μ ν x ≤ -(9 * D / 10) := by
      rw [abs_of_nonpos hxsign] at hx
      linarith
    have hwindow := cdfGap_le_neg_half_on_smoothing_window
      μ ν (le_of_lt hM) hD0 (le_of_lt hε) (le_of_lt hT)
      hν hxneg hwidth
    have hint := smoothedCdfGap_le_of_window
      κ μ ν hD0 hbound hwindow
    have hs := hsmooth (x - ε * T)
    have hslower : -S ≤ smoothedCdfGap κ μ ν ε (x - ε * T) :=
      (abs_le.mp hs).1
    linarith

end HDP.Appendix
