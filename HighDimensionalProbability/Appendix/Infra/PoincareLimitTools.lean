import HighDimensionalProbability.Appendix.Infra.PoincareWeak
import HighDimensionalProbability.Appendix.Infra.PoincareCapExpansion
import HighDimensionalProbability.Appendix.Infra.PoincareQuantile
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Analytic tools for the Poincaré isoperimetric limit

This file packages the moving-threshold cap limit, inversion of the strictly
increasing Gaussian CDF, and the metric regularization inclusions used in the
Poincaré-limit proof of Gaussian isoperimetry.
-/

open MeasureTheory ProbabilityTheory Set Metric InnerProductSpace Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace HDP.Appendix

lemma poincare_sphericalCap_cdf_error_tendsto_zero
    (n : ℕ) (u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1)
    (t : ℕ → ℝ) :
    Tendsto
      (fun k : ℕ =>
        |(HDP.unitSphereMeasure
            (EuclideanSpace ℝ (Fin (n + (k + 2))))).real
            (HDP.Chapter5.sphericalCap (poincareEmbed n (k + 2) u)
              (t k / Real.sqrt (n + (k + 2) : ℝ))) -
          (gaussianReal 0 1).real (Iic (t k))|)
      atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro η hη
  obtain ⟨N, hN⟩ :=
    eventually_atTop.1 (poincare_sphericalCap_cdf_uniform n η hη)
  refine ⟨N, fun k hk => ?_⟩
  rw [Real.dist_eq]
  simpa using hN k hk u hu (t k)

lemma poincare_sphericalCap_mass_tendsto
    (n : ℕ) (u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1)
    {t : ℕ → ℝ} {a : ℝ} (ht : Tendsto t atTop (𝓝 a)) :
    Tendsto
      (fun k : ℕ =>
        HDP.unitSphereMeasure
          (EuclideanSpace ℝ (Fin (n + (k + 2))))
          (HDP.Chapter5.sphericalCap (poincareEmbed n (k + 2) u)
            (t k / Real.sqrt (n + (k + 2) : ℝ))))
      atTop (𝓝 (gaussianReal 0 1 (Iic a))) := by
  have hgauss :
      Tendsto (fun k => (gaussianReal 0 1).real (Iic (t k)))
        atTop (𝓝 ((gaussianReal 0 1).real (Iic a))) := by
    letI : NoAtoms (gaussianReal 0 1) := by
      simp only [gaussianReal, one_ne_zero, if_false]
      infer_instance
    have h :=
      (ProbabilityTheory.continuous_cdf_of_noAtoms
        (gaussianReal 0 1)).continuousAt.tendsto.comp ht
    change Tendsto
      (fun k => ProbabilityTheory.cdf (gaussianReal 0 1) (t k))
      atTop
      (𝓝 (ProbabilityTheory.cdf (gaussianReal 0 1) a)) at h
    simpa only [ProbabilityTheory.cdf_eq_real] using h
  have herr := poincare_sphericalCap_cdf_error_tendsto_zero n u hu t
  have hreal :
      Tendsto
        (fun k : ℕ =>
          (HDP.unitSphereMeasure
            (EuclideanSpace ℝ (Fin (n + (k + 2))))).real
            (HDP.Chapter5.sphericalCap (poincareEmbed n (k + 2) u)
              (t k / Real.sqrt (n + (k + 2) : ℝ))))
        atTop (𝓝 ((gaussianReal 0 1).real (Iic a))) := by
    have hdiff :
        Tendsto
          (fun k : ℕ =>
            (HDP.unitSphereMeasure
              (EuclideanSpace ℝ (Fin (n + (k + 2))))).real
                (HDP.Chapter5.sphericalCap
                  (poincareEmbed n (k + 2) u)
                  (t k / Real.sqrt (n + (k + 2) : ℝ))) -
              (gaussianReal 0 1).real (Iic (t k)))
          atTop (𝓝 0) := by
      rw [tendsto_zero_iff_abs_tendsto_zero]
      simpa [Function.comp_def] using herr
    convert hdiff.add hgauss using 1 <;> simp
  rw [← ENNReal.tendsto_toReal_iff
    (fun k => measure_ne_top _ _)
    (measure_ne_top _ _)]
  simpa [measureReal_def] using hreal

lemma gaussianReal_Iic_tendsto
    {t : ℕ → ℝ} {a : ℝ} (ht : Tendsto t atTop (𝓝 a)) :
    Tendsto (fun k => gaussianReal 0 1 (Iic (t k)))
      atTop (𝓝 (gaussianReal 0 1 (Iic a))) := by
  letI : NoAtoms (gaussianReal 0 1) := by
    simp only [gaussianReal, one_ne_zero, if_false]
    infer_instance
  have h :=
    (ProbabilityTheory.continuous_cdf_of_noAtoms
      (gaussianReal 0 1)).continuousAt.tendsto.comp ht
  change Tendsto
    (fun k => ProbabilityTheory.cdf (gaussianReal 0 1) (t k))
    atTop
    (𝓝 (ProbabilityTheory.cdf (gaussianReal 0 1) a)) at h
  have hreal :
      Tendsto (fun k => (gaussianReal 0 1).real (Iic (t k)))
        atTop (𝓝 ((gaussianReal 0 1).real (Iic a))) := by
    simpa only [ProbabilityTheory.cdf_eq_real] using h
  rw [← ENNReal.tendsto_toReal_iff
    (fun k => measure_ne_top _ _) (measure_ne_top _ _)]
  simpa [measureReal_def] using hreal

lemma tendsto_of_strictMono_comp_tendsto
    {g : ℝ → ℝ≥0∞} (hg : StrictMono g)
    {t : ℕ → ℝ} {a : ℝ}
    (hgt : Tendsto (fun k => g (t k)) atTop (𝓝 (g a))) :
    Tendsto t atTop (𝓝 a) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hleft : g (a - ε) < g a := hg (sub_lt_self a hε)
  have hright : g a < g (a + ε) := hg (lt_add_of_pos_right a hε)
  obtain ⟨N, hN⟩ :=
    eventually_atTop.1 (hgt (Ioo_mem_nhds hleft hright))
  refine ⟨N, fun k hk => ?_⟩
  rw [Real.dist_eq, abs_lt]
  have hIoo := hN k hk
  constructor
  · have := hg.lt_iff_lt.mp hIoo.1
    linarith
  · have := hg.lt_iff_lt.mp hIoo.2
    linarith

lemma poincare_scaled_cap_threshold_tendsto
    (n : ℕ) (u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1)
    {t : ℕ → ℝ} {a : ℝ}
    (hmass :
      Tendsto
        (fun k : ℕ =>
          HDP.unitSphereMeasure
            (EuclideanSpace ℝ (Fin (n + (k + 2))))
            (HDP.Chapter5.sphericalCap (poincareEmbed n (k + 2) u)
              (t k / Real.sqrt (n + (k + 2) : ℝ))))
        atTop (𝓝 (gaussianReal 0 1 (Iic a)))) :
    Tendsto t atTop (𝓝 a) := by
  apply tendsto_of_strictMono_comp_tendsto strictMono_gaussianReal_Iic
  have herr := poincare_sphericalCap_cdf_error_tendsto_zero n u hu t
  have hmassReal :
      Tendsto
        (fun k : ℕ =>
          (HDP.unitSphereMeasure
            (EuclideanSpace ℝ (Fin (n + (k + 2))))).real
            (HDP.Chapter5.sphericalCap (poincareEmbed n (k + 2) u)
              (t k / Real.sqrt (n + (k + 2) : ℝ))))
        atTop (𝓝 ((gaussianReal 0 1).real (Iic a))) := by
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp hmass
  have hdiff :
      Tendsto
        (fun k : ℕ =>
          (HDP.unitSphereMeasure
            (EuclideanSpace ℝ (Fin (n + (k + 2))))).real
              (HDP.Chapter5.sphericalCap
                (poincareEmbed n (k + 2) u)
                (t k / Real.sqrt (n + (k + 2) : ℝ))) -
            (gaussianReal 0 1).real (Iic (t k)))
        atTop (𝓝 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    simpa [Function.comp_def] using herr
  have hgaussReal :
      Tendsto (fun k => (gaussianReal 0 1).real (Iic (t k)))
        atTop (𝓝 ((gaussianReal 0 1).real (Iic a))) := by
    have := hmassReal.sub hdiff
    convert this using 1 <;> simp
  rw [← ENNReal.tendsto_toReal_iff
    (fun k => measure_ne_top _ _)
    (measure_ne_top _ _)]
  simpa [measureReal_def] using hgaussReal

lemma closedExpansion_subset_cthickening {E : Type*}
    [PseudoMetricSpace E] (A : Set E) (δ : ℝ) :
    closedExpansion δ A ⊆ Metric.cthickening δ A := by
  rintro x ⟨y, hy, hxy⟩
  apply Metric.closedBall_subset_cthickening hy δ
  simpa [Metric.mem_closedBall] using hxy

lemma cthickening_thickening_subset_closedExpansion {E : Type*}
    [PseudoMetricSpace E] (A : Set E) {ρ σ ε : ℝ}
    (hσ : 0 ≤ σ) (hsum : ρ + σ < ε) :
    Metric.cthickening σ (Metric.thickening ρ A) ⊆
      closedExpansion ε A := by
  let gap := (ε - (ρ + σ)) / 2
  let τ := σ + gap
  have hgap : 0 < gap := by
    dsimp [gap]
    linarith
  have hτ : 0 < τ := by
    dsimp [τ]
    linarith
  have hστ : σ < τ := by
    dsimp [τ]
    linarith
  have hρε : ρ + τ < ε := by
    dsimp [τ, gap]
    linarith
  intro x hx
  have hx' : x ∈ Metric.thickening τ (Metric.thickening ρ A) :=
    Metric.cthickening_subset_thickening' hτ hστ _ hx
  obtain ⟨y, hy, hxy⟩ := Metric.mem_thickening_iff.mp hx'
  obtain ⟨z, hz, hyz⟩ := Metric.mem_thickening_iff.mp hy
  refine ⟨z, hz, ?_⟩
  exact (dist_triangle x y z).trans
    (le_of_lt (lt_of_lt_of_le (add_lt_add hxy hyz)
      (by linarith : τ + ρ ≤ ε)))

lemma thickening_subset_closedExpansion {E : Type*}
    [PseudoMetricSpace E] (A : Set E) {ρ ε : ℝ} (hρε : ρ ≤ ε) :
    Metric.thickening ρ A ⊆ closedExpansion ε A := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := Metric.mem_thickening_iff.mp hx
  exact ⟨y, hy, hxy.le.trans hρε⟩

lemma poincareProjectionPM_apply (n k : ℕ)
    (B : Set (EuclideanSpace ℝ (Fin n))) (hB : MeasurableSet B) :
    (poincareProjectionPM n k : Measure (EuclideanSpace ℝ (Fin n))) B =
      HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin (n + (k + 2))))
        (poincareLift n (k + 2) B) := by
  dsimp [poincareProjectionPM]
  rw [Measure.map_apply (measurable_poincareProjection n (k + 2)) hB]
  rfl

end HDP.Appendix
