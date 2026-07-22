import HighDimensionalProbability.Appendix.Infra.TalagrandConvexFunction
import HighDimensionalProbability.Chapter5_ConcentrationWithoutIndependence
import Mathlib.Analysis.Convex.Function

/-!
# Talagrand convex concentration

The statement uses the source's actual cube `[-1,1]^n`; the former appendix
version incorrectly replaced it by intervals of width at most one and imposed
global, rather than cube-local, convexity and Lipschitz hypotheses.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal BigOperators

namespace HDP.Chapter5

/-- The closed cube occurring in HDP Theorem 5.2.12. -/
def talagrandCube (n : ℕ) : Set (Fin n → ℝ) :=
  Set.pi Set.univ (fun _ => Set.Icc (-1) 1)

/-- **HDP Theorem 5.2.12 (Talagrand convex concentration).**

The proof first establishes Talagrand's convex-distance inequality by entropy
tensorization, applies it to convex sublevel sets to obtain concentration
around a median, and then uses the standard `ψ₂` centering comparison to pass
from the median to the mean.
-/
theorem talagrand_convex_concentration :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ)
      (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)],
      (∀ i, μ i (Set.Icc (-1) 1) = 1) →
      ∀ (f : (Fin n → ℝ) → ℝ),
        ConvexOn ℝ (talagrandCube n) f → Measurable f →
        (∀ x ∈ talagrandCube n, ∀ y ∈ talagrandCube n,
          |f x - f y| ≤ Real.sqrt (∑ i, (x i - y i) ^ 2)) →
        Integrable f (Measure.pi μ) → ∀ t : ℝ, 0 ≤ t →
        (Measure.pi μ).real
            {x | t ≤ |f x - ∫ y, f y ∂(Measure.pi μ)|} ≤
          2 * Real.exp (-(t ^ 2) / C) := by
  let B : ℝ :=
    (1 + 1 / Real.sqrt (Real.log 2)) * (Real.sqrt 5 * 32)
  have hBpos : 0 < B := by
    dsimp [B]
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  refine ⟨B ^ 2, sq_pos_of_pos hBpos, ?_⟩
  intro n μ _ hμ f hconv hf hLip hfint t ht
  have hconv' : ConvexOn ℝ (HDP.Appendix.realCube n) f := by
    simpa [talagrandCube, HDP.Appendix.realCube] using hconv
  have hLip' :
      ∀ x ∈ HDP.Appendix.realCube n, ∀ y ∈ HDP.Appendix.realCube n,
        |f x - f y| ≤ Real.sqrt (∑ i, (x i - y i) ^ 2) := by
    simpa [talagrandCube, HDP.Appendix.realCube] using hLip
  obtain ⟨M, hMlow, hMhigh⟩ :=
    HDP.Appendix.exists_measure_median (Measure.pi μ) f hf
  have hmedianTailENN : ∀ s : ℝ, 0 ≤ s →
      (Measure.pi μ) {x | s ≤ |(fun z => f z - M) x|} ≤
        ENNReal.ofReal (2 * Real.exp (-s ^ 2 / (32 : ℝ) ^ 2)) := by
    intro s hs
    have hreal :=
      HDP.Appendix.convex_function_median_tail μ hμ f hconv' hLip'
        hMlow hMhigh hs
    calc
      (Measure.pi μ) {x | s ≤ |(fun z => f z - M) x|} =
          ENNReal.ofReal
            ((Measure.pi μ).real {x | s ≤ |(fun z => f z - M) x|}) := by
        rw [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)]
      _ ≤ ENNReal.ofReal
          (2 * Real.exp (-s ^ 2 / (32 : ℝ) ^ 2)) :=
        ENNReal.ofReal_mono (by simpa using hreal)
  have hmedian :=
    HDP.psi2Norm_le_of_tail_bound
      (hf.sub_const M).aemeasurable (show (0 : ℝ) < 32 by norm_num)
      hmedianTailENN
  have hmean :=
    exercise_5_6_mean_center_le_median_center
      hf.aemeasurable hfint M hmedian.1
  have hcenterNorm :
      HDP.psi2Norm
          (fun x => f x - ∫ y, f y ∂(Measure.pi μ)) (Measure.pi μ) ≤ B := by
    calc
      HDP.psi2Norm
          (fun x => f x - ∫ y, f y ∂(Measure.pi μ)) (Measure.pi μ) ≤
          (1 + 1 / Real.sqrt (Real.log 2)) *
            HDP.psi2Norm (fun x => f x - M) (Measure.pi μ) :=
        hmean.2
      _ ≤ (1 + 1 / Real.sqrt (Real.log 2)) *
            (Real.sqrt 5 * 32) := by
        apply mul_le_mul_of_nonneg_left hmedian.2
        have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
        positivity
      _ = B := rfl
  have henn :=
    tail_le_of_subGaussian_psi2Norm_le
      (B := B) (t := t)
      (hf.sub_const (∫ y, f y ∂(Measure.pi μ))).aemeasurable
      hmean.1 hBpos.le hcenterNorm ht
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top henn
  have hrhs0 :
      0 ≤ 2 * Real.exp (-t ^ 2 / B ^ 2) := by positivity
  rw [ENNReal.toReal_ofReal hrhs0] at hreal
  simpa [Measure.real] using hreal

end HDP.Chapter5
