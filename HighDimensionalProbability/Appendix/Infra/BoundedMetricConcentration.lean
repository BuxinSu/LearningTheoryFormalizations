import HighDimensionalProbability.Appendix.Infra.BoundedDifferencesCore

/-!
# Concentration from a deterministic diameter bound

This elementary fallback handles compact low-dimensional exceptional cases:
if every admissible distance is bounded by `D`, every one-Lipschitz observable
deviates from its mean by at most `D`, hence has Gaussian-form concentration
at the coarse scale `2D`.
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal

namespace HDP.Appendix

theorem hasMeanConcentration_of_bounded_distance
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (d : Ω → Ω → ℝ) {D : ℝ} (hD : 0 < D)
    (hdiam : ∀ x y, d x y ≤ D) :
    HDP.Chapter5.HasMeanConcentration μ d (2 * D) := by
  intro f hf hLip hfint t ht
  have hdev (x : Ω) :
      |f x - ∫ y, f y ∂μ| ≤ D := by
    have h :=
      HDP.Chapter5.Appendix.abs_integral_sub_integral_le_of_abs_sub_le
        μ (fun _ => f x) f measurable_const hf D hD.le
        (fun y => (hLip x y).trans (hdiam x y))
    simpa using h
  by_cases htd : t ≤ D
  · calc
      μ.real {x | t ≤ |f x - ∫ y, f y ∂μ|} ≤ 1 :=
        measureReal_le_one
      _ ≤ 2 * Real.exp (-(t ^ 2) / (2 * (2 * D) ^ 2)) := by
        have ht2 : t ^ 2 ≤ D ^ 2 := by nlinarith
        have harg :
            (-1 / 8 : ℝ) ≤ -(t ^ 2) / (2 * (2 * D) ^ 2) := by
          field_simp [hD.ne']
          nlinarith [sq_pos_of_pos hD]
        have hbase : (7 / 8 : ℝ) ≤ Real.exp (-1 / 8) := by
          nlinarith [Real.add_one_le_exp (-1 / 8 : ℝ)]
        have hmono :
            Real.exp (-1 / 8) ≤
              Real.exp (-(t ^ 2) / (2 * (2 * D) ^ 2)) :=
          Real.exp_le_exp.mpr harg
        nlinarith
  · have hDt : D < t := lt_of_not_ge htd
    have hset :
        {x | t ≤ |f x - ∫ y, f y ∂μ|} = (∅ : Set Ω) := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact not_le.mpr ((hdev x).trans_lt hDt)
    rw [hset, measureReal_empty]
    exact mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (Real.exp_pos _).le

end HDP.Appendix
