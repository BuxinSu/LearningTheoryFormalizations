import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.UniformOn

/-!
# Concentration predicates used by the isolated appendix

This module contains only source-neutral notation shared by the external
concentration results.  It is intentionally outside the book's main import
graph.
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal

namespace HDP.Chapter5

/-- Mean-centered Gaussian concentration with an explicit distance gauge. -/
def HasMeanConcentration {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (d : X -> X -> Real) (s : Real) : Prop :=
  forall (f : X -> Real), Measurable f ->
    (forall x y, |f x - f y| <= d x y) -> Integrable f mu ->
    forall t : Real, 0 <= t ->
      mu.real {x | t <= |f x - ∫ y, f y ∂mu|} <=
        2 * Real.exp (-(t ^ 2) / (2 * s ^ 2))

namespace HasMeanConcentration

/-- A concentration bound remains valid when its scale parameter is enlarged. -/
theorem mono_scale
    {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {d : X → X → ℝ} {s S : ℝ}
    (h : HasMeanConcentration μ d s) (hs : 0 < s) (hsS : s ≤ S) :
    HasMeanConcentration μ d S := by
  intro f hf hLip hfint t ht
  have htail := h f hf hLip hfint t ht
  calc
    μ.real {x | t ≤ |f x - ∫ y, f y ∂μ|} ≤
        2 * Real.exp (-(t ^ 2) / (2 * s ^ 2)) := htail
    _ ≤ 2 * Real.exp (-(t ^ 2) / (2 * S ^ 2)) := by
      have hS : 0 < S := hs.trans_le hsS
      have hs2 : 0 < s ^ 2 := sq_pos_of_pos hs
      have hS2 : 0 < S ^ 2 := sq_pos_of_pos hS
      have hsq : s ^ 2 ≤ S ^ 2 :=
        (sq_le_sq₀ hs.le hS.le).2 hsS
      have harg :
          -(t ^ 2) / (2 * s ^ 2) ≤
            -(t ^ 2) / (2 * S ^ 2) := by
        apply (div_le_div_iff₀ (mul_pos (by norm_num) hs2)
          (mul_pos (by norm_num) hS2)).2
        nlinarith [sq_nonneg t]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg)
        (by norm_num)

/-- Concentration descends through a measure-preserving Lipschitz map. -/
theorem map_of_lipschitz
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y}
    {dX : X → X → ℝ} {dY : Y → Y → ℝ} {s L : ℝ}
    (hμ : HasMeanConcentration μ dX s)
    (φ : X → Y) (hφ : MeasurePreserving φ μ ν)
    (hL : 0 < L)
    (hlip : ∀ x y, dY (φ x) (φ y) ≤ L * dX x y) :
    HasMeanConcentration ν dY (L * s) := by
  intro f hf hflip hfint t ht
  let g : X → ℝ := fun x => f (φ x) / L
  have hg : Measurable g := (hf.comp hφ.measurable).div_const L
  have hgfint : Integrable (fun x => f (φ x)) μ :=
    hφ.integrable_comp_of_integrable hfint
  have hgint : Integrable g μ := hgfint.div_const L
  have hglip : ∀ x y, |g x - g y| ≤ dX x y := by
    intro x y
    have hxy : |f (φ x) - f (φ y)| ≤ L * dX x y :=
      (hflip (φ x) (φ y)).trans (hlip x y)
    dsimp [g]
    rw [div_sub_div_same, abs_div, abs_of_pos hL]
    exact (div_le_iff₀ hL).2 (by simpa [mul_comm] using hxy)
  have htail := hμ g hg hglip hgint (t / L) (div_nonneg ht hL.le)
  have hmeanComp :
      (∫ x, f (φ x) ∂μ) = ∫ y, f y ∂ν :=
    by
      rw [← hφ.map_eq]
      exact (integral_map hφ.measurable.aemeasurable hf.aestronglyMeasurable).symm
  have hmean :
      (∫ x, g x ∂μ) = (∫ y, f y ∂ν) / L := by
    simp only [g, div_eq_mul_inv]
    rw [integral_mul_const, hmeanComp]
  let A : Set Y := {y | t ≤ |f y - ∫ z, f z ∂ν|}
  have hA : MeasurableSet A := by
    exact measurableSet_le measurable_const (hf.sub measurable_const).abs
  have hpre :
      {x | t / L ≤ |g x - ∫ z, g z ∂μ|} = φ ⁻¹' A := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, A, g, hmean]
    rw [div_sub_div_same, abs_div, abs_of_pos hL]
    exact div_le_div_iff_of_pos_right hL
  have hmeasure : μ.real (φ ⁻¹' A) = ν.real A := by
    rw [measureReal_def, measureReal_def, ← hφ.map_eq,
      Measure.map_apply hφ.measurable hA]
  rw [hpre, hmeasure] at htail
  convert htail using 1
  field_simp [hL.ne']

end HasMeanConcentration

end HDP.Chapter5

namespace HDP.Appendix

/-- A centered sub-Gaussian MGF bound implies its standard two-sided tail. -/
lemma twoSidedTail_of_hasSubgaussianMGF
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (c : ℝ≥0)
    (hX : HasSubgaussianMGF X c μ) (t : ℝ) (ht : 0 ≤ t) :
    μ.real {x | t ≤ |X x|} ≤
      2 * Real.exp (-(t ^ 2) / (2 * (c : ℝ))) := by
  let A : Set Ω := {x | t ≤ X x}
  let B : Set Ω := {x | t ≤ -X x}
  have hset : {x | t ≤ |X x|} = A ∪ B := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_union, A, B]
    constructor
    · intro h
      by_cases hx : 0 ≤ X x
      · left
        simpa [abs_of_nonneg hx] using h
      · right
        have hx' : X x ≤ 0 := le_of_not_ge hx
        simpa [abs_of_nonpos hx'] using h
    · rintro (h | h)
      · exact h.trans (le_abs_self _)
      · exact h.trans (neg_le_abs _)
  have hupper :
      μ.real A ≤ Real.exp (-(t ^ 2) / (2 * (c : ℝ))) := by
    simpa [A] using hX.measure_ge_le ht
  have hneg : HasSubgaussianMGF (fun x => -X x) c μ := by
    convert hX.const_mul (-1) using 1
    · funext x
      ring
    · apply NNReal.eq
      rw [NNReal.coe_mul]
      change (c : ℝ) = (-1 : ℝ) ^ 2 * (c : ℝ)
      ring
  have hlower :
      μ.real B ≤ Real.exp (-(t ^ 2) / (2 * (c : ℝ))) := by
    have htail := hneg.measure_ge_le ht
    simpa [B] using htail
  rw [hset]
  calc
    μ.real (A ∪ B) ≤ μ.real A + μ.real B := measureReal_union_le A B
    _ ≤ Real.exp (-(t ^ 2) / (2 * (c : ℝ))) +
        Real.exp (-(t ^ 2) / (2 * (c : ℝ))) :=
      add_le_add hupper hlower
    _ = 2 * Real.exp (-(t ^ 2) / (2 * (c : ℝ))) := by ring

end HDP.Appendix
