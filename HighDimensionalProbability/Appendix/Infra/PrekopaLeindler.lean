import MatrixConcentration.Appendix_GaussianConcentration
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Finite-dimensional Prékopa--Leindler infrastructure

This file tensorizes the sibling development's one-dimensional
Prékopa--Leindler theorem and transports it to finite-dimensional Euclidean
space.  It is used by the isolated Euclidean isoperimetric theorem.
-/

open MeasureTheory
open scoped ENNReal

namespace HDP.Appendix

/-- The Prékopa--Leindler property for a measure and a chosen affine
combination operation. -/
def PrekopaLeindler {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (comb : ℝ → α → α → α) : Prop :=
  ∀ p : ℝ, 0 < p → p < 1 →
    ∀ F G H : α → ℝ≥0∞, Measurable F → Measurable G → Measurable H →
      (∀ x y : α, F x ^ (1 - p) * G y ^ p ≤ H (comb p x y)) →
      (∫⁻ x, F x ∂μ) ^ (1 - p) * (∫⁻ y, G y ∂μ) ^ p ≤
        ∫⁻ z, H z ∂μ

/-- The measurable-set consequence of Prékopa--Leindler. -/
lemma PrekopaLeindler.measure_rpow_mul_measure_rpow_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {comb : ℝ → α → α → α} (hPL : PrekopaLeindler μ comb)
    {A B C : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hC : MeasurableSet C) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (hcomb : ∀ x ∈ A, ∀ y ∈ B, comb p x y ∈ C) :
    (μ A) ^ (1 - p) * (μ B) ^ p ≤ μ C := by
  have hpoint : ∀ x y : α,
      (A.indicator (1 : α → ℝ≥0∞) x) ^ (1 - p) *
          (B.indicator (1 : α → ℝ≥0∞) y) ^ p ≤
        C.indicator (1 : α → ℝ≥0∞) (comb p x y) := by
    intro x y
    by_cases hx : x ∈ A
    · by_cases hy : y ∈ B
      · simp [Set.indicator_of_mem hx, Set.indicator_of_mem hy,
          Set.indicator_of_mem (hcomb x hx y hy)]
      · simp [Set.indicator_of_mem hx, Set.indicator_of_notMem hy,
          ENNReal.zero_rpow_of_pos hp0]
    · simp [Set.indicator_of_notMem hx,
        ENNReal.zero_rpow_of_pos (sub_pos.mpr hp1)]
  have h := hPL p hp0 hp1
    (A.indicator (1 : α → ℝ≥0∞))
    (B.indicator (1 : α → ℝ≥0∞))
    (C.indicator (1 : α → ℝ≥0∞))
    (measurable_const.indicator hA)
    (measurable_const.indicator hB)
    (measurable_const.indicator hC) hpoint
  simpa [lintegral_indicator_one hA, lintegral_indicator_one hB,
    lintegral_indicator_one hC] using h

/-- The sibling development's one-dimensional Prékopa--Leindler theorem,
repackaged in the local tensorizable interface. -/
theorem prekopaLeindler_real :
    PrekopaLeindler (volume : Measure ℝ)
      (fun p x y => (1 - p) * x + p * y) := by
  intro p hp0 hp1 F G H hF hG hH hcond
  exact MatrixConcentration.oneDim_prekopa_leindler
    hp0 hp1 hF hG hH hcond

/-- Prékopa--Leindler is stable under finite-product tensorization. -/
lemma PrekopaLeindler.prod {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    {c₁ : ℝ → α → α → α} {c₂ : ℝ → β → β → β}
    (h₁ : PrekopaLeindler μ c₁) (h₂ : PrekopaLeindler ν c₂) :
    PrekopaLeindler (μ.prod ν)
      (fun p u v => (c₁ p u.1 v.1, c₂ p u.2 v.2)) := by
  intro p hp0 hp1 F G H hF hG hH hcond
  have hinner : ∀ a₁ a₂ : α,
      (∫⁻ b, F (a₁, b) ∂ν) ^ (1 - p) *
          (∫⁻ b, G (a₂, b) ∂ν) ^ p ≤
        ∫⁻ b, H (c₁ p a₁ a₂, b) ∂ν := by
    intro a₁ a₂
    exact h₂ p hp0 hp1
      (fun b => F (a₁, b)) (fun b => G (a₂, b))
      (fun b => H (c₁ p a₁ a₂, b))
      (hF.comp measurable_prodMk_left)
      (hG.comp measurable_prodMk_left)
      (hH.comp measurable_prodMk_left)
      (fun b₁ b₂ => hcond (a₁, b₁) (a₂, b₂))
  have houter := h₁ p hp0 hp1
    (fun a => ∫⁻ b, F (a, b) ∂ν)
    (fun a => ∫⁻ b, G (a, b) ∂ν)
    (fun a => ∫⁻ b, H (a, b) ∂ν)
    hF.lintegral_prod_right' hG.lintegral_prod_right'
    hH.lintegral_prod_right' hinner
  rw [lintegral_prod F hF.aemeasurable,
    lintegral_prod G hG.aemeasurable,
    lintegral_prod H hH.aemeasurable]
  exact houter

/-- Prékopa--Leindler transfers through a measure-preserving measurable
equivalence which intertwines the affine-combination operations. -/
lemma PrekopaLeindler.transfer {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β}
    {comb : ℝ → α → α → α} {comb' : ℝ → β → β → β}
    (hPL : PrekopaLeindler μ comb) (e : β ≃ᵐ α)
    (he : MeasurePreserving e ν μ)
    (hcomb : ∀ (p : ℝ) (x y : β),
      e (comb' p x y) = comb p (e x) (e y)) :
    PrekopaLeindler ν comb' := by
  intro p hp0 hp1 F G H hF hG hH hcond
  have hcond' : ∀ u v : α,
      (fun u => F (e.symm u)) u ^ (1 - p) *
          (fun v => G (e.symm v)) v ^ p ≤
        (fun w => H (e.symm w)) (comb p u v) := by
    intro u v
    have h2 : e.symm (comb p u v) =
        comb' p (e.symm u) (e.symm v) := by
      have h3 := hcomb p (e.symm u) (e.symm v)
      rw [e.apply_symm_apply, e.apply_symm_apply] at h3
      rw [← h3, e.symm_apply_apply]
    change F (e.symm u) ^ (1 - p) * G (e.symm v) ^ p ≤
      H (e.symm (comb p u v))
    rw [h2]
    exact hcond (e.symm u) (e.symm v)
  have hout := hPL p hp0 hp1
    (fun u => F (e.symm u)) (fun v => G (e.symm v))
    (fun w => H (e.symm w))
    (hF.comp e.symm.measurable) (hG.comp e.symm.measurable)
    (hH.comp e.symm.measurable) hcond'
  have hes : MeasurePreserving (⇑e.symm) μ ν := he.symm e
  rw [hes.lintegral_comp hF, hes.lintegral_comp hG,
    hes.lintegral_comp hH] at hout
  exact hout

/-- Prékopa--Leindler for the standard Lebesgue product measure on
`Fin n → ℝ`. -/
theorem prekopaLeindler_pi_fin : ∀ n : ℕ,
    PrekopaLeindler (Measure.pi fun _ : Fin n => (volume : Measure ℝ))
      (fun p x y k => (1 - p) * x k + p * y k) := by
  intro n
  induction n with
  | zero =>
      intro p hp0 hp1 F G H hF hG hH hcond
      have hpi := Measure.pi_of_empty
        (fun _ : Fin 0 => (volume : Measure ℝ))
      rw [hpi, lintegral_dirac' _ hF, lintegral_dirac' _ hG,
        lintegral_dirac' _ hH]
      let z : Fin 0 → ℝ := fun a => isEmptyElim a
      have h := hcond z z
      convert h using 1
      apply congrArg H
      funext a
      exact isEmptyElim a
  | succ n ih =>
      have hprod := PrekopaLeindler.prod prekopaLeindler_real ih
      let e := MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (n + 1) => ℝ) 0
      have he : MeasurePreserving e
          (Measure.pi fun _ : Fin (n + 1) => (volume : Measure ℝ))
          ((volume : Measure ℝ).prod
            (Measure.pi fun _ : Fin n => (volume : Measure ℝ))) :=
        measurePreserving_piFinSuccAbove
          (fun _ : Fin (n + 1) => (volume : Measure ℝ)) 0
      exact PrekopaLeindler.transfer hprod e he (fun _ _ _ => rfl)

/-- Finite-dimensional Prékopa--Leindler on Euclidean space. -/
theorem prekopaLeindler_euclideanSpace (n : ℕ) :
    PrekopaLeindler (volume : Measure (EuclideanSpace ℝ (Fin n)))
      (fun p x y => (1 - p) • x + p • y) := by
  let e : EuclideanSpace ℝ (Fin n) ≃ᵐ (Fin n → ℝ) :=
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm
  have he : MeasurePreserving e
      (volume : Measure (EuclideanSpace ℝ (Fin n)))
      (Measure.pi fun _ : Fin n => (volume : Measure ℝ)) := by
    simpa only [← volume_pi] using
      EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin n)
  refine PrekopaLeindler.transfer (prekopaLeindler_pi_fin n) e he ?_
  intro p x y
  rfl

end HDP.Appendix
