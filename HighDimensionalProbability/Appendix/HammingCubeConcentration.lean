import HighDimensionalProbability.Appendix.BoundedDifferences
import HighDimensionalProbability.Prelude.MetricEntropy

/-!
# HDP Theorem 5.2.5: concentration on the Hamming cube

The normalized Hamming cube is a finite product of unbiased bits.  Changing one
bit changes every one-Lipschitz observable by at most `1 / n`; applying bounded
differences to the observable and its negative gives the two-sided estimate.
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators ENNReal NNReal

namespace HDP.Chapter5

private theorem hammingDistance_le_one_of_eq_off
    {n : ℕ} (x y : HDP.BinaryWord n) (i : Fin n)
    (hxy : ∀ j, j ≠ i → x j = y j) :
    HDP.hammingDistance x y ≤ 1 := by
  classical
  unfold HDP.hammingDistance hammingDist
  apply Finset.card_le_one.mpr
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  by_contra hab
  have hai : a = i := by
    by_contra hai
    exact ha (hxy a hai)
  have hbi : b = i := by
    by_contra hbi
    exact hb (hxy b hbi)
  exact hab (hai.trans hbi.symm)

/-- **HDP Theorem 5.2.5 (concentration on the normalized Hamming cube).** -/
theorem hamming_cube_concentration :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 0 < n →
      letI : MeasurableSpace (HDP.BinaryWord n) := ⊤
      HasMeanConcentration
        (uniformOn (Set.univ : Set (HDP.BinaryWord n)))
        (fun x y ↦ HDP.hammingDistance x y / (n : ℝ))
        (C / Real.sqrt n) := by
  refine ⟨1 / 2, by norm_num, ?_⟩
  intro n hn
  letI : MeasurableSpace (HDP.BinaryWord n) := ⊤
  intro f hf hlip hfint t ht
  let μbit : Fin n → Measure Bool :=
    fun _ ↦ uniformOn (Set.univ : Set Bool)
  let c : Fin n → ℝ := fun _ ↦ 1 / (n : ℝ)
  let e : (Fin n → Bool) ≃ᵐ HDP.BinaryWord n :=
    { toEquiv := Hamming.toHamming
      measurable_toFun := measurable_of_finite _
      measurable_invFun := measurable_of_finite _ }
  let g : (Fin n → Bool) → ℝ := fun x ↦ f (e x)
  have hnℝ : (0 : ℝ) < n := by exact_mod_cast hn
  have hnℝ0 : (n : ℝ) ≠ 0 := ne_of_gt hnℝ
  have hprod :
      Measure.pi μbit = uniformOn (Set.univ : Set (Fin n → Bool)) := by
    symm
    have huniv :
        Set.univ.pi (fun _ : Fin n ↦ (Set.univ : Set Bool)) =
          (Set.univ : Set (Fin n → Bool)) := by
      ext x
      simp
    rw [← huniv]
    simpa [μbit] using
      (ProbabilityTheory.uniformOn_pi
        (f := fun _ : Fin n ↦ (Set.univ : Set Bool)))
  have hmap :
      Measure.map e (Measure.pi μbit) =
        uniformOn (Set.univ : Set (HDP.BinaryWord n)) := by
    rw [hprod]
    apply Measure.ext_of_singleton
    intro x
    rw [Measure.map_apply e.measurable (MeasurableSet.singleton x)]
    have hpre : e ⁻¹' {x} = {e.symm x} := by
      ext y
      change e y = x ↔ y = e.symm x
      exact e.toEquiv.apply_eq_iff_eq_symm_apply
    rw [hpre, uniformOn_univ, uniformOn_univ]
    simp only [Measure.count_singleton]
    rw [Fintype.card_congr e.toEquiv]
  let hpres : MeasurePreserving e (Measure.pi μbit)
      (uniformOn (Set.univ : Set (HDP.BinaryWord n))) := ⟨e.measurable, hmap⟩
  have hg : Measurable g := by
    exact hf.comp e.measurable
  have hgfint : Integrable g (Measure.pi μbit) := by
    simpa only [g, Function.comp_def] using
      hpres.integrable_comp_of_integrable hfint
  have hmean :
      (∫ x, g x ∂Measure.pi μbit) =
        ∫ y, f y ∂uniformOn (Set.univ : Set (HDP.BinaryWord n)) := by
    simpa only [g, Function.comp_def] using hpres.integral_comp' f
  have hc : ∀ i, 0 ≤ c i := by
    intro i
    simp only [c]
    positivity
  have hcoordinate :
      ∀ x y i, (∀ j, j ≠ i → x j = y j) → |g x - g y| ≤ c i := by
    intro x y i hxy
    refine (hlip (e x) (e y)).trans ?_
    have hdist : (HDP.hammingDistance (e x) (e y) : ℝ) ≤ 1 := by
      exact_mod_cast hammingDistance_le_one_of_eq_off (e x) (e y) i hxy
    simp only [c]
    exact (div_le_div_iff_of_pos_right hnℝ).2 hdist
  have hsum : ∑ i, c i ^ 2 = 1 / (n : ℝ) := by
    simp only [c, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    field_simp [hnℝ0]
  have hupperPi := bounded_differences μbit g c hg hc hcoordinate hgfint t ht
  have hlowerPi := bounded_differences μbit (fun x ↦ -g x) c hg.neg hc
    (by
      intro x y i hxy
      simpa only [neg_sub_neg, abs_sub_comm] using hcoordinate x y i hxy)
    hgfint.neg t ht
  have hexponent :
      -2 * t ^ 2 / ∑ i, c i ^ 2 = -2 * (n : ℝ) * t ^ 2 := by
    rw [hsum]
    field_simp [hnℝ0]
  rw [hexponent] at hupperPi hlowerPi
  simp only [integral_neg] at hlowerPi
  let m : ℝ := ∫ x, f x ∂uniformOn (Set.univ : Set (HDP.BinaryWord n))
  let upper : Set (HDP.BinaryWord n) := {x | m + t ≤ f x}
  let lower : Set (HDP.BinaryWord n) := {x | -m + t ≤ -f x}
  have hevent :
      {x | t ≤ |f x - m|} = upper ∪ lower := by
    ext x
    simp only [upper, lower, Set.mem_setOf_eq, Set.mem_union]
    constructor
    · intro hx
      rw [le_abs] at hx
      rcases hx with hx | hx
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    · rintro (hx | hx)
      · exact (le_abs_self (f x - m)).trans' (by linarith)
      · exact (neg_le_abs (f x - m)).trans' (by linarith)
  have hupper' :
      (uniformOn (Set.univ : Set (HDP.BinaryWord n))).real upper ≤
        Real.exp (-2 * (n : ℝ) * t ^ 2) := by
    rw [← hpres.measureReal_preimage (by simp : NullMeasurableSet upper _)]
    simpa only [upper, m, g, Set.preimage_setOf_eq, hmean] using hupperPi
  have hlower' :
      (uniformOn (Set.univ : Set (HDP.BinaryWord n))).real lower ≤
        Real.exp (-2 * (n : ℝ) * t ^ 2) := by
    rw [← hpres.measureReal_preimage (by simp : NullMeasurableSet lower _)]
    simpa only [lower, m, g, Set.preimage_setOf_eq, hmean] using hlowerPi
  rw [show (∫ y, f y ∂uniformOn (Set.univ : Set (HDP.BinaryWord n))) = m from rfl,
    hevent]
  calc
    (uniformOn (Set.univ : Set (HDP.BinaryWord n))).real (upper ∪ lower) ≤
        (uniformOn (Set.univ : Set (HDP.BinaryWord n))).real upper +
          (uniformOn (Set.univ : Set (HDP.BinaryWord n))).real lower :=
      measureReal_union_le _ _
    _ ≤ 2 * Real.exp (-2 * (n : ℝ) * t ^ 2) := by
      linarith
    _ = 2 * Real.exp (-(t ^ 2) / (2 * ((1 / 2) / Real.sqrt n) ^ 2)) := by
      congr 2
      have hsqrt : Real.sqrt (n : ℝ) ^ 2 = n :=
        Real.sq_sqrt (le_of_lt hnℝ)
      have hsqrt0 : Real.sqrt (n : ℝ) ≠ 0 :=
        ne_of_gt (Real.sqrt_pos.2 hnℝ)
      field_simp [hsqrt0, hnℝ0]
      nlinarith

end HDP.Chapter5
