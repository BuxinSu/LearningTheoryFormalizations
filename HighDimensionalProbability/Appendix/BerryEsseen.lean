import HighDimensionalProbability.Appendix.Infra.BerryEsseenCertificate
import HighDimensionalProbability.Appendix.Infra.BerryEsseenSmoothing
import HighDimensionalProbability.Appendix.Infra.BerryEsseenStandardization

/-!
# Berry--Esseen theorem

This file derives the quantitative central limit theorem from the fully
formalized smoothing, inversion, characteristic-function, and numerical
certificate developed in `Appendix.Infra`.
-/

open MeasureTheory ProbabilityTheory Real

namespace HDP.Chapter2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **HDP Theorem 2.1.4 (Berry--Esseen central limit theorem).** -/
theorem berryEsseen [IsProbabilityMeasure μ] {X : Nat → Ω → Real}
    {m sig : Real} (hsig : 0 < sig) (hindep : iIndepFun X μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hmem : MemLp (X 0) 3 μ) (hmean : ∫ ω, X 0 ω ∂μ = m)
    (hvar : Var[X 0; μ] = sig ^ 2) {N : Nat} (hN : 0 < N) (t : Real) :
    abs (μ.real {ω |
        t ≤ (∑ i ∈ Finset.range N, X i ω - N * m) /
          (sig * Real.sqrt N)} -
      (gaussianReal 0 1).real (Set.Ici t)) ≤
      ((∫ ω, abs (X 0 ω - m) ^ 3 ∂μ) / sig ^ 3) /
        Real.sqrt N := by
  let Y : ℕ → Ω → ℝ := fun i ω =>
    -(HDP.Appendix.standardized (X i) m sig ω)
  let δ : ℝ :=
    ((∫ ω, |X 0 ω - m| ^ 3 ∂μ) / sig ^ 3) /
      Real.sqrt N
  have hYmem : MemLp (Y 0) 3 μ := by
    change MemLp (-HDP.Appendix.standardized (X 0) m sig) 3 μ
    exact
      (HDP.Appendix.memLp_standardized
        (P := μ) (m := m) (σ := sig) hmem).neg
  have hYmean : ∫ ω, Y 0 ω ∂μ = 0 := by
    have hzero :=
      HDP.Appendix.integral_standardized_eq_zero
        (P := μ) hsig hmem hmean
    change ∫ ω, -HDP.Appendix.standardized (X 0) m sig ω ∂μ = 0
    rw [integral_neg]
    rw [hzero]
    simp
  have hYsecond : ∫ ω, Y 0 ω ^ 2 ∂μ = 1 := by
    simpa [Y] using
      HDP.Appendix.integral_standardized_sq_eq_one
        (P := μ) hsig hmem hmean hvar
  have hYindep : iIndepFun Y μ := by
    simpa [Y, Function.comp_def, HDP.Appendix.standardized] using
      hindep.comp
        (fun (_ : ℕ) (x : ℝ) => -((x - m) / sig))
        (fun _ => by fun_prop)
  have hYident : ∀ i : ℕ, IdentDistrib (Y i) (Y 0) μ μ := by
    intro i
    simpa [Y, Function.comp_def, HDP.Appendix.standardized] using
      (hident i).comp
        (u := fun x : ℝ => -((x - m) / sig))
        (by fun_prop)
  have hδeq :
      δ = (∫ ω, |Y 0 ω| ^ 3 ∂μ) / Real.sqrt N := by
    dsimp [δ, Y]
    rw [show
      (fun ω => |-HDP.Appendix.standardized (X 0) m sig ω| ^ 3) =
        (fun ω => |HDP.Appendix.standardized (X 0) m sig ω| ^ 3) by
      funext ω
      rw [abs_neg]]
    rw [HDP.Appendix.integral_abs_standardized_pow_three
      (P := μ) hsig]
  have hthirdInt :
      Integrable (fun ω => |Y 0 ω| ^ 3) μ := by
    simpa [Real.norm_eq_abs] using hYmem.integrable_norm_pow'
  have hthirdPos : 0 < ∫ ω, |Y 0 ω| ^ 3 ∂μ := by
    have hnonneg : 0 ≤ ∫ ω, |Y 0 ω| ^ 3 ∂μ :=
      integral_nonneg (fun _ => by positivity)
    apply lt_of_le_of_ne hnonneg
    intro hz
    have hae :
        (fun ω => |Y 0 ω| ^ 3) =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg
        (fun _ => by positivity) hthirdInt).1 hz.symm
    have hae2 :
        (fun ω => Y 0 ω ^ 2) =ᵐ[μ] 0 := by
      filter_upwards [hae] with ω hω
      have hω' : |Y 0 ω| ^ 3 = 0 := by
        simpa using hω
      have habs : |Y 0 ω| = 0 := by
        exact eq_zero_of_pow_eq_zero hω'
      rw [abs_eq_zero] at habs
      simp [habs]
    have hz2 := integral_eq_zero_of_ae hae2
    rw [hYsecond] at hz2
    norm_num at hz2
  have hδ0 : 0 < δ := by
    rw [hδeq]
    positivity
  by_cases hδ1 : δ < 1
  · have hcdf :=
      HDP.Appendix.abs_cdf_normalizedSum_sub_gaussian_le_of_scalarCertificate
        hYindep hYident hYmem hYmean hYsecond hN
        hδ0 hδ1 hδeq
        (HDP.Appendix.berryScalarCertificate hδ0 hδ1)
        (-t)
    let ZY : Ω → ℝ := fun ω =>
      (Real.sqrt N)⁻¹ *
        ∑ k ∈ Finset.range N, Y k ω
    let Z : Ω → ℝ := fun ω =>
      (∑ k ∈ Finset.range N, X k ω - N * m) /
        (sig * Real.sqrt N)
    have hZY (ω : Ω) : ZY ω = -Z ω := by
      dsimp [ZY, Z, Y, HDP.Appendix.standardized]
      rw [Finset.sum_neg_distrib, ← Finset.sum_div,
        Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp [hsig.ne', (Real.sqrt_pos.2 (Nat.cast_pos.2 hN)).ne']
    have hZYae : AEMeasurable ZY μ := by
      dsimp [ZY]
      apply AEMeasurable.const_mul
      have hsume := Finset.aemeasurable_sum
        (Finset.range N) (fun i hi =>
          (hYident i).aemeasurable_fst)
      exact hsume.congr (ae_of_all _ fun x => by
        simp only [Finset.sum_apply])
    have hcdfY :
        cdf (μ.map ZY) (-t) =
          μ.real {ω | t ≤ Z ω} := by
      letI : IsProbabilityMeasure (μ.map ZY) :=
        Measure.isProbabilityMeasure_map hZYae
      rw [cdf_eq_real]
      rw [Measure.real, Measure.real,
        Measure.map_apply_of_aemeasurable hZYae measurableSet_Iic]
      congr 2
      ext ω
      simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_setOf_eq]
      rw [hZY]
      constructor <;> intro h <;> linarith
    have hcdfG :
        cdf (gaussianReal 0 1) (-t) =
          (gaussianReal 0 1).real (Set.Ici t) := by
      rw [cdf_eq_real]
      have hneg :
          Measure.map (fun x : ℝ => -x) (gaussianReal 0 1) =
            gaussianReal 0 1 := by
        simpa using
          (gaussianReal_map_neg (μ := (0 : ℝ)) (v := (1 : NNReal)))
      have hpre :
          (fun x : ℝ => -x) ⁻¹' Set.Iic (-t) = Set.Ici t := by
        ext x
        change (-x ≤ -t) ↔ t ≤ x
        constructor <;> intro h <;> linarith
      rw [Measure.real, Measure.real]
      calc
        ((gaussianReal 0 1) (Set.Iic (-t))).toReal =
            ((Measure.map (fun x : ℝ => -x) (gaussianReal 0 1))
              (Set.Iic (-t))).toReal := by rw [hneg]
        _ = ((gaussianReal 0 1) (Set.Ici t)).toReal := by
          rw [Measure.map_apply (by fun_prop) measurableSet_Iic, hpre]
    change |cdf (μ.map ZY) (-t) -
      cdf (gaussianReal 0 1) (-t)| ≤ δ at hcdf
    rw [hcdfY, hcdfG] at hcdf
    simpa [δ, Z] using hcdf
  · have hδlarge : 1 ≤ δ := le_of_not_gt hδ1
    have hp0 :
        0 ≤ μ.real {ω |
          t ≤ (∑ i ∈ Finset.range N, X i ω - N * m) /
            (sig * Real.sqrt N)} := measureReal_nonneg
    have hp1 :
        μ.real {ω |
          t ≤ (∑ i ∈ Finset.range N, X i ω - N * m) /
            (sig * Real.sqrt N)} ≤ 1 := measureReal_le_one
    have hg0 :
        0 ≤ (gaussianReal 0 1).real (Set.Ici t) :=
      measureReal_nonneg
    have hg1 :
        (gaussianReal 0 1).real (Set.Ici t) ≤ 1 :=
      measureReal_le_one
    have habs :
        abs (μ.real {ω |
            t ≤ (∑ i ∈ Finset.range N, X i ω - N * m) /
              (sig * Real.sqrt N)} -
          (gaussianReal 0 1).real (Set.Ici t)) ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith
    simpa [δ] using habs.trans hδlarge

end HDP.Chapter2
