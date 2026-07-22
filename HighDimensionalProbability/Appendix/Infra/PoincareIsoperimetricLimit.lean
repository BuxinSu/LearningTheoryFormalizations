import HighDimensionalProbability.Appendix.Infra.PoincareLimitTools
import HighDimensionalProbability.Appendix.SphericalIsoperimetric

/-!
# Gaussian isoperimetry by the Poincaré spherical limit

The proof regularizes the competitor by a small open thickening whose
Gaussian boundary has measure zero. Weak Poincaré convergence then gives
convergence of its lifted masses. Exact spherical-cap quantiles match those
masses at every sufficiently large dimension, spherical isoperimetry compares
the corresponding expansions, and the closed-set half of Portmanteau passes
the comparison to the Gaussian limit.
-/

open MeasureTheory ProbabilityTheory Set Metric InnerProductSpace Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace HDP.Appendix

/-- Gaussian isoperimetry at a strictly smaller half-space expansion radius.
The slack is used for null-boundary regularization and the spherical chordal
cap expansion. -/
theorem gaussian_isoperimetric_closedExpansion_lt
    {n : ℕ} [NeZero n]
    (A : Set (EuclideanSpace ℝ (Fin n))) (_hA : MeasurableSet A)
    (u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1)
    (a ε s : ℝ) (hs : 0 < s) (hsε : s < ε)
    (hmass : stdGaussian (EuclideanSpace ℝ (Fin n)) A =
      stdGaussian (EuclideanSpace ℝ (Fin n))
        (gaussianLinearHalfspace u a)) :
    stdGaussian (EuclideanSpace ℝ (Fin n))
        (closedExpansion s (gaussianLinearHalfspace u a)) ≤
      stdGaussian (EuclideanSpace ℝ (Fin n))
        (closedExpansion ε A) := by
  classical
  let gap : ℝ := (ε - s) / 3
  have hgap : 0 < gap := by
    dsimp [gap]
    linarith
  obtain ⟨ρ, ⟨hρ0, hρgap⟩, hρfront⟩ :=
    exists_null_frontier_thickening
      (stdGaussian (EuclideanSpace ℝ (Fin n))) A hgap
  let σ : ℝ := s + gap
  let B : Set (EuclideanSpace ℝ (Fin n)) := Metric.thickening ρ A
  let F : Set (EuclideanSpace ℝ (Fin n)) := Metric.cthickening σ B
  have hσ0 : 0 < σ := by
    dsimp [σ]
    linarith
  have hsσ : s < σ := by
    dsimp [σ]
    linarith
  have hρε : ρ < ε := by
    dsimp [gap] at hρgap
    linarith
  have hρσ : ρ + σ < ε := by
    have hρgap' : ρ < (ε - s) / 3 := by
      simpa [gap] using hρgap
    dsimp [σ, gap]
    linarith
  have hBopen : IsOpen B := by
    dsimp [B]
    exact Metric.isOpen_thickening
  have hBmeas : MeasurableSet B := hBopen.measurableSet
  have hFclosed : IsClosed F := by
    dsimp [F]
    exact Metric.isClosed_cthickening
  have hFmeas : MeasurableSet F := hFclosed.measurableSet
  have hfront :
      stdGaussian (EuclideanSpace ℝ (Fin n)) (frontier B) = 0 := by
    simpa [B] using hρfront
  have hAB : A ⊆ B := by
    dsimp [B]
    exact Metric.self_subset_thickening hρ0 A
  have hpApos :
      0 < stdGaussian (EuclideanSpace ℝ (Fin n)) A := by
    rw [hmass, stdGaussian_gaussianLinearHalfspace u a hu]
    exact lt_of_le_of_lt (by exact bot_le)
      (strictMono_gaussianReal_Iic (sub_lt_self a zero_lt_one))
  have hpBpos :
      0 < stdGaussian (EuclideanSpace ℝ (Fin n)) B :=
    hpApos.trans_le (measure_mono hAB)
  by_cases hpB1 :
      stdGaussian (EuclideanSpace ℝ (Fin n)) B = 1
  · calc
      stdGaussian (EuclideanSpace ℝ (Fin n))
          (closedExpansion s (gaussianLinearHalfspace u a)) ≤
          stdGaussian (EuclideanSpace ℝ (Fin n)) Set.univ :=
        measure_mono (subset_univ _)
      _ = 1 := measure_univ
      _ = stdGaussian (EuclideanSpace ℝ (Fin n)) B := hpB1.symm
      _ ≤ stdGaussian (EuclideanSpace ℝ (Fin n))
          (closedExpansion ε A) :=
        measure_mono
          (thickening_subset_closedExpansion A hρε.le)
  have hpBle :
      stdGaussian (EuclideanSpace ℝ (Fin n)) B ≤ 1 := by
    calc
      stdGaussian (EuclideanSpace ℝ (Fin n)) B ≤
          stdGaussian (EuclideanSpace ℝ (Fin n)) Set.univ :=
        measure_mono (subset_univ _)
      _ = 1 := measure_univ
  have hpBlt :
      stdGaussian (EuclideanSpace ℝ (Fin n)) B < 1 :=
    lt_of_le_of_ne hpBle hpB1
  let q : ℕ → ℝ≥0∞ := fun k =>
    (poincareProjectionPM n k :
      Measure (EuclideanSpace ℝ (Fin n))) B
  have hq :
      Tendsto q atTop
        (𝓝 (stdGaussian (EuclideanSpace ℝ (Fin n)) B)) := by
    have h :=
      ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
        (poincareProjectionPM_tendsto n) hfront
    simpa [q, stdGaussianPM] using h
  have hqpos : ∀ᶠ k : ℕ in atTop, 0 < q k :=
    (tendsto_order.1 hq).1 0 hpBpos
  have hqlt : ∀ᶠ k : ℕ in atTop, q k < 1 :=
    (tendsto_order.1 hq).2 1 hpBlt
  let b : ℕ → ℝ := fun k =>
    if hk : 0 < q k ∧ q k < 1 then
      Classical.choose
        (exists_sphericalCap_measure_eq
          (d := n + (k + 2)) (by omega)
          (poincareEmbed n (k + 2) u)
          (by simpa [norm_poincareEmbed] using hu)
          hk.1 hk.2)
    else 0
  have hbmass :
      ∀ᶠ k : ℕ in atTop,
        HDP.unitSphereMeasure
          (EuclideanSpace ℝ (Fin (n + (k + 2))))
          (HDP.Chapter5.sphericalCap
            (poincareEmbed n (k + 2) u) (b k)) = q k := by
    filter_upwards [hqpos, hqlt] with k hk0 hk1
    dsimp [b]
    rw [dif_pos ⟨hk0, hk1⟩]
    exact Classical.choose_spec
      (exists_sphericalCap_measure_eq
        (d := n + (k + 2)) (by omega)
        (poincareEmbed n (k + 2) u)
        (by simpa [norm_poincareEmbed] using hu)
        hk0 hk1)
  let t : ℕ → ℝ := fun k =>
    b k * Real.sqrt (n + (k + 2) : ℝ)
  have htscale : ∀ k : ℕ,
      t k / Real.sqrt (n + (k + 2) : ℝ) = b k := by
    intro k
    have hsqrt : Real.sqrt (n + (k + 2) : ℝ) ≠ 0 := by
      apply (Real.sqrt_pos.2 ?_).ne'
      positivity
    dsimp [t]
    field_simp
  have hcapmass :
      ∀ᶠ k : ℕ in atTop,
        HDP.unitSphereMeasure
          (EuclideanSpace ℝ (Fin (n + (k + 2))))
          (HDP.Chapter5.sphericalCap
            (poincareEmbed n (k + 2) u)
            (t k / Real.sqrt (n + (k + 2) : ℝ))) = q k := by
    filter_upwards [hbmass] with k hk
    rw [htscale]
    exact hk
  have hcapTendsto :
      Tendsto
        (fun k : ℕ =>
          HDP.unitSphereMeasure
            (EuclideanSpace ℝ (Fin (n + (k + 2))))
            (HDP.Chapter5.sphericalCap
              (poincareEmbed n (k + 2) u)
              (t k / Real.sqrt (n + (k + 2) : ℝ))))
        atTop
        (𝓝 (stdGaussian (EuclideanSpace ℝ (Fin n)) B)) := by
    apply hq.congr'
    filter_upwards [hcapmass] with k hk
    exact hk.symm
  obtain ⟨c, hc⟩ :=
    exists_gaussianReal_Iic_eq hpBpos hpBlt
  have ht : Tendsto t atTop (𝓝 c) := by
    apply poincare_scaled_cap_threshold_tendsto n u hu
    simpa [hc] using hcapTendsto
  have hgeom :=
    poincare_sphericalCap_shift_subset_expansion_eventually
      n ht hs.le hsσ
  have hineq :
      ∀ᶠ k : ℕ in atTop,
        HDP.unitSphereMeasure
          (EuclideanSpace ℝ (Fin (n + (k + 2))))
          (HDP.Chapter5.sphericalCap
            (poincareEmbed n (k + 2) u)
            ((t k + s) / Real.sqrt (n + (k + 2) : ℝ))) ≤
          (poincareProjectionPM n k :
            Measure (EuclideanSpace ℝ (Fin n))) F := by
    filter_upwards [hqpos, hqlt, hcapmass, hgeom]
      with k hk0 hk1 hkcap hkgeom
    have hdim : 2 ≤ n + (k + 2) := by omega
    have hdimPos : 0 < n + (k + 2) := by omega
    have hsqrtPos : 0 < Real.sqrt (n + (k + 2) : ℝ) := by
      apply Real.sqrt_pos.2
      exact_mod_cast hdimPos
    have hnormal :
        ‖poincareEmbed n (k + 2) u‖ = 1 := by
      simpa [norm_poincareEmbed] using hu
    have hqLift :
        q k =
          HDP.unitSphereMeasure
            (EuclideanSpace ℝ (Fin (n + (k + 2))))
            (poincareLift n (k + 2) B) := by
      dsimp [q]
      exact poincareProjectionPM_apply n k B hBmeas
    have hmassIso :
        HDP.unitSphereMeasure
            (EuclideanSpace ℝ (Fin (n + (k + 2))))
            (poincareLift n (k + 2) B) =
          HDP.unitSphereMeasure
            (EuclideanSpace ℝ (Fin (n + (k + 2))))
            (HDP.Chapter5.sphericalCap
              (poincareEmbed n (k + 2) u)
              (t k / Real.sqrt (n + (k + 2) : ℝ))) := by
      rw [← hqLift, hkcap]
    have hcapPos :
        0 < HDP.unitSphereMeasure
          (EuclideanSpace ℝ (Fin (n + (k + 2))))
          (HDP.Chapter5.sphericalCap
            (poincareEmbed n (k + 2) u)
            (t k / Real.sqrt (n + (k + 2) : ℝ))) := by
      rw [hkcap]
      exact hk0
    have hiso := HDP.Chapter5.spherical_isoperimetric
      hdim
      (poincareLift n (k + 2) B)
      (measurableSet_poincareLift hBmeas)
      (poincareEmbed n (k + 2) u) hnormal
      (t k / Real.sqrt (n + (k + 2) : ℝ))
      (σ / Real.sqrt (n + (k + 2) : ℝ))
      (div_pos hσ0 hsqrtPos)
      hcapPos hmassIso
    calc
      HDP.unitSphereMeasure
          (EuclideanSpace ℝ (Fin (n + (k + 2))))
          (HDP.Chapter5.sphericalCap
            (poincareEmbed n (k + 2) u)
            ((t k + s) / Real.sqrt (n + (k + 2) : ℝ))) ≤
          HDP.unitSphereMeasure
            (EuclideanSpace ℝ (Fin (n + (k + 2))))
            (closedExpansion
              (σ / Real.sqrt (n + (k + 2) : ℝ))
              (HDP.Chapter5.sphericalCap
                (poincareEmbed n (k + 2) u)
                (t k / Real.sqrt (n + (k + 2) : ℝ)))) :=
        measure_mono (hkgeom _ hnormal)
      _ ≤ HDP.unitSphereMeasure
            (EuclideanSpace ℝ (Fin (n + (k + 2))))
            (closedExpansion
              (σ / Real.sqrt (n + (k + 2) : ℝ))
              (poincareLift n (k + 2) B)) := hiso
      _ ≤ HDP.unitSphereMeasure
            (EuclideanSpace ℝ (Fin (n + (k + 2))))
            (poincareLift n (k + 2) (closedExpansion σ B)) :=
        measure_mono (by
          simpa only [Nat.cast_add, Nat.cast_ofNat] using
            (closedExpansion_poincareLift_div_sqrt_subset
              n (k + 2) hdimPos B σ))
      _ ≤ HDP.unitSphereMeasure
            (EuclideanSpace ℝ (Fin (n + (k + 2))))
            (poincareLift n (k + 2) F) := by
        apply measure_mono
        apply preimage_mono
        dsimp [F]
        exact closedExpansion_subset_cthickening B σ
      _ = (poincareProjectionPM n k :
            Measure (EuclideanSpace ℝ (Fin n))) F :=
        (poincareProjectionPM_apply n k F hFmeas).symm
  have hshift :
      Tendsto
        (fun k : ℕ =>
          HDP.unitSphereMeasure
            (EuclideanSpace ℝ (Fin (n + (k + 2))))
            (HDP.Chapter5.sphericalCap
              (poincareEmbed n (k + 2) u)
              ((t k + s) / Real.sqrt (n + (k + 2) : ℝ))))
        atTop (𝓝 (gaussianReal 0 1 (Iic (c + s)))) := by
    apply poincare_sphericalCap_mass_tendsto n u hu
    exact ht.add_const s
  have hlimsupF :
      limsup
          (fun k : ℕ =>
            (poincareProjectionPM n k :
              Measure (EuclideanSpace ℝ (Fin n))) F)
          atTop ≤
        stdGaussian (EuclideanSpace ℝ (Fin n)) F := by
    have h :=
      ProbabilityMeasure.limsup_measure_closed_le_of_tendsto
        (poincareProjectionPM_tendsto n) hFclosed
    simpa [stdGaussianPM] using h
  have hcapF :
      gaussianReal 0 1 (Iic (c + s)) ≤
        stdGaussian (EuclideanSpace ℝ (Fin n)) F := by
    calc
      gaussianReal 0 1 (Iic (c + s)) =
          limsup
            (fun k : ℕ =>
              HDP.unitSphereMeasure
                (EuclideanSpace ℝ (Fin (n + (k + 2))))
                (HDP.Chapter5.sphericalCap
                  (poincareEmbed n (k + 2) u)
                  ((t k + s) /
                    Real.sqrt (n + (k + 2) : ℝ))))
            atTop := hshift.limsup_eq.symm
      _ ≤ limsup
            (fun k : ℕ =>
              (poincareProjectionPM n k :
                Measure (EuclideanSpace ℝ (Fin n))) F)
            atTop :=
        limsup_le_limsup hineq
      _ ≤ stdGaussian (EuclideanSpace ℝ (Fin n)) F := hlimsupF
  have hac : a ≤ c := by
    apply strictMono_gaussianReal_Iic.le_iff_le.mp
    rw [hc]
    calc
      gaussianReal 0 1 (Iic a) =
          stdGaussian (EuclideanSpace ℝ (Fin n))
            (gaussianLinearHalfspace u a) :=
        (stdGaussian_gaussianLinearHalfspace u a hu).symm
      _ = stdGaussian (EuclideanSpace ℝ (Fin n)) A := hmass.symm
      _ ≤ stdGaussian (EuclideanSpace ℝ (Fin n)) B :=
        measure_mono hAB
  calc
    stdGaussian (EuclideanSpace ℝ (Fin n))
        (closedExpansion s (gaussianLinearHalfspace u a)) =
        gaussianReal 0 1 (Iic (a + s)) :=
      stdGaussian_closedExpansion_gaussianLinearHalfspace
        u a s hu hs.le
    _ ≤ gaussianReal 0 1 (Iic (c + s)) :=
      strictMono_gaussianReal_Iic.monotone (by linarith)
    _ ≤ stdGaussian (EuclideanSpace ℝ (Fin n)) F := hcapF
    _ ≤ stdGaussian (EuclideanSpace ℝ (Fin n))
        (closedExpansion ε A) := by
      apply measure_mono
      dsimp [F, B]
      exact cthickening_thickening_subset_closedExpansion
        A hσ0.le hρσ

/-- The full Gaussian closed-neighborhood comparison obtained as a
Poincaré limit of spherical isoperimetry. -/
theorem gaussian_isoperimetric_poincare
    {n : ℕ} [NeZero n]
    (A : Set (EuclideanSpace ℝ (Fin n))) (hA : MeasurableSet A)
    (u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1)
    (a ε : ℝ) (hε : 0 < ε)
    (hmass : stdGaussian (EuclideanSpace ℝ (Fin n)) A =
      stdGaussian (EuclideanSpace ℝ (Fin n))
        (gaussianLinearHalfspace u a)) :
    stdGaussian (EuclideanSpace ℝ (Fin n))
        (closedExpansion ε (gaussianLinearHalfspace u a)) ≤
      stdGaussian (EuclideanSpace ℝ (Fin n))
        (closedExpansion ε A) := by
  let s : ℕ → ℝ := fun k => ε - ((k + 1 : ℕ) : ℝ)⁻¹
  have hden :
      Tendsto (fun k : ℕ => ((k + 1 : ℕ) : ℝ)) atTop atTop := by
    have hNat : Tendsto (fun k : ℕ => k + 1) atTop atTop :=
      tendsto_add_atTop_nat 1
    exact tendsto_natCast_atTop_atTop.comp hNat
  have hinv :
      Tendsto (fun k : ℕ => ((k + 1 : ℕ) : ℝ)⁻¹)
        atTop (𝓝 0) :=
    hden.inv_tendsto_atTop
  have hs : Tendsto s atTop (𝓝 ε) := by
    simpa [s] using tendsto_const_nhds.sub hinv
  have hspos : ∀ᶠ k : ℕ in atTop, 0 < s k :=
    hs.eventually (Ioi_mem_nhds hε)
  have hslt : ∀ k : ℕ, s k < ε := by
    intro k
    dsimp [s]
    have hk : 0 < ((k + 1 : ℕ) : ℝ) := by positivity
    have hinvPos : 0 < ((k + 1 : ℕ) : ℝ)⁻¹ := inv_pos.mpr hk
    linarith
  have hineq :
      ∀ᶠ k : ℕ in atTop,
        stdGaussian (EuclideanSpace ℝ (Fin n))
            (closedExpansion (s k) (gaussianLinearHalfspace u a)) ≤
          stdGaussian (EuclideanSpace ℝ (Fin n))
            (closedExpansion ε A) := by
    filter_upwards [hspos] with k hk
    exact gaussian_isoperimetric_closedExpansion_lt
      A hA u hu a ε (s k) hk (hslt k) hmass
  have hprofile :
      Tendsto
        (fun k => gaussianReal 0 1 (Iic (a + s k)))
        atTop (𝓝 (gaussianReal 0 1 (Iic (a + ε)))) := by
    apply gaussianReal_Iic_tendsto
    exact tendsto_const_nhds.add hs
  have hleft :
      Tendsto
        (fun k =>
          stdGaussian (EuclideanSpace ℝ (Fin n))
            (closedExpansion (s k) (gaussianLinearHalfspace u a)))
        atTop
        (𝓝 (stdGaussian (EuclideanSpace ℝ (Fin n))
          (closedExpansion ε (gaussianLinearHalfspace u a)))) := by
    rw [stdGaussian_closedExpansion_gaussianLinearHalfspace
      u a ε hu hε.le]
    apply hprofile.congr'
    filter_upwards [hspos] with k hk
    exact (stdGaussian_closedExpansion_gaussianLinearHalfspace
      u a (s k) hu hk.le).symm
  exact le_of_tendsto hleft hineq

end HDP.Appendix
