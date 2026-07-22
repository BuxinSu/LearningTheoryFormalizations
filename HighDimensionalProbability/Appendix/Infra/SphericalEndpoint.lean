import HighDimensionalProbability.Appendix.Infra.SphericalCapExpansion

/-!
# Endpoint and measurable-set completion of spherical isoperimetry

The polarization minimizer first gives the comparison for compact sets with
a strict radius slack.  Continuity from above for closed thickenings removes
that slack.  The final section passes from compact sets to arbitrary
measurable sets.
-/

open MeasureTheory Set Metric InnerProductSpace Filter Function
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace HDP.Appendix

noncomputable section

variable {n : ℕ}

/-- The strict radius slack in compact spherical isoperimetry can be removed
by continuity from above of closed thickenings. -/
lemma spherical_isoperimetric_compact
    [Nonempty (Fin n)] (hn : 2 ≤ n)
    (K : SphereCompacts n)
    (u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1)
    (a ε : ℝ) (hε : 0 ≤ ε)
    (hcap : 0 < HDP.unitSphereMeasure
      (EuclideanSpace ℝ (Fin n))
      (HDP.Chapter5.sphericalCap u a))
    (hmass :
      HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
          (K : Set (SphereE n)) =
        HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
          (HDP.Chapter5.sphericalCap u a)) :
    HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
        (closedExpansion ε (HDP.Chapter5.sphericalCap u a)) ≤
      HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
        (closedExpansion ε (K : Set (SphereE n))) := by
  let μ := HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
  have hlim :
      Tendsto
        (fun s : ℝ => μ (Metric.cthickening s (K : Set (SphereE n))))
        (𝓝[Ioi ε] ε)
        (𝓝 (μ (Metric.cthickening ε (K : Set (SphereE n))))) := by
    have h :=
      tendsto_measure_biInter_gt
        (μ := μ)
        (s := fun s : ℝ =>
          Metric.cthickening s (K : Set (SphereE n)))
        (a := ε)
        (fun _ _ => Metric.isClosed_cthickening.nullMeasurableSet)
        (fun _ _ _ hij => Metric.cthickening_mono hij _)
        ⟨ε + 1, by linarith,
          measure_ne_top μ
            (Metric.cthickening (ε + 1)
              (K : Set (SphereE n)))⟩
    rw [← Metric.cthickening_eq_iInter_cthickening] at h
    simpa [Function.comp_def] using h
  have hbound :
      μ (closedExpansion ε
          (HDP.Chapter5.sphericalCap u a)) ≤
        μ (Metric.cthickening ε (K : Set (SphereE n))) := by
    apply ge_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hspos : 0 ≤ s := hε.trans hs.le
    have hslack :=
      spherical_isoperimetric_compact_slack hn K u hu a
        hcap hmass ε s hε hs
    rwa [closedExpansion_eq_cthickening
      K.isCompact.isClosed hspos] at hslack
  rwa [closedExpansion_eq_cthickening
    K.isCompact.isClosed hε]

/-- Chordal distance on the unit sphere is at most its diameter, `2`. -/
lemma dist_le_two_sphere (x y : SphereE n) :
    dist x y ≤ 2 := by
  change
    ‖(x : EuclideanSpace ℝ (Fin n)) -
      (y : EuclideanSpace ℝ (Fin n))‖ ≤ 2
  calc
    ‖(x : EuclideanSpace ℝ (Fin n)) -
        (y : EuclideanSpace ℝ (Fin n))‖ ≤
        ‖(x : EuclideanSpace ℝ (Fin n))‖ +
          ‖(y : EuclideanSpace ℝ (Fin n))‖ :=
      norm_sub_le _ _
    _ = 2 := by
      rw [mem_sphere_zero_iff_norm.mp x.property,
        mem_sphere_zero_iff_norm.mp y.property]
      norm_num

/-- A smaller closed expansion of the closure of `A` lies in any strictly
larger open expansion of `A`. -/
lemma closedExpansion_closure_subset_thickening
    {X : Type*} [PseudoMetricSpace X]
    (A : Set X) {r ε : ℝ} (hre : r < ε) :
    closedExpansion r (closure A) ⊆ Metric.thickening ε A := by
  rintro x ⟨y, hy, hxy⟩
  rw [Metric.mem_thickening_iff]
  obtain ⟨z, hzA, hyz⟩ :=
    Metric.mem_closure_iff.1 hy (ε - r) (sub_pos.mpr hre)
  refine ⟨z, hzA, ?_⟩
  calc
    dist x z ≤ dist x y + dist y z := dist_triangle _ _ _
    _ < r + (ε - r) := add_lt_add_of_le_of_lt hxy hyz
    _ = ε := by ring

/-- An open expansion is the directed union of all its nonnegative smaller
closed expansions. -/
lemma thickening_eq_iUnion_closedExpansion
    {X : Type*} [PseudoMetricSpace X]
    (A : Set X) {ε : ℝ} (hε : 0 < ε) :
    Metric.thickening ε A =
      ⋃ r : Set.Ico (0 : ℝ) ε, closedExpansion (r : ℝ) A := by
  ext x
  constructor
  · intro hx
    rw [Metric.mem_thickening_iff] at hx
    rcases hx with ⟨y, hyA, hxy⟩
    let r : ℝ := (dist x y + ε) / 2
    have hr0 : 0 ≤ r := by
      dsimp [r]
      positivity
    have hrε : r < ε := by
      dsimp [r]
      linarith
    have hxyr : dist x y ≤ r := by
      dsimp [r]
      linarith
    rw [mem_iUnion]
    exact ⟨⟨r, hr0, hrε⟩, y, hyA, hxyr⟩
  · intro hx
    rw [mem_iUnion] at hx
    rcases hx with ⟨r, y, hyA, hxy⟩
    rw [Metric.mem_thickening_iff]
    exact ⟨y, hyA, hxy.trans_lt r.property.2⟩

/-- The measurable-set spherical comparison, proved from the compact
polarization theorem by taking the closure of the competitor and using
strictly smaller radii. -/
lemma spherical_isoperimetric_measurable
    [Nonempty (Fin n)] (hn : 2 ≤ n)
    (A : Set (SphereE n)) (_hA : MeasurableSet A)
    (u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1)
    (a ε : ℝ) (hε : 0 < ε)
    (hcap : 0 < HDP.unitSphereMeasure
      (EuclideanSpace ℝ (Fin n))
      (HDP.Chapter5.sphericalCap u a))
    (hmass :
      HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)) A =
        HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
          (HDP.Chapter5.sphericalCap u a)) :
    HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
        (closedExpansion ε (HDP.Chapter5.sphericalCap u a)) ≤
      HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
        (closedExpansion ε A) := by
  let μ := HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
  have hApos : 0 < μ A := by
    rw [hmass]
    exact hcap
  have hAne : A.Nonempty :=
    nonempty_of_measure_ne_zero hApos.ne'
  by_cases hε2 : ε < 2
  · let K : SphereCompacts n :=
      ⟨⟨closure A, isClosed_closure.isCompact⟩,
        hAne.mono subset_closure⟩
    let q : ℝ≥0∞ := μ (K : Set (SphereE n))
    have hpq :
        μ (HDP.Chapter5.sphericalCap u a) ≤ q := by
      calc
        μ (HDP.Chapter5.sphericalCap u a) = μ A := hmass.symm
        _ ≤ μ (closure A) := measure_mono subset_closure
        _ = q := rfl
    have hqpos : 0 < q := hcap.trans_le hpq
    have hqle : q ≤ 1 := by
      calc
        q ≤ μ Set.univ := measure_mono (subset_univ _)
        _ = 1 := measure_univ
    obtain ⟨b, hbmass, hCab⟩ :
        ∃ b : ℝ,
          μ (HDP.Chapter5.sphericalCap u b) = q ∧
          HDP.Chapter5.sphericalCap u a ⊆
            HDP.Chapter5.sphericalCap u b := by
      by_cases hqp :
          q = μ (HDP.Chapter5.sphericalCap u a)
      · exact ⟨a, hqp.symm, Subset.rfl⟩
      by_cases hq1 : q = 1
      · refine ⟨1, ?_, ?_⟩
        · rw [sphericalCap_eq_univ_of_one_le u hu 1 le_rfl,
            measure_univ, hq1]
        · rw [sphericalCap_eq_univ_of_one_le u hu 1 le_rfl]
          exact subset_univ _
      · have hqlt : q < 1 := lt_of_le_of_ne hqle hq1
        obtain ⟨b, hbmass⟩ :=
          exists_sphericalCap_measure_eq hn u hu hqpos hqlt
        have hp_lt_q :
            μ (HDP.Chapter5.sphericalCap u a) < q :=
          lt_of_le_of_ne hpq (Ne.symm hqp)
        have hab : a ≤ b := by
          by_contra hnab
          have hba : b < a := lt_of_not_ge hnab
          have hsub :
              HDP.Chapter5.sphericalCap u b ⊆
                HDP.Chapter5.sphericalCap u a := by
            intro x hx
            exact hx.trans hba.le
          have hq_le_p :
              q ≤ μ (HDP.Chapter5.sphericalCap u a) := by
            rw [← hbmass]
            exact measure_mono hsub
          exact (not_le_of_gt hp_lt_q) hq_le_p
        exact ⟨b, hbmass, fun _ hx => hx.trans hab⟩
    have hbpos :
        0 < μ (HDP.Chapter5.sphericalCap u b) := by
      rw [hbmass]
      exact hqpos
    have hKmass :
        μ (K : Set (SphereE n)) =
          μ (HDP.Chapter5.sphericalCap u b) := by
      change q = μ (HDP.Chapter5.sphericalCap u b)
      exact hbmass.symm
    have hrbound :
        ∀ r : ℝ, 0 ≤ r → r < ε →
          μ (closedExpansion r
              (HDP.Chapter5.sphericalCap u a)) ≤
            μ (Metric.thickening ε A) := by
      intro r hr hre
      calc
        μ (closedExpansion r
            (HDP.Chapter5.sphericalCap u a)) ≤
            μ (closedExpansion r
              (HDP.Chapter5.sphericalCap u b)) :=
          measure_mono (closedExpansion_mono_set hCab r)
        _ ≤ μ (closedExpansion r
            (K : Set (SphereE n))) :=
          spherical_isoperimetric_compact hn K u hu b r hr
            hbpos hKmass
        _ ≤ μ (Metric.thickening ε A) :=
          measure_mono
            (closedExpansion_closure_subset_thickening A hre)
    have hCne :
        (HDP.Chapter5.sphericalCap u a).Nonempty :=
      nonempty_of_measure_ne_zero hcap.ne'
    calc
      μ (closedExpansion ε
          (HDP.Chapter5.sphericalCap u a)) =
          μ (Metric.thickening ε
            (HDP.Chapter5.sphericalCap u a)) :=
        unitSphereMeasure_closedExpansion_sphericalCap_eq_thickening
          hn u hu a ε hε hε2 hCne
      _ = μ (⋃ r : Set.Ico (0 : ℝ) ε,
          closedExpansion (r : ℝ)
            (HDP.Chapter5.sphericalCap u a)) := by
        rw [thickening_eq_iUnion_closedExpansion
          (HDP.Chapter5.sphericalCap u a) hε]
      _ = ⨆ r : Set.Ico (0 : ℝ) ε,
          μ (closedExpansion (r : ℝ)
            (HDP.Chapter5.sphericalCap u a)) := by
        apply Monotone.measure_iUnion
        intro r s hrs
        exact closedExpansion_mono_radius
          (HDP.Chapter5.sphericalCap u a)
          (show (r : ℝ) ≤ s from hrs)
      _ ≤ μ (Metric.thickening ε A) := by
        apply iSup_le
        intro r
        exact hrbound r r.property.1 r.property.2
      _ ≤ μ (closedExpansion ε A) := by
        apply measure_mono
        intro x hx
        rw [Metric.mem_thickening_iff] at hx
        rcases hx with ⟨y, hyA, hxy⟩
        exact ⟨y, hyA, hxy.le⟩
  · have h2ε : 2 ≤ ε := le_of_not_gt hε2
    have hAexp : closedExpansion ε A = Set.univ := by
      apply eq_univ_iff_forall.2
      intro x
      obtain ⟨y, hyA⟩ := hAne
      exact ⟨y, hyA, (dist_le_two_sphere x y).trans h2ε⟩
    rw [hAexp]
    exact measure_mono (μ := μ) (subset_univ _)

end

end HDP.Appendix
