import HighDimensionalProbability.Appendix.Infra.SphericalCapGeometry

/-!
# The compact-set spherical isoperimetric principle

We minimize the linear moment over the compact slack-admissible class.
Unless the minimizer contains the comparison cap, a reflection interchanging
an exterior support point with a missing interior cap point produces a strict
moment decrease while preserving admissibility.
-/

open MeasureTheory Set Metric InnerProductSpace Filter Function
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace HDP.Appendix

noncomputable section

variable {n : ℕ}

lemma measure_sdiff_eq_sdiff_of_measure_eq
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {B D : Set X} (hB : MeasurableSet B) (hD : MeasurableSet D)
    (hmass : μ D = μ B) :
    μ (D \ B) = μ (B \ D) := by
  rw [measure_sdiff' D hB.nullMeasurableSet (measure_ne_top μ B),
    measure_sdiff' B hD.nullMeasurableSet (measure_ne_top μ D),
    union_comm B D, hmass]

/-- A support point on the negative side and a missing point on the positive
side force the polarization gain to have positive measure. -/
lemma unitSphereMeasure_polarizationGain_pos_of_support
    [Nonempty (Fin n)]
    (B E : Set (SphereE n)) (hB : IsClosed B) (hE : MeasurableSet E)
    (hEB : E ⊆ B)
    (x y : SphereE n) (v : EuclideanSpace ℝ (Fin n))
    (hv : ‖v‖ = 1)
    (hreflect : sphereReflection v x = y)
    (hx : x ∈
      ((HDP.unitSphereMeasure
        (EuclideanSpace ℝ (Fin n))).restrict E).support)
    (hyB : y ∉ B) (hyplus : y ∈ openPlusHemisphere v) :
    0 < HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
      (polarizationGain v B) := by
  let μ := HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
  let V : Set (SphereE n) := Bᶜ ∩ openPlusHemisphere v
  let W : Set (SphereE n) := sphereReflection v ⁻¹' V
  have hVopen : IsOpen V :=
    hB.isOpen_compl.inter (isOpen_openPlusHemisphere v)
  have hyV : y ∈ V := ⟨hyB, hyplus⟩
  have hWopen : IsOpen W := hVopen.preimage (sphereReflection v).continuous
  have hxW : x ∈ W := by
    change sphereReflection v x ∈ V
    rw [hreflect]
    exact hyV
  have hrestrict_pos : 0 < (μ.restrict E) W :=
    (Measure.mem_support_iff_forall x).1 hx W
      (hWopen.mem_nhds hxW)
  have hWmeas : MeasurableSet W := hWopen.measurableSet
  rw [Measure.restrict_apply hWmeas] at hrestrict_pos
  have hWBpos : 0 < μ (W ∩ B) := by
    exact lt_of_lt_of_le hrestrict_pos
      (measure_mono (inter_subset_inter_right _ hEB))
  let T : Set (SphereE n) :=
    V ∩ sphereReflection v ⁻¹' B
  have hpre : sphereReflection v ⁻¹' T = W ∩ B := by
    ext z
    simp only [T, W, mem_preimage, mem_inter_iff,
      sphereReflection_involutive]
  have hTpos : 0 < μ T := by
    have hpres :=
      (measurePreserving_sphereReflection v).measure_preimage_emb
        (sphereReflection v).measurableEmbedding T
    rw [hpre] at hpres
    rwa [← hpres]
  exact lt_of_lt_of_le hTpos (measure_mono (by
    intro z hz
    refine ⟨⟨hz.2, ?_⟩, hz.1.2⟩
    exact hz.1.1))

/-- If a proper comparison cap is not contained in a compact equal-mass set,
some cap-oriented polarization strictly lowers the linear moment. -/
lemma exists_strict_sphericalPolarization_of_not_subset_cap
    [Nonempty (Fin n)] (hn : 2 ≤ n)
    (u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1)
    (a : ℝ) (ha : a ∈ Set.Ioo (-1 : ℝ) 1)
    (B : SphereCompacts n)
    (hmass :
      HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
          (B : Set (SphereE n)) =
        HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
          (HDP.Chapter5.sphericalCap u a))
    (hnsub :
      ¬ HDP.Chapter5.sphericalCap u a ⊆
        (B : Set (SphereE n))) :
    ∃ v : EuclideanSpace ℝ (Fin n), ∃ hv : ‖v‖ = 1,
      inner ℝ u v < 0 ∧
      0 < HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
        (polarizationGain v (B : Set (SphereE n))) := by
  let μ := HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
  let C := HDP.Chapter5.sphericalCap u a
  have hopen_not_subset :
      ¬ openSphericalCap u a ⊆ (B : Set (SphereE n)) := by
    intro hopen
    apply hnsub
    calc
      C ⊆ closure (openSphericalCap u a) :=
        sphericalCap_subset_closure_openSphericalCap u hu a ha
      _ ⊆ (B : Set (SphereE n)) :=
        B.isCompact.isClosed.closure_subset_iff.2 hopen
  obtain ⟨y, hyopen, hyB⟩ := Set.not_subset.1 hopen_not_subset
  let O : Set (SphereE n) :=
    openSphericalCap u a ∩ (B : Set (SphereE n))ᶜ
  have hOopen : IsOpen O :=
    (isOpen_openSphericalCap u a).inter
      B.isCompact.isClosed.isOpen_compl
  have hyO : y ∈ O := ⟨hyopen, hyB⟩
  have hOpos : 0 < μ O :=
    hOopen.measure_pos μ ⟨y, hyO⟩
  have hOsub : O ⊆ C \ (B : Set (SphereE n)) := by
    intro z hz
    exact ⟨openSphericalCap_subset_sphericalCap u a hz.1, hz.2⟩
  have hCBpos : 0 < μ (C \ (B : Set (SphereE n))) :=
    lt_of_lt_of_le hOpos (measure_mono hOsub)
  have hBCeq :
      μ ((B : Set (SphereE n)) \ C) =
        μ (C \ (B : Set (SphereE n))) := by
    exact measure_sdiff_eq_sdiff_of_measure_eq
      (B := C) (D := (B : Set (SphereE n)))
      (measurableSet_sphericalCap u a) B.isCompact.measurableSet
      hmass
  have hBCpos : 0 < μ ((B : Set (SphereE n)) \ C) := by
    rwa [hBCeq]
  let E : Set (SphereE n) := (B : Set (SphereE n)) \ C
  have hEmeas : MeasurableSet E :=
    B.isCompact.measurableSet.diff (measurableSet_sphericalCap u a)
  have hrestrict_ne : μ.restrict E ≠ 0 := by
    intro hzero
    have hEzero : μ E = 0 := Measure.restrict_eq_zero.mp hzero
    exact (ne_of_gt hBCpos) hEzero
  obtain ⟨x, hx⟩ := (μ.restrict E).nonempty_support hrestrict_ne
  have hxsupport :
      x ∈ closure E ∩ μ.support :=
    Measure.support_restrict_subset hx
  have hxcoord :
      a ≤ inner ℝ u (x : EuclideanSpace ℝ (Fin n)) := by
    have hEsub :
        E ⊆ {z : SphereE n |
          a ≤ inner ℝ u (z : EuclideanSpace ℝ (Fin n))} := by
      intro z hz
      rcases hz with ⟨hzB, hzC⟩
      change ¬ inner ℝ u (z : EuclideanSpace ℝ (Fin n)) ≤ a at hzC
      exact le_of_lt (lt_of_not_ge hzC)
    exact (isClosed_le continuous_const (by fun_prop)).closure_subset_iff.2
      hEsub hxsupport.1
  have hycoord :
      inner ℝ u (y : EuclideanSpace ℝ (Fin n)) < a := hyopen
  have hxy : x ≠ y := by
    intro h
    rw [h] at hxcoord
    linarith
  let v := normalizedChord x y
  have hv : ‖v‖ = 1 := norm_normalizedChord hxy
  refine ⟨v, hv, ?_, ?_⟩
  · exact inner_normalizedChord_direction_lt u hxy
      (lt_of_lt_of_le hycoord hxcoord)
  · apply unitSphereMeasure_polarizationGain_pos_of_support
      (B : Set (SphereE n)) E B.isCompact.isClosed hEmeas
      sdiff_subset x y v hv
      (sphereReflection_normalizedChord_left hxy) hx hyB
    exact inner_normalizedChord_right_pos hxy

/-- The moment attains a minimum on the compact admissible class. -/
lemma exists_sphericalMoment_minimizer
    [Nonempty (Fin n)]
    (K : SphereCompacts n)
    (u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1) :
    ∃ B ∈ sphericalAdmissible K,
      IsMinOn (sphericalMoment u) (sphericalAdmissible K) B := by
  have hcont :
      ContinuousOn (sphericalMoment u) (sphericalAdmissible K) :=
    (continuousOn_sphericalMoment_fixedMass u hu K).mono
      (fun _ hB => hB.1)
  exact (isCompact_sphericalAdmissible K).exists_isMinOn
    (sphericalAdmissible_nonempty K) hcont

/-- Compact equal-mass sets satisfy the spherical isoperimetric comparison,
with the harmless strict radius slack used in the Hausdorff minimization. -/
lemma spherical_isoperimetric_compact_slack
    [Nonempty (Fin n)] (hn : 2 ≤ n)
    (K : SphereCompacts n)
    (u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1)
    (a : ℝ)
    (hcap : 0 < HDP.unitSphereMeasure
      (EuclideanSpace ℝ (Fin n))
      (HDP.Chapter5.sphericalCap u a))
    (hmass :
      HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
          (K : Set (SphereE n)) =
        HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
          (HDP.Chapter5.sphericalCap u a)) :
    ∀ r s : ℝ, 0 ≤ r → r < s →
      HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
          (closedExpansion r (HDP.Chapter5.sphericalCap u a)) ≤
        HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
          (closedExpansion s (K : Set (SphereE n))) := by
  intro r s hr hrs
  have ha_lower : -1 < a :=
    neg_one_lt_of_sphericalCap_measure_pos hn u hu a hcap
  by_cases ha_upper : a < 1
  · have ha : a ∈ Set.Ioo (-1 : ℝ) 1 := ⟨ha_lower, ha_upper⟩
    obtain ⟨B, hBadm, hBmin⟩ :=
      exists_sphericalMoment_minimizer K u hu
    have hCB :
        HDP.Chapter5.sphericalCap u a ⊆
          (B : Set (SphereE n)) := by
      by_contra hnsub
      obtain ⟨v, hv, huv, hgain⟩ :=
        exists_strict_sphericalPolarization_of_not_subset_cap
          hn u hu a ha B (hBadm.1.trans hmass) hnsub
      have hPadm :=
        sphericalPolarization_mem_sphericalAdmissible
          hn K B hBadm v hv
      have hminle :=
        (isMinOn_iff.mp hBmin) (polarizedCompacts B v hv) hPadm
      have hlt :=
        sphericalMoment_polarizedCompacts_lt u v hv huv B hgain
      linarith
    calc
      HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
          (closedExpansion r (HDP.Chapter5.sphericalCap u a)) ≤
          HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
            (closedExpansion r (B : Set (SphereE n))) :=
        measure_mono (closedExpansion_mono_set hCB r)
      _ ≤ HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
          (closedExpansion s (K : Set (SphereE n))) :=
        hBadm.2 r s hr hrs
  · have ha1 : 1 ≤ a := le_of_not_gt ha_upper
    have hCuniv := sphericalCap_eq_univ_of_one_le u hu a ha1
    have hKcompl :
        HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
          ((K : Set (SphereE n))ᶜ) = 0 := by
      rw [measure_compl K.isCompact.measurableSet
        (measure_ne_top _ _), hmass, hCuniv, tsub_self]
    have hKuniv : (K : Set (SphereE n)) = Set.univ := by
      apply eq_univ_iff_forall.2
      intro x
      by_contra hx
      have hpos :
          0 < HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
            ((K : Set (SphereE n))ᶜ) :=
        K.isCompact.isClosed.isOpen_compl.measure_pos _
          ⟨x, hx⟩
      rw [hKcompl] at hpos
      exact lt_irrefl 0 hpos
    rw [hCuniv, hKuniv]
    exact measure_mono
      (closedExpansion_mono_radius (Set.univ : Set (SphereE n)) hrs.le)

end

end HDP.Appendix
