import HighDimensionalProbability.Appendix.Infra.SphericalMinimizer

/-!
# Exact metric expansions of spherical caps

Polarization geometry implies that moving a point toward a cap (in the order
of the defining linear coordinate) cannot increase its distance to the cap.
Consequently every closed chordal expansion of a cap is again a cap.

For radii below the diameter of the unit sphere, the open expansion is dense
in the closed expansion.  This shows that the two expansions differ only on
one spherical-coordinate level set and hence have the same normalized surface
measure.
-/

open MeasureTheory Set Metric InnerProductSpace Filter Function
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace HDP.Appendix

noncomputable section

variable {n : ℕ}

/-- Reflecting a point toward a cap cannot increase its distance to any
appropriate reflected cap point. -/
lemma exists_sphericalCap_point_dist_le_of_coord_le
    (u : EuclideanSpace ℝ (Fin n)) (a : ℝ)
    {x y z : SphereE n}
    (hz : z ∈ HDP.Chapter5.sphericalCap u a)
    (hcoord :
      inner ℝ u (y : EuclideanSpace ℝ (Fin n)) ≤
        inner ℝ u (x : EuclideanSpace ℝ (Fin n))) :
    ∃ w ∈ HDP.Chapter5.sphericalCap u a,
      dist y w ≤ dist x z := by
  by_cases hxy : x = y
  · subst y
    exact ⟨z, hz, le_rfl⟩
  let v := normalizedChord x y
  have hv : ‖v‖ = 1 := norm_normalizedChord hxy
  have hreflect : sphereReflection v x = y :=
    sphereReflection_normalizedChord_left hxy
  have hyplus : y ∈ closedPlusHemisphere v := by
    change 0 ≤ inner ℝ v (y : EuclideanSpace ℝ (Fin n))
    exact (inner_normalizedChord_right_pos hxy).le
  have huv : inner ℝ u v ≤ 0 :=
    inner_normalizedChord_direction_le u hxy hcoord
  by_cases hzplus : z ∈ closedPlusHemisphere v
  · refine ⟨z, hz, ?_⟩
    have hle :=
      dist_le_dist_sphereReflection_of_closedPlus v hv hyplus hzplus
    have hiso := sphereReflection_dist v x z
    rw [hreflect] at hiso
    exact hle.trans_eq hiso
  · have hzminus : z ∈ closedMinusHemisphere v := by
      change inner ℝ v (z : EuclideanSpace ℝ (Fin n)) ≤ 0
      change ¬ 0 ≤ inner ℝ v (z : EuclideanSpace ℝ (Fin n)) at hzplus
      exact (lt_of_not_ge hzplus).le
    refine ⟨sphereReflection v z, ?_, ?_⟩
    · have hzP :
          z ∈ sphericalPolarization v
            (HDP.Chapter5.sphericalCap u a) := by
        rw [sphericalPolarization_sphericalCap v hv u a huv]
        exact hz
      exact
        (mem_sphericalPolarization_closedMinus v hv hzminus).1 hzP |>.2
    · have hiso := sphereReflection_dist v x z
      rw [hreflect] at hiso
      exact hiso.le

lemma closedExpansion_sphericalCap_coord_mono
    (u : EuclideanSpace ℝ (Fin n)) (a ε : ℝ)
    {x y : SphereE n}
    (hx : x ∈ closedExpansion ε (HDP.Chapter5.sphericalCap u a))
    (hcoord :
      inner ℝ u (y : EuclideanSpace ℝ (Fin n)) ≤
        inner ℝ u (x : EuclideanSpace ℝ (Fin n))) :
    y ∈ closedExpansion ε (HDP.Chapter5.sphericalCap u a) := by
  rcases hx with ⟨z, hz, hxz⟩
  obtain ⟨w, hw, hyw⟩ :=
    exists_sphericalCap_point_dist_le_of_coord_le u a hz hcoord
  exact ⟨w, hw, hyw.trans hxz⟩

lemma thickening_sphericalCap_coord_mono
    (u : EuclideanSpace ℝ (Fin n)) (a ε : ℝ)
    {x y : SphereE n}
    (hx : x ∈ Metric.thickening ε (HDP.Chapter5.sphericalCap u a))
    (hcoord :
      inner ℝ u (y : EuclideanSpace ℝ (Fin n)) ≤
        inner ℝ u (x : EuclideanSpace ℝ (Fin n))) :
    y ∈ Metric.thickening ε (HDP.Chapter5.sphericalCap u a) := by
  rw [Metric.mem_thickening_iff] at hx ⊢
  rcases hx with ⟨z, hz, hxz⟩
  obtain ⟨w, hw, hyw⟩ :=
    exists_sphericalCap_point_dist_le_of_coord_le u a hz hcoord
  exact ⟨w, hw, hyw.trans_lt hxz⟩

/-- A nonempty closed expansion of a spherical cap is another spherical cap;
`x₀` is a point on its top coordinate level. -/
lemma exists_closedExpansion_sphericalCap_eq_sphericalCap
    [Nonempty (Fin n)]
    (u : EuclideanSpace ℝ (Fin n)) (a ε : ℝ) (hε : 0 ≤ ε)
    (hC : (HDP.Chapter5.sphericalCap u a).Nonempty) :
    ∃ b : ℝ, ∃ x₀ : SphereE n,
      x₀ ∈ closedExpansion ε (HDP.Chapter5.sphericalCap u a) ∧
      sphereLinearCoordinate u x₀ = b ∧
      closedExpansion ε (HDP.Chapter5.sphericalCap u a) =
        HDP.Chapter5.sphericalCap u b := by
  let D : Set (SphereE n) :=
    closedExpansion ε (HDP.Chapter5.sphericalCap u a)
  have hDclosed : IsClosed D := by
    dsimp [D]
    rw [closedExpansion_eq_cthickening (isClosed_sphericalCap u a) hε]
    exact Metric.isClosed_cthickening
  have hDcompact : IsCompact D := hDclosed.isCompact
  have hDne : D.Nonempty := by
    obtain ⟨z, hz⟩ := hC
    exact ⟨z, z, hz, (dist_self z).le.trans hε⟩
  have hcont : ContinuousOn (sphereLinearCoordinate u) D := by
    unfold sphereLinearCoordinate
    fun_prop
  obtain ⟨x₀, hx₀D, hx₀max⟩ :=
    hDcompact.exists_isMaxOn hDne hcont
  let b := sphereLinearCoordinate u x₀
  refine ⟨b, x₀, hx₀D, rfl, ?_⟩
  ext y
  constructor
  · intro hyD
    change sphereLinearCoordinate u y ≤ b
    exact (isMaxOn_iff.mp hx₀max) y hyD
  · intro hycap
    apply closedExpansion_sphericalCap_coord_mono u a ε hx₀D
    exact hycap

lemma dist_sq_eq_two_sub_two_mul_inner
    (x y : SphereE n) :
    dist x y ^ 2 =
      2 - 2 * inner ℝ
        (x : EuclideanSpace ℝ (Fin n))
        (y : EuclideanSpace ℝ (Fin n)) := by
  change
    ‖(x : EuclideanSpace ℝ (Fin n)) -
      (y : EuclideanSpace ℝ (Fin n))‖ ^ 2 = _
  rw [norm_sub_sq_real,
    mem_sphere_zero_iff_norm.mp x.property,
    mem_sphere_zero_iff_norm.mp y.property]
  ring

/-- Below the sphere diameter, the open expansion of a compact cap is dense
in its closed expansion. -/
lemma closure_thickening_sphericalCap
    [Nonempty (Fin n)]
    (u : EuclideanSpace ℝ (Fin n)) (a ε : ℝ)
    (hε : 0 < ε) (hε2 : ε < 2) :
    closure (Metric.thickening ε (HDP.Chapter5.sphericalCap u a)) =
      closedExpansion ε (HDP.Chapter5.sphericalCap u a) := by
  apply le_antisymm
  · rw [closedExpansion_eq_cthickening (isClosed_sphericalCap u a) hε.le]
    exact Metric.closure_thickening_subset_cthickening ε _
  · intro x hx
    rcases hx with ⟨z, hzC, hxz⟩
    by_cases hlt : dist x z < ε
    · exact subset_closure
        (Metric.mem_thickening_iff.2 ⟨z, hzC, hlt⟩)
    have hdist : dist x z = ε := le_antisymm hxz (le_of_not_gt hlt)
    have hxzne : x ≠ z := by
      intro h
      rw [h, dist_self] at hdist
      linarith
    let c : ℝ :=
      inner ℝ (z : EuclideanSpace ℝ (Fin n))
        (x : EuclideanSpace ℝ (Fin n))
    have hc_upper : c < 1 := by
      exact (inner_lt_one_iff_real_of_norm_eq_one
        (mem_sphere_zero_iff_norm.mp z.property)
        (mem_sphere_zero_iff_norm.mp x.property)).2 (by
          intro h
          apply hxzne
          exact Subtype.ext h.symm)
    have hc_lower : -1 < c := by
      have hsq := dist_sq_eq_two_sub_two_mul_inner x z
      have hcomm :
          inner ℝ (x : EuclideanSpace ℝ (Fin n))
              (z : EuclideanSpace ℝ (Fin n)) = c := by
        dsimp [c]
        rw [real_inner_comm]
      rw [hcomm, hdist] at hsq
      nlinarith
    let q : EuclideanSpace ℝ (Fin n) :=
      (x : EuclideanSpace ℝ (Fin n)) - c •
        (z : EuclideanSpace ℝ (Fin n))
    have hqne : q ≠ 0 := by
      intro hq
      have hxcz :
          (x : EuclideanSpace ℝ (Fin n)) =
            c • (z : EuclideanSpace ℝ (Fin n)) :=
        sub_eq_zero.mp hq
      have hnormx :
          ‖(x : EuclideanSpace ℝ (Fin n))‖ = 1 :=
        mem_sphere_zero_iff_norm.mp x.property
      rw [hxcz, norm_smul,
        mem_sphere_zero_iff_norm.mp z.property] at hnormx
      have habs : |c| = 1 := by simpa using hnormx
      have habslt : |c| < 1 := abs_lt.mpr ⟨hc_lower, hc_upper⟩
      linarith
    let w : EuclideanSpace ℝ (Fin n) := NormedSpace.normalize q
    have hw : ‖w‖ = 1 := NormedSpace.norm_normalize hqne
    have hzw : inner ℝ (z : EuclideanSpace ℝ (Fin n)) w = 0 := by
      dsimp [w, q, NormedSpace.normalize]
      rw [inner_smul_right, inner_sub_right, inner_smul_right,
        real_inner_self_eq_norm_sq,
        mem_sphere_zero_iff_norm.mp z.property]
      dsimp [c]
      ring
    let F : ℝ → SphereE n :=
      sphericalMeridian
        (z : EuclideanSpace ℝ (Fin n)) w
        (mem_sphere_zero_iff_norm.mp z.property) hw hzw
    have hFc : F c = x := by
      exact sphericalMeridian_eq_of_boundary
        (z : EuclideanSpace ℝ (Fin n))
        (mem_sphere_zero_iff_norm.mp z.property)
        c ⟨hc_lower, hc_upper⟩ x rfl
    have hc_closure : c ∈ closure (Set.Ioo c (1 : ℝ)) := by
      rw [closure_Ioo (ne_of_lt hc_upper)]
      exact ⟨le_rfl, hc_upper.le⟩
    have hmaps :
        MapsTo F (Set.Ioo c (1 : ℝ))
          (Metric.thickening ε (HDP.Chapter5.sphericalCap u a)) := by
      intro b hb
      rw [Metric.mem_thickening_iff]
      refine ⟨z, hzC, ?_⟩
      have hcoordF :
          inner ℝ (z : EuclideanSpace ℝ (Fin n))
              ((F b : SphereE n) :
                EuclideanSpace ℝ (Fin n)) = b := by
        exact sphereLinearCoordinate_sphericalMeridian_of_mem_Icc
          (z : EuclideanSpace ℝ (Fin n)) w
          (mem_sphere_zero_iff_norm.mp z.property) hw hzw
          ⟨hc_lower.le.trans hb.1.le, hb.2.le⟩
      have hsqF := dist_sq_eq_two_sub_two_mul_inner (F b) z
      have hcommF :
          inner ℝ ((F b : SphereE n) :
              EuclideanSpace ℝ (Fin n))
              (z : EuclideanSpace ℝ (Fin n)) = b := by
        rw [real_inner_comm]
        exact hcoordF
      rw [hcommF] at hsqF
      have hsqxz := dist_sq_eq_two_sub_two_mul_inner x z
      have hcommxz :
          inner ℝ (x : EuclideanSpace ℝ (Fin n))
              (z : EuclideanSpace ℝ (Fin n)) = c := by
        dsimp [c]
        rw [real_inner_comm]
      rw [hcommxz, hdist] at hsqxz
      have hsqlt : dist (F b) z ^ 2 < ε ^ 2 := by
        rw [hsqF, hsqxz]
        linarith [hb.1]
      exact (sq_lt_sq₀ dist_nonneg hε.le).mp hsqlt
    have hcont :
        ContinuousWithinAt F (Set.Ioo c (1 : ℝ)) c :=
      ContinuousAt.continuousWithinAt
        (continuous_sphericalMeridian
          (z : EuclideanSpace ℝ (Fin n)) w
          (mem_sphere_zero_iff_norm.mp z.property) hw hzw).continuousAt
    have hmem := hcont.mem_closure hc_closure hmaps
    rwa [hFc] at hmem

/-- For a positive radius smaller than the diameter, a cap's open and closed
expansions have the same normalized surface measure. -/
lemma unitSphereMeasure_closedExpansion_sphericalCap_eq_thickening
    [Nonempty (Fin n)] (hn : 2 ≤ n)
    (u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1)
    (a ε : ℝ) (hε : 0 < ε) (hε2 : ε < 2)
    (hC : (HDP.Chapter5.sphericalCap u a).Nonempty) :
    HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
        (closedExpansion ε (HDP.Chapter5.sphericalCap u a)) =
      HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
        (Metric.thickening ε (HDP.Chapter5.sphericalCap u a)) := by
  let D := closedExpansion ε (HDP.Chapter5.sphericalCap u a)
  let T := Metric.thickening ε (HDP.Chapter5.sphericalCap u a)
  obtain ⟨b, x₀, hx₀D, hx₀b, hDcap⟩ :=
    exists_closedExpansion_sphericalCap_eq_sphericalCap
      u a ε hε.le hC
  have hclosure : closure T = D :=
    closure_thickening_sphericalCap u a ε hε hε2
  have hopen_subset :
      openSphericalCap u b ⊆ T := by
    intro y hy
    let O : Set (SphereE n) :=
      {x | sphereLinearCoordinate u y < sphereLinearCoordinate u x}
    have hOopen : IsOpen O := isOpen_lt continuous_const (by
      unfold sphereLinearCoordinate
      fun_prop)
    have hx₀O : x₀ ∈ O := by
      change sphereLinearCoordinate u y < sphereLinearCoordinate u x₀
      rw [hx₀b]
      exact hy
    have hx₀cl : x₀ ∈ closure T := by
      rw [hclosure]
      exact hx₀D
    have hfreqT := mem_closure_iff_frequently.1 hx₀cl
    have heventO : ∀ᶠ x in 𝓝 x₀, x ∈ O :=
      hOopen.mem_nhds hx₀O
    obtain ⟨x, hxT, hxO⟩ :=
      (hfreqT.and_eventually heventO).exists
    apply thickening_sphericalCap_coord_mono u a ε hxT
    exact hxO.le
  have hdiffsub :
      D \ T ⊆ {x : SphereE n | sphereLinearCoordinate u x = b} := by
    intro x hx
    have hxcap : x ∈ HDP.Chapter5.sphericalCap u b := by
      rw [← hDcap]
      exact hx.1
    change sphereLinearCoordinate u x = b
    apply le_antisymm hxcap
    by_contra hlt
    have hxopen : x ∈ openSphericalCap u b := lt_of_not_ge hlt
    exact hx.2 (hopen_subset hxopen)
  have hdiffzero :
      HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)) (D \ T) = 0 :=
    measure_mono_null hdiffsub
      (unitSphereMeasure_sphereLinearCoordinate_level hn u hu b)
  have hTmeas : MeasurableSet T := Metric.isOpen_thickening.measurableSet
  have hTD : T ⊆ D := by
    intro x hx
    rw [Metric.mem_thickening_iff] at hx
    rcases hx with ⟨z, hz, hxz⟩
    exact ⟨z, hz, hxz.le⟩
  calc
    HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)) D =
        HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)) T +
          HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)) (D \ T) := by
      have h :=
        measure_union
          (μ := HDP.unitSphereMeasure
            (EuclideanSpace ℝ (Fin n)))
          (s₁ := D \ T) (s₂ := T)
          disjoint_sdiff_left hTmeas
      rw [Set.sdiff_union_of_subset hTD] at h
      simpa [add_comm] using h
    _ = HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)) T := by
      rw [hdiffzero, add_zero]

end

end HDP.Appendix
