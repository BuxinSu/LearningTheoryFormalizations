import HighDimensionalProbability.Appendix.Infra.SphericalMoment
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Order.Interval.Set.ProjIcc

/-!
# Geometry of spherical caps

This file supplies the local geometry used by the global polarization
argument: proper caps are closures of their strict interiors, level sets of a
spherical linear coordinate are null, and a normalized chord is the normal of
the reflection interchanging its endpoints.
-/

open MeasureTheory Set Metric InnerProductSpace Filter Function
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace HDP.Appendix

noncomputable section

variable {n : ℕ}

/-- The strict interior of the cap with threshold `a`. -/
def openSphericalCap
    (u : EuclideanSpace ℝ (Fin n)) (a : ℝ) :
    Set (SphereE n) :=
  {x | inner ℝ u (x : EuclideanSpace ℝ (Fin n)) < a}

lemma isClosed_sphericalCap
    (u : EuclideanSpace ℝ (Fin n)) (a : ℝ) :
    IsClosed (HDP.Chapter5.sphericalCap u a) := by
  exact isClosed_le (by fun_prop) continuous_const

lemma measurableSet_sphericalCap
    (u : EuclideanSpace ℝ (Fin n)) (a : ℝ) :
    MeasurableSet (HDP.Chapter5.sphericalCap u a) :=
  (isClosed_sphericalCap u a).measurableSet

lemma isOpen_openSphericalCap
    (u : EuclideanSpace ℝ (Fin n)) (a : ℝ) :
    IsOpen (openSphericalCap u a) := by
  exact isOpen_lt (by fun_prop) continuous_const

lemma measurableSet_openSphericalCap
    (u : EuclideanSpace ℝ (Fin n)) (a : ℝ) :
    MeasurableSet (openSphericalCap u a) :=
  (isOpen_openSphericalCap u a).measurableSet

lemma openSphericalCap_subset_sphericalCap
    (u : EuclideanSpace ℝ (Fin n)) (a : ℝ) :
    openSphericalCap u a ⊆ HDP.Chapter5.sphericalCap u a := by
  intro x hx
  change inner ℝ u (x : EuclideanSpace ℝ (Fin n)) ≤ a
  exact hx.le

/-- Every level set of a nonzero unit spherical coordinate has zero surface
measure. -/
lemma unitSphereMeasure_sphereLinearCoordinate_level
    [Nonempty (Fin n)] (hn : 2 ≤ n)
    (u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1) (a : ℝ) :
    HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
        {x : SphereE n | sphereLinearCoordinate u x = a} = 0 := by
  let μ := HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
  have hno :
      NoAtoms (Measure.map (sphereLinearCoordinate u) μ) :=
    noAtoms_map_sphereLinearCoordinate_unitSphereMeasure u hu
      (by simpa [finrank_euclideanSpace] using hn)
  letI : NoAtoms (Measure.map (sphereLinearCoordinate u) μ) := hno
  have hsingleton :
      Measure.map (sphereLinearCoordinate u) μ ({a} : Set ℝ) = 0 :=
    measure_singleton a
  rw [Measure.map_apply (measurable_sphereLinearCoordinate u)
    (measurableSet_singleton a)] at hsingleton
  exact hsingleton

lemma unitSphereMeasure_sphericalCap_boundary
    [Nonempty (Fin n)] (hn : 2 ≤ n)
    (u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1) (a : ℝ) :
    HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
        (HDP.Chapter5.sphericalCap u a \ openSphericalCap u a) = 0 := by
  apply measure_mono_null ?_
    (unitSphereMeasure_sphereLinearCoordinate_level hn u hu a)
  intro x hx
  rcases hx with ⟨hxcap, hxopen⟩
  change inner ℝ u (x : EuclideanSpace ℝ (Fin n)) = a
  change inner ℝ u (x : EuclideanSpace ℝ (Fin n)) ≤ a at hxcap
  change ¬ inner ℝ u (x : EuclideanSpace ℝ (Fin n)) < a at hxopen
  exact le_antisymm hxcap (le_of_not_gt hxopen)

lemma neg_one_lt_of_sphericalCap_measure_pos
    [Nonempty (Fin n)] (hn : 2 ≤ n)
    (u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1)
    (a : ℝ)
    (hcap : 0 < HDP.unitSphereMeasure
      (EuclideanSpace ℝ (Fin n))
      (HDP.Chapter5.sphericalCap u a)) :
    -1 < a := by
  by_contra ha
  have ha' : a ≤ -1 := le_of_not_gt ha
  have hsub :
      HDP.Chapter5.sphericalCap u a ⊆
        {x : SphereE n | sphereLinearCoordinate u x = -1} := by
    intro x hx
    have hlower :=
      neg_one_le_real_inner_of_norm_eq_one hu
        (mem_sphere_zero_iff_norm.mp x.property)
    change sphereLinearCoordinate u x = -1
    change inner ℝ u (x : EuclideanSpace ℝ (Fin n)) ≤ a at hx
    change inner ℝ u (x : EuclideanSpace ℝ (Fin n)) = -1
    linarith
  have hzero :
      HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
          (HDP.Chapter5.sphericalCap u a) = 0 :=
    measure_mono_null hsub
      (unitSphereMeasure_sphereLinearCoordinate_level hn u hu (-1))
  rw [hzero] at hcap
  exact lt_irrefl 0 hcap

lemma sphericalCap_eq_univ_of_one_le
    (u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1)
    (a : ℝ) (ha : 1 ≤ a) :
    HDP.Chapter5.sphericalCap u a = Set.univ := by
  ext x
  simp only [HDP.Chapter5.sphericalCap, mem_setOf_eq, mem_univ, iff_true]
  exact (real_inner_le_one_of_norm_eq_one hu
    (mem_sphere_zero_iff_norm.mp x.property)).trans ha

/-- The elementary norm calculation underlying a spherical meridian. -/
lemma norm_meridianVector
    (u w : EuclideanSpace ℝ (Fin n))
    (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (huw : inner ℝ u w = 0)
    (c : ℝ) (hc : c ∈ Set.Icc (-1 : ℝ) 1) :
    ‖c • u + Real.sqrt (1 - c ^ 2) • w‖ = 1 := by
  have hs : 0 ≤ 1 - c ^ 2 := by
    have hp : 0 ≤ (1 - c) * (1 + c) :=
      mul_nonneg (sub_nonneg.mpr hc.2) (by linarith [hc.1])
    nlinarith
  apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num)).mp
  rw [norm_add_sq_real, norm_smul, norm_smul, hu, hw,
    Real.norm_eq_abs, Real.norm_eq_abs,
    real_inner_smul_left, real_inner_smul_right, huw]
  simp only [mul_zero, add_zero, mul_one, one_pow]
  rw [sq_abs, sq_abs, Real.sq_sqrt hs]
  ring

/-- A great-circle meridian through two orthogonal unit vectors, with its
parameter projected to `[-1,1]`. -/
def sphericalMeridian
    (u w : EuclideanSpace ℝ (Fin n))
    (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (huw : inner ℝ u w = 0)
    (b : ℝ) : SphereE n :=
  ⟨(Set.projIcc (-1 : ℝ) 1 (by norm_num) b : ℝ) • u +
      Real.sqrt
        (1 - (Set.projIcc (-1 : ℝ) 1 (by norm_num) b : ℝ) ^ 2) • w,
    by
      rw [mem_sphere_zero_iff_norm]
      exact norm_meridianVector u w hu hw huw _
        (Set.projIcc (-1 : ℝ) 1 (by norm_num) b).property⟩

lemma sphericalMeridian_coe
    (u w : EuclideanSpace ℝ (Fin n))
    (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (huw : inner ℝ u w = 0)
    (b : ℝ) :
    ((sphericalMeridian u w hu hw huw b : SphereE n) :
        EuclideanSpace ℝ (Fin n)) =
      (Set.projIcc (-1 : ℝ) 1 (by norm_num) b : ℝ) • u +
        Real.sqrt
          (1 - (Set.projIcc (-1 : ℝ) 1 (by norm_num) b : ℝ) ^ 2) • w :=
  rfl

lemma continuous_sphericalMeridian
    (u w : EuclideanSpace ℝ (Fin n))
    (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (huw : inner ℝ u w = 0) :
    Continuous (sphericalMeridian u w hu hw huw) := by
  apply continuous_induced_rng.2
  change Continuous (fun b =>
    ((sphericalMeridian u w hu hw huw b : SphereE n) :
      EuclideanSpace ℝ (Fin n)))
  rw [show (fun b =>
      ((sphericalMeridian u w hu hw huw b : SphereE n) :
        EuclideanSpace ℝ (Fin n))) =
      fun b =>
        (Set.projIcc (-1 : ℝ) 1 (by norm_num) b : ℝ) • u +
          Real.sqrt
            (1 - (Set.projIcc (-1 : ℝ) 1
              (by norm_num) b : ℝ) ^ 2) • w by
        funext b
        rfl]
  fun_prop

lemma sphereLinearCoordinate_sphericalMeridian_of_mem_Icc
    (u w : EuclideanSpace ℝ (Fin n))
    (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (huw : inner ℝ u w = 0)
    {b : ℝ} (hb : b ∈ Set.Icc (-1 : ℝ) 1) :
    sphereLinearCoordinate u (sphericalMeridian u w hu hw huw b) = b := by
  rw [sphereLinearCoordinate, sphericalMeridian_coe,
    Set.projIcc_of_mem (by norm_num) hb]
  rw [inner_add_right, inner_smul_right, inner_smul_right,
    real_inner_self_eq_norm_sq, hu, huw]
  simp

lemma sphericalMeridian_eq_of_boundary
    (u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1)
    (a : ℝ) (ha : a ∈ Set.Ioo (-1 : ℝ) 1)
    (x : SphereE n)
    (hx : inner ℝ u (x : EuclideanSpace ℝ (Fin n)) = a) :
    let q : EuclideanSpace ℝ (Fin n) :=
      (x : EuclideanSpace ℝ (Fin n)) - a • u
    let w := NormedSpace.normalize q
    sphericalMeridian u w hu
      (NormedSpace.norm_normalize (by
        intro hq
        have hxau : (x : EuclideanSpace ℝ (Fin n)) = a • u := by
          dsimp [q] at hq
          exact sub_eq_zero.mp hq
        have hnormx : ‖(x : EuclideanSpace ℝ (Fin n))‖ = 1 :=
          mem_sphere_zero_iff_norm.mp x.property
        rw [hxau, norm_smul, hu] at hnormx
        have habs : |a| = 1 := by simpa using hnormx
        have habslt : |a| < 1 := abs_lt.mpr ha
        linarith))
      (by
        dsimp [w, q, NormedSpace.normalize]
        rw [inner_smul_right, inner_sub_right, inner_smul_right,
          real_inner_self_eq_norm_sq, hu, hx]
        simp)
      a = x := by
  dsimp
  apply Subtype.ext
  rw [sphericalMeridian_coe,
    Set.projIcc_of_mem (by norm_num) ⟨ha.1.le, ha.2.le⟩]
  let q : EuclideanSpace ℝ (Fin n) :=
    (x : EuclideanSpace ℝ (Fin n)) - a • u
  have hqinner : inner ℝ u q = 0 := by
    dsimp [q]
    rw [inner_sub_right, inner_smul_right,
      real_inner_self_eq_norm_sq, hu, hx]
    ring
  have hqnormsq : ‖q‖ ^ 2 = 1 - a ^ 2 := by
    have hxu :
        inner ℝ (x : EuclideanSpace ℝ (Fin n)) u = a := by
      rw [real_inner_comm]
      exact hx
    dsimp [q]
    rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
      mem_sphere_zero_iff_norm.mp x.property, hu,
      inner_smul_right, hxu]
    simp only [mul_one]
    rw [sq_abs]
    ring
  have hs : 0 ≤ 1 - a ^ 2 := by nlinarith
  have hsqrt : Real.sqrt (1 - a ^ 2) = ‖q‖ := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (norm_nonneg _)).mp
    rw [Real.sq_sqrt hs, hqnormsq]
  rw [hsqrt, NormedSpace.norm_smul_normalize]
  dsimp [q]
  abel

/-- A proper closed cap is the closure of its strict interior. -/
lemma sphericalCap_subset_closure_openSphericalCap
    (u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1)
    (a : ℝ) (ha : a ∈ Set.Ioo (-1 : ℝ) 1) :
    HDP.Chapter5.sphericalCap u a ⊆
      closure (openSphericalCap u a) := by
  intro x hx
  by_cases hstrict : x ∈ openSphericalCap u a
  · exact subset_closure hstrict
  · have hxeq :
        inner ℝ u (x : EuclideanSpace ℝ (Fin n)) = a := by
      change inner ℝ u (x : EuclideanSpace ℝ (Fin n)) ≤ a at hx
      change ¬ inner ℝ u (x : EuclideanSpace ℝ (Fin n)) < a at hstrict
      exact le_antisymm hx (le_of_not_gt hstrict)
    let q : EuclideanSpace ℝ (Fin n) :=
      (x : EuclideanSpace ℝ (Fin n)) - a • u
    have hqne : q ≠ 0 := by
      intro hq
      have hxau : (x : EuclideanSpace ℝ (Fin n)) = a • u := by
        exact sub_eq_zero.mp hq
      have hnormx : ‖(x : EuclideanSpace ℝ (Fin n))‖ = 1 :=
        mem_sphere_zero_iff_norm.mp x.property
      rw [hxau, norm_smul, hu] at hnormx
      have habs : |a| = 1 := by simpa using hnormx
      have habslt : |a| < 1 := abs_lt.mpr ha
      linarith
    let w : EuclideanSpace ℝ (Fin n) := NormedSpace.normalize q
    have hw : ‖w‖ = 1 := NormedSpace.norm_normalize hqne
    have huw : inner ℝ u w = 0 := by
      dsimp [w, q, NormedSpace.normalize]
      rw [inner_smul_right, inner_sub_right, inner_smul_right,
        real_inner_self_eq_norm_sq, hu, hxeq]
      simp
    let F : ℝ → SphereE n := sphericalMeridian u w hu hw huw
    have ha_closure : a ∈ closure (Set.Ioo (-1 : ℝ) a) := by
      rw [closure_Ioo (ne_of_lt ha.1)]
      exact ⟨ha.1.le, le_rfl⟩
    have hmaps :
        MapsTo F (Set.Ioo (-1 : ℝ) a) (openSphericalCap u a) := by
      intro b hb
      change sphereLinearCoordinate u (F b) < a
      rw [sphereLinearCoordinate_sphericalMeridian_of_mem_Icc
        u w hu hw huw ⟨hb.1.le, hb.2.trans ha.2 |>.le⟩]
      exact hb.2
    have hmem :
        F a ∈ closure (openSphericalCap u a) :=
      by
        have hcont :
            ContinuousWithinAt F (Set.Ioo (-1 : ℝ) a) a :=
          ContinuousAt.continuousWithinAt
            (continuous_sphericalMeridian u w hu hw huw).continuousAt
        exact hcont.mem_closure ha_closure hmaps
    have hFa : F a = x := by
      exact sphericalMeridian_eq_of_boundary u hu a ha x hxeq
    rwa [hFa] at hmem

lemma closure_openSphericalCap_eq_sphericalCap
    (u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1)
    (a : ℝ) (ha : a ∈ Set.Ioo (-1 : ℝ) 1) :
    closure (openSphericalCap u a) =
      HDP.Chapter5.sphericalCap u a := by
  apply le_antisymm
  · exact (isClosed_sphericalCap u a).closure_subset_iff.2
      (openSphericalCap_subset_sphericalCap u a)
  · exact sphericalCap_subset_closure_openSphericalCap u hu a ha

/-- The normalized chord from `x` to `y`. -/
def normalizedChord (x y : SphereE n) :
    EuclideanSpace ℝ (Fin n) :=
  NormedSpace.normalize
    ((y : EuclideanSpace ℝ (Fin n)) -
      (x : EuclideanSpace ℝ (Fin n)))

lemma norm_normalizedChord {x y : SphereE n} (hxy : x ≠ y) :
    ‖normalizedChord x y‖ = 1 := by
  apply NormedSpace.norm_normalize
  intro h
  apply hxy
  apply Subtype.ext
  exact sub_eq_zero.mp h |>.symm

lemma hyperplaneReflection_normalizedChord_left
    {x y : SphereE n} (hxy : x ≠ y) :
    hyperplaneReflection (normalizedChord x y)
        (x : EuclideanSpace ℝ (Fin n)) =
      (y : EuclideanSpace ℝ (Fin n)) := by
  let d : EuclideanSpace ℝ (Fin n) :=
    (y : EuclideanSpace ℝ (Fin n)) -
      (x : EuclideanSpace ℝ (Fin n))
  have hdne : d ≠ 0 := by
    intro h
    apply hxy
    apply Subtype.ext
    exact sub_eq_zero.mp h |>.symm
  have hdnorm : 0 < ‖d‖ := norm_pos_iff.mpr hdne
  have hdnormsq :
      ‖d‖ ^ 2 =
        2 - 2 * inner ℝ
          (y : EuclideanSpace ℝ (Fin n))
          (x : EuclideanSpace ℝ (Fin n)) := by
    dsimp [d]
    rw [norm_sub_sq_real,
      mem_sphere_zero_iff_norm.mp y.property,
      mem_sphere_zero_iff_norm.mp x.property]
    ring
  have hdx :
      inner ℝ d (x : EuclideanSpace ℝ (Fin n)) =
        inner ℝ (y : EuclideanSpace ℝ (Fin n))
          (x : EuclideanSpace ℝ (Fin n)) - 1 := by
    dsimp [d]
    rw [inner_sub_left, real_inner_self_eq_norm_sq,
      mem_sphere_zero_iff_norm.mp x.property]
    ring
  have hcoef :
      (2 * inner ℝ (‖d‖⁻¹ • d)
          (x : EuclideanSpace ℝ (Fin n))) * ‖d‖⁻¹ = -1 := by
    rw [real_inner_smul_left, hdx]
    field_simp [ne_of_gt hdnorm]
    nlinarith [hdnormsq]
  rw [hyperplaneReflection_apply_of_unit
    (normalizedChord x y) (x : EuclideanSpace ℝ (Fin n))
    (norm_normalizedChord hxy)]
  change
    (x : EuclideanSpace ℝ (Fin n)) -
        (2 * inner ℝ (‖d‖⁻¹ • d)
          (x : EuclideanSpace ℝ (Fin n))) • (‖d‖⁻¹ • d) =
      (y : EuclideanSpace ℝ (Fin n))
  rw [smul_smul, hcoef]
  dsimp [d]
  module

lemma sphereReflection_normalizedChord_left
    {x y : SphereE n} (hxy : x ≠ y) :
    sphereReflection (normalizedChord x y) x = y := by
  apply Subtype.ext
  exact hyperplaneReflection_normalizedChord_left hxy

lemma inner_normalizedChord_right_pos
    {x y : SphereE n} (hxy : x ≠ y) :
    0 < inner ℝ (normalizedChord x y)
      (y : EuclideanSpace ℝ (Fin n)) := by
  let d : EuclideanSpace ℝ (Fin n) :=
    (y : EuclideanSpace ℝ (Fin n)) -
      (x : EuclideanSpace ℝ (Fin n))
  have hdne : d ≠ 0 := by
    intro h
    apply hxy
    apply Subtype.ext
    exact sub_eq_zero.mp h |>.symm
  have hdnorm : 0 < ‖d‖ := norm_pos_iff.mpr hdne
  have hinnerlt :
      inner ℝ (x : EuclideanSpace ℝ (Fin n))
        (y : EuclideanSpace ℝ (Fin n)) < 1 := by
    have hsq : 0 < ‖d‖ ^ 2 := sq_pos_of_pos hdnorm
    dsimp [d] at hsq
    rw [norm_sub_sq_real,
      mem_sphere_zero_iff_norm.mp y.property,
      mem_sphere_zero_iff_norm.mp x.property] at hsq
    have hcomm :
        inner ℝ (x : EuclideanSpace ℝ (Fin n))
            (y : EuclideanSpace ℝ (Fin n)) =
          inner ℝ (y : EuclideanSpace ℝ (Fin n))
            (x : EuclideanSpace ℝ (Fin n)) :=
      real_inner_comm _ _
    linarith
  rw [normalizedChord, NormedSpace.normalize, inner_smul_left]
  have hinv : 0 < ‖d‖⁻¹ := inv_pos.mpr hdnorm
  have hdy :
      inner ℝ d (y : EuclideanSpace ℝ (Fin n)) =
        1 - inner ℝ (x : EuclideanSpace ℝ (Fin n))
          (y : EuclideanSpace ℝ (Fin n)) := by
    dsimp [d]
    rw [inner_sub_left, real_inner_self_eq_norm_sq,
      mem_sphere_zero_iff_norm.mp y.property]
    ring
  rw [hdy]
  positivity

lemma inner_normalizedChord_left_neg
    {x y : SphereE n} (hxy : x ≠ y) :
    inner ℝ (normalizedChord x y)
      (x : EuclideanSpace ℝ (Fin n)) < 0 := by
  have hreflection :=
    inner_normal_sphereReflection_of_unit
      (normalizedChord x y) (norm_normalizedChord hxy) x
  rw [sphereReflection_normalizedChord_left hxy] at hreflection
  have hypos := inner_normalizedChord_right_pos hxy
  linarith

lemma inner_normalizedChord_direction_lt
    (u : EuclideanSpace ℝ (Fin n)) {x y : SphereE n}
    (hxy : x ≠ y)
    (hcoord :
      inner ℝ u (y : EuclideanSpace ℝ (Fin n)) <
        inner ℝ u (x : EuclideanSpace ℝ (Fin n))) :
    inner ℝ u (normalizedChord x y) < 0 := by
  let d : EuclideanSpace ℝ (Fin n) :=
    (y : EuclideanSpace ℝ (Fin n)) -
      (x : EuclideanSpace ℝ (Fin n))
  have hdne : d ≠ 0 := by
    intro h
    apply hxy
    apply Subtype.ext
    exact sub_eq_zero.mp h |>.symm
  have hdnorm : 0 < ‖d‖ := norm_pos_iff.mpr hdne
  rw [normalizedChord, NormedSpace.normalize, inner_smul_right,
    inner_sub_right]
  exact mul_neg_of_pos_of_neg (inv_pos.mpr hdnorm)
    (sub_neg.mpr hcoord)

lemma inner_normalizedChord_direction_le
    (u : EuclideanSpace ℝ (Fin n)) {x y : SphereE n}
    (hxy : x ≠ y)
    (hcoord :
      inner ℝ u (y : EuclideanSpace ℝ (Fin n)) ≤
        inner ℝ u (x : EuclideanSpace ℝ (Fin n))) :
    inner ℝ u (normalizedChord x y) ≤ 0 := by
  let d : EuclideanSpace ℝ (Fin n) :=
    (y : EuclideanSpace ℝ (Fin n)) -
      (x : EuclideanSpace ℝ (Fin n))
  have hdne : d ≠ 0 := by
    intro h
    apply hxy
    apply Subtype.ext
    exact sub_eq_zero.mp h |>.symm
  have hdnorm : 0 < ‖d‖ := norm_pos_iff.mpr hdne
  rw [normalizedChord, NormedSpace.normalize, inner_smul_right,
    inner_sub_right]
  exact mul_nonpos_of_nonneg_of_nonpos (inv_pos.mpr hdnorm).le
    (sub_nonpos.mpr hcoord)

end

end HDP.Appendix
