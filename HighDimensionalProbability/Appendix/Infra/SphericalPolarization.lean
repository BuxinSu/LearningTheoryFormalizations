import HighDimensionalProbability.Appendix.Infra.MetricExpansion
import HighDimensionalProbability.Appendix.Infra.PoincareQuantile
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Two-point polarization on a Euclidean sphere

This file develops the elementary part of the Baernstein--Taylor proof of
Lévy's spherical isoperimetric inequality.  Reflection in a hyperplane
through the origin preserves normalized surface measure.  Polarization moves
each one-point reflection orbit to a chosen hemisphere, preserves measure,
and cannot increase any closed metric expansion.
-/

open MeasureTheory Set Metric InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace

namespace HDP.Appendix

noncomputable section

variable {n : ℕ}

/-- The unit sphere in `n`-dimensional Euclidean space. -/
abbrev SphereE (n : ℕ) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1

instance instIsOpenPosMeasureUnitSphereMeasure
    [Nonempty (Fin n)] :
    (HDP.unitSphereMeasure
      (EuclideanSpace ℝ (Fin n))).IsOpenPosMeasure := by
  rw [HDP.unitSphereMeasure, ProbabilityTheory.cond,
    Measure.restrict_univ]
  exact Measure.isOpenPosMeasure_smul _
    (ENNReal.inv_ne_zero.mpr
      (measure_ne_top
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere)
        Set.univ))

/-- Ambient reflection in the hyperplane perpendicular to `v`. -/
def hyperplaneReflection (v : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
  (ℝ ∙ v : Submodule ℝ (EuclideanSpace ℝ (Fin n)))ᗮ.reflection

/-- Reflection restricted to the unit sphere. -/
def sphereReflection (v : EuclideanSpace ℝ (Fin n)) :
    SphereE n ≃ₜ SphereE n :=
  HDP.unitSphereHomeomorph (hyperplaneReflection v)

@[simp]
lemma sphereReflection_coe (v : EuclideanSpace ℝ (Fin n))
    (x : SphereE n) :
    ((sphereReflection v x : SphereE n) :
      EuclideanSpace ℝ (Fin n)) = hyperplaneReflection v x := rfl

@[simp]
lemma sphereReflection_symm (v : EuclideanSpace ℝ (Fin n)) :
    (sphereReflection v).symm = sphereReflection v := by
  rw [sphereReflection, HDP.unitSphereHomeomorph_symm,
    hyperplaneReflection, Submodule.reflection_symm]

@[simp]
lemma sphereReflection_involutive (v : EuclideanSpace ℝ (Fin n))
    (x : SphereE n) :
    sphereReflection v (sphereReflection v x) = x := by
  apply Subtype.ext
  exact Submodule.reflection_reflection _ _

lemma measurePreserving_sphereReflection
    (v : EuclideanSpace ℝ (Fin n)) :
    MeasurePreserving (sphereReflection v)
      (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)))
      (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))) :=
  HDP.measurePreserving_unitSphereHomeomorph (hyperplaneReflection v)

/-- Closed hemisphere selected by `v`. -/
def closedPlusHemisphere (v : EuclideanSpace ℝ (Fin n)) :
    Set (SphereE n) :=
  {x | 0 ≤ inner ℝ v (x : EuclideanSpace ℝ (Fin n))}

/-- The opposite closed hemisphere. -/
def closedMinusHemisphere (v : EuclideanSpace ℝ (Fin n)) :
    Set (SphereE n) :=
  {x | inner ℝ v (x : EuclideanSpace ℝ (Fin n)) ≤ 0}

/-- The open positive hemisphere. -/
def openPlusHemisphere (v : EuclideanSpace ℝ (Fin n)) :
    Set (SphereE n) :=
  {x | 0 < inner ℝ v (x : EuclideanSpace ℝ (Fin n))}

/-- The open negative hemisphere. -/
def openMinusHemisphere (v : EuclideanSpace ℝ (Fin n)) :
    Set (SphereE n) :=
  {x | inner ℝ v (x : EuclideanSpace ℝ (Fin n)) < 0}

/-- Equator fixed by the reflection. -/
def reflectionEquator (v : EuclideanSpace ℝ (Fin n)) :
    Set (SphereE n) :=
  {x | inner ℝ v (x : EuclideanSpace ℝ (Fin n)) = 0}

lemma isClosed_closedPlusHemisphere
    (v : EuclideanSpace ℝ (Fin n)) :
    IsClosed (closedPlusHemisphere v) := by
  exact isClosed_le continuous_const (by fun_prop)

lemma isClosed_closedMinusHemisphere
    (v : EuclideanSpace ℝ (Fin n)) :
    IsClosed (closedMinusHemisphere v) := by
  exact isClosed_le (by fun_prop) continuous_const

lemma isOpen_openPlusHemisphere
    (v : EuclideanSpace ℝ (Fin n)) :
    IsOpen (openPlusHemisphere v) := by
  exact isOpen_lt continuous_const (by fun_prop)

lemma isOpen_openMinusHemisphere
    (v : EuclideanSpace ℝ (Fin n)) :
    IsOpen (openMinusHemisphere v) := by
  exact isOpen_lt (by fun_prop) continuous_const

lemma isClosed_reflectionEquator
    (v : EuclideanSpace ℝ (Fin n)) :
    IsClosed (reflectionEquator v) := by
  exact isClosed_eq (by fun_prop) continuous_const

lemma measurableSet_closedPlusHemisphere
    (v : EuclideanSpace ℝ (Fin n)) :
    MeasurableSet (closedPlusHemisphere v) :=
  (isClosed_closedPlusHemisphere v).measurableSet

lemma measurableSet_closedMinusHemisphere
    (v : EuclideanSpace ℝ (Fin n)) :
    MeasurableSet (closedMinusHemisphere v) :=
  (isClosed_closedMinusHemisphere v).measurableSet

lemma measurableSet_openPlusHemisphere
    (v : EuclideanSpace ℝ (Fin n)) :
    MeasurableSet (openPlusHemisphere v) :=
  (isOpen_openPlusHemisphere v).measurableSet

lemma measurableSet_openMinusHemisphere
    (v : EuclideanSpace ℝ (Fin n)) :
    MeasurableSet (openMinusHemisphere v) :=
  (isOpen_openMinusHemisphere v).measurableSet

lemma measurableSet_reflectionEquator
    (v : EuclideanSpace ℝ (Fin n)) :
    MeasurableSet (reflectionEquator v) :=
  (isClosed_reflectionEquator v).measurableSet

/-- Formula for reflection in the hyperplane normal to a unit vector. -/
lemma hyperplaneReflection_apply_of_unit
    (v x : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ = 1) :
    hyperplaneReflection v x = x - (2 * inner ℝ v x) • v := by
  rw [hyperplaneReflection, Submodule.reflection_orthogonal_apply,
    Submodule.reflection_singleton_apply, hv]
  rw [neg_sub]
  congr 1
  norm_num
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  norm_num

lemma inner_hyperplaneReflection_normal_of_unit
    (v x : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ = 1) :
    inner ℝ v (hyperplaneReflection v x) = - inner ℝ v x := by
  rw [hyperplaneReflection_apply_of_unit v x hv, inner_sub_right,
    inner_smul_right, real_inner_self_eq_norm_sq, hv]
  simp
  ring

lemma inner_normal_sphereReflection_of_unit
    (v : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ = 1)
    (x : SphereE n) :
    inner ℝ v
        ((sphereReflection v x : SphereE n) :
          EuclideanSpace ℝ (Fin n)) =
      -inner ℝ v (x : EuclideanSpace ℝ (Fin n)) := by
  exact inner_hyperplaneReflection_normal_of_unit v x hv

lemma sphereReflection_mem_openPlus_iff_of_unit
    (v : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ = 1)
    (x : SphereE n) :
    sphereReflection v x ∈ openPlusHemisphere v ↔
      x ∈ openMinusHemisphere v := by
  simp only [openPlusHemisphere, openMinusHemisphere, mem_setOf_eq,
    inner_normal_sphereReflection_of_unit v hv x, neg_pos]

lemma sphereReflection_mem_openMinus_iff_of_unit
    (v : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ = 1)
    (x : SphereE n) :
    sphereReflection v x ∈ openMinusHemisphere v ↔
      x ∈ openPlusHemisphere v := by
  simp only [openPlusHemisphere, openMinusHemisphere, mem_setOf_eq,
    inner_normal_sphereReflection_of_unit v hv x, neg_lt_zero]

lemma sphereReflection_mem_closedPlus_iff_of_unit
    (v : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ = 1)
    (x : SphereE n) :
    sphereReflection v x ∈ closedPlusHemisphere v ↔
      x ∈ closedMinusHemisphere v := by
  simp only [closedPlusHemisphere, closedMinusHemisphere, mem_setOf_eq,
    inner_normal_sphereReflection_of_unit v hv x, neg_nonneg]

lemma sphereReflection_mem_closedMinus_iff_of_unit
    (v : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ = 1)
    (x : SphereE n) :
    sphereReflection v x ∈ closedMinusHemisphere v ↔
      x ∈ closedPlusHemisphere v := by
  simp only [closedPlusHemisphere, closedMinusHemisphere, mem_setOf_eq,
    inner_normal_sphereReflection_of_unit v hv x, neg_nonpos]

lemma sphereReflection_mem_equator_iff_of_unit
    (v : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ = 1)
    (x : SphereE n) :
    sphereReflection v x ∈ reflectionEquator v ↔
      x ∈ reflectionEquator v := by
  simp only [reflectionEquator, mem_setOf_eq,
    inner_normal_sphereReflection_of_unit v hv x, neg_eq_zero]

lemma sphereReflection_eq_self_of_mem_equator
    (v : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ = 1)
    {x : SphereE n} (hx : x ∈ reflectionEquator v) :
    sphereReflection v x = x := by
  apply Subtype.ext
  rw [sphereReflection_coe, hyperplaneReflection_apply_of_unit v x hv]
  simp only [reflectionEquator, mem_setOf_eq] at hx
  rw [hx]
  simp

/-- The reflection equator has zero normalized surface measure. -/
lemma unitSphereMeasure_reflectionEquator
    (hn : 2 ≤ n) (v : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ = 1) :
    HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
        (reflectionEquator v) = 0 := by
  let μ := HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
  have hno :
      NoAtoms
        (Measure.map (sphereLinearCoordinate v) μ) :=
    noAtoms_map_sphereLinearCoordinate_unitSphereMeasure v hv
      (by simpa [finrank_euclideanSpace] using hn)
  letI : NoAtoms (Measure.map (sphereLinearCoordinate v) μ) := hno
  have hsingleton :
      Measure.map (sphereLinearCoordinate v) μ ({0} : Set ℝ) = 0 :=
    measure_singleton 0
  rw [Measure.map_apply (measurable_sphereLinearCoordinate v)
    (measurableSet_singleton 0)] at hsingleton
  exact hsingleton

/-- Polarization toward the positive hemisphere.  On each two-point
reflection orbit, one occupied point is placed on the positive side and two
occupied points remain on both sides. -/
def sphericalPolarization
    (v : EuclideanSpace ℝ (Fin n)) (A : Set (SphereE n)) :
    Set (SphereE n) :=
  ((A ∪ sphereReflection v ⁻¹' A) ∩ closedPlusHemisphere v) ∪
    ((A ∩ sphereReflection v ⁻¹' A) ∩ closedMinusHemisphere v)

lemma measurableSet_sphericalPolarization
    (v : EuclideanSpace ℝ (Fin n)) {A : Set (SphereE n)}
    (hA : MeasurableSet A) :
    MeasurableSet (sphericalPolarization v A) := by
  exact ((hA.union (hA.preimage (sphereReflection v).measurable)).inter
      (measurableSet_closedPlusHemisphere v)).union
    ((hA.inter (hA.preimage (sphereReflection v).measurable)).inter
      (measurableSet_closedMinusHemisphere v))

lemma isClosed_sphericalPolarization
    (v : EuclideanSpace ℝ (Fin n)) {A : Set (SphereE n)}
    (hA : IsClosed A) :
    IsClosed (sphericalPolarization v A) := by
  exact ((hA.union (hA.preimage (sphereReflection v).continuous)).inter
      (isClosed_closedPlusHemisphere v)).union
    ((hA.inter (hA.preimage (sphereReflection v).continuous)).inter
      (isClosed_closedMinusHemisphere v))

lemma mem_sphericalPolarization_of_mem_equator
    (v : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ = 1)
    {A : Set (SphereE n)} {x : SphereE n}
    (hx : x ∈ reflectionEquator v) :
    x ∈ sphericalPolarization v A ↔ x ∈ A := by
  have hrx : sphereReflection v x = x :=
    sphereReflection_eq_self_of_mem_equator v hv hx
  simp only [sphericalPolarization, mem_union, mem_inter_iff,
    mem_preimage, hrx]
  have hp : x ∈ closedPlusHemisphere v := by
    change 0 ≤ inner ℝ v (x : EuclideanSpace ℝ (Fin n))
    change inner ℝ v (x : EuclideanSpace ℝ (Fin n)) = 0 at hx
    exact hx.symm.le
  have hm : x ∈ closedMinusHemisphere v := by
    change inner ℝ v (x : EuclideanSpace ℝ (Fin n)) ≤ 0
    change inner ℝ v (x : EuclideanSpace ℝ (Fin n)) = 0 at hx
    exact hx.le
  tauto

lemma mem_sphericalPolarization_openPlus
    (v : EuclideanSpace ℝ (Fin n)) {A : Set (SphereE n)}
    {x : SphereE n} (hx : x ∈ openPlusHemisphere v) :
    x ∈ sphericalPolarization v A ↔
      x ∈ A ∨ sphereReflection v x ∈ A := by
  change 0 < inner ℝ v (x : EuclideanSpace ℝ (Fin n)) at hx
  have hp : x ∈ closedPlusHemisphere v := by
    exact le_of_lt hx
  have hnm : x ∉ closedMinusHemisphere v := by
    exact not_le_of_gt hx
  simp [sphericalPolarization, hp, hnm]

lemma mem_sphericalPolarization_openMinus
    (v : EuclideanSpace ℝ (Fin n)) {A : Set (SphereE n)}
    {x : SphereE n} (hx : x ∈ openMinusHemisphere v) :
    x ∈ sphericalPolarization v A ↔
      x ∈ A ∧ sphereReflection v x ∈ A := by
  change inner ℝ v (x : EuclideanSpace ℝ (Fin n)) < 0 at hx
  have hm : x ∈ closedMinusHemisphere v := by
    exact le_of_lt hx
  have hnp : x ∉ closedPlusHemisphere v := by
    exact not_le_of_gt hx
  simp [sphericalPolarization, hm, hnp]

lemma mem_sphericalPolarization_closedPlus
    (v : EuclideanSpace ℝ (Fin n)) {A : Set (SphereE n)}
    {x : SphereE n} (hx : x ∈ closedPlusHemisphere v) :
    x ∈ sphericalPolarization v A ↔
      x ∈ A ∨ sphereReflection v x ∈ A := by
  simp only [sphericalPolarization, mem_union, mem_inter_iff,
    mem_preimage, hx, and_true]
  tauto

lemma mem_sphericalPolarization_closedMinus
    (v : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ = 1)
    {A : Set (SphereE n)} {x : SphereE n}
    (hx : x ∈ closedMinusHemisphere v) :
    x ∈ sphericalPolarization v A ↔
      x ∈ A ∧ sphereReflection v x ∈ A := by
  by_cases hxm : x ∈ openMinusHemisphere v
  · exact mem_sphericalPolarization_openMinus v hxm
  · have hxe : x ∈ reflectionEquator v := by
      change inner ℝ v (x : EuclideanSpace ℝ (Fin n)) = 0
      change inner ℝ v (x : EuclideanSpace ℝ (Fin n)) ≤ 0 at hx
      change ¬ inner ℝ v (x : EuclideanSpace ℝ (Fin n)) < 0 at hxm
      exact le_antisymm hx (le_of_not_gt hxm)
    rw [mem_sphericalPolarization_of_mem_equator v hv hxe,
      sphereReflection_eq_self_of_mem_equator v hv hxe]
    tauto

lemma sphericalPolarization_nonempty
    (v : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ = 1)
    {A : Set (SphereE n)} (hA : A.Nonempty) :
    (sphericalPolarization v A).Nonempty := by
  obtain ⟨x, hxA⟩ := hA
  by_cases hxp : x ∈ closedPlusHemisphere v
  · exact ⟨x,
      (mem_sphericalPolarization_closedPlus v hxp).2
        (Or.inl hxA)⟩
  · have hxm : x ∈ closedMinusHemisphere v := by
      change inner ℝ v (x : EuclideanSpace ℝ (Fin n)) ≤ 0
      change ¬ 0 ≤ inner ℝ v
          (x : EuclideanSpace ℝ (Fin n)) at hxp
      exact (lt_of_not_ge hxp).le
    by_cases hrxA : sphereReflection v x ∈ A
    · exact ⟨x,
        (mem_sphericalPolarization_closedMinus v hv hxm).2
          ⟨hxA, hrxA⟩⟩
    · have hrxp :
          sphereReflection v x ∈ closedPlusHemisphere v :=
        (sphereReflection_mem_closedPlus_iff_of_unit v hv x).2 hxm
      exact ⟨sphereReflection v x,
        (mem_sphericalPolarization_closedPlus v hrxp).2
          (Or.inr (by simpa using hxA))⟩

/-- Reflection is an isometry on the sphere. -/
lemma sphereReflection_dist
    (v : EuclideanSpace ℝ (Fin n)) (x y : SphereE n) :
    dist (sphereReflection v x) (sphereReflection v y) = dist x y := by
  change
    ‖hyperplaneReflection v x - hyperplaneReflection v y‖ =
      ‖(x : EuclideanSpace ℝ (Fin n)) -
        (y : EuclideanSpace ℝ (Fin n))‖
  rw [← map_sub, (hyperplaneReflection v).norm_map]

/-- Points in the same closed hemisphere are closer to each other than one
of them is to the reflection of the other. -/
lemma dist_le_dist_sphereReflection_of_inner_mul_nonneg
    (v : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ = 1)
    (x y : SphereE n)
    (hxy : 0 ≤
      inner ℝ v (x : EuclideanSpace ℝ (Fin n)) *
        inner ℝ v (y : EuclideanSpace ℝ (Fin n))) :
    dist x y ≤ dist x (sphereReflection v y) := by
  change
    ‖(x : EuclideanSpace ℝ (Fin n)) -
        (y : EuclideanSpace ℝ (Fin n))‖ ≤
      ‖(x : EuclideanSpace ℝ (Fin n)) -
        hyperplaneReflection v y‖
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  rw [norm_sub_sq_real, norm_sub_sq_real,
    (hyperplaneReflection v).norm_map,
    hyperplaneReflection_apply_of_unit v y hv,
    inner_sub_right, inner_smul_right]
  rw [real_inner_comm v (x : EuclideanSpace ℝ (Fin n))]
  nlinarith

lemma dist_le_dist_sphereReflection_of_closedPlus
    (v : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ = 1)
    {x y : SphereE n}
    (hx : x ∈ closedPlusHemisphere v)
    (hy : y ∈ closedPlusHemisphere v) :
    dist x y ≤ dist x (sphereReflection v y) := by
  apply dist_le_dist_sphereReflection_of_inner_mul_nonneg v hv
  exact mul_nonneg hx hy

lemma dist_le_dist_sphereReflection_of_closedMinus
    (v : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ = 1)
    {x y : SphereE n}
    (hx : x ∈ closedMinusHemisphere v)
    (hy : y ∈ closedMinusHemisphere v) :
    dist x y ≤ dist x (sphereReflection v y) := by
  apply dist_le_dist_sphereReflection_of_inner_mul_nonneg v hv
  exact mul_nonneg_of_nonpos_of_nonpos hx hy

lemma inner_sphereReflection_of_unit
    (v : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ = 1)
    (u : EuclideanSpace ℝ (Fin n)) (x : SphereE n) :
    inner ℝ u
        ((sphereReflection v x : SphereE n) :
          EuclideanSpace ℝ (Fin n)) =
      inner ℝ u (x : EuclideanSpace ℝ (Fin n)) -
        2 * inner ℝ v (x : EuclideanSpace ℝ (Fin n)) *
          inner ℝ u v := by
  rw [sphereReflection_coe, hyperplaneReflection_apply_of_unit v x hv,
    inner_sub_right, inner_smul_right]

/-- A cap is fixed by every polarization whose positive hemisphere points
toward the cap. -/
lemma sphericalPolarization_sphericalCap
    (v : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ = 1)
    (u : EuclideanSpace ℝ (Fin n)) (a : ℝ)
    (huv : inner ℝ u v ≤ 0) :
    sphericalPolarization v (HDP.Chapter5.sphericalCap u a) =
      HDP.Chapter5.sphericalCap u a := by
  ext x
  by_cases hxp : x ∈ closedPlusHemisphere v
  · rw [mem_sphericalPolarization_closedPlus v hxp]
    change
      (inner ℝ u (x : EuclideanSpace ℝ (Fin n)) ≤ a ∨
          inner ℝ u
            ((sphereReflection v x : SphereE n) :
              EuclideanSpace ℝ (Fin n)) ≤ a) ↔
        inner ℝ u (x : EuclideanSpace ℝ (Fin n)) ≤ a
    rw [inner_sphereReflection_of_unit v hv u x]
    change 0 ≤ inner ℝ v (x : EuclideanSpace ℝ (Fin n)) at hxp
    constructor
    · rintro (hx | hx)
      · exact hx
      · have hprod :
          inner ℝ v (x : EuclideanSpace ℝ (Fin n)) *
              inner ℝ u v ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hxp huv
        nlinarith
    · exact Or.inl
  · have hxm : x ∈ closedMinusHemisphere v := by
      change inner ℝ v (x : EuclideanSpace ℝ (Fin n)) ≤ 0
      change ¬ 0 ≤ inner ℝ v (x : EuclideanSpace ℝ (Fin n)) at hxp
      exact (lt_of_not_ge hxp).le
    rw [mem_sphericalPolarization_closedMinus v hv hxm]
    change
      (inner ℝ u (x : EuclideanSpace ℝ (Fin n)) ≤ a ∧
          inner ℝ u
            ((sphereReflection v x : SphereE n) :
              EuclideanSpace ℝ (Fin n)) ≤ a) ↔
        inner ℝ u (x : EuclideanSpace ℝ (Fin n)) ≤ a
    rw [inner_sphereReflection_of_unit v hv u x]
    change inner ℝ v (x : EuclideanSpace ℝ (Fin n)) ≤ 0 at hxm
    constructor
    · exact fun hx => hx.1
    · intro hx
      refine ⟨hx, ?_⟩
      have hprod :
          0 ≤ inner ℝ v (x : EuclideanSpace ℝ (Fin n)) *
              inner ℝ u v :=
        mul_nonneg_of_nonpos_of_nonpos hxm huv
      nlinarith

/-- Polarization cannot enlarge a closed metric expansion. -/
lemma closedExpansion_sphericalPolarization_subset
    (v : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ = 1)
    (ε : ℝ) (A : Set (SphereE n)) :
    closedExpansion ε (sphericalPolarization v A) ⊆
      sphericalPolarization v (closedExpansion ε A) := by
  intro x hx
  rcases hx with ⟨z, hzP, hxz⟩
  by_cases hxp : x ∈ closedPlusHemisphere v
  · rw [mem_sphericalPolarization_closedPlus v hxp]
    by_cases hzp : z ∈ closedPlusHemisphere v
    · rw [mem_sphericalPolarization_closedPlus v hzp] at hzP
      rcases hzP with hzA | hrzA
      · exact Or.inl ⟨z, hzA, hxz⟩
      · refine Or.inr ⟨sphereReflection v z, hrzA, ?_⟩
        rw [sphereReflection_dist]
        exact hxz
    · have hzm : z ∈ closedMinusHemisphere v := by
        change inner ℝ v (z : EuclideanSpace ℝ (Fin n)) ≤ 0
        change ¬ 0 ≤ inner ℝ v (z : EuclideanSpace ℝ (Fin n)) at hzp
        exact (lt_of_not_ge hzp).le
      rw [mem_sphericalPolarization_closedMinus v hv hzm] at hzP
      exact Or.inl ⟨z, hzP.1, hxz⟩
  · have hxm : x ∈ closedMinusHemisphere v := by
      change inner ℝ v (x : EuclideanSpace ℝ (Fin n)) ≤ 0
      change ¬ 0 ≤ inner ℝ v (x : EuclideanSpace ℝ (Fin n)) at hxp
      exact (lt_of_not_ge hxp).le
    rw [mem_sphericalPolarization_closedMinus v hv hxm]
    by_cases hzp : z ∈ closedPlusHemisphere v
    · rw [mem_sphericalPolarization_closedPlus v hzp] at hzP
      rcases hzP with hzA | hrzA
      · refine ⟨⟨z, hzA, hxz⟩, ⟨z, hzA, ?_⟩⟩
        have hrxp : sphereReflection v x ∈ closedPlusHemisphere v :=
          (sphereReflection_mem_closedPlus_iff_of_unit v hv x).2 hxm
        have hclose :=
          dist_le_dist_sphereReflection_of_closedPlus v hv hrxp hzp
        rw [sphereReflection_dist v x z] at hclose
        exact hclose.trans hxz
      · refine
          ⟨⟨sphereReflection v z, hrzA, ?_⟩,
            ⟨sphereReflection v z, hrzA, ?_⟩⟩
        · have hrzm : sphereReflection v z ∈ closedMinusHemisphere v :=
            (sphereReflection_mem_closedMinus_iff_of_unit v hv z).2 hzp
          have hclose :=
            dist_le_dist_sphereReflection_of_closedMinus v hv hxm hrzm
          rw [sphereReflection_involutive] at hclose
          exact hclose.trans hxz
        · rw [sphereReflection_dist]
          exact hxz
    · have hzm : z ∈ closedMinusHemisphere v := by
        change inner ℝ v (z : EuclideanSpace ℝ (Fin n)) ≤ 0
        change ¬ 0 ≤ inner ℝ v (z : EuclideanSpace ℝ (Fin n)) at hzp
        exact (lt_of_not_ge hzp).le
      rw [mem_sphericalPolarization_closedMinus v hv hzm] at hzP
      refine
        ⟨⟨z, hzP.1, hxz⟩,
          ⟨sphereReflection v z, hzP.2, ?_⟩⟩
      rw [sphereReflection_dist]
      exact hxz

/-- Up to the null equator, the two open hemispheres partition the sphere. -/
lemma measure_eq_inter_openPlus_add_inter_openMinus
    (hn : 2 ≤ n) (v : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ = 1)
    {A : Set (SphereE n)} (hA : MeasurableSet A) :
    HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)) A =
      HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
          (A ∩ openPlusHemisphere v) +
        HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
          (A ∩ openMinusHemisphere v) := by
  let μ := HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
  have heq : μ (reflectionEquator v) = 0 :=
    unitSphereMeasure_reflectionEquator hn v hv
  have hsets :
      A \ reflectionEquator v =
        (A ∩ openPlusHemisphere v) ∪
          (A ∩ openMinusHemisphere v) := by
    ext x
    change
      (x ∈ A ∧
          inner ℝ v (x : EuclideanSpace ℝ (Fin n)) ≠ 0) ↔
        (x ∈ A ∧
            0 < inner ℝ v (x : EuclideanSpace ℝ (Fin n))) ∨
          (x ∈ A ∧
            inner ℝ v (x : EuclideanSpace ℝ (Fin n)) < 0)
    constructor
    · rintro ⟨hxA, hx0⟩
      rcases lt_or_gt_of_ne hx0 with hx | hx
      · exact Or.inr ⟨hxA, hx⟩
      · exact Or.inl ⟨hxA, hx⟩
    · rintro (⟨hxA, hx⟩ | ⟨hxA, hx⟩)
      · exact ⟨hxA, ne_of_gt hx⟩
      · exact ⟨hxA, ne_of_lt hx⟩
  have hdis :
      Disjoint (A ∩ openPlusHemisphere v)
        (A ∩ openMinusHemisphere v) := by
    rw [Set.disjoint_left]
    intro x hxP hxM
    rcases hxP with ⟨_, hxP⟩
    rcases hxM with ⟨_, hxM⟩
    change 0 < inner ℝ v (x : EuclideanSpace ℝ (Fin n)) at hxP
    change inner ℝ v (x : EuclideanSpace ℝ (Fin n)) < 0 at hxM
    linarith
  calc
    μ A = μ (A \ reflectionEquator v) :=
      (measure_sdiff_null heq).symm
    _ = μ ((A ∩ openPlusHemisphere v) ∪
        (A ∩ openMinusHemisphere v)) := congrArg μ hsets
    _ = μ (A ∩ openPlusHemisphere v) +
        μ (A ∩ openMinusHemisphere v) :=
      measure_union hdis
        (hA.inter (measurableSet_openMinusHemisphere v))

lemma measure_preimage_inter_openPlus
    (v : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ = 1)
    {A : Set (SphereE n)} (hA : MeasurableSet A) :
    HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
        ((sphereReflection v ⁻¹' A) ∩ openPlusHemisphere v) =
      HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
        (A ∩ openMinusHemisphere v) := by
  let μ := HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
  have hset :
      (sphereReflection v ⁻¹' A) ∩ openPlusHemisphere v =
        sphereReflection v ⁻¹' (A ∩ openMinusHemisphere v) := by
    ext x
    simp only [mem_inter_iff, mem_preimage]
    rw [sphereReflection_mem_openMinus_iff_of_unit v hv x]
  rw [hset]
  exact (measurePreserving_sphereReflection v).measure_preimage
    (hA.inter (measurableSet_openMinusHemisphere v)).nullMeasurableSet

lemma measure_symmetric_inter_openMinus_eq_openPlus
    (v : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ = 1)
    {A : Set (SphereE n)} (hA : MeasurableSet A) :
    HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
        ((A ∩ sphereReflection v ⁻¹' A) ∩ openMinusHemisphere v) =
      HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
        ((A ∩ sphereReflection v ⁻¹' A) ∩ openPlusHemisphere v) := by
  let μ := HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
  let B := (A ∩ sphereReflection v ⁻¹' A) ∩ openPlusHemisphere v
  have hB : MeasurableSet B :=
    (hA.inter (hA.preimage (sphereReflection v).measurable)).inter
      (measurableSet_openPlusHemisphere v)
  have hset :
      sphereReflection v ⁻¹' B =
        (A ∩ sphereReflection v ⁻¹' A) ∩ openMinusHemisphere v := by
    ext x
    simp only [B, mem_preimage, mem_inter_iff]
    rw [sphereReflection_involutive,
      sphereReflection_mem_openPlus_iff_of_unit v hv x]
    tauto
  rw [← hset]
  exact (measurePreserving_sphereReflection v).measure_preimage
    hB.nullMeasurableSet

/-- Two-point polarization preserves normalized surface measure. -/
lemma unitSphereMeasure_sphericalPolarization
    (hn : 2 ≤ n) (v : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ = 1)
    {A : Set (SphereE n)} (hA : MeasurableSet A) :
    HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
        (sphericalPolarization v A) =
      HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)) A := by
  let μ := HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
  let R : SphereE n → SphereE n := sphereReflection v
  have hPA : MeasurableSet (sphericalPolarization v A) :=
    measurableSet_sphericalPolarization v hA
  have hsplitP :=
    measure_eq_inter_openPlus_add_inter_openMinus
      hn v hv hPA
  have hsplitA :=
    measure_eq_inter_openPlus_add_inter_openMinus
      hn v hv hA
  have hPplus :
      sphericalPolarization v A ∩ openPlusHemisphere v =
        (A ∪ R ⁻¹' A) ∩ openPlusHemisphere v := by
    ext x
    by_cases hx : x ∈ openPlusHemisphere v
    · simp only [mem_inter_iff, hx, and_true]
      exact mem_sphericalPolarization_openPlus v hx
    · simp [hx]
  have hPminus :
      sphericalPolarization v A ∩ openMinusHemisphere v =
        (A ∩ R ⁻¹' A) ∩ openMinusHemisphere v := by
    ext x
    by_cases hx : x ∈ openMinusHemisphere v
    · simp only [mem_inter_iff, hx, and_true]
      exact mem_sphericalPolarization_openMinus v hx
    · simp [hx]
  have hunion :
      (A ∪ R ⁻¹' A) ∩ openPlusHemisphere v =
        (A ∩ openPlusHemisphere v) ∪
          ((R ⁻¹' A) ∩ openPlusHemisphere v) := by
    ext x
    simp only [mem_inter_iff, mem_union, mem_preimage]
    tauto
  have hinter :
      (A ∩ R ⁻¹' A) ∩ openPlusHemisphere v =
        (A ∩ openPlusHemisphere v) ∩
          ((R ⁻¹' A) ∩ openPlusHemisphere v) := by
    ext x
    simp only [mem_inter_iff, mem_preimage]
    tauto
  rw [hsplitP, hPplus, hPminus,
    measure_symmetric_inter_openMinus_eq_openPlus v hv hA,
    hunion, hinter]
  rw [measure_union_add_inter
    (A ∩ openPlusHemisphere v)
    ((hA.preimage (sphereReflection v).measurable).inter
      (measurableSet_openPlusHemisphere v))]
  rw [measure_preimage_inter_openPlus v hv hA]
  exact hsplitA.symm

/-- Polarizing a closed set does not increase the measure of any nonnegative
closed expansion. -/
lemma unitSphereMeasure_closedExpansion_sphericalPolarization_le
    (hn : 2 ≤ n) (v : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ = 1)
    (ε : ℝ) (hε : 0 ≤ ε) {A : Set (SphereE n)} (hA : IsClosed A) :
    HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
        (closedExpansion ε (sphericalPolarization v A)) ≤
      HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
        (closedExpansion ε A) := by
  have hEA : MeasurableSet (closedExpansion ε A) := by
    rw [closedExpansion_eq_cthickening hA hε]
    exact isClosed_cthickening.measurableSet
  calc
    HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
        (closedExpansion ε (sphericalPolarization v A)) ≤
      HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
        (sphericalPolarization v (closedExpansion ε A)) :=
      measure_mono
        (closedExpansion_sphericalPolarization_subset v hv ε A)
    _ = HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
        (closedExpansion ε A) :=
      unitSphereMeasure_sphericalPolarization hn v hv hEA

end

end HDP.Appendix
