import HighDimensionalProbability.Appendix.Infra.SphericalSymmetrization
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# A Lyapunov functional for spherical polarization

The integral of a linear coordinate over a compact subset of the sphere is
continuous on every fixed-mass Hausdorff hyperspace.  Polarization toward the
negative `u`-direction decreases this moment, and decreases it strictly as
soon as a positive-measure reflection orbit is moved.
-/

open MeasureTheory Set Metric InnerProductSpace Filter Function
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace HDP.Appendix

noncomputable section

variable {n : ℕ}

/-- The first moment of a spherical compact set in direction `u`. -/
def sphericalMoment [Nonempty (Fin n)]
    (u : EuclideanSpace ℝ (Fin n)) (B : SphereCompacts n) : ℝ :=
  ∫ x in (B : Set (SphereE n)), sphereLinearCoordinate u x ∂
    HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))

lemma abs_sphereLinearCoordinate_le_one
    (u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1)
    (x : SphereE n) :
    |sphereLinearCoordinate u x| ≤ 1 := by
  rw [abs_le]
  constructor
  · exact neg_one_le_real_inner_of_norm_eq_one hu
      (mem_sphere_zero_iff_norm.mp x.property)
  · exact real_inner_le_one_of_norm_eq_one hu
      (mem_sphere_zero_iff_norm.mp x.property)

lemma integrable_sphereLinearCoordinate
    [Nonempty (Fin n)] (u : EuclideanSpace ℝ (Fin n)) :
    Integrable (sphereLinearCoordinate u)
      (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))) := by
  simpa only [integrableOn_univ] using
    (show Continuous (sphereLinearCoordinate u) by
      unfold sphereLinearCoordinate
      fun_prop).continuousOn.integrableOn_compact isCompact_univ

/-- A bounded set integral changes by at most the measure of the symmetric
difference of its domains. -/
lemma abs_setIntegral_sub_setIntegral_le_symmDiff
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {f : X → ℝ} (hf : Integrable f μ)
    (hbound : ∀ x, |f x| ≤ 1)
    {B D : Set X} (hB : MeasurableSet B) (hD : MeasurableSet D) :
    |(∫ x in D, f x ∂μ) - ∫ x in B, f x ∂μ| ≤
      μ.real (D \ B) + μ.real (B \ D) := by
  have hDsplit := integral_inter_add_sdiff hB hf.integrableOn
    (s := D)
  have hBsplit := integral_inter_add_sdiff hD hf.integrableOn
    (s := B)
  have hrewrite :
      (∫ x in D, f x ∂μ) - ∫ x in B, f x ∂μ =
        (∫ x in D \ B, f x ∂μ) -
          ∫ x in B \ D, f x ∂μ := by
    rw [← hDsplit, ← hBsplit]
    rw [inter_comm D B]
    ring
  rw [hrewrite]
  calc
    |(∫ x in D \ B, f x ∂μ) -
        ∫ x in B \ D, f x ∂μ| ≤
        |∫ x in D \ B, f x ∂μ| +
          |∫ x in B \ D, f x ∂μ| := abs_sub _ _
    _ ≤ μ.real (D \ B) + μ.real (B \ D) := by
      gcongr
      · simpa [Real.norm_eq_abs] using
          (norm_setIntegral_le_of_norm_le_const (f := f) (C := 1)
            (measure_lt_top μ (D \ B)) (fun x _ => by
              simpa [Real.norm_eq_abs] using hbound x))
      · simpa [Real.norm_eq_abs] using
          (norm_setIntegral_le_of_norm_le_const (f := f) (C := 1)
            (measure_lt_top μ (B \ D)) (fun x _ => by
              simpa [Real.norm_eq_abs] using hbound x))

lemma measureReal_sdiff_eq_sdiff_of_measure_eq
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {B D : Set X} (hB : MeasurableSet B) (hD : MeasurableSet D)
    (hmass : μ D = μ B) :
    μ.real (D \ B) = μ.real (B \ D) := by
  have hmassReal : μ.real D = μ.real B := by
    simpa [measureReal_def] using congrArg ENNReal.toReal hmass
  rw [measureReal_sdiff' hB, measureReal_sdiff' hD, union_comm B D,
    hmassReal]

/-- On compact sets of a prescribed mass, the linear moment is continuous
for the Hausdorff metric. -/
lemma continuousOn_sphericalMoment_fixedMass
    [Nonempty (Fin n)] (u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1)
    (K : SphereCompacts n) :
    ContinuousOn (sphericalMoment u)
      {B : SphereCompacts n |
        HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
            (B : Set (SphereE n)) =
          HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
            (K : Set (SphereE n))} := by
  let μ := HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
  intro B hBmass
  apply Metric.continuousWithinAt_iff'.2
  intro ε hε
  have ht :
      Tendsto
        (fun r : ℝ => μ.real
          (Metric.cthickening r (B : Set (SphereE n))))
        (𝓝 0) (𝓝 (μ.real (B : Set (SphereE n)))) := by
    exact (ENNReal.tendsto_toReal (measure_ne_top μ
      (B : Set (SphereE n)))).comp
      (tendsto_measure_cthickening_of_isCompact B.isCompact)
  have hshell :
      Tendsto
        (fun r : ℝ =>
          μ.real (Metric.cthickening r (B : Set (SphereE n))) -
            μ.real (B : Set (SphereE n)))
        (𝓝 0) (𝓝 0) := by
    simpa using ht.sub_const (μ.real (B : Set (SphereE n)))
  have hevent :
      ∀ᶠ r : ℝ in 𝓝 0,
        |μ.real (Metric.cthickening r (B : Set (SphereE n))) -
            μ.real (B : Set (SphereE n))| < ε / 2 := by
    rw [Metric.tendsto_nhds] at hshell
    simpa [Real.dist_eq] using hshell (ε / 2) (by positivity)
  obtain ⟨ρ, hρ, hρshell⟩ := Metric.mem_nhds_iff.1 hevent
  let δ := ρ / 2
  have hδ : 0 < δ := by
    dsimp [δ]
    linarith
  let S : Set (SphereCompacts n) :=
    {D |
      HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
          (D : Set (SphereE n)) =
        HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
          (K : Set (SphereE n))}
  filter_upwards [inter_mem_nhdsWithin S (Metric.ball_mem_nhds B hδ)]
    with D hDB
  have hclose : dist D B < δ := by
    simpa [Metric.mem_ball] using hDB.2
  have hDsub :
      (D : Set (SphereE n)) ⊆
        closedExpansion δ (B : Set (SphereE n)) :=
    NonemptyCompacts.subset_closedExpansion_of_dist_lt hclose
  have hδnonneg : 0 ≤ δ := hδ.le
  have hDsub' :
      (D : Set (SphereE n)) ⊆
        Metric.cthickening δ (B : Set (SphereE n)) := by
    simpa [closedExpansion_eq_cthickening B.isCompact.isClosed
      hδnonneg] using hDsub
  have hDmass :
      μ (D : Set (SphereE n)) = μ (B : Set (SphereE n)) := by
    exact hDB.1.trans hBmass.symm
  have hsdiff :
      μ.real ((D : Set (SphereE n)) \ (B : Set (SphereE n))) ≤
        μ.real (Metric.cthickening δ (B : Set (SphereE n))) -
          μ.real (B : Set (SphereE n)) := by
    calc
      μ.real ((D : Set (SphereE n)) \ (B : Set (SphereE n))) ≤
          μ.real
            (Metric.cthickening δ (B : Set (SphereE n)) \
              (B : Set (SphereE n))) :=
        measureReal_mono (by
          intro x hx
          exact ⟨hDsub' hx.1, hx.2⟩)
      _ = μ.real (Metric.cthickening δ (B : Set (SphereE n))) -
          μ.real (B : Set (SphereE n)) := by
        rw [measureReal_sdiff (Metric.self_subset_cthickening
          (B : Set (SphereE n)))
          B.isCompact.measurableSet]
  have hshell_nonneg :
      0 ≤ μ.real (Metric.cthickening δ (B : Set (SphereE n))) -
          μ.real (B : Set (SphereE n)) := by
    exact sub_nonneg.mpr (measureReal_mono
      (Metric.self_subset_cthickening (B : Set (SphereE n))))
  have hshell_lt :
      μ.real (Metric.cthickening δ (B : Set (SphereE n))) -
          μ.real (B : Set (SphereE n)) < ε / 2 := by
    have hδρ : δ < ρ := by
      dsimp [δ]
      linarith
    have hmem : δ ∈ Metric.ball (0 : ℝ) ρ := by
      simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos hδ]
    have habs := hρshell hmem
    simpa [abs_of_nonneg hshell_nonneg] using habs
  have hdiff_eq :
      μ.real ((D : Set (SphereE n)) \ (B : Set (SphereE n))) =
        μ.real ((B : Set (SphereE n)) \ (D : Set (SphereE n))) :=
    measureReal_sdiff_eq_sdiff_of_measure_eq
      B.isCompact.measurableSet D.isCompact.measurableSet hDmass
  change dist (sphericalMoment u D) (sphericalMoment u B) < ε
  rw [Real.dist_eq, sphericalMoment, sphericalMoment]
  calc
    |(∫ x in (D : Set (SphereE n)), sphereLinearCoordinate u x ∂μ) -
        ∫ x in (B : Set (SphereE n)), sphereLinearCoordinate u x ∂μ| ≤
        μ.real ((D : Set (SphereE n)) \ (B : Set (SphereE n))) +
          μ.real ((B : Set (SphereE n)) \ (D : Set (SphereE n))) :=
      abs_setIntegral_sub_setIntegral_le_symmDiff
        (integrable_sphereLinearCoordinate u)
        (abs_sphereLinearCoordinate_le_one u hu)
        B.isCompact.measurableSet D.isCompact.measurableSet
    _ = 2 * μ.real
        ((D : Set (SphereE n)) \ (B : Set (SphereE n))) := by
      rw [← hdiff_eq]
      ring
    _ < ε := by linarith

/-- Points gained by polarization: the positive member of a singly occupied
reflection orbit when that member was not originally present. -/
def polarizationGain (v : EuclideanSpace ℝ (Fin n))
    (A : Set (SphereE n)) : Set (SphereE n) :=
  ((sphereReflection v ⁻¹' A) \ A) ∩ openPlusHemisphere v

/-- Points lost by polarization: the negative member of a singly occupied
reflection orbit. -/
def polarizationLoss (v : EuclideanSpace ℝ (Fin n))
    (A : Set (SphereE n)) : Set (SphereE n) :=
  (A \ sphereReflection v ⁻¹' A) ∩ openMinusHemisphere v

lemma measurableSet_polarizationGain
    (v : EuclideanSpace ℝ (Fin n)) {A : Set (SphereE n)}
    (hA : MeasurableSet A) :
    MeasurableSet (polarizationGain v A) :=
  ((hA.preimage (sphereReflection v).measurable).diff hA).inter
    (measurableSet_openPlusHemisphere v)

lemma measurableSet_polarizationLoss
    (v : EuclideanSpace ℝ (Fin n)) {A : Set (SphereE n)}
    (hA : MeasurableSet A) :
    MeasurableSet (polarizationLoss v A) :=
  (hA.diff (hA.preimage (sphereReflection v).measurable)).inter
    (measurableSet_openMinusHemisphere v)

lemma sphereReflection_preimage_polarizationGain
    (v : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ = 1)
    (A : Set (SphereE n)) :
    sphereReflection v ⁻¹' polarizationGain v A =
      polarizationLoss v A := by
  ext x
  change
    ((sphereReflection v (sphereReflection v x) ∈ A ∧
        sphereReflection v x ∉ A) ∧
      sphereReflection v x ∈ openPlusHemisphere v) ↔
      ((x ∈ A ∧ sphereReflection v x ∉ A) ∧
        x ∈ openMinusHemisphere v)
  rw [sphereReflection_involutive,
    sphereReflection_mem_openPlus_iff_of_unit v hv x]

lemma sphericalPolarization_eq_remove_loss_union_gain
    (v : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ = 1)
    (A : Set (SphereE n)) :
    sphericalPolarization v A =
      (A \ polarizationLoss v A) ∪ polarizationGain v A := by
  ext x
  by_cases hxp : x ∈ openPlusHemisphere v
  · have hpc : x ∈ closedPlusHemisphere v := by
      change 0 ≤ inner ℝ v (x : EuclideanSpace ℝ (Fin n))
      exact hxp.le
    have hnm : x ∉ openMinusHemisphere v := by
      change ¬ inner ℝ v (x : EuclideanSpace ℝ (Fin n)) < 0
      change 0 < inner ℝ v (x : EuclideanSpace ℝ (Fin n)) at hxp
      linarith
    rw [mem_sphericalPolarization_openPlus v hxp]
    simp [polarizationGain, polarizationLoss, hxp, hnm]
    tauto
  · by_cases hxm : x ∈ openMinusHemisphere v
    · have hnp : x ∉ openPlusHemisphere v := hxp
      rw [mem_sphericalPolarization_openMinus v hxm]
      simp [polarizationGain, polarizationLoss, hxm, hnp]
      tauto
    · have hxeq : x ∈ reflectionEquator v := by
        change inner ℝ v (x : EuclideanSpace ℝ (Fin n)) = 0
        change ¬ 0 < inner ℝ v (x : EuclideanSpace ℝ (Fin n)) at hxp
        change ¬ inner ℝ v (x : EuclideanSpace ℝ (Fin n)) < 0 at hxm
        exact le_antisymm (le_of_not_gt hxp) (le_of_not_gt hxm)
      rw [mem_sphericalPolarization_of_mem_equator v hv hxeq]
      simp [polarizationGain, polarizationLoss, hxp, hxm]

lemma polarizationGain_disjoint_original
    (v : EuclideanSpace ℝ (Fin n)) (A : Set (SphereE n)) :
    Disjoint (polarizationGain v A) A := by
  exact Set.disjoint_left.2 fun _ hxG hxA => hxG.1.2 hxA

lemma polarizationLoss_subset
    (v : EuclideanSpace ℝ (Fin n)) (A : Set (SphereE n)) :
    polarizationLoss v A ⊆ A :=
  fun _ hx => hx.1.1

/-- Exact change-of-variables formula for the moment under polarization. -/
lemma sphericalMoment_polarizedCompacts_sub
    [Nonempty (Fin n)]
    (u v : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ = 1)
    (B : SphereCompacts n) :
    sphericalMoment u (polarizedCompacts B v hv) - sphericalMoment u B =
      ∫ x in polarizationGain v (B : Set (SphereE n)),
        (sphereLinearCoordinate u x -
          sphereLinearCoordinate u (sphereReflection v x)) ∂
          HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)) := by
  let μ := HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
  let f := sphereLinearCoordinate u
  let G := polarizationGain v (B : Set (SphereE n))
  let L := polarizationLoss v (B : Set (SphereE n))
  have hf : Integrable f μ := integrable_sphereLinearCoordinate u
  have hG : MeasurableSet G :=
    measurableSet_polarizationGain v B.isCompact.measurableSet
  have hL : MeasurableSet L :=
    measurableSet_polarizationLoss v B.isCompact.measurableSet
  have hLsub : L ⊆ (B : Set (SphereE n)) :=
    polarizationLoss_subset v _
  have hdisj : Disjoint ((B : Set (SphereE n)) \ L) G := by
    exact (polarizationGain_disjoint_original v _).symm.mono_left
      sdiff_subset
  have hpol :
      sphericalPolarization v (B : Set (SphereE n)) =
        ((B : Set (SphereE n)) \ L) ∪ G := by
    exact sphericalPolarization_eq_remove_loss_union_gain v hv _
  have hchange :
      ∫ x in L, f x ∂μ = ∫ x in G, f (sphereReflection v x) ∂μ := by
    have hmp := measurePreserving_sphereReflection v
    have hemb : MeasurableEmbedding (sphereReflection v) :=
      (sphereReflection v).measurableEmbedding
    have hcv :=
      hmp.setIntegral_preimage_emb hemb
        (fun y => f (sphereReflection v y)) G
    rw [sphereReflection_preimage_polarizationGain v hv] at hcv
    simpa only [sphereReflection_involutive] using hcv
  have hfR : Integrable (fun x => f (sphereReflection v x)) μ := by
    change Integrable (f ∘ sphereReflection v) μ
    exact
      (measurePreserving_sphereReflection v).integrable_comp_of_integrable hf
  have hsubint :
      ∫ x in G, (f x - f (sphereReflection v x)) ∂μ =
        (∫ x in G, f x ∂μ) -
          ∫ x in G, f (sphereReflection v x) ∂μ := by
    exact integral_sub hf.integrableOn hfR.integrableOn
  change
    (∫ x in sphericalPolarization v (B : Set (SphereE n)), f x ∂μ) -
        ∫ x in (B : Set (SphereE n)), f x ∂μ =
      ∫ x in G, (f x - f (sphereReflection v x)) ∂μ
  rw [hpol]
  rw [setIntegral_union hdisj hG
    (hf.integrableOn.mono_set sdiff_subset) hf.integrableOn]
  rw [setIntegral_sdiff hL hf.integrableOn hLsub]
  rw [hchange, hsubint]
  ring

lemma sphereLinearCoordinate_sub_reflection
    (u v : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ = 1)
    (x : SphereE n) :
    sphereLinearCoordinate u x -
        sphereLinearCoordinate u (sphereReflection v x) =
      2 * inner ℝ v (x : EuclideanSpace ℝ (Fin n)) * inner ℝ u v := by
  rw [sphereLinearCoordinate, sphereLinearCoordinate,
    inner_sphereReflection_of_unit v hv u x]
  ring

/-- Strict Lyapunov decrease when polarization actually moves a
positive-measure family of orbits toward the cap direction. -/
lemma sphericalMoment_polarizedCompacts_lt
    [Nonempty (Fin n)]
    (u v : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ = 1)
    (huv : inner ℝ u v < 0) (B : SphereCompacts n)
    (hgain : 0 < HDP.unitSphereMeasure
      (EuclideanSpace ℝ (Fin n))
      (polarizationGain v (B : Set (SphereE n)))) :
    sphericalMoment u (polarizedCompacts B v hv) <
      sphericalMoment u B := by
  let μ := HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
  let G := polarizationGain v (B : Set (SphereE n))
  let g : SphereE n → ℝ := fun x =>
    -(sphereLinearCoordinate u x -
      sphereLinearCoordinate u (sphereReflection v x))
  have hg_nonneg : ∀ x ∈ G, 0 ≤ g x := by
    intro x hx
    rw [show g x =
      -(2 * inner ℝ v (x : EuclideanSpace ℝ (Fin n)) *
          inner ℝ u v) by
        simp only [g, sphereLinearCoordinate_sub_reflection u v hv x]]
    have hxplus :
        0 < inner ℝ v (x : EuclideanSpace ℝ (Fin n)) := hx.2
    have hprod :
        2 * inner ℝ v (x : EuclideanSpace ℝ (Fin n)) *
            inner ℝ u v < 0 :=
      mul_neg_of_pos_of_neg (mul_pos (by norm_num) hxplus) huv
    linarith
  have hg_ne : ∀ x ∈ G, g x ≠ 0 := by
    intro x hx
    rw [show g x =
      -(2 * inner ℝ v (x : EuclideanSpace ℝ (Fin n)) *
          inner ℝ u v) by
        simp only [g, sphereLinearCoordinate_sub_reflection u v hv x]]
    have hxplus :
        0 < inner ℝ v (x : EuclideanSpace ℝ (Fin n)) := hx.2
    have hprod :
        2 * inner ℝ v (x : EuclideanSpace ℝ (Fin n)) *
            inner ℝ u v < 0 :=
      mul_neg_of_pos_of_neg (mul_pos (by norm_num) hxplus) huv
    linarith
  have hg_int : IntegrableOn g G μ := by
    exact
      ((integrable_sphereLinearCoordinate u).sub
        ((measurePreserving_sphereReflection v).integrable_comp_of_integrable
          (integrable_sphereLinearCoordinate u))).neg.integrableOn
  have hGmeas : MeasurableSet G :=
    measurableSet_polarizationGain v B.isCompact.measurableSet
  have hg_nonneg_ae : 0 ≤ᵐ[μ.restrict G] g := by
    filter_upwards [ae_restrict_mem hGmeas] with x hx
    exact hg_nonneg x hx
  have hg_pos : 0 < ∫ x in G, g x ∂μ := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae hg_nonneg_ae hg_int]
    exact lt_of_lt_of_le hgain
      (measure_mono fun x hx => ⟨hg_ne x hx, hx⟩)
  have hneg :
      (∫ x in G,
        (sphereLinearCoordinate u x -
          sphereLinearCoordinate u (sphereReflection v x)) ∂μ) =
        -∫ x in G, g x ∂μ := by
    rw [← integral_neg]
    apply setIntegral_congr_fun
      (measurableSet_polarizationGain v B.isCompact.measurableSet)
    intro x hx
    simp [g]
  have hsub :
      sphericalMoment u (polarizedCompacts B v hv) -
          sphericalMoment u B < 0 := by
    rw [sphericalMoment_polarizedCompacts_sub u v hv B, hneg]
    linarith
  linarith

end

end HDP.Appendix
