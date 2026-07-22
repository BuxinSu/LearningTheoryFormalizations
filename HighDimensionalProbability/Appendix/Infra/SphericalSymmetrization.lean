import HighDimensionalProbability.Appendix.Infra.SphericalPolarization
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Topology.MetricSpace.Closeds
import Mathlib.Topology.Order.Compact

/-!
# Compactness for spherical two-point symmetrization

The space of nonempty compact subsets of a compact metric space is compact in
the Hausdorff metric.  We use a slightly slack expansion comparison; unlike
the same-radius comparison it is closed under Hausdorff limits, and the slack
is harmless in the final isoperimetric argument.
-/

open MeasureTheory Set Metric InnerProductSpace Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace HDP.Appendix

noncomputable section

variable {n : ℕ}

/-- The space of nonempty compact subsets of the Euclidean unit sphere. -/
abbrev SphereCompacts (n : ℕ) :=
  TopologicalSpace.NonemptyCompacts (SphereE n)

lemma closedExpansion_mono_set {X : Type*} [PseudoMetricSpace X]
    {A B : Set X} (hAB : A ⊆ B) (r : ℝ) :
    closedExpansion r A ⊆ closedExpansion r B := by
  rintro x ⟨y, hyA, hxy⟩
  exact ⟨y, hAB hyA, hxy⟩

lemma closedExpansion_mono_radius {X : Type*} [PseudoMetricSpace X]
    (A : Set X) {r s : ℝ} (hrs : r ≤ s) :
    closedExpansion r A ⊆ closedExpansion s A := by
  rintro x ⟨y, hyA, hxy⟩
  exact ⟨y, hyA, hxy.trans hrs⟩

lemma closedExpansion_closedExpansion_subset {X : Type*}
    [PseudoMetricSpace X] (A : Set X) (r s : ℝ) :
    closedExpansion r (closedExpansion s A) ⊆
      closedExpansion (r + s) A := by
  rintro x ⟨y, ⟨z, hzA, hyz⟩, hxy⟩
  exact ⟨z, hzA, (dist_triangle x y z).trans (add_le_add hxy hyz)⟩

/-- Hausdorff-close nonempty compact sets are contained in one another's
closed expansions. -/
lemma NonemptyCompacts.subset_closedExpansion_of_dist_lt
    {B D : SphereCompacts n} {r : ℝ} (hBD : dist B D < r) :
    (B : Set (SphereE n)) ⊆ closedExpansion r (D : Set (SphereE n)) := by
  rw [Metric.NonemptyCompacts.dist_eq] at hBD
  intro x hxB
  have hfin :
      hausdorffEDist (B : Set (SphereE n)) (D : Set (SphereE n)) ≠ ∞ :=
    hausdorffEDist_ne_top_of_nonempty_of_bounded
      B.nonempty D.nonempty B.isCompact.isBounded D.isCompact.isBounded
  obtain ⟨y, hyD, hxy⟩ :=
    exists_dist_lt_of_hausdorffDist_lt hxB hBD hfin
  exact ⟨y, hyD, hxy.le⟩

/-- Compact competitors with the same mass as `K` and every strictly smaller
expansion controlled by the corresponding larger expansion of `K`. -/
def sphericalAdmissible
    [Nonempty (Fin n)] (K : SphereCompacts n) :
    Set (SphereCompacts n) :=
  {B |
    HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
        (B : Set (SphereE n)) =
      HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
        (K : Set (SphereE n)) ∧
    ∀ r s : ℝ, 0 ≤ r → r < s →
      HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
          (closedExpansion r (B : Set (SphereE n))) ≤
        HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
          (closedExpansion s (K : Set (SphereE n)))}

lemma self_mem_sphericalAdmissible
    [Nonempty (Fin n)] (K : SphereCompacts n) :
    K ∈ sphericalAdmissible K := by
  refine ⟨rfl, ?_⟩
  intro r s _ hrs
  exact measure_mono
    (closedExpansion_mono_radius (K : Set (SphereE n)) hrs.le)

lemma sphericalAdmissible_nonempty
    [Nonempty (Fin n)] (K : SphereCompacts n) :
    (sphericalAdmissible K).Nonempty :=
  ⟨K, self_mem_sphericalAdmissible K⟩

/-- The slack-admissible class is closed in the Hausdorff hyperspace. -/
lemma isClosed_sphericalAdmissible
    [Nonempty (Fin n)] (K : SphereCompacts n) :
    IsClosed (sphericalAdmissible K) := by
  apply IsSeqClosed.isClosed
  intro Bs B hBs hlim
  let μ := HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
  let δ : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have hδpos : ∀ j, 0 < δ j := by
    intro j
    dsimp [δ]
    positivity
  have hδlim : Tendsto δ atTop (nhds 0) := by
    simpa [δ] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun j : ℕ => (1 : ℝ) / (j + 1)) atTop (nhds 0))
  have hmass_ge :
      μ (K : Set (SphereE n)) ≤ μ (B : Set (SphereE n)) := by
    have ht :
        Tendsto
          (fun j => μ (Metric.cthickening (δ j) (B : Set (SphereE n))))
          atTop (nhds (μ (B : Set (SphereE n)))) :=
      (tendsto_measure_cthickening_of_isCompact B.isCompact).comp hδlim
    apply ge_of_tendsto' ht
    intro j
    obtain ⟨N, hN⟩ :=
      Metric.tendsto_atTop.1 hlim (δ j) (hδpos j)
    have hclose : dist (Bs N) B < δ j := hN N le_rfl
    have hsub :
        (Bs N : Set (SphereE n)) ⊆
          closedExpansion (δ j) (B : Set (SphereE n)) :=
      NonemptyCompacts.subset_closedExpansion_of_dist_lt hclose
    calc
      μ (K : Set (SphereE n)) =
          μ (Bs N : Set (SphereE n)) := (hBs N).1.symm
      _ ≤ μ (closedExpansion (δ j) (B : Set (SphereE n))) :=
        measure_mono hsub
      _ = μ (Metric.cthickening (δ j) (B : Set (SphereE n))) := by
        rw [closedExpansion_eq_cthickening B.isCompact.isClosed
          (hδpos j).le]
  have hmass_le :
      μ (B : Set (SphereE n)) ≤ μ (K : Set (SphereE n)) := by
    have h2δlim : Tendsto (fun j => 2 * δ j) atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul hδlim
    have ht :
        Tendsto
          (fun j => μ
            (Metric.cthickening (2 * δ j) (K : Set (SphereE n))))
          atTop (nhds (μ (K : Set (SphereE n)))) :=
      (tendsto_measure_cthickening_of_isCompact K.isCompact).comp h2δlim
    apply ge_of_tendsto' ht
    intro j
    obtain ⟨N, hN⟩ :=
      Metric.tendsto_atTop.1 hlim (δ j) (hδpos j)
    have hclose : dist B (Bs N) < δ j := by
      rw [dist_comm]
      exact hN N le_rfl
    have hsub :
        (B : Set (SphereE n)) ⊆
          closedExpansion (δ j) (Bs N : Set (SphereE n)) :=
      NonemptyCompacts.subset_closedExpansion_of_dist_lt hclose
    calc
      μ (B : Set (SphereE n)) ≤
          μ (closedExpansion (δ j) (Bs N : Set (SphereE n))) :=
        measure_mono hsub
      _ ≤ μ (closedExpansion (2 * δ j) (K : Set (SphereE n))) :=
        (hBs N).2 (δ j) (2 * δ j) (hδpos j).le (by
          nlinarith [hδpos j])
      _ = μ (Metric.cthickening (2 * δ j) (K : Set (SphereE n))) := by
        rw [closedExpansion_eq_cthickening K.isCompact.isClosed]
        positivity
  refine ⟨le_antisymm hmass_le hmass_ge, ?_⟩
  intro r s hr hrs
  let d := (s - r) / 2
  have hd : 0 < d := by
    dsimp [d]
    linarith
  obtain ⟨N, hN⟩ :=
    Metric.tendsto_atTop.1 hlim d hd
  have hclose : dist B (Bs N) < d := by
    rw [dist_comm]
    exact hN N le_rfl
  have hBsub :
      (B : Set (SphereE n)) ⊆
        closedExpansion d (Bs N : Set (SphereE n)) :=
    NonemptyCompacts.subset_closedExpansion_of_dist_lt hclose
  have hexp :
      closedExpansion r (B : Set (SphereE n)) ⊆
        closedExpansion (r + d) (Bs N : Set (SphereE n)) :=
    (closedExpansion_mono_set hBsub r).trans
      (closedExpansion_closedExpansion_subset
        (Bs N : Set (SphereE n)) r d)
  calc
    μ (closedExpansion r (B : Set (SphereE n))) ≤
        μ (closedExpansion (r + d) (Bs N : Set (SphereE n))) :=
      measure_mono hexp
    _ ≤ μ (closedExpansion s (K : Set (SphereE n))) :=
      (hBs N).2 (r + d) s (by positivity) (by
        dsimp [d]
        linarith)

lemma isCompact_sphericalAdmissible
    [Nonempty (Fin n)] (K : SphereCompacts n) :
    IsCompact (sphericalAdmissible K) :=
  (isClosed_sphericalAdmissible K).isCompact

/-- Polarization bundled as a nonempty compact set. -/
def polarizedCompacts (B : SphereCompacts n)
    (v : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ = 1) :
    SphereCompacts n :=
  ⟨⟨sphericalPolarization v (B : Set (SphereE n)),
      (isClosed_sphericalPolarization v
        B.isCompact.isClosed).isCompact⟩,
    sphericalPolarization_nonempty v hv B.nonempty⟩

@[simp]
lemma coe_polarizedCompacts (B : SphereCompacts n)
    (v : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ = 1) :
    (polarizedCompacts B v hv : Set (SphereE n)) =
      sphericalPolarization v (B : Set (SphereE n)) :=
  rfl

/-- Polarization preserves slack admissibility. -/
lemma sphericalPolarization_mem_sphericalAdmissible
    [Nonempty (Fin n)] (hn : 2 ≤ n)
    (K B : SphereCompacts n) (hB : B ∈ sphericalAdmissible K)
    (v : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ = 1) :
    polarizedCompacts B v hv ∈ sphericalAdmissible K := by
  constructor
  · change HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
        (sphericalPolarization v (B : Set (SphereE n))) =
      HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)) (K : Set (SphereE n))
    rw [unitSphereMeasure_sphericalPolarization hn v hv
      B.isCompact.measurableSet]
    exact hB.1
  · intro r s hr hrs
    calc
      HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
          (closedExpansion r
            (sphericalPolarization v (B : Set (SphereE n)))) ≤
        HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
          (closedExpansion r (B : Set (SphereE n))) :=
        unitSphereMeasure_closedExpansion_sphericalPolarization_le
          hn v hv r hr B.isCompact.isClosed
      _ ≤ HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
          (closedExpansion s (K : Set (SphereE n))) :=
        hB.2 r s hr hrs

end

end HDP.Appendix
