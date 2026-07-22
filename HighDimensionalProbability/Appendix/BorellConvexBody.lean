import HighDimensionalProbability.Chapter3_RandomVectorsInHighDimensions
import Mathlib.Analysis.Convex.Body
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Convex-body normalized-law domain support

This appendix module proves the normalized uniform law and its domain
obligations for the full-dimensional convex bodies considered in
**Book Example 3.4.6** (physical pages 83–84, printed pages 75–76).
It makes no marginal tail or `ψ₁` theorem claim.
-/

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

namespace HDP.Chapter3

noncomputable section

/-- Normalized Lebesgue measure on a full-dimensional convex body.

The explicit nonempty-interior hypothesis used by the theorems below is
necessary because Mathlib's `ConvexBody` also permits lower-dimensional
compact convex sets.

**Book Example 3.4.6.** -/
def convexBodyUniformMeasure {n : ℕ}
    (K : ConvexBody (EuclideanSpace ℝ (Fin n))) :
    Measure (EuclideanSpace ℝ (Fin n)) :=
  ((volume : Measure (EuclideanSpace ℝ (Fin n))) (K : Set _))⁻¹ •
    (volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (K : Set _)

/-- A convex body with nonempty interior has positive finite volume, so its
normalized Lebesgue restriction is a probability measure.

**Book Example 3.4.6.** -/
theorem convexBodyUniformMeasure_isProbability
    {n : ℕ} (K : ConvexBody (EuclideanSpace ℝ (Fin n)))
    (hK : (interior (K : Set (EuclideanSpace ℝ (Fin n)))).Nonempty) :
    IsProbabilityMeasure (convexBodyUniformMeasure K) := by
  constructor
  unfold convexBodyUniformMeasure
  rw [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ]
  simp only [Set.univ_inter]
  exact ENNReal.inv_mul_cancel
    (Measure.measure_pos_of_nonempty_interior
      (volume : Measure (EuclideanSpace ℝ (Fin n))) hK).ne'
    K.isCompact.measure_lt_top.ne

/-- The identity random vector under the normalized convex-body law is
measurable.

**Book Example 3.4.6.** -/
theorem convexBodyUniformVector_measurable
    {n : ℕ} (_K : ConvexBody (EuclideanSpace ℝ (Fin n))) :
    Measurable (fun x : EuclideanSpace ℝ (Fin n) => x) :=
  measurable_id

/-- The identity random vector under a full-dimensional convex-body law has a
finite second moment.  This discharges the integrability convention implicit
in the source's isotropy hypothesis.

**Book Example 3.4.6.** -/
theorem convexBodyUniformVector_memLp_two
    {n : ℕ} (K : ConvexBody (EuclideanSpace ℝ (Fin n)))
    (hK : (interior (K : Set (EuclideanSpace ℝ (Fin n)))).Nonempty) :
    MemLp (fun x : EuclideanSpace ℝ (Fin n) => x) 2
      (convexBodyUniformMeasure K) := by
  letI : IsProbabilityMeasure (convexBodyUniformMeasure K) :=
    convexBodyUniformMeasure_isProbability K hK
  obtain ⟨C, hC⟩ := K.isBounded.exists_norm_le
  refine MemLp.of_bound measurable_id.aestronglyMeasurable C ?_
  unfold convexBodyUniformMeasure
  apply Measure.ae_smul_measure
  filter_upwards [ae_restrict_mem K.isClosed.measurableSet] with x hx
  exact hC x hx

/-- For the normalized convex-body law, the raw second-moment identity
therefore induces the source-facing isotropic-random-vector package.

**Book Definition 3.2.5; Book Example 3.4.6.** -/
theorem convexBodyUniformVector_isIsotropicRandomVector
    {n : ℕ} (K : ConvexBody (EuclideanSpace ℝ (Fin n)))
    (hK : (interior (K : Set (EuclideanSpace ℝ (Fin n)))).Nonempty)
    (hIso : IsIsotropic
      (fun x : EuclideanSpace ℝ (Fin n) => x)
      (convexBodyUniformMeasure K)) :
    IsIsotropicRandomVector
      (fun x : EuclideanSpace ℝ (Fin n) => x)
      (convexBodyUniformMeasure K) where
  isProbabilityMeasure := convexBodyUniformMeasure_isProbability K hK
  aemeasurable := measurable_id.aemeasurable
  memLp_two := convexBodyUniformVector_memLp_two K hK
  isIsotropic := hIso

end

end HDP.Chapter3
