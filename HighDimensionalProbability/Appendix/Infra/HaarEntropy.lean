import HighDimensionalProbability.Appendix.Infra.ProductEntropy
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Entropy decomposition by right-Haar averaging

Let `μ` be a right-invariant probability measure on a measurable group and
let `ν` be any probability measure on the same group (in applications, Haar
measure on a compact subgroup, pushed forward to the ambient group).  The
right average

`A f (x) = ∫ h, f (x * h) ∂ν`

gives the exact entropy decomposition

`Ent_μ(f) = Ent_μ(A f) + ∫ Ent_ν(h ↦ f (x*h)) ∂μ(x)`.

The proof is just the entropy chain rule on `ν × μ`, followed by the
measure-preserving Haar shear `(h,x) ↦ x*h`.  In particular it avoids choosing
a measurable section of the homogeneous quotient.
-/

open MeasureTheory ProbabilityTheory Real

namespace HDP.Appendix

/-- Right averaging of a real-valued function by a probability measure on the
same group. -/
noncomputable def rightAverage
    {G : Type*} [MeasurableSpace G] [Mul G]
    (ν : Measure G) (f : G → ℝ) (x : G) : ℝ :=
  ∫ h, f (x * h) ∂ν

/-- A normalized Haar measure on a compact group is also invariant under
right multiplication.  Mathlib's base Haar typeclass is left-oriented, so
we record the probability-normalized compact consequence explicitly. -/
theorem probabilityHaar_map_mul_right_eq_self
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [CompactSpace G]
    (μ : Measure G) [Measure.IsHaarMeasure μ] [IsProbabilityMeasure μ]
    (g : G) :
    Measure.map (fun x => x * g) μ = μ := by
  letI : IsProbabilityMeasure (Measure.map (fun x => x * g) μ) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  have heq := Measure.isMulInvariant_eq_smul_of_compactSpace
    (Measure.map (fun x => x * g) μ) μ
  have hmass := congrArg (fun ν : Measure G => ν Set.univ) heq
  have hscalar :
      Measure.haarScalarFactor
          (Measure.map (fun x => x * g) μ) μ = 1 := by
    simpa using hmass.symm
  simpa [hscalar] using heq

/-- Typeclass-form wrapper for the preceding compact normalized-Haar
invariance theorem.  It is deliberately a definition rather than a global
instance, so applications can install it locally without changing Mathlib's
left-oriented Haar instance search. -/
@[reducible] def probabilityHaarIsMulRightInvariant
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [CompactSpace G]
    (μ : Measure G) [Measure.IsHaarMeasure μ] [IsProbabilityMeasure μ] :
    Measure.IsMulRightInvariant μ where
  map_mul_right_eq_self :=
    probabilityHaar_map_mul_right_eq_self μ

/-- Inversion preserves normalized Haar probability on a compact group. -/
theorem probabilityHaar_map_inv_eq_self
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [CompactSpace G]
    (μ : Measure G) [Measure.IsHaarMeasure μ] [IsProbabilityMeasure μ] :
    Measure.map Inv.inv μ = μ := by
  letI : Measure.IsMulRightInvariant μ :=
    probabilityHaarIsMulRightInvariant μ
  letI : Measure.IsMulLeftInvariant (Measure.map Inv.inv μ) := by
    change Measure.IsMulLeftInvariant μ.inv
    infer_instance
  letI : IsProbabilityMeasure (Measure.map Inv.inv μ) :=
    Measure.isProbabilityMeasure_map measurable_inv.aemeasurable
  have heq := Measure.isMulInvariant_eq_smul_of_compactSpace
    (Measure.map Inv.inv μ) μ
  have hmass := congrArg (fun ν : Measure G => ν Set.univ) heq
  have hscalar :
      Measure.haarScalarFactor (Measure.map Inv.inv μ) μ = 1 := by
    simpa using hmass.symm
  simpa [hscalar] using heq

private lemma map_snd_mul_of_rightInvariant
    {G : Type*} [MeasurableSpace G] [Group G] [MeasurableMul₂ G]
    (μ ν : Measure G) [SFinite μ] [IsProbabilityMeasure ν]
    [Measure.IsMulRightInvariant μ] :
    Measure.map (fun p : G × G => p.2 * p.1) (ν.prod μ) = μ := by
  have hshear :
      Measure.map (fun p : G × G => (p.1, p.2 * p.1)) (ν.prod μ) =
        ν.prod μ :=
    (measurePreserving_prod_mul_right ν μ).map_eq
  calc
    Measure.map (fun p : G × G => p.2 * p.1) (ν.prod μ) =
        Measure.map Prod.snd
          (Measure.map (fun p : G × G => (p.1, p.2 * p.1))
            (ν.prod μ)) := by
      rw [Measure.map_map]
      · rfl
      · exact measurable_snd
      · exact measurable_fst.prodMk (measurable_snd.mul measurable_fst)
    _ = Measure.map Prod.snd (ν.prod μ) := by rw [hshear]
    _ = μ := by
      rw [Measure.map_snd_prod, measure_univ, one_smul]

/-- Exact entropy decomposition under right averaging.

The explicit integrability assumptions are the ones required by the
product-entropy chain rule.  They are automatic for the uniformly positive
bounded smooth densities used in the `SO(n)` logarithmic-Sobolev induction. -/
theorem boltzmannEntropy_eq_rightAverage_add
    {G : Type*} [MeasurableSpace G] [Group G] [MeasurableMul₂ G]
    (μ ν : Measure G) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [Measure.IsMulRightInvariant μ]
    (f : G → ℝ)
    (hf : Measurable f)
    (hprod : Integrable (fun p : G × G => f (p.2 * p.1)) (ν.prod μ))
    (hprodlog : Integrable
      (fun p : G × G =>
        f (p.2 * p.1) * Real.log (f (p.2 * p.1))) (ν.prod μ))
    (havlog : Integrable
      (fun x =>
        rightAverage ν f x * Real.log (rightAverage ν f x)) μ) :
    boltzmannEntropy μ f =
      (∫ x, boltzmannEntropy ν (fun h => f (x * h)) ∂μ) +
        boltzmannEntropy μ (rightAverage ν f) := by
  let F : G × G → ℝ := fun p => f (p.2 * p.1)
  have hmap :
      Measure.map (fun p : G × G => p.2 * p.1) (ν.prod μ) = μ :=
    map_snd_mul_of_rightInvariant μ ν
  have hFentropy :
      boltzmannEntropy (ν.prod μ) F = boltzmannEntropy μ f := by
    unfold boltzmannEntropy
    have hmeas : Measurable (fun p : G × G => p.2 * p.1) := by fun_prop
    have hfirst :
        (∫ p, F p * Real.log (F p) ∂(ν.prod μ)) =
          ∫ x, f x * Real.log (f x) ∂μ := by
      have h := integral_map (μ := ν.prod μ) hmeas.aemeasurable
        ((hf.mul hf.log).aestronglyMeasurable)
      rw [hmap] at h
      exact h.symm
    have hsecond :
        (∫ p, F p ∂(ν.prod μ)) = ∫ x, f x ∂μ := by
      have h := integral_map (μ := ν.prod μ) hmeas.aemeasurable
        hf.aestronglyMeasurable
      rw [hmap] at h
      exact h.symm
    rw [hfirst, hsecond]
  have hchain := boltzmannEntropy_prod_eq ν μ F hprod hprodlog havlog
  rw [hFentropy] at hchain
  change boltzmannEntropy μ f =
    (∫ y, boltzmannEntropy ν (fun x => f (y * x)) ∂μ) +
      boltzmannEntropy μ (fun y => ∫ x, f (y * x) ∂ν)
  exact hchain

/-- Symmetric presentation of the same decomposition, with the quotient
entropy written first. -/
theorem boltzmannEntropy_eq_rightAverage
    {G : Type*} [MeasurableSpace G] [Group G] [MeasurableMul₂ G]
    (μ ν : Measure G) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [Measure.IsMulRightInvariant μ]
    (f : G → ℝ)
    (hf : Measurable f)
    (hprod : Integrable (fun p : G × G => f (p.2 * p.1)) (ν.prod μ))
    (hprodlog : Integrable
      (fun p : G × G =>
        f (p.2 * p.1) * Real.log (f (p.2 * p.1))) (ν.prod μ))
    (havlog : Integrable
      (fun x =>
        rightAverage ν f x * Real.log (rightAverage ν f x)) μ) :
    boltzmannEntropy μ f =
      boltzmannEntropy μ (rightAverage ν f) +
        ∫ x, boltzmannEntropy ν (fun h => f (x * h)) ∂μ := by
  rw [boltzmannEntropy_eq_rightAverage_add μ ν f hf
    hprod hprodlog havlog, add_comm]

end HDP.Appendix
