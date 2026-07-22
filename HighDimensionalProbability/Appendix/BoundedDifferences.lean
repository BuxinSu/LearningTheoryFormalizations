import HighDimensionalProbability.Appendix.Infra.BoundedDifferencesCore

/-!
# HDP Theorem 5.7.1: bounded differences

This is a proof of McDiarmid's inequality reconstructed from the proof in the
source: sharp Hoeffding's lemma is tensorized over the finite product and the
resulting MGF estimate is converted to a Chernoff tail bound.
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators ENNReal NNReal

namespace HDP.Chapter5

/-- **HDP Theorem 5.7.1 (bounded differences/McDiarmid).** -/
theorem bounded_differences :
    forall {N : Nat} {X : Fin N -> Type*} [forall i, MeasurableSpace (X i)]
      (mu : forall i, Measure (X i)) [forall i, IsProbabilityMeasure (mu i)]
      (f : (forall i, X i) -> Real) (c : Fin N -> Real),
      Measurable f -> (forall i, 0 <= c i) ->
      (forall x y i, (forall j, j ≠ i -> x j = y j) -> |f x - f y| <= c i) ->
      Integrable f (Measure.pi mu) -> forall t : Real, 0 <= t ->
        (Measure.pi mu).real
          {x | (∫ y, f y ∂(Measure.pi mu)) + t <= f x} <=
          Real.exp (-2 * t ^ 2 / ∑ i, c i ^ 2) := by
  intro N X _ mu _ f c hf hc hbounded hfint t ht
  have hsubg := Appendix.boundedDifferences_hasSubgaussianMGF
    mu f c hf hc hbounded hfint
  have htail := hsubg.measure_ge_le ht
  have hparam : (Appendix.boundedDifferencesParameter c : Real) =
      (∑ i, c i ^ 2) / 4 := by
    simp only [Appendix.boundedDifferencesParameter, NNReal.coe_sum,
      Appendix.coe_oscillationParameter (hc _)]
    rw [Finset.sum_div]
  have hevent :
      {x | (∫ y, f y ∂(Measure.pi mu)) + t <= f x} =
        {x | t <= f x - ∫ y, f y ∂(Measure.pi mu)} := by
    ext x
    simp only [Set.mem_setOf_eq]
    constructor <;> intro h <;> linarith
  rw [hevent]
  rw [hparam] at htail
  have hexponent :
      -(t ^ 2) / (2 * ((∑ i, c i ^ 2) / 4)) =
        -2 * t ^ 2 / ∑ i, c i ^ 2 := by
    by_cases hs : (∑ i, c i ^ 2) = 0
    · simp [hs]
    · field_simp [hs]
      ring
  rwa [hexponent] at htail

end HDP.Chapter5
