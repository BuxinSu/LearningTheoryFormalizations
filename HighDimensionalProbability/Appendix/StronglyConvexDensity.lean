import HighDimensionalProbability.Appendix.Infra.StrongLogConcave

/-!
# Strongly log-concave density concentration

This isolated file records HDP Theorem 5.2.11.  The proof uses the reusable
quadratic Prékopa--Leindler and property-`(τ)` infrastructure developed under
`Appendix/Infra`.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal RealInnerProductSpace

namespace HDP.Chapter5

/-- **HDP Theorem 5.2.11 (strongly convex exponential density).**

The proof uses the quadratic-cost Prékopa--Leindler property of a strongly
log-concave density and the property-`(τ)` Laplace-transform argument.
-/
theorem strongly_convex_density_concentration :
    ∃ C : ℝ, 0 < C ∧
      ∀ {n : ℕ} [NeZero n]
        (U : EuclideanSpace ℝ (Fin n) → ℝ) (hU : Measurable U)
        {κ : ℝ}, 0 < κ → StrongConvexOn Set.univ κ U →
        exponentialPotentialMeasure U Set.univ = 1 →
        HasMeanConcentration (exponentialPotentialMeasure U)
          (fun x y => dist x y) (C / Real.sqrt κ) := by
  refine ⟨Real.sqrt 2, Real.sqrt_pos.2 (by norm_num), ?_⟩
  intro n _ U hUm κ hκ hU hmass
  letI : IsProbabilityMeasure (exponentialPotentialMeasure U) := ⟨hmass⟩
  exact HDP.Appendix.gaussPL_metric_hasMeanConcentration
    (exponentialPotentialMeasure U)
    (fun p x y => (1 - p) • x + p • y) hκ
    (HDP.Appendix.gaussPL_exponentialPotentialMeasure U hUm hU)

end HDP.Chapter5
