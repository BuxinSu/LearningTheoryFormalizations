import HighDimensionalProbability.Appendix.Infra.PoissonApproximation

/-!
# Triangular-array Poisson limit theorem

This module reconstructs the proof of the non-identically-distributed
rare-events limit using characteristic functions, Lévy convergence, and
Portmanteau.
-/

open MeasureTheory ProbabilityTheory Real Filter
open scoped ENNReal NNReal unitInterval Topology Nat BigOperators

namespace HDP.Chapter1

private lemma bernoulli_charFun_eq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ℝ} {p : I}
    (h : IsBernoulli X p μ) (t : ℝ) :
    charFun (μ.map X) t =
      1 + (p : ℂ) * (Complex.exp (t * Complex.I) - 1) := by
  rw [h.map_eq, charFun_apply_real, integral_bernoulliMeasure]
  push_cast
  simp
  ring

/-! ## HDP Theorem 1.7.6: the Poisson limit theorem -/

/-- **HDP Theorem 1.7.6 (Poisson limit theorem).**

For a triangular array of independent Bernoulli variables whose largest
success probability tends to zero and whose row mean tends to `lam`, the row
sums converge at every nonintegral CDF threshold to the Poisson law of rate
`lam`.
-/
theorem poisson_limit_theorem {Ω' : ℕ → Type*} [∀ N, MeasurableSpace (Ω' N)]
    (μ' : ∀ N, Measure (Ω' N)) [∀ N, IsProbabilityMeasure (μ' N)]
    (X : ∀ N, Fin N → Ω' N → ℝ) (p : ∀ N, Fin N → I) (lam : ℝ≥0)
    (hX : ∀ N i, IsBernoulli (X N i) (p N i) (μ' N))
    (hindep : ∀ N, iIndepFun (X N) (μ' N))
    (hmax : Tendsto (fun N => ⨆ i : Fin N, (p N i : ℝ)) atTop (𝓝 0))
    (hmean : Tendsto (fun N => ∑ i : Fin N, (p N i : ℝ)) atTop (𝓝 lam))
    (t : ℝ) (ht : ∀ k : ℕ, t ≠ k) :
    Tendsto (fun N => (μ' N).real {ω | ∑ i, X N i ω ≤ t}) atTop
      (𝓝 ((poissonMeasure lam).real {n : ℕ | (n : ℝ) ≤ t})) := by
  let S : ∀ N, Ω' N → ℝ := fun N ω => ∑ i : Fin N, X N i ω
  have hS : ∀ N, AEMeasurable (S N) (μ' N) := fun N => by
    exact Finset.aemeasurable_fun_sum Finset.univ fun i _ => (hX N i).aemeasurable
  let rowLaw : ℕ → ProbabilityMeasure ℝ := fun N =>
    ⟨(μ' N).map (S N), Measure.isProbabilityMeasure_map (hS N)⟩
  let poissonLaw : ProbabilityMeasure ℝ :=
    ⟨(poissonMeasure lam).map (fun n : ℕ => (n : ℝ)),
      Measure.isProbabilityMeasure_map .of_discrete⟩
  have hchar (u : ℝ) :
      Tendsto (fun N => charFun (rowLaw N) u) atTop
        (𝓝 (charFun poissonLaw u)) := by
    have hprod :
        Tendsto
          (fun N => ∏ i : Fin N,
            (1 + ((p N i : ℝ) : ℂ) *
              (Complex.exp (u * Complex.I) - 1)))
          atTop
          (𝓝 (Complex.exp ((lam : ℂ) *
            (Complex.exp (u * Complex.I) - 1)))) := by
      exact HDP.Appendix.tendsto_prod_one_add_of_max_sum
        (fun N i => (p N i : ℝ)) lam
        (fun N i => (p N i).2.1) hmax hmean
        (Complex.exp (u * Complex.I) - 1)
    have hrow (N : ℕ) :
        charFun (rowLaw N) u =
          ∏ i : Fin N,
            (1 + ((p N i : ℝ) : ℂ) *
              (Complex.exp (u * Complex.I) - 1)) := by
      change charFun ((μ' N).map (S N)) u = _
      rw [(hindep N).charFun_map_fun_sum_eq_prod
        (fun i => (hX N i).aemeasurable)]
      rw [Fintype.prod_apply]
      apply Finset.prod_congr rfl
      intro i hi
      exact bernoulli_charFun_eq (hX N i) u
    have hpoisson :
        charFun poissonLaw u =
          Complex.exp ((lam : ℂ) *
            (Complex.exp (u * Complex.I) - 1)) := by
      change charFun ((poissonMeasure lam).map (fun n : ℕ => (n : ℝ))) u =
        Complex.exp ((lam : ℂ) * (Complex.exp (u * Complex.I) - 1))
      exact charFun_map_cast_poissonMeasure lam u
    rw [hpoisson]
    exact hprod.congr' (Eventually.of_forall fun N => (hrow N).symm)
  have hweak : Tendsto rowLaw atTop (𝓝 poissonLaw) :=
    ProbabilityMeasure.tendsto_iff_tendsto_charFun.mpr hchar
  have hfrontier :
      (poissonLaw : Measure ℝ) (frontier (Set.Iic t)) = 0 := by
    rw [frontier_Iic]
    change ((poissonMeasure lam).map (fun n : ℕ => (n : ℝ))) {t} = 0
    rw [Measure.map_apply .of_discrete (measurableSet_singleton t)]
    have hempty : (fun n : ℕ => (n : ℝ)) ⁻¹' ({t} : Set ℝ) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro n hn
      change (n : ℝ) = t at hn
      exact ht n hn.symm
    rw [hempty, measure_empty]
  have hIic := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    hweak hfrontier
  have hreal := (ENNReal.tendsto_toReal (measure_ne_top (poissonLaw : Measure ℝ) (Set.Iic t))).comp
    hIic
  simp only [Function.comp_def] at hreal
  convert hreal using 1
  · funext N
    rw [measureReal_def]
    change ((μ' N) {ω | S N ω ≤ t}).toReal =
      (((μ' N).map (S N)) (Set.Iic t)).toReal
    rw [Measure.map_apply_of_aemeasurable (hS N) measurableSet_Iic]
    rfl
  · apply congrArg nhds
    rw [measureReal_def]
    change ((poissonMeasure lam) {n : ℕ | (n : ℝ) ≤ t}).toReal =
      (((poissonMeasure lam).map (fun n : ℕ => (n : ℝ))) (Set.Iic t)).toReal
    rw [Measure.map_apply .of_discrete measurableSet_Iic]
    rfl

end HDP.Chapter1
