import HighDimensionalProbability.Appendix.Infra.MajorizingMeasureRanked

/-!
# Fernique--Talagrand majorizing-measure lower bound

This appendix supplies the finite lower theorem by combining the canonical
Euclidean representation of a finite Gaussian process with the ranked
growth construction.
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators ENNReal NNReal RealInnerProductSpace

namespace HDP.Chapter8.Appendix

noncomputable section

variable {I Ω : Type*} [Fintype I] [Nonempty I] [MeasurableSpace Ω]

/-- Equality of canonical increments under the finite Euclidean
representation. -/
theorem canonicalRepresentation_increment_eq
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : I → Ω → ℝ)
    (hX : IsGaussianProcess X μ)
    (hX0 : HDP.IsCenteredProcess X μ)
    (hX2 : HDP.IsL2Process X μ)
    (a : I → EuclideanSpace ℝ I)
    (hlaw : IdentDistrib (HDP.Chapter7.processEuclideanVector X)
      (fun g => WithLp.toLp 2 (fun i => inner ℝ (a i) g)) μ
      (stdGaussian (EuclideanSpace ℝ I)))
    (s t : I) :
    HDP.processIncrement X μ s t = dist (a s) (a t) := by
  let F : EuclideanSpace ℝ I → ℝ :=
    fun v => (v s - v t) ^ 2
  have hF : Measurable F := by
    fun_prop
  have hsecond :
      HDP.Chapter7.processIncrementSecondMoment μ X s t =
        HDP.Chapter7.processIncrementSecondMoment
          (stdGaussian (EuclideanSpace ℝ I))
          (HDP.Chapter7.canonicalGaussianProcess a) s t := by
    have h := (hlaw.comp hF).integral_eq
    simpa [F, HDP.Chapter7.processIncrementSecondMoment,
      HDP.Chapter7.processEuclideanVector,
      HDP.Chapter7.canonicalGaussianProcess] using h
  have hXsq := processIncrement_sq_eq_secondMoment
    μ X hX hX0 hX2 s t
  have hcanGaussian :=
    HDP.Chapter7.canonicalGaussianProcess_isGaussian a
  have hcanCentered :=
    HDP.Chapter7.canonicalGaussianProcess_centered a
  have hcanL2 :=
    HDP.Chapter7.canonicalGaussianProcess_memLp_two a
  have hcansq := processIncrement_sq_eq_secondMoment
    (stdGaussian (EuclideanSpace ℝ I))
    (HDP.Chapter7.canonicalGaussianProcess a)
    hcanGaussian hcanCentered hcanL2 s t
  have hcandist :=
    HDP.Chapter7.canonicalGaussianProcess_increment a s t
  have hsquare :
      HDP.processIncrement X μ s t ^ 2 =
        dist (a s) (a t) ^ 2 := by
    calc
      HDP.processIncrement X μ s t ^ 2 =
          HDP.Chapter7.processIncrementSecondMoment μ X s t := hXsq
      _ = HDP.Chapter7.processIncrementSecondMoment
          (stdGaussian (EuclideanSpace ℝ I))
          (HDP.Chapter7.canonicalGaussianProcess a) s t := hsecond
      _ = HDP.processIncrement
          (HDP.Chapter7.canonicalGaussianProcess a)
          (stdGaussian (EuclideanSpace ℝ I)) s t ^ 2 := hcansq.symm
      _ = dist (a s) (a t) ^ 2 := by
        rw [hcandist, dist_eq_norm]
  have hinc0 := HDP.processIncrement_nonneg (hX2 s) (hX2 t)
  have hdist0 : 0 ≤ dist (a s) (a t) := dist_nonneg
  nlinarith

/-- The expected maximum is preserved by the finite Euclidean
representation. -/
theorem canonicalRepresentation_expectedSup_eq
    (μ : Measure Ω)
    (X : I → Ω → ℝ)
    (a : I → EuclideanSpace ℝ I)
    (hlaw : IdentDistrib (HDP.Chapter7.processEuclideanVector X)
      (fun g => WithLp.toLp 2 (fun i => inner ℝ (a i) g)) μ
      (stdGaussian (EuclideanSpace ℝ I))) :
    HDP.Chapter7.expectedFiniteSupremum μ X =
      localGaussianWidth a (Finset.univ : Finset I)
        Finset.univ_nonempty := by
  let F : EuclideanSpace ℝ I → ℝ :=
    fun v => Finset.univ.sup' Finset.univ_nonempty fun i : I => v i
  have hF : Measurable F := by
    have hcoord : ∀ i : I,
        Measurable (fun v : EuclideanSpace ℝ I => v i) := by
      intro i
      exact (measurable_pi_apply i).comp
        (WithLp.measurable_ofLp 2 _)
    have hsup :
        Measurable
          (Finset.univ.sup' Finset.univ_nonempty
            (fun i : I =>
              fun v : EuclideanSpace ℝ I => v i)) :=
      Finset.measurable_sup' Finset.univ_nonempty
        (fun i hi => hcoord i)
    have heq :
        (Finset.univ.sup' Finset.univ_nonempty
            (fun i : I =>
              fun v : EuclideanSpace ℝ I => v i)) = F := by
      funext v
      exact Finset.sup'_apply Finset.univ_nonempty
        (fun i : I =>
          fun x : EuclideanSpace ℝ I => x i) v
    rw [← heq]
    exact hsup
  have h := (hlaw.comp hF).integral_eq
  simpa [F, HDP.Chapter7.expectedFiniteSupremum,
    HDP.Chapter5.finiteMaximum,
    HDP.Chapter7.processEuclideanVector,
    localGaussianWidth, localGaussianMaximum,
    Finset.sup'_apply] using h

/-- The finite Gaussian-process form of the majorizing-measure lower
estimate. -/
theorem finiteGaussianProcess_gamma2_le_expectedSup
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : I → Ω → ℝ)
    (hX : IsGaussianProcess X μ)
    (hX0 : HDP.IsCenteredProcess X μ)
    (hX2 : HDP.IsL2Process X μ) :
    (HDP.gamma2 (HDP.Chapter8.canonicalProcessEDistance X μ)).toReal ≤
      11520078400 *
        HDP.Chapter7.expectedFiniteSupremum μ X := by
  obtain ⟨a, hlaw⟩ :=
    finiteGaussianProcess_canonicalRepresentation μ X hX hX0
  let anchor : I := Classical.choice (inferInstance : Nonempty I)
  have hmetric :
      HDP.Chapter8.canonicalProcessEDistance X μ =
        fun s t => ENNReal.ofReal (dist (a s) (a t)) := by
    funext s t
    rw [HDP.Chapter8.canonicalProcessEDistance,
      canonicalRepresentation_increment_eq
        μ X hX hX0 hX2 a hlaw s t]
  have hwidth := gamma2_euclidean_le_width a anchor
  have hsup :=
    canonicalRepresentation_expectedSup_eq μ X a hlaw
  rw [hmetric]
  calc
    (HDP.gamma2
        (fun s t => ENNReal.ofReal (dist (a s) (a t)))).toReal ≤
        11520078400 *
          localGaussianWidth a (Finset.univ : Finset I)
            Finset.univ_nonempty := hwidth
    _ = 11520078400 *
        HDP.Chapter7.expectedFiniteSupremum μ X := by
      rw [← hsup]

end

end HDP.Chapter8.Appendix

namespace HDP.Chapter8

/-- **HDP Theorem 8.5.5, lower majorizing-measure bound (finite form).**

The witness is proved in the appendix from the finite canonical
representation and a complete ranked separated-growth construction. -/
theorem majorizingMeasureLowerPrinciple_external :
    Nonempty MajorizingMeasureLowerPrinciple := by
  refine ⟨{
    constant := 11520078400
    constant_pos := by norm_num
    lower := ?_ }⟩
  intro I Ω instI instI0 instΩ μ instμ X hX hX0 hX2 hfinite
  exact Appendix.finiteGaussianProcess_gamma2_le_expectedSup
    μ X hX hX0 hX2

end HDP.Chapter8
