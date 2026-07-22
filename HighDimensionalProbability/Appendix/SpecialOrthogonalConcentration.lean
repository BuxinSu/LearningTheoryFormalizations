import HighDimensionalProbability.Appendix.Infra.Concentration
import HighDimensionalProbability.Appendix.Infra.BoundedMetricConcentration
import HighDimensionalProbability.Appendix.Infra.SpecialOrthogonalLieAlgebra
import HighDimensionalProbability.Appendix.Infra.SpecialOrthogonalAmbientLogSobolev
import HighDimensionalProbability.Appendix.Infra.SpecialOrthogonalHerbst
import HighDimensionalProbability.Appendix.Infra.SubgaussianLimit
import HighDimensionalProbability.Chapter5_ConcentrationWithoutIndependence

/-!
# Concentration on the special orthogonal group

The old declaration overwrote the natural Borel sigma algebra with `⊤` and
quantified a potentially nonexistent full-powerset Haar law.  This corrected
statement uses the canonical normalized Borel Haar probability already
constructed in Chapter 5.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace HDP.Chapter5

/-- Frobenius distance on the special orthogonal group. -/
noncomputable def specialOrthogonalDistance {n : ℕ}
    (U V : Matrix.specialOrthogonalGroup (Fin n) ℝ) : ℝ :=
  HDP.matrixFrobeniusNorm
    ((U : Matrix (Fin n) (Fin n) ℝ) -
      (V : Matrix (Fin n) (Fin n) ℝ))

private lemma continuous_specialOrthogonalDistance (n : ℕ) :
    Continuous (fun p :
      Matrix.specialOrthogonalGroup (Fin n) ℝ ×
        Matrix.specialOrthogonalGroup (Fin n) ℝ =>
      specialOrthogonalDistance p.1 p.2) := by
  unfold specialOrthogonalDistance HDP.matrixFrobeniusNorm
  fun_prop

/-- Compactness gives a finite positive bound for the chordal Frobenius
diameter.  This supplies the elementary treatment of the exceptional circle
`SO(2)`, whose intrinsic Ricci curvature vanishes. -/
lemma exists_pos_specialOrthogonalDistance_bound (n : ℕ) :
    ∃ D : ℝ, 0 < D ∧
      ∀ U V : Matrix.specialOrthogonalGroup (Fin n) ℝ,
        specialOrthogonalDistance U V ≤ D := by
  have hbdd :
      BddAbove ((fun p :
          Matrix.specialOrthogonalGroup (Fin n) ℝ ×
            Matrix.specialOrthogonalGroup (Fin n) ℝ =>
          specialOrthogonalDistance p.1 p.2) '' Set.univ) :=
    IsCompact.bddAbove_image isCompact_univ
      (continuous_specialOrthogonalDistance n).continuousOn
  rcases bddAbove_def.mp hbdd with ⟨B, hB⟩
  refine ⟨max B 1, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro U V
  exact (hB _ ⟨(U, V), Set.mem_univ _, rfl⟩).trans (le_max_left _ _)

/-- **HDP Theorem 5.2.7 (special-orthogonal concentration).**

The proof uses the ambient logarithmic-Sobolev inequality obtained by
coordinate-stabilizer induction, applies Herbst to smooth ambient
approximations of a Lipschitz observable, and passes to the bounded pointwise
limit. -/
theorem special_orthogonal_concentration :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 2 ≤ n →
      HasMeanConcentration (specialOrthogonalHaarMeasure n)
        specialOrthogonalDistance (C / Real.sqrt n) := by
  refine ⟨16, by norm_num, ?_⟩
  intro n hn
  have hnpos : 0 < (n : ℝ) := by
    positivity
  have hρ : 0 ≤ (256 / (n : ℝ)) := by
    positivity
  intro f hf hLip hfint t ht
  obtain ⟨H, hHlip, hHeq⟩ :=
    HDP.Appendix.SpecialOrthogonal.exists_ambient_lipschitzExtension
      n f (by
        intro U V
        simpa [specialOrthogonalDistance] using hLip U V)
  let Xk : ℕ →
      Matrix.specialOrthogonalGroup (Fin n) ℝ → ℝ :=
    fun k U =>
      HDP.Appendix.SpecialOrthogonal.smoothLipschitzApproximation
        n H k
          (HDP.Appendix.SpecialOrthogonal.specialOrthogonalEmbedding n U)
  let X : Matrix.specialOrthogonalGroup (Fin n) ℝ → ℝ := f
  have hXkMeas : ∀ k, Measurable (Xk k) := by
    intro k
    exact
      ((HDP.Appendix.SpecialOrthogonal.smoothLipschitzApproximation_contDiff
          n H hHlip k).continuous.comp
        (HDP.Appendix.SpecialOrthogonal.continuous_specialOrthogonalEmbedding
          n)).measurable
  have hXMeas : Measurable X := by
    simpa [X] using hf
  obtain ⟨D, hD, hDbound⟩ :=
    exists_pos_specialOrthogonalDistance_bound n
  let e : Matrix.specialOrthogonalGroup (Fin n) ℝ := 1
  let B : ℝ := D + |f e| +
    Real.sqrt ((n : ℝ) * (n : ℝ))
  have hfBound (U : Matrix.specialOrthogonalGroup (Fin n) ℝ) :
      |f U| ≤ D + |f e| := by
    calc
      |f U| = |(f U - f e) + f e| := by ring_nf
      _ ≤ |f U - f e| + |f e| := abs_add_le _ _
      _ ≤ D + |f e| := by
        gcongr
        exact (hLip U e).trans (hDbound U e)
  have herror (k : ℕ)
      (U : Matrix.specialOrthogonalGroup (Fin n) ℝ) :
      |Xk k U - f U| ≤
        Real.sqrt ((n : ℝ) * (n : ℝ)) := by
    have happ :=
      HDP.Appendix.SpecialOrthogonal.smoothLipschitzApproximation_dist_le
        n H hHlip k
          (HDP.Appendix.SpecialOrthogonal.specialOrthogonalEmbedding n U)
    rw [Real.dist_eq] at happ
    rw [hHeq U] at happ
    calc
      |Xk k U - f U| ≤
          (1 / ((k : ℝ) + 1)) *
            Real.sqrt ((n : ℝ) * (n : ℝ)) := by
        simpa [Xk] using happ
      _ ≤ Real.sqrt ((n : ℝ) * (n : ℝ)) := by
        have hk : 1 / ((k : ℝ) + 1) ≤ 1 := by
          apply (div_le_one (by positivity)).2
          norm_num
        simpa only [one_mul] using
          (mul_le_mul_of_nonneg_right hk (Real.sqrt_nonneg _))
  have hXkBound : ∀ k U, |Xk k U| ≤ B := by
    intro k U
    calc
      |Xk k U| ≤ |Xk k U - f U| + |f U| := by
        have := abs_add_le (Xk k U - f U) (f U)
        simpa only [sub_add_cancel] using this
      _ ≤ Real.sqrt ((n : ℝ) * (n : ℝ)) + (D + |f e|) :=
        add_le_add (herror k U) (hfBound U)
      _ = B := by simp [B]; ring
  have hXBound : ∀ U, |X U| ≤ B := by
    intro U
    calc
      |X U| = |f U| := rfl
      _ ≤ D + |f e| := hfBound U
      _ ≤ B := by
        simp only [B]
        exact le_add_of_nonneg_right (Real.sqrt_nonneg _)
  have hlim : ∀ U, Filter.Tendsto
      (fun k => Xk k U) Filter.atTop (𝓝 (X U)) := by
    intro U
    have h :=
      HDP.Appendix.SpecialOrthogonal.smoothLipschitzApproximation_tendsto
        n H hHlip
          (HDP.Appendix.SpecialOrthogonal.specialOrthogonalEmbedding n U)
    simpa [Xk, X, hHeq U] using h
  have hsub :
      ∀ k,
        HasSubgaussianMGF
          (fun U =>
            Xk k U -
              ∫ V, Xk k V ∂(specialOrthogonalHaarMeasure n))
          ⟨256 / (n : ℝ), hρ⟩
          (specialOrthogonalHaarMeasure n) := by
    intro k
    let K :=
      HDP.Appendix.SpecialOrthogonal.smoothLipschitzApproximation n H k
    have hKc :
        ContDiff ℝ (⊤ : ℕ∞) K :=
      HDP.Appendix.SpecialOrthogonal.smoothLipschitzApproximation_contDiff
        n H hHlip k
    have hKdiff : Differentiable ℝ K :=
      hKc.differentiable (by simp)
    have hKf : Continuous (fderiv ℝ K) :=
      hKc.continuous_fderiv (by simp)
    have hKbound : ∀ y, ‖fderiv ℝ K y‖ ≤ 1 :=
      HDP.Appendix.SpecialOrthogonal.smoothLipschitzApproximation_fderiv_norm_le
        n H hHlip k
    simpa [Xk, K] using
      HDP.Appendix.SpecialOrthogonal.hasSubgaussianMGF_centered_of_ambient_logSobolev
        n (specialOrthogonalHaarMeasure n) (256 / (n : ℝ)) hρ
        (HDP.Appendix.SpecialOrthogonal.specialOrthogonal_ambient_logSobolev
          n hn)
        K hKdiff hKf hKbound
  have hsubLimit :
      HasSubgaussianMGF
        (fun U =>
          f U - ∫ V, f V ∂(specialOrthogonalHaarMeasure n))
        ⟨256 / (n : ℝ), hρ⟩
        (specialOrthogonalHaarMeasure n) := by
    simpa [X] using
      HDP.Appendix.hasSubgaussianMGF_centered_of_bounded_tendsto
        (specialOrthogonalHaarMeasure n) Xk X
        ⟨256 / (n : ℝ), hρ⟩ B
        hXkMeas hXMeas hXkBound hXBound hlim hsub
  have htail :=
    HDP.Appendix.twoSidedTail_of_hasSubgaussianMGF
      (specialOrthogonalHaarMeasure n)
      (fun U =>
        f U - ∫ V, f V ∂(specialOrthogonalHaarMeasure n))
      ⟨256 / (n : ℝ), hρ⟩ hsubLimit t ht
  have hscale :
      (16 / Real.sqrt (n : ℝ)) ^ 2 = 256 / (n : ℝ) := by
    rw [div_pow, Real.sq_sqrt hnpos.le]
    norm_num
  change
    (specialOrthogonalHaarMeasure n).real
        {x | t ≤ |f x -
          ∫ V, f V ∂(specialOrthogonalHaarMeasure n)|} ≤
      2 * Real.exp (-t ^ 2 / (2 * (256 / (n : ℝ)))) at htail
  simpa only [hscale] using htail

end HDP.Chapter5
