import HighDimensionalProbability.Appendix.Infra.PoincareSphere
import HighDimensionalProbability.Chapter3_RandomVectorsInHighDimensions

/-!
# Multivariate weak Poincaré convergence

The rescaled first `n` coordinates of a uniform point on a sphere of
dimension tending to infinity converge weakly to standard Gaussian measure.
The proof uses the common infinite Gaussian product space already developed
for the one-dimensional projective central limit theorem.
-/

open MeasureTheory ProbabilityTheory Set Metric InnerProductSpace Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace HDP.Appendix

local instance :
    IsProbabilityMeasure HDP.Chapter3.projectiveProbability := by
  dsimp [HDP.Chapter3.projectiveProbability]
  infer_instance

/-- The first `n` Gaussian coordinates divided by the empirical norm of the
first `n+m` coordinates. -/
noncomputable def poincareGaussianRatio (n m : ℕ)
    (w : HDP.Chapter3.ProjectiveOmega) : EuclideanSpace ℝ (Fin n) :=
  (HDP.Chapter3.projectiveDenominator (n + m) w)⁻¹ •
    HDP.Chapter3.projectiveGaussianVector n w

lemma measurable_poincareGaussianRatio (n m : ℕ) :
    Measurable (poincareGaussianRatio n m) := by
  change Measurable (fun w : HDP.Chapter3.ProjectiveOmega =>
    (Real.sqrt ((∑ i ∈ Finset.range (n + m), (w i) ^ 2) /
      ((n + m : ℕ) : ℝ)))⁻¹ • WithLp.toLp 2 (fun i : Fin n => w i))
  fun_prop

lemma poincareGaussianRatio_ae_tendsto (n : ℕ) :
    ∀ᵐ w ∂HDP.Chapter3.projectiveProbability,
      Tendsto (fun k : ℕ => poincareGaussianRatio n (k + 2) w) atTop
        (𝓝 (HDP.Chapter3.projectiveGaussianVector n w)) := by
  have hindex : Tendsto (fun k : ℕ => n + (k + 2)) atTop atTop := by
    convert tendsto_add_atTop_nat (n + 2) using 1
    ext k
    omega
  filter_upwards [HDP.Chapter3.projectiveDenominator_ae] with w hw
  have hden := hw.comp hindex
  have hinv := hden.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  simpa [poincareGaussianRatio] using
    hinv.smul_const (HDP.Chapter3.projectiveGaussianVector n w)

lemma poincareGaussianRatio_tendstoInDistribution (n : ℕ) :
    TendstoInDistribution
      (fun k : ℕ => poincareGaussianRatio n (k + 2)) atTop
      (HDP.Chapter3.projectiveGaussianVector n)
      (fun _ => HDP.Chapter3.projectiveProbability)
      HDP.Chapter3.projectiveProbability := by
  exact tendstoInDistribution_of_ae_tendsto
    (fun k => (measurable_poincareGaussianRatio n (k + 2)).aemeasurable)
    (HDP.Chapter3.measurable_projectiveGaussianVector n).aemeasurable
    (poincareGaussianRatio_ae_tendsto n)

lemma poincareProjection_gaussianDirection_eq_ratio
    (n m : ℕ) [Nonempty (Fin (n + m))] (hdim : 0 < n + m)
    (w : HDP.Chapter3.ProjectiveOmega)
    (hw : HDP.Chapter3.projectiveGaussianVector (n + m) w ≠ 0) :
    poincareProjection n m
        (HDP.gaussianDirection
          (HDP.Chapter3.projectiveGaussianVector (n + m) w)) =
      poincareGaussianRatio n m w := by
  ext i
  rw [poincareGaussianRatio]
  change (Real.sqrt (n + m : ℝ) • poincareHead n m
      (((HDP.gaussianDirection
        (HDP.Chapter3.projectiveGaussianVector (n + m) w) :
          Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + m))) 1) :
            EuclideanSpace ℝ (Fin (n + m))))) i = _
  rw [HDP.Chapter3.coe_gaussianDirection_eq_inv_norm_smul _ hw]
  change Real.sqrt (n + m : ℝ) *
      (‖HDP.Chapter3.projectiveGaussianVector (n + m) w‖⁻¹ * w i) =
    (HDP.Chapter3.projectiveDenominator (n + m) w)⁻¹ * w i
  rw [HDP.Chapter3.projectiveDenominator_eq_norm_div_sqrt
    (n + m) hdim w]
  have hnorm : ‖HDP.Chapter3.projectiveGaussianVector (n + m) w‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hw
  have hsqrt : Real.sqrt (n + m : ℝ) ≠ 0 :=
    (Real.sqrt_pos.2 (by exact_mod_cast hdim)).ne'
  field_simp
  rw [Nat.cast_add]
  ring

lemma map_poincareProjection_unitSphereMeasure_eq_ratio
    (n m : ℕ) [Nonempty (Fin (n + m))] (hdim : 0 < n + m) :
    Measure.map (poincareProjection n m)
        (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin (n + m)))) =
      Measure.map (poincareGaussianRatio n m)
        HDP.Chapter3.projectiveProbability := by
  rw [← HDP.Chapter3.map_projectiveGaussianDirection (n + m)]
  rw [Measure.map_map (measurable_poincareProjection n m)
    ((HDP.measurable_gaussianDirection
      (E := EuclideanSpace ℝ (Fin (n + m)))).comp
        (HDP.Chapter3.measurable_projectiveGaussianVector (n + m)))]
  apply Measure.map_congr
  filter_upwards [HDP.Chapter3.projectiveGaussianVector_ae_ne_zero
    (n + m) hdim] with w hw
  exact poincareProjection_gaussianDirection_eq_ratio n m hdim w hw

/-- The law of the finite-dimensional Gaussian ratio used in the Poincaré limit. -/
noncomputable def poincareRatioPM (n k : ℕ) :
    ProbabilityMeasure (EuclideanSpace ℝ (Fin n)) :=
  ⟨Measure.map (poincareGaussianRatio n (k + 2))
      HDP.Chapter3.projectiveProbability,
    Measure.isProbabilityMeasure_map
      (measurable_poincareGaussianRatio n (k + 2)).aemeasurable⟩

/-- The law of the first `n` coordinates in the projective Gaussian product space. -/
noncomputable def projectiveGaussianVectorPM (n : ℕ) :
    ProbabilityMeasure (EuclideanSpace ℝ (Fin n)) :=
  ⟨Measure.map (HDP.Chapter3.projectiveGaussianVector n)
      HDP.Chapter3.projectiveProbability,
    Measure.isProbabilityMeasure_map
      (HDP.Chapter3.measurable_projectiveGaussianVector n).aemeasurable⟩

/-- The projected uniform-sphere law as a probability measure. -/
noncomputable def poincareProjectionPM (n k : ℕ) :
    ProbabilityMeasure (EuclideanSpace ℝ (Fin n)) := by
  letI : Nonempty (Fin (n + (k + 2))) := ⟨⟨0, by omega⟩⟩
  exact
    ⟨Measure.map (poincareProjection n (k + 2))
        (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin (n + (k + 2))))),
      Measure.isProbabilityMeasure_map
        (measurable_poincareProjection n (k + 2)).aemeasurable⟩

/-- Standard Gaussian probability measure on `EuclideanSpace ℝ (Fin n)`. -/
noncomputable def stdGaussianPM (n : ℕ) :
    ProbabilityMeasure (EuclideanSpace ℝ (Fin n)) :=
  ⟨stdGaussian (EuclideanSpace ℝ (Fin n)), inferInstance⟩

/-- Weak convergence of the fixed-dimensional Poincaré projections to
standard Gaussian measure. -/
lemma poincareProjectionPM_tendsto (n : ℕ) :
    Tendsto (fun k : ℕ => poincareProjectionPM n k) atTop
      (𝓝 (stdGaussianPM n)) := by
  have hratio : Tendsto (fun k : ℕ => poincareRatioPM n k) atTop
      (𝓝 (projectiveGaussianVectorPM n)) := by
    exact (poincareGaussianRatio_tendstoInDistribution n).tendsto
  have hseq : (fun k : ℕ => poincareProjectionPM n k) =
      fun k : ℕ => poincareRatioPM n k := by
    funext k
    apply Subtype.ext
    exact map_poincareProjection_unitSphereMeasure_eq_ratio
      n (k + 2) (by omega)
  have hlim : stdGaussianPM n = projectiveGaussianVectorPM n := by
    apply Subtype.ext
    exact (HDP.Chapter3.map_projectiveGaussianVector n).symm
  rw [hseq, hlim]
  exact hratio

end HDP.Appendix
