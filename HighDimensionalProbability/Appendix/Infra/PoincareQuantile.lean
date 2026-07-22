import HighDimensionalProbability.Appendix.Infra.PoincareCap
import Mathlib.Probability.CDF

/-!
# Exact spherical-cap quantiles

The one-dimensional marginal of normalized surface measure on a sphere has
an explicit density.  Consequently it has no atoms, its cumulative
distribution function is continuous, and every probability strictly between
zero and one is the mass of a spherical cap.
-/

open MeasureTheory ProbabilityTheory Set Metric InnerProductSpace Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace HDP.Appendix

lemma unit_ne_zero {E : Type*} [NormedAddCommGroup E]
    (u : E) (hu : ‖u‖ = 1) : u ≠ 0 := by
  intro h
  rw [h, norm_zero] at hu
  exact zero_ne_one hu

/-- The span of a unit vector, identified isometrically with `ℝ`. -/
noncomputable def spanUnitEquiv {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (u : E) (hu : ‖u‖ = 1) :
    (ℝ ∙ u : Submodule ℝ E) ≃ₗᵢ[ℝ] ℝ where
  __ := LinearEquiv.coord ℝ E u (unit_ne_zero u hu)
  norm_map' y := by
    calc
      ‖(LinearEquiv.coord ℝ E u (unit_ne_zero u hu)) y‖ =
          ‖(LinearEquiv.coord ℝ E u (unit_ne_zero u hu)) y‖ * ‖u‖ := by
            rw [hu, mul_one]
      _ = ‖(LinearEquiv.coord ℝ E u (unit_ne_zero u hu)) y • u‖ := by
            rw [norm_smul]
      _ = ‖(y : E)‖ := congrArg norm
            (LinearEquiv.coord_apply_smul ℝ E u (unit_ne_zero u hu) y)
      _ = ‖y‖ := rfl

lemma spanUnitEquiv_apply_eq_inner {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (u : E) (hu : ‖u‖ = 1)
    (y : (ℝ ∙ u : Submodule ℝ E)) :
    spanUnitEquiv u hu y = inner ℝ u (y : E) := by
  have hy : spanUnitEquiv u hu y • u = (y : E) := by
    exact LinearEquiv.coord_apply_smul ℝ E u (unit_ne_zero u hu) y
  rw [← hy, inner_smul_right, real_inner_self_eq_norm_sq, hu]
  simp

/-- Orthogonal decomposition along a prescribed unit vector, with its span
written as the first real coordinate of an `L²` product. -/
noncomputable def unitOrthogonalDecomposition {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (u : E) (hu : ‖u‖ = 1) :
    E ≃ₗᵢ[ℝ] WithLp 2 (ℝ × (ℝ ∙ u : Submodule ℝ E)ᗮ) :=
  ((ℝ ∙ u : Submodule ℝ E).orthogonalDecomposition).trans
    (LinearIsometryEquiv.withLpProdCongr 2 (spanUnitEquiv u hu)
      (LinearIsometryEquiv.refl ℝ ((ℝ ∙ u : Submodule ℝ E)ᗮ)))

lemma firstL2Coordinate_unitOrthogonalDecomposition {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (u x : E) (hu : ‖u‖ = 1) :
    HDP.firstL2Coordinate ((ℝ ∙ u : Submodule ℝ E)ᗮ)
      (unitOrthogonalDecomposition u hu x) = inner ℝ u x := by
  rw [unitOrthogonalDecomposition]
  change spanUnitEquiv u hu
      ((ℝ ∙ u : Submodule ℝ E).orthogonalProjectionOnto x) = inner ℝ u x
  rw [spanUnitEquiv_apply_eq_inner]
  let us : (ℝ ∙ u : Submodule ℝ E) :=
    ⟨u, Submodule.mem_span_singleton_self u⟩
  have h :=
    (ℝ ∙ u : Submodule ℝ E).inner_orthogonalProjectionOnto_eq_of_mem_left us x
  exact h

end HDP.Appendix

namespace ProbabilityTheory

/-- The CDF of an atomless real probability measure is continuous. -/
lemma continuous_cdf_of_noAtoms (μ : Measure ℝ)
    [IsProbabilityMeasure μ] [NoAtoms μ] :
    Continuous (cdf μ) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [(monotone_cdf μ).continuousAt_iff_leftLim_eq_rightLim,
    StieltjesFunction.rightLim_eq]
  apply le_antisymm
  · exact (monotone_cdf μ).leftLim_le le_rfl
  · have hzero : (cdf μ).measure {x} = 0 := by
      rw [measure_cdf μ]
      exact measure_singleton x
    rw [StieltjesFunction.measure_singleton] at hzero
    have hnonpos : cdf μ x - Function.leftLim (cdf μ) x ≤ 0 :=
      ENNReal.ofReal_eq_zero.mp hzero
    linarith

/-- Every value strictly between zero and one is attained by the CDF of an
atomless real probability measure. -/
lemma exists_cdf_eq_of_mem_Ioo (μ : Measure ℝ)
    [IsProbabilityMeasure μ] [NoAtoms μ]
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    ∃ x : ℝ, cdf μ x = p := by
  obtain ⟨a, ha⟩ :
      ∃ a : ℝ, cdf μ a < p :=
    ((tendsto_order.1 (tendsto_cdf_atBot μ)).2 p hp.1).exists
  obtain ⟨b, hb⟩ :
      ∃ b : ℝ, p < cdf μ b :=
    ((tendsto_order.1 (tendsto_cdf_atTop μ)).1 p hp.2).exists
  have hab : a ≤ b := by
    by_contra h
    have := monotone_cdf μ (le_of_not_ge h)
    linarith
  have hpIcc : p ∈ Icc (cdf μ a) (cdf μ b) := ⟨ha.le, hb.le⟩
  obtain ⟨x, _hx, hxp⟩ :=
    intermediate_value_Icc hab
      (continuous_cdf_of_noAtoms μ).continuousOn hpIcc
  exact ⟨x, hxp⟩

end ProbabilityTheory

namespace HDP.Appendix

/-- The unscaled linear coordinate on a unit sphere. -/
def sphereLinearCoordinate {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (u : E) :
    Metric.sphere (0 : E) 1 → ℝ :=
  fun x => inner ℝ u (x : E)

lemma measurable_sphereLinearCoordinate {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] (u : E) :
    Measurable (sphereLinearCoordinate u) := by
  unfold sphereLinearCoordinate
  fun_prop

lemma sphereLinearCoordinate_unitOrthogonalDecomposition {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (u : E) (hu : ‖u‖ = 1)
    (x : Metric.sphere (0 : E) 1) :
    HDP.firstL2SphereCoordinate ((ℝ ∙ u : Submodule ℝ E)ᗮ)
        (HDP.unitSphereHomeomorph
          (unitOrthogonalDecomposition u hu) x) =
      sphereLinearCoordinate u x := by
  exact firstL2Coordinate_unitOrthogonalDecomposition u x hu

/-- Rotation invariance reduces every spherical linear coordinate to the
first coordinate in an orthogonal `L²` decomposition. -/
lemma map_sphereLinearCoordinate_unitSphereMeasure {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (u : E) (hu : ‖u‖ = 1) :
    Measure.map (sphereLinearCoordinate u) (HDP.unitSphereMeasure E) =
      Measure.map
        (HDP.firstL2SphereCoordinate ((ℝ ∙ u : Submodule ℝ E)ᗮ))
        (HDP.unitSphereMeasure
          (WithLp 2 (ℝ × (ℝ ∙ u : Submodule ℝ E)ᗮ))) := by
  let J := unitOrthogonalDecomposition u hu
  calc
    Measure.map (sphereLinearCoordinate u) (HDP.unitSphereMeasure E) =
        Measure.map
          (HDP.firstL2SphereCoordinate ((ℝ ∙ u : Submodule ℝ E)ᗮ) ∘
            HDP.unitSphereHomeomorph J)
          (HDP.unitSphereMeasure E) := by
            apply Measure.map_congr
            filter_upwards with x
            exact
              (sphereLinearCoordinate_unitOrthogonalDecomposition u hu x).symm
    _ = Measure.map
          (HDP.firstL2SphereCoordinate ((ℝ ∙ u : Submodule ℝ E)ᗮ))
          (Measure.map (HDP.unitSphereHomeomorph J)
            (HDP.unitSphereMeasure E)) := by
            rw [Measure.map_map
              (HDP.measurable_firstL2SphereCoordinate
                ((ℝ ∙ u : Submodule ℝ E)ᗮ))
              (HDP.unitSphereHomeomorph J).measurable]
    _ = Measure.map
          (HDP.firstL2SphereCoordinate ((ℝ ∙ u : Submodule ℝ E)ᗮ))
          (HDP.unitSphereMeasure
            (WithLp 2 (ℝ × (ℝ ∙ u : Submodule ℝ E)ᗮ))) := by
            rw [HDP.map_unitSphereMeasure J]

lemma nontrivial_orthogonal_span_of_two_le_finrank {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (u : E) (hu : ‖u‖ = 1)
    (hdim : 2 ≤ Module.finrank ℝ E) :
    Nontrivial ((ℝ ∙ u : Submodule ℝ E)ᗮ) := by
  apply Module.nontrivial_of_finrank_pos (R := ℝ)
  have hsum :=
    (ℝ ∙ u : Submodule ℝ E).finrank_add_finrank_orthogonal
  rw [finrank_span_singleton (unit_ne_zero u hu)] at hsum
  omega

lemma noAtoms_map_sphereLinearCoordinate_unitSphereMeasure {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (u : E) (hu : ‖u‖ = 1)
    (hdim : 2 ≤ Module.finrank ℝ E) :
    NoAtoms
      (Measure.map (sphereLinearCoordinate u) (HDP.unitSphereMeasure E)) := by
  letI : Nontrivial ((ℝ ∙ u : Submodule ℝ E)ᗮ) :=
    nontrivial_orthogonal_span_of_two_le_finrank u hu hdim
  rw [map_sphereLinearCoordinate_unitSphereMeasure u hu,
    HDP.map_firstL2SphereCoordinate_unitSphereMeasure]
  infer_instance

/-- Every nontrivial probability is the mass of a cap with prescribed unit
normal on a sphere of ambient dimension at least two. -/
lemma exists_sphericalCap_measure_eq
    {d : ℕ} (hdim : 2 ≤ d)
    (u : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1)
    {p : ℝ≥0∞} (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ b : ℝ,
      HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin d))
          (HDP.Chapter5.sphericalCap u b) = p := by
  letI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  let μ : Measure ℝ :=
    Measure.map (sphereLinearCoordinate u)
      (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin d)))
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    exact Measure.isProbabilityMeasure_map
      (measurable_sphereLinearCoordinate u).aemeasurable
  letI : NoAtoms μ := by
    dsimp [μ]
    exact noAtoms_map_sphereLinearCoordinate_unitSphereMeasure u hu
      (by simpa [finrank_euclideanSpace] using hdim)
  have hpTop : p ≠ ∞ := by
    exact ne_of_lt (hp1.trans ENNReal.one_lt_top)
  have hpReal : p.toReal ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact ENNReal.toReal_pos hp0.ne' hpTop
    · rw [← ENNReal.toReal_one,
        ENNReal.toReal_lt_toReal hpTop ENNReal.one_ne_top]
      exact hp1
  obtain ⟨b, hb⟩ :=
    ProbabilityTheory.exists_cdf_eq_of_mem_Ioo μ hpReal
  refine ⟨b, ?_⟩
  have hμ : μ (Iic b) = p := by
    rw [← ProbabilityTheory.ofReal_cdf μ b, hb,
      ENNReal.ofReal_toReal hpTop]
  rw [← hμ]
  change
    HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin d))
        (HDP.Chapter5.sphericalCap u b) =
      Measure.map (sphereLinearCoordinate u)
        (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin d))) (Iic b)
  rw [Measure.map_apply (measurable_sphereLinearCoordinate u)
    measurableSet_Iic]
  rfl

/-- Every probability strictly between zero and one is the mass of a
one-dimensional standard-Gaussian lower half-line. -/
lemma exists_gaussianReal_Iic_eq {p : ℝ≥0∞}
    (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ a : ℝ, gaussianReal 0 1 (Iic a) = p := by
  let μ : Measure ℝ := gaussianReal 0 1
  letI : NoAtoms μ := by
    dsimp [μ]
    simp only [gaussianReal, one_ne_zero, if_false]
    infer_instance
  have hpTop : p ≠ ∞ := ne_of_lt (hp1.trans ENNReal.one_lt_top)
  have hpReal : p.toReal ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact ENNReal.toReal_pos hp0.ne' hpTop
    · rw [← ENNReal.toReal_one,
        ENNReal.toReal_lt_toReal hpTop ENNReal.one_ne_top]
      exact hp1
  obtain ⟨a, ha⟩ :=
    ProbabilityTheory.exists_cdf_eq_of_mem_Ioo μ hpReal
  refine ⟨a, ?_⟩
  rw [← ProbabilityTheory.ofReal_cdf μ a, ha,
    ENNReal.ofReal_toReal hpTop]

end HDP.Appendix
