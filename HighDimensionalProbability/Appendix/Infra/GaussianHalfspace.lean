import HighDimensionalProbability.Appendix.Infra.MetricExpansion
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Elementary Gaussian half-space geometry

This file isolates the elementary geometric and measure-theoretic parts of
Gaussian isoperimetry.  The genuinely isoperimetric step is deliberately not
hidden here: these lemmas reduce the measure of a half-space and its closed
expansion to the corresponding one-dimensional Gaussian quantities.
-/

open MeasureTheory ProbabilityTheory Set Metric InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace

namespace HDP.Appendix

/-- A closed affine half-space whose outward coordinate is `x ↦ ⟪u, x⟫`. -/
def gaussianLinearHalfspace {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (u : E) (a : ℝ) : Set E :=
  {x | inner ℝ u x ≤ a}

theorem isClosed_gaussianLinearHalfspace {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (u : E) (a : ℝ) :
    IsClosed (gaussianLinearHalfspace u a) := by
  have hcont : Continuous (fun x : E => inner ℝ u x) :=
    continuous_const.inner continuous_id
  exact isClosed_Iic.preimage hcont

theorem measurableSet_gaussianLinearHalfspace {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] (u : E) (a : ℝ) :
    MeasurableSet (gaussianLinearHalfspace u a) :=
  (isClosed_gaussianLinearHalfspace u a).measurableSet

/-- The closed `ε`-expansion of a unit-normal half-space is obtained by
shifting its threshold by `ε`. -/
theorem closedExpansion_gaussianLinearHalfspace {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u : E) (a ε : ℝ) (hu : ‖u‖ = 1) (hε : 0 ≤ ε) :
    closedExpansion ε (gaussianLinearHalfspace u a) =
      gaussianLinearHalfspace u (a + ε) := by
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    change inner ℝ u x ≤ a + ε
    change inner ℝ u y ≤ a at hy
    have hinner : inner ℝ u x ≤ inner ℝ u y + dist x y := by
      calc
        inner ℝ u x =
            inner ℝ u y + inner ℝ u (x - y) := by
              rw [inner_sub_right]
              ring
        _ ≤ inner ℝ u y + |inner ℝ u (x - y)| :=
          by
            simpa [add_comm] using
              add_le_add_left (le_abs_self (inner ℝ u (x - y))) (inner ℝ u y)
        _ ≤ inner ℝ u y + ‖u‖ * ‖x - y‖ :=
          by
            simpa [add_comm] using
              add_le_add_left (abs_real_inner_le_norm u (x - y)) (inner ℝ u y)
        _ = inner ℝ u y + dist x y := by
          rw [hu, one_mul, dist_eq_norm]
    linarith
  · intro hx
    change inner ℝ u x ≤ a + ε at hx
    by_cases hxa : inner ℝ u x ≤ a
    · exact ⟨x, hxa, by simpa using hε⟩
    · let t : ℝ := inner ℝ u x - a
      let y : E := x - t • u
      have ht : 0 < t := by
        dsimp [t]
        linarith
      have huu : inner ℝ u u = 1 := by
        rw [real_inner_self_eq_norm_sq, hu]
        norm_num
      refine ⟨y, ?_, ?_⟩
      · change inner ℝ u y ≤ a
        dsimp [y]
        rw [inner_sub_right, inner_smul_right, huu]
        dsimp [t]
        ring_nf
        exact le_rfl
      · rw [dist_eq_norm]
        dsimp [y]
        have hsub : x - (x - t • u) = t • u := by abel
        rw [hsub, norm_smul, hu, mul_one,
          Real.norm_eq_abs, abs_of_pos ht]
        dsimp [t]
        linarith

/-- A unit linear coordinate maps standard Gaussian measure to the standard
one-dimensional Gaussian measure. -/
theorem map_inner_stdGaussian {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (u : E) (hu : ‖u‖ = 1) :
    (stdGaussian E).map (innerSL ℝ u) = gaussianReal 0 1 := by
  rw [IsGaussian.map_eq_gaussianReal]
  rw [integral_strongDual_stdGaussian, variance_dual_stdGaussian,
    innerSL_apply_norm, hu]
  norm_num

/-- The Gaussian mass of a unit-normal half-space is its one-dimensional
Gaussian CDF value. -/
theorem stdGaussian_gaussianLinearHalfspace {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (u : E) (a : ℝ) (hu : ‖u‖ = 1) :
    stdGaussian E (gaussianLinearHalfspace u a) =
      gaussianReal 0 1 (Set.Iic a) := by
  have hm := map_inner_stdGaussian u hu
  have hmeas : Measurable (innerSL ℝ u) := (innerSL ℝ u).continuous.measurable
  calc
    stdGaussian E (gaussianLinearHalfspace u a) =
        (stdGaussian E).map (innerSL ℝ u) (Set.Iic a) := by
          rw [Measure.map_apply hmeas (measurableSet_Iic : MeasurableSet (Set.Iic a))]
          rfl
    _ = gaussianReal 0 1 (Set.Iic a) := by rw [hm]

/-- The mass of the closed expansion of a unit-normal Gaussian half-space is
the one-dimensional standard Gaussian CDF at the shifted threshold. -/
theorem stdGaussian_closedExpansion_gaussianLinearHalfspace {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (u : E) (a ε : ℝ)
    (hu : ‖u‖ = 1) (hε : 0 ≤ ε) :
    stdGaussian E (closedExpansion ε (gaussianLinearHalfspace u a)) =
      gaussianReal 0 1 (Set.Iic (a + ε)) := by
  rw [closedExpansion_gaussianLinearHalfspace u a ε hu hε,
    stdGaussian_gaussianLinearHalfspace u (a + ε) hu]

/-- The standard Gaussian measure assigns positive mass to every nonempty
real interval. -/
theorem gaussianReal_Ioc_pos {a b : ℝ} (hab : a < b) :
    0 < gaussianReal 0 1 (Set.Ioc a b) := by
  rw [gaussianReal_apply 0 one_ne_zero]
  rw [setLIntegral_pos_iff (measurable_gaussianPDF 0 1)]
  have hsupp : Function.support (gaussianPDF 0 1) = Set.univ := by
    ext x
    simp only [Function.mem_support, ne_eq, Set.mem_univ, iff_true]
    exact (ENNReal.ofReal_pos.mpr
      (gaussianPDFReal_pos 0 1 x one_ne_zero)).ne'
  rw [hsupp, Set.univ_inter]
  simp [Real.volume_Ioc, ENNReal.ofReal_pos, sub_pos.mpr hab]

/-- The one-dimensional standard Gaussian CDF, kept in `ℝ≥0∞` form, is
strictly increasing. -/
theorem strictMono_gaussianReal_Iic :
    StrictMono (fun a : ℝ => gaussianReal 0 1 (Set.Iic a)) := by
  intro a b hab
  have hdecomp : Set.Iic b = Set.Iic a ∪ Set.Ioc a b := by
    ext x
    simp only [Set.mem_Iic, Set.mem_union, Set.mem_Ioc]
    constructor
    · intro hxb
      exact le_or_gt x a |>.elim (fun hxa => Or.inl hxa)
        (fun hax => Or.inr ⟨hax, hxb⟩)
    · rintro (hxa | ⟨_, hxb⟩)
      · exact hxa.trans hab.le
      · exact hxb
  have hdisj : Disjoint (Set.Iic a) (Set.Ioc a b) := by
    exact Set.disjoint_left.2 (fun _ hle hlt => (not_lt_of_ge hle) hlt.1)
  change gaussianReal 0 1 (Set.Iic a) < gaussianReal 0 1 (Set.Iic b)
  rw [hdecomp, measure_union hdisj (measurableSet_Ioc : MeasurableSet (Set.Ioc a b))]
  exact ENNReal.lt_add_right
    (measure_ne_top (gaussianReal 0 1) (Set.Iic a))
    (gaussianReal_Ioc_pos hab).ne'

/-- Unit-normal Gaussian half-spaces with the same Gaussian mass have the
same threshold.  Their normal directions need not agree. -/
theorem threshold_eq_of_stdGaussian_halfspace_mass_eq {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {u v : E} {a b : ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hmass : stdGaussian E (gaussianLinearHalfspace u a) =
      stdGaussian E (gaussianLinearHalfspace v b)) :
    a = b := by
  rw [stdGaussian_gaussianLinearHalfspace u a hu,
    stdGaussian_gaussianLinearHalfspace v b hv] at hmass
  exact strictMono_gaussianReal_Iic.injective hmass

/-- The desired Gaussian enlargement comparison is an equality when the
competitor is itself a unit-normal half-space of the same mass. -/
theorem stdGaussian_closedExpansion_halfspace_eq_of_mass_eq {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {u v : E} {a b ε : ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hε : 0 ≤ ε)
    (hmass : stdGaussian E (gaussianLinearHalfspace u a) =
      stdGaussian E (gaussianLinearHalfspace v b)) :
    stdGaussian E (closedExpansion ε (gaussianLinearHalfspace u a)) =
      stdGaussian E (closedExpansion ε (gaussianLinearHalfspace v b)) := by
  have hab : a = b :=
    threshold_eq_of_stdGaussian_halfspace_mass_eq hu hv hmass
  rw [stdGaussian_closedExpansion_gaussianLinearHalfspace u a ε hu hε,
    stdGaussian_closedExpansion_gaussianLinearHalfspace v b ε hv hε, hab]

end HDP.Appendix
