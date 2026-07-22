import HighDimensionalProbability.Appendix.Infra.BrownianFiniteGrid
import HighDimensionalProbability.Appendix.Infra.BrownianGridError

/-!
# Brownian reflection endpoint

This audit-only appendix module isolates the reflection-principle ingredient
used in **Book Remark 7.2.1** (physical page 207, printed page 199).  The book
interprets an arbitrary expected supremum through finite subfamilies and
states

`E sup_{s ≤ t} B_s = sqrt (2t / pi)`.

The proof below combines a finite Gaussian-increment reflection argument with
layer cake.  Sorted grids control arbitrary queried finite families, while
uniform grids give the reverse bound because their expected largest increment
tends to zero.
-/

open MeasureTheory ProbabilityTheory Real Filter
open scoped ENNReal NNReal Topology

namespace HDP.Chapter7

noncomputable section

open BrownianDiscrete BrownianFiniteGrid

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- Once the maximum has the reflected endpoint law, its expectation reduces
to the exact first absolute Gaussian moment.

**Book Remark 7.2.1.** -/
theorem brownianMaximum_expectation_of_identDistrib_abs
    [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (t : ℝ≥0) {M : Ω → ℝ}
    (hreflect : IdentDistrib M (fun ω ↦ |B t ω|) P P) :
    (∫ ω, M ω ∂P) =
      Real.sqrt (t : ℝ) * (Real.sqrt 2 / Real.sqrt Real.pi) := by
  rw [hreflect.integral_eq]
  by_cases ht : t = 0
  · subst t
    simp only [NNReal.coe_zero, Real.sqrt_zero, zero_mul]
    apply integral_eq_zero_of_ae
    filter_upwards [hB.eval_zero_ae_eq_zero] with ω hω
    simp [hω]
  · have htpos : 0 < (t : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr ht)
    let z : Ω → ℝ := fun ω ↦ B t ω / Real.sqrt (t : ℝ)
    have hz : HasLaw z (gaussianReal 0 1) P := by
      have h := gaussianReal_div_const (hB.hasLaw_eval t) (Real.sqrt (t : ℝ))
      have hv : t / .mk (Real.sqrt (t : ℝ) ^ 2) (sq_nonneg _) = 1 := by
        ext
        simp [Real.sq_sqrt htpos.le, htpos.ne']
      rw [hv] at h
      simpa [z] using h
    have hzabs := HDP.Chapter2.gaussian_absolute_moment hz
      (p := (1 : ℝ)) (by norm_num)
    have hzabs' : (∫ ω, |z ω| ∂P) =
        Real.sqrt 2 / Real.sqrt Real.pi := by
      rw [show Real.sqrt 2 = (2 : ℝ) ^ (1 / 2 : ℝ) by
        rw [← Real.sqrt_eq_rpow]]
      simpa [Real.rpow_one, Real.Gamma_one] using hzabs
    have hBz : ∀ ω, |B t ω| = Real.sqrt (t : ℝ) * |z ω| := by
      intro ω
      dsimp [z]
      rw [abs_div, abs_of_pos (Real.sqrt_pos.2 htpos)]
      field_simp [Real.sqrt_ne_zero'.2 htpos]
    calc
      (∫ ω, |B t ω| ∂P) =
          ∫ ω, Real.sqrt (t : ℝ) * |z ω| ∂P := by
            apply integral_congr_ae
            exact ae_of_all _ hBz
      _ = Real.sqrt (t : ℝ) * ∫ ω, |z ω| ∂P := by
            rw [integral_const_mul]
      _ = Real.sqrt (t : ℝ) *
          (Real.sqrt 2 / Real.sqrt Real.pi) := by rw [hzabs']

/-- The conditional expected-maximum endpoint in the exact normalization
printed in the source.

**Book Remark 7.2.1.** -/
theorem brownianMaximum_expectation_of_reflection
    [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (t : ℝ≥0) {M : Ω → ℝ}
    (hreflect : IdentDistrib M (fun ω ↦ |B t ω|) P P) :
    (∫ ω, M ω ∂P) =
      Real.sqrt (2 * (t : ℝ) / Real.pi) := by
  rw [brownianMaximum_expectation_of_identDistrib_abs hB t hreflect]
  rw [Real.sqrt_div (by positivity : 0 ≤ 2 * (t : ℝ)) Real.pi]
  have hnum :
      Real.sqrt (2 * (t : ℝ)) =
        Real.sqrt (t : ℝ) * Real.sqrt 2 := by
    rw [show 2 * (t : ℝ) = (t : ℝ) * 2 by ring,
      Real.sqrt_mul (by positivity : 0 ≤ (t : ℝ))]
  rw [hnum]
  ring

/-- The reflection identity at the book's finite-subfamily
interface.  It identifies the extended expected supremum on `[0,t]` with the
first absolute moment of the endpoint.

**Book Remark 7.2.1.** -/
def BrownianReflectionPrinciple
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ) : Prop :=
  IsBrownianReal B P →
  ∀ t : ℝ≥0,
    extendedExpectedSupremum P
        (fun s : {s : ℝ≥0 // s ≤ t} ↦ B s.1) =
      ((∫ ω, |B t ω| ∂P) : ℝ)

/-- A supplied reflection identity gives the exact extended-valued
finite-subfamily expectation stated in the book.

**Book Remark 7.2.1.** -/
theorem brownianExtendedExpectedSupremum_of_reflection
    [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (t : ℝ≥0)
    (hreflect :
      extendedExpectedSupremum P
          (fun s : {s : ℝ≥0 // s ≤ t} ↦ B s.1) =
        ((∫ ω, |B t ω| ∂P) : ℝ)) :
    extendedExpectedSupremum P
        (fun s : {s : ℝ≥0 // s ≤ t} ↦ B s.1) =
      (Real.sqrt (2 * (t : ℝ) / Real.pi) : ℝ) := by
  rw [hreflect]
  norm_cast
  exact brownianMaximum_expectation_of_reflection hB.toIsPreBrownianReal t
    (IdentDistrib.refl
      (measurable_abs.comp_aemeasurable (hB.aemeasurable t)))

/-- A supplied universal reflection principle specializes to the exact
source-facing Brownian expected-supremum formula.

**Book Remark 7.2.1.** -/
theorem brownianExtendedExpectedSupremum_of_principle
    [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hreflection : BrownianReflectionPrinciple P B)
    (t : ℝ≥0) :
    extendedExpectedSupremum P
        (fun s : {s : ℝ≥0 // s ≤ t} ↦ B s.1) =
      (Real.sqrt (2 * (t : ℝ) / Real.pi) : ℝ) := by
  apply brownianExtendedExpectedSupremum_of_reflection hB t
  exact hreflection hB t

/-- Brownian reflection at the finite-subfamily expected-supremum interface.

On each finite grid, reflection after the first strict crossing preserves the
centered Gaussian increment product law.  Integrating the resulting tail
bounds gives an upper endpoint bound and a lower bound with twice the largest
increment as mesh error.  Sorted grids prove the upper bound for every finite
queried family; uniform grids and the Gaussian maximum estimate make the mesh
error vanish for the reverse bound. -/
theorem brownianReflectionPrinciple_external :
    ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ),
      BrownianReflectionPrinciple P B := by
  intro Ω _ P _ B hB t
  let target : ℝ := ∫ ω, |B t ω| ∂P
  have hupper :
      extendedExpectedSupremum P
          (fun s : {s : ℝ≥0 // s ≤ t} ↦ B s.1) ≤
        (target : EReal) := by
    unfold extendedExpectedSupremum
    apply iSup_le
    intro n
    apply iSup_le
    intro u
    have hint :=
      integrable_finiteMaximum_eval hB.toIsPreBrownianReal
        (fun i => (u i).1)
    rw [extendedExpectation_eq_integral hint]
    apply EReal.coe_le_coe_iff.mpr
    calc
      (∫ ω, HDP.Chapter5.finiteMaximum
          (fun i => B (u i).1) ω ∂P) ≤
          ∫ x, runningMax x
            ∂gaussianIncrementMeasure
              (incrementVariances (familyGridTime t u)) :=
        finiteFamily_integral_le_runningMax_product
          hB.toIsPreBrownianReal t u
      _ ≤ ∫ x, |endpoint x|
          ∂gaussianIncrementMeasure
            (incrementVariances (familyGridTime t u)) :=
        integral_runningMax_le_abs_endpoint _
      _ = target := by
        simpa [target] using
          integral_abs_familyEndpoint_eq hB.toIsPreBrownianReal t u
  let err : ℕ → ℝ := fun n =>
    ∫ x : Fin (n + 2) → ℝ, maxAbsStep x
      ∂gaussianIncrementMeasure
        (fun _ : Fin (n + 2) => t / (n + 2))
  have herr : Tendsto err atTop (𝓝 0) := by
    simpa [err, maxAbsStep, gaussianIncrementMeasure] using
      BrownianGridError.tendsto_integral_uniformGaussianMax t
  have hgridBound : ∀ n : ℕ,
      ((target - 2 * err n : ℝ) : EReal) ≤
        extendedExpectedSupremum P
          (fun s : {s : ℝ≥0 // s ≤ t} ↦ B s.1) := by
    intro n
    let G : Ω → ℝ := fun ω =>
      HDP.Chapter5.finiteMaximum
        (fun k : Fin (n + 3) => B (uniformGridTime t n k)) ω
    have hGint : Integrable G P := by
      simpa [G] using
        integrable_finiteMaximum_eval hB.toIsPreBrownianReal
          (uniformGridTime t n)
    have hmaxId :=
      uniformGridMaximum_identDistrib_runningMax
        hB.toIsPreBrownianReal t n
    have hendId :=
      evalLast_identDistrib_endpoint hB.toIsPreBrownianReal
        (uniformGridTime t n) (monotone_uniformGridTime t n)
        (uniformGridTime_zero t n)
    have habs :
        (∫ x, |endpoint x|
            ∂gaussianIncrementMeasure
              (fun _ : Fin (n + 2) => t / (n + 2))) =
          target := by
      have hc := (hendId.comp measurable_abs).integral_eq.symm
      simpa [uniformGrid_incrementVariances, uniformGridTime_last,
        target] using hc
    have hreal : target - 2 * err n ≤ ∫ ω, G ω ∂P := by
      calc
        target - 2 * err n =
            (∫ x, |endpoint x|
              ∂gaussianIncrementMeasure
                (fun _ : Fin (n + 2) => t / (n + 2))) -
              2 * ∫ x, maxAbsStep x
                ∂gaussianIncrementMeasure
                  (fun _ : Fin (n + 2) => t / (n + 2)) := by
            rw [habs]
        _ ≤ ∫ x, runningMax x
            ∂gaussianIncrementMeasure
              (fun _ : Fin (n + 2) => t / (n + 2)) :=
          integral_abs_endpoint_sub_two_maxAbsStep_le_runningMax _
        _ = ∫ ω, G ω ∂P := by
          simpa [G] using hmaxId.integral_eq.symm
    have hGle :
        ((∫ ω, G ω ∂P : ℝ) : EReal) ≤
          extendedExpectedSupremum P
            (fun s : {s : ℝ≥0 // s ≤ t} ↦ B s.1) := by
      calc
        ((∫ ω, G ω ∂P : ℝ) : EReal) =
            extendedExpectation P G :=
          (extendedExpectation_eq_integral hGint).symm
        _ ≤ extendedExpectedSupremum P
            (fun s : {s : ℝ≥0 // s ≤ t} ↦ B s.1) := by
          unfold extendedExpectedSupremum
          apply le_iSup_of_le (n + 2)
          apply le_iSup_of_le (uniformGridPoint t n)
          exact le_rfl
    exact (EReal.coe_le_coe_iff.mpr hreal).trans hGle
  have hlim :
      Tendsto (fun n => target - 2 * err n) atTop (𝓝 target) := by
    simpa using tendsto_const_nhds.sub (herr.const_mul 2)
  have hlower :
      (target : EReal) ≤
        extendedExpectedSupremum P
          (fun s : {s : ℝ≥0 // s ≤ t} ↦ B s.1) :=
    le_of_tendsto' (EReal.tendsto_coe.mpr hlim) hgridBound
  exact le_antisymm hupper hlower

end

end HDP.Chapter7
