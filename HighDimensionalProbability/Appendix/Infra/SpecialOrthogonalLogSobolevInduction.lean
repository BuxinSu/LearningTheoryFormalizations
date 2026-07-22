import HighDimensionalProbability.Appendix.Infra.SphereGaussianLogSobolev
import HighDimensionalProbability.Appendix.Infra.HaarEntropy
import HighDimensionalProbability.Appendix.Infra.SpecialOrthogonalSubgroup
import HighDimensionalProbability.Appendix.Infra.SpecialOrthogonalSphere
import HighDimensionalProbability.Appendix.Infra.SpecialOrthogonalAveraging
import HighDimensionalProbability.Appendix.Infra.Herbst

/-!
# Averaged stabilizer induction for logarithmic Sobolev inequalities on `SO(n)`

This file isolates the exact entropy-and-energy induction step behind the
coordinate-stabilizer proof of concentration on the special orthogonal group.
The analytic inputs are a logarithmic Sobolev estimate on every stabilizer
fiber and a spherical quotient estimate.  The conclusion has the coefficient
needed by the abstract Herbst theorem.
-/

open Matrix MeasureTheory ProbabilityTheory Real
open scoped BigOperators RealInnerProductSpace Topology

namespace HDP.Appendix.SpecialOrthogonal

noncomputable section

local instance matrixFirstCountableTopology (n : ℕ) :
    FirstCountableTopology
      (Matrix (Fin n) (Fin n) ℝ) :=
  inferInstanceAs
    (FirstCountableTopology (Fin n → Fin n → ℝ))

local instance matrixSecondCountableTopology (n : ℕ) :
    SecondCountableTopology
      (Matrix (Fin n) (Fin n) ℝ) :=
  inferInstanceAs
    (SecondCountableTopology (Fin n → Fin n → ℝ))

local instance specialOrthogonalFirstCountableTopology (n : ℕ) :
    FirstCountableTopology
      (Matrix.specialOrthogonalGroup (Fin n) ℝ) :=
  TopologicalSpace.firstCountableTopology_induced
    (Matrix.specialOrthogonalGroup (Fin n) ℝ)
    (Matrix (Fin n) (Fin n) ℝ) Subtype.val

local instance specialOrthogonalSecondCountableTopology (n : ℕ) :
    SecondCountableTopology
      (Matrix.specialOrthogonalGroup (Fin n) ℝ) :=
  TopologicalSpace.secondCountableTopology_induced
    (Matrix.specialOrthogonalGroup (Fin n) ℝ)
    (Matrix (Fin n) (Fin n) ℝ) Subtype.val

/-- Right averaging by a coordinate stabilizer preserves continuity. -/
lemma continuous_rightAverage_coordinateStabilizer
    {n : ℕ} (i : Fin (n + 1))
    {f : Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ → ℝ}
    (hf : Continuous f) :
    Continuous (rightAverage (coordinateStabilizerMeasure i) f) := by
  unfold rightAverage
  have hjoint :
      Continuous
        (Function.uncurry
          (fun x h :
              Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ =>
            f (x * h))) := by
    fun_prop
  simpa using
    (continuous_parametric_integral_of_continuous
      (μ := coordinateStabilizerMeasure i)
      hjoint (s := Set.univ) isCompact_univ)

/-- Entropy with respect to the embedded stabilizer Haar measure is exactly
entropy on the lower-dimensional special orthogonal group. -/
lemma boltzmannEntropy_coordinateStabilizerMeasure_of_continuous
    {n : ℕ} (i : Fin (n + 1))
    (f : Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ → ℝ)
    (hf : Continuous f) :
    boltzmannEntropy (coordinateStabilizerMeasure i) f =
      boltzmannEntropy
        (HDP.Chapter5.specialOrthogonalHaarMeasure n)
        (fun V => f (coordinateStabilizerHom i V)) := by
  unfold boltzmannEntropy
  rw [integral_coordinateStabilizerMeasure_of_continuous i
      (fun U => f U * Real.log (f U)) hf.mul_log,
    integral_coordinateStabilizerMeasure_of_continuous i f hf]

/-- Fiber entropy written on the canonical copy of `SO(n)`.  This is the
measure-theoretic bridge needed to apply the inductive logarithmic-Sobolev
hypothesis on each stabilizer fiber. -/
lemma boltzmannEntropy_coordinateStabilizer_sq_mul
    {n : ℕ} (i : Fin (n + 1))
    (U : Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ)
    (g : Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ → ℝ)
    (hg : Continuous g) :
    boltzmannEntropy (coordinateStabilizerMeasure i)
        (fun V => g (U * V) ^ 2) =
      boltzmannEntropy
        (HDP.Chapter5.specialOrthogonalHaarMeasure n)
        (fun V => g (U * coordinateStabilizerHom i V) ^ 2) := by
  apply boltzmannEntropy_coordinateStabilizerMeasure_of_continuous
  fun_prop

/-- The entropy of a continuous function restricted to a moving stabilizer
coset depends continuously on the base point. -/
lemma continuous_fiberBoltzmannEntropy_coordinateStabilizer
    {n : ℕ} (i : Fin (n + 1))
    (g : Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ → ℝ)
    (hg : Continuous g) :
    Continuous
      (fun U =>
        boltzmannEntropy (coordinateStabilizerMeasure i)
          (fun V => g (U * V) ^ 2)) := by
  have hsq :
      Continuous
        (Function.uncurry
          (fun U V :
              Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ =>
            g (U * V) ^ 2)) := by
    fun_prop
  have hav :
      Continuous
        (fun U =>
          ∫ V, g (U * V) ^ 2
            ∂coordinateStabilizerMeasure i) := by
    simpa only [Measure.restrict_univ] using
      (continuous_parametric_integral_of_continuous
        (μ := coordinateStabilizerMeasure i)
        hsq (s := Set.univ) isCompact_univ)
  have havlog :
      Continuous
        (fun U =>
          ∫ V,
            g (U * V) ^ 2 * Real.log (g (U * V) ^ 2)
            ∂coordinateStabilizerMeasure i) := by
    simpa only [Measure.restrict_univ] using
      (continuous_parametric_integral_of_continuous
        (μ := coordinateStabilizerMeasure i)
        (f := fun U V =>
          g (U * V) ^ 2 * Real.log (g (U * V) ^ 2))
        hsq.mul_log (s := Set.univ) isCompact_univ)
  unfold boltzmannEntropy
  exact havlog.sub hav.mul_log

/-- Entropy is transported exactly by the second-column orbit map from Haar
`SO(n)` to uniform measure on the sphere. -/
lemma boltzmannEntropy_comp_specialOrthogonalSphereOrbit_second
    (n : ℕ) (hn : 2 ≤ n)
    (f : Metric.sphere
      (0 : EuclideanSpace ℝ (Fin n)) 1 → ℝ)
    (hf : Continuous f) :
    boltzmannEntropy
        (HDP.Chapter5.specialOrthogonalHaarMeasure n)
        (fun U =>
          f (specialOrthogonalSphereOrbit
            (coordinateSpherePoint (⟨1, hn⟩ : Fin n)) U)) =
      boltzmannEntropy
        (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))) f := by
  let orbit :=
    specialOrthogonalSphereOrbit
      (coordinateSpherePoint (⟨1, hn⟩ : Fin n))
  let μ := HDP.Chapter5.specialOrthogonalHaarMeasure n
  let σ := HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n))
  have horbit : Continuous orbit := by
    simpa [orbit] using
      continuous_specialOrthogonalSphereOrbit
        (coordinateSpherePoint (⟨1, hn⟩ : Fin n))
  have hmap : Measure.map orbit μ = σ := by
    simpa [orbit, μ, σ] using
      map_specialOrthogonalSphereOrbit_second n hn
  have hint :
      (∫ U, f (orbit U) ∂μ) = ∫ u, f u ∂σ := by
    calc
      (∫ U, f (orbit U) ∂μ) =
          ∫ u, f u ∂Measure.map orbit μ :=
        (integral_map horbit.aemeasurable
          hf.aestronglyMeasurable).symm
      _ = ∫ u, f u ∂σ := by rw [hmap]
  have hintlog :
      (∫ U, f (orbit U) * Real.log (f (orbit U)) ∂μ) =
        ∫ u, f u * Real.log (f u) ∂σ := by
    calc
      (∫ U, f (orbit U) * Real.log (f (orbit U)) ∂μ) =
          ∫ u, f u * Real.log (f u)
            ∂Measure.map orbit μ :=
        (integral_map horbit.aemeasurable
          hf.mul_log.aestronglyMeasurable).symm
      _ = ∫ u, f u * Real.log (f u) ∂σ := by rw [hmap]
  unfold boltzmannEntropy
  rw [hintlog, hint]

/-- Exact entropy decomposition of a continuous square along a coordinate
stabilizer.  Compactness discharges all integrability hypotheses in the
general Haar entropy chain rule. -/
theorem boltzmannEntropy_sq_eq_coordinateStabilizer
    {n : ℕ} (i : Fin (n + 1))
    (g : Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ → ℝ)
    (hg : Continuous g) :
    boltzmannEntropy
        (HDP.Chapter5.specialOrthogonalHaarMeasure (n + 1))
        (fun U => g U ^ 2) =
      boltzmannEntropy
          (HDP.Chapter5.specialOrthogonalHaarMeasure (n + 1))
          (rightAverage (coordinateStabilizerMeasure i)
            (fun U => g U ^ 2)) +
        ∫ U,
          boltzmannEntropy (coordinateStabilizerMeasure i)
            (fun V => g (U * V) ^ 2)
          ∂HDP.Chapter5.specialOrthogonalHaarMeasure (n + 1) := by
  let G :=
    Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ
  let μ : Measure G :=
    HDP.Chapter5.specialOrthogonalHaarMeasure (n + 1)
  let ν : Measure G := coordinateStabilizerMeasure i
  letI : Measure.IsMulRightInvariant μ :=
    probabilityHaarIsMulRightInvariant μ
  have hsq : Continuous (fun U : G => g U ^ 2) := hg.pow 2
  have hprod :
      Integrable
        (fun p : G × G => g (p.2 * p.1) ^ 2)
        (ν.prod μ) := by
    have hcont :
        Continuous (fun p : G × G => g (p.2 * p.1) ^ 2) := by
      fun_prop
    simpa using
      hcont.continuousOn.integrableOn_compact
        (μ := ν.prod μ) isCompact_univ
  have hprodlog :
      Integrable
        (fun p : G × G =>
          g (p.2 * p.1) ^ 2 *
            Real.log (g (p.2 * p.1) ^ 2))
        (ν.prod μ) := by
    have hcont :
        Continuous (fun p : G × G => g (p.2 * p.1) ^ 2) := by
      fun_prop
    simpa using
      hcont.mul_log.continuousOn.integrableOn_compact
        (μ := ν.prod μ) isCompact_univ
  have havcont :
      Continuous
        (rightAverage ν (fun U : G => g U ^ 2)) := by
    simpa [ν, G] using
      continuous_rightAverage_coordinateStabilizer i hsq
  have havlog :
      Integrable
        (fun U : G =>
          rightAverage ν (fun W : G => g W ^ 2) U *
            Real.log
              (rightAverage ν (fun W : G => g W ^ 2) U))
        μ := by
    simpa using
      havcont.mul_log.continuousOn.integrableOn_compact
        (μ := μ) isCompact_univ
  simpa [G, μ, ν] using
    boltzmannEntropy_eq_rightAverage
      μ ν (fun U : G => g U ^ 2)
      hsq.measurable hprod hprodlog havlog

/-- Total squared Frobenius energy of a matrix-valued tangent field. -/
def tangentFieldSquareEnergy
    {n : ℕ}
    (X : Matrix.specialOrthogonalGroup (Fin n) ℝ →
      Matrix (Fin n) (Fin n) ℝ)
    (U : Matrix.specialOrthogonalGroup (Fin n) ℝ) : ℝ :=
  HDP.matrixFrobeniusNorm (X U) ^ 2

/-- Horizontal energy of a tangent field for the stabilizer fixing
coordinate `i`. -/
def tangentFieldHorizontalEnergy
    {n : ℕ}
    (X : Matrix.specialOrthogonalGroup (Fin n) ℝ →
      Matrix (Fin n) (Fin n) ℝ)
    (i : Fin n)
    (U : Matrix.specialOrthogonalGroup (Fin n) ℝ) : ℝ :=
  horizontalSquareEnergy (X U) i

/-- Vertical energy of a tangent field for the stabilizer fixing
coordinate `i`. -/
def tangentFieldVerticalEnergy
    {n : ℕ}
    (X : Matrix.specialOrthogonalGroup (Fin n) ℝ →
      Matrix (Fin n) (Fin n) ℝ)
    (i : Fin n)
    (U : Matrix.specialOrthogonalGroup (Fin n) ℝ) : ℝ :=
  verticalSquareEnergy (X U) i

/-- The second coordinate in ambient dimension `k + 3`, used by the
currently available special-orthogonal orbit law. -/
def secondCoordinateIndex (k : ℕ) : Fin (k + 3) :=
  ⟨1, by omega⟩

/-- Exact spherical quotient estimate for the second coordinate.

The two geometric inputs are stated explicitly:

* a globally bounded `C¹` ambient representative whose square is the
  stabilizer average along every orbit;
* comparison of its spherical tangent energy with the ambient horizontal
  matrix energy.

These are precisely the descent and differential estimates still required
to turn the abstract quotient into an application of the spherical
logarithmic-Sobolev theorem. -/
theorem secondCoordinate_quotient_entropy_le_of_sphere_logSobolev
    (k : ℕ)
    (g : Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ → ℝ)
    (X : Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ →
      Matrix (Fin (k + 3)) (Fin (k + 3)) ℝ)
    (H : EuclideanSpace ℝ (Fin (k + 3)) → ℝ)
    (hH_diff : Differentiable ℝ H)
    (hH_grad_cont : Continuous (fun y => fderiv ℝ H y))
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hH_bound : ∀ y, ‖H y‖ ≤ C)
    (hH_grad_bound : ∀ y, ‖fderiv ℝ H y‖ ≤ D)
    (hRepresentative :
      ∀ U,
        rightAverage
            (coordinateStabilizerMeasure
              (secondCoordinateIndex k))
            (fun W => g W ^ 2) U =
          H (specialOrthogonalSphereOrbit
            (coordinateSpherePoint
              (secondCoordinateIndex k)) U) ^ 2)
    (hEnergyComparison :
      (∫ u : Metric.sphere
            (0 : EuclideanSpace ℝ (Fin (k + 3))) 1,
          sphereTangentEnergy H u
            ∂HDP.unitSphereMeasure
              (EuclideanSpace ℝ (Fin (k + 3)))) ≤
        ∫ U,
          tangentFieldHorizontalEnergy X
            (secondCoordinateIndex k) U
          ∂HDP.Chapter5.specialOrthogonalHaarMeasure (k + 3)) :
    boltzmannEntropy
        (HDP.Chapter5.specialOrthogonalHaarMeasure (k + 3))
        (rightAverage
          (coordinateStabilizerMeasure (secondCoordinateIndex k))
          (fun W => g W ^ 2)) ≤
      2 * (
        (((k + 1 : ℕ) : ℝ))⁻¹ *
          ∫ U,
            tangentFieldHorizontalEnergy X
              (secondCoordinateIndex k) U
            ∂HDP.Chapter5.specialOrthogonalHaarMeasure (k + 3)) := by
  let orbit :=
    specialOrthogonalSphereOrbit
      (coordinateSpherePoint (secondCoordinateIndex k))
  have haverage :
      rightAverage
          (coordinateStabilizerMeasure (secondCoordinateIndex k))
          (fun W => g W ^ 2) =
        fun U => H (orbit U) ^ 2 := by
    funext U
    exact hRepresentative U
  rw [haverage]
  calc
    boltzmannEntropy
        (HDP.Chapter5.specialOrthogonalHaarMeasure (k + 3))
        (fun U => H (orbit U) ^ 2) =
      boltzmannEntropy
        (HDP.unitSphereMeasure
          (EuclideanSpace ℝ (Fin (k + 3))))
        (fun u => H u ^ 2) := by
          simpa [orbit, secondCoordinateIndex] using
            boltzmannEntropy_comp_specialOrthogonalSphereOrbit_second
              (k + 3) (by omega)
              (fun u : Metric.sphere
                (0 : EuclideanSpace ℝ (Fin (k + 3))) 1 =>
                  H u ^ 2)
              ((hH_diff.continuous.comp continuous_subtype_val).pow 2)
    _ ≤
        2 * (
          (((k + 1 : ℕ) : ℝ))⁻¹ *
            ∫ u : Metric.sphere
                (0 : EuclideanSpace ℝ (Fin (k + 3))) 1,
              sphereTangentEnergy H u
                ∂HDP.unitSphereMeasure
                  (EuclideanSpace ℝ (Fin (k + 3)))) :=
      sphere_logSobolev_bounded_C1
        k H hH_diff hH_grad_cont hC hD
        hH_bound hH_grad_bound
    _ ≤
        2 * (
          (((k + 1 : ℕ) : ℝ))⁻¹ *
            ∫ U,
              tangentFieldHorizontalEnergy X
                (secondCoordinateIndex k) U
              ∂HDP.Chapter5.specialOrthogonalHaarMeasure (k + 3)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hEnergyComparison
          (inv_nonneg.mpr (by positivity)))
        (by norm_num)

/-- Dimension-uniform version of the second-coordinate quotient estimate.
The Gaussian-radial constant satisfies `1 / (k + 1) ≤ 3 / (k + 3)`, so this
is the form that closes the averaged group induction with `a = 6`. -/
theorem secondCoordinate_quotient_entropy_le_three
    (k : ℕ)
    (g : Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ → ℝ)
    (X : Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ →
      Matrix (Fin (k + 3)) (Fin (k + 3)) ℝ)
    (H : EuclideanSpace ℝ (Fin (k + 3)) → ℝ)
    (hH_diff : Differentiable ℝ H)
    (hH_grad_cont : Continuous (fun y => fderiv ℝ H y))
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hH_bound : ∀ y, ‖H y‖ ≤ C)
    (hH_grad_bound : ∀ y, ‖fderiv ℝ H y‖ ≤ D)
    (hRepresentative :
      ∀ U,
        rightAverage
            (coordinateStabilizerMeasure
              (secondCoordinateIndex k))
            (fun W => g W ^ 2) U =
          H (specialOrthogonalSphereOrbit
            (coordinateSpherePoint
              (secondCoordinateIndex k)) U) ^ 2)
    (hEnergyComparison :
      (∫ u : Metric.sphere
            (0 : EuclideanSpace ℝ (Fin (k + 3))) 1,
          sphereTangentEnergy H u
            ∂HDP.unitSphereMeasure
              (EuclideanSpace ℝ (Fin (k + 3)))) ≤
        ∫ U,
          tangentFieldHorizontalEnergy X
            (secondCoordinateIndex k) U
          ∂HDP.Chapter5.specialOrthogonalHaarMeasure (k + 3)) :
    boltzmannEntropy
        (HDP.Chapter5.specialOrthogonalHaarMeasure (k + 3))
        (rightAverage
          (coordinateStabilizerMeasure (secondCoordinateIndex k))
          (fun W => g W ^ 2)) ≤
      2 * (3 / (((k + 3 : ℕ) : ℝ))) *
        ∫ U,
          tangentFieldHorizontalEnergy X
            (secondCoordinateIndex k) U
          ∂HDP.Chapter5.specialOrthogonalHaarMeasure (k + 3) := by
  have hbase :=
    secondCoordinate_quotient_entropy_le_of_sphere_logSobolev
      k g X H hH_diff hH_grad_cont hC hD
      hH_bound hH_grad_bound hRepresentative hEnergyComparison
  have hk1 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hk3 : (0 : ℝ) < ((k + 3 : ℕ) : ℝ) := by positivity
  have hcoefficient :
      (((k + 1 : ℕ) : ℝ))⁻¹ ≤
        3 / (((k + 3 : ℕ) : ℝ)) := by
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
    rw [inv_eq_one_div]
    apply (div_le_div_iff₀ hk1 hk3).2
    norm_num [Nat.cast_add, Nat.cast_one]
    nlinarith
  have hEnergyNonneg :
      0 ≤
        ∫ U,
          tangentFieldHorizontalEnergy X
            (secondCoordinateIndex k) U
          ∂HDP.Chapter5.specialOrthogonalHaarMeasure (k + 3) := by
    apply integral_nonneg
    intro U
    unfold tangentFieldHorizontalEnergy horizontalSquareEnergy
      rowSquareEnergy
    positivity
  calc
    boltzmannEntropy
        (HDP.Chapter5.specialOrthogonalHaarMeasure (k + 3))
        (rightAverage
          (coordinateStabilizerMeasure (secondCoordinateIndex k))
          (fun W => g W ^ 2)) ≤
      2 * (
        (((k + 1 : ℕ) : ℝ))⁻¹ *
          ∫ U,
            tangentFieldHorizontalEnergy X
              (secondCoordinateIndex k) U
            ∂HDP.Chapter5.specialOrthogonalHaarMeasure (k + 3)) :=
      hbase
    _ ≤
      2 * (
        (3 / (((k + 3 : ℕ) : ℝ))) *
          ∫ U,
            tangentFieldHorizontalEnergy X
              (secondCoordinateIndex k) U
            ∂HDP.Chapter5.specialOrthogonalHaarMeasure (k + 3)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hcoefficient hEnergyNonneg)
        (by norm_num)
    _ =
      2 * (3 / (((k + 3 : ℕ) : ℝ))) *
        ∫ U,
          tangentFieldHorizontalEnergy X
            (secondCoordinateIndex k) U
          ∂HDP.Chapter5.specialOrthogonalHaarMeasure (k + 3) := by
      ring

lemma continuous_tangentFieldSquareEnergy
    {n : ℕ}
    {X : Matrix.specialOrthogonalGroup (Fin n) ℝ →
      Matrix (Fin n) (Fin n) ℝ}
    (hX : Continuous X) :
    Continuous (tangentFieldSquareEnergy X) := by
  unfold tangentFieldSquareEnergy HDP.matrixFrobeniusNorm
  fun_prop

lemma continuous_tangentFieldHorizontalEnergy
    {n : ℕ}
    {X : Matrix.specialOrthogonalGroup (Fin n) ℝ →
      Matrix (Fin n) (Fin n) ℝ}
    (hX : Continuous X) (i : Fin n) :
    Continuous (tangentFieldHorizontalEnergy X i) := by
  unfold tangentFieldHorizontalEnergy horizontalSquareEnergy
    rowSquareEnergy
  fun_prop

lemma continuous_tangentFieldVerticalEnergy
    {n : ℕ}
    {X : Matrix.specialOrthogonalGroup (Fin n) ℝ →
      Matrix (Fin n) (Fin n) ℝ}
    (hX : Continuous X) (i : Fin n) :
    Continuous (tangentFieldVerticalEnergy X i) := by
  unfold tangentFieldVerticalEnergy verticalSquareEnergy
  exact (continuous_tangentFieldSquareEnergy hX).sub
    (continuous_tangentFieldHorizontalEnergy hX i)

lemma integrable_tangentFieldSquareEnergy
    {n : ℕ}
    {X : Matrix.specialOrthogonalGroup (Fin n) ℝ →
      Matrix (Fin n) (Fin n) ℝ}
    (hX : Continuous X) :
    Integrable (tangentFieldSquareEnergy X)
      (HDP.Chapter5.specialOrthogonalHaarMeasure n) := by
  simpa using
    (continuous_tangentFieldSquareEnergy hX).continuousOn
      |>.integrableOn_compact
        (μ := HDP.Chapter5.specialOrthogonalHaarMeasure n)
        isCompact_univ

lemma integrable_tangentFieldHorizontalEnergy
    {n : ℕ}
    {X : Matrix.specialOrthogonalGroup (Fin n) ℝ →
      Matrix (Fin n) (Fin n) ℝ}
    (hX : Continuous X) (i : Fin n) :
    Integrable (tangentFieldHorizontalEnergy X i)
      (HDP.Chapter5.specialOrthogonalHaarMeasure n) := by
  simpa using
    (continuous_tangentFieldHorizontalEnergy hX i).continuousOn
      |>.integrableOn_compact
        (μ := HDP.Chapter5.specialOrthogonalHaarMeasure n)
        isCompact_univ

lemma integrable_tangentFieldVerticalEnergy
    {n : ℕ}
    {X : Matrix.specialOrthogonalGroup (Fin n) ℝ →
      Matrix (Fin n) (Fin n) ℝ}
    (hX : Continuous X) (i : Fin n) :
    Integrable (tangentFieldVerticalEnergy X i)
      (HDP.Chapter5.specialOrthogonalHaarMeasure n) := by
  simpa using
    (continuous_tangentFieldVerticalEnergy hX i).continuousOn
      |>.integrableOn_compact
        (μ := HDP.Chapter5.specialOrthogonalHaarMeasure n)
        isCompact_univ

/-- The lower-dimensional logarithmic-Sobolev inequality supplies the fiber
premise of the stabilizer induction once the embedded-fiber Dirichlet energy
is controlled by the ambient vertical energy.

The continuity theorem above makes the fiber entropy automatically
integrable.  Thus the only analytic hypothesis retained here is integrability
of the lower-dimensional energy before its comparison with the vertical
energy. -/
theorem integrated_fiber_entropy_le_of_logSobolev
    (n : ℕ) (hn : 1 ≤ n)
    (g : Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ → ℝ)
    (hg : Continuous g)
    (X : Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (lowerAdmissible :
      (Matrix.specialOrthogonalGroup (Fin n) ℝ → ℝ) → Prop)
    (lowerEnergy :
      (Matrix.specialOrthogonalGroup (Fin n) ℝ → ℝ) →
        Matrix.specialOrthogonalGroup (Fin n) ℝ → ℝ)
    {a : ℝ} (ha : 0 ≤ a)
    (hLowerLSI :
      HasLogSobolevInequality
        (HDP.Chapter5.specialOrthogonalHaarMeasure n)
        lowerAdmissible lowerEnergy (a / (n : ℝ)))
    (hFiberAdmissible :
      ∀ i : Fin (n + 1),
        ∀ U : Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ,
          lowerAdmissible
            (fun V => g (U * coordinateStabilizerHom i V)))
    (hLowerEnergyIntegrable :
      ∀ i : Fin (n + 1),
        Integrable
          (fun U =>
            ∫ V,
              lowerEnergy
                (fun W =>
                  g (U * coordinateStabilizerHom i W)) V
              ∂HDP.Chapter5.specialOrthogonalHaarMeasure n)
          (HDP.Chapter5.specialOrthogonalHaarMeasure (n + 1)))
    (hEnergyComparison :
      ∀ i : Fin (n + 1),
        (∫ U,
            ∫ V,
              lowerEnergy
                (fun W =>
                  g (U * coordinateStabilizerHom i W)) V
              ∂HDP.Chapter5.specialOrthogonalHaarMeasure n
            ∂HDP.Chapter5.specialOrthogonalHaarMeasure (n + 1)) ≤
          ∫ U, tangentFieldVerticalEnergy X i U
            ∂HDP.Chapter5.specialOrthogonalHaarMeasure (n + 1)) :
    ∀ i : Fin (n + 1),
      (∫ U,
          boltzmannEntropy (coordinateStabilizerMeasure i)
            (fun V => g (U * V) ^ 2)
          ∂HDP.Chapter5.specialOrthogonalHaarMeasure (n + 1)) ≤
        2 * (a / (n : ℝ)) *
          ∫ U, tangentFieldVerticalEnergy X i U
            ∂HDP.Chapter5.specialOrthogonalHaarMeasure (n + 1) := by
  intro i
  let μ :=
    HDP.Chapter5.specialOrthogonalHaarMeasure (n + 1)
  have hEntropyIntegrable :
      Integrable
        (fun U =>
          boltzmannEntropy (coordinateStabilizerMeasure i)
            (fun V => g (U * V) ^ 2)) μ := by
    simpa [μ] using
      (continuous_fiberBoltzmannEntropy_coordinateStabilizer i g hg)
        |>.continuousOn.integrableOn_compact
          (μ := μ) isCompact_univ
  have hPointwise :
      ∀ U,
        boltzmannEntropy (coordinateStabilizerMeasure i)
            (fun V => g (U * V) ^ 2) ≤
          2 * (a / (n : ℝ)) *
            ∫ V,
              lowerEnergy
                (fun W =>
                  g (U * coordinateStabilizerHom i W)) V
              ∂HDP.Chapter5.specialOrthogonalHaarMeasure n := by
    intro U
    rw [boltzmannEntropy_coordinateStabilizer_sq_mul i U g hg]
    exact hLowerLSI _ (hFiberAdmissible i U)
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hcoefficient : 0 ≤ 2 * (a / (n : ℝ)) :=
    mul_nonneg (by norm_num) (div_nonneg ha hnpos.le)
  have hEnergyIntegrable :
      Integrable
        (fun U =>
          ∫ V,
            lowerEnergy
              (fun W =>
                g (U * coordinateStabilizerHom i W)) V
            ∂HDP.Chapter5.specialOrthogonalHaarMeasure n) μ := by
    simpa [μ] using hLowerEnergyIntegrable i
  calc
    (∫ U,
        boltzmannEntropy (coordinateStabilizerMeasure i)
          (fun V => g (U * V) ^ 2) ∂μ) ≤
        ∫ U,
          2 * (a / (n : ℝ)) *
            (∫ V,
              lowerEnergy
                (fun W =>
                  g (U * coordinateStabilizerHom i W)) V
              ∂HDP.Chapter5.specialOrthogonalHaarMeasure n) ∂μ := by
      exact integral_mono hEntropyIntegrable
        (hEnergyIntegrable.const_mul _)
        hPointwise
    _ =
        2 * (a / (n : ℝ)) *
          ∫ U,
            ∫ V,
              lowerEnergy
                (fun W =>
                  g (U * coordinateStabilizerHom i W)) V
              ∂HDP.Chapter5.specialOrthogonalHaarMeasure n ∂μ := by
      exact integral_const_mul _ _
    _ ≤
        2 * (a / (n : ℝ)) *
          ∫ U, tangentFieldVerticalEnergy X i U ∂μ := by
      exact mul_le_mul_of_nonneg_left
        (by simpa [μ] using hEnergyComparison i) hcoefficient

lemma sum_tangentFieldHorizontalEnergy
    {n : ℕ}
    (X : Matrix.specialOrthogonalGroup (Fin n) ℝ →
      Matrix (Fin n) (Fin n) ℝ)
    (U : Matrix.specialOrthogonalGroup (Fin n) ℝ) :
    ∑ i : Fin n, tangentFieldHorizontalEnergy X i U =
      2 * tangentFieldSquareEnergy X U := by
  exact sum_horizontalSquareEnergy (X U)

lemma sum_tangentFieldVerticalEnergy
    {n : ℕ}
    (X : Matrix.specialOrthogonalGroup (Fin n) ℝ →
      Matrix (Fin n) (Fin n) ℝ)
    (U : Matrix.specialOrthogonalGroup (Fin n) ℝ) :
    ∑ i : Fin n, tangentFieldVerticalEnergy X i U =
      ((n : ℝ) - 2) * tangentFieldSquareEnergy X U := by
  exact sum_verticalSquareEnergy (X U)

lemma sum_integral_tangentFieldHorizontalEnergy
    {n : ℕ}
    {X : Matrix.specialOrthogonalGroup (Fin n) ℝ →
      Matrix (Fin n) (Fin n) ℝ}
    (hX : Continuous X) :
    ∑ i : Fin n,
        ∫ U, tangentFieldHorizontalEnergy X i U
          ∂HDP.Chapter5.specialOrthogonalHaarMeasure n =
      2 * ∫ U, tangentFieldSquareEnergy X U
        ∂HDP.Chapter5.specialOrthogonalHaarMeasure n := by
  rw [← integral_finsetSum Finset.univ
    (fun i _ => integrable_tangentFieldHorizontalEnergy hX i)]
  simp_rw [sum_tangentFieldHorizontalEnergy X]
  exact integral_const_mul 2 _

lemma sum_integral_tangentFieldVerticalEnergy
    {n : ℕ}
    {X : Matrix.specialOrthogonalGroup (Fin n) ℝ →
      Matrix (Fin n) (Fin n) ℝ}
    (hX : Continuous X) :
    ∑ i : Fin n,
        ∫ U, tangentFieldVerticalEnergy X i U
          ∂HDP.Chapter5.specialOrthogonalHaarMeasure n =
      ((n : ℝ) - 2) *
        ∫ U, tangentFieldSquareEnergy X U
          ∂HDP.Chapter5.specialOrthogonalHaarMeasure n := by
  rw [← integral_finsetSum Finset.univ
    (fun i _ => integrable_tangentFieldVerticalEnergy hX i)]
  simp_rw [sum_tangentFieldVerticalEnergy X]
  exact integral_const_mul ((n : ℝ) - 2) _

/-- Pure scalar form of the averaged-stabilizer induction.  It is separated
from the Haar argument so that the exact coefficient bookkeeping is reusable
for any tangent-field realization. -/
lemma averaged_stabilizer_entropy_le
    {n : ℕ} (hn : 2 ≤ n)
    {Q E a b : ℝ} (hE : 0 ≤ E)
    (ha : 0 ≤ a) (hab : 2 * b ≤ a)
    (H V : Fin n → ℝ)
    (hH : ∑ i, H i = 2 * E)
    (hV : ∑ i, V i = ((n : ℝ) - 2) * E)
    (hlocal :
      ∀ i,
        Q ≤ 2 * ((b / (n : ℝ)) * H i +
            (a / ((n : ℝ) - 1)) * V i)) :
    Q ≤ 2 * (a / (n : ℝ)) * E := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by positivity
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hsum :
      ∑ _i : Fin n, Q ≤
        ∑ i : Fin n,
          2 * (
            (b / (n : ℝ)) * H i +
              (a / ((n : ℝ) - 1)) * V i) :=
    Finset.sum_le_sum fun i _ => hlocal i
  have hsum' :
      (n : ℝ) * Q ≤
        2 * (
          (b / (n : ℝ)) * (2 * E) +
            (a / ((n : ℝ) - 1)) *
              (((n : ℝ) - 2) * E)) := by
    calc
      (n : ℝ) * Q = ∑ _i : Fin n, Q := by simp
      _ ≤ ∑ i : Fin n,
          2 * (
            (b / (n : ℝ)) * H i +
              (a / ((n : ℝ) - 1)) * V i) := hsum
      _ = 2 * (
          (b / (n : ℝ)) * (∑ i, H i) +
            (a / ((n : ℝ) - 1)) * (∑ i, V i)) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum]
      _ = 2 * (
          (b / (n : ℝ)) * (2 * E) +
            (a / ((n : ℝ) - 1)) *
              (((n : ℝ) - 2) * E)) := by rw [hH, hV]
  have hcoefficient :=
    averaged_stabilizer_coefficient_le hn ha hab
  have hpre :
      Q ≤
        2 * (
          (a / ((n : ℝ) - 1)) *
              (((n : ℝ) - 2) / (n : ℝ)) +
            (b / (n : ℝ)) * (2 / (n : ℝ))) * E := by
    apply (mul_le_mul_iff_right₀ hn0).mp
    calc
      (n : ℝ) * Q ≤ 2 * (
          (b / (n : ℝ)) * (2 * E) +
            (a / ((n : ℝ) - 1)) *
              (((n : ℝ) - 2) * E)) := hsum'
      _ = (n : ℝ) * (2 * (
          (a / ((n : ℝ) - 1)) *
              (((n : ℝ) - 2) / (n : ℝ)) +
            (b / (n : ℝ)) * (2 / (n : ℝ))) * E) := by
        field_simp [hn0.ne', hn1.ne']
        ring
  calc
    Q ≤
        2 * (
          (a / ((n : ℝ) - 1)) *
              (((n : ℝ) - 2) / (n : ℝ)) +
            (b / (n : ℝ)) * (2 / (n : ℝ))) * E := hpre
    _ ≤ 2 * (a / (n : ℝ)) * E := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcoefficient (by norm_num))
        hE

/-- Exact one-function Haar logarithmic-Sobolev induction step.

The two analytic premises are precisely the estimates on the spherical
quotient and on the `SO(n)` stabilizer fibers.  Once they are supplied, the
averaged horizontal/vertical identities close the coefficient at
`a / (n + 1)` without harmonic loss. -/
theorem specialOrthogonal_logSobolev_induction_step
    (n : ℕ) (hn : 1 ≤ n)
    (g : Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ → ℝ)
    (hg : Continuous g)
    (X : Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hX : Continuous X)
    {a b : ℝ} (ha : 0 ≤ a) (hab : 2 * b ≤ a)
    (hQuotient :
      ∀ i : Fin (n + 1),
        boltzmannEntropy
            (HDP.Chapter5.specialOrthogonalHaarMeasure (n + 1))
            (rightAverage (coordinateStabilizerMeasure i)
              (fun U => g U ^ 2)) ≤
          2 * (b / ((n + 1 : ℕ) : ℝ)) *
            ∫ U, tangentFieldHorizontalEnergy X i U
              ∂HDP.Chapter5.specialOrthogonalHaarMeasure (n + 1))
    (hFiber :
      ∀ i : Fin (n + 1),
        (∫ U,
            boltzmannEntropy (coordinateStabilizerMeasure i)
              (fun V => g (U * V) ^ 2)
            ∂HDP.Chapter5.specialOrthogonalHaarMeasure (n + 1)) ≤
          2 * (a / (n : ℝ)) *
            ∫ U, tangentFieldVerticalEnergy X i U
              ∂HDP.Chapter5.specialOrthogonalHaarMeasure (n + 1)) :
    boltzmannEntropy
        (HDP.Chapter5.specialOrthogonalHaarMeasure (n + 1))
        (fun U => g U ^ 2) ≤
      2 * (a / ((n + 1 : ℕ) : ℝ)) *
        ∫ U, tangentFieldSquareEnergy X U
          ∂HDP.Chapter5.specialOrthogonalHaarMeasure (n + 1) := by
  let μ :=
    HDP.Chapter5.specialOrthogonalHaarMeasure (n + 1)
  let Q :=
    boltzmannEntropy μ (fun U => g U ^ 2)
  let E :=
    ∫ U, tangentFieldSquareEnergy X U ∂μ
  let H : Fin (n + 1) → ℝ :=
    fun i => ∫ U, tangentFieldHorizontalEnergy X i U ∂μ
  let V : Fin (n + 1) → ℝ :=
    fun i => ∫ U, tangentFieldVerticalEnergy X i U ∂μ
  have hE : 0 ≤ E := by
    apply integral_nonneg
    intro U
    exact sq_nonneg _
  have hHsum : ∑ i, H i = 2 * E := by
    simpa [H, E, μ] using
      sum_integral_tangentFieldHorizontalEnergy hX
  have hVsum :
      ∑ i, V i =
        (((n + 1 : ℕ) : ℝ) - 2) * E := by
    simpa [V, E, μ] using
      sum_integral_tangentFieldVerticalEnergy hX
  have hlocal :
      ∀ i : Fin (n + 1),
        Q ≤ 2 * (
          (b / ((n + 1 : ℕ) : ℝ)) * H i +
            (a / (((n + 1 : ℕ) : ℝ) - 1)) * V i) := by
    intro i
    rw [show Q =
        boltzmannEntropy μ
            (rightAverage (coordinateStabilizerMeasure i)
              (fun U => g U ^ 2)) +
          ∫ U,
            boltzmannEntropy (coordinateStabilizerMeasure i)
              (fun W => g (U * W) ^ 2) ∂μ by
      simpa [Q, μ] using
        boltzmannEntropy_sq_eq_coordinateStabilizer i g hg]
    calc
      boltzmannEntropy μ
            (rightAverage (coordinateStabilizerMeasure i)
              (fun U => g U ^ 2)) +
          ∫ U,
            boltzmannEntropy (coordinateStabilizerMeasure i)
              (fun W => g (U * W) ^ 2) ∂μ ≤
          2 * (b / ((n + 1 : ℕ) : ℝ)) * H i +
            2 * (a / (n : ℝ)) * V i := by
        exact add_le_add
          (by simpa [H, μ] using hQuotient i)
          (by simpa [V, μ] using hFiber i)
      _ = 2 * (
          (b / ((n + 1 : ℕ) : ℝ)) * H i +
            (a / (((n + 1 : ℕ) : ℝ) - 1)) * V i) := by
        norm_num [Nat.cast_add, Nat.cast_one]
        ring
  simpa [Q, E, μ] using
    averaged_stabilizer_entropy_le
      (n := n + 1) (by omega) hE ha hab H V hHsum hVsum hlocal

/-- Herbst-facing form of the averaged stabilizer induction.

This is the smallest abstract interface consumed by
`hasHerbstEntropyBound_of_logSobolev`: admissible functions only need a
continuous matrix-valued tangent field, together with the quotient and fiber
entropy estimates. -/
theorem hasLogSobolevInequality_specialOrthogonal_of_stabilizer_estimates
    (n : ℕ) (hn : 1 ≤ n)
    (admissible :
      (Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ → ℝ) → Prop)
    (gradient :
      (Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ → ℝ) →
        Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ →
          Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : 2 * b ≤ a)
    (hContinuous :
      ∀ g, admissible g → Continuous g)
    (hGradientContinuous :
      ∀ g, admissible g → Continuous (gradient g))
    (hQuotient :
      ∀ g, admissible g → ∀ i : Fin (n + 1),
        boltzmannEntropy
            (HDP.Chapter5.specialOrthogonalHaarMeasure (n + 1))
            (rightAverage (coordinateStabilizerMeasure i)
              (fun U => g U ^ 2)) ≤
          2 * (b / ((n + 1 : ℕ) : ℝ)) *
            ∫ U,
              tangentFieldHorizontalEnergy (gradient g) i U
              ∂HDP.Chapter5.specialOrthogonalHaarMeasure (n + 1))
    (hFiber :
      ∀ g, admissible g → ∀ i : Fin (n + 1),
        (∫ U,
            boltzmannEntropy (coordinateStabilizerMeasure i)
              (fun V => g (U * V) ^ 2)
            ∂HDP.Chapter5.specialOrthogonalHaarMeasure (n + 1)) ≤
          2 * (a / (n : ℝ)) *
            ∫ U,
              tangentFieldVerticalEnergy (gradient g) i U
              ∂HDP.Chapter5.specialOrthogonalHaarMeasure (n + 1)) :
    HasLogSobolevInequality
      (HDP.Chapter5.specialOrthogonalHaarMeasure (n + 1))
      admissible
      (fun g => tangentFieldSquareEnergy (gradient g))
      (a / ((n + 1 : ℕ) : ℝ)) := by
  intro g hg
  exact specialOrthogonal_logSobolev_induction_step
    n hn g (hContinuous g hg) (gradient g)
    (hGradientContinuous g hg) ha hab
    (hQuotient g hg) (hFiber g hg)

/-- Exact recursive Haar logarithmic-Sobolev induction.

Compared with `hasLogSobolevInequality_specialOrthogonal_of_stabilizer_estimates`,
the fiber premise is discharged here by an `SO(n)` logarithmic-Sobolev
inequality.  What remains exposed is precisely the differential-geometric
comparison between the lower-dimensional fiber energy and the ambient
vertical energy. -/
theorem hasLogSobolevInequality_specialOrthogonal_induction
    (n : ℕ) (hn : 1 ≤ n)
    (admissible :
      (Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ → ℝ) → Prop)
    (gradient :
      (Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ → ℝ) →
        Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ →
          Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (lowerAdmissible :
      (Matrix.specialOrthogonalGroup (Fin n) ℝ → ℝ) → Prop)
    (lowerEnergy :
      (Matrix.specialOrthogonalGroup (Fin n) ℝ → ℝ) →
        Matrix.specialOrthogonalGroup (Fin n) ℝ → ℝ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : 2 * b ≤ a)
    (hLowerLSI :
      HasLogSobolevInequality
        (HDP.Chapter5.specialOrthogonalHaarMeasure n)
        lowerAdmissible lowerEnergy (a / (n : ℝ)))
    (hContinuous :
      ∀ g, admissible g → Continuous g)
    (hGradientContinuous :
      ∀ g, admissible g → Continuous (gradient g))
    (hQuotient :
      ∀ g, admissible g → ∀ i : Fin (n + 1),
        boltzmannEntropy
            (HDP.Chapter5.specialOrthogonalHaarMeasure (n + 1))
            (rightAverage (coordinateStabilizerMeasure i)
              (fun U => g U ^ 2)) ≤
          2 * (b / ((n + 1 : ℕ) : ℝ)) *
            ∫ U,
              tangentFieldHorizontalEnergy (gradient g) i U
              ∂HDP.Chapter5.specialOrthogonalHaarMeasure (n + 1))
    (hFiberAdmissible :
      ∀ g, admissible g → ∀ i : Fin (n + 1),
        ∀ U : Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ,
          lowerAdmissible
            (fun V => g (U * coordinateStabilizerHom i V)))
    (hLowerEnergyIntegrable :
      ∀ g, admissible g → ∀ i : Fin (n + 1),
        Integrable
          (fun U =>
            ∫ V,
              lowerEnergy
                (fun W =>
                  g (U * coordinateStabilizerHom i W)) V
              ∂HDP.Chapter5.specialOrthogonalHaarMeasure n)
          (HDP.Chapter5.specialOrthogonalHaarMeasure (n + 1)))
    (hEnergyComparison :
      ∀ g, admissible g → ∀ i : Fin (n + 1),
        (∫ U,
            ∫ V,
              lowerEnergy
                (fun W =>
                  g (U * coordinateStabilizerHom i W)) V
              ∂HDP.Chapter5.specialOrthogonalHaarMeasure n
            ∂HDP.Chapter5.specialOrthogonalHaarMeasure (n + 1)) ≤
          ∫ U,
            tangentFieldVerticalEnergy (gradient g) i U
            ∂HDP.Chapter5.specialOrthogonalHaarMeasure (n + 1)) :
    HasLogSobolevInequality
      (HDP.Chapter5.specialOrthogonalHaarMeasure (n + 1))
      admissible
      (fun g => tangentFieldSquareEnergy (gradient g))
      (a / ((n + 1 : ℕ) : ℝ)) := by
  apply
    hasLogSobolevInequality_specialOrthogonal_of_stabilizer_estimates
      n hn admissible gradient ha hab hContinuous hGradientContinuous
      hQuotient
  intro g hg
  exact integrated_fiber_entropy_le_of_logSobolev
    n hn g (hContinuous g hg) (gradient g)
    lowerAdmissible lowerEnergy ha hLowerLSI
    (hFiberAdmissible g hg)
    (hLowerEnergyIntegrable g hg)
    (hEnergyComparison g hg)

end

end HDP.Appendix.SpecialOrthogonal
