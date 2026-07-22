import HighDimensionalProbability.Appendix.Infra.PoincareSphere
import HighDimensionalProbability.Appendix.Infra.SphericalCap
import HighDimensionalProbability.Chapter3_RandomVectorsInHighDimensions

/-!
# One-dimensional cap input for the Poincaré limit

The project already proves a uniform central limit theorem for every
one-dimensional spherical projection.  Here it is repackaged in exactly the
spherical-cap notation used by Appendix isoperimetry.
-/

open MeasureTheory ProbabilityTheory Set Metric InnerProductSpace Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace HDP.Appendix

/-- A unit vector regarded as a point of the unit sphere. -/
def unitSpherePoint {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (u : E) (hu : ‖u‖ = 1) :
    Metric.sphere (0 : E) 1 :=
  ⟨u, by simpa [mem_sphere_zero_iff_norm]⟩

/-- A spherical cap at threshold `t / √d` is the lower-CDF event for the
`√d`-scaled spherical projection. -/
theorem sphericalCap_eq_sphericalProjection_preimage_Iic
    {d : ℕ} (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1) (t : ℝ) :
    HDP.Chapter5.sphericalCap u (t / Real.sqrt (d : ℝ)) =
      HDP.Chapter3.sphericalProjection d (unitSpherePoint u hu) ⁻¹'
        Set.Iic t := by
  ext x
  change inner ℝ u (x : EuclideanSpace ℝ (Fin d)) ≤
      t / Real.sqrt (d : ℝ) ↔
    Real.sqrt d *
      inner ℝ (x : EuclideanSpace ℝ (Fin d)) u ≤ t
  rw [real_inner_comm]
  have hsqrt : 0 < Real.sqrt (d : ℝ) := by
    apply Real.sqrt_pos.2
    exact_mod_cast hd
  constructor
  · intro h
    simpa [mul_comm] using (le_div_iff₀ hsqrt).mp h
  · intro h
    apply (le_div_iff₀ hsqrt).mpr
    simpa [mul_comm] using h

/-- The mass of a rescaled spherical cap is the CDF of the corresponding
spherical projection law. -/
theorem unitSphereMeasure_sphericalCap_div_sqrt
    {d : ℕ} (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1) (t : ℝ) :
    HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin d))
        (HDP.Chapter5.sphericalCap u (t / Real.sqrt (d : ℝ))) =
      Measure.map
        (HDP.Chapter3.sphericalProjection d (unitSpherePoint u hu))
        (HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin d)))
        (Set.Iic t) := by
  rw [Measure.map_apply
    (HDP.Chapter3.measurable_sphericalProjection d (unitSpherePoint u hu))
    measurableSet_Iic]
  rw [← sphericalCap_eq_sphericalProjection_preimage_Iic hd u hu t]

/-- Uniform CDF convergence for the embedded normals used in the Poincaré
approximation. -/
theorem poincare_sphericalCap_cdf_uniform (n : ℕ) :
    ∀ η > 0, ∀ᶠ k : ℕ in atTop,
      ∀ (u : EuclideanSpace ℝ (Fin n)), ‖u‖ = 1 → ∀ t : ℝ,
        |(HDP.unitSphereMeasure
            (EuclideanSpace ℝ (Fin (n + (k + 2))))).real
            (HDP.Chapter5.sphericalCap (poincareEmbed n (k + 2) u)
              (t / Real.sqrt (n + (k + 2) : ℝ))) -
          (gaussianReal 0 1).real (Set.Iic t)| < η := by
  intro η hη
  have hdimTendsto :
      Tendsto (fun k : ℕ => n + (k + 2)) atTop atTop := by
    convert tendsto_add_atTop_nat (n + 2) using 1
    ext k
    omega
  have hclt := hdimTendsto.eventually
    (HDP.Chapter3.projectiveCentralLimitTheorem η hη)
  filter_upwards [hclt] with k hk
  intro u hu t
  let v : Metric.sphere
      (0 : EuclideanSpace ℝ (Fin (n + (k + 2)))) 1 :=
    unitSpherePoint (poincareEmbed n (k + 2) u)
      (by simpa [norm_poincareEmbed] using hu)
  have h := hk v t
  have hmass := unitSphereMeasure_sphericalCap_div_sqrt
    (d := n + (k + 2)) (by omega)
    (poincareEmbed n (k + 2) u)
    (by simpa [norm_poincareEmbed] using hu) t
  dsimp [v] at h
  rw [measureReal_def] at h ⊢
  rw [← hmass] at h
  simpa only [Nat.cast_add, Nat.cast_ofNat, v] using h

end HDP.Appendix
