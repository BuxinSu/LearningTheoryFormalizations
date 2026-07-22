import HighDimensionalProbability.Appendix.Infra.GaussianHalfspace
import HighDimensionalProbability.Prelude.Sphere
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Geometry for the Poincaré spherical approximation

The classical Poincaré-limit proof of Gaussian isoperimetry projects the
unit sphere in `ℝ^(n+m)` onto its first `n` coordinates and rescales by the
square root of the ambient dimension.  This file records the deterministic
geometry of that construction.  Probability convergence is kept separate.
-/

open MeasureTheory Set Metric InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace

namespace HDP.Appendix

/-- Restriction to the first `n` coordinates of `ℝ^(n+m)`. -/
noncomputable def poincareHead (n m : ℕ) :
    EuclideanSpace ℝ (Fin (n + m)) → EuclideanSpace ℝ (Fin n) :=
  fun x => WithLp.toLp 2 (fun i => x (Fin.castAdd m i))

@[simp]
theorem poincareHead_apply (n m : ℕ)
    (x : EuclideanSpace ℝ (Fin (n + m))) (i : Fin n) :
    poincareHead n m x i = x (Fin.castAdd m i) :=
  rfl

theorem poincareHead_zero (n m : ℕ) :
    poincareHead n m (0 : EuclideanSpace ℝ (Fin (n + m))) = 0 := by
  ext i
  rfl

theorem poincareHead_sub (n m : ℕ)
    (x y : EuclideanSpace ℝ (Fin (n + m))) :
    poincareHead n m (x - y) = poincareHead n m x - poincareHead n m y := by
  ext i
  rfl

/-- Dropping coordinates cannot increase the Euclidean norm. -/
theorem norm_poincareHead_le (n m : ℕ)
    (x : EuclideanSpace ℝ (Fin (n + m))) :
    ‖poincareHead n m x‖ ≤ ‖x‖ := by
  have hsum :
      ∑ i : Fin n, (x (Fin.castAdd m i)) ^ 2 ≤
        ∑ j : Fin (n + m), (x j) ^ 2 := by
    rw [Fin.sum_univ_add]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hsquare :
      ‖poincareHead n m x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    simpa only [poincareHead_apply] using hsum
  nlinarith [norm_nonneg (poincareHead n m x), norm_nonneg x]

theorem dist_poincareHead_le (n m : ℕ)
    (x y : EuclideanSpace ℝ (Fin (n + m))) :
    dist (poincareHead n m x) (poincareHead n m y) ≤ dist x y := by
  simpa only [dist_eq_norm, ← poincareHead_sub] using
    norm_poincareHead_le n m (x - y)

theorem continuous_poincareHead (n m : ℕ) :
    Continuous (poincareHead n m) := by
  apply continuous_iff_continuousAt.2
  intro x
  rw [Metric.continuousAt_iff]
  intro ε hε
  exact ⟨ε, hε, fun y hy =>
    lt_of_le_of_lt (dist_poincareHead_le n m y x) hy⟩

/-- The first-coordinate projection rescaled by the square root of ambient
dimension, as used in the Poincaré limit theorem. -/
noncomputable def poincareProjection (n m : ℕ)
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + m))) 1) :
    EuclideanSpace ℝ (Fin n) :=
  Real.sqrt (n + m : ℝ) • poincareHead n m (x : EuclideanSpace ℝ (Fin (n + m)))

theorem continuous_poincareProjection (n m : ℕ) :
    Continuous (poincareProjection n m) := by
  exact continuous_const.smul
    ((continuous_poincareHead n m).comp continuous_subtype_val)

theorem measurable_poincareProjection (n m : ℕ) :
    Measurable (poincareProjection n m) :=
  (continuous_poincareProjection n m).measurable

theorem poincareProjection_dist_le (n m : ℕ)
    (x y : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + m))) 1) :
    dist (poincareProjection n m x) (poincareProjection n m y) ≤
      Real.sqrt (n + m : ℝ) * dist x y := by
  rw [poincareProjection, poincareProjection, dist_smul₀, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul_of_nonneg_left
    (dist_poincareHead_le n m (x : EuclideanSpace ℝ (Fin (n + m))) y)
    (Real.sqrt_nonneg _)

/-- The lift of a Euclidean set to the high-dimensional unit sphere. -/
def poincareLift (n m : ℕ) (A : Set (EuclideanSpace ℝ (Fin n))) :
    Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + m))) 1) :=
  poincareProjection n m ⁻¹' A

theorem measurableSet_poincareLift {n m : ℕ}
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : MeasurableSet A) :
    MeasurableSet (poincareLift n m A) :=
  hA.preimage (measurable_poincareProjection n m)

/-- Spherical closed expansion of a lifted set projects into the Euclidean
closed expansion with the correspondingly rescaled radius. -/
theorem closedExpansion_poincareLift_subset (n m : ℕ)
    (A : Set (EuclideanSpace ℝ (Fin n))) (δ : ℝ) :
    closedExpansion δ (poincareLift n m A) ⊆
      poincareLift n m
        (closedExpansion (Real.sqrt (n + m : ℝ) * δ) A) := by
  intro x hx
  rcases hx with ⟨y, hyA, hxy⟩
  exact ⟨poincareProjection n m y, hyA,
    (poincareProjection_dist_le n m x y).trans
      (mul_le_mul_of_nonneg_left hxy (Real.sqrt_nonneg _))⟩

/-- Radius-normalized form of `closedExpansion_poincareLift_subset`. -/
theorem closedExpansion_poincareLift_div_sqrt_subset
    (n m : ℕ) (hdim : 0 < n + m)
    (A : Set (EuclideanSpace ℝ (Fin n))) (ε : ℝ) :
    closedExpansion (ε / Real.sqrt (n + m : ℝ)) (poincareLift n m A) ⊆
      poincareLift n m (closedExpansion ε A) := by
  have hdimR : 0 < (n + m : ℝ) := by exact_mod_cast hdim
  have hsqrtPos : 0 < Real.sqrt (n + m : ℝ) :=
    Real.sqrt_pos.2 hdimR
  have hsqrt : Real.sqrt (n + m : ℝ) ≠ 0 := by
    exact hsqrtPos.ne'
  have hmul :
      Real.sqrt (n + m : ℝ) * (ε / Real.sqrt (n + m : ℝ)) = ε := by
    field_simp
  have h := closedExpansion_poincareLift_subset n m A
    (ε / Real.sqrt (n + m : ℝ))
  rw [hmul] at h
  exact h

/-- Embed `ℝⁿ` isometrically as the first coordinates of `ℝ^(n+m)`. -/
noncomputable def poincareEmbed (n m : ℕ)
    (u : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin (n + m)) :=
  WithLp.toLp 2 (Fin.append (fun i => u i) (fun _ : Fin m => 0))

@[simp]
theorem poincareEmbed_castAdd_apply (n m : ℕ)
    (u : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    poincareEmbed n m u (Fin.castAdd m i) = u i := by
  simp [poincareEmbed, Fin.append_left]

@[simp]
theorem poincareEmbed_natAdd_apply (n m : ℕ)
    (u : EuclideanSpace ℝ (Fin n)) (i : Fin m) :
    poincareEmbed n m u (Fin.natAdd n i) = 0 := by
  simp [poincareEmbed, Fin.append_right]

/-- The first-coordinate embedding preserves Euclidean norm. -/
theorem norm_poincareEmbed (n m : ℕ)
    (u : EuclideanSpace ℝ (Fin n)) :
    ‖poincareEmbed n m u‖ = ‖u‖ := by
  have hsquare : ‖poincareEmbed n m u‖ ^ 2 = ‖u‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
      Fin.sum_univ_add]
    simp
  nlinarith [norm_nonneg (poincareEmbed n m u), norm_nonneg u]

/-- Inner products against an embedded normal depend only on the head
coordinates. -/
theorem inner_poincareEmbed (n m : ℕ)
    (u : EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin (n + m))) :
    inner ℝ (poincareEmbed n m u) x =
      inner ℝ u (poincareHead n m x) := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
  rw [Fin.sum_univ_add]
  simp [poincareEmbed, poincareHead]

/-- A Gaussian half-space lifted by the Poincaré projection is a spherical
cap with the embedded normal and the rescaled threshold. -/
theorem poincareLift_gaussianLinearHalfspace (n m : ℕ)
    (u : EuclideanSpace ℝ (Fin n)) (a : ℝ) :
    poincareLift n m (gaussianLinearHalfspace u a) =
      {x : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + m))) 1 |
        inner ℝ (poincareEmbed n m u)
            (x : EuclideanSpace ℝ (Fin (n + m))) *
              Real.sqrt (n + m : ℝ) ≤ a} := by
  ext x
  change inner ℝ u (Real.sqrt (n + m : ℝ) •
    poincareHead n m (x : EuclideanSpace ℝ (Fin (n + m)))) ≤ a ↔ _
  rw [inner_smul_right, ← inner_poincareEmbed]
  ring_nf
  rfl

/-- Division form of the lifted-halfspace identity, matching the threshold
used by spherical caps. -/
theorem poincareLift_gaussianLinearHalfspace_div_sqrt
    (n m : ℕ) (hdim : 0 < n + m)
    (u : EuclideanSpace ℝ (Fin n)) (a : ℝ) :
    poincareLift n m (gaussianLinearHalfspace u a) =
      {x : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + m))) 1 |
        inner ℝ (poincareEmbed n m u)
            (x : EuclideanSpace ℝ (Fin (n + m))) ≤
              a / Real.sqrt (n + m : ℝ)} := by
  rw [poincareLift_gaussianLinearHalfspace]
  ext x
  simp only [Set.mem_setOf_eq]
  have hdimR : 0 < (n + m : ℝ) := by exact_mod_cast hdim
  have hsqrt : 0 < Real.sqrt (n + m : ℝ) :=
    Real.sqrt_pos.2 hdimR
  exact (le_div_iff₀ hsqrt).symm

end HDP.Appendix
