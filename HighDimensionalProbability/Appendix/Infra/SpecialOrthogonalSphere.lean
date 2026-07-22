import HighDimensionalProbability.Appendix.Infra.SpecialOrthogonalSubgroup
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.Swap

/-!
# Spherical coordinate orbits of Haar special-orthogonal matrices

For dimension at least two, every coordinate column of a Haar `SO(n)` matrix
is uniform on the Euclidean unit sphere.  The proof starts from the
determinant-correction construction of Haar `SO(n)` from Haar `O(n)`: the
correction reflects the first coordinate, hence leaves the second coordinate
fixed.  Right-Haar invariance and explicit special-orthogonal rotations then
transfer the result to every coordinate.
-/

open Matrix MeasureTheory
open scoped RealInnerProductSpace

namespace HDP.Appendix.SpecialOrthogonal

/-- The coordinate unit vector, bundled as a point of the unit sphere. -/
noncomputable def coordinateSpherePoint {n : ℕ} (i : Fin n) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
  ⟨EuclideanSpace.single i 1, by
    simp [Metric.mem_sphere, dist_zero_right]⟩

/-- The non-inverted orthogonal orbit of a unit vector. -/
noncomputable def orthogonalSphereOrbit {n : ℕ}
    (v : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
  ⟨HDP.Chapter5.orthogonalAction U v, by
    simpa [Metric.mem_sphere, dist_zero_right] using
      HDP.Chapter5.norm_orthogonalAction U v⟩

lemma continuous_orthogonalSphereOrbit {n : ℕ}
    (v : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    Continuous (orthogonalSphereOrbit v) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun U : Matrix.orthogonalGroup (Fin n) ℝ =>
    U.1.toEuclideanLin
      (v : EuclideanSpace ℝ (Fin n)))
  change Continuous (fun U : Matrix.orthogonalGroup (Fin n) ℝ =>
    WithLp.toLp 2 (fun i : Fin n =>
      ∑ j : Fin n, U.1 i j *
        (v : EuclideanSpace ℝ (Fin n)) j))
  apply (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).comp
  apply continuous_pi
  intro i
  apply continuous_finsetSum
  intro j _
  have hij : Continuous
      (fun U : Matrix.orthogonalGroup (Fin n) ℝ => U.1 i j) :=
    (continuous_apply j).comp
      ((continuous_apply i).comp continuous_subtype_val)
  exact hij.mul continuous_const

lemma map_orthogonalSphereOrbit {n : ℕ} (hn : 0 < n)
    (v : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    Measure.map (orthogonalSphereOrbit v)
        (HDP.Chapter5.orthogonalHaarMeasure n) =
      HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)) := by
  let μ := HDP.Chapter5.orthogonalHaarMeasure n
  have hfun :
      orthogonalSphereOrbit v =
        HDP.Chapter5.inverseOrthogonalSphereOrbit v ∘ Inv.inv := by
    funext U
    apply Subtype.ext
    rfl
  rw [hfun, ← Measure.map_map]
  · rw [HDP.Appendix.probabilityHaar_map_inv_eq_self μ]
    exact HDP.Chapter5.map_inverseOrthogonalSphereOrbit hn v
  · exact
      (HDP.Chapter5.continuous_inverseOrthogonalSphereOrbit v).measurable
  · exact measurable_inv

/-- The non-inverted special-orthogonal orbit of a unit vector. -/
noncomputable def specialOrthogonalSphereOrbit {n : ℕ}
    (v : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
    (U : Matrix.specialOrthogonalGroup (Fin n) ℝ) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
  orthogonalSphereOrbit v (HDP.Chapter5.specialToOrthogonal n U)

lemma continuous_specialOrthogonalSphereOrbit {n : ℕ}
    (v : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    Continuous (specialOrthogonalSphereOrbit v) := by
  have hinc : Continuous (HDP.Chapter5.specialToOrthogonal n) := by
    apply continuous_induced_rng.mpr
    exact continuous_subtype_val
  exact (continuous_orthogonalSphereOrbit v).comp hinc

private lemma firstCoordinateReflection_fixes_second
    (n : ℕ) (hn : 2 ≤ n) :
    HDP.Chapter5.orthogonalAction
        (HDP.Chapter5.firstCoordinateReflection n (by omega))
        (coordinateSpherePoint (⟨1, hn⟩ : Fin n) :
          EuclideanSpace ℝ (Fin n)) =
      coordinateSpherePoint (⟨1, hn⟩ : Fin n) := by
  ext k
  simp [HDP.Chapter5.orthogonalAction,
    HDP.Chapter5.firstCoordinateReflection,
    Matrix.toLpLin_apply, coordinateSpherePoint,
    Matrix.diagonal_mulVec_single]

private lemma specialOrbit_second_orthogonalToSpecial
    (n : ℕ) (hn : 2 ≤ n)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) :
    specialOrthogonalSphereOrbit
        (coordinateSpherePoint (⟨1, hn⟩ : Fin n))
        (HDP.Chapter5.orthogonalToSpecial n (by omega) U) =
      orthogonalSphereOrbit
        (coordinateSpherePoint (⟨1, hn⟩ : Fin n)) U := by
  apply Subtype.ext
  classical
  by_cases hdet : U.1.det = 1
  · have heq :
        HDP.Chapter5.specialToOrthogonal n
            (HDP.Chapter5.orthogonalToSpecial n (by omega) U) = U := by
      apply Subtype.ext
      exact HDP.Chapter5.orthogonalToSpecial_of_det_one
        n (by omega) U hdet
    simp only [specialOrthogonalSphereOrbit, orthogonalSphereOrbit]
    rw [heq]
  · simp only [specialOrthogonalSphereOrbit, orthogonalSphereOrbit]
    have hval := HDP.Chapter5.orthogonalToSpecial_val
      n (by omega) U
    rw [if_neg hdet] at hval
    have heq :
        HDP.Chapter5.specialToOrthogonal n
            (HDP.Chapter5.orthogonalToSpecial n (by omega) U) =
          U * HDP.Chapter5.firstCoordinateReflection n (by omega) := by
      apply Subtype.ext
      exact hval
    rw [heq, HDP.Chapter5.orthogonalAction_mul,
      firstCoordinateReflection_fixes_second n hn]

/-- The second column of Haar `SO(n)` is uniform on the sphere. -/
lemma map_specialOrthogonalSphereOrbit_second
    (n : ℕ) (hn : 2 ≤ n) :
    Measure.map
        (specialOrthogonalSphereOrbit
          (coordinateSpherePoint (⟨1, hn⟩ : Fin n)))
        (HDP.Chapter5.specialOrthogonalHaarMeasure n) =
      HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)) := by
  rw [← HDP.Chapter5.determinantCorrectedOrthogonalMeasure_eq_specialOrthogonalHaar
    n (by omega)]
  rw [HDP.Chapter5.determinantCorrectedOrthogonalMeasure,
    Measure.map_map
      (continuous_specialOrthogonalSphereOrbit _).measurable
      (HDP.Chapter5.measurable_orthogonalToSpecial n (by omega))]
  have hfun :
      specialOrthogonalSphereOrbit
          (coordinateSpherePoint (⟨1, hn⟩ : Fin n)) ∘
        HDP.Chapter5.orthogonalToSpecial n (by omega) =
      orthogonalSphereOrbit
          (coordinateSpherePoint (⟨1, hn⟩ : Fin n)) := by
    funext U
    exact specialOrbit_second_orthogonalToSpecial n hn U
  rw [hfun]
  exact map_orthogonalSphereOrbit (by omega) _

/-! ## Transport from the second column to every coordinate column -/

/-- Reflection in an arbitrary coordinate hyperplane. -/
noncomputable def coordinateReflection {n : ℕ} (i : Fin n) :
    Matrix.orthogonalGroup (Fin n) ℝ := by
  classical
  refine
    ⟨Matrix.diagonal (fun j => if j = i then -1 else 1), ?_⟩
  rw [Matrix.mem_orthogonalGroup_iff (Fin n) ℝ]
  rw [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
  ext j k
  rw [Matrix.diagonal_apply, Matrix.one_apply]
  by_cases hjk : j = k
  · subst k
    by_cases hj : j = i <;> simp [hj]
  · simp [hjk]

/-- An arbitrary coordinate reflection has determinant `-1`. -/
@[simp] lemma coordinateReflection_det {n : ℕ} (i : Fin n) :
    (coordinateReflection i).1.det = -1 := by
  change
    (Matrix.diagonal (fun j : Fin n =>
      if j = i then (-1 : ℝ) else 1)).det = -1
  rw [Matrix.det_diagonal]
  exact Fintype.prod_ite_eq' i (fun _ : Fin n => (-1 : ℝ))

/-- A coordinate swap, regarded as an orthogonal matrix. -/
noncomputable def coordinateSwapOrthogonal {n : ℕ} (i j : Fin n) :
    Matrix.orthogonalGroup (Fin n) ℝ := by
  classical
  refine ⟨Matrix.swap ℝ i j, ?_⟩
  rw [Matrix.mem_orthogonalGroup_iff (Fin n) ℝ,
    Matrix.transpose_swap, Matrix.swap_mul_self]

/-- Swapping two distinct coordinates has determinant `-1`. -/
@[simp] lemma coordinateSwapOrthogonal_det {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) :
    (coordinateSwapOrthogonal i j).1.det = -1 := by
  change Matrix.det (Matrix.swap ℝ i j) = -1
  simp [Matrix.swap, Equiv.Perm.sign_swap hij]

/-- A determinant-one signed permutation sending the second coordinate vector
to the `i`-th coordinate vector.  The extra reflection corrects the
determinant of the transposition and fixes the second vector. -/
noncomputable def secondToCoordinateRotation
    (n : ℕ) (hn : 2 ≤ n) (i : Fin n) :
    Matrix.specialOrthogonalGroup (Fin n) ℝ := by
  classical
  let s : Fin n := ⟨1, hn⟩
  by_cases hi : i = s
  · exact 1
  · let Q : Matrix.orthogonalGroup (Fin n) ℝ :=
      coordinateSwapOrthogonal s i * coordinateReflection i
    refine ⟨Q.1, ?_⟩
    rw [Matrix.mem_specialOrthogonalGroup_iff]
    refine ⟨Q.2, ?_⟩
    change
      Matrix.det
        ((coordinateSwapOrthogonal s i).1 *
          (coordinateReflection i).1) = 1
    rw [Matrix.det_mul, coordinateSwapOrthogonal_det (fun h => hi h.symm),
      coordinateReflection_det]
    norm_num

/-- The signed permutation above sends the second coordinate point to the
specified coordinate point. -/
lemma secondToCoordinateRotation_action
    (n : ℕ) (hn : 2 ≤ n) (i : Fin n) :
    HDP.Chapter5.orthogonalAction
        (HDP.Chapter5.specialToOrthogonal n
          (secondToCoordinateRotation n hn i))
        (coordinateSpherePoint (⟨1, hn⟩ : Fin n) :
          EuclideanSpace ℝ (Fin n)) =
      coordinateSpherePoint i := by
  classical
  let s : Fin n := ⟨1, hn⟩
  change
    HDP.Chapter5.orthogonalAction
        (HDP.Chapter5.specialToOrthogonal n
          (secondToCoordinateRotation n hn i))
        (coordinateSpherePoint s : EuclideanSpace ℝ (Fin n)) =
      coordinateSpherePoint i
  by_cases hi : i = s
  · subst i
    simp [secondToCoordinateRotation, s,
      HDP.Chapter5.orthogonalAction, coordinateSpherePoint]
  · have hval :
        (secondToCoordinateRotation n hn i).1 =
          (coordinateSwapOrthogonal s i).1 *
            (coordinateReflection i).1 := by
      simp [secondToCoordinateRotation, s, hi]
    have hoval :
        (HDP.Chapter5.specialToOrthogonal n
          (secondToCoordinateRotation n hn i)).1 =
          (coordinateSwapOrthogonal s i).1 *
            (coordinateReflection i).1 :=
      hval
    unfold HDP.Chapter5.orthogonalAction
    rw [hoval]
    ext k
    simp only [Matrix.toLpLin_apply, coordinateSpherePoint]
    simp only [PiLp.ofLp_single]
    change
      ((Matrix.swap ℝ s i *
          Matrix.diagonal (fun j => if j = i then -1 else 1)) *ᵥ
        (Pi.single s (1 : ℝ) : Fin n → ℝ)) k =
          (Pi.single i (1 : ℝ) : Fin n → ℝ) k
    rw [← Matrix.mulVec_mulVec]
    rw [Matrix.diagonal_mulVec_single]
    have hsi : s ≠ i := fun h => hi h.symm
    simp only [if_neg hsi, one_mul]
    rw [Matrix.swap_mulVec]
    change (Pi.single s (1 : ℝ) : Fin n → ℝ) (Equiv.swap s i k) =
      (Pi.single i (1 : ℝ) : Fin n → ℝ) k
    by_cases hki : k = i
    · subst k
      simp [hsi]
    · by_cases hks : k = s
      · subst k
        simp [hsi, hki]
      · rw [Equiv.swap_apply_of_ne_of_ne hks hki]
        simp [hks, hki]

/-- Right multiplication by the signed permutation converts the second-column
orbit into the `i`-th-column orbit. -/
lemma specialOrthogonalSphereOrbit_coordinate_eq_second_mul
    (n : ℕ) (hn : 2 ≤ n) (i : Fin n)
    (U : Matrix.specialOrthogonalGroup (Fin n) ℝ) :
    specialOrthogonalSphereOrbit (coordinateSpherePoint i) U =
      specialOrthogonalSphereOrbit
        (coordinateSpherePoint (⟨1, hn⟩ : Fin n))
        (U * secondToCoordinateRotation n hn i) := by
  apply Subtype.ext
  simp only [specialOrthogonalSphereOrbit, orthogonalSphereOrbit]
  rw [map_mul, HDP.Chapter5.orthogonalAction_mul,
    secondToCoordinateRotation_action]

/-- Every coordinate column of a Haar `SO(n)` matrix is uniform on the
Euclidean unit sphere. -/
lemma map_specialOrthogonalSphereOrbit_coordinate
    (n : ℕ) (hn : 2 ≤ n) (i : Fin n) :
    Measure.map
        (specialOrthogonalSphereOrbit (coordinateSpherePoint i))
        (HDP.Chapter5.specialOrthogonalHaarMeasure n) =
      HDP.unitSphereMeasure (EuclideanSpace ℝ (Fin n)) := by
  let μ := HDP.Chapter5.specialOrthogonalHaarMeasure n
  let Q := secondToCoordinateRotation n hn i
  have hfun :
      specialOrthogonalSphereOrbit (coordinateSpherePoint i) =
        specialOrthogonalSphereOrbit
            (coordinateSpherePoint (⟨1, hn⟩ : Fin n)) ∘
          (fun U => U * Q) := by
    funext U
    exact specialOrthogonalSphereOrbit_coordinate_eq_second_mul n hn i U
  rw [hfun, ← Measure.map_map]
  · rw [HDP.Appendix.probabilityHaar_map_mul_right_eq_self μ Q]
    exact map_specialOrthogonalSphereOrbit_second n hn
  · exact
      (continuous_specialOrthogonalSphereOrbit
        (coordinateSpherePoint (⟨1, hn⟩ : Fin n))).measurable
  · fun_prop

end HDP.Appendix.SpecialOrthogonal
