import HighDimensionalProbability.Appendix.Infra.SpecialOrthogonalLogSobolevInduction
import HighDimensionalProbability.Appendix.Infra.SpecialOrthogonalFiberSmoothCore
import Mathlib.LinearAlgebra.Matrix.SchurComplement

open Matrix MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace HDP.Appendix.SpecialOrthogonal

noncomputable section

/-- The coordinate formula for the real Euclidean inner product. -/
def euclideanDot {n : ℕ}
    (v w : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ a : Fin n, v a * w a

lemma euclideanDot_self_eq_norm_sq {n : ℕ}
    (v : EuclideanSpace ℝ (Fin n)) :
    euclideanDot v v = ‖v‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
  simp [euclideanDot, pow_two]

lemma euclideanDot_self_pos {n : ℕ}
    {v : EuclideanSpace ℝ (Fin n)} (hv : v ≠ 0) :
    0 < euclideanDot v v := by
  rw [euclideanDot_self_eq_norm_sq]
  positivity

/-- The matrix-valued Householder-reflection formula associated with `v`. -/
noncomputable def householderMatrix {n : ℕ}
    (v : EuclideanSpace ℝ (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ :=
  1 - (2 / euclideanDot v v) •
    Matrix.vecMulVec (fun a => v a) (fun a => v a)

lemma householderMatrix_transpose {n : ℕ}
    (v : EuclideanSpace ℝ (Fin n)) :
    (householderMatrix v)ᵀ = householderMatrix v := by
  classical
  ext a b
  change
    (if b = a then 1 else 0) -
        (2 / euclideanDot v v) * (v b * v a) =
      (if a = b then 1 else 0) -
        (2 / euclideanDot v v) * (v a * v b)
  by_cases hab : a = b
  · subst b
    simp
  · simp only [hab, Ne.symm hab, if_false]
    ring

lemma vecMulVec_self_mul {n : ℕ}
    (v : EuclideanSpace ℝ (Fin n)) :
    Matrix.vecMulVec (fun a => v a) (fun a => v a) *
        Matrix.vecMulVec (fun a => v a) (fun a => v a) =
      euclideanDot v v •
        Matrix.vecMulVec (fun a => v a) (fun a => v a) := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply,
    Matrix.smul_apply, smul_eq_mul]
  rw [euclideanDot]
  calc
    (∑ x : Fin n, v a * v x * (v x * v b)) =
        ∑ x : Fin n, (v a * v b) * (v x * v x) := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = (v a * v b) * ∑ x : Fin n, v x * v x :=
      (Finset.mul_sum _ _ _).symm
    _ = (∑ x : Fin n, v x * v x) * (v a * v b) := by
      ring

lemma householderMatrix_mul_self {n : ℕ}
    (v : EuclideanSpace ℝ (Fin n)) (hv : v ≠ 0) :
    householderMatrix v * householderMatrix v = 1 := by
  classical
  have hs : euclideanDot v v ≠ 0 :=
    ne_of_gt (euclideanDot_self_pos hv)
  let s := euclideanDot v v
  let c := 2 / s
  let P :=
    Matrix.vecMulVec (fun a => v a) (fun a => v a)
  have hPP : P * P = s • P := by
    exact vecMulVec_self_mul v
  have hc : c * c * s = 2 * c := by
    dsimp [c, s]
    field_simp [hs]
  have hscaled :
      (c • P) * (c • P) = (c * c) • (P * P) := by
    rw [smul_mul_assoc, mul_smul_comm, smul_smul]
  change (1 - c • P) * (1 - c • P) = 1
  rw [sub_mul, one_mul, mul_sub, mul_one, hscaled,
    hPP, smul_smul, hc]
  module

lemma householderMatrix_mem_orthogonal {n : ℕ}
    (v : EuclideanSpace ℝ (Fin n)) (hv : v ≠ 0) :
    householderMatrix v ∈ Matrix.orthogonalGroup (Fin n) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff (Fin n) ℝ,
    householderMatrix_transpose,
    householderMatrix_mul_self v hv]

lemma householderMatrix_det {n : ℕ}
    (v : EuclideanSpace ℝ (Fin n)) (hv : v ≠ 0) :
    (householderMatrix v).det = -1 := by
  classical
  have hs : euclideanDot v v ≠ 0 :=
    ne_of_gt (euclideanDot_self_pos hv)
  have heq :
      householderMatrix v =
        1 + Matrix.vecMulVec
          (fun a => (-2 / euclideanDot v v) * v a)
          (fun a => v a) := by
    ext a b
    simp [householderMatrix, Matrix.vecMulVec]
    ring
  rw [heq, Matrix.vecMulVec_eq Unit,
    Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp only [dotProduct, Pi.add_apply]
  have hsum : (∑ x : Fin n,
      v x * ((-2 / euclideanDot v v) * v x)) =
      (-2 / euclideanDot v v) * euclideanDot v v := by
    rw [euclideanDot]
    calc
      (∑ x : Fin n,
          v x * ((-2 / ∑ a : Fin n, v a * v a) * v x)) =
          ∑ x : Fin n,
            (-2 / ∑ a : Fin n, v a * v a) *
              (v x * v x) := by
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ =
          (-2 / ∑ a : Fin n, v a * v a) *
            ∑ x : Fin n, v x * v x :=
        (Finset.mul_sum _ _ _).symm
  rw [hsum]
  field_simp [hs]
  norm_num

lemma householderMatrix_mulVec {n : ℕ}
    (v x : EuclideanSpace ℝ (Fin n)) :
    householderMatrix v *ᵥ (fun a => x a) =
      fun a => x a -
        (2 * euclideanDot v x / euclideanDot v v) * v a := by
  have hP :
      Matrix.vecMulVec (fun a => v a) (fun a => v a) *ᵥ
          (fun a => x a) =
        fun a => v a * euclideanDot v x := by
    ext a
    unfold Matrix.mulVec euclideanDot dotProduct
    simp only [Matrix.vecMulVec_apply]
    calc
      (∑ x_1 : Fin n, v a * v x_1 * x x_1) =
          ∑ x_1 : Fin n, v a * (v x_1 * x x_1) := by
        apply Finset.sum_congr rfl
        intro z _
        ring
      _ = v a * ∑ x_1 : Fin n, v x_1 * x x_1 :=
        (Finset.mul_sum Finset.univ
          (fun z : Fin n => v z * x z) (v a)).symm
  unfold householderMatrix
  rw [Matrix.sub_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec, hP]
  ext a
  simp
  ring

lemma euclideanDot_add_left {n : ℕ}
    (u v w : EuclideanSpace ℝ (Fin n)) :
    euclideanDot (u + v) w =
      euclideanDot u w + euclideanDot v w := by
  simp [euclideanDot, add_mul, Finset.sum_add_distrib]

lemma euclideanDot_add_right {n : ℕ}
    (u v w : EuclideanSpace ℝ (Fin n)) :
    euclideanDot u (v + w) =
      euclideanDot u v + euclideanDot u w := by
  simp [euclideanDot, mul_add, Finset.sum_add_distrib]

lemma euclideanDot_sub_left {n : ℕ}
    (u v w : EuclideanSpace ℝ (Fin n)) :
    euclideanDot (u - v) w =
      euclideanDot u w - euclideanDot v w := by
  simp [euclideanDot, sub_mul, Finset.sum_sub_distrib]

lemma euclideanDot_sub_right {n : ℕ}
    (u v w : EuclideanSpace ℝ (Fin n)) :
    euclideanDot u (v - w) =
      euclideanDot u v - euclideanDot u w := by
  simp [euclideanDot, mul_sub, Finset.sum_sub_distrib]

lemma euclideanDot_comm {n : ℕ}
    (u v : EuclideanSpace ℝ (Fin n)) :
    euclideanDot u v = euclideanDot v u := by
  unfold euclideanDot
  apply Finset.sum_congr rfl
  intro a _
  ring

lemma euclideanDot_neg_right {n : ℕ}
    (u v : EuclideanSpace ℝ (Fin n)) :
    euclideanDot u (-v) = -euclideanDot u v := by
  simp [euclideanDot, Finset.sum_neg_distrib]

lemma euclideanDot_coordinateSpherePoint {n : ℕ}
    (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    euclideanDot
        (coordinateSpherePoint i :
          EuclideanSpace ℝ (Fin n)) x = x i := by
  simp [euclideanDot, coordinateSpherePoint]

lemma euclideanDot_coordinateSpherePoint_right {n : ℕ}
    (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    euclideanDot x
        (coordinateSpherePoint i :
          EuclideanSpace ℝ (Fin n)) = x i := by
  rw [euclideanDot_comm,
    euclideanDot_coordinateSpherePoint]

lemma householderMatrix_mulVec_self {n : ℕ}
    (v : EuclideanSpace ℝ (Fin n)) (hv : v ≠ 0) :
    householderMatrix v *ᵥ (fun a => v a) =
      fun a => (-v) a := by
  rw [householderMatrix_mulVec,
    euclideanDot_self_eq_norm_sq]
  have hn : ‖v‖ ^ 2 ≠ 0 := by
    positivity
  funext a
  field_simp [hn]
  simp only [PiLp.neg_apply]
  ring

lemma euclideanDot_add_self_of_unit {n : ℕ}
    (r y : EuclideanSpace ℝ (Fin n))
    (hr : ‖r‖ = 1) (hy : ‖y‖ = 1) :
    euclideanDot (r + y) (r + y) =
      2 * (1 + euclideanDot r y) := by
  rw [euclideanDot_add_left, euclideanDot_add_right,
    euclideanDot_add_right, euclideanDot_self_eq_norm_sq,
    euclideanDot_self_eq_norm_sq, hr, hy,
    euclideanDot_comm y r]
  ring

lemma euclideanDot_sub_self_of_unit {n : ℕ}
    (r y : EuclideanSpace ℝ (Fin n))
    (hr : ‖r‖ = 1) (hy : ‖y‖ = 1) :
    euclideanDot (r - y) (r - y) =
      2 * (1 - euclideanDot r y) := by
  rw [euclideanDot_sub_left, euclideanDot_sub_right,
    euclideanDot_sub_right, euclideanDot_self_eq_norm_sq,
    euclideanDot_self_eq_norm_sq, hr, hy,
    euclideanDot_comm y r]
  ring

lemma householderMatrix_add_mulVec_neg_left
    {n : ℕ} (r y : EuclideanSpace ℝ (Fin n))
    (hr : ‖r‖ = 1) (hy : ‖y‖ = 1)
    (hry : r + y ≠ 0) :
    householderMatrix (r + y) *ᵥ (fun a => (-r) a) =
      fun a => y a := by
  rw [householderMatrix_mulVec]
  have hs := ne_of_gt (euclideanDot_self_pos hry)
  have hden := euclideanDot_add_self_of_unit r y hr hy
  have hnum :
      euclideanDot (r + y) (-r) =
        -(1 + euclideanDot r y) := by
    rw [euclideanDot_add_left, euclideanDot_neg_right,
      euclideanDot_neg_right]
    rw [euclideanDot_self_eq_norm_sq, hr,
      euclideanDot_comm y r]
    ring
  funext a
  rw [hnum, hden]
  have hbase : 1 + euclideanDot r y ≠ 0 := by
    intro h
    apply hs
    rw [hden, h]
    ring
  field_simp [hbase]
  simp only [PiLp.neg_apply, PiLp.add_apply]
  ring

lemma householderMatrix_sub_mulVec_left
    {n : ℕ} (r y : EuclideanSpace ℝ (Fin n))
    (hr : ‖r‖ = 1) (hy : ‖y‖ = 1)
    (hry : r - y ≠ 0) :
    householderMatrix (r - y) *ᵥ (fun a => r a) =
      fun a => y a := by
  rw [householderMatrix_mulVec]
  have hs := ne_of_gt (euclideanDot_self_pos hry)
  have hden := euclideanDot_sub_self_of_unit r y hr hy
  have hnum :
      euclideanDot (r - y) r =
        1 - euclideanDot r y := by
    rw [euclideanDot_sub_left,
      euclideanDot_self_eq_norm_sq, hr,
      euclideanDot_comm y r]
    ring
  funext a
  rw [hnum, hden]
  have hbase : 1 - euclideanDot r y ≠ 0 := by
    intro h
    apply hs
    rw [hden, h]
    ring
  field_simp [hbase]
  simp only [PiLp.sub_apply]
  ring

lemma householderMatrix_mulVec_of_dot_eq_zero {n : ℕ}
    (v x : EuclideanSpace ℝ (Fin n))
    (h : euclideanDot v x = 0) :
    householderMatrix v *ᵥ (fun a => x a) =
      fun a => x a := by
  rw [householderMatrix_mulVec, h]
  simp

/-- The first distinguished coordinate in the `(k + 3)`-dimensional quotient model. -/
def quotientFirstCoordinate (k : ℕ) : Fin (k + 3) :=
  ⟨0, by omega⟩

/-- The second distinguished coordinate in the `(k + 3)`-dimensional quotient model. -/
abbrev quotientSecondCoordinate (k : ℕ) : Fin (k + 3) :=
  secondCoordinateIndex k

/-- The reference unit vector at the second distinguished coordinate. -/
noncomputable def quotientReference (k : ℕ) :
    EuclideanSpace ℝ (Fin (k + 3)) :=
  coordinateSpherePoint (quotientSecondCoordinate k)

/-- The auxiliary unit vector at the first distinguished coordinate. -/
noncomputable def quotientAuxiliary (k : ℕ) :
    EuclideanSpace ℝ (Fin (k + 3)) :=
  coordinateSpherePoint (quotientFirstCoordinate k)

@[simp] lemma norm_quotientReference (k : ℕ) :
    ‖quotientReference k‖ = 1 :=
  by
    unfold quotientReference
    simp [coordinateSpherePoint]

@[simp] lemma norm_quotientAuxiliary (k : ℕ) :
    ‖quotientAuxiliary k‖ = 1 :=
  by
    unfold quotientAuxiliary
    simp [coordinateSpherePoint]

lemma norm_coe_mem_unitSphere {n : ℕ}
    (y : Metric.sphere
      (0 : EuclideanSpace ℝ (Fin n)) 1) :
    ‖(y : EuclideanSpace ℝ (Fin n))‖ = 1 := by
  simpa [Metric.mem_sphere, dist_zero_right] using y.2

lemma quotientReference_ne_zero (k : ℕ) :
    quotientReference k ≠ 0 := by
  intro h
  have := norm_quotientReference k
  rw [h, norm_zero] at this
  norm_num at this

lemma quotientAuxiliary_ne_zero (k : ℕ) :
    quotientAuxiliary k ≠ 0 := by
  intro h
  have := norm_quotientAuxiliary k
  rw [h, norm_zero] at this
  norm_num at this

lemma quotientAuxiliary_dot_reference (k : ℕ) :
    euclideanDot (quotientAuxiliary k)
      (quotientReference k) = 0 := by
  unfold quotientAuxiliary quotientReference
  rw [euclideanDot_coordinateSpherePoint]
  simp [quotientReference, quotientAuxiliary,
    quotientFirstCoordinate, quotientSecondCoordinate,
    secondCoordinateIndex, coordinateSpherePoint]

/-- The product of Householder reflections used for the positive quotient chart. -/
noncomputable def quotientPlusSectionMatrix
    (k : ℕ) (y : EuclideanSpace ℝ (Fin (k + 3))) :
    Matrix (Fin (k + 3)) (Fin (k + 3)) ℝ :=
  householderMatrix (quotientReference k + y) *
    householderMatrix (quotientReference k)

/-- The product of Householder reflections used for the negative quotient chart. -/
noncomputable def quotientMinusSectionMatrix
    (k : ℕ) (y : EuclideanSpace ℝ (Fin (k + 3))) :
    Matrix (Fin (k + 3)) (Fin (k + 3)) ℝ :=
  householderMatrix (quotientReference k - y) *
    householderMatrix (quotientAuxiliary k)

lemma quotientPlusSectionMatrix_mem_specialOrthogonal
    (k : ℕ)
    (y : Metric.sphere
      (0 : EuclideanSpace ℝ (Fin (k + 3))) 1)
    (hy : quotientReference k + (y : EuclideanSpace ℝ _) ≠ 0) :
    quotientPlusSectionMatrix k y ∈
      Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  refine ⟨?_, ?_⟩
  · exact (Matrix.orthogonalGroup (Fin (k + 3)) ℝ).mul_mem
      (householderMatrix_mem_orthogonal _ hy)
      (householderMatrix_mem_orthogonal _
        (quotientReference_ne_zero k))
  · rw [quotientPlusSectionMatrix, Matrix.det_mul,
      householderMatrix_det _ hy,
      householderMatrix_det _
        (quotientReference_ne_zero k)]
    norm_num

lemma quotientMinusSectionMatrix_mem_specialOrthogonal
    (k : ℕ)
    (y : Metric.sphere
      (0 : EuclideanSpace ℝ (Fin (k + 3))) 1)
    (hy : quotientReference k - (y : EuclideanSpace ℝ _) ≠ 0) :
    quotientMinusSectionMatrix k y ∈
      Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  refine ⟨?_, ?_⟩
  · exact (Matrix.orthogonalGroup (Fin (k + 3)) ℝ).mul_mem
      (householderMatrix_mem_orthogonal _ hy)
      (householderMatrix_mem_orthogonal _
        (quotientAuxiliary_ne_zero k))
  · rw [quotientMinusSectionMatrix, Matrix.det_mul,
      householderMatrix_det _ hy,
      householderMatrix_det _
        (quotientAuxiliary_ne_zero k)]
    norm_num

lemma quotientPlusSectionMatrix_mulVec_reference
    (k : ℕ)
    (y : Metric.sphere
      (0 : EuclideanSpace ℝ (Fin (k + 3))) 1)
    (hy : quotientReference k + (y : EuclideanSpace ℝ _) ≠ 0) :
    quotientPlusSectionMatrix k y *ᵥ
        (fun a => quotientReference k a) =
      fun a => (y : EuclideanSpace ℝ _) a := by
  rw [quotientPlusSectionMatrix, ← Matrix.mulVec_mulVec]
  rw [householderMatrix_mulVec_self _
      (quotientReference_ne_zero k)]
  exact householderMatrix_add_mulVec_neg_left
    (quotientReference k) y
    (norm_quotientReference k) (norm_coe_mem_unitSphere y) hy

lemma quotientMinusSectionMatrix_mulVec_reference
    (k : ℕ)
    (y : Metric.sphere
      (0 : EuclideanSpace ℝ (Fin (k + 3))) 1)
    (hy : quotientReference k - (y : EuclideanSpace ℝ _) ≠ 0) :
    quotientMinusSectionMatrix k y *ᵥ
        (fun a => quotientReference k a) =
      fun a => (y : EuclideanSpace ℝ _) a := by
  rw [quotientMinusSectionMatrix, ← Matrix.mulVec_mulVec]
  rw [householderMatrix_mulVec_of_dot_eq_zero
    (quotientAuxiliary k) (quotientReference k)
    (quotientAuxiliary_dot_reference k)]
  exact householderMatrix_sub_mulVec_left
    (quotientReference k) y
    (norm_quotientReference k) (norm_coe_mem_unitSphere y) hy

lemma coordinateStabilizerMatrix_injective {n : ℕ}
    (i : Fin (n + 1)) :
    Function.Injective (coordinateStabilizerMatrix i) := by
  intro A B h
  ext j k
  simpa using congrArg
    (fun M => M (i.succAbove j) (i.succAbove k)) h

lemma coordinateStabilizerMatrix_transpose {n : ℕ}
    (i : Fin (n + 1))
    (A : Matrix (Fin n) (Fin n) ℝ) :
    coordinateStabilizerMatrix i Aᵀ =
      (coordinateStabilizerMatrix i A)ᵀ := by
  ext a b
  cases a using i.succAboveCases
    <;> cases b using i.succAboveCases
    <;> simp

lemma coordinateStabilizerMatrix_det {n : ℕ}
    (i : Fin (n + 1))
    (A : Matrix (Fin n) (Fin n) ℝ) :
    (coordinateStabilizerMatrix i A).det = A.det := by
  classical
  unfold coordinateStabilizerMatrix
  rw [Matrix.det_reindex_self,
    Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, mul_one]

/-- The minor obtained by deleting the row and column at the distinguished coordinate `i`. -/
noncomputable def coordinateStabilizerMinor {n : ℕ}
    (i : Fin (n + 1))
    (W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun j k => W (i.succAbove j) (i.succAbove k)

lemma specialOrthogonal_eq_coordinateStabilizer_of_mulVec_fixed
    {n : ℕ} (i : Fin (n + 1))
    (W : Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ)
    (hfix :
      W.1 *ᵥ
          (fun a =>
            (coordinateSpherePoint i :
              EuclideanSpace ℝ (Fin (n + 1))) a) =
        fun a =>
          (coordinateSpherePoint i :
            EuclideanSpace ℝ (Fin (n + 1))) a) :
    ∃ V : Matrix.specialOrthogonalGroup (Fin n) ℝ,
      W = coordinateStabilizerHom i V := by
  classical
  have hcol (a : Fin (n + 1)) :
      W.1 a i = if a = i then 1 else 0 := by
    have h := congrFun hfix a
    simpa [coordinateSpherePoint, Matrix.mulVec,
      dotProduct] using h
  have horth :
      W.1ᵀ * W.1 = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin (n + 1)) ℝ).mp W.2.1
  have horth' :
      W.1 * W.1ᵀ = 1 :=
    (Matrix.mem_orthogonalGroup_iff (Fin (n + 1)) ℝ).mp W.2.1
  have hrow (b : Fin (n + 1)) :
      W.1 i b = if b = i then 1 else 0 := by
    have h := congrArg (fun M => M i b) horth
    simp only [Matrix.mul_apply, Matrix.transpose_apply] at h
    simp only [hcol, Finset.sum_ite_eq',
      Finset.mem_univ, one_mul] at h
    simpa [Matrix.one_apply, eq_comm] using h
  let A := coordinateStabilizerMinor i W.1
  have hWA : coordinateStabilizerMatrix i A = W.1 := by
    ext a b
    cases a using i.succAboveCases
      <;> cases b using i.succAboveCases
      <;> simp [A, coordinateStabilizerMinor, hcol, hrow]
  have hAorth : A ∈ Matrix.orthogonalGroup (Fin n) ℝ := by
    rw [Matrix.mem_orthogonalGroup_iff (Fin n) ℝ]
    apply coordinateStabilizerMatrix_injective i
    rw [coordinateStabilizerMatrix_mul,
      coordinateStabilizerMatrix_transpose, hWA,
      horth', coordinateStabilizerMatrix_one]
  have hAdet : A.det = 1 := by
    rw [← coordinateStabilizerMatrix_det i A, hWA]
    exact W.2.2
  let V : Matrix.specialOrthogonalGroup (Fin n) ℝ :=
    ⟨A, by
      rw [Matrix.mem_specialOrthogonalGroup_iff]
      exact ⟨hAorth, hAdet⟩⟩
  refine ⟨V, ?_⟩
  apply Subtype.ext
  exact hWA.symm

lemma coordinateStabilizerMeasure_mul_left_eq_self {n : ℕ}
    (i : Fin (n + 1))
    (V : Matrix.specialOrthogonalGroup (Fin n) ℝ) :
    Measure.map
        (fun U : Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ =>
          coordinateStabilizerHom i V * U)
        (coordinateStabilizerMeasure i) =
      coordinateStabilizerMeasure i := by
  rw [coordinateStabilizerMeasure,
    Measure.map_map (by fun_prop)
      (continuous_coordinateStabilizerHom i).measurable]
  let μ := HDP.Chapter5.specialOrthogonalHaarMeasure n
  let ι := coordinateStabilizerHom i
  calc
    Measure.map
        ((fun U : Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ =>
          ι V * U) ∘ ι) μ =
      Measure.map (ι ∘ fun U => V * U) μ := by
        congr 1
        funext U
        exact (ι.map_mul V U).symm
    _ = Measure.map ι (Measure.map (fun U => V * U) μ) := by
      exact (Measure.map_map
        (continuous_coordinateStabilizerHom i).measurable
        (by fun_prop)).symm
    _ = Measure.map ι μ := by
      rw [map_mul_left_eq_self μ V]

lemma rightAverage_coordinateStabilizer_mul_right
    {n : ℕ} (i : Fin (n + 1))
    (f : Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ → ℝ)
    (hf : Continuous f)
    (U : Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ)
    (V : Matrix.specialOrthogonalGroup (Fin n) ℝ) :
    rightAverage (coordinateStabilizerMeasure i) f
        (U * coordinateStabilizerHom i V) =
      rightAverage (coordinateStabilizerMeasure i) f U := by
  unfold rightAverage
  simp only [mul_assoc]
  have hmap :
      AEMeasurable
        (fun W : Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ =>
          coordinateStabilizerHom i V * W)
        (coordinateStabilizerMeasure i) :=
    (by fun_prop : Continuous
      (fun W : Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ =>
        coordinateStabilizerHom i V * W)).aemeasurable
  have hm :
      AEStronglyMeasurable
        (fun W : Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ =>
          f (U * W))
        (Measure.map
          (fun W : Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ =>
            coordinateStabilizerHom i V * W)
          (coordinateStabilizerMeasure i)) :=
    (hf.comp (by fun_prop : Continuous
      (fun W : Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ =>
        U * W))).aestronglyMeasurable
  rw [← integral_map hmap hm]
  rw [coordinateStabilizerMeasure_mul_left_eq_self]

lemma rightAverage_coordinateStabilizer_eq_of_mulVec_eq
    {n : ℕ} (i : Fin (n + 1))
    (f : Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ → ℝ)
    (hf : Continuous f)
    (U W : Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ)
    (horbit :
      U.1 *ᵥ
          (fun a =>
            (coordinateSpherePoint i :
              EuclideanSpace ℝ (Fin (n + 1))) a) =
        W.1 *ᵥ
          (fun a =>
            (coordinateSpherePoint i :
              EuclideanSpace ℝ (Fin (n + 1))) a)) :
    rightAverage (coordinateStabilizerMeasure i) f U =
      rightAverage (coordinateStabilizerMeasure i) f W := by
  have hfix :
      (U⁻¹ * W).1 *ᵥ
          (fun a =>
            (coordinateSpherePoint i :
              EuclideanSpace ℝ (Fin (n + 1))) a) =
        fun a =>
          (coordinateSpherePoint i :
            EuclideanSpace ℝ (Fin (n + 1))) a := by
    change
      (U⁻¹.1 * W.1) *ᵥ
          (fun a =>
            (coordinateSpherePoint i :
              EuclideanSpace ℝ (Fin (n + 1))) a) =
        fun a =>
          (coordinateSpherePoint i :
            EuclideanSpace ℝ (Fin (n + 1))) a
    rw [← Matrix.mulVec_mulVec, ← horbit,
      Matrix.mulVec_mulVec]
    change
      (U⁻¹ * U).1 *ᵥ
          (fun a =>
            (coordinateSpherePoint i :
              EuclideanSpace ℝ (Fin (n + 1))) a) =
        fun a =>
          (coordinateSpherePoint i :
            EuclideanSpace ℝ (Fin (n + 1))) a
    rw [inv_mul_cancel]
    simp
  obtain ⟨V, hV⟩ :=
    specialOrthogonal_eq_coordinateStabilizer_of_mulVec_fixed
      i (U⁻¹ * W) hfix
  have hW : W = U * coordinateStabilizerHom i V := by
    rw [← hV]
    simp
  rw [hW, rightAverage_coordinateStabilizer_mul_right
    i f hf U V]

end

end HDP.Appendix.SpecialOrthogonal
