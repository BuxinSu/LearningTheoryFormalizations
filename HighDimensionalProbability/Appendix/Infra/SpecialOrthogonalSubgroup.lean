import HighDimensionalProbability.Appendix.Infra.HaarEntropy
import HighDimensionalProbability.Chapter5_ConcentrationWithoutIndependence

/-!
# Coordinate stabilizers in the special orthogonal group

For `i : Fin (n+1)`, the subgroup of `SO(n+1)` fixing the coordinate vector
`eᵢ` is canonically a copy of `SO(n)`.  This file constructs the embedding by
putting an `n × n` special-orthogonal matrix and the scalar `1` on the two
diagonal blocks, then reindexing so that the final singleton block occupies
coordinate `i`.
-/

open Matrix MeasureTheory

namespace HDP.Appendix.SpecialOrthogonal

/-- Reindex the coordinates so that `i` becomes the final singleton block. -/
def coordinateBlockEquiv {n : ℕ} (i : Fin (n + 1)) :
    Fin (n + 1) ≃ Fin n ⊕ PUnit.{1} :=
  (finSuccEquiv' i).trans
    (Equiv.optionEquivSumPUnit.{0} (Fin n))

/-- The ambient block-diagonal matrix fixing coordinate `i`. -/
noncomputable def coordinateStabilizerMatrix {n : ℕ}
    (i : Fin (n + 1)) (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.reindex (coordinateBlockEquiv i).symm
    (coordinateBlockEquiv i).symm
    (Matrix.fromBlocks A 0 0
      (1 : Matrix PUnit.{1} PUnit.{1} ℝ))

private lemma blockDiagonal_mul {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.fromBlocks A 0 0
          (1 : Matrix PUnit.{1} PUnit.{1} ℝ) *
        Matrix.fromBlocks B 0 0
          (1 : Matrix PUnit.{1} PUnit.{1} ℝ) =
      Matrix.fromBlocks (A * B) 0 0
        (1 : Matrix PUnit.{1} PUnit.{1} ℝ) := by
  rw [Matrix.fromBlocks_multiply]
  simp

@[simp] lemma coordinateStabilizerMatrix_one {n : ℕ}
    (i : Fin (n + 1)) :
    coordinateStabilizerMatrix i (1 : Matrix (Fin n) (Fin n) ℝ) = 1 := by
  classical
  unfold coordinateStabilizerMatrix
  rw [Matrix.fromBlocks_one]
  exact Matrix.reindexLinearEquiv_one (R := ℝ) (A := ℝ)
    (coordinateBlockEquiv i).symm

@[simp] lemma coordinateStabilizerMatrix_mul {n : ℕ}
    (i : Fin (n + 1)) (A B : Matrix (Fin n) (Fin n) ℝ) :
    coordinateStabilizerMatrix i (A * B) =
      coordinateStabilizerMatrix i A * coordinateStabilizerMatrix i B := by
  classical
  unfold coordinateStabilizerMatrix
  rw [← blockDiagonal_mul]
  exact (Matrix.reindexAlgEquiv ℝ ℝ
    (coordinateBlockEquiv i).symm).map_mul _ _

private lemma blockDiagonal_mem_specialOrthogonal {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ Matrix.specialOrthogonalGroup (Fin n) ℝ) :
    Matrix.fromBlocks A 0 0
        (1 : Matrix PUnit.{1} PUnit.{1} ℝ) ∈
      Matrix.specialOrthogonalGroup (Fin n ⊕ PUnit.{1}) ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff] at hA ⊢
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_orthogonalGroup_iff] at hA ⊢
    rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
    simpa [hA.1, ← Matrix.fromBlocks_one]
  · simpa using hA.2

private lemma coordinateStabilizerMatrix_mem_specialOrthogonal {n : ℕ}
    (i : Fin (n + 1)) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ Matrix.specialOrthogonalGroup (Fin n) ℝ) :
    coordinateStabilizerMatrix i A ∈
      Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ := by
  classical
  have hblock := blockDiagonal_mem_specialOrthogonal A hA
  rw [Matrix.mem_specialOrthogonalGroup_iff] at hblock ⊢
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_orthogonalGroup_iff] at hblock ⊢
    unfold coordinateStabilizerMatrix
    have htranspose :
        (Matrix.reindex (coordinateBlockEquiv i).symm
          (coordinateBlockEquiv i).symm
          (Matrix.fromBlocks A 0 0
            (1 : Matrix PUnit.{1} PUnit.{1} ℝ)))ᵀ =
        Matrix.reindex (coordinateBlockEquiv i).symm
          (coordinateBlockEquiv i).symm
          (Matrix.fromBlocks A 0 0
            (1 : Matrix PUnit.{1} PUnit.{1} ℝ))ᵀ := by
      ext a b
      rfl
    rw [htranspose]
    change
      (Matrix.reindexAlgEquiv ℝ ℝ
          (coordinateBlockEquiv i).symm)
            (Matrix.fromBlocks A 0 0
              (1 : Matrix PUnit.{1} PUnit.{1} ℝ)) *
        (Matrix.reindexAlgEquiv ℝ ℝ
          (coordinateBlockEquiv i).symm)
            ((Matrix.fromBlocks A 0 0
              (1 : Matrix PUnit.{1} PUnit.{1} ℝ))ᵀ) = 1
    rw [← map_mul, hblock.1, map_one]
  · unfold coordinateStabilizerMatrix
    rw [Matrix.det_reindex_self]
    exact hblock.2

/-- The standard coordinate-stabilizer embedding `SO(n) → SO(n+1)`. -/
noncomputable def coordinateStabilizerHom {n : ℕ}
    (i : Fin (n + 1)) :
    Matrix.specialOrthogonalGroup (Fin n) ℝ →*
      Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ where
  toFun U :=
    ⟨coordinateStabilizerMatrix i U.1,
      coordinateStabilizerMatrix_mem_specialOrthogonal i U.1 U.2⟩
  map_one' := by
    apply Subtype.ext
    exact coordinateStabilizerMatrix_one i
  map_mul' U V := by
    apply Subtype.ext
    exact coordinateStabilizerMatrix_mul i U.1 V.1

@[simp] lemma coordinateStabilizerHom_val {n : ℕ}
    (i : Fin (n + 1))
    (U : Matrix.specialOrthogonalGroup (Fin n) ℝ) :
    (coordinateStabilizerHom i U :
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) =
      coordinateStabilizerMatrix i U.1 := rfl

@[simp] lemma coordinateBlockEquiv_at {n : ℕ}
    (i : Fin (n + 1)) :
    coordinateBlockEquiv i i = Sum.inr PUnit.unit := by
  simp [coordinateBlockEquiv, finSuccEquiv'_at,
    Equiv.optionEquivSumPUnit_none]

@[simp] lemma coordinateBlockEquiv_succAbove {n : ℕ}
    (i : Fin (n + 1)) (j : Fin n) :
    coordinateBlockEquiv i (i.succAbove j) = Sum.inl j := by
  simp [coordinateBlockEquiv, finSuccEquiv'_succAbove,
    Equiv.optionEquivSumPUnit_some]

@[simp] lemma coordinateStabilizerMatrix_succAbove {n : ℕ}
    (i : Fin (n + 1)) (A : Matrix (Fin n) (Fin n) ℝ)
    (j k : Fin n) :
    coordinateStabilizerMatrix i A
        (i.succAbove j) (i.succAbove k) = A j k := by
  simp [coordinateStabilizerMatrix, Matrix.reindex_apply]

@[simp] lemma coordinateStabilizerMatrix_fixed {n : ℕ}
    (i : Fin (n + 1)) (A : Matrix (Fin n) (Fin n) ℝ) :
    coordinateStabilizerMatrix i A i i = 1 := by
  simp [coordinateStabilizerMatrix, Matrix.reindex_apply]

@[simp] lemma coordinateStabilizerMatrix_fixed_succAbove {n : ℕ}
    (i : Fin (n + 1)) (A : Matrix (Fin n) (Fin n) ℝ)
    (j : Fin n) :
    coordinateStabilizerMatrix i A i (i.succAbove j) = 0 := by
  simp [coordinateStabilizerMatrix, Matrix.reindex_apply]

@[simp] lemma coordinateStabilizerMatrix_succAbove_fixed {n : ℕ}
    (i : Fin (n + 1)) (A : Matrix (Fin n) (Fin n) ℝ)
    (j : Fin n) :
    coordinateStabilizerMatrix i A (i.succAbove j) i = 0 := by
  simp [coordinateStabilizerMatrix, Matrix.reindex_apply]

lemma coordinateStabilizerHom_injective {n : ℕ}
    (i : Fin (n + 1)) :
    Function.Injective (coordinateStabilizerHom i) := by
  intro U V hUV
  apply Subtype.ext
  ext j k
  have hentries := congrArg
    (fun W : Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ =>
      (W.1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
        (i.succAbove j) (i.succAbove k)) hUV
  simpa using hentries

lemma continuous_coordinateStabilizerMatrix {n : ℕ}
    (i : Fin (n + 1)) :
    Continuous (coordinateStabilizerMatrix i) := by
  unfold coordinateStabilizerMatrix
  fun_prop

lemma continuous_coordinateStabilizerHom {n : ℕ}
    (i : Fin (n + 1)) :
    Continuous (coordinateStabilizerHom i) := by
  apply continuous_induced_rng.mpr
  exact (continuous_coordinateStabilizerMatrix i).comp
    continuous_subtype_val

/-- Haar probability on the coordinate stabilizer, viewed as a measure on
the ambient special orthogonal group. -/
noncomputable def coordinateStabilizerMeasure {n : ℕ}
    (i : Fin (n + 1)) :
    Measure (Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ) :=
  Measure.map (coordinateStabilizerHom i)
    (HDP.Chapter5.specialOrthogonalHaarMeasure n)

instance instIsProbabilityMeasureCoordinateStabilizer {n : ℕ}
    (i : Fin (n + 1)) :
    IsProbabilityMeasure (coordinateStabilizerMeasure i) :=
  Measure.isProbabilityMeasure_map
    (continuous_coordinateStabilizerHom i).aemeasurable

lemma integral_coordinateStabilizerMeasure {n : ℕ}
    (i : Fin (n + 1))
    (f : Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ → ℝ)
    (hf : AEStronglyMeasurable f (coordinateStabilizerMeasure i)) :
    (∫ U, f U ∂coordinateStabilizerMeasure i) =
      ∫ V, f (coordinateStabilizerHom i V)
        ∂HDP.Chapter5.specialOrthogonalHaarMeasure n := by
  rw [coordinateStabilizerMeasure]
  exact integral_map
    (continuous_coordinateStabilizerHom i).aemeasurable hf

lemma integral_coordinateStabilizerMeasure_of_continuous {n : ℕ}
    (i : Fin (n + 1))
    (f : Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ → ℝ)
    (hf : Continuous f) :
    (∫ U, f U ∂coordinateStabilizerMeasure i) =
      ∫ V, f (coordinateStabilizerHom i V)
        ∂HDP.Chapter5.specialOrthogonalHaarMeasure n :=
  integral_coordinateStabilizerMeasure i f
    hf.aestronglyMeasurable

lemma coordinateStabilizerMeasure_mul_right_eq_self {n : ℕ}
    (i : Fin (n + 1))
    (V : Matrix.specialOrthogonalGroup (Fin n) ℝ) :
    Measure.map
        (fun U : Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ =>
          U * coordinateStabilizerHom i V)
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
          U * ι V) ∘ ι) μ =
      Measure.map (ι ∘ fun U => U * V) μ := by
        congr 1
        funext U
        exact (ι.map_mul U V).symm
    _ = Measure.map ι (Measure.map (fun U => U * V) μ) := by
      exact (Measure.map_map
        (continuous_coordinateStabilizerHom i).measurable
        (by fun_prop)).symm
    _ = Measure.map ι μ := by
      rw [HDP.Appendix.probabilityHaar_map_mul_right_eq_self μ V]

end HDP.Appendix.SpecialOrthogonal
