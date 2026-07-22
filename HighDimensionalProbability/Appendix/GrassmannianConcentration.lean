import HighDimensionalProbability.Appendix.SpecialOrthogonalConcentration

/-!
# Concentration on Grassmannians
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal NNReal RealInnerProductSpace

namespace HDP.Chapter5

/-- The `SO(n)` orbit map defining a random Grassmannian point. -/
noncomputable def specialGrassmannOrbit (n m : ℕ)
    (U : Matrix.specialOrthogonalGroup (Fin n) ℝ) : Grassmannian n m :=
  grassmannOrbit n m (specialToOrthogonal n U)

private lemma measurable_specialGrassmannOrbit (n m : ℕ) :
    Measurable (specialGrassmannOrbit n m) := by
  have hinc : Measurable (specialToOrthogonal n) := by
    apply Measurable.subtype_mk
    exact continuous_subtype_val.measurable
  exact (continuous_grassmannOrbit n m).measurable.comp hinc

private lemma coordinateProjectionMatrix_opNorm_le_one (n m : ℕ) :
    HDP.matrixOpNorm (coordinateProjectionMatrix n m) ≤ 1 := by
  let P := coordinateProjectionMatrix n m
  have hgram : HDP.gramMatrix P = P := by
    simp only [HDP.gramMatrix, P, coordinateProjectionMatrix_transpose,
      coordinateProjectionMatrix_mul_self]
  have hs := HDP.matrixOpNorm_sq_eq_gram P
  rw [hgram] at hs
  nlinarith [HDP.matrixOpNorm_nonneg P]

private lemma firstCoordinateReflection_conj_coordinateProjection
    (n m : ℕ) (hn : 0 < n) :
    (firstCoordinateReflection n hn).1 * coordinateProjectionMatrix n m *
        (firstCoordinateReflection n hn).1ᵀ =
      coordinateProjectionMatrix n m := by
  let i₀ : Fin n := ⟨0, hn⟩
  change
    Matrix.diagonal (fun i : Fin n => if i = i₀ then (-1 : ℝ) else 1) *
          Matrix.diagonal (fun i : Fin n => if (i : ℕ) < m then 1 else 0) *
          (Matrix.diagonal
            (fun i : Fin n => if i = i₀ then (-1 : ℝ) else 1))ᵀ =
        Matrix.diagonal (fun i : Fin n => if (i : ℕ) < m then 1 else 0)
  rw [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases hi : i = i₀
  · subst i
    by_cases him : (i₀ : ℕ) < m <;> simp [him]
  · by_cases him : (i : ℕ) < m <;> simp [hi, him]

private lemma specialGrassmannOrbit_orthogonalToSpecial
    (n m : ℕ) (hn : 0 < n)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) :
    specialGrassmannOrbit n m (orthogonalToSpecial n hn U) =
      grassmannOrbit n m U := by
  classical
  apply Subtype.ext
  simp only [specialGrassmannOrbit, grassmannOrbit, specialToOrthogonal,
    MonoidHom.coe_mk, OneHom.coe_mk, orthogonalToSpecial_val]
  split
  · rfl
  · let R := firstCoordinateReflection n hn
    change
      (U.1 * R.1) * coordinateProjectionMatrix n m * (U.1 * R.1)ᵀ =
        U.1 * coordinateProjectionMatrix n m * U.1ᵀ
    rw [Matrix.transpose_mul]
    calc
      (U.1 * R.1) * coordinateProjectionMatrix n m * (R.1ᵀ * U.1ᵀ) =
          U.1 *
            (R.1 * coordinateProjectionMatrix n m * R.1ᵀ) * U.1ᵀ := by
        noncomm_ring
      _ = U.1 * coordinateProjectionMatrix n m * U.1ᵀ := by
        rw [firstCoordinateReflection_conj_coordinateProjection n m hn]

private lemma map_specialGrassmannOrbit_specialOrthogonalHaar
    (n m : ℕ) (hn : 0 < n) :
    Measure.map (specialGrassmannOrbit n m)
        (specialOrthogonalHaarMeasure n) =
      grassmannHaarMeasure n m := by
  rw [← determinantCorrectedOrthogonalMeasure_eq_specialOrthogonalHaar n hn]
  unfold determinantCorrectedOrthogonalMeasure grassmannHaarMeasure
  rw [Measure.map_map (measurable_specialGrassmannOrbit n m)
    (measurable_orthogonalToSpecial n hn)]
  congr 1
  funext U
  exact specialGrassmannOrbit_orthogonalToSpecial n m hn U

private lemma measurePreserving_specialGrassmannOrbit
    (n m : ℕ) (hn : 0 < n) :
    MeasurePreserving (specialGrassmannOrbit n m)
      (specialOrthogonalHaarMeasure n) (grassmannHaarMeasure n m) :=
  ⟨measurable_specialGrassmannOrbit n m,
    map_specialGrassmannOrbit_specialOrthogonalHaar n m hn⟩

private lemma specialGrassmannOrbit_lipschitz (n m : ℕ)
    (U V : Matrix.specialOrthogonalGroup (Fin n) ℝ) :
    grassmannDistance (specialGrassmannOrbit n m U)
        (specialGrassmannOrbit n m V) ≤
      2 * specialOrthogonalDistance U V := by
  let P := coordinateProjectionMatrix n m
  have hP : HDP.matrixOpNorm P ≤ 1 :=
    coordinateProjectionMatrix_opNorm_le_one n m
  have hU : HDP.matrixOpNorm U.1 ≤ 1 :=
    HDP.Chapter4.matrixOpNorm_orthogonal_le_one U.1 U.2.1
  have hV : HDP.matrixOpNorm V.1 ≤ 1 :=
    HDP.Chapter4.matrixOpNorm_orthogonal_le_one V.1 V.2.1
  have hUt : HDP.matrixOpNorm U.1ᵀ ≤ 1 := by
    simpa using hU
  have hfirst :
      HDP.matrixOpNorm ((U.1 - V.1) * P * U.1ᵀ) ≤
        HDP.matrixOpNorm (U.1 - V.1) := by
    calc
      HDP.matrixOpNorm ((U.1 - V.1) * P * U.1ᵀ) ≤
          HDP.matrixOpNorm ((U.1 - V.1) * P) *
            HDP.matrixOpNorm U.1ᵀ := HDP.matrixOpNorm_mul _ _
      _ ≤ (HDP.matrixOpNorm (U.1 - V.1) * HDP.matrixOpNorm P) *
          HDP.matrixOpNorm U.1ᵀ := by
        exact mul_le_mul_of_nonneg_right (HDP.matrixOpNorm_mul _ _)
          (HDP.matrixOpNorm_nonneg U.1ᵀ)
      _ ≤ (HDP.matrixOpNorm (U.1 - V.1) * 1) * 1 := by
        have hdiff : 0 ≤ HDP.matrixOpNorm (U.1 - V.1) :=
          HDP.matrixOpNorm_nonneg _
        calc
          (HDP.matrixOpNorm (U.1 - V.1) * HDP.matrixOpNorm P) *
              HDP.matrixOpNorm U.1ᵀ ≤
              (HDP.matrixOpNorm (U.1 - V.1) * 1) *
                HDP.matrixOpNorm U.1ᵀ := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hP hdiff)
              (HDP.matrixOpNorm_nonneg U.1ᵀ)
          _ ≤ (HDP.matrixOpNorm (U.1 - V.1) * 1) * 1 := by
            exact mul_le_mul_of_nonneg_left hUt
              (mul_nonneg hdiff zero_le_one)
      _ = HDP.matrixOpNorm (U.1 - V.1) := by ring
  have hsecond :
      HDP.matrixOpNorm (V.1 * P * (U.1ᵀ - V.1ᵀ)) ≤
        HDP.matrixOpNorm (U.1 - V.1) := by
    calc
      HDP.matrixOpNorm (V.1 * P * (U.1ᵀ - V.1ᵀ)) ≤
          HDP.matrixOpNorm (V.1 * P) *
            HDP.matrixOpNorm (U.1ᵀ - V.1ᵀ) := HDP.matrixOpNorm_mul _ _
      _ ≤ (HDP.matrixOpNorm V.1 * HDP.matrixOpNorm P) *
          HDP.matrixOpNorm (U.1ᵀ - V.1ᵀ) := by
        exact mul_le_mul_of_nonneg_right (HDP.matrixOpNorm_mul _ _)
          (HDP.matrixOpNorm_nonneg (U.1ᵀ - V.1ᵀ))
      _ ≤ (1 * 1) * HDP.matrixOpNorm (U.1ᵀ - V.1ᵀ) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul hV hP (HDP.matrixOpNorm_nonneg P) zero_le_one)
          (HDP.matrixOpNorm_nonneg (U.1ᵀ - V.1ᵀ))
      _ = HDP.matrixOpNorm (U.1 - V.1) := by
        simp [← Matrix.transpose_sub]
  have hdecomp :
      U.1 * P * U.1ᵀ - V.1 * P * V.1ᵀ =
        (U.1 - V.1) * P * U.1ᵀ +
          V.1 * P * (U.1ᵀ - V.1ᵀ) := by
    noncomm_ring
  change HDP.matrixOpNorm (U.1 * P * U.1ᵀ - V.1 * P * V.1ᵀ) ≤
    2 * HDP.matrixFrobeniusNorm (U.1 - V.1)
  rw [hdecomp]
  calc
    HDP.matrixOpNorm
        ((U.1 - V.1) * P * U.1ᵀ +
          V.1 * P * (U.1ᵀ - V.1ᵀ)) ≤
        HDP.matrixOpNorm ((U.1 - V.1) * P * U.1ᵀ) +
          HDP.matrixOpNorm (V.1 * P * (U.1ᵀ - V.1ᵀ)) :=
      HDP.matrixOpNorm_add_le _ _
    _ ≤ HDP.matrixOpNorm (U.1 - V.1) +
        HDP.matrixOpNorm (U.1 - V.1) := add_le_add hfirst hsecond
    _ ≤ 2 * HDP.matrixFrobeniusNorm (U.1 - V.1) := by
      nlinarith [HDP.Chapter4.operatorNorm_le_frobeniusNorm (U.1 - V.1)]

/-- **HDP Theorem 5.2.9 (Grassmannian concentration).**

Concentration passes from `SO(n)` to its Grassmannian quotient through the
projection-orbit map.  In the source metrics this map is `2`-Lipschitz.
-/
theorem grassmannian_concentration :
    ∃ C : ℝ, 0 < C ∧ ∀ (n m : ℕ), 1 ≤ m → m < n →
      HasMeanConcentration (grassmannHaarMeasure n m)
        grassmannDistance (C / Real.sqrt n) := by
  obtain ⟨C, hC, hSO⟩ := special_orthogonal_concentration
  refine ⟨2 * C, mul_pos (by norm_num) hC, ?_⟩
  intro n m hm hmn
  have hn : 0 < n := by omega
  have hn2 : 2 ≤ n := by omega
  have hmap := HasMeanConcentration.map_of_lipschitz
    (hSO n hn2) (specialGrassmannOrbit n m)
    (measurePreserving_specialGrassmannOrbit n m hn)
    (show (0 : ℝ) < 2 by norm_num)
    (specialGrassmannOrbit_lipschitz n m)
  convert hmap using 1
  ring

end HDP.Chapter5
