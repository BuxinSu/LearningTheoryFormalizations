import HighDimensionalProbability.Appendix.Infra.SpecialOrthogonalQuotientAnalytic

/-!
# Coordinate transport for the special-orthogonal quotient estimate

Conjugation by a determinant-one signed permutation identifies every
coordinate stabilizer with the second-coordinate stabilizer.  This module
transports conditional Haar entropy and right-trivialized horizontal energy
through that identification, extending the analytic quotient estimate to
every coordinate.
-/

open Matrix MeasureTheory
open scoped BigOperators RealInnerProductSpace Topology

namespace HDP.Appendix.SpecialOrthogonal

noncomputable section

private lemma conjugate_secondStabilizer_fixes_coordinate
    (k : ℕ) (i : Fin (k + 3))
    (V : Matrix.specialOrthogonalGroup (Fin (k + 2)) ℝ) :
    let Q :=
      secondToCoordinateRotation (k + 3) (by omega) i
    (Q * coordinateStabilizerHom (secondCoordinateIndex k) V * Q⁻¹).1 *ᵥ
        (fun p =>
          (coordinateSpherePoint i :
            EuclideanSpace ℝ (Fin (k + 3))) p) =
      fun p =>
        (coordinateSpherePoint i :
          EuclideanSpace ℝ (Fin (k + 3))) p := by
  let s := secondCoordinateIndex k
  let Q := secondToCoordinateRotation (k + 3) (by omega) i
  have hQ :
      Q.1 *ᵥ
          (fun p =>
            (coordinateSpherePoint s :
              EuclideanSpace ℝ (Fin (k + 3))) p) =
        fun p =>
          (coordinateSpherePoint i :
            EuclideanSpace ℝ (Fin (k + 3))) p := by
    have h :=
      secondToCoordinateRotation_action (k + 3) (by omega) i
    ext p
    have hp := congrFun (congrArg WithLp.ofLp h) p
    change
      (Q.1 *ᵥ
          (fun q =>
            (coordinateSpherePoint s :
              EuclideanSpace ℝ (Fin (k + 3))) q)) p =
        (coordinateSpherePoint i :
          EuclideanSpace ℝ (Fin (k + 3))) p at hp
    exact hp
  have hQinv :
      Q⁻¹.1 *ᵥ
          (fun p =>
            (coordinateSpherePoint i :
              EuclideanSpace ℝ (Fin (k + 3))) p) =
        fun p =>
          (coordinateSpherePoint s :
            EuclideanSpace ℝ (Fin (k + 3))) p := by
    rw [← hQ]
    calc
      Q⁻¹.1 *ᵥ
          (Q.1 *ᵥ
            (fun p =>
              (coordinateSpherePoint s :
                EuclideanSpace ℝ (Fin (k + 3))) p)) =
          (Q⁻¹.1 * Q.1) *ᵥ
            (fun p =>
              (coordinateSpherePoint s :
                EuclideanSpace ℝ (Fin (k + 3))) p) := by
            rw [Matrix.mulVec_mulVec]
      _ = _ := by
        have hQQ :
            (Q⁻¹ * Q :
              Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ) = 1 := by
          simp
        have hQQval := congrArg Subtype.val hQQ
        change Q⁻¹.1 * Q.1 = 1 at hQQval
        rw [hQQval]
        simp
  have hV :
      (coordinateStabilizerHom s V).1 *ᵥ
          (fun p =>
            (coordinateSpherePoint s :
              EuclideanSpace ℝ (Fin (k + 3))) p) =
        fun p =>
          (coordinateSpherePoint s :
            EuclideanSpace ℝ (Fin (k + 3))) p := by
    ext p
    refine Fin.succAboveCases s ?_ (fun j => ?_) p
    · simp [coordinateSpherePoint, Matrix.mulVec, dotProduct]
    · simp [coordinateSpherePoint, Matrix.mulVec, dotProduct]
  dsimp only
  rw [show
      (Q * coordinateStabilizerHom s V * Q⁻¹).1 =
        Q.1 * (coordinateStabilizerHom s V).1 * Q⁻¹.1 by rfl]
  rw [← Matrix.mulVec_mulVec, hQinv,
    ← Matrix.mulVec_mulVec, hV, hQ]

private lemma conjugatedSecondStabilizer_exists
    (k : ℕ) (i : Fin (k + 3))
    (V : Matrix.specialOrthogonalGroup (Fin (k + 2)) ℝ) :
    ∃ W : Matrix.specialOrthogonalGroup (Fin (k + 2)) ℝ,
      secondToCoordinateRotation (k + 3) (by omega) i *
          coordinateStabilizerHom (secondCoordinateIndex k) V *
          (secondToCoordinateRotation (k + 3) (by omega) i)⁻¹ =
        coordinateStabilizerHom i W :=
  specialOrthogonal_eq_coordinateStabilizer_of_mulVec_fixed i
    (secondToCoordinateRotation (k + 3) (by omega) i *
      coordinateStabilizerHom (secondCoordinateIndex k) V *
      (secondToCoordinateRotation (k + 3) (by omega) i)⁻¹)
    (conjugate_secondStabilizer_fixes_coordinate k i V)

private noncomputable def conjugatedSecondStabilizerHom
    (k : ℕ) (i : Fin (k + 3)) :
    Matrix.specialOrthogonalGroup (Fin (k + 2)) ℝ →*
      Matrix.specialOrthogonalGroup (Fin (k + 2)) ℝ where
  toFun V :=
    Classical.choose (conjugatedSecondStabilizer_exists k i V)
  map_one' := by
    apply coordinateStabilizerHom_injective i
    rw [← Classical.choose_spec
      (conjugatedSecondStabilizer_exists k i 1)]
    simp
  map_mul' V W := by
    apply coordinateStabilizerHom_injective i
    rw [← Classical.choose_spec
      (conjugatedSecondStabilizer_exists k i (V * W))]
    rw [map_mul]
    simp only [map_mul]
    rw [← Classical.choose_spec
      (conjugatedSecondStabilizer_exists k i V)]
    rw [← Classical.choose_spec
      (conjugatedSecondStabilizer_exists k i W)]
    group

private lemma coordinateStabilizerHom_conjugatedSecondStabilizerHom
    (k : ℕ) (i : Fin (k + 3))
    (V : Matrix.specialOrthogonalGroup (Fin (k + 2)) ℝ) :
    coordinateStabilizerHom i
        (conjugatedSecondStabilizerHom k i V) =
      secondToCoordinateRotation (k + 3) (by omega) i *
        coordinateStabilizerHom (secondCoordinateIndex k) V *
        (secondToCoordinateRotation (k + 3) (by omega) i)⁻¹ :=
  (Classical.choose_spec
    (conjugatedSecondStabilizer_exists k i V)).symm

private lemma continuous_conjugatedSecondStabilizerHom
    (k : ℕ) (i : Fin (k + 3)) :
    Continuous (conjugatedSecondStabilizerHom k i) := by
  apply continuous_induced_rng.mpr
  change Continuous
    (fun V : Matrix.specialOrthogonalGroup (Fin (k + 2)) ℝ =>
      (conjugatedSecondStabilizerHom k i V).1)
  apply continuous_pi
  intro a
  apply continuous_pi
  intro b
  have hentry :
      ∀ V : Matrix.specialOrthogonalGroup (Fin (k + 2)) ℝ,
        (conjugatedSecondStabilizerHom k i V).1 a b =
          (secondToCoordinateRotation (k + 3) (by omega) i *
            coordinateStabilizerHom (secondCoordinateIndex k) V *
            (secondToCoordinateRotation (k + 3) (by omega) i)⁻¹).1
              (i.succAbove a) (i.succAbove b) := by
    intro V
    have h := congrArg
      (fun W : Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ =>
        W.1 (i.succAbove a) (i.succAbove b))
      (coordinateStabilizerHom_conjugatedSecondStabilizerHom k i V)
    simpa using h
  simp_rw [hentry]
  have hconj :
      Continuous
        (fun V : Matrix.specialOrthogonalGroup (Fin (k + 2)) ℝ =>
          secondToCoordinateRotation (k + 3) (by omega) i *
            coordinateStabilizerHom (secondCoordinateIndex k) V *
            (secondToCoordinateRotation (k + 3) (by omega) i)⁻¹) := by
    exact
      (continuous_const.mul
        (continuous_coordinateStabilizerHom
          (secondCoordinateIndex k))).mul continuous_const
  exact
    (continuous_apply (i.succAbove b)).comp
      ((continuous_apply (i.succAbove a)).comp
        (continuous_subtype_val.comp hconj))

private lemma inverseConjugate_coordinateStabilizer_fixes_second
    (k : ℕ) (i : Fin (k + 3))
    (T : Matrix.specialOrthogonalGroup (Fin (k + 2)) ℝ) :
    let Q :=
      secondToCoordinateRotation (k + 3) (by omega) i
    (Q⁻¹ * coordinateStabilizerHom i T * Q).1 *ᵥ
        (fun p =>
          (coordinateSpherePoint (secondCoordinateIndex k) :
            EuclideanSpace ℝ (Fin (k + 3))) p) =
      fun p =>
        (coordinateSpherePoint (secondCoordinateIndex k) :
          EuclideanSpace ℝ (Fin (k + 3))) p := by
  let s := secondCoordinateIndex k
  let Q := secondToCoordinateRotation (k + 3) (by omega) i
  have hQ :
      Q.1 *ᵥ
          (fun p =>
            (coordinateSpherePoint s :
              EuclideanSpace ℝ (Fin (k + 3))) p) =
        fun p =>
          (coordinateSpherePoint i :
            EuclideanSpace ℝ (Fin (k + 3))) p := by
    have h :=
      secondToCoordinateRotation_action (k + 3) (by omega) i
    ext p
    have hp := congrFun (congrArg WithLp.ofLp h) p
    change
      (Q.1 *ᵥ
          (fun q =>
            (coordinateSpherePoint s :
              EuclideanSpace ℝ (Fin (k + 3))) q)) p =
        (coordinateSpherePoint i :
          EuclideanSpace ℝ (Fin (k + 3))) p at hp
    exact hp
  have hQinv :
      Q⁻¹.1 *ᵥ
          (fun p =>
            (coordinateSpherePoint i :
              EuclideanSpace ℝ (Fin (k + 3))) p) =
        fun p =>
          (coordinateSpherePoint s :
            EuclideanSpace ℝ (Fin (k + 3))) p := by
    rw [← hQ]
    calc
      Q⁻¹.1 *ᵥ
          (Q.1 *ᵥ
            (fun p =>
              (coordinateSpherePoint s :
                EuclideanSpace ℝ (Fin (k + 3))) p)) =
          (Q⁻¹.1 * Q.1) *ᵥ
            (fun p =>
              (coordinateSpherePoint s :
                EuclideanSpace ℝ (Fin (k + 3))) p) := by
            rw [Matrix.mulVec_mulVec]
      _ = _ := by
        have hQQ :
            (Q⁻¹ * Q :
              Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ) = 1 := by
          simp
        have hQQval := congrArg Subtype.val hQQ
        change Q⁻¹.1 * Q.1 = 1 at hQQval
        rw [hQQval]
        simp
  have hT :
      (coordinateStabilizerHom i T).1 *ᵥ
          (fun p =>
            (coordinateSpherePoint i :
              EuclideanSpace ℝ (Fin (k + 3))) p) =
        fun p =>
          (coordinateSpherePoint i :
            EuclideanSpace ℝ (Fin (k + 3))) p := by
    ext p
    refine Fin.succAboveCases i ?_ (fun j => ?_) p
    · simp [coordinateSpherePoint, Matrix.mulVec, dotProduct]
    · simp [coordinateSpherePoint, Matrix.mulVec, dotProduct]
  dsimp only
  rw [show
      (Q⁻¹ * coordinateStabilizerHom i T * Q).1 =
        Q⁻¹.1 * (coordinateStabilizerHom i T).1 * Q.1 by rfl]
  rw [← Matrix.mulVec_mulVec, hQ,
    ← Matrix.mulVec_mulVec, hT, hQinv]

private lemma surjective_conjugatedSecondStabilizerHom
    (k : ℕ) (i : Fin (k + 3)) :
    Function.Surjective (conjugatedSecondStabilizerHom k i) := by
  intro T
  let Q := secondToCoordinateRotation (k + 3) (by omega) i
  obtain ⟨S, hS⟩ :=
    specialOrthogonal_eq_coordinateStabilizer_of_mulVec_fixed
      (secondCoordinateIndex k)
      (Q⁻¹ * coordinateStabilizerHom i T * Q)
      (inverseConjugate_coordinateStabilizer_fixes_second k i T)
  refine ⟨S, coordinateStabilizerHom_injective i ?_⟩
  rw [coordinateStabilizerHom_conjugatedSecondStabilizerHom]
  rw [← hS]
  dsimp only [Q]
  group

private lemma map_conjugatedSecondStabilizerHom_haar
    (k : ℕ) (i : Fin (k + 3)) :
    Measure.map (conjugatedSecondStabilizerHom k i)
        (HDP.Chapter5.specialOrthogonalHaarMeasure (k + 2)) =
      HDP.Chapter5.specialOrthogonalHaarMeasure (k + 2) := by
  let μ := HDP.Chapter5.specialOrthogonalHaarMeasure (k + 2)
  let ψ := conjugatedSecondStabilizerHom k i
  let ν := Measure.map ψ μ
  letI : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map
      (continuous_conjugatedSecondStabilizerHom k i).aemeasurable
  letI : Measure.IsMulLeftInvariant ν :=
    MeasureTheory.isMulLeftInvariant_map ψ.toMulHom
      (continuous_conjugatedSecondStabilizerHom k i).measurable
      (surjective_conjugatedSecondStabilizerHom k i)
  have heq :=
    Measure.isMulInvariant_eq_smul_of_compactSpace ν μ
  have hmass := congrArg (fun m : Measure
      (Matrix.specialOrthogonalGroup (Fin (k + 2)) ℝ) =>
        m Set.univ) heq
  have hscalar : Measure.haarScalarFactor ν μ = 1 := by
    simpa using hmass.symm
  simpa [ν, μ, ψ, hscalar] using heq

private lemma map_conjugation_coordinateStabilizerMeasure
    (k : ℕ) (i : Fin (k + 3)) :
    let Q :=
      secondToCoordinateRotation (k + 3) (by omega) i
    Measure.map
        (fun V : Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ =>
          Q * V * Q⁻¹)
        (coordinateStabilizerMeasure (secondCoordinateIndex k)) =
      coordinateStabilizerMeasure i := by
  dsimp only
  let Q := secondToCoordinateRotation (k + 3) (by omega) i
  let μ := HDP.Chapter5.specialOrthogonalHaarMeasure (k + 2)
  let ψ := conjugatedSecondStabilizerHom k i
  unfold coordinateStabilizerMeasure
  rw [Measure.map_map (by fun_prop)
    (continuous_coordinateStabilizerHom
      (secondCoordinateIndex k)).measurable]
  have hfun :
      (fun V : Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ =>
          Q * V * Q⁻¹) ∘
          coordinateStabilizerHom (secondCoordinateIndex k) =
        coordinateStabilizerHom i ∘ ψ := by
    funext V
    exact
      (coordinateStabilizerHom_conjugatedSecondStabilizerHom
        k i V).symm
  rw [hfun, ← Measure.map_map]
  · rw [map_conjugatedSecondStabilizerHom_haar]
  · exact (continuous_coordinateStabilizerHom i).measurable
  · exact (continuous_conjugatedSecondStabilizerHom k i).measurable

private lemma rightAverage_coordinate_eq_second_conjugate
    (k : ℕ) (i : Fin (k + 3))
    (f : Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ → ℝ)
    (hf : Continuous f)
    (U : Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ) :
    let Q :=
      secondToCoordinateRotation (k + 3) (by omega) i
    rightAverage (coordinateStabilizerMeasure i) f U =
      rightAverage
        (coordinateStabilizerMeasure (secondCoordinateIndex k))
        (fun W => f (W * Q⁻¹)) (U * Q) := by
  dsimp only
  let Q := secondToCoordinateRotation (k + 3) (by omega) i
  unfold rightAverage
  rw [← map_conjugation_coordinateStabilizerMeasure k i]
  have hconj :
      Continuous
        (fun V : Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ =>
          Q * V * Q⁻¹) := by
    fun_prop
  have hint :
      Continuous
        (fun V : Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ =>
          f (U * V)) := by
    fun_prop
  rw [integral_map hconj.aemeasurable hint.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards []
  intro V
  dsimp only [Q]
  congr 1
  group

private lemma boltzmannEntropy_comp_mul_right_specialOrthogonal
    (n : ℕ)
    (f : Matrix.specialOrthogonalGroup (Fin n) ℝ → ℝ)
    (hf : Continuous f)
    (Q : Matrix.specialOrthogonalGroup (Fin n) ℝ) :
    boltzmannEntropy
        (HDP.Chapter5.specialOrthogonalHaarMeasure n)
        (fun U => f (U * Q)) =
      boltzmannEntropy
        (HDP.Chapter5.specialOrthogonalHaarMeasure n) f := by
  let μ := HDP.Chapter5.specialOrthogonalHaarMeasure n
  have hmap :
      Measure.map
          (fun U : Matrix.specialOrthogonalGroup (Fin n) ℝ => U * Q) μ =
        μ :=
    HDP.Appendix.probabilityHaar_map_mul_right_eq_self μ Q
  have hright :
      Continuous
        (fun V : Matrix.specialOrthogonalGroup (Fin n) ℝ => V * Q) := by
    fun_prop
  have hav :
      (∫ U, f (U * Q) ∂μ) = ∫ U, f U ∂μ := by
    calc
      (∫ U, f (U * Q) ∂μ) =
          ∫ U, f U
            ∂Measure.map
              (fun V : Matrix.specialOrthogonalGroup (Fin n) ℝ => V * Q)
              μ :=
        (integral_map hright.aemeasurable
          hf.aestronglyMeasurable).symm
      _ = _ := by rw [hmap]
  have havlog :
      (∫ U, f (U * Q) * Real.log (f (U * Q)) ∂μ) =
        ∫ U, f U * Real.log (f U) ∂μ := by
    calc
      (∫ U, f (U * Q) * Real.log (f (U * Q)) ∂μ) =
          ∫ U, f U * Real.log (f U)
            ∂Measure.map
              (fun V : Matrix.specialOrthogonalGroup (Fin n) ℝ => V * Q)
              μ :=
        (integral_map hright.aemeasurable
          (Real.continuous_mul_log.comp hf).aestronglyMeasurable).symm
      _ = _ := by rw [hmap]
  unfold boltzmannEntropy
  rw [hav, havlog]

private noncomputable def rightTranslatedAmbient
    {n : ℕ} (H : FrobeniusEuclidean n → ℝ)
    (Q : Matrix.specialOrthogonalGroup (Fin n) ℝ) :
    FrobeniusEuclidean n → ℝ :=
  H ∘ vectorizedRightMulCLM Q⁻¹.1

private lemma differentiable_rightTranslatedAmbient
    {n : ℕ} (H : FrobeniusEuclidean n → ℝ)
    (Q : Matrix.specialOrthogonalGroup (Fin n) ℝ)
    (hHdiff : Differentiable ℝ H) :
    Differentiable ℝ (rightTranslatedAmbient H Q) :=
  hHdiff.comp (vectorizedRightMulCLM Q⁻¹.1).differentiable

private lemma fderiv_rightTranslatedAmbient
    {n : ℕ} (H : FrobeniusEuclidean n → ℝ)
    (Q : Matrix.specialOrthogonalGroup (Fin n) ℝ)
    (hHdiff : Differentiable ℝ H)
    (y : FrobeniusEuclidean n) :
    fderiv ℝ (rightTranslatedAmbient H Q) y =
      (fderiv ℝ H (vectorizedRightMulCLM Q⁻¹.1 y)).comp
        (vectorizedRightMulCLM Q⁻¹.1) := by
  exact
    ((hHdiff _).hasFDerivAt.comp y
      (vectorizedRightMulCLM Q⁻¹.1).hasFDerivAt).fderiv

private lemma continuous_fderiv_rightTranslatedAmbient
    {n : ℕ} (H : FrobeniusEuclidean n → ℝ)
    (Q : Matrix.specialOrthogonalGroup (Fin n) ℝ)
    (hHdiff : Differentiable ℝ H)
    (hHderiv : Continuous (fderiv ℝ H)) :
    Continuous (fderiv ℝ (rightTranslatedAmbient H Q)) := by
  rw [show
      fderiv ℝ (rightTranslatedAmbient H Q) =
        fun y =>
          (fderiv ℝ H (vectorizedRightMulCLM Q⁻¹.1 y)).comp
            (vectorizedRightMulCLM Q⁻¹.1) by
    funext y
    exact fderiv_rightTranslatedAmbient H Q hHdiff y]
  exact
    (hHderiv.comp
      (vectorizedRightMulCLM Q⁻¹.1).continuous).clm_comp
        continuous_const

private lemma ambientGradientMatrix_rightTranslatedAmbient
    {n : ℕ} (H : FrobeniusEuclidean n → ℝ)
    (Q : Matrix.specialOrthogonalGroup (Fin n) ℝ)
    (hHdiff : Differentiable ℝ H)
    (y : FrobeniusEuclidean n) :
    ambientGradientMatrix (rightTranslatedAmbient H Q) y =
      ambientGradientMatrix H
          (vectorizedRightMulCLM Q⁻¹.1 y) *
        Q.1 := by
  classical
  ext a b
  let E : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.single a b 1
  calc
    ambientGradientMatrix (rightTranslatedAmbient H Q) y a b =
        fderiv ℝ (rightTranslatedAmbient H Q) y
          (HDP.gaussianMatrixVectorize E) := by
      rw [fderiv_vectorize_eq_sum_ambientGradientMatrix]
      simp only [E, Matrix.single, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_eq_single a]
      · rw [Finset.sum_eq_single b]
        · simp
        · intro q _ hq
          simp [hq, Ne.symm hq]
        · simp
      · intro p _ hp
        simp [hp, Ne.symm hp]
      · simp
    _ =
        fderiv ℝ H (vectorizedRightMulCLM Q⁻¹.1 y)
          (vectorizedRightMulCLM Q⁻¹.1
            (HDP.gaussianMatrixVectorize E)) := by
      rw [fderiv_rightTranslatedAmbient H Q hHdiff]
      rfl
    _ =
        fderiv ℝ H (vectorizedRightMulCLM Q⁻¹.1 y)
          (HDP.gaussianMatrixVectorize (E * Q⁻¹.1)) := by
      rfl
    _ =
        ∑ p : Fin n, ∑ q : Fin n,
          ambientGradientMatrix H
              (vectorizedRightMulCLM Q⁻¹.1 y) p q *
            (E * Q⁻¹.1) p q := by
      rw [fderiv_vectorize_eq_sum_ambientGradientMatrix]
    _ =
        (ambientGradientMatrix H
            (vectorizedRightMulCLM Q⁻¹.1 y) * Q.1) a b := by
      have hQinv : Q⁻¹.1 = Q.1ᵀ := by
        rfl
      have hEmul (p q : Fin n) :
          (E * Q⁻¹.1) p q =
            if p = a then Q⁻¹.1 b q else 0 := by
        rw [Matrix.mul_apply]
        by_cases hp : p = a
        · subst p
          simp [E, Matrix.single]
        · simp [E, Matrix.single, hp, Ne.symm hp]
      simp_rw [hEmul]
      rw [Finset.sum_eq_single a]
      · simp [hQinv, Matrix.mul_apply]
      · intro p _ hp
        simp [hp]
      · simp

private lemma rightAmbientMatrix_rightTranslatedAmbient
    {n : ℕ} (H : FrobeniusEuclidean n → ℝ)
    (Q : Matrix.specialOrthogonalGroup (Fin n) ℝ)
    (hHdiff : Differentiable ℝ H)
    (U : Matrix.specialOrthogonalGroup (Fin n) ℝ) :
    rightAmbientMatrix (rightTranslatedAmbient H Q) (U * Q) =
      Q⁻¹.1 * rightAmbientMatrix H U * Q.1 := by
  have hpoint :
      vectorizedRightMulCLM Q⁻¹.1
          (HDP.gaussianMatrixVectorize (U * Q).1) =
        HDP.gaussianMatrixVectorize U.1 := by
    simp only [vectorizedRightMulCLM_apply,
      HDP.gaussianMatrixUnvectorize_vectorize]
    congr 1
    have hgroup :
        (U * Q) * Q⁻¹ = U := by group
    exact congrArg Subtype.val hgroup
  unfold rightAmbientMatrix
  rw [ambientGradientMatrix_rightTranslatedAmbient H Q hHdiff,
    hpoint]
  change
    (U.1 * Q.1)ᵀ *
        (ambientGradientMatrix H
            (HDP.gaussianMatrixVectorize U.1) * Q.1) =
      Q⁻¹.1 *
        (U.1ᵀ *
          ambientGradientMatrix H
            (HDP.gaussianMatrixVectorize U.1)) * Q.1
  rw [Matrix.transpose_mul]
  change
    Q⁻¹.1 * U.1ᵀ *
        (ambientGradientMatrix H
            (HDP.gaussianMatrixVectorize U.1) * Q.1) =
      Q⁻¹.1 *
        (U.1ᵀ *
          ambientGradientMatrix H
            (HDP.gaussianMatrixVectorize U.1)) * Q.1
  noncomm_ring

private lemma tangentGradient_eq_half_smul_sub_transpose
    {n : ℕ} (H : FrobeniusEuclidean n → ℝ)
    (U : Matrix.specialOrthogonalGroup (Fin n) ℝ) :
    tangentGradient H U =
      (1 / 2 : ℝ) •
        (rightAmbientMatrix H U - (rightAmbientMatrix H U)ᵀ) := by
  ext a b
  simp [tangentGradient]
  ring

private lemma tangentGradient_rightTranslatedAmbient
    {n : ℕ} (H : FrobeniusEuclidean n → ℝ)
    (Q : Matrix.specialOrthogonalGroup (Fin n) ℝ)
    (hHdiff : Differentiable ℝ H)
    (U : Matrix.specialOrthogonalGroup (Fin n) ℝ) :
    tangentGradient (rightTranslatedAmbient H Q) (U * Q) =
      Q⁻¹.1 * tangentGradient H U * Q.1 := by
  rw [tangentGradient_eq_half_smul_sub_transpose,
    rightAmbientMatrix_rightTranslatedAmbient H Q hHdiff,
    tangentGradient_eq_half_smul_sub_transpose]
  have hQt : Q.1ᵀ = Q⁻¹.1 := by rfl
  have hQinvt : Q⁻¹.1ᵀ = Q.1 := by
    rw [hQt.symm, Matrix.transpose_transpose]
  rw [Matrix.transpose_mul, Matrix.transpose_mul, hQt, hQinvt]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
    Matrix.smul_mul]
  noncomm_ring

private lemma rowSquareEnergy_mul_special
    {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℝ)
    (Q : Matrix.specialOrthogonalGroup (Fin n) ℝ)
    (i : Fin n) :
    rowSquareEnergy (Y * Q.1) i = rowSquareEnergy Y i := by
  let A : Matrix (Fin 1) (Fin n) ℝ :=
    fun _ q => Y i q
  have hOne :
      (1 : Matrix (Fin 1) (Fin 1) ℝ) ∈
        Matrix.orthogonalGroup (Fin 1) ℝ := by
    simp
  have hnorm :=
    (HDP.Chapter4.orthogonalInvariance A
      (1 : Matrix (Fin 1) (Fin 1) ℝ) Q.1 hOne Q.2.1).1
  have hsq := congrArg (fun x : ℝ => x ^ 2) hnorm
  simpa [A, rowSquareEnergy, HDP.matrixFrobeniusNorm_sq,
    Matrix.mul_apply] using hsq

private lemma rowSquareEnergy_conjugate_secondToCoordinate
    (k : ℕ) (i : Fin (k + 3))
    (Y : Matrix (Fin (k + 3)) (Fin (k + 3)) ℝ) :
    let Q :=
      secondToCoordinateRotation (k + 3) (by omega) i
    rowSquareEnergy (Q⁻¹.1 * Y * Q.1) (secondCoordinateIndex k) =
      rowSquareEnergy Y i := by
  dsimp only
  let s := secondCoordinateIndex k
  let Q := secondToCoordinateRotation (k + 3) (by omega) i
  have hQ :
      Q.1 *ᵥ
          (fun p =>
            (coordinateSpherePoint s :
              EuclideanSpace ℝ (Fin (k + 3))) p) =
        fun p =>
          (coordinateSpherePoint i :
            EuclideanSpace ℝ (Fin (k + 3))) p := by
    have h :=
      secondToCoordinateRotation_action (k + 3) (by omega) i
    ext p
    have hp := congrFun (congrArg WithLp.ofLp h) p
    change
      (Q.1 *ᵥ
          (fun q =>
            (coordinateSpherePoint s :
              EuclideanSpace ℝ (Fin (k + 3))) q)) p =
        (coordinateSpherePoint i :
          EuclideanSpace ℝ (Fin (k + 3))) p at hp
    exact hp
  have hQcol (p : Fin (k + 3)) :
      Q.1 p s = if p = i then 1 else 0 := by
    have hp := congrFun hQ p
    simpa [coordinateSpherePoint, Matrix.mulVec, dotProduct] using hp
  have hentry (j : Fin (k + 3)) :
      (Q⁻¹.1 * Y * Q.1) s j = (Y * Q.1) i j := by
    have hQinv : Q⁻¹.1 = Q.1ᵀ := by rfl
    simp only [Matrix.mul_apply, hQinv,
      Matrix.transpose_apply, hQcol]
    apply Finset.sum_congr rfl
    intro q _
    congr 1
    rw [Finset.sum_eq_single i]
    · simp
    · intro p _ hp
      simp [hp]
    · simp
  rw [show
      rowSquareEnergy (Q⁻¹.1 * Y * Q.1) s =
        rowSquareEnergy (Y * Q.1) i by
    unfold rowSquareEnergy
    apply Finset.sum_congr rfl
    intro j _
    rw [hentry]]
  exact rowSquareEnergy_mul_special Y Q i

private lemma horizontalSquareEnergy_conjugate_secondToCoordinate
    (k : ℕ) (i : Fin (k + 3))
    (Y : Matrix (Fin (k + 3)) (Fin (k + 3)) ℝ) :
    let Q :=
      secondToCoordinateRotation (k + 3) (by omega) i
    horizontalSquareEnergy (Q⁻¹.1 * Y * Q.1)
        (secondCoordinateIndex k) =
      horizontalSquareEnergy Y i := by
  dsimp only
  unfold horizontalSquareEnergy
  rw [rowSquareEnergy_conjugate_secondToCoordinate k i Y]

theorem coordinate_quotient_entropy_le_ambient_six
    (k : ℕ) (H : FrobeniusEuclidean (k + 3) → ℝ)
    (hHdiff : Differentiable ℝ H)
    (hHderiv : Continuous (fderiv ℝ H))
    (i : Fin (k + 3)) :
    boltzmannEntropy
        (HDP.Chapter5.specialOrthogonalHaarMeasure (k + 3))
        (rightAverage
          (coordinateStabilizerMeasure i)
          (fun W => H (HDP.gaussianMatrixVectorize W.1) ^ 2)) ≤
      2 * (6 / (((k + 3 : ℕ) : ℝ))) *
        ∫ U : Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ,
          horizontalSquareEnergy (tangentGradient H U) i
          ∂HDP.Chapter5.specialOrthogonalHaarMeasure (k + 3) := by
  let G := Matrix.specialOrthogonalGroup (Fin (k + 3)) ℝ
  let μ := HDP.Chapter5.specialOrthogonalHaarMeasure (k + 3)
  let s := secondCoordinateIndex k
  let Q := secondToCoordinateRotation (k + 3) (by omega) i
  let K : FrobeniusEuclidean (k + 3) → ℝ :=
    rightTranslatedAmbient H Q
  let fH : G → ℝ :=
    fun W => H (HDP.gaussianMatrixVectorize W.1) ^ 2
  let fK : G → ℝ :=
    fun W => K (HDP.gaussianMatrixVectorize W.1) ^ 2
  let qH : G → ℝ :=
    rightAverage (coordinateStabilizerMeasure i) fH
  let qK : G → ℝ :=
    rightAverage (coordinateStabilizerMeasure s) fK
  let eH : G → ℝ :=
    fun U => horizontalSquareEnergy (tangentGradient H U) i
  let eK : G → ℝ :=
    fun U => horizontalSquareEnergy (tangentGradient K U) s
  have hKdiff : Differentiable ℝ K :=
    differentiable_rightTranslatedAmbient H Q hHdiff
  have hKderiv : Continuous (fderiv ℝ K) :=
    continuous_fderiv_rightTranslatedAmbient H Q hHdiff hHderiv
  have hfK : Continuous fK :=
    (hKdiff.continuous.comp
      (continuous_gaussianMatrixVectorize.comp
        continuous_subtype_val)).pow 2
  have hqK : Continuous qK :=
    continuous_rightAverage_coordinateStabilizer s hfK
  have hqpoint (U : G) : qH U = qK (U * Q) := by
    have h :=
      rightAverage_coordinate_eq_second_conjugate
        k i fH
          ((hHdiff.continuous.comp
            (continuous_gaussianMatrixVectorize.comp
              continuous_subtype_val)).pow 2)
        U
    simpa [qH, qK, fH, fK, K, rightTranslatedAmbient,
      vectorizedRightMulCLM_apply] using h
  have hEntropy :
      boltzmannEntropy μ qH = boltzmannEntropy μ qK := by
    rw [show qH = fun U => qK (U * Q) by
      funext U
      exact hqpoint U]
    exact
      boltzmannEntropy_comp_mul_right_specialOrthogonal
        (k + 3) qK hqK Q
  have heK : Continuous eK :=
    continuous_tangentFieldHorizontalEnergy
      (continuous_tangentGradient hKderiv) s
  have hepoint (U : G) : eK (U * Q) = eH U := by
    dsimp only [eK, eH, K]
    rw [tangentGradient_rightTranslatedAmbient H Q hHdiff U]
    exact
      horizontalSquareEnergy_conjugate_secondToCoordinate
        k i (tangentGradient H U)
  have hEnergy : (∫ U, eK U ∂μ) = ∫ U, eH U ∂μ := by
    have hmap :
        Measure.map (fun U : G => U * Q) μ = μ :=
      HDP.Appendix.probabilityHaar_map_mul_right_eq_self μ Q
    have hshift : (∫ U, eK (U * Q) ∂μ) = ∫ U, eK U ∂μ := by
      calc
        (∫ U, eK (U * Q) ∂μ) =
            ∫ U, eK U
              ∂Measure.map (fun V : G => V * Q) μ :=
          (integral_map (by fun_prop) heK.aestronglyMeasurable).symm
        _ = _ := by rw [hmap]
    calc
      (∫ U, eK U ∂μ) = ∫ U, eK (U * Q) ∂μ := hshift.symm
      _ = ∫ U, eH U ∂μ := by
        apply integral_congr_ae
        filter_upwards []
        intro U
        exact hepoint U
  have hsecond :=
    secondCoordinate_quotient_entropy_le_ambient_six
      k K hKdiff hKderiv
  simpa only [G, μ, s, K, fH, fK, qH, qK, eH, eK] using
    (show
      boltzmannEntropy μ qH ≤
        2 * (6 / (((k + 3 : ℕ) : ℝ))) * ∫ U, eH U ∂μ by
      calc
        boltzmannEntropy μ qH = boltzmannEntropy μ qK := hEntropy
        _ ≤
            2 * (6 / (((k + 3 : ℕ) : ℝ))) *
              ∫ U, eK U ∂μ := hsecond
        _ =
            2 * (6 / (((k + 3 : ℕ) : ℝ))) *
              ∫ U, eH U ∂μ := by rw [hEnergy])

end

end HDP.Appendix.SpecialOrthogonal
