import HighDimensionalProbability.Prelude.RandomMatrix
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.ProductMeasure

/-!
# Canonical finite standard Gaussian matrices

This source-neutral file exposes the product law of a real matrix with
independent standard Gaussian entries, its Euclidean vectorization, and the
linear action on a fixed vector.  The vectorization is the bridge to Mathlib's
`stdGaussian`; all Gaussianity and independence statements below are proved
through that bridge.
-/

open MeasureTheory ProbabilityTheory InnerProductSpace WithLp
open scoped BigOperators RealInnerProductSpace ENNReal

namespace HDP

noncomputable section

/-- Product law of an `m × n` matrix of independent standard real Gaussian
entries. -/
abbrev stdGaussianMatrixMeasure (m n : ℕ) :
    Measure (Matrix (Fin m) (Fin n) ℝ) :=
  Measure.pi (fun _ : Fin m =>
    Measure.pi (fun _ : Fin n => gaussianReal 0 1))

/-- The canonical finite Gaussian matrix law is a probability measure. -/
instance isProbabilityMeasure_stdGaussianMatrixMeasure (m n : ℕ) :
    IsProbabilityMeasure (stdGaussianMatrixMeasure m n) := by
  unfold stdGaussianMatrixMeasure
  exact Measure.pi.instIsProbabilityMeasure _

/-- Row-major scalar flattening of a finite matrix.

**Lean implementation helper.** -/
def gaussianMatrixFlatten {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) : Fin m × Fin n → ℝ :=
  fun p => A p.1 p.2

/-- Row-major Euclidean vectorization of a finite matrix.

**Lean implementation helper.** -/
def gaussianMatrixVectorize {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    EuclideanSpace ℝ (Fin m × Fin n) :=
  WithLp.toLp 2 (gaussianMatrixFlatten A)

/-- Inverse row-major Euclidean vectorization.

**Lean implementation helper.** -/
def gaussianMatrixUnvectorize {m n : ℕ}
    (g : EuclideanSpace ℝ (Fin m × Fin n)) :
    Matrix (Fin m) (Fin n) ℝ :=
  fun i j => WithLp.ofLp g (i, j)

/-- Unvectorizing the vectorization of a finite real matrix recovers the original matrix.

**Lean implementation helper.** -/
@[simp]
theorem gaussianMatrixUnvectorize_vectorize {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    gaussianMatrixUnvectorize (gaussianMatrixVectorize A) = A := by
  rfl

/-- Vectorizing an unvectorized Euclidean vector recovers the original vector.

**Lean implementation helper.** -/
@[simp]
theorem gaussianMatrixVectorize_unvectorize {m n : ℕ}
    (g : EuclideanSpace ℝ (Fin m × Fin n)) :
    gaussianMatrixVectorize (gaussianMatrixUnvectorize g) = g := by
  apply WithLp.ofLp_injective
  rfl

/-- Matrix vectorization is genuinely measurable.

**Lean implementation helper.** -/
theorem gaussianMatrixVectorize_measurable {m n : ℕ} :
    Measurable (gaussianMatrixVectorize :
      Matrix (Fin m) (Fin n) ℝ ->
        EuclideanSpace ℝ (Fin m × Fin n)) := by
  have hflat : Measurable (gaussianMatrixFlatten :
      Matrix (Fin m) (Fin n) ℝ -> (Fin m × Fin n -> ℝ)) := by
    apply measurable_pi_lambda
    intro p
    exact (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)
  change Measurable ((WithLp.toLp 2) ∘ gaussianMatrixFlatten)
  exact (PiLp.continuous_toLp (p := (2 : ℝ≥0∞))
    (fun _ : Fin m × Fin n => ℝ)).measurable.comp hflat

/-- Matrix unvectorization is genuinely measurable.

**Lean implementation helper.** -/
theorem gaussianMatrixUnvectorize_measurable {m n : ℕ} :
    Measurable (gaussianMatrixUnvectorize :
      EuclideanSpace ℝ (Fin m × Fin n) ->
        Matrix (Fin m) (Fin n) ℝ) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  exact (PiLp.continuous_apply (p := (2 : ℝ≥0∞))
    (fun _ : Fin m × Fin n => ℝ) (i, j)).measurable

/-- Vectorizing the product Gaussian matrix gives Mathlib's canonical
standard Gaussian measure on the Frobenius Euclidean space.

**Lean implementation helper.** -/
theorem gaussianMatrixVectorize_hasLaw (m n : ℕ) :
    HasLaw gaussianMatrixVectorize
      (stdGaussian (EuclideanSpace ℝ (Fin m × Fin n)))
      (stdGaussianMatrixMeasure m n) := by
  refine ⟨gaussianMatrixVectorize_measurable.aemeasurable, ?_⟩
  have hflat :
      (stdGaussianMatrixMeasure m n).map gaussianMatrixFlatten =
        Measure.pi (fun _ : Fin m × Fin n => gaussianReal 0 1) := by
    change (Measure.pi (fun _ : Fin m =>
      Measure.pi (fun _ : Fin n => gaussianReal 0 1))).map
        gaussianMatrixFlatten = _
    have h := Measure.infinitePi_map_curry_symm
      (fun _ : Fin m => fun _ : Fin n => gaussianReal 0 1)
    have hfun : gaussianMatrixFlatten =
        ⇑(MeasurableEquiv.curry (Fin m) (Fin n) ℝ).symm := rfl
    rw [hfun]
    simp only [Measure.infinitePi_eq_pi] at h
    convert h using 1
    congr 2
  rw [show gaussianMatrixVectorize =
      (WithLp.toLp 2) ∘ gaussianMatrixFlatten by rfl,
    ← Measure.map_map (by fun_prop)
      (by
        apply measurable_pi_lambda
        intro p
        exact (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)),
    hflat, map_pi_eq_stdGaussian]

/-- Action of a finite matrix on a Euclidean vector.

**Lean implementation helper.** -/
def gaussianMatrixAction {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun i => ∑ j, A i j * x j)

/-- The `i`th coordinate of a matrix action is the dot product of row `i` with the input vector.

**Lean implementation helper.** -/
@[simp]
theorem gaussianMatrixAction_apply {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin m) :
    gaussianMatrixAction A x i = ∑ j, A i j * x j :=
  rfl

/-- Compatibility with Mathlib's Euclidean matrix linear map.

**Lean implementation helper.** -/
theorem gaussianMatrixAction_eq_toEuclideanLin {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    gaussianMatrixAction A x = A.toEuclideanLin x := by
  apply WithLp.ofLp_injective
  ext i
  simp [gaussianMatrixAction, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]

/-- The fixed-direction matrix action as a continuous linear map from the
Frobenius Euclidean space.

**Lean implementation helper.** -/
def gaussianMatrixActionLinearMap {m n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin m × Fin n) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin m) where
  toFun g := gaussianMatrixAction (gaussianMatrixUnvectorize g) x
  map_add' g h := by
    apply WithLp.ofLp_injective
    ext i
    simp [gaussianMatrixAction, gaussianMatrixUnvectorize,
      add_mul, Finset.sum_add_distrib]
  map_smul' c g := by
    apply WithLp.ofLp_injective
    ext i
    simp [gaussianMatrixAction, gaussianMatrixUnvectorize,
      Finset.mul_sum, mul_assoc]

/-- Continuous version of `gaussianMatrixActionLinearMap`.

**Lean implementation helper.** -/
def gaussianMatrixActionCLM {m n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin m × Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin m) :=
  LinearMap.toContinuousLinearMap (gaussianMatrixActionLinearMap x)

/-- The continuous fixed-direction matrix-action map unvectorizes its input and applies the resulting matrix to the fixed vector.

**Lean implementation helper.** -/
@[simp]
theorem gaussianMatrixActionCLM_apply {m n : ℕ}
    (x : EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin m × Fin n)) :
    gaussianMatrixActionCLM x g =
      gaussianMatrixAction (gaussianMatrixUnvectorize g) x :=
  rfl

/-- The continuous linear matrix-action map applied to a vectorized matrix agrees with ordinary matrix action.

**Lean implementation helper.** -/
@[simp]
theorem gaussianMatrixActionCLM_vectorize {m n : ℕ}
    (x : EuclideanSpace ℝ (Fin n))
    (A : Matrix (Fin m) (Fin n) ℝ) :
    gaussianMatrixActionCLM x (gaussianMatrixVectorize A) =
      gaussianMatrixAction A x := by
  rw [gaussianMatrixActionCLM_apply,
    gaussianMatrixUnvectorize_vectorize]

/-- The action on a fixed vector is genuinely measurable in the matrix.

**Lean implementation helper.** -/
theorem gaussianMatrixAction_measurable {m n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) :
    Measurable (fun A : Matrix (Fin m) (Fin n) ℝ =>
      gaussianMatrixAction A x) := by
  have hfun : (fun A : Matrix (Fin m) (Fin n) ℝ =>
      gaussianMatrixAction A x) =
      gaussianMatrixActionCLM x ∘ gaussianMatrixVectorize := by
    funext A
    exact (gaussianMatrixActionCLM_vectorize x A).symm
  rw [hfun]
  exact (gaussianMatrixActionCLM x).continuous.measurable.comp
    gaussianMatrixVectorize_measurable

/-- Rank-one coefficient vector representing the scalar matrix action
`⟪u, A x⟫`.

**Lean implementation helper.** -/
def gaussianMatrixCoefficient {m n : ℕ}
    (x : EuclideanSpace ℝ (Fin n))
    (u : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin m × Fin n) :=
  WithLp.toLp 2 (fun p => u p.1 * x p.2)

/-- The inner product of two Gaussian matrix coefficient vectors factors into the product of the row- and column-space inner products.

**Lean implementation helper.** -/
theorem gaussianMatrixCoefficient_inner {m n : ℕ}
    (x y : EuclideanSpace ℝ (Fin n))
    (u v : EuclideanSpace ℝ (Fin m)) :
    inner ℝ (gaussianMatrixCoefficient x u)
        (gaussianMatrixCoefficient y v) =
      inner ℝ u v * inner ℝ x y := by
  change (∑ p : Fin m × Fin n,
      (v p.1 * y p.2) * (u p.1 * x p.2)) =
    (∑ i, v i * u i) * ∑ j, y j * x j
  rw [Fintype.sum_prod_type]
  calc
    (∑ i, ∑ j, (v i * y j) * (u i * x j)) =
        ∑ i, (v i * u i) * ∑ j, y j * x j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (∑ i, v i * u i) * ∑ j, y j * x j := by
      rw [Finset.sum_mul]

/-- Pairing a matrix action with an output vector equals pairing the vectorized matrix with the associated coefficient vector.

**Lean implementation helper.** -/
theorem inner_gaussianMatrixAction {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n))
    (u : EuclideanSpace ℝ (Fin m)) :
    inner ℝ u (gaussianMatrixAction A x) =
      inner ℝ (gaussianMatrixCoefficient x u)
        (gaussianMatrixVectorize A) := by
  simp only [gaussianMatrixAction, gaussianMatrixCoefficient,
    gaussianMatrixVectorize, gaussianMatrixFlatten,
    PiLp.inner_apply, Real.inner_apply]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The fixed-direction action is the corresponding linear image of the
canonical standard Gaussian on the vectorized matrix space.

**Lean implementation helper.** -/
theorem gaussianMatrixAction_map_eq_linearImage (m n : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) :
    (stdGaussianMatrixMeasure m n).map
        (fun A => gaussianMatrixAction A x) =
      (stdGaussian (EuclideanSpace ℝ (Fin m × Fin n))).map
        (gaussianMatrixActionCLM x) := by
  calc
    (stdGaussianMatrixMeasure m n).map
        (fun A => gaussianMatrixAction A x) =
        (stdGaussianMatrixMeasure m n).map
          (gaussianMatrixActionCLM x ∘ gaussianMatrixVectorize) := by
      rfl
    _ = ((stdGaussianMatrixMeasure m n).map gaussianMatrixVectorize).map
        (gaussianMatrixActionCLM x) := by
      rw [← Measure.map_map
        (gaussianMatrixActionCLM x).continuous.measurable
        gaussianMatrixVectorize_measurable]
    _ = (stdGaussian (EuclideanSpace ℝ (Fin m × Fin n))).map
        (gaussianMatrixActionCLM x) := by
      rw [(gaussianMatrixVectorize_hasLaw m n).map_eq]

/-- Every fixed-direction action of a standard Gaussian matrix is a Gaussian
random vector.

**Lean implementation helper.** -/
theorem gaussianMatrixAction_hasGaussianLaw (m n : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) :
    HasGaussianLaw (fun A : Matrix (Fin m) (Fin n) ℝ =>
      gaussianMatrixAction A x) (stdGaussianMatrixMeasure m n) := by
  have hvec : HasGaussianLaw gaussianMatrixVectorize
      (stdGaussianMatrixMeasure m n) :=
    (gaussianMatrixVectorize_hasLaw m n).hasGaussianLaw
  have h := hvec.map_fun (gaussianMatrixActionCLM x)
  exact h.congr (ae_of_all _ fun A =>
    gaussianMatrixActionCLM_vectorize x A)

/-- Two fixed-direction actions form a jointly Gaussian random vector.

**Lean implementation helper.** -/
theorem gaussianMatrixAction_joint_hasGaussianLaw (m n : ℕ)
    (x y : EuclideanSpace ℝ (Fin n)) :
    HasGaussianLaw
      (fun A : Matrix (Fin m) (Fin n) ℝ =>
        (gaussianMatrixAction A x, gaussianMatrixAction A y))
      (stdGaussianMatrixMeasure m n) := by
  have hvec : HasGaussianLaw gaussianMatrixVectorize
      (stdGaussianMatrixMeasure m n) :=
    (gaussianMatrixVectorize_hasLaw m n).hasGaussianLaw
  have h := hvec.map_fun
    ((gaussianMatrixActionCLM x).prod (gaussianMatrixActionCLM y))
  exact h.congr (ae_of_all _ fun A => by
    simp only [ContinuousLinearMap.prod_apply]
    rw [gaussianMatrixActionCLM_vectorize,
      gaussianMatrixActionCLM_vectorize])

/-- Cross-covariance formula for two matrix directions.

**Lean implementation helper.** -/
theorem gaussianMatrixAction_covariance (m n : ℕ)
    (x y : EuclideanSpace ℝ (Fin n))
    (u v : EuclideanSpace ℝ (Fin m)) :
    cov[fun A => inner ℝ u (gaussianMatrixAction A x),
        fun A => inner ℝ v (gaussianMatrixAction A y);
        stdGaussianMatrixMeasure m n] =
      inner ℝ u v * inner ℝ x y := by
  let a := gaussianMatrixCoefficient x u
  let b := gaussianMatrixCoefficient y v
  have hvec := gaussianMatrixVectorize_hasLaw m n
  have hcov := hvec.covariance_fun_comp
    (f := fun g => inner ℝ a g) (g := fun g => inner ℝ b g)
    ((innerSL ℝ a).continuous.measurable.aemeasurable)
    ((innerSL ℝ b).continuous.measurable.aemeasurable)
  have hstd : cov[fun g : EuclideanSpace ℝ (Fin m × Fin n) => inner ℝ a g,
      fun g => inner ℝ b g; stdGaussian (EuclideanSpace ℝ (Fin m × Fin n))] =
      inner ℝ a b := by
    rw [← covarianceBilin_apply_eq_cov
      (ProbabilityTheory.IsGaussian.memLp_two_id :
        MemLp id 2 (stdGaussian (EuclideanSpace ℝ (Fin m × Fin n)))) a b,
      covarianceBilin_stdGaussian]
    rfl
  rw [hstd] at hcov
  simpa only [Function.comp_apply, a, b, inner_gaussianMatrixAction,
    gaussianMatrixCoefficient_inner] using hcov

/-- Orthogonal input directions give independent Gaussian matrix actions.

**Lean implementation helper.** -/
theorem gaussianMatrixAction_indep_of_inner_eq_zero (m n : ℕ)
    (x y : EuclideanSpace ℝ (Fin n))
    (hxy : inner ℝ x y = 0) :
    IndepFun
      (fun A : Matrix (Fin m) (Fin n) ℝ => gaussianMatrixAction A x)
      (fun A : Matrix (Fin m) (Fin n) ℝ => gaussianMatrixAction A y)
      (stdGaussianMatrixMeasure m n) := by
  apply (gaussianMatrixAction_joint_hasGaussianLaw m n x y).indepFun_of_covariance_inner
  intro u v
  rw [gaussianMatrixAction_covariance, hxy, mul_zero]

/-- Scalar image of a standard Gaussian measure.

**Lean implementation helper.** -/
def scaledStdGaussianMeasure
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (c : ℝ) : Measure E :=
  (stdGaussian E).map (c • ContinuousLinearMap.id ℝ E)

instance isGaussian_scaledStdGaussianMeasure
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (c : ℝ) : IsGaussian (scaledStdGaussianMeasure (E := E) c) := by
  unfold scaledStdGaussianMeasure
  exact isGaussian_map_of_measurable (by fun_prop)

instance isProbabilityMeasure_scaledStdGaussianMeasure
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (c : ℝ) : IsProbabilityMeasure (scaledStdGaussianMeasure (E := E) c) := by
  unfold scaledStdGaussianMeasure
  infer_instance

/-- Every centered scaled standard Gaussian measure has vector expectation zero.

**Lean implementation helper.** -/
@[simp]
theorem integral_id_scaledStdGaussianMeasure
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (c : ℝ) :
    ∫ z : E, z ∂scaledStdGaussianMeasure (E := E) c = 0 := by
  rw [scaledStdGaussianMeasure,
    ContinuousLinearMap.integral_id_map
      (ProbabilityTheory.IsGaussian.integrable_id :
        Integrable id (stdGaussian E)),
    integral_id_stdGaussian, map_zero]

/-- Raw Gaussian correlations satisfy `E[U_i V_j]=<u_i,v_j>`, turning the bilinear sum into an expectation.

**Book Equation (3.24).** -/
theorem covarianceBilin_scaledStdGaussianMeasure
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (c : ℝ) (u v : E) :
    covarianceBilin (scaledStdGaussianMeasure (E := E) c) u v =
      c ^ 2 * inner ℝ u v := by
  have hcov : cov[fun z : E => inner ℝ u z,
      fun z => inner ℝ v z; stdGaussian E] = inner ℝ u v := by
    rw [← covarianceBilin_apply_eq_cov
      (ProbabilityTheory.IsGaussian.memLp_two_id :
        MemLp id 2 (stdGaussian E)) u v,
      covarianceBilin_stdGaussian]
    rfl
  rw [covarianceBilin_apply_eq_cov
    (ProbabilityTheory.IsGaussian.memLp_two_id :
      MemLp id 2 (scaledStdGaussianMeasure (E := E) c))]
  rw [scaledStdGaussianMeasure,
    covariance_map_fun (by fun_prop) (by fun_prop) (by fun_prop)]
  simp only [smul_apply, ContinuousLinearMap.id_apply,
    real_inner_smul_right]
  rw [covariance_const_mul_left, covariance_const_mul_right, hcov]
  ring

/-- Exact fixed-direction law: `A x` is a standard Gaussian vector scaled by
`‖x‖`. This includes the degenerate case `x = 0`.

**Lean implementation helper.** -/
theorem gaussianMatrixAction_map_eq_scaledStdGaussian (m n : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) :
    (stdGaussianMatrixMeasure m n).map
        (fun A => gaussianMatrixAction A x) =
      scaledStdGaussianMeasure
        (E := EuclideanSpace ℝ (Fin m)) ‖x‖ := by
  let μx := (stdGaussianMatrixMeasure m n).map
    (fun A => gaussianMatrixAction A x)
  letI : IsGaussian μx :=
    (gaussianMatrixAction_hasGaussianLaw m n x).isGaussian_map
  apply IsGaussian.ext
  · change (∫ z, z ∂μx) = _
    rw [show μx =
        (stdGaussian (EuclideanSpace ℝ (Fin m × Fin n))).map
          (gaussianMatrixActionCLM x) by
      exact gaussianMatrixAction_map_eq_linearImage m n x]
    rw [ContinuousLinearMap.integral_id_map
        (ProbabilityTheory.IsGaussian.integrable_id :
          Integrable id
            (stdGaussian (EuclideanSpace ℝ (Fin m × Fin n)))),
      integral_id_stdGaussian, map_zero]
    simpa only [id_eq] using
      (integral_id_scaledStdGaussianMeasure
        (E := EuclideanSpace ℝ (Fin m)) ‖x‖).symm
  · ext u v
    rw [covarianceBilin_apply_eq_cov
      (ProbabilityTheory.IsGaussian.memLp_two_id : MemLp id 2 μx)]
    change cov[fun z => inner ℝ u z, fun z => inner ℝ v z;
      (stdGaussianMatrixMeasure m n).map
        (fun A => gaussianMatrixAction A x)] = _
    rw [covariance_map_fun (by fun_prop) (by fun_prop)
      (gaussianMatrixAction_measurable x).aemeasurable,
      gaussianMatrixAction_covariance,
      covarianceBilin_scaledStdGaussianMeasure]
    rw [real_inner_self_eq_norm_sq]
    exact mul_comm _ _

/-- `HasLaw` form of the exact fixed-direction scaled-Gaussian identity.

**Lean implementation helper.** -/
theorem gaussianMatrixAction_hasLaw_scaledStdGaussian (m n : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) :
    HasLaw (fun A : Matrix (Fin m) (Fin n) ℝ =>
      gaussianMatrixAction A x)
      (scaledStdGaussianMeasure
        (E := EuclideanSpace ℝ (Fin m)) ‖x‖)
      (stdGaussianMatrixMeasure m n) :=
  ⟨(gaussianMatrixAction_measurable x).aemeasurable,
    gaussianMatrixAction_map_eq_scaledStdGaussian m n x⟩

end

end HDP
