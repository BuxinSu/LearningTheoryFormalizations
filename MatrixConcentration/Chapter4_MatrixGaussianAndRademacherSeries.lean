import MatrixConcentration.Chapter2_MatrixFunctionsAndProbabilityWithMatrices
import MatrixConcentration.Chapter3_MatrixLaplaceTransformMethod
import MatrixConcentration.Appendix_GaussianConcentration
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# Chapter 4: Matrix Gaussian and Rademacher series

This consolidated chapter contains:

* **Book §§4.1 and 4.6:** scalar and matrix mgf lemmas for Rademacher and Gaussian variables;
* **Book §§4.1 and 4.6:** Hermitian and rectangular matrix-series bounds;
* **Book §4.6:** unbounded master inequalities and Gaussian matrix series;
* **Book §§4.1 and 4.6:** scalar comparisons, sharpness, and Gaussian concentration;
* **Book §§4.2–4.4:** diagonal examples and random Toeplitz matrix estimates.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# Gaussian × matrix and Rademacher × matrix: mgf and cgf (Tropp §4.6, Lemmas 4.6.2–4.6.3)

* `gaussian_matrix_mgf`/`gaussian_matrix_cgf` — **Book Lemma 4.6.2**
  (C4-14): `𝔼 e^{γθA} = e^{θ²A²/2}` and
  `log 𝔼 e^{γθA} = (θ²/2)A²` for a standard normal `γ` and fixed Hermitian `A`.
  The source proves this through the Gaussian moment series; here the equivalent
  eigenbasis route is used (Definition 2.1.2/`diagMap`): the matrix mgf is the
  `diagMap`-transport of the *scalar* Gaussian mgf at the eigenvalues
  (Mathlib correspondence `ProbabilityTheory.mgf_gaussianReal`) — the same
  computation, organized through the spectral decomposition instead of the series;
  the equivalence is documented in the proof audit;
* `rademacher_matrix_mgf`, `rademacher_matrix_mgf_le`, `rademacher_matrix_cgf_le` —
  **Book Lemma 4.6.3** (C4-15): `𝔼 e^{ϱθA} = cosh(θA) ≼ e^{θ²A²/2}`
  and `log 𝔼 e^{ϱθA} ≼ (θ²/2)A²`, via the Transfer Rule (2.1.14) exactly as in the
  source; the scalar ingredient (4.6.6) `cosh a ≤ e^{a²/2}` is Mathlib's
  `Real.cosh_le_exp_half_sq` (Mathlib correspondence — the source's factorial
  comparison `(2q)! ≥ 2^q q!` is internal to that proof);
* cfc/`diagMap` toolkit (H): `diagMap_eigenvalues`, `smul_eq_cfc`, `smul_cfc`,
  `exp_cfc`, `cfc_apply_entry`, and the scalar-modulator expectation exchange
  `expectation_cfc_modulated`.
-/

namespace MatrixConcentration

open Matrix Finset MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {A : Matrix n n ℂ}

section CfcToolkit

/-- Lean implementation helper: `diagMap` at the eigenvalues recovers the matrix
(the spectral decomposition (2.1.3) read backwards). -/
lemma diagMap_eigenvalues (hA : A.IsHermitian) :
    diagMap hA hA.eigenvalues = A := by
  rw [diagMap_apply]
  exact (spectral_decomposition hA).symm

/-- Lean implementation helper: real scalar multiples as standard matrix functions,
`s•A = cfc (s·x) A`. -/
lemma smul_eq_cfc (hA : A.IsHermitian) (s : ℝ) :
    s • A = cfc (fun x : ℝ => s * x) A := by
  have h1 : s • A = diagMap hA (s • hA.eigenvalues) := by
    rw [map_smul, diagMap_eigenvalues]
  rw [h1, show (s • hA.eigenvalues) = fun i => (fun x : ℝ => s * x) (hA.eigenvalues i)
    from rfl]
  exact diagMap_comp_eigenvalues hA _

/-- Lean implementation helper: scalars move through `cfc`,
`c • cfc f A = cfc (c·f) A`. -/
lemma smul_cfc (hA : A.IsHermitian) (c : ℝ) (f : ℝ → ℝ) :
    c • cfc f A = cfc (fun x => c * f x) A := by
  have h1 : c • cfc f A = c • diagMap hA (fun i => f (hA.eigenvalues i)) := by
    rw [diagMap_comp_eigenvalues hA f]
  have h2 : c • diagMap hA (fun i => f (hA.eigenvalues i)) =
      diagMap hA (fun i => c * f (hA.eigenvalues i)) := by
    rw [← map_smul]
    congr 1
  rw [h1, h2]
  exact diagMap_comp_eigenvalues hA fun x => c * f x


/-- Lean implementation helper: the exponential of a standard matrix function,
`exp (cfc f A) = cfc (exp ∘ f) A`. -/
lemma exp_cfc (hA : A.IsHermitian) {f : ℝ → ℝ} (hf : Continuous f) :
    NormedSpace.exp (cfc f A) = cfc (fun x => Real.exp (f x)) A := by
  rw [matrixExp_eq_cfc (isHermitian_cfc f A),
    ← cfc_comp' Real.exp f A Real.continuous_exp.continuousOn hf.continuousOn]

/-- Lean implementation helper: `e^{sA}` as a standard matrix function. -/
lemma exp_smul_eq_cfc (hA : A.IsHermitian) (s : ℝ) :
    NormedSpace.exp (s • A) = cfc (fun x : ℝ => Real.exp (s * x)) A := by
  rw [smul_eq_cfc hA s, exp_cfc hA (by fun_prop : Continuous fun x : ℝ => s * x)]

/-- Lean implementation helper: entry formula for a standard matrix function. -/
lemma cfc_apply_entry (hA : A.IsHermitian) (f : ℝ → ℝ) (a b : n) :
    cfc f A a b = ∑ i, (hA.eigenvectorUnitary : Matrix n n ℂ) a i *
      ((f (hA.eigenvalues i) : ℝ) : ℂ) *
      star ((hA.eigenvectorUnitary : Matrix n n ℂ) b i) := by
  rw [cfc_eq_book_formula hA f, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [Matrix.diagonal_apply_eq, Matrix.conjTranspose_apply]
    rfl
  · intro c _ hc
    rw [Matrix.diagonal_apply_ne _ hc, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

end CfcToolkit

section ExpectationExchange

/-- Lean implementation helper: exchange of expectation with a scalar-modulated
standard matrix function — the eigenbasis rendering of "take the expectation of the
series term by term".  For a random scalar `ζ` and a family of scalar functions
`g : ℝ → ℝ → ℝ`, `𝔼[cfc (g (ζ ω)) A] = diagMap hA (fun i => 𝔼[g (ζ ω) (λ_i)])`. -/
lemma expectation_cfc_modulated {ζ : Ω → ℝ} (hA : A.IsHermitian) (g : ℝ → ℝ → ℝ)
    (hint : ∀ i, Integrable (fun ω => g (ζ ω) (hA.eigenvalues i)) μ) :
    expectation μ (fun ω => cfc (g (ζ ω)) A) =
      diagMap hA (fun i => ∫ ω, g (ζ ω) (hA.eigenvalues i) ∂μ) := by
  ext a b
  rw [expectation_apply]
  have h1 : ∀ ω, cfc (g (ζ ω)) A a b =
      ∑ i, (hA.eigenvectorUnitary : Matrix n n ℂ) a i *
        ((g (ζ ω) (hA.eigenvalues i) : ℝ) : ℂ) *
        star ((hA.eigenvectorUnitary : Matrix n n ℂ) b i) := fun ω =>
    cfc_apply_entry hA (g (ζ ω)) a b
  have h2 : diagMap hA (fun i => ∫ ω, g (ζ ω) (hA.eigenvalues i) ∂μ) a b =
      ∑ i, (hA.eigenvectorUnitary : Matrix n n ℂ) a i *
        (((∫ ω, g (ζ ω) (hA.eigenvalues i) ∂μ : ℝ)) : ℂ) *
        star ((hA.eigenvectorUnitary : Matrix n n ℂ) b i) := by
    rw [diagMap_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [Matrix.diagonal_apply_eq, Matrix.conjTranspose_apply]
      rfl
    · intro c _ hc
      rw [Matrix.diagonal_apply_ne _ hc, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  simp only [h1, h2]
  rw [MeasureTheory.integral_finsetSum _
    (fun i _ => (((hint i).ofReal.const_mul _).mul_const _))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MeasureTheory.integral_mul_const, MeasureTheory.integral_const_mul]
  congr 2
  exact integral_ofReal

end ExpectationExchange

section ScalarIngredients

/-- Lean implementation helper: the scalar mgf of a standard Gaussian
(`𝔼 e^{sγ} = e^{s²/2}`), via the Mathlib correspondence
`ProbabilityTheory.mgf_gaussianReal`. -/
lemma integral_exp_mul_isStdGaussian [IsProbabilityMeasure μ] {γ : Ω → ℝ}
    (hγm : Measurable γ) (hγ : IsStdGaussian γ μ) (s : ℝ) :
    ∫ ω, Real.exp (s * γ ω) ∂μ = Real.exp (s ^ 2 / 2) := by
  have h1 : ProbabilityTheory.mgf γ μ s = Real.exp (0 * s + 1 * s ^ 2 / 2) :=
    ProbabilityTheory.mgf_gaussianReal hγ s
  simpa [ProbabilityTheory.mgf] using h1

/-- Lean implementation helper: integrability of `e^{sγ}` for standard Gaussian γ. -/
lemma integrable_exp_mul_isStdGaussian [IsProbabilityMeasure μ] {γ : Ω → ℝ}
    (hγm : Measurable γ) (hγ : IsStdGaussian γ μ) (s : ℝ) :
    Integrable (fun ω => Real.exp (s * γ ω)) μ := by
  have h1 : Integrable (fun x : ℝ => Real.exp (s * x)) (μ.map γ) := by
    rw [hγ]
    exact ProbabilityTheory.integrable_exp_mul_gaussianReal s
  have hm : Measurable fun x : ℝ => Real.exp (s * x) := by fun_prop
  rwa [integrable_map_measure hm.aestronglyMeasurable hγm.aemeasurable] at h1

/-- Lean implementation helper: a Rademacher variable takes the values ±1 almost
surely (from its law). -/
lemma ae_range_isRademacher [IsProbabilityMeasure μ] {ϱ : Ω → ℝ}
    (hϱm : Measurable ϱ) (hϱ : IsRademacher ϱ μ) :
    ∀ᵐ ω ∂μ, ϱ ω = 1 ∨ ϱ ω = -1 := by
  have hS : MeasurableSet ({1, -1} : Set ℝ) :=
    (measurableSet_singleton 1).union (measurableSet_singleton (-1))
  have h1 : μ.map ϱ {1, -1} = 1 := by
    rw [hϱ, show rademacherMeasure = (2⁻¹ : ENNReal) • MeasureTheory.Measure.dirac 1 +
      (2⁻¹ : ENNReal) • MeasureTheory.Measure.dirac (-1) from rfl]
    rw [MeasureTheory.Measure.add_apply, MeasureTheory.Measure.smul_apply,
      MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.dirac_apply' _ hS,
      MeasureTheory.Measure.dirac_apply' _ hS]
    have hm1 : (1 : ℝ) ∈ ({1, -1} : Set ℝ) := by simp
    have hm2 : (-1 : ℝ) ∈ ({1, -1} : Set ℝ) := by simp
    rw [Set.indicator_of_mem hm1, Set.indicator_of_mem hm2]
    simp only [Pi.one_apply, smul_eq_mul, mul_one]
    rw [ENNReal.inv_two_add_inv_two]
  have h2 : μ (ϱ ⁻¹' {1, -1}) = 1 := by
    rw [← MeasureTheory.Measure.map_apply hϱm hS]
    exact h1
  have h3 : μ (ϱ ⁻¹' {1, -1})ᶜ = 0 := by
    rw [MeasureTheory.measure_compl (hϱm hS) (by simp), h2]
    simp
  refine MeasureTheory.ae_iff.mpr ?_
  have h4 : {ω | ¬(ϱ ω = 1 ∨ ϱ ω = -1)} = (ϱ ⁻¹' {1, -1})ᶜ := by
    ext ω
    simp [Set.mem_preimage]
  rw [h4]
  exact h3

/-- Lean implementation helper: every measurable function of a Rademacher variable
is integrable (the variable is a.s. two-valued). -/
lemma integrable_isRademacher [IsProbabilityMeasure μ] {ϱ : Ω → ℝ}
    (hϱm : Measurable ϱ) (hϱ : IsRademacher ϱ μ) {f : ℝ → ℝ} (hf : Measurable f) :
    Integrable (fun ω => f (ϱ ω)) μ := by
  refine Integrable.of_bound (hf.comp hϱm).aestronglyMeasurable
    (max |f 1| |f (-1)|) ?_
  filter_upwards [ae_range_isRademacher hϱm hϱ] with ω h
  rw [Real.norm_eq_abs]
  rcases h with h | h <;> rw [h]
  · exact le_max_left _ _
  · exact le_max_right _ _

/-- Lean implementation helper: expectation of a (measurable) function of a
Rademacher variable is the two-point average, `𝔼 f(ϱ) = ½f(1) + ½f(−1)`. -/
lemma integral_isRademacher [IsProbabilityMeasure μ] {ϱ : Ω → ℝ}
    (hϱm : Measurable ϱ) (hϱ : IsRademacher ϱ μ) {f : ℝ → ℝ} (hf : Measurable f) :
    ∫ ω, f (ϱ ω) ∂μ = 2⁻¹ * f 1 + 2⁻¹ * f (-1) := by
  have hs1 : MeasurableSet (ϱ ⁻¹' {1}) := hϱm (measurableSet_singleton 1)
  have hμ1 : μ.real (ϱ ⁻¹' {1}) = 2⁻¹ := by
    have h1 : μ.map ϱ {1} = 2⁻¹ := by
      rw [hϱ, show rademacherMeasure = (2⁻¹ : ENNReal) • MeasureTheory.Measure.dirac 1 +
        (2⁻¹ : ENNReal) • MeasureTheory.Measure.dirac (-1) from rfl]
      rw [MeasureTheory.Measure.add_apply, MeasureTheory.Measure.smul_apply,
        MeasureTheory.Measure.smul_apply,
        MeasureTheory.Measure.dirac_apply' _ (measurableSet_singleton _),
        MeasureTheory.Measure.dirac_apply' _ (measurableSet_singleton _)]
      norm_num [Set.indicator_apply]
    have h2 : μ (ϱ ⁻¹' {1}) = 2⁻¹ := by
      rw [← MeasureTheory.Measure.map_apply hϱm (measurableSet_singleton 1)]
      exact h1
    rw [MeasureTheory.measureReal_def, h2]
    simp
  have hμ2 : μ.real (ϱ ⁻¹' {-1}) = 2⁻¹ := by
    have h1 : μ.map ϱ {-1} = 2⁻¹ := by
      rw [hϱ, show rademacherMeasure = (2⁻¹ : ENNReal) • MeasureTheory.Measure.dirac 1 +
        (2⁻¹ : ENNReal) • MeasureTheory.Measure.dirac (-1) from rfl]
      rw [MeasureTheory.Measure.add_apply, MeasureTheory.Measure.smul_apply,
        MeasureTheory.Measure.smul_apply,
        MeasureTheory.Measure.dirac_apply' _ (measurableSet_singleton _),
        MeasureTheory.Measure.dirac_apply' _ (measurableSet_singleton _)]
      norm_num [Set.indicator_apply]
    have h2 : μ (ϱ ⁻¹' {-1}) = 2⁻¹ := by
      rw [← MeasureTheory.Measure.map_apply hϱm (measurableSet_singleton (-1))]
      exact h1
    rw [MeasureTheory.measureReal_def, h2]
    simp
  have hcongr : (fun ω => f (ϱ ω)) =ᵐ[μ]
      fun ω => Set.indicator (ϱ ⁻¹' {1}) (fun _ => f 1) ω +
        Set.indicator (ϱ ⁻¹' {-1}) (fun _ => f (-1)) ω := by
    filter_upwards [ae_range_isRademacher hϱm hϱ] with ω h
    rcases h with h | h <;>
      norm_num [Set.indicator_apply, Set.mem_preimage, h]
  rw [MeasureTheory.integral_congr_ae hcongr, MeasureTheory.integral_add
    ((MeasureTheory.integrable_indicator_iff hs1).mpr (by simp))
    ((MeasureTheory.integrable_indicator_iff
      (hϱm (measurableSet_singleton (-1)))).mpr (by simp)),
    MeasureTheory.integral_indicator_const _ hs1,
    MeasureTheory.integral_indicator_const _ (hϱm (measurableSet_singleton (-1)))]
  rw [smul_eq_mul, smul_eq_mul, hμ1, hμ2]

end ScalarIngredients

section GaussianLemma

variable [IsProbabilityMeasure μ]

/-- **Book Lemma 4.6.2 (Gaussian × Matrix: Mgf)** (§4.6,
p. 52), mgf half: for a fixed Hermitian `A` and a standard normal `γ`,
`𝔼 e^{γθA} = e^{θ²A²/2}`.  Explicit source declaration.  The source computes with
the Gaussian moment series; the proof here is the equivalent eigenbasis computation
(the scalar Gaussian mgf at each eigenvalue, Definition 2.1.2), documented in the
proof audit. -/
theorem gaussian_matrix_mgf {γ : Ω → ℝ} (hγm : Measurable γ)
    (hγ : IsStdGaussian γ μ) (hA : A.IsHermitian) (θ : ℝ) :
    matrixMgf μ (fun ω => γ ω • A) θ =
      NormedSpace.exp ((θ ^ 2 / 2) • A ^ 2) := by
  have hRHS : NormedSpace.exp ((θ ^ 2 / 2) • A ^ 2) =
      cfc (fun x : ℝ => Real.exp (θ ^ 2 / 2 * x ^ 2)) A := by
    rw [← cfc_pow_eq hA 2, smul_cfc hA,
      exp_cfc hA (by fun_prop : Continuous fun x : ℝ => θ ^ 2 / 2 * x ^ 2)]
  have hLHS : matrixMgf μ (fun ω => γ ω • A) θ =
      diagMap hA (fun i => ∫ ω, Real.exp ((θ * γ ω) * hA.eigenvalues i) ∂μ) := by
    rw [matrixMgf_def]
    have h1 : (fun ω => NormedSpace.exp (θ • (γ ω • A))) =
        fun ω => cfc ((fun s x => Real.exp (s * x)) (θ * γ ω)) A := by
      funext ω
      rw [smul_smul, exp_smul_eq_cfc hA]
    rw [h1]
    refine expectation_cfc_modulated (ζ := fun ω => θ * γ ω) hA
      (fun s x => Real.exp (s * x)) fun i => ?_
    show Integrable (fun ω => Real.exp ((θ * γ ω) * hA.eigenvalues i)) μ
    have h2 : (fun ω => Real.exp ((θ * γ ω) * hA.eigenvalues i)) =
        fun ω => Real.exp ((θ * hA.eigenvalues i) * γ ω) := by
      funext ω
      ring_nf
    rw [h2]
    exact integrable_exp_mul_isStdGaussian hγm hγ _
  rw [hLHS, hRHS, ← diagMap_comp_eigenvalues hA]
  congr 1
  funext i
  have h3 : (fun ω => Real.exp ((θ * γ ω) * hA.eigenvalues i)) =
      fun ω => Real.exp ((θ * hA.eigenvalues i) * γ ω) := by
    funext ω
    ring_nf
  rw [h3, integral_exp_mul_isStdGaussian hγm hγ]
  congr 1
  ring

/-- **Book Lemma 4.6.2**, cgf half: `log 𝔼 e^{γθA} = (θ²/2)A²` (via (2.1.17)). -/
theorem gaussian_matrix_cgf {γ : Ω → ℝ} (hγm : Measurable γ)
    (hγ : IsStdGaussian γ μ) (hA : A.IsHermitian) (θ : ℝ) :
    matrixCgf μ (fun ω => γ ω • A) θ = (θ ^ 2 / 2) • A ^ 2 := by
  rw [show matrixCgf μ (fun ω => γ ω • A) θ =
    CFC.log (matrixMgf μ (fun ω => γ ω • A) θ) from rfl,
    gaussian_matrix_mgf hγm hγ hA θ]
  exact log_exp_eq (isHermitian_real_smul (hA.pow 2) _)

end GaussianLemma

section RademacherLemma

variable [IsProbabilityMeasure μ]

/-- **Book Lemma 4.6.3 (Rademacher × Matrix: Mgf)** (§4.6,
p. 54), computation half: `𝔼 e^{ϱθA} = cosh(θA)` (the standard matrix function of
`cosh`). -/
theorem rademacher_matrix_mgf {ϱ : Ω → ℝ} (hϱm : Measurable ϱ)
    (hϱ : IsRademacher ϱ μ) (hA : A.IsHermitian) (θ : ℝ) :
    matrixMgf μ (fun ω => ϱ ω • A) θ =
      cfc (fun x : ℝ => Real.cosh (θ * x)) A := by
  have hLHS : matrixMgf μ (fun ω => ϱ ω • A) θ =
      diagMap hA (fun i => ∫ ω, Real.exp ((θ * ϱ ω) * hA.eigenvalues i) ∂μ) := by
    rw [matrixMgf_def]
    have h1 : (fun ω => NormedSpace.exp (θ • (ϱ ω • A))) =
        fun ω => cfc ((fun s x => Real.exp (s * x)) (θ * ϱ ω)) A := by
      funext ω
      rw [smul_smul, exp_smul_eq_cfc hA]
    rw [h1]
    refine expectation_cfc_modulated (ζ := fun ω => θ * ϱ ω) hA
      (fun s x => Real.exp (s * x)) fun i => ?_
    show Integrable (fun ω => Real.exp ((θ * ϱ ω) * hA.eigenvalues i)) μ
    have h2 : (fun ω => Real.exp ((θ * ϱ ω) * hA.eigenvalues i)) =
        fun ω => (fun x => Real.exp ((θ * hA.eigenvalues i) * x)) (ϱ ω) := by
      funext ω
      show Real.exp ((θ * ϱ ω) * hA.eigenvalues i) = _
      ring_nf
    rw [h2]
    exact integrable_isRademacher hϱm hϱ
      (f := fun x => Real.exp ((θ * hA.eigenvalues i) * x)) (by fun_prop)
  rw [hLHS, ← diagMap_comp_eigenvalues hA]
  congr 1
  funext i
  have h2 : (fun x : ℝ => Real.exp ((θ * x) * hA.eigenvalues i)) =
      fun x : ℝ => Real.exp ((θ * hA.eigenvalues i) * x) := by
    funext x
    ring_nf
  have h3 := integral_isRademacher hϱm hϱ
    (f := fun x : ℝ => Real.exp ((θ * hA.eigenvalues i) * x))
    (Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id))
  have h4 : (∫ ω, Real.exp ((θ * ϱ ω) * hA.eigenvalues i) ∂μ) =
      ∫ ω, Real.exp ((θ * hA.eigenvalues i) * ϱ ω) ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    show Real.exp ((θ * ϱ ω) * hA.eigenvalues i) = _
    ring_nf
  rw [h4, h3, Real.cosh_eq]
  have h5 : θ * hA.eigenvalues i * -1 = -(θ * hA.eigenvalues i) := by ring
  have h6 : θ * hA.eigenvalues i * 1 = θ * hA.eigenvalues i := by ring
  rw [h5, h6]
  ring

/-- **Book Lemma 4.6.3**, semidefinite mgf bound: `𝔼 e^{ϱθA} ≼ e^{θ²A²/2}` — the
Transfer Rule (2.1.14) applied to (4.6.6) `cosh a ≤ e^{a²/2}` (Mathlib
correspondence `Real.cosh_le_exp_half_sq`), exactly the source's proof. -/
theorem rademacher_matrix_mgf_le {ϱ : Ω → ℝ} (hϱm : Measurable ϱ)
    (hϱ : IsRademacher ϱ μ) (hA : A.IsHermitian) (θ : ℝ) :
    matrixMgf μ (fun ω => ϱ ω • A) θ ≤ NormedSpace.exp ((θ ^ 2 / 2) • A ^ 2) := by
  rw [rademacher_matrix_mgf hϱm hϱ hA θ,
    show NormedSpace.exp ((θ ^ 2 / 2) • A ^ 2) =
      cfc (fun x : ℝ => Real.exp (θ ^ 2 / 2 * x ^ 2)) A by
        rw [← cfc_pow_eq hA 2, smul_cfc hA,
          exp_cfc hA (by fun_prop : Continuous fun x : ℝ => θ ^ 2 / 2 * x ^ 2)]]
  refine transfer_rule hA (I := Set.univ) (fun i => Set.mem_univ _) fun a _ => ?_
  have h1 := Real.cosh_le_exp_half_sq (θ * a)
  refine h1.trans (le_of_eq ?_)
  congr 1
  ring

/-- Lean implementation helper: the Rademacher matrix mgf is positive definite
(`cosh ≥ 1`), so its logarithm is well-defined. -/
lemma posDef_rademacher_mgf {ϱ : Ω → ℝ} (hϱm : Measurable ϱ)
    (hϱ : IsRademacher ϱ μ) (hA : A.IsHermitian) (θ : ℝ) :
    (matrixMgf μ (fun ω => ϱ ω • A) θ).PosDef := by
  rw [rademacher_matrix_mgf hϱm hϱ hA θ]
  have h1 : (1 : Matrix n n ℂ) ≤ cfc (fun x : ℝ => Real.cosh (θ * x)) A := by
    rw [show (1 : Matrix n n ℂ) = ((1 : ℝ) : ℂ) • (1 : Matrix n n ℂ) by norm_num,
      ← cfc_const_eq_smul_one hA 1]
    refine transfer_rule hA (I := Set.univ) (fun i => Set.mem_univ _)
      fun a _ => ?_
    rw [Real.cosh_eq]
    have h1 := Real.exp_pos (θ * a)
    have h2 : Real.exp (-(θ * a)) = (Real.exp (θ * a))⁻¹ := Real.exp_neg _
    rw [h2, le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
    have h3 : 0 < (Real.exp (θ * a))⁻¹ := by positivity
    nlinarith [sq_nonneg (Real.exp (θ * a) - 1),
      mul_inv_cancel₀ (ne_of_gt h1)]
  have h2 := Matrix.le_iff.mp h1
  have h3 := Matrix.PosDef.one.add_posSemidef h2
  rwa [add_sub_cancel] at h3

/-- **Book Lemma 4.6.3**, cgf half: `log 𝔼 e^{ϱθA} ≼ (θ²/2)A²` — the Transfer Rule
applied to `log cosh a ≤ a²/2`. -/
theorem rademacher_matrix_cgf_le {ϱ : Ω → ℝ} (hϱm : Measurable ϱ)
    (hϱ : IsRademacher ϱ μ) (hA : A.IsHermitian) (θ : ℝ) :
    matrixCgf μ (fun ω => ϱ ω • A) θ ≤ (θ ^ 2 / 2) • A ^ 2 := by
  rw [show matrixCgf μ (fun ω => ϱ ω • A) θ =
    CFC.log (matrixMgf μ (fun ω => ϱ ω • A) θ) from rfl,
    rademacher_matrix_mgf hϱm hϱ hA θ]
  have hlogc : ContinuousOn Real.log
      ((fun x : ℝ => Real.cosh (θ * x)) '' spectrum ℝ A) := by
    refine Real.continuousOn_log.mono ?_
    rintro y ⟨x, _, rfl⟩
    have := Real.cosh_pos (θ * x)
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    positivity
  have hcoshc : ContinuousOn (fun x : ℝ => Real.cosh (θ * x)) (spectrum ℝ A) := by
    fun_prop
  have hlog : CFC.log (cfc (fun x : ℝ => Real.cosh (θ * x)) A) =
      cfc (fun x : ℝ => Real.log (Real.cosh (θ * x))) A := by
    show cfc Real.log _ = _
    rw [← cfc_comp' Real.log (fun x : ℝ => Real.cosh (θ * x)) A hlogc hcoshc]
  rw [hlog, show (θ ^ 2 / 2) • A ^ 2 =
    cfc (fun x : ℝ => θ ^ 2 / 2 * x ^ 2) A by rw [← cfc_pow_eq hA 2, smul_cfc hA]]
  refine transfer_rule hA (I := Set.univ) (fun i => Set.mem_univ _) fun a _ => ?_
  have h1 : Real.log (Real.cosh (θ * a)) ≤ Real.log (Real.exp ((θ * a) ^ 2 / 2)) :=
    Real.log_le_log (Real.cosh_pos _) (Real.cosh_le_exp_half_sq _)
  rw [Real.log_exp] at h1
  refine h1.trans (le_of_eq ?_)
  ring

end RademacherLemma

end MatrixConcentration


/-!
# Almost-sure representatives for the Rademacher bounds

The book formulates its Rademacher results in terms of the distributional predicate alone.
The following siblings remove the pointwise support assumptions from the earlier computational
versions by replacing a variable on its null exceptional set and transferring the conclusions
back along almost-everywhere equality.
-/

namespace MatrixConcentration

open Matrix Finset MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}

/-- Lean implementation helper: choose a genuinely two-valued representative of a real
function which is almost surely Rademacher-valued. -/
noncomputable def rademacherRepresentative (x : ℝ) : ℝ :=
  if x = 1 ∨ x = -1 then x else 1

lemma measurable_rademacherRepresentative : Measurable rademacherRepresentative := by
  have hs : MeasurableSet {x : ℝ | x = 1 ∨ x = -1} := by
    convert (measurableSet_singleton (-1 : ℝ)).union (measurableSet_singleton (1 : ℝ)) using 1
    ext x
    simp
  exact Measurable.ite hs measurable_id measurable_const

lemma rademacherRepresentative_range (x : ℝ) :
    rademacherRepresentative x = 1 ∨ rademacherRepresentative x = -1 := by
  by_cases hx : x = 1 ∨ x = -1
  · simpa [rademacherRepresentative, hx] using hx
  · simp [rademacherRepresentative, hx]

lemma rademacherRepresentative_ae_eq [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Measurable f) (hlaw : IsRademacher f μ) :
    (fun ω => rademacherRepresentative (f ω)) =ᵐ[μ] f := by
  filter_upwards [ae_range_isRademacher hf hlaw] with ω hω
  simp [rademacherRepresentative, hω]

lemma isRademacher_rademacherRepresentative [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Measurable f) (hlaw : IsRademacher f μ) :
    IsRademacher (fun ω => rademacherRepresentative (f ω)) μ := by
  unfold IsRademacher
  rw [Measure.map_congr (rademacherRepresentative_ae_eq hf hlaw), hlaw]

lemma iIndepFun_rademacherRepresentative {ι : Type*} [IsProbabilityMeasure μ]
    {f : ι → Ω → ℝ} (hf : ∀ k, Measurable (f k))
    (hlaw : ∀ k, IsRademacher (f k) μ) (hind : iIndepFun f μ) :
    iIndepFun (fun k ω => rademacherRepresentative (f k ω)) μ := by
  exact hind.congr fun k => (rademacherRepresentative_ae_eq (hf k) (hlaw k)).symm

lemma rademacherRepresentative_matsum_ae {ι m n : Type*}
    [Fintype ι] [DecidableEq ι] {f : ι → Ω → ℝ} (hf : ∀ k, Measurable (f k))
    [IsProbabilityMeasure μ] (hlaw : ∀ k, IsRademacher (f k) μ)
    (C : ι → Matrix m n ℂ) :
    (fun ω => ∑ k, rademacherRepresentative (f k ω) • C k) =ᵐ[μ]
      fun ω => ∑ k, f k ω • C k := by
  filter_upwards [MeasureTheory.ae_all_iff.mpr
    (fun k => rademacherRepresentative_ae_eq (hf k) (hlaw k))] with ω hω
  exact Finset.sum_congr rfl fun k _ => by rw [hω k]


end MatrixConcentration


set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# Matrix Rademacher series with Hermitian coefficients (Tropp §4.6, Thm 4.6.1)

* `rademacher_herm_expectation`/`rademacher_herm_tail` — **Book Theorem 4.6.1**
  (C4-11), Rademacher case: for `Y = Σ_k ϱ_k A_k` with fixed
  Hermitian `A_k` and independent Rademacher signs, with
  `v = ‖Σ_k A_k²‖`:  `𝔼 λ_max(Y) ≤ √(2 v log d)` and
  `P(λ_max(Y) ≥ t) ≤ d·e^{−t²/(2v)}`.  Faithful translation of the source proof
  (§4.6.4): the master bounds (Theorem 3.6.1) + the Rademacher cgf bound
  (Lemma 4.6.3) substituted through the trace-exponential monotonicity (2.1.16),
  then the explicit θ-optimizations (`θ* = √(2 log d / v)`, `θ* = t/v`); the
  degenerate cases `v = 0` and `d = 1` are handled through the pointwise-θ master
  bounds (the source's infimum silently covers them);
* `rademacher_herm_min_expectation`/`rademacher_herm_min_tail` — the λ_min displays
  and (C4-13): realized by instantiating the
  λ_max results at the negated coefficient family (`λ_min(Y) = −λ_max(−Y)`
  pointwise, same variance) — equivalent to the source's distributional-symmetry
  argument without transporting laws (documented in the proof audit);
* helpers (C4-16): `trace_re_le_card_mul_lambdaMax`, `posSemidef_matsum_sq`,
  `sum_loewner_mono`, the optimization lemma `le_sqrt_of_forall_theta`.

The Rademacher modulators are ±1-valued (hypothesis `hrange`, the book's
definition), so the sequence is uniformly bounded and the Chapter-3 master bounds
apply directly; the law hypothesis `IsRademacher` feeds Lemma 4.6.3.
-/

namespace MatrixConcentration

open Matrix Finset MeasureTheory
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section Helpers

/-- Lean implementation helper (C4-16): `tr A ≤ d·λ_max(A)` for Hermitian `A`. -/
lemma trace_re_le_card_mul_lambdaMax [Nonempty n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) :
    (A.trace).re ≤ (Fintype.card n : ℝ) * lambdaMax hA := by
  rw [trace_re_eq_sum_eigenvalues hA]
  calc (∑ i, hA.eigenvalues i) ≤ ∑ _i : n, lambdaMax hA :=
        Finset.sum_le_sum fun i _ => eigenvalues_le_lambdaMax hA i
  _ = (Fintype.card n : ℝ) * lambdaMax hA := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Lean implementation helper: sums of psd matrices are psd. -/
lemma posSemidef_matsum {M : ι → Matrix n n ℂ} (s : Finset ι)
    (hM : ∀ k, (M k).PosSemidef) : (∑ k ∈ s, M k).PosSemidef := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Matrix.PosSemidef.zero
  | insert b t hb iht =>
    rw [Finset.sum_insert hb]
    exact (hM b).add iht

/-- Lean implementation helper: the Loewner order is compatible with finite sums. -/
lemma sum_loewner_mono {f g : ι → Matrix n n ℂ} (s : Finset ι)
    (h : ∀ k ∈ s, f k ≤ g k) : (∑ k ∈ s, f k) ≤ ∑ k ∈ s, g k := by
  rw [Matrix.le_iff]
  have hdecomp : (∑ k ∈ s, g k) - ∑ k ∈ s, f k = ∑ k ∈ s, (g k - f k) := by
    rw [Finset.sum_sub_distrib]
  rw [hdecomp]
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simpa using Matrix.PosSemidef.zero
  · intro b t hb ih h
    rw [Finset.sum_insert hb]
    exact (Matrix.le_iff.mp (h b (Finset.mem_insert_self b t))).add
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

/-- Lean implementation helper (C4-16): the θ-optimization
`inf_{θ>0} (L/θ + θv/2) = √(2vL)`, in the one-sided form the proofs consume; the
degenerate cases `v = 0` and `L = 0` are covered (the infimum is then `0`,
approached but not attained — the book's `inf` handles this silently). -/
lemma le_sqrt_of_forall_theta {E v L : ℝ} (hv : 0 ≤ v) (hL : 0 ≤ L)
    (h : ∀ θ : ℝ, 0 < θ → E ≤ θ⁻¹ * L + θ * v / 2) :
    E ≤ Real.sqrt (2 * v * L) := by
  rcases eq_or_lt_of_le hv with hv0 | hvpos
  · -- v = 0 : E ≤ L/θ for all θ, so E ≤ 0
    have h0 : E ≤ 0 := by
      refine le_of_forall_pos_le_add fun ε hε => ?_
      rcases eq_or_lt_of_le hL with hL0 | hLpos
      · have := h 1 one_pos
        rw [← hv0, ← hL0] at this
        simpa using this.trans (by linarith)
      · have := h (L / ε) (div_pos hLpos hε)
        rw [← hv0] at this
        have h1 : (L / ε)⁻¹ * L + L / ε * 0 / 2 = ε := by
          rw [mul_zero, zero_div, add_zero, inv_div]
          field_simp
        rw [h1] at this
        linarith
    exact h0.trans (Real.sqrt_nonneg _)
  · rcases eq_or_lt_of_le hL with hL0 | hLpos
    · -- L = 0 : E ≤ θv/2 for all θ, so E ≤ 0
      have h0 : E ≤ 0 := by
        refine le_of_forall_pos_le_add fun ε hε => ?_
        have := h (2 * ε / v) (by positivity)
        rw [← hL0] at this
        have h1 : (2 * ε / v)⁻¹ * 0 + (2 * ε / v) * v / 2 = ε := by
          rw [mul_zero, zero_add]
          field_simp
        rw [h1] at this
        linarith
      exact h0.trans (Real.sqrt_nonneg _)
    · -- main case: θ* = √(2vL)/v
      set s := Real.sqrt (2 * v * L) with hs
      have hs2 : s ^ 2 = 2 * v * L := Real.sq_sqrt (by positivity)
      have hspos : 0 < s := Real.sqrt_pos.mpr (by positivity)
      have hθ : (0 : ℝ) < s / v := by positivity
      have h1 := h (s / v) hθ
      have h2 : (s / v)⁻¹ * L + (s / v) * v / 2 = s := by
        rw [inv_div]
        field_simp
        nlinarith [hs2]
      rwa [h2] at h1

end Helpers

section RademacherHermitian

variable [IsProbabilityMeasure μ] [Nonempty n]
variable {A : ι → Matrix n n ℂ} {ϱ : ι → Ω → ℝ}

/-- The shared cgf-substitution chain of §4.6.4: for every `θ`,
`tr exp(Σ_k Ξ_{ϱ_k A_k}(θ)) ≤ d · e^{(θ²/2)·v}` where `v = ‖Σ_k A_k²‖`.
Lean implementation helper (the display inside the Rademacher-case proof, justified
there by Lemma 4.6.3 and the monotonicity (2.1.16)). -/
lemma rademacher_cgf_trace_bound
    (hmeas : ∀ k, Measurable (ϱ k)) (hlaw : ∀ k, IsRademacher (ϱ k) μ)
    (hA : ∀ k, (A k).IsHermitian) (θ : ℝ) :
    ((NormedSpace.exp (∑ k, matrixCgf μ (fun ω => ϱ k ω • A k) θ)).trace).re ≤
      (Fintype.card n : ℝ) *
        Real.exp (θ ^ 2 / 2 * ‖∑ k, (A k) ^ 2‖) := by
  have hsq : ∀ k, ((A k) ^ 2).PosSemidef := fun k => by
    have h := posSemidef_sq (hA k)
    rwa [← pow_two] at h
  have hsumsq : (∑ k, (A k) ^ 2).PosSemidef :=
    posSemidef_matsum Finset.univ hsq
  -- cgf bound summed
  have hstep : (∑ k, matrixCgf μ (fun ω => ϱ k ω • A k) θ) ≤
      (θ ^ 2 / 2) • ∑ k, (A k) ^ 2 := by
    have h1 : (θ ^ 2 / 2) • ∑ k, (A k) ^ 2 = ∑ k, (θ ^ 2 / 2) • (A k) ^ 2 :=
      Finset.smul_sum
    rw [h1]
    exact sum_loewner_mono Finset.univ fun k _ =>
      rademacher_matrix_cgf_le (hmeas k) (hlaw k) (hA k) θ
  -- Hermitian data
  have hcgfHerm : (∑ k, matrixCgf μ (fun ω => ϱ k ω • A k) θ).IsHermitian :=
    isHermitian_matsum Finset.univ fun k => isHermitian_cfc_log _
  have hsumHerm : ((θ ^ 2 / 2) • ∑ k, (A k) ^ 2).IsHermitian :=
    isHermitian_real_smul hsumsq.1 _
  -- trace-exponential monotonicity (2.1.16)
  have h2 := trace_exp_monotone hcgfHerm hsumHerm hstep
  refine h2.trans ?_
  -- tr exp((θ²/2)ΣA²) ≤ d·λ_max(exp(...)) = d·e^{(θ²/2)‖ΣA²‖}
  have h3 := trace_re_le_card_mul_lambdaMax (isHermitian_exp hsumHerm)
  refine h3.trans ?_
  have h4 : lambdaMax (isHermitian_exp hsumHerm) =
      Real.exp (lambdaMax hsumHerm) := lambdaMax_exp hsumHerm
  have h5 : lambdaMax hsumHerm = (θ ^ 2 / 2) * lambdaMax hsumsq.1 :=
    lambdaMax_smul_nonneg hsumsq.1 (by positivity) hsumHerm
  have h6 : lambdaMax hsumsq.1 = ‖∑ k, (A k) ^ 2‖ :=
    (posSemidef_l2_opNorm_eq_lambdaMax hsumsq).symm
  rw [h4, h5, h6]

/-- **Book Theorem 4.6.1 (Matrix Rademacher Series, Hermitian Case)**
 (§4.6, p. 51), expectation bound (4.6.3), Rademacher case:
`𝔼 λ_max(Σ_k ϱ_k A_k) ≤ √(2 v log d)` with `v = ‖Σ_k A_k²‖`.
Explicit source declaration; faithful translation of the §4.6.4 proof.

**Author note.** Lean additionally assumes the chosen representatives satisfy
`ϱ_k(ω) ∈ {−1,1}` pointwise; the distributional hypothesis supplies this only
almost everywhere. See `rademacher_herm_expectation_of_isRademacher` for the
source-faithful law-only statement. -/
theorem rademacher_herm_expectation
    (hmeas : ∀ k, Measurable (ϱ k)) (hlaw : ∀ k, IsRademacher (ϱ k) μ)
    (hrange : ∀ k ω, ϱ k ω = 1 ∨ ϱ k ω = -1)
    (hind : ProbabilityTheory.iIndepFun ϱ μ)
    (hA : ∀ k, (A k).IsHermitian) :
    ∫ ω, lambdaMax (isHermitian_matsum Finset.univ
        (fun k => isHermitian_real_smul (hA k) (ϱ k ω))) ∂μ ≤
      Real.sqrt (2 * ‖∑ k, (A k) ^ 2‖ * Real.log (Fintype.card n)) := by
  classical
  set X : ι → Ω → Matrix n n ℂ := fun k ω => ϱ k ω • A k with hXdef
  have hXmeas : ∀ k, Measurable (X k) := fun k => by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    show Measurable fun ω => ϱ k ω • A k i j
    exact (hmeas k).smul_const _
  have hXherm : ∀ k ω, (X k ω).IsHermitian := fun k ω =>
    isHermitian_real_smul (hA k) _
  have hXbd : ∀ k ω, ‖X k ω‖ ≤ ‖A k‖ := fun k ω => by
    show ‖ϱ k ω • A k‖ ≤ ‖A k‖
    rw [norm_smul, Real.norm_eq_abs]
    rcases hrange k ω with h | h <;> rw [h] <;> norm_num
  have hXind : ProbabilityTheory.iIndepFun X μ := by
    refine hind.comp (fun k s => s • A k) fun k => ?_
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    show Measurable fun s : ℝ => s • A k i j
    exact measurable_id.smul_const _
  refine le_sqrt_of_forall_theta (norm_nonneg _)
    (Real.log_nonneg (by exact_mod_cast Fintype.card_pos)) fun θ hθ => ?_
  have h1 := master_expectation_upper (μ := μ) hXmeas hXherm hXbd hXind hθ
  refine h1.trans ?_
  have h2 := rademacher_cgf_trace_bound hmeas hlaw hA θ
  have hpos : 0 < ((NormedSpace.exp (∑ k, matrixCgf μ (X k) θ)).trace).re :=
    trace_exp_re_pos (isHermitian_matsum Finset.univ fun k => isHermitian_cfc_log _)
  have h3 : Real.log ((NormedSpace.exp (∑ k, matrixCgf μ (X k) θ)).trace).re ≤
      Real.log ((Fintype.card n : ℝ) *
        Real.exp (θ ^ 2 / 2 * ‖∑ k, (A k) ^ 2‖)) :=
    Real.log_le_log hpos h2
  have h4 : Real.log ((Fintype.card n : ℝ) *
      Real.exp (θ ^ 2 / 2 * ‖∑ k, (A k) ^ 2‖)) =
      Real.log (Fintype.card n) + θ ^ 2 / 2 * ‖∑ k, (A k) ^ 2‖ := by
    rw [Real.log_mul (by exact_mod_cast Fintype.card_pos.ne')
      (Real.exp_pos _).ne', Real.log_exp]
  calc θ⁻¹ * Real.log ((NormedSpace.exp (∑ k, matrixCgf μ (X k) θ)).trace).re
      ≤ θ⁻¹ * (Real.log (Fintype.card n) + θ ^ 2 / 2 * ‖∑ k, (A k) ^ 2‖) := by
        rw [← h4]
        exact mul_le_mul_of_nonneg_left h3 (inv_pos.mpr hθ).le
  _ = θ⁻¹ * Real.log (Fintype.card n) + θ * ‖∑ k, (A k) ^ 2‖ / 2 := by
      field_simp

/-- **Book Theorem 4.6.1, equation (4.6.3), upper-tail Rademacher case:**
`P(λ_max(Σ_k ϱ_k A_k) ≥ t) ≤ d·e^{−t²/(2v)}` for `t ≥ 0`.

**Author note.** Lean additionally assumes the chosen representatives are
pointwise `{−1,1}`-valued. See `rademacher_herm_tail_of_isRademacher`. -/
theorem rademacher_herm_tail
    (hmeas : ∀ k, Measurable (ϱ k)) (hlaw : ∀ k, IsRademacher (ϱ k) μ)
    (hrange : ∀ k ω, ϱ k ω = 1 ∨ ϱ k ω = -1)
    (hind : ProbabilityTheory.iIndepFun ϱ μ)
    (hA : ∀ k, (A k).IsHermitian) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ lambdaMax (isHermitian_matsum Finset.univ
        (fun k => isHermitian_real_smul (hA k) (ϱ k ω)))} ≤
      (Fintype.card n : ℝ) *
        Real.exp (-(t ^ 2) / (2 * ‖∑ k, (A k) ^ 2‖)) := by
  classical
  set v : ℝ := ‖∑ k, (A k) ^ 2‖ with hv
  set X : ι → Ω → Matrix n n ℂ := fun k ω => ϱ k ω • A k with hXdef
  have hXmeas : ∀ k, Measurable (X k) := fun k => by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    show Measurable fun ω => ϱ k ω • A k i j
    exact (hmeas k).smul_const _
  have hXherm : ∀ k ω, (X k ω).IsHermitian := fun k ω =>
    isHermitian_real_smul (hA k) _
  have hXbd : ∀ k ω, ‖X k ω‖ ≤ ‖A k‖ := fun k ω => by
    show ‖ϱ k ω • A k‖ ≤ ‖A k‖
    rw [norm_smul, Real.norm_eq_abs]
    rcases hrange k ω with h | h <;> rw [h] <;> norm_num
  have hXind : ProbabilityTheory.iIndepFun X μ := by
    refine hind.comp (fun k s => s • A k) fun k => ?_
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    show Measurable fun s : ℝ => s • A k i j
    exact measurable_id.smul_const _
  have hcard1 : (1 : ℝ) ≤ (Fintype.card n : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hPle : ∀ S : Set Ω, μ.real S ≤ 1 := fun S => by
    have h := MeasureTheory.measureReal_mono (μ := μ) (Set.subset_univ S)
    rwa [MeasureTheory.probReal_univ] at h
  rcases eq_or_lt_of_le (norm_nonneg (∑ k, (A k) ^ 2)) with hv0 | hvpos
  · -- v = 0 : the right side is `d·e⁰ = d ≥ 1 ≥ P` (Lean division-by-zero junk)
    have h1 : -(t ^ 2) / (2 * v) = -(t ^ 2) / 0 := by
      rw [hv, ← hv0, mul_zero]
    rw [hv] at h1 ⊢
    rw [h1, div_zero, Real.exp_zero, mul_one]
    exact (hPle _).trans hcard1
  · rcases eq_or_lt_of_le ht with ht0 | htpos
    · -- t = 0 : the bound is at least d·e^{-0} ≥ 1 ≥ P
      rw [← ht0]
      norm_num
      exact (hPle _).trans hcard1
    · -- main case: master tail bound at θ = t/v
      have hθ : (0 : ℝ) < t / v := div_pos htpos hvpos
      have h1 := master_tail_upper (μ := μ) hXmeas hXherm hXbd hXind t hθ
      refine h1.trans ?_
      have h2 := rademacher_cgf_trace_bound hmeas hlaw hA (t / v)
      calc Real.exp (-(t / v) * t) *
          ((NormedSpace.exp (∑ k, matrixCgf μ (X k) (t / v))).trace).re
          ≤ Real.exp (-(t / v) * t) * ((Fintype.card n : ℝ) *
            Real.exp ((t / v) ^ 2 / 2 * v)) :=
          mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
      _ = (Fintype.card n : ℝ) * (Real.exp (-(t / v) * t) *
            Real.exp ((t / v) ^ 2 / 2 * v)) := by ring
      _ = (Fintype.card n : ℝ) * Real.exp (-(t ^ 2) / (2 * v)) := by
          rw [← Real.exp_add]
          congr 1
          field_simp
          ring

/-- Lean implementation helper (C4-13): the pointwise identity
`λ_min(Σ_k ϱ_k A_k) = −λ_max(Σ_k ϱ_k (−A_k))` — the negated-coefficient rendering of
the source's symmetry argument. -/
lemma lambdaMin_series_eq_neg_lambdaMax_neg
    (hA : ∀ k, (A k).IsHermitian) (ω : Ω) :
    lambdaMin (isHermitian_matsum Finset.univ
      (fun k => isHermitian_real_smul (hA k) (ϱ k ω))) =
    -(lambdaMax (isHermitian_matsum Finset.univ
      (fun k => isHermitian_real_smul ((hA k).neg) (ϱ k ω)))) := by
  have hmat : (∑ k, ϱ k ω • (-(A k))) = -(∑ k, ϱ k ω • A k) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _ => smul_neg _ _
  have h1 := lambdaMax_congr hmat
    (isHermitian_matsum Finset.univ fun k => isHermitian_real_smul ((hA k).neg) (ϱ k ω))
    ((isHermitian_matsum Finset.univ fun k =>
      isHermitian_real_smul (hA k) (ϱ k ω)).neg)
  rw [h1, lambdaMax_neg (isHermitian_matsum Finset.univ fun k =>
    isHermitian_real_smul (hA k) (ϱ k ω))]
  ring

/-- **Book §4.6.2**, lower-expectation display (C4-13):
`𝔼 λ_min(Y) ≥ −√(2 v log d)` — obtained by instantiating the λ_max bound at the
negated coefficients (`−Y` is the series over `−A_k`; the source argues via the
distributional symmetry `−Y ∼ Y`, which is the same computation).

**Author note.** This pointwise-support form is retained for compatibility; see
`rademacher_herm_min_expectation_of_isRademacher` for the source-faithful
law-only sibling. -/
theorem rademacher_herm_min_expectation
    (hmeas : ∀ k, Measurable (ϱ k)) (hlaw : ∀ k, IsRademacher (ϱ k) μ)
    (hrange : ∀ k ω, ϱ k ω = 1 ∨ ϱ k ω = -1)
    (hind : ProbabilityTheory.iIndepFun ϱ μ)
    (hA : ∀ k, (A k).IsHermitian) :
    -Real.sqrt (2 * ‖∑ k, (A k) ^ 2‖ * Real.log (Fintype.card n)) ≤
      ∫ ω, lambdaMin (isHermitian_matsum Finset.univ
        (fun k => isHermitian_real_smul (hA k) (ϱ k ω))) ∂μ := by
  have hmain := rademacher_herm_expectation hmeas hlaw hrange hind
    (fun k => (hA k).neg)
  have hvar : (∑ k, (-(A k)) ^ 2) = ∑ k, (A k) ^ 2 := by
    exact Finset.sum_congr rfl fun k _ => neg_sq _
  rw [hvar] at hmain
  have hcongr : (∫ ω, lambdaMin (isHermitian_matsum Finset.univ
      (fun k => isHermitian_real_smul (hA k) (ϱ k ω))) ∂μ) =
      -∫ ω, lambdaMax (isHermitian_matsum Finset.univ
        (fun k => isHermitian_real_smul ((hA k).neg) (ϱ k ω))) ∂μ := by
    rw [← MeasureTheory.integral_neg]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by
      exact lambdaMin_series_eq_neg_lambdaMax_neg hA ω)
  rw [hcongr]
  linarith

/-- **Book §4.6.2**, lower-tail display (C4-13):
`P(λ_min(Y) ≤ −t) ≤ d·e^{−t²/(2v)}` for `t ≥ 0`.

**Author note.** This pointwise-support form is retained for compatibility; see
`rademacher_herm_min_tail_of_isRademacher` for the source-faithful law-only
sibling. -/
theorem rademacher_herm_min_tail
    (hmeas : ∀ k, Measurable (ϱ k)) (hlaw : ∀ k, IsRademacher (ϱ k) μ)
    (hrange : ∀ k ω, ϱ k ω = 1 ∨ ϱ k ω = -1)
    (hind : ProbabilityTheory.iIndepFun ϱ μ)
    (hA : ∀ k, (A k).IsHermitian) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | lambdaMin (isHermitian_matsum Finset.univ
        (fun k => isHermitian_real_smul (hA k) (ϱ k ω))) ≤ -t} ≤
      (Fintype.card n : ℝ) *
        Real.exp (-(t ^ 2) / (2 * ‖∑ k, (A k) ^ 2‖)) := by
  have hmain := rademacher_herm_tail hmeas hlaw hrange hind
    (fun k => (hA k).neg) ht
  have hvar : (∑ k, (-(A k)) ^ 2) = ∑ k, (A k) ^ 2 := by
    exact Finset.sum_congr rfl fun k _ => neg_sq _
  rw [hvar] at hmain
  have hevent : {ω | lambdaMin (isHermitian_matsum Finset.univ
      (fun k => isHermitian_real_smul (hA k) (ϱ k ω))) ≤ -t} =
      {ω | t ≤ lambdaMax (isHermitian_matsum Finset.univ
        (fun k => isHermitian_real_smul ((hA k).neg) (ϱ k ω)))} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    rw [lambdaMin_series_eq_neg_lambdaMax_neg hA ω]
    constructor <;> intro h <;> linarith
  rw [hevent]
  exact hmain

end RademacherHermitian

end MatrixConcentration


set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# Matrix Rademacher series with rectangular coefficients (Tropp §4.1/§4.6.5)

* `rademacher_series_rect_expectation`/`rademacher_series_rect_tail` —
  **Book Theorem 4.1.1** (C4-02), Rademacher case:
  for `Z = Σ_k ϱ_k B_k` with fixed `d₁ × d₂` coefficients,
  `v(Z) = max{‖ΣB_kB_k*‖, ‖ΣB_k*B_k‖}` ((4.1.4)),
  `𝔼‖Z‖ ≤ √(2 v log(d₁+d₂))` ((4.1.5)) and
  `P(‖Z‖ ≥ t) ≤ (d₁+d₂)·e^{−t²/(2v)}` ((4.1.6)).
  Faithful translation of the §4.6.5 proof: apply the Hermitian theorem to the
  Hermitian dilation of the series (`H` is real-linear, `‖Z‖ = λ_max(H(Z))`
  by (2.1.27), and `v(H(Z)) = v(Z)` via (2.1.26) + the block-diagonal norm
  identity C2-67);
* `hermDilation_sum_smul` (C4-17): the dilation of the series is the series of the
  dilations;
* `dilation_coeff_sq_norm` (C4-17): `‖Σ_k H(B_k)²‖ = max{‖ΣB_kB_k*‖,‖ΣB_k*B_k‖}`.
The Gaussian case of Theorem 4.1.1 follows the same dilation route from the
Gaussian Hermitian theorem (see the checkpoint; SI-C4-2).
-/

namespace MatrixConcentration

open Matrix Finset MeasureTheory
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section DilationHelpers

/-- **Book §4.6.3**, implicit real-linearity step (C4-17): the Hermitian dilation
commutes with the series
("The second expression for `Y` holds because the Hermitian dilation is
real-linear").  Implicit source declaration. -/
lemma hermDilation_sum_smul (s : Finset ι) (c : ι → ℝ) (B : ι → Matrix m n ℂ) :
    hermDilation (∑ k ∈ s, c k • B k) = ∑ k ∈ s, c k • hermDilation (B k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [show (0 : Matrix m n ℂ) = (0 : ℝ) • (0 : Matrix m n ℂ) by simp,
      hermDilation_smul_real]
    simp
  | insert b t hb iht =>
    rw [Finset.sum_insert hb, Finset.sum_insert hb, hermDilation_add,
      hermDilation_smul_real, iht]

/-- Lean implementation helper: sums of block-diagonal matrices. -/
lemma sum_fromBlocks_diagonal (s : Finset ι) (f : ι → Matrix m m ℂ)
    (g : ι → Matrix n n ℂ) :
    (∑ k ∈ s, Matrix.fromBlocks (f k) 0 0 (g k)) =
      Matrix.fromBlocks (∑ k ∈ s, f k) 0 0 (∑ k ∈ s, g k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Matrix.fromBlocks_zero]
  | insert b t hb iht =>
    rw [Finset.sum_insert hb, Finset.sum_insert hb, Finset.sum_insert hb, iht,
      Matrix.fromBlocks_add]
    simp

/-- **Book eqs. (2.2.9) and (2.2.10)**, the variance identification for the dilated
series (C4-17),
`‖Σ_k H(B_k)²‖ = max{‖Σ_k B_kB_k*‖, ‖Σ_k B_k*B_k‖}` — "In view of the calculation
(2.2.9)/(2.2.10) for the variance statistic of a dilation" rendered at the
coefficient level via (2.1.26) and the block-diagonal norm identity (C2-67).
Implicit source declaration. -/
lemma dilation_coeff_sq_norm (B : ι → Matrix m n ℂ) :
    ‖∑ k, (hermDilation (B k)) ^ 2‖ =
      max ‖∑ k, B k * (B k)ᴴ‖ ‖∑ k, (B k)ᴴ * B k‖ := by
  have h1 : (∑ k, (hermDilation (B k)) ^ 2) =
      Matrix.fromBlocks (∑ k, B k * (B k)ᴴ) 0 0 (∑ k, (B k)ᴴ * B k) := by
    rw [← sum_fromBlocks_diagonal]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pow_two]
    exact hermDilation_sq (B k)
  rw [h1]
  exact l2_opNorm_fromBlocks_diagonal _ _

end DilationHelpers

section RectangularRademacher

variable [IsProbabilityMeasure μ] [Nonempty m] [Nonempty n]
variable {B : ι → Matrix m n ℂ} {ϱ : ι → Ω → ℝ}

/-- **Book Theorem 4.1.1 (Matrix Rademacher Series)**
(§4.1, p. 42), expectation bound (4.1.5), Rademacher case:
`𝔼‖Σ_k ϱ_k B_k‖ ≤ √(2 v(Z) log(d₁+d₂))` with
`v(Z) = max{‖Σ_k B_kB_k*‖, ‖Σ_k B_k*B_k‖}` ((4.1.4)).
Explicit source declaration; faithful translation of the §4.6.5 dilation proof.

**Author note.** Lean additionally assumes the chosen representatives are
pointwise `{−1,1}`-valued. See
`rademacher_series_rect_expectation_of_isRademacher`. -/
theorem rademacher_series_rect_expectation
    (hmeas : ∀ k, Measurable (ϱ k)) (hlaw : ∀ k, IsRademacher (ϱ k) μ)
    (hrange : ∀ k ω, ϱ k ω = 1 ∨ ϱ k ω = -1)
    (hind : ProbabilityTheory.iIndepFun ϱ μ) :
    ∫ ω, ‖∑ k, ϱ k ω • B k‖ ∂μ ≤
      Real.sqrt (2 * max ‖∑ k, B k * (B k)ᴴ‖ ‖∑ k, (B k)ᴴ * B k‖ *
        Real.log (Fintype.card m + Fintype.card n)) := by
  have hmain := rademacher_herm_expectation (μ := μ)
    (A := fun k => hermDilation (B k)) hmeas hlaw hrange hind
    (fun k => isHermitian_hermDilation (B k))
  have hnorm : (∫ ω, ‖∑ k, ϱ k ω • B k‖ ∂μ) =
      ∫ ω, lambdaMax (isHermitian_matsum Finset.univ
        (fun k => isHermitian_real_smul (isHermitian_hermDilation (B k))
          (ϱ k ω))) ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    show ‖∑ k, ϱ k ω • B k‖ = lambdaMax (isHermitian_matsum Finset.univ
      (fun k => isHermitian_real_smul (isHermitian_hermDilation (B k)) (ϱ k ω)))
    have h1 : (∑ k, ϱ k ω • hermDilation (B k)) =
        hermDilation (∑ k, ϱ k ω • B k) :=
      (hermDilation_sum_smul Finset.univ _ _).symm
    have h2 := lambdaMax_congr h1
      (isHermitian_matsum Finset.univ fun k =>
        isHermitian_real_smul (isHermitian_hermDilation (B k)) (ϱ k ω))
      (isHermitian_hermDilation (∑ k, ϱ k ω • B k))
    rw [h2, lambdaMax_hermDilation]
  rw [hnorm]
  refine hmain.trans (le_of_eq ?_)
  rw [dilation_coeff_sq_norm]
  congr 2
  rw [Fintype.card_sum]
  push_cast
  ring

/-- **Book Theorem 4.1.1**, tail bound (4.1.6), Rademacher case:
`P(‖Σ_k ϱ_k B_k‖ ≥ t) ≤ (d₁+d₂)·e^{−t²/(2v)}` for `t ≥ 0`.

**Author note.** As in the Hermitian theorem used here, Lean additionally assumes
the chosen representatives are pointwise `{−1,1}`-valued. See
`rademacher_series_rect_tail_of_isRademacher`. -/
theorem rademacher_series_rect_tail
    (hmeas : ∀ k, Measurable (ϱ k)) (hlaw : ∀ k, IsRademacher (ϱ k) μ)
    (hrange : ∀ k ω, ϱ k ω = 1 ∨ ϱ k ω = -1)
    (hind : ProbabilityTheory.iIndepFun ϱ μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ ‖∑ k, ϱ k ω • B k‖} ≤
      ((Fintype.card m : ℝ) + Fintype.card n) *
        Real.exp (-(t ^ 2) /
          (2 * max ‖∑ k, B k * (B k)ᴴ‖ ‖∑ k, (B k)ᴴ * B k‖)) := by
  have hmain := rademacher_herm_tail (μ := μ)
    (A := fun k => hermDilation (B k)) hmeas hlaw hrange hind
    (fun k => isHermitian_hermDilation (B k)) ht
  have hevent : {ω | t ≤ ‖∑ k, ϱ k ω • B k‖} =
      {ω | t ≤ lambdaMax (isHermitian_matsum Finset.univ
        (fun k => isHermitian_real_smul (isHermitian_hermDilation (B k))
          (ϱ k ω)))} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    have h1 : (∑ k, ϱ k ω • hermDilation (B k)) =
        hermDilation (∑ k, ϱ k ω • B k) :=
      (hermDilation_sum_smul Finset.univ _ _).symm
    have h2 := lambdaMax_congr h1
      (isHermitian_matsum Finset.univ fun k =>
        isHermitian_real_smul (isHermitian_hermDilation (B k)) (ϱ k ω))
      (isHermitian_hermDilation (∑ k, ϱ k ω • B k))
    rw [h2, lambdaMax_hermDilation]
  rw [hevent]
  refine hmain.trans (le_of_eq ?_)
  rw [dilation_coeff_sq_norm]
  congr 2
  rw [Fintype.card_sum]
  push_cast
  ring

end RectangularRademacher

end MatrixConcentration


set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# The master bounds under integrability hypotheses (SI-C4-2 machinery)

The Chapter-3 master bounds were formalized under the book's standing boundedness
convention (§2.2.1).  The Gaussian halves of Theorems 4.1.1/4.6.1 apply them to
*unbounded* modulators — a regularity extension the book invokes silently
(source issue SI-C4-2).  This file closes the gap: it generalizes the chain

  Jensen (2.2.2) → Corollary 3.4.2 → Lemma 3.5.1 → Theorem 3.6.1

from bounded to integrable hypotheses.  The bounded-case pinching argument is
replaced by the classical supporting-hyperplane proof of Jensen's inequality on an
**open** convex set (`concaveOn_isOpen_expectation_le`, via
`geometric_hahn_banach_open_point` and the finite-dimensional continuity of concave
functions); the measurability of `λ_max` is obtained without bounds as a pointwise
limit of the shift formulas (`measurable_lambdaMax_of_forall`).
-/

namespace MatrixConcentration

open Matrix Finset MeasureTheory
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
variable {n : Type*} [Fintype n] [DecidableEq n]

section UnboundedLambdaMax

variable {Y : Ω → Matrix n n ℂ}

/-- Lean implementation helper: without uniform bounds, `ω ↦ λ_max(Y ω)` is
measurable for any measurable family
of Hermitian matrices (pointwise limit of the shift formulas
`‖Y + R·I‖ − R`, which stabilize once `R ≥ ‖Y ω‖`). -/
lemma measurable_lambdaMax_of_forall [Nonempty n] (hY : Measurable Y)
    (hHerm : ∀ ω, (Y ω).IsHermitian) :
    Measurable fun ω => lambdaMax (hHerm ω) := by
  have hR : ∀ R : ℕ, Measurable fun ω => ‖Y ω + (R : ℂ) • (1 : Matrix n n ℂ)‖ - (R : ℝ) := by
    intro R
    have hshift : Measurable fun ω => Y ω + (R : ℂ) • (1 : Matrix n n ℂ) := by
      apply measurable_pi_lambda
      intro i
      apply measurable_pi_lambda
      intro j
      show Measurable fun ω => Y ω i j + ((R : ℂ) • (1 : Matrix n n ℂ)) i j
      exact ((measurable_entry i j).comp hY).add_const _
    exact ((continuous_l2_opNorm.measurable).comp hshift).sub_const _
  refine measurable_of_tendsto_metrizable hR ?_
  rw [tendsto_pi_nhds]
  intro ω
  refine tendsto_atTop_of_eventually_const (i₀ := ⌈‖Y ω‖⌉₊) fun R hle => ?_
  refine (lambdaMax_eq_norm_shift (hHerm ω) ?_).symm
  calc ‖Y ω‖ ≤ (⌈‖Y ω‖⌉₊ : ℝ) := Nat.le_ceil _
  _ ≤ (R : ℝ) := by exact_mod_cast hle

/-- Lean implementation helper: the `λ_min` version, via
`λ_min(A) = −λ_max(−A)`. -/
lemma measurable_lambdaMin_of_forall [Nonempty n] (hY : Measurable Y)
    (hHerm : ∀ ω, (Y ω).IsHermitian) :
    Measurable fun ω => lambdaMin (hHerm ω) := by
  have heq : (fun ω => lambdaMin (hHerm ω)) =
      fun ω => -(lambdaMax (hHerm ω).neg) :=
    funext fun ω => by
      have := lambdaMax_neg (hHerm ω)
      linarith
  rw [heq]
  have hnegY : Measurable fun ω => -(Y ω) := by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    show Measurable fun ω => -(Y ω i j)
    exact ((measurable_entry i j).comp hY).neg
  exact (measurable_lambdaMax_of_forall hnegY fun ω => (hHerm ω).neg).neg

end UnboundedLambdaMax

section ScalarLogJensen

/-- Lean implementation helper: without uniform bounds, `𝔼 log Z ≤ log 𝔼Z` for an
a.e.-positive integrable
`Z` with integrable logarithm (tangent-line argument at `m = 𝔼Z`). -/
lemma integral_log_le_log_integral' [IsProbabilityMeasure μ] {Z : Ω → ℝ}
    (hpos : ∀ᵐ ω ∂μ, 0 < Z ω) (hZint : Integrable Z μ)
    (hlogint : Integrable (fun ω => Real.log (Z ω)) μ) :
    ∫ ω, Real.log (Z ω) ∂μ ≤ Real.log (∫ ω, Z ω ∂μ) := by
  set m : ℝ := ∫ ω, Z ω ∂μ with hm
  have hmpos : 0 < m := by
    rw [hm]
    rw [MeasureTheory.integral_pos_iff_support_of_nonneg_ae
      (hpos.mono fun ω h => h.le) hZint]
    have h1 : {ω | 0 < Z ω} ⊆ Function.support Z := fun ω h => ne_of_gt h
    have h2 : μ {ω | ¬ (0 < Z ω)} = 0 := MeasureTheory.ae_iff.mp hpos
    calc (0 : ℝ≥0∞) < 1 := by norm_num
    _ = μ Set.univ := (MeasureTheory.measure_univ).symm
    _ = μ ({ω | 0 < Z ω} ∪ {ω | ¬ (0 < Z ω)}) := by
        congr 1
        ext ω
        simp only [Set.mem_univ, Set.mem_union, Set.mem_setOf_eq, true_iff]
        exact or_not
    _ ≤ μ {ω | 0 < Z ω} + μ {ω | ¬ (0 < Z ω)} := MeasureTheory.measure_union_le _ _
    _ = μ {ω | 0 < Z ω} := by rw [h2, add_zero]
    _ ≤ μ (Function.support Z) := MeasureTheory.measure_mono h1
  have htangent : ∀ᵐ ω ∂μ, Real.log (Z ω) ≤ Real.log m + (Z ω / m - 1) := by
    filter_upwards [hpos] with ω hzpos
    have h1 : Real.log (Z ω / m) ≤ Z ω / m - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hzpos hmpos)
    rw [Real.log_div (ne_of_gt hzpos) (ne_of_gt hmpos)] at h1
    linarith
  have hint2 : Integrable (fun ω => Real.log m + (Z ω / m - 1)) μ :=
    (integrable_const _).add ((hZint.div_const m).sub (integrable_const 1))
  have h3 := integral_mono_ae hlogint hint2 htangent
  have hsubint : Integrable (fun ω => Z ω / m - 1) μ :=
    (hZint.div_const m).sub (integrable_const 1)
  have h4 : (∫ ω, (Real.log m + (Z ω / m - 1)) ∂μ) = Real.log m := by
    rw [integral_add (integrable_const _) hsubint]
    have h5 : (∫ ω, (Z ω / m - 1) ∂μ) = 0 := by
      rw [integral_sub (hZint.div_const m) (integrable_const 1), integral_div,
        integral_const]
      simp only [MeasureTheory.probReal_univ, one_smul, smul_eq_mul]
      rw [← hm]
      field_simp
      norm_num
    rw [h5, add_zero, integral_const]
    simp
  rw [h4] at h3
  exact h3

end ScalarLogJensen

section SupportingHyperplane

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Lean implementation helper: the supporting-hyperplane (superdifferential)
existence theorem for a concave
function on an open convex set in a finite-dimensional space: at any point of the
set there is an affine majorant touching there.  Recovered classical prerequisite
for the unbounded Jensen inequality (C3-23′). -/
theorem exists_affine_majorant [FiniteDimensional ℝ E] {s : Set E}
    (hs : IsOpen s) (hsc : Convex ℝ s) {f : E → ℝ} (hf : ConcaveOn ℝ s f)
    {x₀ : E} (hx₀ : x₀ ∈ s) :
    ∃ ψ : E →L[ℝ] ℝ, ∀ y ∈ s, f y ≤ f x₀ + (ψ x₀ - ψ y) := by
  classical
  have hcont : ContinuousOn f s := hf.continuousOn hs
  -- the strict hypograph is open and convex
  set U : Set (E × ℝ) := {p | p.1 ∈ s ∧ p.2 < f p.1} with hU
  have hUconv : Convex ℝ U := by
    rintro p ⟨hp1, hp2⟩ q ⟨hq1, hq2⟩ a b ha hb hab
    refine ⟨hsc hp1 hq1 ha hb hab, ?_⟩
    have hcc := hf.2 hp1 hq1 ha hb hab
    show a • p.2 + b • q.2 < f (a • p.1 + b • q.1)
    rcases eq_or_lt_of_le ha with ha0 | hapos
    · have hb1 : b = 1 := by linarith
      simp only [← ha0, hb1, zero_smul, one_smul, zero_add] at hcc ⊢
      exact lt_of_lt_of_le hq2 hcc
    · have h1 : a • p.2 + b • q.2 < a • f p.1 + b • f q.1 := by
        have h2 : a • p.2 < a • f p.1 := by
          exact (smul_lt_smul_iff_of_pos_left hapos).mpr hp2
        have h3 : b • q.2 ≤ b • f q.1 := smul_le_smul_of_nonneg_left hq2.le hb
        linarith [h2, h3]
      exact lt_of_lt_of_le h1 hcc
  have hUopen : IsOpen U := by
    rw [Metric.isOpen_iff]
    rintro ⟨y, r⟩ ⟨hy, hr⟩
    have hcy : ContinuousAt f y := hcont.continuousAt (hs.mem_nhds hy)
    set ε : ℝ := (f y - r) / 2 with hε
    have hεpos : 0 < ε := by
      rw [hε]
      linarith
    obtain ⟨δ₁, hδ₁, hball₁⟩ := Metric.continuousAt_iff.mp hcy ε hεpos
    obtain ⟨δ₂, hδ₂, hball₂⟩ := Metric.isOpen_iff.mp hs y hy
    refine ⟨min (min δ₁ δ₂) ε, by positivity, ?_⟩
    rintro ⟨z, t⟩ hzt
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff] at hzt
    obtain ⟨hz, ht⟩ := hzt
    have hzs : z ∈ s := hball₂ (lt_of_lt_of_le hz
      (le_trans (min_le_left _ _) (min_le_right _ _)))
    refine ⟨hzs, ?_⟩
    have h1 : |f z - f y| < ε := by
      have := hball₁ (lt_of_lt_of_le hz
        (le_trans (min_le_left _ _) (min_le_left _ _)))
      rwa [Real.dist_eq] at this
    have h2 : |t - r| < ε := by
      have := lt_of_lt_of_le ht (min_le_right _ _)
      rwa [Real.dist_eq] at this
    have h3 := abs_lt.mp h1
    have h4 := abs_lt.mp h2
    rw [hε] at h3 h4
    linarith [h3.1, h4.2]
  -- the touching point is not in the strict hypograph
  have hx₀U : ((x₀, f x₀) : E × ℝ) ∉ U := fun h => lt_irrefl _ h.2
  obtain ⟨φ, hφ⟩ := geometric_hahn_banach_open_point hUconv hUopen hx₀U
  -- decompose φ(y, r) = ψ(y) + r·c
  set ψ : E →L[ℝ] ℝ := φ.comp (ContinuousLinearMap.inl ℝ E ℝ) with hψ
  set c : ℝ := φ (0, 1) with hc
  have hdecomp : ∀ (y : E) (r : ℝ), φ (y, r) = ψ y + r * c := by
    intro y r
    have h1 : ((y, r) : E × ℝ) = (y, 0) + r • ((0 : E), (1 : ℝ)) := by
      simp [Prod.ext_iff]
    rw [h1, map_add, map_smul]
    simp only [hψ, hc, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
      smul_eq_mul]
  -- c > 0 (push r below f x₀ at x₀)
  have hcpos : 0 < c := by
    have h1 : ((x₀, f x₀ - 1) : E × ℝ) ∈ U := by
      refine ⟨hx₀, ?_⟩
      show f x₀ - 1 < f x₀
      linarith
    have h2 := hφ _ h1
    rw [hdecomp, hdecomp] at h2
    nlinarith
  -- the affine majorant
  refine ⟨(c⁻¹ • ψ : E →L[ℝ] ℝ), fun y hy => ?_⟩
  have hkey : ψ y + f y * c ≤ ψ x₀ + f x₀ * c := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have h1 : ((y, f y - ε / c) : E × ℝ) ∈ U := by
      refine ⟨hy, ?_⟩
      show f y - ε / c < f y
      have : 0 < ε / c := by positivity
      linarith
    have h2 := hφ _ h1
    rw [hdecomp, hdecomp] at h2
    have h3 : (f y - ε / c) * c = f y * c - ε := by
      field_simp
    nlinarith
  have h5 : f y ≤ f x₀ + (c⁻¹ * ψ x₀ - c⁻¹ * ψ y) := by
    have h6 : f y * c ≤ f x₀ * c + (ψ x₀ - ψ y) := by linarith
    have h7 := mul_le_mul_of_nonneg_right h6 (inv_pos.mpr hcpos).le
    calc f y = f y * c * c⁻¹ := by field_simp
    _ ≤ (f x₀ * c + (ψ x₀ - ψ y)) * c⁻¹ := h7
    _ = f x₀ + (c⁻¹ * ψ x₀ - c⁻¹ * ψ y) := by field_simp
  simpa using h5

/-- Lean implementation helper: **Jensen's inequality on an open convex set**
(C3-23′), for `f` concave on an
open convex `s` in a finite-dimensional space and an integrable random vector `A`
supported in `s` whose mean lies in `s`, `𝔼 f(A) ≤ f(𝔼A)`.  No boundedness or
closedness is required (supporting-hyperplane proof).  Recovered prerequisite for
the Gaussian case of Chapter 4 (the book's silent regularity extension,
SI-C4-2). -/
theorem concaveOn_isOpen_expectation_le [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    [IsProbabilityMeasure μ] {s : Set E} (hs : IsOpen s) (hsc : Convex ℝ s)
    {f : E → ℝ} (hf : ConcaveOn ℝ s f)
    {A : Ω → E} (hAint : Integrable A μ)
    (hAmem : ∀ᵐ ω ∂μ, A ω ∈ s) (hmean : (∫ ω, A ω ∂μ) ∈ s)
    (hfAint : Integrable (fun ω => f (A ω)) μ) :
    ∫ ω, f (A ω) ∂μ ≤ f (∫ ω, A ω ∂μ) := by
  obtain ⟨ψ, hψ⟩ := exists_affine_majorant hs hsc hf hmean
  have hmaj : ∀ᵐ ω ∂μ, f (A ω) ≤ f (∫ ω', A ω' ∂μ) +
      (ψ (∫ ω', A ω' ∂μ) - ψ (A ω)) := by
    filter_upwards [hAmem] with ω h
    exact hψ _ h
  have hψint : Integrable (fun ω => ψ (A ω)) μ :=
    ContinuousLinearMap.integrable_comp ψ hAint
  have hint2 : Integrable (fun ω => f (∫ ω', A ω' ∂μ) +
      (ψ (∫ ω', A ω' ∂μ) - ψ (A ω))) μ :=
    (integrable_const _).add ((integrable_const _).sub hψint)
  have h1 := integral_mono_ae hfAint hint2 hmaj
  have hsub : Integrable (fun ω => ψ (∫ ω', A ω' ∂μ) - ψ (A ω)) μ :=
    (integrable_const _).sub hψint
  have h2 : (∫ ω, (f (∫ ω', A ω' ∂μ) +
      (ψ (∫ ω', A ω' ∂μ) - ψ (A ω))) ∂μ) = f (∫ ω', A ω' ∂μ) := by
    rw [integral_add (integrable_const _) hsub,
      integral_sub (integrable_const _) hψint,
      ContinuousLinearMap.integral_comp_comm ψ hAint, integral_const,
      integral_const]
    simp
  rw [h2] at h1
  exact h1

end SupportingHyperplane

section UnboundedCor

variable [IsProbabilityMeasure μ]

/-- **Book Corollary 3.4.2 under integrability hypotheses** (C3-22′, the regularity
extension SI-C4-2): `𝔼 tr exp(H + X) ≤ tr exp(H + log 𝔼e^X)` for a measurable
random Hermitian `X` with Bochner-integrable exponential, integrable trace
exponential, and positive-definite mgf.  Same proof as Corollary 3.4.2 with the
pinched Jensen replaced by `concaveOn_isOpen_expectation_le`. -/
theorem expectation_trace_exp_add_le' {Hm : Matrix n n ℂ} (hHm : Hm.IsHermitian)
    {X : Ω → Matrix n n ℂ} (hX : Measurable X) (hHerm : ∀ ω, (X ω).IsHermitian)
    (hexpint : Integrable (fun ω => NormedSpace.exp (X ω)) μ)
    (htrint : Integrable (fun ω => ((NormedSpace.exp (Hm + X ω)).trace).re) μ)
    (hpd : (expectation μ fun ω => NormedSpace.exp (X ω)).PosDef) :
    ∫ ω, ((NormedSpace.exp (Hm + X ω)).trace).re ∂μ ≤
      ((NormedSpace.exp (Hm + CFC.log
        (expectation μ fun ω => NormedSpace.exp (X ω)))).trace).re := by
  classical
  haveI : FiniteDimensional ℝ (Matrix n n ℂ) :=
    Module.Finite.trans (R := ℝ) ℂ (Matrix n n ℂ)
  have hf := lieb_trace_exp_log_concave Hm hHm
  set g : Matrix n n ℂ → ℝ :=
    fun x => ((NormedSpace.exp (Hm + CFC.log (hermPart x))).trace).re with hgdef
  have hgconc : ConcaveOn ℝ (hermPart ⁻¹' {A : Matrix n n ℂ | A.PosDef}) g :=
    hf.comp_affineMap hermPart.toAffineMap
  have hsconv : Convex ℝ (hermPart ⁻¹' {A : Matrix n n ℂ | A.PosDef}) :=
    convex_posDef.linear_preimage hermPart
  set A : Ω → Matrix n n ℂ := fun ω => NormedSpace.exp (X ω) with hAdef
  have hApd : ∀ ω, (A ω).PosDef := fun ω => posDef_exp (hHerm ω)
  have hAmem : ∀ ω, A ω ∈ hermPart ⁻¹' {M : Matrix n n ℂ | M.PosDef} := fun ω => by
    show hermPart (A ω) ∈ {M : Matrix n n ℂ | M.PosDef}
    rw [hermPart_of_isHermitian (hApd ω).1]
    exact hApd ω
  have hEA : (∫ ω, A ω ∂μ) = expectation μ A := (expectation_eq_integral hexpint).symm
  have hEAherm : (expectation μ A).IsHermitian :=
    isHermitian_expectation (Filter.Eventually.of_forall fun ω => (hApd ω).1)
  have hmean : (∫ ω, A ω ∂μ) ∈ hermPart ⁻¹' {M : Matrix n n ℂ | M.PosDef} := by
    show hermPart (∫ ω, A ω ∂μ) ∈ {M : Matrix n n ℂ | M.PosDef}
    rw [hEA, hermPart_of_isHermitian hEAherm]
    exact hpd
  have hgA : ∀ ω, g (A ω) = ((NormedSpace.exp (Hm + X ω)).trace).re := fun ω => by
    rw [hgdef]
    show ((NormedSpace.exp (Hm + CFC.log (hermPart (A ω)))).trace).re = _
    rw [hermPart_of_isHermitian (hApd ω).1]
    show ((NormedSpace.exp (Hm + CFC.log (NormedSpace.exp (X ω)))).trace).re = _
    rw [log_exp_eq (hHerm ω)]
  have hfAint : Integrable (fun ω => g (A ω)) μ :=
    htrint.congr (Filter.Eventually.of_forall fun ω => (hgA ω).symm)
  have hjensen := concaveOn_isOpen_expectation_le (μ := μ)
    isOpen_hermPart_preimage_posDef hsconv hgconc hexpint
    (Filter.Eventually.of_forall hAmem) hmean hfAint
  have hLHS : (∫ ω, g (A ω) ∂μ) = ∫ ω, ((NormedSpace.exp (Hm + X ω)).trace).re ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω => hgA ω)
  have hRHS : g (∫ ω, A ω ∂μ) = ((NormedSpace.exp (Hm + CFC.log
      (expectation μ fun ω => NormedSpace.exp (X ω)))).trace).re := by
    rw [hgdef]
    show ((NormedSpace.exp (Hm + CFC.log (hermPart (∫ ω, A ω ∂μ)))).trace).re = _
    rw [hEA, hermPart_of_isHermitian hEAherm]
  rw [← hLHS, ← hRHS]
  exact hjensen

end UnboundedCor

section UnboundedSubadditivity

variable [IsProbabilityMeasure μ]
variable {ι : Type*} [DecidableEq ι]

/-- Lean implementation helper: the peeling step under integrability hypotheses
(C3-26′). -/
theorem indep_peel_trace_exp' {U V : Ω → Matrix n n ℂ}
    (hUmeas : Measurable U) (hVmeas : Measurable V)
    (hUherm : ∀ ω, (U ω).IsHermitian) (hVherm : ∀ ω, (V ω).IsHermitian)
    (hUexp : Integrable (fun ω => Real.exp ‖U ω‖) μ)
    (hVexp : Integrable (fun ω => Real.exp ‖V ω‖) μ)
    (hVexpint : Integrable (fun ω => NormedSpace.exp (V ω)) μ)
    (hVpd : (expectation μ fun ω => NormedSpace.exp (V ω)).PosDef)
    (hindep : ProbabilityTheory.IndepFun U V μ) :
    ∫ ω, ((NormedSpace.exp (U ω + V ω)).trace).re ∂μ ≤
      ∫ ω, ((NormedSpace.exp (U ω + CFC.log
        (expectation μ fun ω' => NormedSpace.exp (V ω')))).trace).re ∂μ := by
  classical
  set F : Matrix n n ℂ × Matrix n n ℂ → ℝ :=
    fun q => ((NormedSpace.exp (q.1 + q.2)).trace).re with hFdef
  have hFmeas : Measurable F :=
    measurable_trace_exp_re (measurable_matadd measurable_fst measurable_snd)
  have hpairmeas : Measurable fun ω => (U ω, V ω) := hUmeas.prodMk hVmeas
  have hlaw : μ.map (fun ω => (U ω, V ω)) = (μ.prod μ).map (Prod.map U V) := by
    rw [hindep.map_prod_eq_prod_map_map hUmeas.aemeasurable hVmeas.aemeasurable]
    exact MeasureTheory.Measure.map_prod_map μ μ hUmeas hVmeas
  have hghost : (∫ ω, F (U ω, V ω) ∂μ) = ∫ p, F (U p.1, V p.2) ∂(μ.prod μ) := by
    have h1 : (∫ ω, F (U ω, V ω) ∂μ) = ∫ q, F q ∂(μ.map fun ω => (U ω, V ω)) :=
      (integral_map hpairmeas.aemeasurable hFmeas.aestronglyMeasurable).symm
    have h2 : (∫ q, F q ∂((μ.prod μ).map (Prod.map U V))) =
        ∫ p, F (Prod.map U V p) ∂(μ.prod μ) :=
      integral_map (hUmeas.prodMap hVmeas).aemeasurable hFmeas.aestronglyMeasurable
    rw [h1, hlaw, h2]
    rfl
  have hGmeas : Measurable fun p : Ω × Ω => F (U p.1, V p.2) :=
    hFmeas.comp ((hUmeas.comp measurable_fst).prodMk (hVmeas.comp measurable_snd))
  have hprodint : Integrable
      (fun p : Ω × Ω => Real.exp ‖U p.1‖ * Real.exp ‖V p.2‖) (μ.prod μ) :=
    hUexp.mul_prod hVexp
  have hGint : Integrable (fun p : Ω × Ω => F (U p.1, V p.2)) (μ.prod μ) := by
    refine Integrable.mono'
      (hprodint.const_mul (Fintype.card n : ℝ)) hGmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs]
    have h2 := abs_trace_exp_re_le ((hUherm p.1).add (hVherm p.2))
      (norm_add_le (U p.1) (V p.2))
    rw [Real.exp_add] at h2
    exact h2
  have hfubini : (∫ p, F (U p.1, V p.2) ∂(μ.prod μ)) =
      ∫ ω, (∫ ω', F (U ω, V ω') ∂μ) ∂μ :=
    MeasureTheory.integral_prod _ hGint
  have hinner : ∀ ω, (∫ ω', F (U ω, V ω') ∂μ) ≤
      ((NormedSpace.exp (U ω + CFC.log
        (expectation μ fun ω' => NormedSpace.exp (V ω')))).trace).re := fun ω => by
    refine expectation_trace_exp_add_le' (hUherm ω) hVmeas hVherm hVexpint ?_ hVpd
    refine Integrable.mono' (hVexp.const_mul
      ((Fintype.card n : ℝ) * Real.exp ‖U ω‖)) ?_
      (Filter.Eventually.of_forall fun ω' => ?_)
    · exact (measurable_trace_exp_re
        (measurable_matadd measurable_const hVmeas)).aestronglyMeasurable
    · rw [Real.norm_eq_abs]
      have h2 := abs_trace_exp_re_le ((hUherm ω).add (hVherm ω'))
        (norm_add_le (U ω) (V ω'))
      rw [Real.exp_add] at h2
      refine h2.trans (le_of_eq ?_)
      ring
  have hInt1 : Integrable (fun ω => ∫ ω', F (U ω, V ω') ∂μ) μ :=
    hGint.integral_prod_left
  have hInt2 : Integrable (fun ω => ((NormedSpace.exp (U ω + CFC.log
      (expectation μ fun ω' => NormedSpace.exp (V ω')))).trace).re) μ := by
    set L := CFC.log (expectation μ fun ω' => NormedSpace.exp (V ω')) with hLdef
    refine Integrable.mono' (hUexp.const_mul
      ((Fintype.card n : ℝ) * Real.exp ‖L‖))
      ((measurable_trace_exp_re
        (measurable_matadd hUmeas measurable_const)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    have h2 := abs_trace_exp_re_le ((hUherm ω).add (isHermitian_cfc_log _))
      (norm_add_le (U ω) L)
    rw [Real.exp_add] at h2
    refine h2.trans (le_of_eq ?_)
    ring
  calc (∫ ω, ((NormedSpace.exp (U ω + V ω)).trace).re ∂μ)
      = ∫ ω, (∫ ω', F (U ω, V ω') ∂μ) ∂μ := by rw [← hfubini, ← hghost]
  _ ≤ ∫ ω, ((NormedSpace.exp (U ω + CFC.log
        (expectation μ fun ω' => NormedSpace.exp (V ω')))).trace).re ∂μ :=
      integral_mono hInt1 hInt2 hinner

/-- Lean implementation helper: Book Lemma 3.5.1's θ = 1 core under integrability
hypotheses (C3-25′), for a family
carries all exponential norm-moments, so every product integrability needed by the
ghost-copy/Fubini argument is available through
`iIndepFun.integrable_exp_mul_sum`. -/
theorem trace_exp_sum_le_aux' [Fintype ι] (s : Finset ι)
    {X : ι → Ω → Matrix n n ℂ}
    (hmeas : ∀ k, Measurable (X k)) (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hexpc : ∀ k, ∀ c : ℝ, Integrable (fun ω => Real.exp (c * ‖X k ω‖)) μ)
    (hind : ProbabilityTheory.iIndepFun X μ)
    (hmgfpd : ∀ k, (expectation μ fun ω => NormedSpace.exp (X k ω)).PosDef)
    {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    ∫ ω, ((NormedSpace.exp (H + ∑ k ∈ s, X k ω)).trace).re ∂μ ≤
      ((NormedSpace.exp (H + ∑ k ∈ s,
        CFC.log (expectation μ fun ω => NormedSpace.exp (X k ω)))).trace).re := by
  classical
  -- the norm family is independent with all exponential moments
  have hWmeas : ∀ k, Measurable fun ω => ‖X k ω‖ := fun k =>
    continuous_l2_opNorm.measurable.comp (hmeas k)
  have hWind : ProbabilityTheory.iIndepFun (fun k ω => ‖X k ω‖) μ :=
    hind.comp _ fun k => continuous_l2_opNorm.measurable
  induction s using Finset.induction_on generalizing H with
  | empty =>
    simp only [Finset.sum_empty, add_zero]
    rw [MeasureTheory.integral_const, MeasureTheory.probReal_univ, one_smul]
  | insert a s ha ih =>
    have hUmeas : Measurable fun ω => H + ∑ k ∈ s, X k ω :=
      measurable_matadd measurable_const (measurable_matsum s hmeas)
    have hUherm : ∀ ω, (H + ∑ k ∈ s, X k ω).IsHermitian := fun ω =>
      hH.add (isHermitian_matsum s fun k => hherm k ω)
    -- exponential integrability of the accumulated sum
    have hsumexp : Integrable
        (fun ω => Real.exp ((1 : ℝ) * (∑ k ∈ s, fun ω' => ‖X k ω'‖) ω)) μ := by
      refine ProbabilityTheory.iIndepFun.integrable_exp_mul_sum hWind hWmeas
        fun k _ => ?_
      simpa using hexpc k 1
    have hUexp : Integrable (fun ω => Real.exp ‖H + ∑ k ∈ s, X k ω‖) μ := by
      refine Integrable.mono' (hsumexp.const_mul (Real.exp ‖H‖)) ?_
        (Filter.Eventually.of_forall fun ω => ?_)
      · exact (Real.continuous_exp.measurable.comp
          (continuous_l2_opNorm.measurable.comp hUmeas)).aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        have h1 : ‖H + ∑ k ∈ s, X k ω‖ ≤ ‖H‖ + ∑ k ∈ s, ‖X k ω‖ := by
          calc ‖H + ∑ k ∈ s, X k ω‖ ≤ ‖H‖ + ‖∑ k ∈ s, X k ω‖ := norm_add_le _ _
          _ ≤ ‖H‖ + ∑ k ∈ s, ‖X k ω‖ := by
              have := norm_sum_le s (fun k => X k ω)
              linarith
        calc Real.exp ‖H + ∑ k ∈ s, X k ω‖ ≤ Real.exp (‖H‖ + ∑ k ∈ s, ‖X k ω‖) :=
              Real.exp_le_exp.mpr h1
        _ = Real.exp ‖H‖ * Real.exp ((1 : ℝ) * (∑ k ∈ s, fun ω' => ‖X k ω'‖) ω) := by
            rw [← Real.exp_add]
            congr 1
            have h2 : ((∑ k ∈ s, fun ω' => ‖X k ω'‖) ω) = ∑ k ∈ s, ‖X k ω‖ := by
              rw [Finset.sum_apply]
            rw [h2]
            ring
    have hVexp : Integrable (fun ω => Real.exp ‖X a ω‖) μ := by
      simpa using hexpc a 1
    have hVexpint : Integrable (fun ω => NormedSpace.exp (X a ω)) μ := by
      refine Integrable.mono' hVexp
        ((measurable_matrixExp_comp (hmeas a)).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun ω => ?_)
      exact l2_opNorm_exp_le (hherm a ω)
    have hVindep : ProbabilityTheory.IndepFun
        (fun ω => H + ∑ k ∈ s, X k ω) (X a) μ := by
      have h1 : ProbabilityTheory.IndepFun
          (fun ω => ∑ k ∈ s, X k ω) (X a) μ := by
        have h2 := ProbabilityTheory.iIndepFun.indepFun_finsetSum_of_notMem
          hind hmeas ha
        have h3 : (∑ k ∈ s, X k) = fun ω => ∑ k ∈ s, X k ω := by
          funext ω
          exact Finset.sum_apply ω s X
        rwa [h3] at h2
      exact h1.comp (φ := fun M : Matrix n n ℂ => H + M) (ψ := id)
        (measurable_matadd measurable_const measurable_id) measurable_id
    have hpeel := indep_peel_trace_exp' (μ := μ) hUmeas (hmeas a) hUherm
      (hherm a) hUexp hVexp hVexpint (hmgfpd a) hVindep
    have hstep1 : (∫ ω, ((NormedSpace.exp (H + ∑ k ∈ insert a s, X k ω)).trace).re ∂μ)
        = ∫ ω, ((NormedSpace.exp ((H + ∑ k ∈ s, X k ω) + X a ω)).trace).re ∂μ := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      show ((NormedSpace.exp (H + ∑ k ∈ insert a s, X k ω)).trace).re =
        ((NormedSpace.exp ((H + ∑ k ∈ s, X k ω) + X a ω)).trace).re
      congr 2
      rw [Finset.sum_insert ha]
      abel
    have hstep2 : (∫ ω, ((NormedSpace.exp ((H + ∑ k ∈ s, X k ω) +
        CFC.log (expectation μ fun ω' => NormedSpace.exp (X a ω')))).trace).re ∂μ)
        = ∫ ω, ((NormedSpace.exp ((H +
            CFC.log (expectation μ fun ω' => NormedSpace.exp (X a ω'))) +
            ∑ k ∈ s, X k ω)).trace).re ∂μ := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      show ((NormedSpace.exp ((H + ∑ k ∈ s, X k ω) +
          CFC.log (expectation μ fun ω' => NormedSpace.exp (X a ω')))).trace).re =
        ((NormedSpace.exp ((H +
          CFC.log (expectation μ fun ω' => NormedSpace.exp (X a ω'))) +
          ∑ k ∈ s, X k ω)).trace).re
      congr 2
      abel
    have hih := ih (H := H + CFC.log (expectation μ fun ω' =>
      NormedSpace.exp (X a ω'))) (hH.add (isHermitian_cfc_log _))
    have hfinal : ((NormedSpace.exp ((H +
        CFC.log (expectation μ fun ω' => NormedSpace.exp (X a ω'))) + ∑ k ∈ s,
        CFC.log (expectation μ fun ω => NormedSpace.exp (X k ω)))).trace).re =
        ((NormedSpace.exp (H + ∑ k ∈ insert a s,
          CFC.log (expectation μ fun ω => NormedSpace.exp (X k ω)))).trace).re := by
      congr 2
      rw [Finset.sum_insert ha]
      abel
    rw [hstep1]
    refine hpeel.trans ?_
    rw [hstep2]
    refine hih.trans ?_
    rw [hfinal]

end UnboundedSubadditivity

section UnboundedMasterBounds

variable [IsProbabilityMeasure μ] [Nonempty n]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Ω → Matrix n n ℂ}

/-- Lean implementation helper: a.e.-positive integrable functions have positive
integral (probability measure). -/
lemma integral_pos_of_ae_pos {Z : Ω → ℝ}
    (hpos : ∀ᵐ ω ∂μ, 0 < Z ω) (hZint : Integrable Z μ) : 0 < ∫ ω, Z ω ∂μ := by
  rw [MeasureTheory.integral_pos_iff_support_of_nonneg_ae
    (hpos.mono fun ω h => h.le) hZint]
  have h1 : {ω | 0 < Z ω} ⊆ Function.support Z := fun ω h => ne_of_gt h
  have h2 : μ {ω | ¬ (0 < Z ω)} = 0 := MeasureTheory.ae_iff.mp hpos
  calc (0 : ℝ≥0∞) < 1 := by norm_num
  _ = μ Set.univ := (MeasureTheory.measure_univ).symm
  _ = μ ({ω | 0 < Z ω} ∪ {ω | ¬ (0 < Z ω)}) := by
      congr 1
      ext ω
      simp only [Set.mem_univ, Set.mem_union, Set.mem_setOf_eq, true_iff]
      exact or_not
  _ ≤ μ {ω | 0 < Z ω} + μ {ω | ¬ (0 < Z ω)} := MeasureTheory.measure_union_le _ _
  _ = μ {ω | 0 < Z ω} := by rw [h2, add_zero]
  _ ≤ μ (Function.support Z) := MeasureTheory.measure_mono h1

/-- Lean implementation helper: package-derived exponential integrability of the
sum's norm. -/
lemma integrable_exp_norm_sum
    (hmeas : ∀ k, Measurable (X k))
    (hexpc : ∀ k, ∀ c : ℝ, Integrable (fun ω => Real.exp (c * ‖X k ω‖)) μ)
    (hind : ProbabilityTheory.iIndepFun X μ) {c : ℝ} (hc : 0 ≤ c) :
    Integrable (fun ω => Real.exp (c * ‖∑ k, X k ω‖)) μ := by
  classical
  have hWmeas : ∀ k, Measurable fun ω => ‖X k ω‖ := fun k =>
    continuous_l2_opNorm.measurable.comp (hmeas k)
  have hWind : ProbabilityTheory.iIndepFun (fun k ω => ‖X k ω‖) μ :=
    hind.comp _ fun k => continuous_l2_opNorm.measurable
  have hsumexp : Integrable
      (fun ω => Real.exp (c * (∑ k, fun ω' => ‖X k ω'‖) ω)) μ :=
    ProbabilityTheory.iIndepFun.integrable_exp_mul_sum hWind hWmeas
      fun k _ => hexpc k c
  refine Integrable.mono' hsumexp ?_ (Filter.Eventually.of_forall fun ω => ?_)
  · exact (Real.continuous_exp.measurable.comp
      ((continuous_l2_opNorm.measurable.comp
        (measurable_matsum Finset.univ hmeas)).const_mul c)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.mpr ?_
    have h1 : ‖∑ k, X k ω‖ ≤ ∑ k, ‖X k ω‖ := norm_sum_le _ _
    have h2 : ((∑ k, fun ω' => ‖X k ω'‖) ω) = ∑ k, ‖X k ω‖ := by
      rw [Finset.sum_apply]
    rw [h2]
    exact mul_le_mul_of_nonneg_left h1 hc

/-- **Book Theorem 3.6.1, eq. (3.6.1), under integrability hypotheses**—the master
expectation bound for a sum of independent random Hermitian matrices with all
exponential norm-moments (the regularity regime of the Gaussian series, SI-C4-2):
for `θ > 0`, `𝔼 λ_max(Σ X_k) ≤ θ⁻¹ log tr exp(Σ_k Ξ_{X_k}(θ))`. -/
theorem unbounded_master_expectation_upper
    (hmeas : ∀ k, Measurable (X k)) (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hexpc : ∀ k, ∀ c : ℝ, Integrable (fun ω => Real.exp (c * ‖X k ω‖)) μ)
    (hind : ProbabilityTheory.iIndepFun X μ)
    {θ : ℝ} (hθ : 0 < θ) (hmgfpd : ∀ k, (matrixMgf μ (X k) θ).PosDef) :
    ∫ ω, lambdaMax (isHermitian_matsum Finset.univ (fun k => hherm k ω)) ∂μ ≤
      θ⁻¹ * Real.log
        ((NormedSpace.exp (∑ k, matrixCgf μ (X k) θ)).trace).re := by
  classical
  set Y : Ω → Matrix n n ℂ := fun ω => ∑ k, X k ω with hYdef
  have hYmeas : Measurable Y := measurable_matsum Finset.univ hmeas
  have hYherm : ∀ ω, (Y ω).IsHermitian := fun ω =>
    isHermitian_matsum Finset.univ fun k => hherm k ω
  have hYhermθ : ∀ ω, (θ • Y ω).IsHermitian := fun ω =>
    isHermitian_real_smul (hYherm ω) θ
  -- the θ-scaled family and its subadditivity bound
  have hXθmeas : ∀ k, Measurable fun ω => θ • X k ω := fun k =>
    (hmeas k).const_smul θ
  have hXθherm : ∀ k ω, (θ • X k ω).IsHermitian := fun k ω =>
    isHermitian_real_smul (hherm k ω) θ
  have hXθexpc : ∀ k c, Integrable
      (fun ω => Real.exp (c * ‖θ • X k ω‖)) μ := fun k c => by
    have h1 := hexpc k (c * |θ|)
    refine h1.congr (Filter.Eventually.of_forall fun ω => ?_)
    show Real.exp (c * |θ| * ‖X k ω‖) = Real.exp (c * ‖θ • X k ω‖)
    rw [norm_smul, Real.norm_eq_abs]
    ring_nf
  have hXθind : ProbabilityTheory.iIndepFun (fun k ω => θ • X k ω) μ := by
    have hsmulmeas : Measurable fun M : Matrix n n ℂ => θ • M := by
      apply measurable_pi_lambda
      intro i
      apply measurable_pi_lambda
      intro j
      show Measurable fun M : Matrix n n ℂ => θ • M i j
      exact (measurable_entry i j).const_smul θ
    exact hind.comp _ fun _ => hsmulmeas
  have hsubadd := trace_exp_sum_le_aux' (μ := μ) Finset.univ hXθmeas hXθherm
    hXθexpc hXθind (fun k => hmgfpd k) (Matrix.isHermitian_zero (n := n))
  simp only [zero_add] at hsubadd
  -- identify with the θ-smul of Y
  have hswap : (∫ ω, ((NormedSpace.exp (θ • Y ω)).trace).re ∂μ) =
      ∫ ω, ((NormedSpace.exp (∑ k, θ • X k ω)).trace).re ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    show ((NormedSpace.exp (θ • ∑ k, X k ω)).trace).re =
      ((NormedSpace.exp (∑ k, θ • X k ω)).trace).re
    rw [Finset.smul_sum (r := θ) (f := fun k => X k ω) (s := Finset.univ)]
  -- integrability package for Y
  have hnormY : Integrable (fun ω => ‖Y ω‖) μ := by
    refine Integrable.mono' (integrable_exp_norm_sum hmeas hexpc hind
      (le_of_lt one_pos)) ?_ (Filter.Eventually.of_forall fun ω => ?_)
    · exact (continuous_l2_opNorm.measurable.comp hYmeas).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), one_mul]
      calc ‖Y ω‖ ≤ Real.exp ‖Y ω‖ - 1 + 1 := by
            have := Real.add_one_le_exp ‖Y ω‖
            linarith
      _ = Real.exp ‖Y ω‖ := by ring
  have hlamint : Integrable
      (fun ω => lambdaMax (isHermitian_matsum Finset.univ
        (fun k => hherm k ω))) μ := by
    refine Integrable.mono' hnormY ((measurable_lambdaMax_of_forall hYmeas
      hYherm).aestronglyMeasurable) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    exact abs_lambdaMax_le (hYherm ω)
  -- Z := λ_max(e^{θY}) = e^{λ_max(θY)}
  set Z : Ω → ℝ := fun ω => Real.exp (lambdaMax (hYhermθ ω)) with hZdef
  have hZmeas : Measurable Z :=
    Real.measurable_exp.comp
      (measurable_lambdaMax_of_forall (hYmeas.const_smul θ) hYhermθ)
  have hZbd : ∀ ω, Z ω ≤ Real.exp (θ * ‖Y ω‖) := fun ω => by
    refine Real.exp_le_exp.mpr ?_
    have h1 := abs_lambdaMax_le (hYhermθ ω)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hθ] at h1
    linarith [abs_le.mp h1]
  have hZint : Integrable Z μ := by
    refine Integrable.mono' (integrable_exp_norm_sum hmeas hexpc hind hθ.le) ?_
      (Filter.Eventually.of_forall fun ω => ?_)
    · exact hZmeas.aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact hZbd ω
  have hlogZint : Integrable (fun ω => Real.log (Z ω)) μ := by
    have h1 : (fun ω => Real.log (Z ω)) =
        fun ω => lambdaMax (hYhermθ ω) := by
      funext ω
      rw [hZdef]
      exact Real.log_exp _
    rw [h1]
    refine Integrable.mono' (hnormY.const_mul θ)
      ((measurable_lambdaMax_of_forall (hYmeas.const_smul θ)
        hYhermθ).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    have h2 := abs_lambdaMax_le (hYhermθ ω)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hθ] at h2
    exact h2
  -- trace exponential integrability
  have htrint : Integrable
      (fun ω => ((NormedSpace.exp (θ • Y ω)).trace).re) μ := by
    refine Integrable.mono' ((integrable_exp_norm_sum hmeas hexpc hind
      hθ.le).const_mul (Fintype.card n : ℝ)) ?_
      (Filter.Eventually.of_forall fun ω => ?_)
    · exact (measurable_trace_exp_re (hYmeas.const_smul θ)).aestronglyMeasurable
    · rw [Real.norm_eq_abs]
      have h2 := abs_trace_exp_re_le (hYhermθ ω) (le_refl ‖θ • Y ω‖)
      refine h2.trans ?_
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hθ]
  -- the Laplace chain: θ·𝔼λmax(Y) = ∫ log Z ≤ log ∫ Z ≤ log 𝔼 tr e^{θY} ≤ log tr exp(Σ cgf)
  have h1 : θ * (∫ ω, lambdaMax (isHermitian_matsum Finset.univ
      (fun k => hherm k ω)) ∂μ) = ∫ ω, Real.log (Z ω) ∂μ := by
    rw [← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    show θ * lambdaMax (isHermitian_matsum Finset.univ (fun k => hherm k ω)) =
      Real.log (Z ω)
    have hZω : Z ω = Real.exp (lambdaMax (hYhermθ ω)) := rfl
    rw [hZω, Real.log_exp]
    exact (lambdaMax_smul_nonneg (hYherm ω) hθ.le (hYhermθ ω)).symm
  have h2 : (∫ ω, Real.log (Z ω) ∂μ) ≤ Real.log (∫ ω, Z ω ∂μ) :=
    integral_log_le_log_integral'
      (Filter.Eventually.of_forall fun ω => Real.exp_pos _) hZint hlogZint
  have h3 : (∫ ω, Z ω ∂μ) ≤ ∫ ω, ((NormedSpace.exp (θ • Y ω)).trace).re ∂μ := by
    refine integral_mono hZint htrint fun ω => ?_
    show Real.exp (lambdaMax (hYhermθ ω)) ≤ _
    exact exp_lambdaMax_le_trace_exp (hYhermθ ω)
  have hZmeanpos : 0 < ∫ ω, Z ω ∂μ :=
    integral_pos_of_ae_pos (Filter.Eventually.of_forall fun ω => Real.exp_pos _)
      hZint
  have h4 : Real.log (∫ ω, Z ω ∂μ) ≤
      Real.log ((NormedSpace.exp (∑ k, matrixCgf μ (X k) θ)).trace).re := by
    refine Real.log_le_log hZmeanpos ?_
    refine h3.trans ?_
    rw [hswap]
    exact hsubadd
  have hchain : θ * (∫ ω, lambdaMax (isHermitian_matsum Finset.univ
      (fun k => hherm k ω)) ∂μ) ≤
      Real.log ((NormedSpace.exp (∑ k, matrixCgf μ (X k) θ)).trace).re := by
    rw [h1]
    exact h2.trans h4
  rw [inv_mul_eq_div, le_div_iff₀ hθ, mul_comm]
  exact hchain

/-- **Book Theorem 3.6.1, eq. (3.6.3), under integrability hypotheses**—the master
tail bound in the unbounded regime: for `θ > 0` and all `t`,
`P(λ_max(Σ X_k) ≥ t) ≤ e^{−θt}·tr exp(Σ_k Ξ_{X_k}(θ))`. -/
theorem unbounded_master_tail_upper
    (hmeas : ∀ k, Measurable (X k)) (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hexpc : ∀ k, ∀ c : ℝ, Integrable (fun ω => Real.exp (c * ‖X k ω‖)) μ)
    (hind : ProbabilityTheory.iIndepFun X μ) (t : ℝ)
    {θ : ℝ} (hθ : 0 < θ) (hmgfpd : ∀ k, (matrixMgf μ (X k) θ).PosDef) :
    μ.real {ω | t ≤ lambdaMax (isHermitian_matsum Finset.univ
        (fun k => hherm k ω))} ≤
      Real.exp (-θ * t) *
        ((NormedSpace.exp (∑ k, matrixCgf μ (X k) θ)).trace).re := by
  classical
  set Y : Ω → Matrix n n ℂ := fun ω => ∑ k, X k ω with hYdef
  have hYmeas : Measurable Y := measurable_matsum Finset.univ hmeas
  have hYherm : ∀ ω, (Y ω).IsHermitian := fun ω =>
    isHermitian_matsum Finset.univ fun k => hherm k ω
  have hYhermθ : ∀ ω, (θ • Y ω).IsHermitian := fun ω =>
    isHermitian_real_smul (hYherm ω) θ
  -- the subadditivity bound, as in the expectation case
  have hXθmeas : ∀ k, Measurable fun ω => θ • X k ω := fun k =>
    (hmeas k).const_smul θ
  have hXθherm : ∀ k ω, (θ • X k ω).IsHermitian := fun k ω =>
    isHermitian_real_smul (hherm k ω) θ
  have hXθexpc : ∀ k c, Integrable
      (fun ω => Real.exp (c * ‖θ • X k ω‖)) μ := fun k c => by
    have h1 := hexpc k (c * |θ|)
    refine h1.congr (Filter.Eventually.of_forall fun ω => ?_)
    show Real.exp (c * |θ| * ‖X k ω‖) = Real.exp (c * ‖θ • X k ω‖)
    rw [norm_smul, Real.norm_eq_abs]
    ring_nf
  have hXθind : ProbabilityTheory.iIndepFun (fun k ω => θ • X k ω) μ := by
    have hsmulmeas : Measurable fun M : Matrix n n ℂ => θ • M := by
      apply measurable_pi_lambda
      intro i
      apply measurable_pi_lambda
      intro j
      show Measurable fun M : Matrix n n ℂ => θ • M i j
      exact (measurable_entry i j).const_smul θ
    exact hind.comp _ fun _ => hsmulmeas
  have hsubadd := trace_exp_sum_le_aux' (μ := μ) Finset.univ hXθmeas hXθherm
    hXθexpc hXθind (fun k => hmgfpd k) (Matrix.isHermitian_zero (n := n))
  simp only [zero_add] at hsubadd
  have hswap : (∫ ω, ((NormedSpace.exp (θ • Y ω)).trace).re ∂μ) =
      ∫ ω, ((NormedSpace.exp (∑ k, θ • X k ω)).trace).re ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    show ((NormedSpace.exp (θ • ∑ k, X k ω)).trace).re =
      ((NormedSpace.exp (∑ k, θ • X k ω)).trace).re
    rw [Finset.smul_sum (r := θ) (f := fun k => X k ω) (s := Finset.univ)]
  -- Markov at level e^{θt} for e^{θλmax(Y)}
  have hevent : {ω | t ≤ lambdaMax (isHermitian_matsum Finset.univ
      (fun k => hherm k ω))} =
      {ω | Real.exp (θ * t) ≤ Real.exp (lambdaMax (hYhermθ ω))} := by
    ext ω
    simp only [Set.mem_setOf_eq, Real.exp_le_exp]
    have hhom := lambdaMax_smul_nonneg (hYherm ω) hθ.le (hYhermθ ω)
    constructor
    · intro h
      rw [hhom]
      exact mul_le_mul_of_nonneg_left h hθ.le
    · intro h
      rw [hhom] at h
      exact le_of_mul_le_mul_left h hθ
  set Z : Ω → ℝ := fun ω => Real.exp (lambdaMax (hYhermθ ω)) with hZdef
  have hZmeas : Measurable Z :=
    Real.measurable_exp.comp
      (measurable_lambdaMax_of_forall (hYmeas.const_smul θ) hYhermθ)
  have hZint : Integrable Z μ := by
    refine Integrable.mono' (integrable_exp_norm_sum hmeas hexpc hind hθ.le) ?_
      (Filter.Eventually.of_forall fun ω => ?_)
    · exact hZmeas.aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      refine Real.exp_le_exp.mpr ?_
      have h1 := abs_lambdaMax_le (hYhermθ ω)
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hθ] at h1
      linarith [abs_le.mp h1]
  have htrint : Integrable
      (fun ω => ((NormedSpace.exp (θ • Y ω)).trace).re) μ := by
    refine Integrable.mono' ((integrable_exp_norm_sum hmeas hexpc hind
      hθ.le).const_mul (Fintype.card n : ℝ)) ?_
      (Filter.Eventually.of_forall fun ω => ?_)
    · exact (measurable_trace_exp_re (hYmeas.const_smul θ)).aestronglyMeasurable
    · rw [Real.norm_eq_abs]
      have h2 := abs_trace_exp_re_le (hYhermθ ω) (le_refl ‖θ • Y ω‖)
      refine h2.trans ?_
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hθ]
  have hmarkov := markov_inequality
    (Filter.Eventually.of_forall fun ω => (Real.exp_pos (lambdaMax (hYhermθ ω))).le)
    hZint (Real.exp_pos (θ * t))
  have hmono : (∫ ω, Z ω ∂μ) ≤
      ((NormedSpace.exp (∑ k, matrixCgf μ (X k) θ)).trace).re := by
    have h3 : (∫ ω, Z ω ∂μ) ≤
        ∫ ω, ((NormedSpace.exp (θ • Y ω)).trace).re ∂μ := by
      refine integral_mono hZint htrint fun ω => ?_
      show Real.exp (lambdaMax (hYhermθ ω)) ≤ _
      exact exp_lambdaMax_le_trace_exp (hYhermθ ω)
    refine h3.trans ?_
    rw [hswap]
    exact hsubadd
  rw [hevent, show Real.exp (-θ * t) = (Real.exp (θ * t))⁻¹ by
    rw [show -θ * t = -(θ * t) by ring, Real.exp_neg], inv_mul_eq_div]
  refine hmarkov.trans ?_
  gcongr

end UnboundedMasterBounds

end MatrixConcentration


set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# Matrix Gaussian series (Tropp §4.1/§4.6, Gaussian cases)

* `gaussian_herm_expectation`/`gaussian_herm_tail` — **Book Theorem 4.6.1**
  (C4-11), Gaussian case, with the λ_min forms
  `gaussian_herm_min_expectation`/`gaussian_herm_min_tail` (C4-13);
* `gaussian_series_rect_expectation`/`gaussian_series_rect_tail` —
  **Book Theorem 4.1.1** (C4-02), Gaussian case, via the
  Hermitian dilation exactly as in §4.6.5.

The proofs are the source's (§4.6.3): the master bounds with the **exact** Gaussian
cgf `Ξ_{γA}(θ) = (θ²/2)A²` (Lemma 4.6.2) substituted — here through the
integrable-hypothesis master bounds of `04_UnboundedMaster` since the Gaussian
modulators are unbounded (SI-C4-2); the exponential-moment package for the family
is supplied by the scalar Gaussian mgf.
-/

namespace MatrixConcentration

open Matrix Finset MeasureTheory
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section GaussianPackage

variable [IsProbabilityMeasure μ]

/-- Lean implementation helper: all exponential absolute moments of a standard
Gaussian (`𝔼 e^{s|γ|} < ∞`), from the two-sided mgf. -/
lemma integrable_exp_abs_isStdGaussian {γ : Ω → ℝ} (hγm : Measurable γ)
    (hγ : IsStdGaussian γ μ) (s : ℝ) :
    Integrable (fun ω => Real.exp (s * |γ ω|)) μ := by
  have h1 := integrable_exp_mul_isStdGaussian hγm hγ s
  have h2 := integrable_exp_mul_isStdGaussian hγm hγ (-s)
  refine Integrable.mono' (h1.add h2) ?_
    (Filter.Eventually.of_forall fun ω => ?_)
  · exact (Real.measurable_exp.comp
      ((measurable_const.mul hγm.abs))).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rcases abs_cases (γ ω) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
    · show Real.exp (s * γ ω) ≤
        ((fun ω => Real.exp (s * γ ω)) + fun ω => Real.exp (-s * γ ω)) ω
      show Real.exp (s * γ ω) ≤ Real.exp (s * γ ω) + Real.exp (-s * γ ω)
      linarith [Real.exp_pos (-s * γ ω)]
    · show Real.exp (s * -γ ω) ≤
        ((fun ω => Real.exp (s * γ ω)) + fun ω => Real.exp (-s * γ ω)) ω
      show Real.exp (s * -γ ω) ≤ Real.exp (s * γ ω) + Real.exp (-s * γ ω)
      have h3 : Real.exp (s * -γ ω) = Real.exp (-s * γ ω) := by ring_nf
      rw [h3]
      linarith [Real.exp_pos (s * γ ω)]

/-- Lean implementation helper: the exponential-moment package for the Gaussian
series family `γ_k • A_k`. -/
lemma gaussian_family_expc {A : ι → Matrix n n ℂ} {γ : ι → Ω → ℝ}
    (hmeas : ∀ k, Measurable (γ k)) (hlaw : ∀ k, IsStdGaussian (γ k) μ)
    (k : ι) (c : ℝ) :
    Integrable (fun ω => Real.exp (c * ‖γ k ω • A k‖)) μ := by
  have h1 := integrable_exp_abs_isStdGaussian (hmeas k) (hlaw k) (c * ‖A k‖)
  refine h1.congr (Filter.Eventually.of_forall fun ω => ?_)
  show Real.exp (c * ‖A k‖ * |γ k ω|) = Real.exp (c * ‖γ k ω • A k‖)
  rw [norm_smul, Real.norm_eq_abs]
  ring_nf

end GaussianPackage

section GaussianHermitian

variable [IsProbabilityMeasure μ] [Nonempty n]
variable {A : ι → Matrix n n ℂ} {γ : ι → Ω → ℝ}

/-- The Gaussian analogue of the cgf-substitution chain: for every `θ`,
`tr exp(Σ_k Ξ_{γ_k A_k}(θ)) ≤ d·e^{(θ²/2)·v}` — here with the **exact** cgf of
Lemma 4.6.2 (no semidefinite substitution needed).  Lean implementation helper. -/
lemma gaussian_cgf_trace_bound
    (hmeas : ∀ k, Measurable (γ k)) (hlaw : ∀ k, IsStdGaussian (γ k) μ)
    (hA : ∀ k, (A k).IsHermitian) (θ : ℝ) :
    ((NormedSpace.exp (∑ k, matrixCgf μ (fun ω => γ k ω • A k) θ)).trace).re ≤
      (Fintype.card n : ℝ) *
        Real.exp (θ ^ 2 / 2 * ‖∑ k, (A k) ^ 2‖) := by
  have hsq : ∀ k, ((A k) ^ 2).PosSemidef := fun k => by
    have h := posSemidef_sq (hA k)
    rwa [← pow_two] at h
  have hsumsq : (∑ k, (A k) ^ 2).PosSemidef := posSemidef_matsum Finset.univ hsq
  have hcgf : (∑ k, matrixCgf μ (fun ω => γ k ω • A k) θ) =
      (θ ^ 2 / 2) • ∑ k, (A k) ^ 2 := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun k _ =>
      gaussian_matrix_cgf (hmeas k) (hlaw k) (hA k) θ
  rw [hcgf]
  have hsumHerm : ((θ ^ 2 / 2) • ∑ k, (A k) ^ 2).IsHermitian :=
    isHermitian_real_smul hsumsq.1 _
  have h3 := trace_re_le_card_mul_lambdaMax (isHermitian_exp hsumHerm)
  refine h3.trans ?_
  have h4 : lambdaMax (isHermitian_exp hsumHerm) =
      Real.exp (lambdaMax hsumHerm) := lambdaMax_exp hsumHerm
  have h5 : lambdaMax hsumHerm = (θ ^ 2 / 2) * lambdaMax hsumsq.1 :=
    lambdaMax_smul_nonneg hsumsq.1 (by positivity) hsumHerm
  have h6 : lambdaMax hsumsq.1 = ‖∑ k, (A k) ^ 2‖ :=
    (posSemidef_l2_opNorm_eq_lambdaMax hsumsq).symm
  rw [h4, h5, h6]

/-- **Book Theorem 4.6.1 (Matrix Gaussian Series, Hermitian Case)**
 (§4.6, p. 51), expectation bound (4.6.3), Gaussian case:
`𝔼 λ_max(Σ_k γ_k A_k) ≤ √(2 v log d)` with `v = ‖Σ_k A_k²‖`.
Explicit source declaration; faithful translation of the §4.6.3 proof, through the
integrable-hypothesis master bounds (SI-C4-2). -/
theorem gaussian_herm_expectation
    (hmeas : ∀ k, Measurable (γ k)) (hlaw : ∀ k, IsStdGaussian (γ k) μ)
    (hind : ProbabilityTheory.iIndepFun γ μ)
    (hA : ∀ k, (A k).IsHermitian) :
    ∫ ω, lambdaMax (isHermitian_matsum Finset.univ
        (fun k => isHermitian_real_smul (hA k) (γ k ω))) ∂μ ≤
      Real.sqrt (2 * ‖∑ k, (A k) ^ 2‖ * Real.log (Fintype.card n)) := by
  classical
  set X : ι → Ω → Matrix n n ℂ := fun k ω => γ k ω • A k with hXdef
  have hXmeas : ∀ k, Measurable (X k) := fun k => by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    show Measurable fun ω => γ k ω • A k i j
    exact (hmeas k).smul_const _
  have hXherm : ∀ k ω, (X k ω).IsHermitian := fun k ω =>
    isHermitian_real_smul (hA k) _
  have hXexpc : ∀ k c, Integrable (fun ω => Real.exp (c * ‖X k ω‖)) μ :=
    fun k c => gaussian_family_expc hmeas hlaw k c
  have hXind : ProbabilityTheory.iIndepFun X μ := by
    refine hind.comp (fun k s => s • A k) fun k => ?_
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    show Measurable fun s : ℝ => s • A k i j
    exact measurable_id.smul_const _
  have hXmgfpd : ∀ (θ : ℝ) k, (matrixMgf μ (X k) θ).PosDef := fun θ k => by
    rw [show matrixMgf μ (X k) θ = matrixMgf μ (fun ω => γ k ω • A k) θ from rfl,
      gaussian_matrix_mgf (hmeas k) (hlaw k) (hA k) θ]
    exact posDef_exp (isHermitian_real_smul ((hA k).pow 2) _)
  refine le_sqrt_of_forall_theta (norm_nonneg _)
    (Real.log_nonneg (by exact_mod_cast Fintype.card_pos)) fun θ hθ => ?_
  have h1 := unbounded_master_expectation_upper (μ := μ) hXmeas hXherm hXexpc
    hXind hθ (hXmgfpd θ)
  refine h1.trans ?_
  have h2 := gaussian_cgf_trace_bound hmeas hlaw hA θ
  have hpos : 0 < ((NormedSpace.exp (∑ k, matrixCgf μ (X k) θ)).trace).re :=
    trace_exp_re_pos (isHermitian_matsum Finset.univ fun k => isHermitian_cfc_log _)
  have h3 : Real.log ((NormedSpace.exp (∑ k, matrixCgf μ (X k) θ)).trace).re ≤
      Real.log ((Fintype.card n : ℝ) *
        Real.exp (θ ^ 2 / 2 * ‖∑ k, (A k) ^ 2‖)) :=
    Real.log_le_log hpos h2
  have h4 : Real.log ((Fintype.card n : ℝ) *
      Real.exp (θ ^ 2 / 2 * ‖∑ k, (A k) ^ 2‖)) =
      Real.log (Fintype.card n) + θ ^ 2 / 2 * ‖∑ k, (A k) ^ 2‖ := by
    rw [Real.log_mul (by exact_mod_cast Fintype.card_pos.ne')
      (Real.exp_pos _).ne', Real.log_exp]
  calc θ⁻¹ * Real.log ((NormedSpace.exp (∑ k, matrixCgf μ (X k) θ)).trace).re
      ≤ θ⁻¹ * (Real.log (Fintype.card n) + θ ^ 2 / 2 * ‖∑ k, (A k) ^ 2‖) := by
        rw [← h4]
        exact mul_le_mul_of_nonneg_left h3 (inv_pos.mpr hθ).le
  _ = θ⁻¹ * Real.log (Fintype.card n) + θ * ‖∑ k, (A k) ^ 2‖ / 2 := by
      field_simp

/-- **Book Theorem 4.6.1**, tail bound (4.6.4)–(4.6.5), Gaussian case:
`P(λ_max(Σ_k γ_k A_k) ≥ t) ≤ d·e^{−t²/(2v)}` for `t ≥ 0`. -/
theorem gaussian_herm_tail
    (hmeas : ∀ k, Measurable (γ k)) (hlaw : ∀ k, IsStdGaussian (γ k) μ)
    (hind : ProbabilityTheory.iIndepFun γ μ)
    (hA : ∀ k, (A k).IsHermitian) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ lambdaMax (isHermitian_matsum Finset.univ
        (fun k => isHermitian_real_smul (hA k) (γ k ω)))} ≤
      (Fintype.card n : ℝ) *
        Real.exp (-(t ^ 2) / (2 * ‖∑ k, (A k) ^ 2‖)) := by
  classical
  set v : ℝ := ‖∑ k, (A k) ^ 2‖ with hv
  set X : ι → Ω → Matrix n n ℂ := fun k ω => γ k ω • A k with hXdef
  have hXmeas : ∀ k, Measurable (X k) := fun k => by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    show Measurable fun ω => γ k ω • A k i j
    exact (hmeas k).smul_const _
  have hXherm : ∀ k ω, (X k ω).IsHermitian := fun k ω =>
    isHermitian_real_smul (hA k) _
  have hXexpc : ∀ k c, Integrable (fun ω => Real.exp (c * ‖X k ω‖)) μ :=
    fun k c => gaussian_family_expc hmeas hlaw k c
  have hXind : ProbabilityTheory.iIndepFun X μ := by
    refine hind.comp (fun k s => s • A k) fun k => ?_
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    show Measurable fun s : ℝ => s • A k i j
    exact measurable_id.smul_const _
  have hXmgfpd : ∀ (θ : ℝ) k, (matrixMgf μ (X k) θ).PosDef := fun θ k => by
    rw [show matrixMgf μ (X k) θ = matrixMgf μ (fun ω => γ k ω • A k) θ from rfl,
      gaussian_matrix_mgf (hmeas k) (hlaw k) (hA k) θ]
    exact posDef_exp (isHermitian_real_smul ((hA k).pow 2) _)
  have hcard1 : (1 : ℝ) ≤ (Fintype.card n : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hPle : ∀ S : Set Ω, μ.real S ≤ 1 := fun S => by
    have h := MeasureTheory.measureReal_mono (μ := μ) (Set.subset_univ S)
    rwa [MeasureTheory.probReal_univ] at h
  rcases eq_or_lt_of_le (norm_nonneg (∑ k, (A k) ^ 2)) with hv0 | hvpos
  · have h1 : -(t ^ 2) / (2 * v) = -(t ^ 2) / 0 := by
      rw [hv, ← hv0, mul_zero]
    rw [hv] at h1 ⊢
    rw [h1, div_zero, Real.exp_zero, mul_one]
    exact (hPle _).trans hcard1
  · rcases eq_or_lt_of_le ht with ht0 | htpos
    · rw [← ht0]
      norm_num
      exact (hPle _).trans hcard1
    · have hθ : (0 : ℝ) < t / v := div_pos htpos hvpos
      have h1 := unbounded_master_tail_upper (μ := μ) hXmeas hXherm hXexpc
        hXind t hθ (hXmgfpd (t / v))
      refine h1.trans ?_
      have h2 := gaussian_cgf_trace_bound hmeas hlaw hA (t / v)
      calc Real.exp (-(t / v) * t) *
          ((NormedSpace.exp (∑ k, matrixCgf μ (X k) (t / v))).trace).re
          ≤ Real.exp (-(t / v) * t) * ((Fintype.card n : ℝ) *
            Real.exp ((t / v) ^ 2 / 2 * v)) :=
          mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
      _ = (Fintype.card n : ℝ) * (Real.exp (-(t / v) * t) *
            Real.exp ((t / v) ^ 2 / 2 * v)) := by ring
      _ = (Fintype.card n : ℝ) * Real.exp (-(t ^ 2) / (2 * v)) := by
          rw [← Real.exp_add]
          congr 1
          field_simp
          ring

/-- **Book §4.6.2**, lower-expectation display, Gaussian case (C4-13). -/
theorem gaussian_herm_min_expectation
    (hmeas : ∀ k, Measurable (γ k)) (hlaw : ∀ k, IsStdGaussian (γ k) μ)
    (hind : ProbabilityTheory.iIndepFun γ μ)
    (hA : ∀ k, (A k).IsHermitian) :
    -Real.sqrt (2 * ‖∑ k, (A k) ^ 2‖ * Real.log (Fintype.card n)) ≤
      ∫ ω, lambdaMin (isHermitian_matsum Finset.univ
        (fun k => isHermitian_real_smul (hA k) (γ k ω))) ∂μ := by
  have hmain := gaussian_herm_expectation hmeas hlaw hind (fun k => (hA k).neg)
  have hvar : (∑ k, (-(A k)) ^ 2) = ∑ k, (A k) ^ 2 :=
    Finset.sum_congr rfl fun k _ => neg_sq _
  rw [hvar] at hmain
  have hcongr : (∫ ω, lambdaMin (isHermitian_matsum Finset.univ
      (fun k => isHermitian_real_smul (hA k) (γ k ω))) ∂μ) =
      -∫ ω, lambdaMax (isHermitian_matsum Finset.univ
        (fun k => isHermitian_real_smul ((hA k).neg) (γ k ω))) ∂μ := by
    rw [← MeasureTheory.integral_neg]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω =>
      lambdaMin_series_eq_neg_lambdaMax_neg (ϱ := γ) hA ω)
  rw [hcongr]
  linarith

/-- **Book §4.6.2**, lower-tail display, Gaussian case (C4-13). -/
theorem gaussian_herm_min_tail
    (hmeas : ∀ k, Measurable (γ k)) (hlaw : ∀ k, IsStdGaussian (γ k) μ)
    (hind : ProbabilityTheory.iIndepFun γ μ)
    (hA : ∀ k, (A k).IsHermitian) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | lambdaMin (isHermitian_matsum Finset.univ
        (fun k => isHermitian_real_smul (hA k) (γ k ω))) ≤ -t} ≤
      (Fintype.card n : ℝ) *
        Real.exp (-(t ^ 2) / (2 * ‖∑ k, (A k) ^ 2‖)) := by
  have hmain := gaussian_herm_tail hmeas hlaw hind (fun k => (hA k).neg) ht
  have hvar : (∑ k, (-(A k)) ^ 2) = ∑ k, (A k) ^ 2 :=
    Finset.sum_congr rfl fun k _ => neg_sq _
  rw [hvar] at hmain
  have hevent : {ω | lambdaMin (isHermitian_matsum Finset.univ
      (fun k => isHermitian_real_smul (hA k) (γ k ω))) ≤ -t} =
      {ω | t ≤ lambdaMax (isHermitian_matsum Finset.univ
        (fun k => isHermitian_real_smul ((hA k).neg) (γ k ω)))} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    rw [lambdaMin_series_eq_neg_lambdaMax_neg (ϱ := γ) hA ω]
    constructor <;> intro h <;> linarith
  rw [hevent]
  exact hmain

end GaussianHermitian

section GaussianRectangular

variable {m : Type*} [Fintype m] [DecidableEq m]
variable [IsProbabilityMeasure μ] [Nonempty m] [Nonempty n]
variable {B : ι → Matrix m n ℂ} {γ : ι → Ω → ℝ}

/-- **Book Theorem 4.1.1 (Matrix Gaussian Series)**
(§4.1, p. 42), expectation bound (4.1.5), Gaussian case:
`𝔼‖Σ_k γ_k B_k‖ ≤ √(2 v(Z) log(d₁+d₂))`.
Explicit source declaration; §4.6.5 dilation proof. -/
theorem gaussian_series_rect_expectation
    (hmeas : ∀ k, Measurable (γ k)) (hlaw : ∀ k, IsStdGaussian (γ k) μ)
    (hind : ProbabilityTheory.iIndepFun γ μ) :
    ∫ ω, ‖∑ k, γ k ω • B k‖ ∂μ ≤
      Real.sqrt (2 * max ‖∑ k, B k * (B k)ᴴ‖ ‖∑ k, (B k)ᴴ * B k‖ *
        Real.log (Fintype.card m + Fintype.card n)) := by
  have hmain := gaussian_herm_expectation (μ := μ)
    (A := fun k => hermDilation (B k)) hmeas hlaw hind
    (fun k => isHermitian_hermDilation (B k))
  have hnorm : (∫ ω, ‖∑ k, γ k ω • B k‖ ∂μ) =
      ∫ ω, lambdaMax (isHermitian_matsum Finset.univ
        (fun k => isHermitian_real_smul (isHermitian_hermDilation (B k))
          (γ k ω))) ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    show ‖∑ k, γ k ω • B k‖ = lambdaMax (isHermitian_matsum Finset.univ
      (fun k => isHermitian_real_smul (isHermitian_hermDilation (B k)) (γ k ω)))
    have h1 : (∑ k, γ k ω • hermDilation (B k)) =
        hermDilation (∑ k, γ k ω • B k) :=
      (hermDilation_sum_smul Finset.univ _ _).symm
    have h2 := lambdaMax_congr h1
      (isHermitian_matsum Finset.univ fun k =>
        isHermitian_real_smul (isHermitian_hermDilation (B k)) (γ k ω))
      (isHermitian_hermDilation (∑ k, γ k ω • B k))
    rw [h2, lambdaMax_hermDilation]
  rw [hnorm]
  refine hmain.trans (le_of_eq ?_)
  rw [dilation_coeff_sq_norm]
  congr 2
  rw [Fintype.card_sum]
  push_cast
  ring

/-- **Book Theorem 4.1.1**, tail bound (4.1.6), Gaussian case:
`P(‖Σ_k γ_k B_k‖ ≥ t) ≤ (d₁+d₂)·e^{−t²/(2v)}` for `t ≥ 0`. -/
theorem gaussian_series_rect_tail
    (hmeas : ∀ k, Measurable (γ k)) (hlaw : ∀ k, IsStdGaussian (γ k) μ)
    (hind : ProbabilityTheory.iIndepFun γ μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ ‖∑ k, γ k ω • B k‖} ≤
      ((Fintype.card m : ℝ) + Fintype.card n) *
        Real.exp (-(t ^ 2) /
          (2 * max ‖∑ k, B k * (B k)ᴴ‖ ‖∑ k, (B k)ᴴ * B k‖)) := by
  have hmain := gaussian_herm_tail (μ := μ)
    (A := fun k => hermDilation (B k)) hmeas hlaw hind
    (fun k => isHermitian_hermDilation (B k)) ht
  have hevent : {ω | t ≤ ‖∑ k, γ k ω • B k‖} =
      {ω | t ≤ lambdaMax (isHermitian_matsum Finset.univ
        (fun k => isHermitian_real_smul (isHermitian_hermDilation (B k))
          (γ k ω)))} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    have h1 : (∑ k, γ k ω • hermDilation (B k)) =
        hermDilation (∑ k, γ k ω • B k) :=
      (hermDilation_sum_smul Finset.univ _ _).symm
    have h2 := lambdaMax_congr h1
      (isHermitian_matsum Finset.univ fun k =>
        isHermitian_real_smul (isHermitian_hermDilation (B k)) (γ k ω))
      (isHermitian_hermDilation (∑ k, γ k ω • B k))
    rw [h2, lambdaMax_hermDilation]
  rw [hevent]
  refine hmain.trans (le_of_eq ?_)
  rw [dilation_coeff_sq_norm]
  congr 2
  rw [Fintype.card_sum]
  push_cast
  ring

end GaussianRectangular

end MatrixConcentration


set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# The scalar bound and the second-moment identities (Tropp §4.1)

* `scalar_gauss_series_tail` — **Book eq. (4.1.1)** (C4-01):
  `P(|Σ_k γ_k b_k| ≥ t) ≤ 2·e^{−t²/(2v)}` with `v = Σ_k b_k²`, proved by "a routine
  invocation of the scalar Laplace transform method";
* `scalar_gauss_series_variance` — the annotation `v = Var(Z) = Σ_k b_k²` of (4.1.1);
* `series_second_moment_right`/`series_second_moment_left` — **Book eqs. (4.1.3)/(4.6.2)**
  (C4-03/C4-12): `𝔼(ZZ*) = Σ_k B_kB_k*` and `𝔼(Z*Z) = Σ_k B_k*B_k` for a series with
  independent, centered, unit-second-moment scalar modulators (the cross terms vanish
  by independence and the diagonal terms survive with weight one), with the Gaussian
  and Rademacher instantiations `gaussian_series_second_moment_*`,
  `rademacher_series_second_moment_*`.
-/

namespace MatrixConcentration

open Matrix Finset MeasureTheory
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section ScalarLaplace

variable [IsProbabilityMeasure μ]

/-- Lean implementation helper: the mgf of one Gaussian series term,
`𝔼 e^{θ·γb} = e^{θ²b²/2}`. -/
lemma mgf_isStdGaussian_mul {γ : Ω → ℝ} (hγm : Measurable γ)
    (hγ : IsStdGaussian γ μ) (b θ : ℝ) :
    ProbabilityTheory.mgf (fun ω => γ ω * b) μ θ = Real.exp (θ ^ 2 * b ^ 2 / 2) := by
  have h0 : ProbabilityTheory.mgf (fun ω => γ ω * b) μ θ =
      ∫ ω, Real.exp ((θ * b) * γ ω) ∂μ := by
    rw [ProbabilityTheory.mgf]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by
      show Real.exp (θ * (γ ω * b)) = Real.exp ((θ * b) * γ ω)
      ring_nf)
  rw [h0, integral_exp_mul_isStdGaussian hγm hγ]
  congr 1
  ring

variable {b : ι → ℝ} {γ : ι → Ω → ℝ}

/-- Lean implementation helper: the one-sided scalar Gaussian tail,
`P(Σ_k γ_k b_k ≥ t) ≤ e^{−t²/(2v)}`, by the scalar Laplace transform method
(Chernoff at `θ = t/v`). -/
lemma scalar_gauss_series_tail_upper
    (hmeas : ∀ k, Measurable (γ k)) (hlaw : ∀ k, IsStdGaussian (γ k) μ)
    (hind : ProbabilityTheory.iIndepFun γ μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ ∑ k, γ k ω * b k} ≤
      Real.exp (-(t ^ 2) / (2 * ∑ k, (b k) ^ 2)) := by
  classical
  set v : ℝ := ∑ k, (b k) ^ 2 with hv
  have hvnn : 0 ≤ v := Finset.sum_nonneg fun k _ => sq_nonneg _
  set X : ι → Ω → ℝ := fun k ω => γ k ω * b k with hXdef
  have hXmeas : ∀ k, Measurable (X k) := fun k => (hmeas k).mul_const _
  have hXind : ProbabilityTheory.iIndepFun X μ :=
    hind.comp (fun k s => s * b k) fun k => measurable_id.mul_const _
  have hPle : ∀ S : Set Ω, μ.real S ≤ 1 := fun S => by
    have h := MeasureTheory.measureReal_mono (μ := μ) (Set.subset_univ S)
    rwa [MeasureTheory.probReal_univ] at h
  rcases eq_or_lt_of_le hvnn with hv0 | hvpos
  · rw [← hv0, mul_zero, div_zero, Real.exp_zero]
    exact hPle _
  -- the mgf of the series: `𝔼 e^{θZ} = e^{θ²v/2}`
  have hZfun : (fun ω => ∑ k, γ k ω * b k) = ∑ k, X k := by
    funext ω
    rw [Finset.sum_apply]
  have hterm : ∀ (θ : ℝ) k, Integrable (fun ω => Real.exp (θ * X k ω)) μ := by
    intro θ k
    refine (integrable_exp_mul_isStdGaussian (hmeas k) (hlaw k) (θ * b k)).congr
      (Filter.Eventually.of_forall fun ω => ?_)
    show Real.exp ((θ * b k) * γ k ω) = Real.exp (θ * X k ω)
    show Real.exp ((θ * b k) * γ k ω) = Real.exp (θ * (γ k ω * b k))
    ring_nf
  have hZmgf : ∀ θ : ℝ, ProbabilityTheory.mgf (∑ k, X k) μ θ =
      Real.exp (θ ^ 2 * v / 2) := by
    intro θ
    rw [ProbabilityTheory.iIndepFun.mgf_sum hXind hXmeas Finset.univ]
    rw [Finset.prod_congr rfl fun k _ =>
      mgf_isStdGaussian_mul (hmeas k) (hlaw k) (b k) θ]
    rw [← Real.exp_sum]
    congr 1
    rw [hv, Finset.mul_sum, ← Finset.sum_div]
  -- Chernoff at `θ = t/v`
  set θ : ℝ := t / v with hθdef
  have hθnn : 0 ≤ θ := div_nonneg ht hvnn
  have hZint : Integrable (fun ω => Real.exp (θ * (∑ k, X k) ω)) μ :=
    ProbabilityTheory.iIndepFun.integrable_exp_mul_sum hXind hXmeas
      fun k _ => hterm θ k
  have hch := ProbabilityTheory.measure_ge_le_exp_mul_mgf (μ := μ)
    (X := ∑ k, X k) t hθnn hZint
  have hsetX : {ω | t ≤ ∑ k, γ k ω * b k} = {ω | t ≤ (∑ k, X k) ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Finset.sum_apply]
    exact Iff.rfl
  rw [hsetX]
  refine hch.trans (le_of_eq ?_)
  rw [hZmgf θ, ← Real.exp_add]
  congr 1
  rw [hθdef]
  field_simp
  ring

/-- **Book eq. (4.1.1)** (§4.1, p. 42):
`P(|Z| ≥ t) ≤ 2·exp(−t²/(2v))` for the scalar Gaussian series `Z = Σ_k γ_k b_k`
with `v = Σ_k b_k²`.  Explicit source declaration ("A routine invocation of the
scalar Laplace transform method demonstrates that ..."); the routine invocation is
carried out in full. -/
theorem scalar_gauss_series_tail
    (hmeas : ∀ k, Measurable (γ k)) (hlaw : ∀ k, IsStdGaussian (γ k) μ)
    (hind : ProbabilityTheory.iIndepFun γ μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |∑ k, γ k ω * b k|} ≤
      2 * Real.exp (-(t ^ 2) / (2 * ∑ k, (b k) ^ 2)) := by
  classical
  have hup := scalar_gauss_series_tail_upper (b := b) hmeas hlaw hind ht
  have hdown := scalar_gauss_series_tail_upper (b := fun k => -(b k))
    hmeas hlaw hind ht
  have hvneg : (∑ k, (-(b k)) ^ 2) = ∑ k, (b k) ^ 2 :=
    Finset.sum_congr rfl fun k _ => neg_sq _
  rw [hvneg] at hdown
  have hflip : ∀ ω, (∑ k, γ k ω * (-(b k))) = -(∑ k, γ k ω * b k) := by
    intro ω
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _ => mul_neg _ _
  have hsub : {ω | t ≤ |∑ k, γ k ω * b k|} ⊆
      {ω | t ≤ ∑ k, γ k ω * b k} ∪ {ω | t ≤ ∑ k, γ k ω * (-(b k))} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, Set.mem_union] at hω ⊢
    rcases abs_cases (∑ k, γ k ω * b k) with ⟨heq, _⟩ | ⟨heq, _⟩
    · left
      linarith
    · right
      rw [hflip ω]
      linarith
  calc μ.real {ω | t ≤ |∑ k, γ k ω * b k|}
      ≤ μ.real ({ω | t ≤ ∑ k, γ k ω * b k} ∪
          {ω | t ≤ ∑ k, γ k ω * (-(b k))}) :=
        MeasureTheory.measureReal_mono hsub
  _ ≤ μ.real {ω | t ≤ ∑ k, γ k ω * b k} +
        μ.real {ω | t ≤ ∑ k, γ k ω * (-(b k))} :=
      MeasureTheory.measureReal_union_le _ _
  _ ≤ Real.exp (-(t ^ 2) / (2 * ∑ k, (b k) ^ 2)) +
        Real.exp (-(t ^ 2) / (2 * ∑ k, (b k) ^ 2)) := add_le_add hup hdown
  _ = 2 * Real.exp (-(t ^ 2) / (2 * ∑ k, (b k) ^ 2)) := by ring

end ScalarLaplace

section Moments

variable [IsProbabilityMeasure μ]

/-- Lean implementation helper: a standard Gaussian is centered. -/
lemma integral_isStdGaussian {γ : Ω → ℝ} (hγm : Measurable γ)
    (hγ : IsStdGaussian γ μ) : ∫ ω, γ ω ∂μ = 0 := by
  have h1 : ∫ ω, γ ω ∂μ = ∫ x, x ∂(μ.map γ) :=
    (MeasureTheory.integral_map hγm.aemeasurable aestronglyMeasurable_id).symm
  rw [h1, show μ.map γ = ProbabilityTheory.gaussianReal 0 1 from hγ]
  exact ProbabilityTheory.integral_id_gaussianReal

/-- Lean implementation helper: a standard Gaussian is square-integrable. -/
lemma integrable_sq_isStdGaussian {γ : Ω → ℝ} (hγm : Measurable γ)
    (hγ : IsStdGaussian γ μ) : Integrable (fun ω => γ ω ^ 2) μ := by
  have h0 : MemLp id 2 (μ.map γ) := by
    rw [show μ.map γ = ProbabilityTheory.gaussianReal 0 1 from hγ]
    exact ProbabilityTheory.memLp_id_gaussianReal 2
  have h1 : MemLp γ 2 μ :=
    (memLp_map_measure_iff aestronglyMeasurable_id hγm.aemeasurable).mp h0
  exact h1.integrable_sq

/-- Lean implementation helper: a standard Gaussian has unit second moment. -/
lemma integral_sq_isStdGaussian {γ : Ω → ℝ} (hγm : Measurable γ)
    (hγ : IsStdGaussian γ μ) : ∫ ω, γ ω ^ 2 ∂μ = 1 := by
  have h1 : ∫ ω, γ ω ^ 2 ∂μ = ∫ x, x ^ 2 ∂(μ.map γ) :=
    (MeasureTheory.integral_map hγm.aemeasurable
      (measurable_id.pow_const 2).aestronglyMeasurable).symm
  rw [h1, show μ.map γ = ProbabilityTheory.gaussianReal 0 1 from hγ]
  have hL2 : MemLp (fun x : ℝ => x) 2 (ProbabilityTheory.gaussianReal 0 1) :=
    ProbabilityTheory.memLp_id_gaussianReal 2
  have hvar : ProbabilityTheory.variance (fun x : ℝ => x)
      (ProbabilityTheory.gaussianReal 0 1) = 1 := by
    rw [ProbabilityTheory.variance_fun_id_gaussianReal]
    norm_num
  rw [ProbabilityTheory.variance_eq_sub hL2] at hvar
  simp only [Pi.pow_apply] at hvar
  rw [ProbabilityTheory.integral_id_gaussianReal] at hvar
  linarith

/-- Lean implementation helper: a Rademacher variable is centered. -/
lemma integral_id_isRademacher {ϱ : Ω → ℝ} (hϱm : Measurable ϱ)
    (hϱ : IsRademacher ϱ μ) : ∫ ω, ϱ ω ∂μ = 0 := by
  have h := integral_isRademacher (f := fun x => x) hϱm hϱ measurable_id
  rw [h]
  norm_num

/-- Lean implementation helper: a Rademacher variable has unit second moment. -/
lemma integral_sq_isRademacher {ϱ : Ω → ℝ} (hϱm : Measurable ϱ)
    (hϱ : IsRademacher ϱ μ) : ∫ ω, ϱ ω ^ 2 ∂μ = 1 := by
  have h := integral_isRademacher (f := fun x => x ^ 2) hϱm hϱ (by fun_prop)
  rw [h]
  norm_num

variable {ξ : ι → Ω → ℝ}

/-- Lean implementation helper: products of pairs of square-integrable modulators
are integrable (AM–GM domination `|ξ_pξ_q| ≤ (ξ_p² + ξ_q²)/2`). -/
lemma integrable_pair_mul (hmeas : ∀ k, Measurable (ξ k))
    (hsq : ∀ k, Integrable (fun ω => ξ k ω ^ 2) μ) (p q : ι) :
    Integrable (fun ω => ξ p ω * ξ q ω) μ := by
  have h2 : Integrable (fun ω => (ξ p ω ^ 2 + ξ q ω ^ 2) / 2) μ :=
    ((hsq p).add (hsq q)).div_const 2
  refine Integrable.mono' h2
    ((hmeas p).mul (hmeas q)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  nlinarith [sq_nonneg (|ξ p ω| - |ξ q ω|), sq_abs (ξ p ω), sq_abs (ξ q ω),
    abs_nonneg (ξ p ω), abs_nonneg (ξ q ω)]

/-- Lean implementation helper: Book §§4.1 and 4.6 use independence to eliminate
cross terms—
`𝔼(ξ_pξ_q) = 𝔼ξ_p·𝔼ξ_q = 0` for `p ≠ q`.  Implicit source declaration. -/
lemma integral_cross_term (hmeas : ∀ k, Measurable (ξ k))
    (hind : ProbabilityTheory.iIndepFun ξ μ)
    (hcent : ∀ k, ∫ ω, ξ k ω ∂μ = 0) {p q : ι} (hpq : p ≠ q) :
    ∫ ω, ξ p ω * ξ q ω ∂μ = 0 := by
  have hIndep := hind.indepFun hpq
  have h := hIndep.integral_fun_comp_mul_comp (f := id) (g := id)
    (hmeas p).aemeasurable (hmeas q).aemeasurable
    aestronglyMeasurable_id aestronglyMeasurable_id
  simp only [id] at h
  rw [h, hcent p, zero_mul]

/-- Lean implementation helper: the scalar second-moment identity
`𝔼(Σ_k ξ_k b_k)² = Σ_k b_k²` for independent, centered, unit-second-moment
modulators. -/
lemma scalar_series_second_moment {b : ι → ℝ}
    (hmeas : ∀ k, Measurable (ξ k)) (hind : ProbabilityTheory.iIndepFun ξ μ)
    (hcent : ∀ k, ∫ ω, ξ k ω ∂μ = 0)
    (hsq : ∀ k, Integrable (fun ω => ξ k ω ^ 2) μ)
    (hmom : ∀ k, ∫ ω, ξ k ω ^ 2 ∂μ = 1) :
    ∫ ω, (∑ k, ξ k ω * b k) ^ 2 ∂μ = ∑ k, (b k) ^ 2 := by
  classical
  have hpt : (fun ω => (∑ k, ξ k ω * b k) ^ 2) =
      fun ω => ∑ p, ∑ q, (ξ p ω * ξ q ω) * (b p * b q) := by
    funext ω
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
  rw [hpt]
  rw [MeasureTheory.integral_finset_sum _ fun p _ =>
    integrable_finset_sum _ fun q _ =>
      (integrable_pair_mul hmeas hsq p q).mul_const _]
  have hinner : ∀ p, (∫ ω, ∑ q, (ξ p ω * ξ q ω) * (b p * b q) ∂μ) =
      (b p) ^ 2 := by
    intro p
    rw [MeasureTheory.integral_finset_sum _ fun q _ =>
      (integrable_pair_mul hmeas hsq p q).mul_const _]
    have hterm : ∀ q, (∫ ω, (ξ p ω * ξ q ω) * (b p * b q) ∂μ) =
        (∫ ω, ξ p ω * ξ q ω ∂μ) * (b p * b q) := fun q =>
      MeasureTheory.integral_mul_const _ _
    rw [Finset.sum_congr rfl fun q _ => hterm q]
    rw [Finset.sum_eq_single p]
    · have hdiag : (∫ ω, ξ p ω * ξ p ω ∂μ) = 1 := by
        rw [show (fun ω => ξ p ω * ξ p ω) = fun ω => ξ p ω ^ 2 from
          funext fun ω => (pow_two _).symm]
        exact hmom p
      rw [hdiag, one_mul, sq]
    · intro q _ hqp
      rw [integral_cross_term hmeas hind hcent (Ne.symm hqp), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ p) h
  exact Finset.sum_congr rfl fun p _ => hinner p

/-- **Book eq. (4.1.1)**, the annotation `v = Var(Z) = Σ_k b_k²`: the variance of the
scalar Gaussian series is the sum of the squared coefficients.  Explicit source
declaration. -/
theorem scalar_gauss_series_variance {b : ι → ℝ} {γ : ι → Ω → ℝ}
    (hmeas : ∀ k, Measurable (γ k)) (hlaw : ∀ k, IsStdGaussian (γ k) μ)
    (hind : ProbabilityTheory.iIndepFun γ μ) :
    ProbabilityTheory.variance (fun ω => ∑ k, γ k ω * b k) μ = ∑ k, (b k) ^ 2 := by
  classical
  have hL2 : ∀ k, MemLp (fun ω => γ k ω * b k) 2 μ := by
    intro k
    have h0 : MemLp id 2 (μ.map (γ k)) := by
      rw [show μ.map (γ k) = ProbabilityTheory.gaussianReal 0 1 from hlaw k]
      exact ProbabilityTheory.memLp_id_gaussianReal 2
    have h1 : MemLp (γ k) 2 μ :=
      (memLp_map_measure_iff aestronglyMeasurable_id (hmeas k).aemeasurable).mp h0
    exact h1.mul_const _
  have hZL2 : MemLp (fun ω => ∑ k, γ k ω * b k) 2 μ :=
    memLp_finsetSum Finset.univ fun k _ => hL2 k
  have hmean : (∫ ω, ∑ k, γ k ω * b k ∂μ) = 0 := by
    rw [MeasureTheory.integral_finset_sum _ fun k _ =>
      ((hL2 k).integrable one_le_two)]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [MeasureTheory.integral_mul_const, integral_isStdGaussian (hmeas k) (hlaw k),
      zero_mul]
  have hsecond : (∫ ω, (∑ k, γ k ω * b k) ^ 2 ∂μ) = ∑ k, (b k) ^ 2 :=
    scalar_series_second_moment hmeas hind
      (fun k => integral_isStdGaussian (hmeas k) (hlaw k))
      (fun k => integrable_sq_isStdGaussian (hmeas k) (hlaw k))
      (fun k => integral_sq_isStdGaussian (hmeas k) (hlaw k))
  rw [ProbabilityTheory.variance_eq_sub hZL2]
  show (∫ ω, (∑ k, γ k ω * b k) ^ 2 ∂μ) -
      (∫ ω, ∑ k, γ k ω * b k ∂μ) ^ 2 = ∑ k, (b k) ^ 2
  rw [hsecond, hmean]
  norm_num

end Moments

section MatrixSecondMoment

variable [IsProbabilityMeasure μ]
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
variable {ξ : ι → Ω → ℝ} {B : ι → Matrix m n ℂ}

/-- Lean implementation helper: the pointwise expansion of the series Gram matrix,
`ZZ* = Σ_p Σ_q (ξ_pξ_q)·B_pB_q*`. -/
lemma series_gram_expand (ω : Ω) :
    (∑ k, ξ k ω • B k) * (∑ k, ξ k ω • B k)ᴴ =
      ∑ p, ∑ q, (ξ p ω * ξ q ω) • (B p * (B q)ᴴ) := by
  rw [Matrix.conjTranspose_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Matrix.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul]

/-- **Book eq. (4.1.3)/(4.6.2)** (C4-03/C4-12): the second moment of a matrix
series with independent, centered, unit-second-moment scalar modulators:
`𝔼(ZZ*) = Σ_k B_kB_k*` — "the summands are independent" so the cross terms
vanish, and the diagonal terms survive with unit weight.  Explicit source
declaration (stated in the source for the Gaussian and Rademacher cases; the
common calculation is factored through this abstract form).

**Author note.** Lean proves the identity for arbitrary independent, centered,
unit-second-moment real modulators. -/
theorem series_second_moment_right
    (hmeas : ∀ k, Measurable (ξ k)) (hind : ProbabilityTheory.iIndepFun ξ μ)
    (hcent : ∀ k, ∫ ω, ξ k ω ∂μ = 0)
    (hsq : ∀ k, Integrable (fun ω => ξ k ω ^ 2) μ)
    (hmom : ∀ k, ∫ ω, ξ k ω ^ 2 ∂μ = 1) :
    expectation μ (fun ω => (∑ k, ξ k ω • B k) * (∑ k, ξ k ω • B k)ᴴ) =
      ∑ k, B k * (B k)ᴴ := by
  classical
  ext i j
  rw [expectation_apply, Matrix.sum_apply]
  have hpt : (fun ω => ((∑ k, ξ k ω • B k) * (∑ k, ξ k ω • B k)ᴴ) i j) =
      fun ω => ∑ p, ∑ q, (ξ p ω * ξ q ω) • (B p * (B q)ᴴ) i j := by
    funext ω
    rw [series_gram_expand (ξ := ξ) (B := B) ω]
    simp only [Matrix.sum_apply, Matrix.smul_apply]
  rw [hpt]
  rw [MeasureTheory.integral_finset_sum _ fun p _ =>
    integrable_finset_sum _ fun q _ =>
      (integrable_pair_mul hmeas hsq p q).smul_const _]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [MeasureTheory.integral_finset_sum _ fun q _ =>
    (integrable_pair_mul hmeas hsq p q).smul_const _]
  have hterm : ∀ q, (∫ ω, (ξ p ω * ξ q ω) • (B p * (B q)ᴴ) i j ∂μ) =
      (∫ ω, ξ p ω * ξ q ω ∂μ) • (B p * (B q)ᴴ) i j := fun q =>
    integral_smul_const _ _
  rw [Finset.sum_congr rfl fun q _ => hterm q]
  rw [Finset.sum_eq_single p]
  · have hdiag : (∫ ω, ξ p ω * ξ p ω ∂μ) = 1 := by
      rw [show (fun ω => ξ p ω * ξ p ω) = fun ω => ξ p ω ^ 2 from
        funext fun ω => (pow_two _).symm]
      exact hmom p
    rw [hdiag, one_smul]
  · intro q _ hqp
    rw [integral_cross_term hmeas hind hcent (Ne.symm hqp), zero_smul]
  · intro h
    exact absurd (Finset.mem_univ p) h

/-- **Book equations (4.1.3)–(4.1.4)** (C4-03), the companion identity
`𝔼(Z*Z) = Σ_k B_k*B_k`. Explicit source declaration.

**Author note.** This and `series_second_moment_right` prove the source's Gaussian
and Rademacher identities in the stronger common setting of arbitrary independent,
centered, unit-second-moment real modulators. -/
theorem series_second_moment_left
    (hmeas : ∀ k, Measurable (ξ k)) (hind : ProbabilityTheory.iIndepFun ξ μ)
    (hcent : ∀ k, ∫ ω, ξ k ω ∂μ = 0)
    (hsq : ∀ k, Integrable (fun ω => ξ k ω ^ 2) μ)
    (hmom : ∀ k, ∫ ω, ξ k ω ^ 2 ∂μ = 1) :
    expectation μ (fun ω => (∑ k, ξ k ω • B k)ᴴ * (∑ k, ξ k ω • B k)) =
      ∑ k, (B k)ᴴ * B k := by
  have h := series_second_moment_right (B := fun k => (B k)ᴴ) hmeas hind hcent
    hsq hmom
  have hfun : (fun ω => (∑ k, ξ k ω • (B k)ᴴ) * (∑ k, ξ k ω • (B k)ᴴ)ᴴ) =
      fun ω => (∑ k, ξ k ω • B k)ᴴ * (∑ k, ξ k ω • B k) := by
    funext ω
    have h1 : (∑ k, ξ k ω • B k)ᴴ = ∑ k, ξ k ω • (B k)ᴴ := by
      rw [Matrix.conjTranspose_sum]
      exact Finset.sum_congr rfl fun k _ => by
        rw [Matrix.conjTranspose_smul, star_trivial]
    rw [← h1, Matrix.conjTranspose_conjTranspose]
  rw [hfun] at h
  rw [h]
  exact Finset.sum_congr rfl fun k _ => by
    rw [Matrix.conjTranspose_conjTranspose]

/-- **Book eq. (4.1.3)** (C4-03), Gaussian instantiation:
`𝔼(ZZ*) = Σ_k B_kB_k*` and `𝔼(Z*Z) = Σ_k B_k*B_k` for the matrix Gaussian series.
Explicit source declaration. -/
theorem gaussian_series_second_moment {γ : ι → Ω → ℝ}
    (hmeas : ∀ k, Measurable (γ k)) (hlaw : ∀ k, IsStdGaussian (γ k) μ)
    (hind : ProbabilityTheory.iIndepFun γ μ) :
    expectation μ (fun ω => (∑ k, γ k ω • B k) * (∑ k, γ k ω • B k)ᴴ) =
        (∑ k, B k * (B k)ᴴ) ∧
      expectation μ (fun ω => (∑ k, γ k ω • B k)ᴴ * (∑ k, γ k ω • B k)) =
        ∑ k, (B k)ᴴ * B k :=
  ⟨series_second_moment_right hmeas hind
      (fun k => integral_isStdGaussian (hmeas k) (hlaw k))
      (fun k => integrable_sq_isStdGaussian (hmeas k) (hlaw k))
      (fun k => integral_sq_isStdGaussian (hmeas k) (hlaw k)),
    series_second_moment_left hmeas hind
      (fun k => integral_isStdGaussian (hmeas k) (hlaw k))
      (fun k => integrable_sq_isStdGaussian (hmeas k) (hlaw k))
      (fun k => integral_sq_isStdGaussian (hmeas k) (hlaw k))⟩

/-- **Book Theorem 4.1.1, equations (4.1.3)–(4.1.4), Rademacher instantiation.**
Explicit source declaration. -/
theorem rademacher_series_second_moment {ϱ : ι → Ω → ℝ}
    (hmeas : ∀ k, Measurable (ϱ k)) (hlaw : ∀ k, IsRademacher (ϱ k) μ)
    (hind : ProbabilityTheory.iIndepFun ϱ μ) :
    expectation μ (fun ω => (∑ k, ϱ k ω • B k) * (∑ k, ϱ k ω • B k)ᴴ) =
        (∑ k, B k * (B k)ᴴ) ∧
      expectation μ (fun ω => (∑ k, ϱ k ω • B k)ᴴ * (∑ k, ϱ k ω • B k)) =
        ∑ k, (B k)ᴴ * B k :=
  ⟨series_second_moment_right hmeas hind
      (fun k => integral_id_isRademacher (hmeas k) (hlaw k))
      (fun k => integrable_isRademacher (f := fun x => x ^ 2) (hmeas k) (hlaw k)
        (measurable_id.pow_const 2))
      (fun k => integral_sq_isRademacher (hmeas k) (hlaw k)),
    series_second_moment_left hmeas hind
      (fun k => integral_id_isRademacher (hmeas k) (hlaw k))
      (fun k => integrable_isRademacher (f := fun x => x ^ 2) (hmeas k) (hlaw k)
        (measurable_id.pow_const 2))
      (fun k => integral_sq_isRademacher (hmeas k) (hlaw k))⟩

end MatrixSecondMoment

end MatrixConcentration


set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# Sharpness of the matrix Gaussian series bounds (Tropp §4.1.2)

* `gauss_expect_sq_lower`/`gauss_expect_sq_upper` — **Book eq. (4.1.7)**
  (C4-04):
  `v(Z) ≤ 𝔼‖Z‖² ≤ 2 v(Z) (1 + log(d₁+d₂))`; the lower bound by Jensen's
  inequality and the identity (2.1.28), the upper bound by integration by parts
  (the layer-cake formula), splitting the tail integral at
  `E = √(2 v log(d₁+d₂))`, and the Gaussian tail bound (4.1.6);
* `weakVariance` — the **weak variance** `v⋆(Z)` of §4.1.2 (C4-05), with the
  matrix-alignment identity `gauss_quadform_second_moment`
  (`𝔼|u*Zw|² = Σ_k |u*B_k w|²`);
* `weakVariance_le_variance` and `variance_le_max_dim_mul_weakVariance` — the
  comparison `v⋆(Z) ≤ v(Z) ≤ max{d₁,d₂}·v⋆(Z)`.
  **Author note.** The source states the upper comparison with `min{d₁,d₂}`;
  that inequality is FALSE (counterexample: the `1 × d₂` series `B_k = e_kᵀ`,
  where `v = d₂` but `min{d₁,d₂}·v⋆ = 1`).  The bound proved here replaces
  `min` by `max`, which is the correct general inequality (and is attained by
  the same example);
* `gauss_concentration` — **Book eq. (4.1.8)** (C4-06):
  `P(‖Z‖ ≥ 𝔼‖Z‖ + t) ≤ e^{−t²/(2v⋆(Z))}`.
-/

namespace MatrixConcentration

open Matrix Finset MeasureTheory Set
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

section VectorHelpers

/-- Lean implementation helper: standard basis vectors are ℓ₂-unit. -/
lemma l2norm_single_one (j : n) : l2norm (Pi.single j (1 : ℂ)) = 1 := by
  have h : l2norm (Pi.single j (1 : ℂ)) = ‖EuclideanSpace.single j (1 : ℂ)‖ := rfl
  rw [h, EuclideanSpace.norm_single]
  exact norm_one

/-- Lean implementation helper: `(B e_j)ᵢ = Bᵢⱼ`. -/
lemma mulVec_single_one_apply (B : Matrix m n ℂ) (j : n) (i : m) :
    (B *ᵥ Pi.single j 1) i = B i j := by
  simp [Matrix.mulVec_single]

/-- Lean implementation helper: pairing with a standard basis vector extracts a
coordinate. -/
lemma star_single_dotProduct (x : m → ℂ) (i : m) :
    star (Pi.single i (1 : ℂ)) ⬝ᵥ x = x i := by
  show ∑ l, star ((Pi.single i (1 : ℂ) : m → ℂ) l) * x l = x i
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same, star_one, one_mul]
  · intro l _ hli
    rw [Pi.single_eq_of_ne hli, star_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- Lean implementation helper: the Rayleigh value is additive in the matrix. -/
lemma rayleigh_matsum {d : Type*} [Fintype d] [DecidableEq d]
    (M : ι → Matrix d d ℂ) (w : d → ℂ) :
    rayleigh (∑ k, M k) w = ∑ k, rayleigh (M k) w := by
  rw [show rayleigh (∑ k, M k) w = (star w ⬝ᵥ ((∑ k, M k) *ᵥ w)).re from rfl]
  rw [Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
  rfl

/-- Lean implementation helper: the Rayleigh value of a Gram matrix is a
squared vector norm, `w*(B*B)w = ‖Bw‖²`. -/
lemma rayleigh_conjTranspose_mul_self (B : Matrix m n ℂ) (w : n → ℂ) :
    rayleigh ((B)ᴴ * B) w = l2norm (B *ᵥ w) ^ 2 := by
  rw [show rayleigh ((B)ᴴ * B) w = (star w ⬝ᵥ ((Bᴴ * B) *ᵥ w)).re from rfl]
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec,
    dotProduct_star_self_eq]
  exact Complex.ofReal_re _

/-- Lean implementation helper: the companion identity `u*(BB*)u = ‖B*u‖²`. -/
lemma rayleigh_self_mul_conjTranspose (B : Matrix m n ℂ) (u : m → ℂ) :
    rayleigh (B * (B)ᴴ) u = l2norm ((B)ᴴ *ᵥ u) ^ 2 := by
  have h := rayleigh_conjTranspose_mul_self (B := Bᴴ) u
  rwa [Matrix.conjTranspose_conjTranspose] at h

/-- Lean implementation helper: the entries of `B*u` are the pairings `u*(B e_j)`
up to conjugation, so their norms agree. -/
lemma norm_conjTranspose_mulVec_entry (B : Matrix m n ℂ) (u : m → ℂ) (j : n) :
    ‖((B)ᴴ *ᵥ u) j‖ = ‖star u ⬝ᵥ (B *ᵥ Pi.single j 1)‖ := by
  have h1 : ((B)ᴴ *ᵥ u) j = star (star u ⬝ᵥ (B *ᵥ Pi.single j 1)) := by
    show ∑ i, Bᴴ j i * u i = star (∑ i, star u i * (B *ᵥ Pi.single j 1) i)
    rw [star_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mulVec_single_one_apply, Pi.star_apply, star_mul', star_star,
      Matrix.conjTranspose_apply]
    exact mul_comm _ _
  rw [h1, norm_star]

end VectorHelpers

section WeakVariance

variable [Nonempty m] [Nonempty n]

/-- Lean implementation helper: the defining set used to encode the weak variance
from Book §4.1.2—the achievable values of `Σ_k |u*B_k w|²` over unit vectors
`u, w`. -/
def weakVarianceSet (B : ι → Matrix m n ℂ) : Set ℝ :=
  {r | ∃ (u : m → ℂ) (w : n → ℂ), l2norm u = 1 ∧ l2norm w = 1 ∧
    r = ∑ k, ‖star u ⬝ᵥ (B k *ᵥ w)‖ ^ 2}

/-- **Book §4.1.2 (C4-05)**: the **weak variance**
`v⋆(Z) = sup_{‖u‖=‖w‖=1} Σ_k |u*B_k w|²` of the matrix Gaussian series with
coefficients `B_k`.  Explicit source declaration (the second formula of the
display; the first, `sup 𝔼|u*Zw|²`, is recovered by
`gauss_quadform_second_moment`). -/
noncomputable def weakVariance (B : ι → Matrix m n ℂ) : ℝ :=
  sSup (weakVarianceSet B)

variable {B : ι → Matrix m n ℂ}

/-- Lean implementation helper: the weak-variance defining set is nonempty. -/
lemma weakVarianceSet_nonempty (B : ι → Matrix m n ℂ) :
    (weakVarianceSet B).Nonempty :=
  ⟨_, Pi.single (Classical.arbitrary m) 1, Pi.single (Classical.arbitrary n) 1,
    l2norm_single_one _, l2norm_single_one _, rfl⟩

/-- Lean implementation helper: Cauchy–Schwarz termwise, then the Gram identity —
for a unit vector `u`, `Σ_k |u*B_k w|² ≤ w*(Σ_k B_k*B_k)w`. -/
lemma sum_normsq_le_rayleigh {u : m → ℂ} (hu : l2norm u = 1) (w : n → ℂ) :
    ∑ k, ‖star u ⬝ᵥ (B k *ᵥ w)‖ ^ 2 ≤ rayleigh (∑ k, (B k)ᴴ * B k) w := by
  rw [rayleigh_matsum]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [rayleigh_conjTranspose_mul_self]
  have h1 := norm_dotProduct_le u (B k *ᵥ w)
  rw [hu, one_mul] at h1
  have h2 : (0 : ℝ) ≤ ‖star u ⬝ᵥ (B k *ᵥ w)‖ := norm_nonneg _
  nlinarith [l2norm_nonneg (B k *ᵥ w)]

/-- Lean implementation helper: every achievable weak-variance value is at most the
matrix variance statistic. -/
lemma weakVarianceSet_le {r : ℝ} (hr : r ∈ weakVarianceSet B) :
    r ≤ max ‖∑ k, B k * (B k)ᴴ‖ ‖∑ k, (B k)ᴴ * B k‖ := by
  obtain ⟨u, w, hu, hw, rfl⟩ := hr
  have hpsd : (∑ k, (B k)ᴴ * B k).PosSemidef :=
    posSemidef_matsum Finset.univ fun k =>
      Matrix.posSemidef_conjTranspose_mul_self _
  calc ∑ k, ‖star u ⬝ᵥ (B k *ᵥ w)‖ ^ 2
      ≤ rayleigh (∑ k, (B k)ᴴ * B k) w := sum_normsq_le_rayleigh hu w
  _ ≤ lambdaMax hpsd.1 := rayleigh_le_lambdaMax_of_unit hpsd.1 hw
  _ ≤ ‖∑ k, (B k)ᴴ * B k‖ := (le_abs_self _).trans (abs_lambdaMax_le hpsd.1)
  _ ≤ max ‖∑ k, B k * (B k)ᴴ‖ ‖∑ k, (B k)ᴴ * B k‖ := le_max_right _ _

/-- Lean implementation helper: the weak-variance defining set is bounded above. -/
lemma weakVarianceSet_bddAbove (B : ι → Matrix m n ℂ) :
    BddAbove (weakVarianceSet B) :=
  ⟨max ‖∑ k, B k * (B k)ᴴ‖ ‖∑ k, (B k)ᴴ * B k‖, fun _ hr => weakVarianceSet_le hr⟩

/-- Lean implementation helper: weak variance is nonnegative. -/
lemma weakVariance_nonneg (B : ι → Matrix m n ℂ) : 0 ≤ weakVariance B := by
  obtain ⟨r, hr⟩ := weakVarianceSet_nonempty B
  have h0 : 0 ≤ r := by
    obtain ⟨u, w, _, _, rfl⟩ := hr
    positivity
  exact h0.trans (le_csSup (weakVarianceSet_bddAbove B) hr)

/-- **Book §4.1.2 (C4-05)**, the lower comparison `v⋆(Z) ≤ v(Z)`.  Explicit source
declaration ("The best general inequalities between the matrix variance statistic
and the weak variance are ..."). -/
theorem weakVariance_le_variance (B : ι → Matrix m n ℂ) :
    weakVariance B ≤ max ‖∑ k, B k * (B k)ᴴ‖ ‖∑ k, (B k)ᴴ * B k‖ :=
  csSup_le (weakVarianceSet_nonempty B) fun _ hr => weakVarianceSet_le hr

/-- **Book §4.1.2 (C4-05), upper comparison** —
`v(Z) ≤ max{d₁,d₂}·v⋆(Z)`.

**Author note.** The source claims this inequality with `min{d₁, d₂}` in place of
`max{d₁, d₂}`.  The `min` version is FALSE: for the `1 × d₂` series with
coefficients the standard basis row vectors, `v(Z) = d₂` while
`min{d₁,d₂}·v⋆(Z) = 1·1 = 1`.  The proof below (expand the extremal Rayleigh
vector of each Gram matrix against the standard basis of the opposite side)
establishes the `max` version, which the same example shows is sharp. -/
theorem variance_le_max_dim_mul_weakVariance (B : ι → Matrix m n ℂ) :
    max ‖∑ k, B k * (B k)ᴴ‖ ‖∑ k, (B k)ᴴ * B k‖ ≤
      max (Fintype.card m : ℝ) (Fintype.card n) * weakVariance B := by
  refine max_le ?_ ?_
  · -- ‖Σ B_k B_k*‖ ≤ d₂ · v⋆ ≤ max{d₁,d₂} · v⋆
    have hpsd : (∑ k, B k * (B k)ᴴ).PosSemidef :=
      posSemidef_matsum Finset.univ fun k =>
        Matrix.posSemidef_self_mul_conjTranspose _
    obtain ⟨u, hu, hval⟩ := exists_unit_rayleigh_eq_lambdaMax hpsd.1
    calc ‖∑ k, B k * (B k)ᴴ‖ = lambdaMax hpsd.1 :=
          posSemidef_l2_opNorm_eq_lambdaMax hpsd
    _ = rayleigh (∑ k, B k * (B k)ᴴ) u := hval.symm
    _ = ∑ k, rayleigh (B k * (B k)ᴴ) u := rayleigh_matsum _ u
    _ = ∑ k, ∑ j : n, ‖((B k)ᴴ *ᵥ u) j‖ ^ 2 := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [rayleigh_self_mul_conjTranspose, l2norm_sq]
    _ = ∑ j : n, ∑ k, ‖((B k)ᴴ *ᵥ u) j‖ ^ 2 := Finset.sum_comm
    _ = ∑ j : n, ∑ k, ‖star u ⬝ᵥ (B k *ᵥ Pi.single j 1)‖ ^ 2 := by
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
        rw [norm_conjTranspose_mulVec_entry]
    _ ≤ ∑ _j : n, weakVariance B :=
        Finset.sum_le_sum fun j _ => le_csSup (weakVarianceSet_bddAbove B)
          ⟨u, Pi.single j 1, hu, l2norm_single_one j, rfl⟩
    _ = (Fintype.card n : ℝ) * weakVariance B := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ max (Fintype.card m : ℝ) (Fintype.card n) * weakVariance B :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (weakVariance_nonneg B)
  · -- ‖Σ B_k* B_k‖ ≤ d₁ · v⋆ ≤ max{d₁,d₂} · v⋆
    have hpsd : (∑ k, (B k)ᴴ * B k).PosSemidef :=
      posSemidef_matsum Finset.univ fun k =>
        Matrix.posSemidef_conjTranspose_mul_self _
    obtain ⟨w, hw, hval⟩ := exists_unit_rayleigh_eq_lambdaMax hpsd.1
    calc ‖∑ k, (B k)ᴴ * B k‖ = lambdaMax hpsd.1 :=
          posSemidef_l2_opNorm_eq_lambdaMax hpsd
    _ = rayleigh (∑ k, (B k)ᴴ * B k) w := hval.symm
    _ = ∑ k, rayleigh ((B k)ᴴ * B k) w := rayleigh_matsum _ w
    _ = ∑ k, ∑ i : m, ‖(B k *ᵥ w) i‖ ^ 2 := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [rayleigh_conjTranspose_mul_self, l2norm_sq]
    _ = ∑ i : m, ∑ k, ‖(B k *ᵥ w) i‖ ^ 2 := Finset.sum_comm
    _ = ∑ i : m, ∑ k, ‖star (Pi.single i (1:ℂ)) ⬝ᵥ (B k *ᵥ w)‖ ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
        rw [star_single_dotProduct]
    _ ≤ ∑ _i : m, weakVariance B :=
        Finset.sum_le_sum fun i _ => le_csSup (weakVarianceSet_bddAbove B)
          ⟨Pi.single i 1, w, l2norm_single_one i, hw, rfl⟩
    _ = (Fintype.card m : ℝ) * weakVariance B := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ max (Fintype.card m : ℝ) (Fintype.card n) * weakVariance B :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (weakVariance_nonneg B)

end WeakVariance

section QuadformMoment

variable [IsProbabilityMeasure μ]

/-- Lean implementation helper: the complex-coefficient second-moment identity,
`𝔼|Σ_k ξ_k c_k|² = Σ_k |c_k|²` for independent, centered, unit-second-moment real
modulators. -/
lemma scalar_series_second_moment_complex {ξ : ι → Ω → ℝ} {c : ι → ℂ}
    (hmeas : ∀ k, Measurable (ξ k)) (hind : ProbabilityTheory.iIndepFun ξ μ)
    (hcent : ∀ k, ∫ ω, ξ k ω ∂μ = 0)
    (hsq : ∀ k, Integrable (fun ω => ξ k ω ^ 2) μ)
    (hmom : ∀ k, ∫ ω, ξ k ω ^ 2 ∂μ = 1) :
    ∫ ω, ‖∑ k, ξ k ω • c k‖ ^ 2 ∂μ = ∑ k, ‖c k‖ ^ 2 := by
  classical
  have hnormsq : ∀ z : ℂ, ‖z‖ ^ 2 = (z * star z).re := fun z => by
    rw [show star z = (starRingEnd ℂ) z from rfl, RCLike.mul_conj z]
    norm_cast
  have hpt : (fun ω => ‖∑ k, ξ k ω • c k‖ ^ 2) =
      fun ω => ∑ p, ∑ q, (ξ p ω * ξ q ω) * (c p * star (c q)).re := by
    funext ω
    rw [hnormsq]
    have h2 : (∑ k, ξ k ω • c k) * star (∑ k, ξ k ω • c k) =
        ∑ p, ∑ q, (ξ p ω * ξ q ω) • (c p * star (c q)) := by
      rw [star_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
      rw [star_smul, star_trivial, smul_mul_smul_comm]
    rw [h2, Complex.re_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Complex.real_smul, Complex.re_ofReal_mul]
  rw [hpt]
  rw [MeasureTheory.integral_finset_sum _ fun p _ =>
    integrable_finset_sum _ fun q _ =>
      (integrable_pair_mul hmeas hsq p q).mul_const _]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [MeasureTheory.integral_finset_sum _ fun q _ =>
    (integrable_pair_mul hmeas hsq p q).mul_const _]
  rw [Finset.sum_congr rfl fun q _ =>
    MeasureTheory.integral_mul_const ((c p * star (c q)).re) _]
  rw [Finset.sum_eq_single p]
  · rw [show (fun ω => ξ p ω * ξ p ω) = fun ω => ξ p ω ^ 2 from
      funext fun ω => (pow_two _).symm, hmom p, one_mul]
    exact (hnormsq (c p)).symm
  · intro q _ hqp
    rw [integral_cross_term hmeas hind hcent (Ne.symm hqp), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ p) h

/-- **Book §4.1.2 (C4-05)**, the first formula for the weak variance:
`𝔼|u*Zw|² = Σ_k |u*B_k w|²` for every pair of vectors.  Explicit source
declaration (the display defining `v⋆(Z)`).

**Author note.** The source immediately restricts to unit vectors when taking the
supremum; Lean records the identity for arbitrary `u` and `w`. -/
theorem gauss_quadform_second_moment {γ : ι → Ω → ℝ} {B : ι → Matrix m n ℂ}
    (hmeas : ∀ k, Measurable (γ k)) (hlaw : ∀ k, IsStdGaussian (γ k) μ)
    (hind : ProbabilityTheory.iIndepFun γ μ) (u : m → ℂ) (w : n → ℂ) :
    ∫ ω, ‖star u ⬝ᵥ ((∑ k, γ k ω • B k) *ᵥ w)‖ ^ 2 ∂μ =
      ∑ k, ‖star u ⬝ᵥ (B k *ᵥ w)‖ ^ 2 := by
  have hcongr : (fun ω => ‖star u ⬝ᵥ ((∑ k, γ k ω • B k) *ᵥ w)‖ ^ 2) =
      fun ω => ‖∑ k, γ k ω • (star u ⬝ᵥ (B k *ᵥ w))‖ ^ 2 := by
    funext ω
    congr 1
    rw [Matrix.sum_mulVec, dotProduct_sum]
    refine congrArg _ (Finset.sum_congr rfl fun k _ => ?_)
    rw [Matrix.smul_mulVec, dotProduct_smul]
  rw [hcongr]
  exact scalar_series_second_moment_complex hmeas hind
    (fun k => integral_isStdGaussian (hmeas k) (hlaw k))
    (fun k => integrable_sq_isStdGaussian (hmeas k) (hlaw k))
    (fun k => integral_sq_isStdGaussian (hmeas k) (hlaw k))

end QuadformMoment

section TwoSided

variable [IsProbabilityMeasure μ]
variable {γ : ι → Ω → ℝ} {B : ι → Matrix m n ℂ}

/-- Lean implementation helper: the squared norm of the Gaussian series is
integrable (`x² ≤ 2eˣ` and the exponential-moment package for the dilated
series). -/
lemma integrable_norm_sq_gauss_series [Nonempty m] [Nonempty n]
    (hmeas : ∀ k, Measurable (γ k)) (hlaw : ∀ k, IsStdGaussian (γ k) μ)
    (hind : ProbabilityTheory.iIndepFun γ μ) :
    Integrable (fun ω => ‖∑ k, γ k ω • B k‖ ^ 2) μ := by
  classical
  set X : ι → Ω → Matrix (m ⊕ n) (m ⊕ n) ℂ :=
    fun k ω => γ k ω • hermDilation (B k) with hXdef
  have hXmeas : ∀ k, Measurable (X k) := fun k => by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    show Measurable fun ω => γ k ω • hermDilation (B k) i j
    exact (hmeas k).smul_const _
  have hXexpc : ∀ k c, Integrable (fun ω => Real.exp (c * ‖X k ω‖)) μ :=
    fun k c => gaussian_family_expc (A := fun k => hermDilation (B k))
      hmeas hlaw k c
  have hXind : ProbabilityTheory.iIndepFun X μ := by
    refine hind.comp (fun k s => s • hermDilation (B k)) fun k => ?_
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    show Measurable fun s : ℝ => s • hermDilation (B k) i j
    exact measurable_id.smul_const _
  have hexp : Integrable
      (fun ω => Real.exp (1 * ‖∑ k, X k ω‖)) μ :=
    integrable_exp_norm_sum hXmeas hXexpc hXind zero_le_one
  have hZmeas : Measurable fun ω => ∑ k, γ k ω • B k := by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    show Measurable fun ω => (∑ k, γ k ω • B k) i j
    have : ∀ ω, (∑ k, γ k ω • B k) i j = ∑ k, γ k ω • B k i j := fun ω => by
      simp [Matrix.sum_apply]
    simp only [this]
    exact Finset.measurable_sum _ fun k _ => (hmeas k).smul_const _
  refine Integrable.mono' (hexp.const_mul 2)
    (((continuous_l2_opNorm.measurable.comp hZmeas).pow_const 2).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hnn : (0 : ℝ) ≤ ‖∑ k, γ k ω • B k‖ := norm_nonneg _
  have hq := Real.quadratic_le_exp_of_nonneg hnn
  have hZH : ‖∑ k, γ k ω • B k‖ ≤ ‖∑ k, X k ω‖ := by
    have h1 : (∑ k, X k ω) = hermDilation (∑ k, γ k ω • B k) := by
      rw [hermDilation_sum_smul]
    have h2 : ‖∑ k, γ k ω • B k‖ =
        lambdaMax (isHermitian_hermDilation (∑ k, γ k ω • B k)) :=
      (lambdaMax_hermDilation _).symm
    rw [h2]
    calc lambdaMax (isHermitian_hermDilation (∑ k, γ k ω • B k))
        ≤ |lambdaMax (isHermitian_hermDilation (∑ k, γ k ω • B k))| :=
          le_abs_self _
    _ ≤ ‖hermDilation (∑ k, γ k ω • B k)‖ :=
        abs_lambdaMax_le (isHermitian_hermDilation _)
    _ = ‖∑ k, X k ω‖ := by rw [h1]
  calc ‖∑ k, γ k ω • B k‖ ^ 2
      ≤ 2 * Real.exp ‖∑ k, γ k ω • B k‖ := by nlinarith [Real.exp_pos ‖∑ k, γ k ω • B k‖]
  _ ≤ 2 * Real.exp (1 * ‖∑ k, X k ω‖) := by
      rw [one_mul]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hZH) (by norm_num)

/-- **Book eq. (4.1.7)** (§4.1.2), lower half:
`v(Z) ≤ 𝔼‖Z‖²` — "since the spectral norm is convex, Jensen's inequality ensures
that ...", combined with the identity (2.1.28) `‖Z‖² = max{‖ZZ*‖, ‖Z*Z‖}` and the
second-moment identity (4.1.3). Explicit source declaration. -/
theorem gauss_expect_sq_lower [Nonempty m] [Nonempty n]
    (hmeas : ∀ k, Measurable (γ k)) (hlaw : ∀ k, IsStdGaussian (γ k) μ)
    (hind : ProbabilityTheory.iIndepFun γ μ) :
    max ‖∑ k, B k * (B k)ᴴ‖ ‖∑ k, (B k)ᴴ * B k‖ ≤
      ∫ ω, ‖∑ k, γ k ω • B k‖ ^ 2 ∂μ := by
  classical
  have hsq : ∀ k, Integrable (fun ω => γ k ω ^ 2) μ := fun k =>
    integrable_sq_isStdGaussian (hmeas k) (hlaw k)
  have hZnormint : Integrable (fun ω => ‖∑ k, γ k ω • B k‖ ^ 2) μ :=
    integrable_norm_sq_gauss_series hmeas hlaw hind
  have h2mom := gaussian_series_second_moment (B := B) hmeas hlaw hind
  refine max_le ?_ ?_
  · -- right Gram factor
    have hWint : MIntegrable
        (fun ω => (∑ k, γ k ω • B k) * (∑ k, γ k ω • B k)ᴴ) μ := by
      intro i j
      have hpt : (fun ω => ((∑ k, γ k ω • B k) * (∑ k, γ k ω • B k)ᴴ) i j) =
          fun ω => ∑ p, ∑ q, (γ p ω * γ q ω) • (B p * (B q)ᴴ) i j := by
        funext ω
        rw [series_gram_expand (ξ := γ) (B := B) ω]
        simp only [Matrix.sum_apply, Matrix.smul_apply]
      rw [hpt]
      exact integrable_finset_sum _ fun p _ => integrable_finset_sum _ fun q _ =>
        (integrable_pair_mul hmeas hsq p q).smul_const _
    have hWnorm : Integrable
        (fun ω => ‖(∑ k, γ k ω • B k) * (∑ k, γ k ω • B k)ᴴ‖) μ := by
      refine hZnormint.congr (Filter.Eventually.of_forall fun ω => ?_)
      exact (l2_opNorm_sq_eq (∑ k, γ k ω • B k)).1
    calc ‖∑ k, B k * (B k)ᴴ‖
        = ‖expectation μ (fun ω => (∑ k, γ k ω • B k) * (∑ k, γ k ω • B k)ᴴ)‖ := by
          rw [h2mom.1]
    _ ≤ ∫ ω, ‖(∑ k, γ k ω • B k) * (∑ k, γ k ω • B k)ᴴ‖ ∂μ :=
        norm_expectation_le hWint hWnorm
    _ = ∫ ω, ‖∑ k, γ k ω • B k‖ ^ 2 ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall fun ω =>
          ((l2_opNorm_sq_eq (∑ k, γ k ω • B k)).1).symm)
  · -- left Gram factor
    have hWint : MIntegrable
        (fun ω => (∑ k, γ k ω • B k)ᴴ * (∑ k, γ k ω • B k)) μ := by
      intro i j
      have hpt : (fun ω => ((∑ k, γ k ω • B k)ᴴ * (∑ k, γ k ω • B k)) i j) =
          fun ω => ∑ p, ∑ q, (γ p ω * γ q ω) • ((B p)ᴴ * B q) i j := by
        funext ω
        have h1 : (∑ k, γ k ω • B k)ᴴ * (∑ k, γ k ω • B k) =
            ∑ p, ∑ q, (γ p ω * γ q ω) • ((B p)ᴴ * B q) := by
          have h2 : (∑ k, γ k ω • B k)ᴴ = ∑ k, γ k ω • (B k)ᴴ := by
            rw [Matrix.conjTranspose_sum]
            exact Finset.sum_congr rfl fun k _ => by
              rw [Matrix.conjTranspose_smul, star_trivial]
          rw [h2, Matrix.sum_mul]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [Matrix.mul_sum]
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
        rw [h1]
        simp only [Matrix.sum_apply, Matrix.smul_apply]
      rw [hpt]
      exact integrable_finset_sum _ fun p _ => integrable_finset_sum _ fun q _ =>
        (integrable_pair_mul hmeas hsq p q).smul_const _
    have hWnorm : Integrable
        (fun ω => ‖(∑ k, γ k ω • B k)ᴴ * (∑ k, γ k ω • B k)‖) μ := by
      refine hZnormint.congr (Filter.Eventually.of_forall fun ω => ?_)
      exact (l2_opNorm_sq_eq (∑ k, γ k ω • B k)).2
    calc ‖∑ k, (B k)ᴴ * B k‖
        = ‖expectation μ (fun ω => (∑ k, γ k ω • B k)ᴴ * (∑ k, γ k ω • B k))‖ := by
          rw [h2mom.2]
    _ ≤ ∫ ω, ‖(∑ k, γ k ω • B k)ᴴ * (∑ k, γ k ω • B k)‖ ∂μ :=
        norm_expectation_le hWint hWnorm
    _ = ∫ ω, ‖∑ k, γ k ω • B k‖ ^ 2 ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall fun ω =>
          ((l2_opNorm_sq_eq (∑ k, γ k ω • B k)).2).symm)

/-- Lean implementation helper: `v(Z) = 0` forces all coefficients to vanish
(the Gram summands are PSD, a PSD sum is zero only if each summand is, and
`B B* = 0 → B = 0`). -/
lemma coeffs_eq_zero_of_variance_eq_zero
    (hv : max ‖∑ k, B k * (B k)ᴴ‖ ‖∑ k, (B k)ᴴ * B k‖ = 0) (k : ι) : B k = 0 := by
  classical
  have h1 : ‖∑ j, B j * (B j)ᴴ‖ = 0 :=
    le_antisymm (le_max_left _ _ |>.trans hv.le) (norm_nonneg _)
  have hsum0 : (∑ j, B j * (B j)ᴴ) = 0 := norm_eq_zero.mp h1
  have hle : B k * (B k)ᴴ ≤ ∑ j, B j * (B j)ᴴ := by
    rw [Matrix.le_iff]
    have h2 : (∑ j, B j * (B j)ᴴ) - B k * (B k)ᴴ =
        ∑ j ∈ Finset.univ.erase k, B j * (B j)ᴴ := by
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ k)]
    rw [h2]
    exact posSemidef_matsum _ fun j => Matrix.posSemidef_self_mul_conjTranspose _
  have hge : (0 : Matrix m m ℂ) ≤ B k * (B k)ᴴ := by
    rw [Matrix.le_iff, sub_zero]
    exact Matrix.posSemidef_self_mul_conjTranspose _
  have h0 : B k * (B k)ᴴ = 0 := le_antisymm (hsum0 ▸ hle) hge
  exact Matrix.self_mul_conjTranspose_eq_zero.mp h0

/-- **Book eq. (4.1.7)** (§4.1.2), upper half:
`𝔼‖Z‖² ≤ 2 v(Z) (1 + log(d₁+d₂))` — "rewrite the expectation using integration by
parts, and then split the integral at a positive number `E` ... Finally, select
`E² = 2v(Z)log(d₁+d₂)`". Explicit source declaration; faithful translation of the
layer-cake proof.

**Author note.** The proof treats the degenerate case `v(Z)=0` explicitly. -/
theorem gauss_expect_sq_upper [Nonempty m] [Nonempty n]
    (hmeas : ∀ k, Measurable (γ k)) (hlaw : ∀ k, IsStdGaussian (γ k) μ)
    (hind : ProbabilityTheory.iIndepFun γ μ) :
    ∫ ω, ‖∑ k, γ k ω • B k‖ ^ 2 ∂μ ≤
      2 * max ‖∑ k, B k * (B k)ᴴ‖ ‖∑ k, (B k)ᴴ * B k‖ *
        (1 + Real.log ((Fintype.card m : ℝ) + Fintype.card n)) := by
  classical
  set v : ℝ := max ‖∑ k, B k * (B k)ᴴ‖ ‖∑ k, (B k)ᴴ * B k‖ with hvdef
  set D : ℝ := (Fintype.card m : ℝ) + Fintype.card n with hDdef
  have hD1 : (1 : ℝ) ≤ D := by
    rw [hDdef]
    have h1 : (1 : ℝ) ≤ (Fintype.card m : ℝ) := by exact_mod_cast Fintype.card_pos
    have h2 : (0 : ℝ) ≤ (Fintype.card n : ℝ) := by positivity
    linarith
  have hDpos : (0 : ℝ) < D := lt_of_lt_of_le one_pos hD1
  have hlogD : (0 : ℝ) ≤ Real.log D := Real.log_nonneg hD1
  have hvnn : 0 ≤ v := (norm_nonneg _).trans (le_max_left _ _)
  rcases eq_or_lt_of_le hvnn with hv0 | hvpos
  · -- degenerate case: all coefficients vanish
    have hB0 : ∀ k, B k = 0 := coeffs_eq_zero_of_variance_eq_zero hv0.symm
    have hint0 : (fun ω => ‖∑ k, γ k ω • B k‖ ^ 2) = fun _ => (0 : ℝ) := by
      funext ω
      have h1 : (∑ k, γ k ω • B k) = 0 := by
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [hB0 k, smul_zero]
      rw [h1]
      simp
    rw [hint0, MeasureTheory.integral_zero, ← hv0]
    positivity
  -- main case `v > 0`
  set E : ℝ := Real.sqrt (2 * v * Real.log D) with hEdef
  have hEnn : 0 ≤ E := Real.sqrt_nonneg _
  have hE2 : E ^ 2 = 2 * v * Real.log D := Real.sq_sqrt (by positivity)
  have hZmeas : Measurable fun ω => ∑ k, γ k ω • B k := by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    show Measurable fun ω => (∑ k, γ k ω • B k) i j
    have : ∀ ω, (∑ k, γ k ω • B k) i j = ∑ k, γ k ω • B k i j := fun ω => by
      simp [Matrix.sum_apply]
    simp only [this]
    exact Finset.measurable_sum _ fun k _ => (hmeas k).smul_const _
  have hnormmeas : Measurable fun ω => ‖∑ k, γ k ω • B k‖ :=
    continuous_l2_opNorm.measurable.comp hZmeas
  -- the layer-cake identity with weight `2t`
  have hlc := lintegral_comp_eq_lintegral_meas_le_mul μ
    (f := fun ω => ‖∑ k, γ k ω • B k‖) (g := fun t => 2 * t)
    (Filter.Eventually.of_forall fun ω => norm_nonneg _)
    hnormmeas.aemeasurable
    (fun t _ => (continuous_const.mul continuous_id).intervalIntegrable 0 t)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
      have : (0:ℝ) < t := ht
      positivity)
  have hsqint : ∀ x : ℝ, (∫ t in (0:ℝ)..x, 2 * t) = x ^ 2 := by
    intro x
    rw [intervalIntegral.integral_const_mul, integral_id]
    ring
  have hLHSlc : ∫⁻ ω, ENNReal.ofReal (‖∑ k, γ k ω • B k‖ ^ 2) ∂μ =
      ∫⁻ t in Set.Ioi (0:ℝ),
        μ {a | t ≤ ‖∑ k, γ k a • B k‖} * ENNReal.ofReal (2 * t) := by
    rw [← hlc]
    refine lintegral_congr fun ω => ?_
    rw [hsqint]
  -- the FTC computation of the Gaussian tail integral
  have hderiv : ∀ t ∈ Set.Ioi E,
      HasDerivAt (fun t => -(2 * v * D * Real.exp (-(t ^ 2) / (2 * v))))
        (D * Real.exp (-(t ^ 2) / (2 * v)) * (2 * t)) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => t ^ 2) (2 * t) t := by
      simpa using hasDerivAt_pow 2 t
    have h2 : HasDerivAt (fun t : ℝ => -(t ^ 2) / (2 * v)) (-(t / v)) t := by
      have h2' := h1.neg.div_const (2 * v)
      have heq : -(2 * t) / (2 * v) = -(t / v) := by
        rw [neg_div, mul_div_mul_left t v two_ne_zero]
      rwa [heq] at h2'
    have h4 := ((h2.exp).const_mul (2 * v * D)).neg
    have hvne : v ≠ 0 := ne_of_gt hvpos
    have heq2 : -(2 * v * D * (Real.exp (-(t ^ 2) / (2 * v)) * -(t / v))) =
        D * Real.exp (-(t ^ 2) / (2 * v)) * (2 * t) := by
      field_simp
    rwa [heq2] at h4
  have hgpos : ∀ t ∈ Set.Ioi E, 0 ≤ D * Real.exp (-(t ^ 2) / (2 * v)) * (2 * t) := by
    intro t ht
    have ht0 : 0 ≤ t := hEnn.trans (le_of_lt ht)
    positivity
  have hcont : ContinuousWithinAt
      (fun t => -(2 * v * D * Real.exp (-(t ^ 2) / (2 * v)))) (Set.Ici E) E := by
    refine Continuous.continuousWithinAt ?_
    fun_prop
  have htends : Filter.Tendsto (fun t => -(2 * v * D * Real.exp (-(t ^ 2) / (2 * v))))
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun t : ℝ => -(t ^ 2) / (2 * v)) Filter.atTop
        Filter.atBot := by
      apply Filter.Tendsto.atBot_div_const (by positivity)
      exact Filter.tendsto_neg_atBot_iff.mpr (Filter.tendsto_pow_atTop two_ne_zero)
    have h2 : Filter.Tendsto (fun t : ℝ => Real.exp (-(t ^ 2) / (2 * v)))
        Filter.atTop (nhds 0) := Real.tendsto_exp_atBot.comp h1
    have h3 := (h2.const_mul (2 * v * D)).neg
    simpa using h3
  have hFTCint : IntegrableOn
      (fun t => D * Real.exp (-(t ^ 2) / (2 * v)) * (2 * t)) (Set.Ioi E) :=
    integrableOn_Ioi_deriv_of_nonneg hcont hderiv hgpos htends
  have hFTCval : ∫ t in Set.Ioi E, D * Real.exp (-(t ^ 2) / (2 * v)) * (2 * t) =
      2 * v * D * Real.exp (-(E ^ 2) / (2 * v)) := by
    rw [integral_Ioi_of_hasDerivAt_of_nonneg hcont hderiv hgpos htends]
    ring
  -- assemble the bound on the layer-cake integral
  have hkey : ∫⁻ ω, ENNReal.ofReal (‖∑ k, γ k ω • B k‖ ^ 2) ∂μ ≤
      ENNReal.ofReal (E ^ 2) +
        ENNReal.ofReal (2 * v * D * Real.exp (-(E ^ 2) / (2 * v))) := by
    rw [hLHSlc]
    have hsplit : Set.Ioi (0:ℝ) = Set.Ioc 0 E ∪ Set.Ioi E :=
      (Set.Ioc_union_Ioi_eq_Ioi hEnn).symm
    rw [hsplit, lintegral_union measurableSet_Ioi (Set.Ioc_disjoint_Ioi le_rfl)]
    refine add_le_add ?_ ?_
    · -- bounded part: probability at most one
      calc ∫⁻ t in Set.Ioc 0 E,
            μ {a | t ≤ ‖∑ k, γ k a • B k‖} * ENNReal.ofReal (2 * t)
          ≤ ∫⁻ t in Set.Ioc 0 E, 1 * ENNReal.ofReal (2 * t) :=
            lintegral_mono fun t => mul_le_mul_right' prob_le_one _
      _ = ∫⁻ t in Set.Ioc 0 E, ENNReal.ofReal (2 * t) := by
          simp only [one_mul]
      _ = ENNReal.ofReal (∫ t in Set.Ioc 0 E, 2 * t) := by
          have h2tint : IntegrableOn (fun t : ℝ => 2 * t) (Set.Ioc 0 E) := by
            apply Continuous.integrableOn_Ioc
            fun_prop
          rw [← ofReal_integral_eq_lintegral_ofReal h2tint
            (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => by
              have : (0:ℝ) < t := ht.1
              positivity)]
      _ = ENNReal.ofReal (E ^ 2) := by
          rw [← intervalIntegral.integral_of_le hEnn, hsqint]
    · -- tail part: the Gaussian tail bound (4.1.6)
      calc ∫⁻ t in Set.Ioi E,
            μ {a | t ≤ ‖∑ k, γ k a • B k‖} * ENNReal.ofReal (2 * t)
          ≤ ∫⁻ t in Set.Ioi E,
              ENNReal.ofReal (D * Real.exp (-(t ^ 2) / (2 * v)) * (2 * t)) := by
            refine lintegral_mono_ae (ae_restrict_of_forall_mem measurableSet_Ioi
              fun t htE => ?_)
            have ht0 : 0 ≤ t := hEnn.trans (le_of_lt htE)
            have htail := gaussian_series_rect_tail (B := B) hmeas hlaw hind ht0
            have h1 : μ {a | t ≤ ‖∑ k, γ k a • B k‖} =
                ENNReal.ofReal (μ.real {a | t ≤ ‖∑ k, γ k a • B k‖}) :=
              (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
            rw [h1, ← ENNReal.ofReal_mul (by positivity)]
            refine ENNReal.ofReal_le_ofReal ?_
            have h2t : (0:ℝ) ≤ 2 * t := by linarith
            exact mul_le_mul_of_nonneg_right htail h2t
      _ = ENNReal.ofReal
            (∫ t in Set.Ioi E, D * Real.exp (-(t ^ 2) / (2 * v)) * (2 * t)) :=
          (ofReal_integral_eq_lintegral_ofReal hFTCint
            (ae_restrict_of_forall_mem measurableSet_Ioi hgpos)).symm
      _ = ENNReal.ofReal (2 * v * D * Real.exp (-(E ^ 2) / (2 * v))) := by
          rw [hFTCval]
  -- return to the Bochner integral
  have hBochner : ∫ ω, ‖∑ k, γ k ω • B k‖ ^ 2 ∂μ =
      (∫⁻ ω, ENNReal.ofReal (‖∑ k, γ k ω • B k‖ ^ 2) ∂μ).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun ω => sq_nonneg _)
      ((hnormmeas.pow_const 2).aestronglyMeasurable)]
  have hne : ENNReal.ofReal (E ^ 2) +
      ENNReal.ofReal (2 * v * D * Real.exp (-(E ^ 2) / (2 * v))) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
  have hexpE : Real.exp (-(E ^ 2) / (2 * v)) = D⁻¹ := by
    have hv2 : (2 * v) ≠ 0 := by positivity
    have harg : -(E ^ 2) / (2 * v) = -Real.log D := by
      rw [hE2, show 2 * v * Real.log D = Real.log D * (2 * v) by ring, neg_div,
        mul_div_cancel_right₀ _ hv2]
    rw [harg, Real.exp_neg, Real.exp_log hDpos]
  calc ∫ ω, ‖∑ k, γ k ω • B k‖ ^ 2 ∂μ
      = (∫⁻ ω, ENNReal.ofReal (‖∑ k, γ k ω • B k‖ ^ 2) ∂μ).toReal := hBochner
  _ ≤ (ENNReal.ofReal (E ^ 2) +
        ENNReal.ofReal (2 * v * D * Real.exp (-(E ^ 2) / (2 * v)))).toReal :=
      ENNReal.toReal_mono hne hkey
  _ = E ^ 2 + 2 * v * D * Real.exp (-(E ^ 2) / (2 * v)) := by
      rw [ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal (sq_nonneg _),
        ENNReal.toReal_ofReal (by positivity)]
  _ = 2 * v * Real.log D + 2 * v := by
      rw [hexpE, hE2, mul_assoc (2 * v) D D⁻¹, mul_inv_cancel₀ (ne_of_gt hDpos),
        mul_one]
  _ = 2 * v * (1 + Real.log D) := by ring

/-- **Book eq. (4.1.8)** (§4.1.2, C4-06):
`P(‖Z‖ ≥ 𝔼‖Z‖ + t) ≤ exp(−t²/(2 v⋆(Z)))` for the matrix Gaussian series `Z`. -/
theorem gauss_concentration [Nonempty m] [Nonempty n]
    (hmeas : ∀ k, Measurable (γ k)) (hlaw : ∀ k, IsStdGaussian (γ k) μ)
    (hind : ProbabilityTheory.iIndepFun γ μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | (∫ ω', ‖∑ k, γ k ω' • B k‖ ∂μ) + t ≤ ‖∑ k, γ k ω • B k‖} ≤
      Real.exp (-(t ^ 2) / (2 * weakVariance B)) := by
  simpa only [weakVariance, weakVarianceSet, gaussianWeakVariance,
    gaussianWeakVarianceSet, IsStdGaussian] using
      matrix_gaussian_concentration B hmeas hlaw hind ht

end TwoSided

end MatrixConcentration


set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# Examples: Gaussian/Rademacher random matrices (Tropp §4.2–§4.5)

* **§4.2.1 Gaussian Wigner matrices** (C4-07): `wigner_coeff_sq_sum`
  (`Σ_{j<k}(E_jk+E_kj)² = (d−1)I`), `wigner_variance` (`v(W_d) = d−1`), and
  `wigner_expected_norm` — **Book eq. (4.2.3)**:
  `𝔼‖W_d‖ ≤ √(2(d−1)log(2d))`.
* **§4.2.2 rectangular Gaussian matrices** (C4-08): `gaussianRect_coeff_sum_right`/
  `_left` (`ΣΣ E_jkE_jk* = d₂·I`, `ΣΣ E_jk*E_jk = d₁·I`), `gaussianRect_variance`
  (`v(G) = max{d₁,d₂}`), `gaussianRect_expected_norm` — **Book eq. (4.2.6)**
 ; and the elementary comparison display
  `sqrt_max_comparison` (`√d₁+√d₂ ≤ 2√max{d₁,d₂} ≤ 2(√d₁+√d₂)`).
* **§4.3 randomly signed matrices** (C4-09): `signed_coeff_sum_right`/`_left`
  (the diagonal row/column-norm matrices), `signed_variance`
  (`v(B±) = max{max_j‖b_{j:}‖², max_k‖b_{:k}‖²}`, eq. (4.3.2)), and
  `signed_expected_norm` — **Book eq. (4.3.3)**.
* **§4.5 MaxQP rounding** (C4-18): `maxqp_variance_le` (`v(Z) ≤ α²` under the
  relaxation constraints (4.5.1)), `maxqp_rounding_bound`
  (`𝔼‖Z‖ ≤ α√(2 log(d₁+d₂))`), `maxqp_rounding_bound_one` (`𝔼‖Z‖ ≤ 1` at
  `α² = 1/(2log(d₁+d₂))`).

The benchmarks (4.2.2) (Bai–Yin), (4.2.4)
 (Davidson–Szarek), and (4.3.1)
(Seginer; unspecified constant) are **omitted** as documented in the inventory:
external classical results used only for comparison, never in any proof.
-/

namespace MatrixConcentration

open Matrix Finset MeasureTheory
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

section SingleHelpers

/-- Lean implementation helper: `Σ_j E_jj(c_j) = diag(c)`. -/
lemma sum_single_diag_eq_diagonal (c : m → ℂ) :
    (∑ j, Matrix.single j j (c j)) = Matrix.diagonal c := by
  ext a b
  rw [Matrix.sum_apply, Matrix.diagonal_apply]
  simp only [Matrix.single_apply]
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl, Finset.sum_eq_single a]
    · rw [if_pos ⟨rfl, rfl⟩]
    · intro j _ hja
      rw [if_neg (by tauto)]
    · intro h
      exact absurd (Finset.mem_univ a) h
  · rw [if_neg hab]
    exact Finset.sum_eq_zero fun j _ => by
      rw [if_neg (by rintro ⟨rfl, rfl⟩; exact hab rfl)]

/-- Lean implementation helper: `Σ_j E_jj = I`. -/
lemma sum_single_diag_one : (∑ j : m, Matrix.single j j (1 : ℂ)) = 1 := by
  rw [sum_single_diag_eq_diagonal, Matrix.diagonal_one]

/-- Lean implementation helper: `(E_jk)ᴴ = E_kj` (unit entries). -/
lemma conjTranspose_single (j : m) (k : n) :
    (Matrix.single j k (1 : ℂ))ᴴ = Matrix.single k j 1 := by
  ext a b
  rw [Matrix.conjTranspose_apply]
  simp only [Matrix.single_apply]
  by_cases h1 : j = b
  · by_cases h2 : k = a
    · rw [if_pos ⟨h1, h2⟩, if_pos ⟨h2, h1⟩, star_one]
    · rw [if_neg (by tauto), if_neg (by tauto), star_zero]
  · rw [if_neg (by tauto), if_neg (by tauto), star_zero]

/-- Lean implementation helper: `‖I‖ = 1` in the ℓ₂ operator norm. -/
lemma l2_opNorm_one [Nonempty m] : ‖(1 : Matrix m m ℂ)‖ = 1 := by
  rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal, pi_norm_const, norm_one]

/-- Lean implementation helper: the norm of a nonnegative real multiple of the
identity. -/
lemma l2_opNorm_nnreal_smul_one [Nonempty m] {c : ℝ} (hc : 0 ≤ c) :
    ‖((c : ℂ) • (1 : Matrix m m ℂ))‖ = c := by
  rw [norm_smul, l2_opNorm_one, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hc]

/-- Lean implementation helper: a PSD matrix dominated by the identity has norm
at most one (`λ_max ≤ 1` via the Rayleigh characterization). -/
lemma l2_opNorm_le_one_of_le_one [Nonempty m] {M : Matrix m m ℂ}
    (hpsd : M.PosSemidef) (hle : M ≤ 1) : ‖M‖ ≤ 1 := by
  rw [posSemidef_l2_opNorm_eq_lambdaMax hpsd]
  obtain ⟨u, hu, hval⟩ := exists_unit_rayleigh_eq_lambdaMax hpsd.1
  rw [← hval]
  have h1 := rayleigh_mono_of_loewner_le hle u
  have h2 : rayleigh (1 : Matrix m m ℂ) u = 1 := by
    rw [show rayleigh (1 : Matrix m m ℂ) u =
      (star u ⬝ᵥ ((1 : Matrix m m ℂ) *ᵥ u)).re from rfl, Matrix.one_mulVec,
      dotProduct_star_self_eq, hu]
    norm_num
  rw [h2] at h1
  exact h1

end SingleHelpers

section Wigner

variable [IsProbabilityMeasure μ]

/-- Lean implementation helper: the strict-upper-triangle index set of the Wigner
series in Book eq. (4.2.1). -/
abbrev WignerIndex (d : ℕ) := {p : Fin d × Fin d // p.1 < p.2}

/-- **Book eq. (4.2.1)**: the Wigner coefficient matrices `E_jk + E_kj`. -/
noncomputable def wignerCoeff {d : ℕ} (p : WignerIndex d) :
    Matrix (Fin d) (Fin d) ℂ :=
  Matrix.single p.1.1 p.1.2 1 + Matrix.single p.1.2 p.1.1 1

/-- Lean implementation helper: every Wigner coefficient is Hermitian. -/
lemma isHermitian_wignerCoeff {d : ℕ} (p : WignerIndex d) :
    (wignerCoeff p).IsHermitian := by
  rw [Matrix.IsHermitian, wignerCoeff, Matrix.conjTranspose_add,
    conjTranspose_single, conjTranspose_single, add_comm]

/-- **Book §4.2.1**: `(E_jk + E_kj)² = E_jj + E_kk` for `j < k`—"we have used the
facts that `E_jk E_kj = E_jj` while `E_jk E_jk = 0`".  Implicit source
declaration. -/
lemma wignerCoeff_sq {d : ℕ} (p : WignerIndex d) :
    (wignerCoeff p) ^ 2 =
      Matrix.single p.1.1 p.1.1 1 + Matrix.single p.1.2 p.1.2 1 := by
  obtain ⟨⟨j, k⟩, hjk⟩ := p
  have hne : j ≠ k := ne_of_lt hjk
  rw [sq, wignerCoeff]
  simp only [add_mul, mul_add]
  rw [Matrix.single_mul_single_of_ne (h := hne.symm),
    Matrix.single_mul_single_of_ne (h := hne),
    Matrix.single_mul_single_same, Matrix.single_mul_single_same]
  simp
  exact add_comm _ _

/-- **Book §4.2.1 display**: `Σ_{1≤j<k≤d} (E_jk + E_kj)² = (d−1)·I_d`.  Explicit
source declaration. -/
theorem wigner_coeff_sq_sum (d : ℕ) :
    (∑ p : WignerIndex d, (wignerCoeff p) ^ 2) =
      (((d : ℂ) - 1)) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  classical
  have h0 : (∑ p : WignerIndex d, (wignerCoeff p) ^ 2) =
      ∑ p : WignerIndex d,
        (Matrix.single p.1.1 p.1.1 (1:ℂ) + Matrix.single p.1.2 p.1.2 1) :=
    Finset.sum_congr rfl fun p _ => wignerCoeff_sq p
  have h1 : (∑ p : WignerIndex d,
      (Matrix.single p.1.1 p.1.1 (1:ℂ) + Matrix.single p.1.2 p.1.2 1)) =
      ∑ p ∈ Finset.univ.filter (fun p : Fin d × Fin d => p.1 < p.2),
        (Matrix.single p.1 p.1 1 + Matrix.single p.2 p.2 1) :=
    (Finset.sum_subtype (p := fun p : Fin d × Fin d => p.1 < p.2)
      (Finset.univ.filter fun p : Fin d × Fin d => p.1 < p.2)
      (fun q => by simp)
      (fun q => Matrix.single q.1 q.1 (1:ℂ) + Matrix.single q.2 q.2 1)).symm
  rw [h0, h1, Finset.sum_add_distrib]
  have h2 : (∑ p ∈ Finset.univ.filter (fun p : Fin d × Fin d => p.1 < p.2),
      Matrix.single p.2 p.2 (1:ℂ)) =
      ∑ p ∈ Finset.univ.filter (fun p : Fin d × Fin d => p.2 < p.1),
        Matrix.single p.1 p.1 1 := by
    refine Finset.sum_nbij' (fun p => (p.2, p.1)) (fun p => (p.2, p.1)) ?_ ?_
      ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      exact hp
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      exact hp
    · intro p _
      rfl
    · intro p _
      rfl
    · intro p _
      rfl
  rw [h2, ← Finset.sum_union]
  · have h3 : (Finset.univ.filter (fun p : Fin d × Fin d => p.1 < p.2) ∪
        Finset.univ.filter (fun p : Fin d × Fin d => p.2 < p.1)) =
        Finset.univ.filter (fun p : Fin d × Fin d => p.1 ≠ p.2) := by
      ext p
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro (h | h)
        · exact ne_of_lt h
        · exact (ne_of_lt h).symm
      · intro h
        exact lt_or_gt_of_ne h
    rw [h3, Finset.sum_filter]
    rw [show (Finset.univ : Finset (Fin d × Fin d)) =
      Finset.univ ×ˢ Finset.univ from (Finset.univ_product_univ).symm,
      Finset.sum_product]
    have h4 : ∀ j : Fin d,
        (∑ k : Fin d, if j ≠ k then Matrix.single j j (1:ℂ) else 0) =
        ((d : ℂ) - 1) • Matrix.single j j 1 := by
      intro j
      rw [← Finset.sum_filter, Finset.filter_ne, Finset.sum_const,
        Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ,
        Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ]
      have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (by
        rintro rfl
        exact absurd j.2 (by simp))
      rw [Nat.cast_sub hd, Nat.cast_one]
    rw [Finset.sum_congr rfl fun j _ => h4 j, ← Finset.smul_sum,
      sum_single_diag_one]
  · rw [Finset.disjoint_filter]
    intro p _ h1 h2
    exact absurd h2 (not_lt_of_gt h1)

/-- **Book §4.2.1 display**: the matrix variance statistic `v(W_d) = d − 1`.
Explicit source declaration ("Since the terms are Hermitian, we have only one sum
of squares to consider"). -/
theorem wigner_variance (d : ℕ) [NeZero d] :
    ‖∑ p : WignerIndex d, (wignerCoeff p) ^ 2‖ = (d : ℝ) - 1 := by
  rw [wigner_coeff_sq_sum]
  have h1 : ((d : ℂ) - 1) = (((d : ℝ) - 1 : ℝ) : ℂ) := by push_cast; ring
  rw [h1, l2_opNorm_nnreal_smul_one]
  have : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast this
  linarith

/-- **Book eq. (4.2.3)** (§4.2.1, C4-07):
`𝔼‖W_d‖ ≤ √(2(d−1) log(2d))` for the Gaussian Wigner matrix
`W_d = Σ_{j<k} γ_jk (E_jk + E_kj)`.  Explicit source declaration. -/
theorem wigner_expected_norm {d : ℕ} [NeZero d]
    {γ : WignerIndex d → Ω → ℝ}
    (hmeas : ∀ p, Measurable (γ p)) (hlaw : ∀ p, IsStdGaussian (γ p) μ)
    (hind : ProbabilityTheory.iIndepFun γ μ) :
    ∫ ω, ‖∑ p : WignerIndex d, γ p ω • wignerCoeff p‖ ∂μ ≤
      Real.sqrt (2 * ((d : ℝ) - 1) * Real.log (2 * d)) := by
  have h := gaussian_series_rect_expectation (μ := μ)
    (B := fun p : WignerIndex d => wignerCoeff p) hmeas hlaw hind
  refine h.trans (le_of_eq ?_)
  have hBBH : ∀ p : WignerIndex d,
      wignerCoeff p * (wignerCoeff p)ᴴ = (wignerCoeff p) ^ 2 := fun p => by
    rw [(isHermitian_wignerCoeff p).eq, sq]
  have hBHB : ∀ p : WignerIndex d,
      (wignerCoeff p)ᴴ * wignerCoeff p = (wignerCoeff p) ^ 2 := fun p => by
    rw [(isHermitian_wignerCoeff p).eq, sq]
  rw [Finset.sum_congr rfl fun p _ => hBBH p,
    Finset.sum_congr rfl fun p _ => hBHB p, max_self, wigner_variance d]
  have hcard : ((Fintype.card (Fin d) : ℝ) + (Fintype.card (Fin d) : ℝ)) =
      2 * (d : ℝ) := by
    rw [Fintype.card_fin]
    ring
  rw [hcard]

end Wigner

section RectGaussian

variable [IsProbabilityMeasure μ]

/-- **Book §4.2.2 display**: `Σ_j Σ_k E_jk E_jk* = d₂ · I_{d₁}`.  Explicit source
declaration. -/
theorem gaussianRect_coeff_sum_right :
    (∑ p : m × n, Matrix.single p.1 p.2 (1:ℂ) * (Matrix.single p.1 p.2 (1:ℂ))ᴴ) =
      ((Fintype.card n : ℂ)) • (1 : Matrix m m ℂ) := by
  classical
  have h1 : ∀ p : m × n,
      Matrix.single p.1 p.2 (1:ℂ) * (Matrix.single p.1 p.2 (1:ℂ))ᴴ =
        Matrix.single p.1 p.1 1 := fun p => by
    rw [conjTranspose_single, Matrix.single_mul_single_same, one_mul]
  rw [Finset.sum_congr rfl fun p _ => h1 p]
  rw [show (Finset.univ : Finset (m × n)) = Finset.univ ×ˢ Finset.univ from
    (Finset.univ_product_univ).symm, Finset.sum_product]
  have h2 : ∀ j : m, (∑ _k : n, Matrix.single j j (1:ℂ)) =
      (Fintype.card n : ℂ) • Matrix.single j j 1 := fun j => by
    rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ]
  rw [Finset.sum_congr rfl fun j _ => h2 j, ← Finset.smul_sum,
    sum_single_diag_one]

/-- **Book §4.2.2 display**: `Σ_j Σ_k E_jk* E_jk = d₁ · I_{d₂}`.  Explicit source
declaration. -/
theorem gaussianRect_coeff_sum_left :
    (∑ p : m × n, (Matrix.single p.1 p.2 (1:ℂ))ᴴ * Matrix.single p.1 p.2 (1:ℂ)) =
      ((Fintype.card m : ℂ)) • (1 : Matrix n n ℂ) := by
  classical
  have h1 : ∀ p : m × n,
      (Matrix.single p.1 p.2 (1:ℂ))ᴴ * Matrix.single p.1 p.2 (1:ℂ) =
        Matrix.single p.2 p.2 1 := fun p => by
    rw [conjTranspose_single, Matrix.single_mul_single_same, one_mul]
  rw [Finset.sum_congr rfl fun p _ => h1 p]
  rw [show (Finset.univ : Finset (m × n)) = Finset.univ ×ˢ Finset.univ from
    (Finset.univ_product_univ).symm, Finset.sum_product]
  have h2 : ∀ _j : m, (∑ k : n, Matrix.single k k (1:ℂ)) = (1 : Matrix n n ℂ) :=
    fun _ => sum_single_diag_one
  rw [Finset.sum_congr rfl fun j _ => h2 j, Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℂ]

/-- **Book §4.2.2 display**: `v(G) = max{d₁, d₂}`.  Explicit source declaration. -/
theorem gaussianRect_variance [Nonempty m] [Nonempty n] :
    max ‖∑ p : m × n, Matrix.single p.1 p.2 (1:ℂ) * (Matrix.single p.1 p.2 (1:ℂ))ᴴ‖
        ‖∑ p : m × n, (Matrix.single p.1 p.2 (1:ℂ))ᴴ * Matrix.single p.1 p.2 (1:ℂ)‖ =
      max (Fintype.card m : ℝ) (Fintype.card n) := by
  rw [gaussianRect_coeff_sum_right, gaussianRect_coeff_sum_left]
  rw [show ((Fintype.card n : ℂ)) = (((Fintype.card n : ℝ) : ℂ)) by push_cast; rfl,
    show ((Fintype.card m : ℂ)) = (((Fintype.card m : ℝ) : ℂ)) by push_cast; rfl,
    l2_opNorm_nnreal_smul_one (by positivity),
    l2_opNorm_nnreal_smul_one (by positivity), max_comm]

/-- **Book eq. (4.2.6)** (§4.2.2, C4-08):
`𝔼‖G‖ ≤ √(2 max{d₁,d₂} log(d₁+d₂))` for the standard Gaussian `d₁ × d₂` matrix
`G = ΣΣ γ_jk E_jk`.  Explicit source declaration. -/
theorem gaussianRect_expected_norm [Nonempty m] [Nonempty n]
    {γ : m × n → Ω → ℝ}
    (hmeas : ∀ p, Measurable (γ p)) (hlaw : ∀ p, IsStdGaussian (γ p) μ)
    (hind : ProbabilityTheory.iIndepFun γ μ) :
    ∫ ω, ‖∑ p : m × n, γ p ω • Matrix.single p.1 p.2 (1:ℂ)‖ ∂μ ≤
      Real.sqrt (2 * max (Fintype.card m : ℝ) (Fintype.card n) *
        Real.log ((Fintype.card m : ℝ) + Fintype.card n)) := by
  have h := gaussian_series_rect_expectation (μ := μ)
    (B := fun p : m × n => Matrix.single p.1 p.2 (1:ℂ)) hmeas hlaw hind
  refine h.trans (le_of_eq ?_)
  rw [gaussianRect_variance]

/-- **Book §4.2.2 comparison display**:
`√d₁ + √d₂ ≤ 2√max{d₁,d₂} ≤ 2(√d₁ + √d₂)` — "The leading term is roughly
correct because ...".  Explicit source declaration. -/
theorem sqrt_max_comparison (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt a + Real.sqrt b ≤ 2 * Real.sqrt (max a b) ∧
      2 * Real.sqrt (max a b) ≤ 2 * (Real.sqrt a + Real.sqrt b) := by
  constructor
  · have h1 : Real.sqrt a ≤ Real.sqrt (max a b) :=
      Real.sqrt_le_sqrt (le_max_left _ _)
    have h2 : Real.sqrt b ≤ Real.sqrt (max a b) :=
      Real.sqrt_le_sqrt (le_max_right _ _)
    linarith
  · rcases max_cases a b with ⟨hmax, _⟩ | ⟨hmax, _⟩ <;> rw [hmax]
    · have := Real.sqrt_nonneg b
      linarith
    · have := Real.sqrt_nonneg a
      linarith

end RectGaussian

section SignedMatrix

variable [IsProbabilityMeasure μ]

/-- **Book §4.3 display**: the right Gram sum of the signed-matrix coefficients is
the diagonal matrix of squared row norms.  Explicit source declaration. -/
theorem signed_coeff_sum_right (b : Matrix m n ℝ) :
    (∑ p : m × n, (b p.1 p.2 • Matrix.single p.1 p.2 (1:ℂ)) *
        (b p.1 p.2 • Matrix.single p.1 p.2 (1:ℂ))ᴴ) =
      Matrix.diagonal (fun j => ((∑ k, (b j k) ^ 2 : ℝ) : ℂ)) := by
  classical
  have h1 : ∀ p : m × n,
      (b p.1 p.2 • Matrix.single p.1 p.2 (1:ℂ)) *
        (b p.1 p.2 • Matrix.single p.1 p.2 (1:ℂ))ᴴ =
      Matrix.single p.1 p.1 (((b p.1 p.2) ^ 2 : ℝ) : ℂ) := fun p => by
    rw [Matrix.conjTranspose_smul, star_trivial, conjTranspose_single,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.single_mul_single_same, one_mul, Matrix.smul_single]
    congr 1
    rw [Complex.real_smul, mul_one]
    push_cast
    ring
  rw [Finset.sum_congr rfl fun p _ => h1 p]
  rw [show (Finset.univ : Finset (m × n)) = Finset.univ ×ˢ Finset.univ from
    (Finset.univ_product_univ).symm, Finset.sum_product]
  have h2 : ∀ j : m, (∑ k : n, Matrix.single j j (((b j k) ^ 2 : ℝ) : ℂ)) =
      Matrix.single j j (((∑ k, (b j k) ^ 2 : ℝ) : ℂ)) := fun j => by
    ext a c
    rw [Matrix.sum_apply]
    simp only [Matrix.single_apply]
    by_cases hac : j = a ∧ j = c
    · rw [if_pos hac, Finset.sum_congr rfl fun k _ => if_pos hac]
      push_cast
      ring
    · rw [if_neg hac]
      exact Finset.sum_eq_zero fun k _ => if_neg hac
  rw [Finset.sum_congr rfl fun j _ => h2 j, sum_single_diag_eq_diagonal]

/-- **Book §4.3 display**: the left Gram sum is the diagonal matrix of squared
column norms.  Explicit source declaration. -/
theorem signed_coeff_sum_left (b : Matrix m n ℝ) :
    (∑ p : m × n, (b p.1 p.2 • Matrix.single p.1 p.2 (1:ℂ))ᴴ *
        (b p.1 p.2 • Matrix.single p.1 p.2 (1:ℂ))) =
      Matrix.diagonal (fun k => ((∑ j, (b j k) ^ 2 : ℝ) : ℂ)) := by
  classical
  have key : ∀ p : m × n, (b p.1 p.2 • Matrix.single p.1 p.2 (1:ℂ))ᴴ *
      (b p.1 p.2 • Matrix.single p.1 p.2 (1:ℂ)) =
      Matrix.single p.2 p.2 (((b p.1 p.2) ^ 2 : ℝ) : ℂ) := fun p => by
    rw [Matrix.conjTranspose_smul, star_trivial, conjTranspose_single,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.single_mul_single_same, one_mul, Matrix.smul_single]
    congr 1
    rw [Complex.real_smul, mul_one]
    push_cast
    ring
  rw [Finset.sum_congr rfl fun p _ => key p]
  rw [show (Finset.univ : Finset (m × n)) = Finset.univ ×ˢ Finset.univ from
    (Finset.univ_product_univ).symm, Finset.sum_product, Finset.sum_comm]
  have h2 : ∀ k : n, (∑ j : m, Matrix.single k k (((b j k) ^ 2 : ℝ) : ℂ)) =
      Matrix.single k k (((∑ j, (b j k) ^ 2 : ℝ) : ℂ)) := fun k => by
    ext a c
    rw [Matrix.sum_apply]
    simp only [Matrix.single_apply]
    by_cases hac : k = a ∧ k = c
    · rw [if_pos hac, Finset.sum_congr rfl fun j _ => if_pos hac]
      push_cast
      ring
    · rw [if_neg hac]
      exact Finset.sum_eq_zero fun j _ => if_neg hac
  rw [Finset.sum_congr rfl fun k _ => h2 k, sum_single_diag_eq_diagonal]

/-- Lean implementation helper: the ℓ₂ operator norm of a nonnegative real
diagonal matrix is the maximum entry. -/
lemma l2_opNorm_diagonal_nonneg [Nonempty m] (c : m → ℝ) (hc : ∀ j, 0 ≤ c j) :
    ‖(Matrix.diagonal (fun j => ((c j : ℝ) : ℂ)) : Matrix m m ℂ)‖ =
      Finset.univ.sup' Finset.univ_nonempty c := by
  rw [Matrix.l2_opNorm_diagonal]
  refine le_antisymm ?_ ?_
  · rw [pi_norm_le_iff_of_nonneg]
    · intro j
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc j)]
      exact Finset.le_sup' c (Finset.mem_univ j)
    · obtain ⟨j⟩ := ‹Nonempty m›
      exact le_trans (hc j) (Finset.le_sup' c (Finset.mem_univ j))
  · refine Finset.sup'_le _ _ fun j _ => ?_
    calc c j = ‖((c j : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc j)]
    _ ≤ _ := norm_le_pi_norm (fun j : m => ((c j : ℝ) : ℂ)) j

/-- **Book eq. (4.3.2)** (§4.3, C4-09): the matrix variance statistic of the
randomly signed matrix is the maximum squared row/column norm,
`v(B±) = max{max_j ‖b_{j:}‖², max_k ‖b_{:k}‖²}`.  Explicit source declaration. -/
theorem signed_variance [Nonempty m] [Nonempty n] (b : Matrix m n ℝ) :
    max ‖∑ p : m × n, (b p.1 p.2 • Matrix.single p.1 p.2 (1:ℂ)) *
          (b p.1 p.2 • Matrix.single p.1 p.2 (1:ℂ))ᴴ‖
        ‖∑ p : m × n, (b p.1 p.2 • Matrix.single p.1 p.2 (1:ℂ))ᴴ *
          (b p.1 p.2 • Matrix.single p.1 p.2 (1:ℂ))‖ =
      max (Finset.univ.sup' Finset.univ_nonempty fun j => ∑ k, (b j k) ^ 2)
        (Finset.univ.sup' Finset.univ_nonempty fun k => ∑ j, (b j k) ^ 2) := by
  rw [signed_coeff_sum_right, signed_coeff_sum_left,
    l2_opNorm_diagonal_nonneg _ (fun j => Finset.sum_nonneg fun k _ => sq_nonneg _),
    l2_opNorm_diagonal_nonneg _ (fun k => Finset.sum_nonneg fun j _ => sq_nonneg _)]

/-- **Book eq. (4.3.3)** (§4.3, C4-09):
`𝔼‖B±‖ ≤ √(2 v(B±) log(d₁+d₂))`.  Explicit source declaration.

**Author note.** This pointwise-support form is retained for compatibility; see
`signed_expected_norm_of_isRademacher` for the source-faithful law-only
sibling. -/
theorem signed_expected_norm [Nonempty m] [Nonempty n] (b : Matrix m n ℝ)
    {ϱ : m × n → Ω → ℝ}
    (hmeas : ∀ p, Measurable (ϱ p)) (hlaw : ∀ p, IsRademacher (ϱ p) μ)
    (hrange : ∀ p ω, ϱ p ω = 1 ∨ ϱ p ω = -1)
    (hind : ProbabilityTheory.iIndepFun ϱ μ) :
    ∫ ω, ‖∑ p : m × n, ϱ p ω • (b p.1 p.2 • Matrix.single p.1 p.2 (1:ℂ))‖ ∂μ ≤
      Real.sqrt (2 *
        max (Finset.univ.sup' Finset.univ_nonempty fun j => ∑ k, (b j k) ^ 2)
          (Finset.univ.sup' Finset.univ_nonempty fun k => ∑ j, (b j k) ^ 2) *
        Real.log ((Fintype.card m : ℝ) + Fintype.card n)) := by
  have h := rademacher_series_rect_expectation (μ := μ)
    (B := fun p : m × n => b p.1 p.2 • Matrix.single p.1 p.2 (1:ℂ))
    hmeas hlaw hrange hind
  refine h.trans (le_of_eq ?_)
  rw [signed_variance]

end SignedMatrix

section MaxQP

variable [IsProbabilityMeasure μ] [Nonempty m] [Nonempty n]
variable {B : ι → Matrix m n ℂ}

/-- **Book §4.5 display** (C4-18): under the MaxQP relaxation constraints (4.5.1),
the matrix variance statistic of the rounded solution `Z = α Σ_k ϱ_k B_k`
satisfies `v(Z) ≤ α²`.  Explicit source declaration. -/
theorem maxqp_variance_le {α : ℝ}
    (hc1 : (∑ k, B k * (B k)ᴴ) ≤ 1) (hc2 : (∑ k, (B k)ᴴ * B k) ≤ 1) :
    max ‖∑ k, (α • B k) * (α • B k)ᴴ‖ ‖∑ k, (α • B k)ᴴ * (α • B k)‖ ≤ α ^ 2 := by
  have h1 : (∑ k, (α • B k) * (α • B k)ᴴ) = (α ^ 2) • ∑ k, B k * (B k)ᴴ := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, sq]
  have h2 : (∑ k, (α • B k)ᴴ * (α • B k)) = (α ^ 2) • ∑ k, (B k)ᴴ * B k := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, sq]
  have hpsd1 : (∑ k, B k * (B k)ᴴ).PosSemidef :=
    posSemidef_matsum Finset.univ fun k =>
      Matrix.posSemidef_self_mul_conjTranspose _
  have hpsd2 : (∑ k, (B k)ᴴ * B k).PosSemidef :=
    posSemidef_matsum Finset.univ fun k =>
      Matrix.posSemidef_conjTranspose_mul_self _
  rw [h1, h2]
  refine max_le ?_ ?_
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg α)]
    calc α ^ 2 * ‖∑ k, B k * (B k)ᴴ‖ ≤ α ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (l2_opNorm_le_one_of_le_one hpsd1 hc1)
            (sq_nonneg α)
    _ = α ^ 2 := mul_one _
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg α)]
    calc α ^ 2 * ‖∑ k, (B k)ᴴ * B k‖ ≤ α ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (l2_opNorm_le_one_of_le_one hpsd2 hc2)
            (sq_nonneg α)
    _ = α ^ 2 := mul_one _

/-- **Book §4.5 display** (C4-18): `𝔼‖Z‖ ≤ α √(2 log(d₁+d₂))` for the rounded
MaxQP solution.  Explicit source declaration.

**Author note.** This pointwise-support form is retained for compatibility; see
`maxqp_rounding_bound_of_isRademacher` for the source-faithful law-only
sibling. -/
theorem maxqp_rounding_bound {α : ℝ} (hα : 0 ≤ α)
    (hc1 : (∑ k, B k * (B k)ᴴ) ≤ 1) (hc2 : (∑ k, (B k)ᴴ * B k) ≤ 1)
    {ϱ : ι → Ω → ℝ}
    (hmeas : ∀ k, Measurable (ϱ k)) (hlaw : ∀ k, IsRademacher (ϱ k) μ)
    (hrange : ∀ k ω, ϱ k ω = 1 ∨ ϱ k ω = -1)
    (hind : ProbabilityTheory.iIndepFun ϱ μ) :
    ∫ ω, ‖∑ k, ϱ k ω • (α • B k)‖ ∂μ ≤
      α * Real.sqrt (2 * Real.log ((Fintype.card m : ℝ) + Fintype.card n)) := by
  have h := rademacher_series_rect_expectation (μ := μ)
    (B := fun k => α • B k) hmeas hlaw hrange hind
  refine h.trans ?_
  have hlog : (0 : ℝ) ≤ Real.log ((Fintype.card m : ℝ) + Fintype.card n) := by
    refine Real.log_nonneg ?_
    have h1 : (1 : ℝ) ≤ (Fintype.card m : ℝ) := by exact_mod_cast Fintype.card_pos
    have h2 : (0 : ℝ) ≤ (Fintype.card n : ℝ) := by positivity
    linarith
  calc Real.sqrt (2 * max ‖∑ k, (α • B k) * (α • B k)ᴴ‖
        ‖∑ k, (α • B k)ᴴ * (α • B k)‖ *
        Real.log ((Fintype.card m : ℝ) + Fintype.card n))
      ≤ Real.sqrt (2 * α ^ 2 *
          Real.log ((Fintype.card m : ℝ) + Fintype.card n)) := by
        refine Real.sqrt_le_sqrt ?_
        refine mul_le_mul_of_nonneg_right ?_ hlog
        exact mul_le_mul_of_nonneg_left (maxqp_variance_le hc1 hc2) (by norm_num)
  _ = α * Real.sqrt (2 * Real.log ((Fintype.card m : ℝ) + Fintype.card n)) := by
      rw [show 2 * α ^ 2 * Real.log ((Fintype.card m : ℝ) + Fintype.card n) =
        α ^ 2 * (2 * Real.log ((Fintype.card m : ℝ) + Fintype.card n)) by ring,
        Real.sqrt_mul (sq_nonneg α), Real.sqrt_sq hα]

/-- **Book §4.5 conclusion** (C4-18): with the scaling `α² = 1/(2 log(d₁+d₂))`,
the rounded solution obeys the norm constraint on average, `𝔼‖Z‖ ≤ 1`.
Explicit source declaration.

**Author note.** This pointwise-support form is retained for compatibility; see
`maxqp_rounding_bound_one_of_isRademacher` for the source-faithful law-only
sibling. -/
theorem maxqp_rounding_bound_one
    (hc1 : (∑ k, B k * (B k)ᴴ) ≤ 1) (hc2 : (∑ k, (B k)ᴴ * B k) ≤ 1)
    {ϱ : ι → Ω → ℝ}
    (hmeas : ∀ k, Measurable (ϱ k)) (hlaw : ∀ k, IsRademacher (ϱ k) μ)
    (hrange : ∀ k ω, ϱ k ω = 1 ∨ ϱ k ω = -1)
    (hind : ProbabilityTheory.iIndepFun ϱ μ) :
    ∫ ω, ‖∑ k, ϱ k ω •
        ((Real.sqrt (2 * Real.log ((Fintype.card m : ℝ) + Fintype.card n)))⁻¹ •
          B k)‖ ∂μ ≤ 1 := by
  set L : ℝ := Real.sqrt (2 * Real.log ((Fintype.card m : ℝ) + Fintype.card n))
    with hLdef
  have hLpos : 0 < L := by
    rw [hLdef]
    refine Real.sqrt_pos.mpr ?_
    have h1 : (1 : ℝ) ≤ (Fintype.card m : ℝ) := by exact_mod_cast Fintype.card_pos
    have h2 : (1 : ℝ) ≤ (Fintype.card n : ℝ) := by exact_mod_cast Fintype.card_pos
    have h3 : (0 : ℝ) < Real.log ((Fintype.card m : ℝ) + Fintype.card n) := by
      refine Real.log_pos ?_
      linarith
    linarith [h3]
  have h := maxqp_rounding_bound (α := L⁻¹) (by positivity) hc1 hc2 hmeas hlaw
    hrange hind
  refine h.trans (le_of_eq ?_)
  rw [← hLdef]
  exact inv_mul_cancel₀ (ne_of_gt hLpos)

end MaxQP

end MatrixConcentration


set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# Example: Gaussian Toeplitz matrices (Tropp §4.4)

* `shiftPow` — the `k`-step shift-up matrix `C^k` (the shift-up operator `C` of
  the display after (4.4.1) is `shiftPow d 1`), with `shiftPow_one_pow`
  (`C^k` really is the `k`-th power of `C`);
* `shiftPow_mul_conjTranspose`/`conjTranspose_mul_shiftPow` — **§4.4 display**:
  `C^k (C^k)* = Σ_{j≤d−k} E_jj` and `(C^k)* C^k = Σ_{j>k} E_jj` (rendered as
  the corresponding 0/1 diagonal matrices);
* `toeplitzCoeff` — the coefficient family of the series representation
  (4.4.1),
  `Γ_d = γ₀ I + Σ_{k<d−1} γ_k C^k + Σ_{k<d−1} γ_{−k} (C^k)*`
  (index type `Unit ⊕ Fin (d−1) ⊕ Fin (d−1)`);
* `toeplitz_coeff_sum_right`/`_left` — the **§4.4 multline display**:
  `I² + Σ_k C^k(C^k)* + Σ_k (C^k)*C^k = Σ_j (1 + (d−j) + (j−1)) E_jj = d·I`;
* `toeplitz_variance` — `v(Γ_d) = d`;
* `toeplitz_expected_norm` — **Book eq. (4.4.3)**:
  `𝔼‖Γ_d‖ ≤ √(2d log(2d))`.

The Sen–Virág asymptotic comparison (`0.8288 ≤ 𝔼‖Γ_d‖/√(2d log 2d) ≤ 1`) is
**omitted** as documented in the inventory (external + asymptotic benchmark).
-/

namespace MatrixConcentration

open Matrix Finset MeasureTheory
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}

section ShiftMatrix

/-- **Book §4.4**, following eq. (4.4.1): the `k`-step **shift-up matrix** `C^k`,
where `(C^k)_{ij} = 1` iff
`j = i + k`.  `shiftPow d 1` is the shift-up operator `C` displayed after
(4.4.1); `shiftPow_one_pow` verifies the power identity.  Explicit source
declaration. -/
def shiftPow (d k : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun i j => if (j : ℕ) = (i : ℕ) + k then 1 else 0

@[simp] lemma shiftPow_apply (d k : ℕ) (i j : Fin d) :
    shiftPow d k i j = if (j : ℕ) = (i : ℕ) + k then 1 else 0 := rfl

/-- Lean implementation helper: the zero-step shift is the identity matrix. -/
lemma shiftPow_zero (d : ℕ) : shiftPow d 0 = 1 := by
  ext i j
  rw [shiftPow_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, if_pos (by omega)]
  · rw [if_neg hij, if_neg (by
      intro h
      exact hij (Fin.ext (by omega)).symm)]

/-- Lean implementation helper: a `Fin`-indexed sum with a single active index. -/
lemma fin_sum_ite_eq (d c : ℕ) (hc : c < d) (f : Fin d → ℂ) :
    (∑ l : Fin d, if (l : ℕ) = c then f l else 0) = f ⟨c, hc⟩ := by
  rw [Finset.sum_eq_single (⟨c, hc⟩ : Fin d)]
  · rw [if_pos rfl]
  · intro l _ hl
    rw [if_neg fun h => hl (Fin.ext h)]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **Book §4.4**: "`C^k` shifts a vector up by `k` places"—the `k`-step shift is
the `k`-th power of the shift-up operator.  Implicit source declaration. -/
lemma shiftPow_one_pow (d k : ℕ) : (shiftPow d 1) ^ k = shiftPow d k := by
  induction k with
  | zero => rw [pow_zero, shiftPow_zero]
  | succ k ih =>
    rw [pow_succ, ih]
    ext i j
    rw [Matrix.mul_apply, shiftPow_apply]
    have hsummand : ∀ l : Fin d, shiftPow d k i l * shiftPow d 1 l j =
        if (l : ℕ) = (i : ℕ) + k then
          (if (j : ℕ) = (l : ℕ) + 1 then (1 : ℂ) else 0) else 0 := fun l => by
      rw [shiftPow_apply, shiftPow_apply, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_congr rfl fun l _ => hsummand l]
    by_cases hij : (j : ℕ) = (i : ℕ) + (k + 1)
    · have hik : (i : ℕ) + k < d := by
        have := j.isLt
        omega
      rw [fin_sum_ite_eq d ((i : ℕ) + k) hik, if_pos hij,
        if_pos (show (j : ℕ) = ((⟨(i : ℕ) + k, hik⟩ : Fin d) : ℕ) + 1 from by
          show (j : ℕ) = (i : ℕ) + k + 1
          omega)]
    · rw [if_neg hij]
      refine Finset.sum_eq_zero fun l _ => ?_
      by_cases h1 : (l : ℕ) = (i : ℕ) + k
      · rw [if_pos h1, if_neg (by omega)]
      · rw [if_neg h1]

/-- **Book §4.4 display**: `C^k (C^k)* = Σ_{j=1}^{d−k} E_jj`, rendered as the 0/1
diagonal matrix supported on the first `d − k` coordinates.  Explicit source
declaration. -/
lemma shiftPow_mul_conjTranspose (d k : ℕ) :
    shiftPow d k * (shiftPow d k)ᴴ =
      Matrix.diagonal (fun i : Fin d => if (i : ℕ) + k < d then (1 : ℂ) else 0) := by
  ext i j
  have hsummand : ∀ l : Fin d, shiftPow d k i l * (shiftPow d k)ᴴ l j =
      if (l : ℕ) = (i : ℕ) + k then
        (if (l : ℕ) = (j : ℕ) + k then (1 : ℂ) else 0) else 0 := fun l => by
    rw [Matrix.conjTranspose_apply, shiftPow_apply, shiftPow_apply,
      apply_ite (star : ℂ → ℂ), star_one, star_zero, ite_mul, one_mul, zero_mul]
  rw [Matrix.mul_apply, Finset.sum_congr rfl fun l _ => hsummand l,
    Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    by_cases hk : (i : ℕ) + k < d
    · rw [if_pos hk, fin_sum_ite_eq d ((i : ℕ) + k) hk,
        if_pos (show ((⟨(i : ℕ) + k, hk⟩ : Fin d) : ℕ) = (i : ℕ) + k from rfl)]
    · rw [if_neg hk]
      refine Finset.sum_eq_zero fun l _ => ?_
      rw [if_neg (by
        have := l.isLt
        omega)]
  · rw [if_neg hij]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases h1 : (l : ℕ) = (i : ℕ) + k
    · rw [if_pos h1, if_neg (by
        intro h2
        exact hij (Fin.ext (by omega)))]
    · rw [if_neg h1]

/-- **Book §4.4 display**: `(C^k)* C^k = Σ_{j=k+1}^{d} E_jj`, rendered as the 0/1
diagonal matrix supported on the coordinates `≥ k`.  Explicit source
declaration. -/
lemma conjTranspose_mul_shiftPow (d k : ℕ) :
    (shiftPow d k)ᴴ * shiftPow d k =
      Matrix.diagonal (fun i : Fin d => if k ≤ (i : ℕ) then (1 : ℂ) else 0) := by
  ext i j
  have hsummand : ∀ l : Fin d, (shiftPow d k)ᴴ i l * shiftPow d k l j =
      if (i : ℕ) = (l : ℕ) + k then
        (if (j : ℕ) = (l : ℕ) + k then (1 : ℂ) else 0) else 0 := fun l => by
    rw [Matrix.conjTranspose_apply, shiftPow_apply, shiftPow_apply,
      apply_ite (star : ℂ → ℂ), star_one, star_zero, ite_mul, one_mul, zero_mul]
  rw [Matrix.mul_apply, Finset.sum_congr rfl fun l _ => hsummand l,
    Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    by_cases hk : k ≤ (i : ℕ)
    · have hik : (i : ℕ) - k < d := by
        have := i.isLt
        omega
      have hcongr : (∑ l : Fin d, if (i : ℕ) = (l : ℕ) + k then
          (if (i : ℕ) = (l : ℕ) + k then (1 : ℂ) else 0) else 0) =
          ∑ l : Fin d, if (l : ℕ) = (i : ℕ) - k then
            (if (i : ℕ) = (l : ℕ) + k then (1 : ℂ) else 0) else 0 :=
        Finset.sum_congr rfl fun l _ => if_congr (by omega) rfl rfl
      rw [if_pos hk, hcongr, fin_sum_ite_eq d ((i : ℕ) - k) hik,
        if_pos (show (i : ℕ) = ((⟨(i : ℕ) - k, hik⟩ : Fin d) : ℕ) + k from by
          show (i : ℕ) = (i : ℕ) - k + k
          omega)]
    · rw [if_neg hk]
      refine Finset.sum_eq_zero fun l _ => ?_
      rw [if_neg (by omega)]
  · rw [if_neg hij]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases h1 : (i : ℕ) = (l : ℕ) + k
    · rw [if_pos h1, if_neg (by
        intro h2
        exact hij (Fin.ext (by omega)))]
    · rw [if_neg h1]

end ShiftMatrix

section ToeplitzSeries

/-- **Book eq. (4.4.1)**: the coefficient family of the Gaussian Toeplitz series—the identity
(for `γ₀`), the shifts `C^k` (for `γ_k`, `k ≥ 1`), and their adjoints (for
`γ_{−k}`). -/
def toeplitzCoeff (d : ℕ) : Unit ⊕ Fin (d - 1) ⊕ Fin (d - 1) →
    Matrix (Fin d) (Fin d) ℂ
  | Sum.inl _ => 1
  | Sum.inr (Sum.inl k) => shiftPow d ((k : ℕ) + 1)
  | Sum.inr (Sum.inr k) => (shiftPow d ((k : ℕ) + 1))ᴴ

/-- Lean implementation helper: a sum of diagonal matrices is diagonal. -/
lemma diagonal_finset_sum {ι' : Type*} {m : Type*} [Fintype m] [DecidableEq m]
    (s : Finset ι') (f : ι' → m → ℂ) :
    (∑ k ∈ s, Matrix.diagonal (f k)) = Matrix.diagonal (fun i => ∑ k ∈ s, f k i) := by
  ext a b
  rw [Matrix.sum_apply, Matrix.diagonal_apply]
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl]
    exact Finset.sum_congr rfl fun k _ => Matrix.diagonal_apply_eq _ _
  · rw [if_neg hab]
    exact Finset.sum_eq_zero fun k _ => Matrix.diagonal_apply_ne _ hab

/-- Lean implementation helper: counting the modulators active at a coordinate,
`#{k < N : k < c} = c` for `c ≤ N`. -/
lemma sum_ite_coe_lt (N c : ℕ) (hc : c ≤ N) :
    (∑ k : Fin N, if (k : ℕ) < c then (1 : ℂ) else 0) = (c : ℂ) := by
  rw [Fin.sum_univ_eq_sum_range (fun k => if k < c then (1 : ℂ) else 0) N]
  rw [Finset.sum_boole]
  have hfil : {x ∈ Finset.range N | x < c} = Finset.range c := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hfil, Finset.card_range]

/-- **Book §4.4 multline display**: the right Gram sum of the Toeplitz coefficient
family collapses to `d·I` — "In the second line, we (carefully) switch the order
of summation ... `= Σ_j (1 + (d−j) + (j−1)) E_jj = d·I_d`".  Explicit source
declaration. -/
theorem toeplitz_coeff_sum_right (d : ℕ) [NeZero d] :
    (∑ p, toeplitzCoeff d p * (toeplitzCoeff d p)ᴴ) =
      ((d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  classical
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  have h0 : (∑ _x : Unit, toeplitzCoeff d (Sum.inl _x) *
      (toeplitzCoeff d (Sum.inl _x))ᴴ) = Matrix.diagonal (fun _ => (1 : ℂ)) := by
    rw [Fintype.sum_unique]
    show (1 : Matrix (Fin d) (Fin d) ℂ) * (1 : Matrix (Fin d) (Fin d) ℂ)ᴴ = _
    rw [Matrix.conjTranspose_one, mul_one, Matrix.diagonal_one]
  have hterm1 : ∀ k : Fin (d - 1), toeplitzCoeff d (Sum.inr (Sum.inl k)) *
      (toeplitzCoeff d (Sum.inr (Sum.inl k)))ᴴ =
      Matrix.diagonal (fun i : Fin d =>
        if (i : ℕ) + ((k : ℕ) + 1) < d then (1 : ℂ) else 0) := fun k =>
    shiftPow_mul_conjTranspose d ((k : ℕ) + 1)
  have hterm2 : ∀ k : Fin (d - 1), toeplitzCoeff d (Sum.inr (Sum.inr k)) *
      (toeplitzCoeff d (Sum.inr (Sum.inr k)))ᴴ =
      Matrix.diagonal (fun i : Fin d =>
        if ((k : ℕ) + 1) ≤ (i : ℕ) then (1 : ℂ) else 0) := fun k => by
    show (shiftPow d ((k : ℕ) + 1))ᴴ * ((shiftPow d ((k : ℕ) + 1))ᴴ)ᴴ =
      Matrix.diagonal (fun i : Fin d =>
        if ((k : ℕ) + 1) ≤ (i : ℕ) then (1 : ℂ) else 0)
    rw [Matrix.conjTranspose_conjTranspose]
    exact conjTranspose_mul_shiftPow d ((k : ℕ) + 1)
  have h1 : (∑ k : Fin (d - 1), toeplitzCoeff d (Sum.inr (Sum.inl k)) *
      (toeplitzCoeff d (Sum.inr (Sum.inl k)))ᴴ) =
      Matrix.diagonal (fun i : Fin d =>
        ∑ k : Fin (d - 1), if (i : ℕ) + ((k : ℕ) + 1) < d then (1 : ℂ) else 0) := by
    rw [Finset.sum_congr rfl fun k _ => hterm1 k]
    exact diagonal_finset_sum _ _
  have h2 : (∑ k : Fin (d - 1), toeplitzCoeff d (Sum.inr (Sum.inr k)) *
      (toeplitzCoeff d (Sum.inr (Sum.inr k)))ᴴ) =
      Matrix.diagonal (fun i : Fin d =>
        ∑ k : Fin (d - 1), if ((k : ℕ) + 1) ≤ (i : ℕ) then (1 : ℂ) else 0) := by
    rw [Finset.sum_congr rfl fun k _ => hterm2 k]
    exact diagonal_finset_sum _ _
  rw [h0, h1, h2, Matrix.diagonal_add, Matrix.diagonal_add]
  have hone : ((d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ) =
      Matrix.diagonal (fun _ : Fin d => (d : ℂ)) := by
    rw [← Matrix.diagonal_one, ← Matrix.diagonal_smul]
    congr 1
    funext x
    rw [Pi.smul_apply, smul_eq_mul, mul_one]
  rw [hone]
  congr 1
  funext i
  have hi := i.isLt
  have hc1 : (∑ k : Fin (d - 1), if (i : ℕ) + ((k : ℕ) + 1) < d
      then (1 : ℂ) else 0) = ((d - 1 - (i : ℕ) : ℕ) : ℂ) := by
    have hcg : (∑ k : Fin (d - 1), if (i : ℕ) + ((k : ℕ) + 1) < d
        then (1 : ℂ) else 0) =
        ∑ k : Fin (d - 1), if (k : ℕ) < d - 1 - (i : ℕ) then (1 : ℂ) else 0 :=
      Finset.sum_congr rfl fun k _ => if_congr (by omega) rfl rfl
    rw [hcg]
    exact sum_ite_coe_lt (d - 1) (d - 1 - (i : ℕ)) (by omega)
  have hc2 : (∑ k : Fin (d - 1), if ((k : ℕ) + 1) ≤ (i : ℕ)
      then (1 : ℂ) else 0) = (((i : ℕ) : ℕ) : ℂ) := by
    have hcg : (∑ k : Fin (d - 1), if ((k : ℕ) + 1) ≤ (i : ℕ)
        then (1 : ℂ) else 0) =
        ∑ k : Fin (d - 1), if (k : ℕ) < (i : ℕ) then (1 : ℂ) else 0 :=
      Finset.sum_congr rfl fun k _ => if_congr (by omega) rfl rfl
    rw [hcg]
    exact sum_ite_coe_lt (d - 1) (i : ℕ) (by omega)
  rw [hc1, hc2]
  have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hcast : ((d - 1 - (i : ℕ) : ℕ) : ℂ) = (d : ℂ) - 1 - (i : ℕ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one]
  rw [hcast]
  ring

/-- **Book §4.4**: "In this instance, the two terms in the variance are the
same" — the left Gram sum also collapses to `d·I` (the coefficient family is
closed under adjoints).  Explicit source declaration. -/
theorem toeplitz_coeff_sum_left (d : ℕ) [NeZero d] :
    (∑ p, (toeplitzCoeff d p)ᴴ * toeplitzCoeff d p) =
      ((d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  classical
  have h := toeplitz_coeff_sum_right d
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type] at h ⊢
  rw [show (∑ k : Fin (d - 1), (toeplitzCoeff d (Sum.inr (Sum.inl k)))ᴴ *
      toeplitzCoeff d (Sum.inr (Sum.inl k))) =
      ∑ k : Fin (d - 1), toeplitzCoeff d (Sum.inr (Sum.inr k)) *
        (toeplitzCoeff d (Sum.inr (Sum.inr k)))ᴴ from
    Finset.sum_congr rfl fun k _ => by
      show (shiftPow d ((k : ℕ) + 1))ᴴ * shiftPow d ((k : ℕ) + 1) =
        (shiftPow d ((k : ℕ) + 1))ᴴ * ((shiftPow d ((k : ℕ) + 1))ᴴ)ᴴ
      rw [Matrix.conjTranspose_conjTranspose]]
  rw [show (∑ k : Fin (d - 1), (toeplitzCoeff d (Sum.inr (Sum.inr k)))ᴴ *
      toeplitzCoeff d (Sum.inr (Sum.inr k))) =
      ∑ k : Fin (d - 1), toeplitzCoeff d (Sum.inr (Sum.inl k)) *
        (toeplitzCoeff d (Sum.inr (Sum.inl k)))ᴴ from
    Finset.sum_congr rfl fun k _ => by
      show ((shiftPow d ((k : ℕ) + 1))ᴴ)ᴴ * (shiftPow d ((k : ℕ) + 1))ᴴ =
        shiftPow d ((k : ℕ) + 1) * (shiftPow d ((k : ℕ) + 1))ᴴ
      rw [Matrix.conjTranspose_conjTranspose]]
  rw [show (∑ _x : Unit, (toeplitzCoeff d (Sum.inl _x))ᴴ *
      toeplitzCoeff d (Sum.inl _x)) =
      ∑ _x : Unit, toeplitzCoeff d (Sum.inl _x) *
        (toeplitzCoeff d (Sum.inl _x))ᴴ from
    Finset.sum_congr rfl fun x _ => by
      show (1 : Matrix (Fin d) (Fin d) ℂ)ᴴ * 1 = 1 * (1 : Matrix (Fin d) (Fin d) ℂ)ᴴ
      rw [Matrix.conjTranspose_one]]
  rw [show (∑ _x : Unit, toeplitzCoeff d (Sum.inl _x) *
        (toeplitzCoeff d (Sum.inl _x))ᴴ) +
      ((∑ k : Fin (d - 1), toeplitzCoeff d (Sum.inr (Sum.inr k)) *
        (toeplitzCoeff d (Sum.inr (Sum.inr k)))ᴴ) +
       (∑ k : Fin (d - 1), toeplitzCoeff d (Sum.inr (Sum.inl k)) *
        (toeplitzCoeff d (Sum.inr (Sum.inl k)))ᴴ)) =
      (∑ _x : Unit, toeplitzCoeff d (Sum.inl _x) *
        (toeplitzCoeff d (Sum.inl _x))ᴴ) +
      ((∑ k : Fin (d - 1), toeplitzCoeff d (Sum.inr (Sum.inl k)) *
        (toeplitzCoeff d (Sum.inr (Sum.inl k)))ᴴ) +
       (∑ k : Fin (d - 1), toeplitzCoeff d (Sum.inr (Sum.inr k)) *
        (toeplitzCoeff d (Sum.inr (Sum.inr k)))ᴴ)) from by
    congr 1
    exact add_comm _ _]
  exact h

/-- **Book §4.4 display**: `v(Γ_d) = d`.  Explicit source declaration. -/
theorem toeplitz_variance (d : ℕ) [NeZero d] :
    max ‖∑ p, toeplitzCoeff d p * (toeplitzCoeff d p)ᴴ‖
        ‖∑ p, (toeplitzCoeff d p)ᴴ * toeplitzCoeff d p‖ = (d : ℝ) := by
  have : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero (NeZero.ne d))
  rw [toeplitz_coeff_sum_right, toeplitz_coeff_sum_left, max_self,
    show ((d : ℂ)) = (((d : ℝ) : ℂ)) by push_cast; rfl,
    l2_opNorm_nnreal_smul_one (by positivity)]

/-- **Book eq. (4.4.3)** (§4.4, C4-10):
`𝔼‖Γ_d‖ ≤ √(2d log(2d))` for the (unsymmetric) Gaussian Toeplitz matrix (4.4.1).
Explicit source declaration. -/
theorem toeplitz_expected_norm {d : ℕ} [NeZero d] [IsProbabilityMeasure μ]
    {γ : Unit ⊕ Fin (d - 1) ⊕ Fin (d - 1) → Ω → ℝ}
    (hmeas : ∀ p, Measurable (γ p)) (hlaw : ∀ p, IsStdGaussian (γ p) μ)
    (hind : ProbabilityTheory.iIndepFun γ μ) :
    ∫ ω, ‖∑ p, γ p ω • toeplitzCoeff d p‖ ∂μ ≤
      Real.sqrt (2 * (d : ℝ) * Real.log (2 * d)) := by
  have : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero (NeZero.ne d))
  have h := gaussian_series_rect_expectation (μ := μ)
    (B := fun p => toeplitzCoeff d p) hmeas hlaw hind
  refine h.trans (le_of_eq ?_)
  rw [toeplitz_variance]
  have hcard : ((Fintype.card (Fin d) : ℝ) + (Fintype.card (Fin d) : ℝ)) =
      2 * (d : ℝ) := by
    rw [Fintype.card_fin]
    ring
  rw [hcard]

end ToeplitzSeries

end MatrixConcentration


namespace MatrixConcentration

open Matrix Finset MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}

section RademacherSupportWrappers

variable {ι m n : Type*} [Fintype ι] [DecidableEq ι]
variable [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
variable [IsProbabilityMeasure μ]

/-- **Book Theorem 4.6.1, equation (4.6.3), expectation form.**
Source-faithful sibling of `rademacher_herm_expectation`: the Rademacher law supplies
the `{−1,1}` support almost surely, so no pointwise representative hypothesis is needed. -/
theorem rademacher_herm_expectation_of_isRademacher [Nonempty n]
    {A : ι → Matrix n n ℂ} {f : ι → Ω → ℝ}
    (hmeas : ∀ k, Measurable (f k)) (hlaw : ∀ k, IsRademacher (f k) μ)
    (hind : iIndepFun f μ) (hA : ∀ k, (A k).IsHermitian) :
    ∫ ω, lambdaMax (isHermitian_matsum Finset.univ
        (fun k => isHermitian_real_smul (hA k) (f k ω))) ∂μ ≤
      Real.sqrt (2 * ‖∑ k, (A k) ^ 2‖ * Real.log (Fintype.card n)) := by
  let f' : ι → Ω → ℝ := fun k ω => rademacherRepresentative (f k ω)
  have hm' : ∀ k, Measurable (f' k) := fun k =>
    measurable_rademacherRepresentative.comp (hmeas k)
  have hl' : ∀ k, IsRademacher (f' k) μ := fun k =>
    isRademacher_rademacherRepresentative (hmeas k) (hlaw k)
  have hi' : iIndepFun f' μ := iIndepFun_rademacherRepresentative hmeas hlaw hind
  have hr' : ∀ k ω, f' k ω = 1 ∨ f' k ω = -1 := fun k ω =>
    rademacherRepresentative_range (f k ω)
  have hmain := rademacher_herm_expectation (μ := μ) (A := A)
    hm' hl' hr' hi' hA
  have hsum := rademacherRepresentative_matsum_ae hmeas hlaw A
  have hint : (fun ω => lambdaMax (isHermitian_matsum Finset.univ
      (fun k => isHermitian_real_smul (hA k) (f' k ω)))) =ᵐ[μ]
      fun ω => lambdaMax (isHermitian_matsum Finset.univ
        (fun k => isHermitian_real_smul (hA k) (f k ω))) := by
    filter_upwards [hsum] with ω hω
    exact lambdaMax_congr hω _ _
  rwa [integral_congr_ae hint] at hmain

/-- **Book Theorem 4.6.1, equation (4.6.3), upper tail.**
Almost-sure-support sibling of `rademacher_herm_tail`. -/
theorem rademacher_herm_tail_of_isRademacher [Nonempty n]
    {A : ι → Matrix n n ℂ} {f : ι → Ω → ℝ}
    (hmeas : ∀ k, Measurable (f k)) (hlaw : ∀ k, IsRademacher (f k) μ)
    (hind : iIndepFun f μ) (hA : ∀ k, (A k).IsHermitian)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ lambdaMax (isHermitian_matsum Finset.univ
        (fun k => isHermitian_real_smul (hA k) (f k ω)))} ≤
      (Fintype.card n : ℝ) *
        Real.exp (-(t ^ 2) / (2 * ‖∑ k, (A k) ^ 2‖)) := by
  let f' : ι → Ω → ℝ := fun k ω => rademacherRepresentative (f k ω)
  have hm' : ∀ k, Measurable (f' k) := fun k =>
    measurable_rademacherRepresentative.comp (hmeas k)
  have hl' : ∀ k, IsRademacher (f' k) μ := fun k =>
    isRademacher_rademacherRepresentative (hmeas k) (hlaw k)
  have hi' : iIndepFun f' μ := iIndepFun_rademacherRepresentative hmeas hlaw hind
  have hr' : ∀ k ω, f' k ω = 1 ∨ f' k ω = -1 := fun k ω =>
    rademacherRepresentative_range (f k ω)
  have hmain := rademacher_herm_tail (μ := μ) (A := A)
    hm' hl' hr' hi' hA ht
  have hsum := rademacherRepresentative_matsum_ae hmeas hlaw A
  have hevent : ∀ᵐ ω ∂μ, ω ∈ {ω | t ≤ lambdaMax (isHermitian_matsum Finset.univ
      (fun k => isHermitian_real_smul (hA k) (f' k ω)))} ↔
      ω ∈ {ω | t ≤ lambdaMax (isHermitian_matsum Finset.univ
        (fun k => isHermitian_real_smul (hA k) (f k ω)))} := by
    filter_upwards [hsum] with ω hω
    rw [lambdaMax_congr hω _ _]
  have hevent' : {ω | t ≤ lambdaMax (isHermitian_matsum Finset.univ
      (fun k => isHermitian_real_smul (hA k) (f' k ω)))} =ᵐ[μ]
      {ω | t ≤ lambdaMax (isHermitian_matsum Finset.univ
        (fun k => isHermitian_real_smul (hA k) (f k ω)))} :=
    hevent.mono fun _ h => propext h
  rwa [measureReal_congr hevent'] at hmain

/-- **Book §4.6.2**, lower-expectation Rademacher display, with only the
distributional Rademacher hypothesis.  This is the law-only counterpart of
`rademacher_herm_min_expectation`. -/
theorem rademacher_herm_min_expectation_of_isRademacher [Nonempty n]
    {A : ι → Matrix n n ℂ} {f : ι → Ω → ℝ}
    (hmeas : ∀ k, Measurable (f k)) (hlaw : ∀ k, IsRademacher (f k) μ)
    (hind : iIndepFun f μ) (hA : ∀ k, (A k).IsHermitian) :
    -Real.sqrt (2 * ‖∑ k, (A k) ^ 2‖ * Real.log (Fintype.card n)) ≤
      ∫ ω, lambdaMin (isHermitian_matsum Finset.univ
        (fun k => isHermitian_real_smul (hA k) (f k ω))) ∂μ := by
  have hmain := rademacher_herm_expectation_of_isRademacher hmeas hlaw hind
    (fun k => (hA k).neg)
  have hvar : (∑ k, (-(A k)) ^ 2) = ∑ k, (A k) ^ 2 := by
    exact Finset.sum_congr rfl fun k _ => neg_sq _
  rw [hvar] at hmain
  have hcongr : (∫ ω, lambdaMin (isHermitian_matsum Finset.univ
      (fun k => isHermitian_real_smul (hA k) (f k ω))) ∂μ) =
      -∫ ω, lambdaMax (isHermitian_matsum Finset.univ
        (fun k => isHermitian_real_smul ((hA k).neg) (f k ω))) ∂μ := by
    rw [← MeasureTheory.integral_neg]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω =>
      lambdaMin_series_eq_neg_lambdaMax_neg hA ω)
  rw [hcongr]
  linarith
/-- **Book §4.6.2**, lower-tail Rademacher display, with only the distributional
Rademacher hypothesis.  This is the law-only counterpart of
`rademacher_herm_min_tail`. -/
theorem rademacher_herm_min_tail_of_isRademacher [Nonempty n]
    {A : ι → Matrix n n ℂ} {f : ι → Ω → ℝ}
    (hmeas : ∀ k, Measurable (f k)) (hlaw : ∀ k, IsRademacher (f k) μ)
    (hind : iIndepFun f μ) (hA : ∀ k, (A k).IsHermitian)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | lambdaMin (isHermitian_matsum Finset.univ
        (fun k => isHermitian_real_smul (hA k) (f k ω))) ≤ -t} ≤
      (Fintype.card n : ℝ) *
        Real.exp (-(t ^ 2) / (2 * ‖∑ k, (A k) ^ 2‖)) := by
  have hmain := rademacher_herm_tail_of_isRademacher hmeas hlaw hind
    (fun k => (hA k).neg) ht
  have hvar : (∑ k, (-(A k)) ^ 2) = ∑ k, (A k) ^ 2 := by
    exact Finset.sum_congr rfl fun k _ => neg_sq _
  rw [hvar] at hmain
  have hevent : {ω | lambdaMin (isHermitian_matsum Finset.univ
      (fun k => isHermitian_real_smul (hA k) (f k ω))) ≤ -t} =
      {ω | t ≤ lambdaMax (isHermitian_matsum Finset.univ
        (fun k => isHermitian_real_smul ((hA k).neg) (f k ω)))} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    rw [lambdaMin_series_eq_neg_lambdaMax_neg hA ω]
    constructor <;> intro h <;> linarith
  rw [hevent]
  exact hmain
/-- **Book Theorem 4.1.1, equation (4.1.5), Rademacher case.**
Source-faithful rectangular expectation counterpart of
`rademacher_series_rect_expectation`, with no pointwise support premise. -/
theorem rademacher_series_rect_expectation_of_isRademacher [Nonempty m] [Nonempty n]
    {B : ι → Matrix m n ℂ} {f : ι → Ω → ℝ}
    (hmeas : ∀ k, Measurable (f k)) (hlaw : ∀ k, IsRademacher (f k) μ)
    (hind : iIndepFun f μ) :
    ∫ ω, ‖∑ k, f k ω • B k‖ ∂μ ≤
      Real.sqrt (2 * max ‖∑ k, B k * (B k)ᴴ‖ ‖∑ k, (B k)ᴴ * B k‖ *
        Real.log (Fintype.card m + Fintype.card n)) := by
  let f' : ι → Ω → ℝ := fun k ω => rademacherRepresentative (f k ω)
  have hm' : ∀ k, Measurable (f' k) := fun k =>
    measurable_rademacherRepresentative.comp (hmeas k)
  have hl' : ∀ k, IsRademacher (f' k) μ := fun k =>
    isRademacher_rademacherRepresentative (hmeas k) (hlaw k)
  have hi' : iIndepFun f' μ := iIndepFun_rademacherRepresentative hmeas hlaw hind
  have hr' : ∀ k ω, f' k ω = 1 ∨ f' k ω = -1 := fun k ω =>
    rademacherRepresentative_range (f k ω)
  have hmain := rademacher_series_rect_expectation (μ := μ) (B := B)
    hm' hl' hr' hi'
  have hsum := rademacherRepresentative_matsum_ae hmeas hlaw B
  have hint : (fun ω => ‖∑ k, f' k ω • B k‖) =ᵐ[μ]
      fun ω => ‖∑ k, f k ω • B k‖ := hsum.fun_comp norm
  rwa [integral_congr_ae hint] at hmain

/-- **Book Theorem 4.1.1, equation (4.1.6), Rademacher case.**
Source-faithful rectangular tail counterpart of
`rademacher_series_rect_tail`, with no pointwise support premise. -/
theorem rademacher_series_rect_tail_of_isRademacher [Nonempty m] [Nonempty n]
    {B : ι → Matrix m n ℂ} {f : ι → Ω → ℝ}
    (hmeas : ∀ k, Measurable (f k)) (hlaw : ∀ k, IsRademacher (f k) μ)
    (hind : iIndepFun f μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ ‖∑ k, f k ω • B k‖} ≤
      ((Fintype.card m : ℝ) + Fintype.card n) *
        Real.exp (-(t ^ 2) /
          (2 * max ‖∑ k, B k * (B k)ᴴ‖ ‖∑ k, (B k)ᴴ * B k‖)) := by
  let f' : ι → Ω → ℝ := fun k ω => rademacherRepresentative (f k ω)
  have hm' : ∀ k, Measurable (f' k) := fun k =>
    measurable_rademacherRepresentative.comp (hmeas k)
  have hl' : ∀ k, IsRademacher (f' k) μ := fun k =>
    isRademacher_rademacherRepresentative (hmeas k) (hlaw k)
  have hi' : iIndepFun f' μ := iIndepFun_rademacherRepresentative hmeas hlaw hind
  have hr' : ∀ k ω, f' k ω = 1 ∨ f' k ω = -1 := fun k ω =>
    rademacherRepresentative_range (f k ω)
  have hmain := rademacher_series_rect_tail (μ := μ) (B := B)
    hm' hl' hr' hi' ht
  have hsum := rademacherRepresentative_matsum_ae hmeas hlaw B
  have hevent : ∀ᵐ ω ∂μ, ω ∈ {ω | t ≤ ‖∑ k, f' k ω • B k‖} ↔
      ω ∈ {ω | t ≤ ‖∑ k, f k ω • B k‖} := by
    filter_upwards [hsum] with ω hω
    rw [hω]
  have hevent' : {ω | t ≤ ‖∑ k, f' k ω • B k‖} =ᵐ[μ]
      {ω | t ≤ ‖∑ k, f k ω • B k‖} := hevent.mono fun _ h => propext h
  rwa [measureReal_congr hevent'] at hmain

/-- **Book equation (4.3.3).** Almost-sure-support sibling of `signed_expected_norm`. -/
theorem signed_expected_norm_of_isRademacher [Nonempty m] [Nonempty n]
    (b : Matrix m n ℝ) {f : m × n → Ω → ℝ}
    (hmeas : ∀ p, Measurable (f p)) (hlaw : ∀ p, IsRademacher (f p) μ)
    (hind : iIndepFun f μ) :
    ∫ ω, ‖∑ p : m × n, f p ω •
        (b p.1 p.2 • Matrix.single p.1 p.2 (1 : ℂ))‖ ∂μ ≤
      Real.sqrt (2 *
        max (Finset.univ.sup' Finset.univ_nonempty fun j => ∑ k, (b j k) ^ 2)
          (Finset.univ.sup' Finset.univ_nonempty fun k => ∑ j, (b j k) ^ 2) *
        Real.log ((Fintype.card m : ℝ) + Fintype.card n)) := by
  let C : m × n → Matrix m n ℂ := fun p =>
    b p.1 p.2 • Matrix.single p.1 p.2 (1 : ℂ)
  let f' : m × n → Ω → ℝ := fun p ω => rademacherRepresentative (f p ω)
  have hm' : ∀ p, Measurable (f' p) := fun p =>
    measurable_rademacherRepresentative.comp (hmeas p)
  have hl' : ∀ p, IsRademacher (f' p) μ := fun p =>
    isRademacher_rademacherRepresentative (hmeas p) (hlaw p)
  have hi' : iIndepFun f' μ := iIndepFun_rademacherRepresentative hmeas hlaw hind
  have hr' : ∀ p ω, f' p ω = 1 ∨ f' p ω = -1 := fun p ω =>
    rademacherRepresentative_range (f p ω)
  have hmain := signed_expected_norm (μ := μ) b hm' hl' hr' hi'
  have hsum := rademacherRepresentative_matsum_ae hmeas hlaw C
  have hint : (fun ω => ‖∑ p, f' p ω • C p‖) =ᵐ[μ]
      fun ω => ‖∑ p, f p ω • C p‖ := hsum.fun_comp norm
  rw [integral_congr_ae hint] at hmain
  simpa only [C] using hmain

/-- **Book §4.5 rounding display.** Almost-sure-support sibling of
`maxqp_rounding_bound`. -/
theorem maxqp_rounding_bound_of_isRademacher [Nonempty m] [Nonempty n]
    {B : ι → Matrix m n ℂ} {α : ℝ} (hα : 0 ≤ α)
    (hc1 : (∑ k, B k * (B k)ᴴ) ≤ 1) (hc2 : (∑ k, (B k)ᴴ * B k) ≤ 1)
    {f : ι → Ω → ℝ} (hmeas : ∀ k, Measurable (f k))
    (hlaw : ∀ k, IsRademacher (f k) μ) (hind : iIndepFun f μ) :
    ∫ ω, ‖∑ k, f k ω • (α • B k)‖ ∂μ ≤
      α * Real.sqrt (2 * Real.log ((Fintype.card m : ℝ) + Fintype.card n)) := by
  let f' : ι → Ω → ℝ := fun k ω => rademacherRepresentative (f k ω)
  have hm' : ∀ k, Measurable (f' k) := fun k =>
    measurable_rademacherRepresentative.comp (hmeas k)
  have hl' : ∀ k, IsRademacher (f' k) μ := fun k =>
    isRademacher_rademacherRepresentative (hmeas k) (hlaw k)
  have hi' : iIndepFun f' μ := iIndepFun_rademacherRepresentative hmeas hlaw hind
  have hr' : ∀ k ω, f' k ω = 1 ∨ f' k ω = -1 := fun k ω =>
    rademacherRepresentative_range (f k ω)
  have hmain := maxqp_rounding_bound (μ := μ) hα hc1 hc2 hm' hl' hr' hi'
  have hsum := rademacherRepresentative_matsum_ae hmeas hlaw (fun k => α • B k)
  have hint : (fun ω => ‖∑ k, f' k ω • (α • B k)‖) =ᵐ[μ]
      fun ω => ‖∑ k, f k ω • (α • B k)‖ := hsum.fun_comp norm
  rwa [integral_congr_ae hint] at hmain

/-- **Book §4.5 rounding conclusion.** Almost-sure-support sibling of
`maxqp_rounding_bound_one`. -/
theorem maxqp_rounding_bound_one_of_isRademacher [Nonempty m] [Nonempty n]
    {B : ι → Matrix m n ℂ}
    (hc1 : (∑ k, B k * (B k)ᴴ) ≤ 1) (hc2 : (∑ k, (B k)ᴴ * B k) ≤ 1)
    {f : ι → Ω → ℝ} (hmeas : ∀ k, Measurable (f k))
    (hlaw : ∀ k, IsRademacher (f k) μ) (hind : iIndepFun f μ) :
    ∫ ω, ‖∑ k, f k ω •
        ((Real.sqrt (2 * Real.log ((Fintype.card m : ℝ) + Fintype.card n)))⁻¹ •
          B k)‖ ∂μ ≤ 1 := by
  let f' : ι → Ω → ℝ := fun k ω => rademacherRepresentative (f k ω)
  have hm' : ∀ k, Measurable (f' k) := fun k =>
    measurable_rademacherRepresentative.comp (hmeas k)
  have hl' : ∀ k, IsRademacher (f' k) μ := fun k =>
    isRademacher_rademacherRepresentative (hmeas k) (hlaw k)
  have hi' : iIndepFun f' μ := iIndepFun_rademacherRepresentative hmeas hlaw hind
  have hr' : ∀ k ω, f' k ω = 1 ∨ f' k ω = -1 := fun k ω =>
    rademacherRepresentative_range (f k ω)
  have hmain := maxqp_rounding_bound_one (μ := μ) hc1 hc2 hm' hl' hr' hi'
  have hsum := rademacherRepresentative_matsum_ae hmeas hlaw (fun k =>
    (Real.sqrt (2 * Real.log ((Fintype.card m : ℝ) + Fintype.card n)))⁻¹ • B k)
  have hint : (fun ω => ‖∑ k, f' k ω •
      ((Real.sqrt (2 * Real.log ((Fintype.card m : ℝ) + Fintype.card n)))⁻¹ • B k)‖) =ᵐ[μ]
      fun ω => ‖∑ k, f k ω •
        ((Real.sqrt (2 * Real.log ((Fintype.card m : ℝ) + Fintype.card n)))⁻¹ • B k)‖ :=
    hsum.fun_comp norm
  rwa [integral_congr_ae hint] at hmain

end RademacherSupportWrappers

end MatrixConcentration
