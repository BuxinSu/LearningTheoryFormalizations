import MatrixConcentration.Chapter2_MatrixFunctionsAndProbabilityWithMatrices
import MatrixConcentration.Chapter8_ProofOfLiebsTheorem
import MatrixConcentration.Appendix_GoldenThompson
import Mathlib.Probability.Moments.Basic
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Continuous

/-!
# Chapter 3: The matrix Laplace transform method

This consolidated chapter contains:

* **Book §3.1:** matrix moment- and cumulant-generating functions;
* **Book §3.2:** matrix Laplace-transform tail and expectation bounds;
* **Book §3.3:** failure of naive matrix mgf multiplication and Golden–Thompson;
* **Book §3.4:** Lieb's concavity theorem and its probabilistic corollaries;
* **Book §§3.5–3.6:** subadditivity of matrix cgfs and the master bounds.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-!
# Matrix moments and cumulants (Tropp §3.1)

* `matrixMgf`, `matrixCgf` — **Book Definition 3.1.1**, eq. (3.1.1)
  (C3-01): the matrix moment generating function `M_X(θ) = 𝔼 e^{θX}` and the matrix
  cumulant generating function `Ξ_X(θ) = log 𝔼 e^{θX}`.  The book's caveat "the
  expectations may not exist for all values of θ" is handled as in §2.2: `expectation`
  is total (entrywise Bochner integrals) and every substantive statement carries
  explicit boundedness/integrability hypotheses — the standing regularity convention
  of §2.2.1 ("all random variables are bounded");
* `isHermitian_matrixMgf`, `posDef_matrixMgf` — the hidden well-definedness
  obligations of Definition 3.1.1 (C3-02): the mgf of a bounded random Hermitian
  matrix is Hermitian and **positive definite**, so its logarithm (the cgf) is a
  well-defined standard matrix function (§2.1.12);
* `matrixMgf_hasSum_moments` — the first unnumbered display of §3.1 (C3-04):
  `M_X(θ) = I + Σ_{q≥1} (θ^q/q!) 𝔼X^q`, the **matrix moments** expansion, as a
  genuine `HasSum` over `q : ℕ` (the `q = 0` term being `I = 𝔼X⁰`);
* measurability/integrability/norm toolkit (C3-03, C3-24) and the Bochner-integral
  bridge `expectation_eq_integral` (also used by the Jensen argument of §3.4).

The cgf *formal* power series and the matrix cumulants `Ψ_q` (C3-05) are **not**
formalized: the book presents them as formal power series, says "this discussion is
not important for subsequent developments", and never uses the notation again
(cross-book pass); see the inventory and SI-C3-1.
-/

namespace MatrixConcentration

open Matrix Finset MeasureTheory
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {A : Matrix n n ℂ} {X : Ω → Matrix n n ℂ}

section NormToolkit

/-- Lean implementation helper: every entry of a matrix is dominated by its spectral
norm (`|a_{ij}| = |e_i* A e_j| ≤ ‖A‖`). -/
lemma norm_entry_le_l2_opNorm (A : Matrix n n ℂ) (i j : n) : ‖A i j‖ ≤ ‖A‖ := by
  have h := norm_dotProduct_mulVec_le A (Pi.single i 1) (Pi.single j 1)
  have h1 : star (Pi.single i (1 : ℂ)) ⬝ᵥ (A *ᵥ Pi.single j 1) = A i j := by
    rw [Matrix.mulVec_single]
    show (∑ k, star ((Pi.single i (1 : ℂ) : n → ℂ) k) * (A k j * 1)) = A i j
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      simp [Pi.single_apply, hb]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hsingle : ∀ k : n, l2norm (Pi.single k (1 : ℂ)) = 1 := by
    intro k
    rw [l2norm_eq_sqrt_sum]
    have hs : (∑ l, ‖(Pi.single k (1 : ℂ) : n → ℂ) l‖ ^ 2) = 1 := by
      rw [Finset.sum_eq_single k]
      · simp
      · intro b _ hb
        simp [Pi.single_apply, hb]
      · intro h
        exact absurd (Finset.mem_univ k) h
    rw [hs, Real.sqrt_one]
  rw [h1, hsingle i, hsingle j] at h
  simpa using h

/-- Lean implementation helper: the eigenvalues of a Hermitian matrix are bounded in
absolute value by the spectral norm (a reading of eq. (2.1.22)). -/
lemma abs_eigenvalues_le_l2_opNorm (hA : A.IsHermitian) (i : n) :
    |hA.eigenvalues i| ≤ ‖A‖ := by
  haveI : Nonempty n := ⟨i⟩
  rw [l2_opNorm_eq_max_lambda hA]
  rcases abs_cases (hA.eigenvalues i) with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]
    exact le_max_of_le_left (eigenvalues_le_lambdaMax hA i)
  · rw [h]
    exact le_max_of_le_right (neg_le_neg (lambdaMin_le_eigenvalues hA i))

/-- Lean implementation helper: `cfc` of a constant function is the corresponding
multiple of the identity. -/
lemma cfc_const_eq_smul_one (hA : A.IsHermitian) (c : ℝ) :
    cfc (fun _ : ℝ => c) A = (c : ℂ) • (1 : Matrix n n ℂ) := by
  rw [cfc_eq_book_formula hA (fun _ => c)]
  have h1 : diagonal (RCLike.ofReal ∘ (fun _ : ℝ => c) ∘ hA.eigenvalues) =
      (c : ℂ) • (1 : Matrix n n ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.diagonal_apply_eq]
    · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  rw [h1, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  have h2 := Matrix.mem_unitaryGroup_iff.mp hA.eigenvectorUnitary.2
  rw [show (hA.eigenvectorUnitary : Matrix n n ℂ) *
      (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ = 1 by
    simpa [star_eq_conjTranspose] using h2]

/-- **Book Corollary 3.4.2**, implicit Loewner bounds used in its proof (C3-24):
`e^{-R}·I ≼ e^A ≼ e^R·I` whenever `‖A‖ ≤ R`.  Implicit source obligation (used for
the well-definedness of the cgf and for the Jensen step of Corollary 3.4.2). -/
lemma exp_loewner_bounds (hA : A.IsHermitian) {R : ℝ} (hR : ‖A‖ ≤ R) :
    ((Real.exp (-R) : ℂ) • (1 : Matrix n n ℂ) ≤ NormedSpace.exp A) ∧
      (NormedSpace.exp A ≤ (Real.exp R : ℂ) • (1 : Matrix n n ℂ)) := by
  have hspec : ∀ i, hA.eigenvalues i ∈ Set.Icc (-R) R := fun i =>
    abs_le.mp ((abs_eigenvalues_le_l2_opNorm hA i).trans hR)
  constructor
  · rw [matrixExp_eq_cfc hA, ← cfc_const_eq_smul_one hA (Real.exp (-R))]
    exact transfer_rule hA hspec fun a ha => Real.exp_le_exp.mpr ha.1
  · rw [matrixExp_eq_cfc hA, ← cfc_const_eq_smul_one hA (Real.exp R)]
    exact transfer_rule hA hspec fun a ha => Real.exp_le_exp.mpr ha.2

/-- Lean implementation helper: spectral norm bound for the exponential of a
Hermitian matrix, `‖e^A‖ ≤ e^{‖A‖}`. -/
lemma l2_opNorm_exp_le (hA : A.IsHermitian) : ‖NormedSpace.exp A‖ ≤ Real.exp ‖A‖ := by
  rcases isEmpty_or_nonempty n with h | h
  · have h0 : NormedSpace.exp A = (0 : Matrix n n ℂ) := by
      ext i j
      exact h.elim i
    rw [h0]
    simpa using (Real.exp_pos ‖A‖).le
  · have hE : (NormedSpace.exp A).IsHermitian := isHermitian_exp hA
    rw [l2_opNorm_eq_max_lambda hE]
    have hbound : ∀ i, |hE.eigenvalues i| ≤ Real.exp ‖A‖ := by
      intro i
      have hdecomp : NormedSpace.exp A = (hA.eigenvectorUnitary : Matrix n n ℂ) *
          diagonal (RCLike.ofReal ∘ (Real.exp ∘ hA.eigenvalues)) *
          (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
        rw [matrixExp_eq_cfc hA]
        exact cfc_eq_book_formula hA Real.exp
      have hmult := eigenvalues_multiset_unique hE hA.eigenvectorUnitary.2 hdecomp
      have hmem : hE.eigenvalues i ∈
          Multiset.map (Real.exp ∘ hA.eigenvalues) Finset.univ.val := by
        rw [hmult]
        exact Multiset.mem_map.mpr ⟨i, Finset.mem_univ_val i, rfl⟩
      obtain ⟨j, _, hj⟩ := Multiset.mem_map.mp hmem
      rw [← hj]
      have h3 := abs_eigenvalues_le_l2_opNorm hA j
      show |Real.exp (hA.eigenvalues j)| ≤ Real.exp ‖A‖
      rw [abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans h3)
    apply max_le
    · obtain ⟨i, hi⟩ := exists_eigenvalues_eq_lambdaMax hE
      rw [← hi]
      exact (le_abs_self _).trans (hbound i)
    · obtain ⟨i, hi⟩ := exists_eigenvalues_eq_lambdaMin hE
      rw [← hi]
      exact (neg_le_abs _).trans (hbound i)

/-- Lean implementation helper: power-norm bound `‖A^q‖ ≤ ‖1‖·‖A‖^q` (stated with the
`‖1‖` factor so that the empty-index-type case needs no special treatment). -/
lemma l2_opNorm_pow_le (A : Matrix n n ℂ) (q : ℕ) :
    ‖A ^ q‖ ≤ ‖(1 : Matrix n n ℂ)‖ * ‖A‖ ^ q := by
  induction q with
  | zero => simp
  | succ m ih =>
    calc ‖A ^ (m + 1)‖ = ‖A ^ m * A‖ := by rw [pow_succ]
    _ ≤ ‖A ^ m‖ * ‖A‖ := norm_mul_le _ _
    _ ≤ (‖(1 : Matrix n n ℂ)‖ * ‖A‖ ^ m) * ‖A‖ :=
        mul_le_mul_of_nonneg_right ih (norm_nonneg _)
    _ = ‖(1 : Matrix n n ℂ)‖ * ‖A‖ ^ (m + 1) := by ring

end NormToolkit

section Measurability

/-- Lean implementation helper: products of measurable random matrices are measurable
(entrywise; local variant of the Chapter-1 helper to keep the import graph layered). -/
lemma measurable_matmul {Y Z : Ω → Matrix n n ℂ} (hY : Measurable Y)
    (hZ : Measurable Z) : Measurable fun ω => Y ω * Z ω := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  have h : (fun ω => (Y ω * Z ω) i j) =
      fun ω => ∑ k, Y ω i k * Z ω k j := by
    funext ω
    rw [Matrix.mul_apply]
  rw [show (fun ω => (Y ω * Z ω : Matrix n n ℂ) i j) =
      fun ω => ∑ k, Y ω i k * Z ω k j from h]
  exact Finset.measurable_sum _ fun k _ =>
    ((measurable_entry i k).comp hY).mul ((measurable_entry k j).comp hZ)

/-- Lean implementation helper: powers of a measurable random matrix are measurable. -/
lemma measurable_matpow (hX : Measurable X) (q : ℕ) :
    Measurable fun ω => X ω ^ q := by
  induction q with
  | zero => simpa using measurable_const
  | succ m ih =>
    have h : (fun ω => X ω ^ (m + 1)) = fun ω => (X ω ^ m) * (X ω) := by
      funext ω
      rw [pow_succ]
    rw [h]
    exact measurable_matmul ih hX

/-- Lean implementation helper: complex scalar multiples of measurable random
matrices are measurable (entrywise, avoiding `MeasurableSMul` instances). -/
lemma measurable_const_smul_matrix {α : Type*} [MeasurableSpace α] (c : ℂ)
    {Y : α → Matrix n n ℂ} (hY : Measurable Y) :
    Measurable fun a => c • Y a := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  show Measurable fun a => c * Y a i j
  exact measurable_const.mul ((measurable_entry i j).comp hY)

/-- Lean implementation helper: real scalar multiples of Hermitian matrices are
Hermitian (local variant of the Chapter-1 helper). -/
lemma isHermitian_real_smul (hA : A.IsHermitian) (r : ℝ) : (r • A).IsHermitian := by
  ext i j
  rw [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.smul_apply, star_smul,
    star_trivial]
  congr 1
  rw [← Matrix.conjTranspose_apply, hA]

/-- Lean implementation helper: the real-scalar action on complex matrices is the
complex action of the cast (entrywise `Complex.real_smul`). -/
lemma real_smul_eq_complex_smul (r : ℝ) (M : Matrix n n ℂ) :
    r • M = (r : ℂ) • M := by
  ext i j
  show r • M i j = (r : ℂ) * M i j
  rw [Complex.real_smul]

/-- Lean implementation helper (C3-03): the matrix exponential is measurable (as the
pointwise limit of its partial sums, which are polynomial and hence measurable). -/
lemma measurable_matrixExp :
    Measurable (NormedSpace.exp : Matrix n n ℂ → Matrix n n ℂ) := by
  have hpow : ∀ q : ℕ, Measurable fun M : Matrix n n ℂ => M ^ q := by
    intro q
    induction q with
    | zero => simpa using measurable_const
    | succ m ih =>
      have h : (fun M : Matrix n n ℂ => M ^ (m + 1)) =
          fun M => (M ^ m) * M := by
        funext M
        rw [pow_succ]
      rw [h]
      exact measurable_matmul ih measurable_id
  refine measurable_of_tendsto_metrizable
    (f := fun N (M : Matrix n n ℂ) =>
      ∑ q ∈ Finset.range N, ((q.factorial : ℂ))⁻¹ • M ^ q)
    (fun N => Finset.measurable_sum _ fun q _ =>
      measurable_const_smul_matrix _ (hpow q))
    ?_
  rw [tendsto_pi_nhds]
  intro M
  exact (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) M).tendsto_sum_nat

/-- Lean implementation helper (C3-03): the matrix exponential of a measurable random
matrix is measurable. -/
lemma measurable_matrixExp_comp (hX : Measurable X) :
    Measurable fun ω => NormedSpace.exp (X ω) :=
  measurable_matrixExp.comp hX

/-- Lean implementation helper (C3-03): the matrix exponential of a bounded random
Hermitian matrix is entrywise integrable (standing convention §2.2.1). -/
lemma mintegrable_matrixExp_of_bound [IsFiniteMeasure μ] (hX : Measurable X)
    (hHerm : ∀ ω, (X ω).IsHermitian) {R : ℝ} (hR : ∀ ω, ‖X ω‖ ≤ R) :
    MIntegrable (fun ω => NormedSpace.exp (X ω)) μ := by
  refine MIntegrable.of_bound (measurable_matrixExp_comp hX) (Real.exp R) ?_
  refine Filter.Eventually.of_forall fun ω i j => ?_
  calc ‖NormedSpace.exp (X ω) i j‖ ≤ ‖NormedSpace.exp (X ω)‖ :=
        norm_entry_le_l2_opNorm _ i j
  _ ≤ Real.exp ‖X ω‖ := l2_opNorm_exp_le (hHerm ω)
  _ ≤ Real.exp R := Real.exp_le_exp.mpr (hR ω)

/-- Lean implementation helper: entry evaluation as a continuous `ℂ`-linear map
(for exchanging Bochner integrals and entries). -/
noncomputable def entryCLM (i j : n) : Matrix n n ℂ →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

@[simp] lemma entryCLM_apply (i j : n) (M : Matrix n n ℂ) : entryCLM i j M = M i j :=
  rfl

/-- **Book §2.2.4 — Mathlib correspondence:** the entrywise expectation agrees with the
Bochner integral of the matrix-valued map (with respect to the spectral-norm Banach
structure; the topology is the entrywise one, §2.1.4).  Used for the Jensen argument
of §3.4 and the moment expansion of §3.1. -/
lemma expectation_eq_integral {Z : Ω → Matrix n n ℂ}
    (hZ : Integrable Z μ) : expectation μ Z = ∫ ω, Z ω ∂μ := by
  ext i j
  rw [expectation_apply]
  exact ContinuousLinearMap.integral_comp_comm (entryCLM i j) hZ

/-- Lean implementation helper: a measurable, uniformly norm-bounded random matrix is
Bochner integrable. -/
lemma integrable_of_norm_bound [IsFiniteMeasure μ] {Z : Ω → Matrix n n ℂ}
    (hZm : Measurable Z) {C : ℝ} (hC : ∀ ω, ‖Z ω‖ ≤ C) : Integrable Z μ :=
  Integrable.of_bound hZm.aestronglyMeasurable C
    (Filter.Eventually.of_forall hC)

end Measurability

section Definitions

variable (μ)

/-- **Book Definition 3.1.1**, eq. (3.1.1) (§3.1, p. 32): the
matrix moment generating function `M_X(θ) = 𝔼 e^{θX}`.  Explicit source declaration.
The expectation is entrywise (§2.2.4); statements about the mgf carry the
boundedness/integrability hypotheses of the standing convention §2.2.1 (the book:
"the expectations may not exist for all values of θ"). -/
noncomputable def matrixMgf (X : Ω → Matrix n n ℂ) (θ : ℝ) : Matrix n n ℂ :=
  expectation μ fun ω => NormedSpace.exp (θ • X ω)

/-- **Book Definition 3.1.1**, eq. (3.1.1): the matrix cumulant generating function
`Ξ_X(θ) = log 𝔼 e^{θX}`.  Explicit source declaration; `log` is the standard matrix
function of §2.1.12 (`CFC.log`), well-defined on the mgf by `posDef_matrixMgf`. -/
noncomputable def matrixCgf (X : Ω → Matrix n n ℂ) (θ : ℝ) : Matrix n n ℂ :=
  CFC.log (matrixMgf μ X θ)

variable {μ}

/-- Lean implementation helper: unfold the matrix moment-generating function. -/
lemma matrixMgf_def (X : Ω → Matrix n n ℂ) (θ : ℝ) :
    matrixMgf μ X θ = expectation μ (fun ω => NormedSpace.exp (θ • X ω)) := rfl

/-- **Book Definition 3.1.1**, hidden well-definedness obligation (C3-02): the matrix mgf of
a random Hermitian matrix is Hermitian.  Implicit source declaration. -/
lemma isHermitian_matrixMgf (hHerm : ∀ ω, (X ω).IsHermitian) (θ : ℝ) :
    (matrixMgf μ X θ).IsHermitian :=
  isHermitian_expectation (Filter.Eventually.of_forall fun ω =>
    isHermitian_exp (isHermitian_real_smul (hHerm ω) θ))

/-- Lean implementation helper: norm bound for `θ • X`. -/
lemma norm_smul_le_of_bound {R θ : ℝ} (hR : ∀ ω, ‖X ω‖ ≤ R) (ω : Ω) :
    ‖θ • X ω‖ ≤ |θ| * R := by
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hR ω) (abs_nonneg θ)

/-- **Book Definition 3.1.1**, hidden well-definedness obligation (C3-02): for a bounded
random Hermitian matrix, the matrix mgf is **positive definite**, so the matrix cgf
`log M_X(θ)` is a well-defined standard matrix function.  In fact
`e^{-|θ|R}·I ≼ M_X(θ)`.  Implicit source declaration.  The statement also
holds for the empty index type, where the matrix order is vacuous. -/
theorem smul_one_le_matrixMgf [IsProbabilityMeasure μ] (hX : Measurable X)
    (hHerm : ∀ ω, (X ω).IsHermitian) {R : ℝ} (hR : ∀ ω, ‖X ω‖ ≤ R) (θ : ℝ) :
    (Real.exp (-(|θ| * R)) : ℂ) • (1 : Matrix n n ℂ) ≤ matrixMgf μ X θ := by
  have hHermθ : ∀ ω, (θ • X ω).IsHermitian := fun ω =>
    isHermitian_real_smul (hHerm ω) θ
  have hint : MIntegrable (fun ω => NormedSpace.exp (θ • X ω)) μ :=
    mintegrable_matrixExp_of_bound (hX.const_smul θ) hHermθ (norm_smul_le_of_bound hR)
  have hconst : MIntegrable (fun _ : Ω =>
      (Real.exp (-(|θ| * R)) : ℂ) • (1 : Matrix n n ℂ)) μ := fun i j =>
    MeasureTheory.integrable_const _
  have hmono := expectation_loewner_mono hconst hint
    (Filter.Eventually.of_forall fun ω =>
      (exp_loewner_bounds (hHermθ ω) (norm_smul_le_of_bound hR ω)).1)
  rwa [expectation_const (μ := μ)] at hmono

/-- **Book Definition 3.1.1**, positive definiteness of the mgf needed for the cgf. -/
theorem posDef_matrixMgf [IsProbabilityMeasure μ] [Nonempty n] (hX : Measurable X)
    (hHerm : ∀ ω, (X ω).IsHermitian) {R : ℝ} (hR : ∀ ω, ‖X ω‖ ≤ R) (θ : ℝ) :
    (matrixMgf μ X θ).PosDef := by
  have hmono := smul_one_le_matrixMgf (μ := μ) hX hHerm hR θ
  have hpd : ((Real.exp (-(|θ| * R)) : ℂ) • (1 : Matrix n n ℂ)).PosDef :=
    Matrix.PosDef.one.smul (Complex.zero_lt_real.mpr (Real.exp_pos _))
  have hdiff := Matrix.le_iff.mp hmono
  have hsum := hpd.add_posSemidef hdiff
  rwa [add_sub_cancel] at hsum

end Definitions

section MomentSeries

/-- **Book §3.1, first display** (C3-04): the matrix-moments expansion of the matrix
mgf, `M_X(θ) = I + Σ_{q≥1} (θ^q/q!)·𝔼X^q`, formalized as a `HasSum` over `q : ℕ` (the
`q = 0` term is `I = 𝔼X⁰`).  The book calls the display formal; under the standing
boundedness convention it is a genuine convergent identity.  The coefficients `𝔼X^q`
are the book's **matrix moments**. Explicit (unnumbered) source display.

**Author note.** The book treats the series formally; Lean proves convergence under
the standing boundedness hypotheses. -/
theorem matrixMgf_hasSum_moments [IsProbabilityMeasure μ] (hX : Measurable X)
    (hHerm : ∀ ω, (X ω).IsHermitian) {R : ℝ} (hR : ∀ ω, ‖X ω‖ ≤ R) (θ : ℝ) :
    HasSum (fun q : ℕ => ((θ ^ q / q.factorial : ℝ) : ℂ) •
      expectation μ (fun ω => X ω ^ q)) (matrixMgf μ X θ) := by
  classical
  haveI hΩ : Nonempty Ω := by
    by_contra h
    have h1 : μ Set.univ = 1 := MeasureTheory.measure_univ (μ := μ)
    rw [Set.univ_eq_empty_iff.mpr (not_nonempty_iff.mp h), measure_empty] at h1
    exact zero_ne_one h1
  have h0R : (0 : ℝ) ≤ R := le_trans (norm_nonneg _) (hR (Classical.arbitrary Ω))
  set C : ℝ := ‖(1 : Matrix n n ℂ)‖ with hC
  have hC0 : 0 ≤ C := norm_nonneg _
  have hpow_meas : ∀ q : ℕ, Measurable fun ω => X ω ^ q :=
    measurable_matpow hX
  have hFnorm : ∀ (q : ℕ) (ω : Ω),
      ‖((θ ^ q / q.factorial : ℝ) : ℂ) • (X ω ^ q)‖ ≤
        C * ((|θ| * R) ^ q / q.factorial) := by
    intro q ω
    rw [norm_smul]
    have h1 : ‖((θ ^ q / q.factorial : ℝ) : ℂ)‖ = |θ| ^ q / q.factorial := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_pow]
      congr 1
      exact abs_of_nonneg (by positivity)
    rw [h1]
    have h2 : ‖X ω ^ q‖ ≤ C * R ^ q :=
      (l2_opNorm_pow_le (X ω) q).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hR ω) q) hC0)
    calc |θ| ^ q / q.factorial * ‖X ω ^ q‖
        ≤ |θ| ^ q / q.factorial * (C * R ^ q) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = C * ((|θ| * R) ^ q / q.factorial) := by
        rw [mul_pow]
        ring
  have hsummable : Summable fun q : ℕ => C * ((|θ| * R) ^ q / q.factorial) :=
    (Real.summable_pow_div_factorial (|θ| * R)).mul_left C
  have hptwise : ∀ ω : Ω, HasSum
      (fun q : ℕ => ((θ ^ q / q.factorial : ℝ) : ℂ) • (X ω ^ q))
      (NormedSpace.exp (θ • X ω)) := by
    intro ω
    have h1 := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (θ • X ω)
    have h2 : (fun q : ℕ => ((q.factorial : ℂ))⁻¹ • (θ • X ω) ^ q) =
        fun q : ℕ => ((θ ^ q / q.factorial : ℝ) : ℂ) • (X ω ^ q) := by
      funext q
      rw [smul_pow, real_smul_eq_complex_smul, smul_smul]
      congr 1
      push_cast
      rw [div_eq_mul_inv, mul_comm]
    rwa [h2] at h1
  have hswap := MeasureTheory.hasSum_integral_of_dominated_convergence
    (F := fun (q : ℕ) (ω : Ω) => ((θ ^ q / q.factorial : ℝ) : ℂ) • (X ω ^ q))
    (f := fun ω => NormedSpace.exp (θ • X ω)) (μ := μ)
    (fun q _ => C * ((|θ| * R) ^ q / q.factorial))
    (fun q => (measurable_const_smul_matrix _ (hpow_meas q)).aestronglyMeasurable)
    (fun q => Filter.Eventually.of_forall fun ω => hFnorm q ω)
    (Filter.Eventually.of_forall fun _ => hsummable)
    (MeasureTheory.integrable_const _)
    (Filter.Eventually.of_forall hptwise)
  -- convert the Bochner integrals back to entrywise expectations
  have hbridge : ∀ q : ℕ,
      (∫ ω, ((θ ^ q / q.factorial : ℝ) : ℂ) • (X ω ^ q) ∂μ) =
        ((θ ^ q / q.factorial : ℝ) : ℂ) • expectation μ (fun ω => X ω ^ q) := by
    intro q
    have hint : Integrable (fun ω => X ω ^ q) μ :=
      integrable_of_norm_bound (hpow_meas q)
        (fun ω => (l2_opNorm_pow_le (X ω) q).trans
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hR ω) q) hC0))
    rw [MeasureTheory.integral_smul, expectation_eq_integral hint]
  have hbridge2 : (∫ ω, NormedSpace.exp (θ • X ω) ∂μ) = matrixMgf μ X θ := by
    rw [matrixMgf_def]
    refine (expectation_eq_integral ?_).symm
    refine integrable_of_norm_bound (C := Real.exp (|θ| * R))
      (measurable_matrixExp_comp (hX.const_smul θ)) fun ω => ?_
    calc ‖NormedSpace.exp (θ • X ω)‖
        ≤ Real.exp ‖θ • X ω‖ := l2_opNorm_exp_le (isHermitian_real_smul (hHerm ω) θ)
    _ ≤ Real.exp (|θ| * R) := Real.exp_le_exp.mpr (norm_smul_le_of_bound hR ω)
  rw [← hbridge2]
  have hfinal : (fun q : ℕ => ((θ ^ q / q.factorial : ℝ) : ℂ) •
      expectation μ (fun ω => X ω ^ q)) =
      fun q => ∫ ω, ((θ ^ q / q.factorial : ℝ) : ℂ) • (X ω ^ q) ∂μ :=
    funext fun q => (hbridge q).symm
  rw [hfinal]
  exact hswap

end MomentSeries

end MatrixConcentration


set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# The matrix Laplace transform method (Tropp §3.2)

* `matrix_laplace_tail_upper`/`matrix_laplace_tail_lower` — **Book Proposition 3.2.1**,
  eqs. (3.2.1)/(3.2.2) (C3-06), in the pointwise-in-`θ` form used by
  every later chapter; the exact infimum forms of the source display are
  `matrix_laplace_tail_upper_inf`/`matrix_laplace_tail_lower_inf`;
* `matrix_laplace_expectation_upper`/`matrix_laplace_expectation_lower` —
  **Book Proposition 3.2.2**, eqs. (3.2.4)/(3.2.5) (C3-11), with the
  exact inf/sup forms `_inf`/`_sup`;
* `exp_lambdaMax_le_trace_exp` and `lambdaMax_exp` — **Book eq. (3.2.3)** (C3-07):
  `e^{λ_max(A)} = λ_max(e^A) ≤ tr e^A`;
* `lambdaMax_smul_nonpos` — the silent combination of (2.1.4) and (2.1.5) used for
  the `λ_min` bounds (C3-08): `λ_max(θY) = θ·λ_min(Y)` for `θ ≤ 0`;
* `measurable_lambdaMax`, `integrable_lambdaMax` and the λ_min analogues (C3-09):
  the hidden measurability/integrability obligations, via the shift identity
  `λ_max(A) = ‖A + R·I‖ − R` (`lambdaMax_eq_norm_shift`) and the continuity of the
  spectral norm (C2-59 toolkit);
* `measurable_trace_exp_re`, `integrable_trace_exp_re`, `trace_exp_re_pos` (C3-10);
* `integral_log_le_log_integral` (C3-12): the scalar Jensen instance for the concave
  logarithm invoked by the source's proof of Proposition 3.2.2 (citing (2.2.2)),
  proved by the tangent-line argument.

Dimensional convention: the statements require `[Nonempty n]` (`d ≥ 1`); for `d = 0`
the trace is `0` and the displays are degenerate (cf. SI-5, SI-C3-4).
-/

namespace MatrixConcentration

open Matrix Finset MeasureTheory
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {A : Matrix n n ℂ} {Y : Ω → Matrix n n ℂ}

section LambdaMaxToolkit

/-- Lean implementation helper: `|⟨u, Au⟩| ≤ ‖A‖·‖u‖²`. -/
lemma abs_rayleigh_le (A : Matrix n n ℂ) (u : n → ℂ) :
    |rayleigh A u| ≤ ‖A‖ * l2norm u ^ 2 := by
  have h1 : |rayleigh A u| ≤ ‖star u ⬝ᵥ (A *ᵥ u)‖ := by
    rw [show rayleigh A u = (star u ⬝ᵥ (A *ᵥ u)).re from rfl]
    exact Complex.abs_re_le_norm _
  refine h1.trans ?_
  have h2 := norm_dotProduct_mulVec_le A u u
  calc ‖star u ⬝ᵥ (A *ᵥ u)‖ ≤ ‖A‖ * l2norm u * l2norm u := h2
  _ = ‖A‖ * l2norm u ^ 2 := by ring

/-- Lean implementation helper: `|λ_max(A)| ≤ ‖A‖` for Hermitian `A`. -/
lemma abs_lambdaMax_le [Nonempty n] (hA : A.IsHermitian) : |lambdaMax hA| ≤ ‖A‖ := by
  obtain ⟨i, hi⟩ := exists_eigenvalues_eq_lambdaMax hA
  rw [← hi]
  exact abs_eigenvalues_le_l2_opNorm hA i

/-- Lean implementation helper: `|λ_min(A)| ≤ ‖A‖` for Hermitian `A`. -/
lemma abs_lambdaMin_le [Nonempty n] (hA : A.IsHermitian) : |lambdaMin hA| ≤ ‖A‖ := by
  obtain ⟨i, hi⟩ := exists_eigenvalues_eq_lambdaMin hA
  rw [← hi]
  exact abs_eigenvalues_le_l2_opNorm hA i

/-- Lean implementation helper: `A + c·I` is Hermitian for Hermitian `A`, real `c`. -/
lemma isHermitian_add_smul_one (hA : A.IsHermitian) (c : ℝ) :
    (A + (c : ℂ) • (1 : Matrix n n ℂ)).IsHermitian := by
  refine hA.add ?_
  ext i j
  rw [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.smul_apply]
  by_cases hij : i = j
  · subst hij
    simp [Matrix.one_apply_eq, Complex.conj_ofReal]
  · simp [Matrix.one_apply_ne hij, Matrix.one_apply_ne (Ne.symm hij)]

/-- Lean implementation helper: the Rayleigh value of `A + c·I`. -/
lemma rayleigh_add_smul_one (A : Matrix n n ℂ) (c : ℝ) (u : n → ℂ) :
    rayleigh (A + (c : ℂ) • (1 : Matrix n n ℂ)) u =
      rayleigh A u + c * l2norm u ^ 2 := by
  show (star u ⬝ᵥ ((A + (c : ℂ) • (1 : Matrix n n ℂ)) *ᵥ u)).re = _
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_add]
  rw [Complex.add_re]
  congr 1
  have h1 : star u ⬝ᵥ (c : ℂ) • u = (c : ℂ) * (star u ⬝ᵥ u) := by
    rw [dotProduct_smul]
    rfl
  rw [h1, dotProduct_star_self_eq]
  rw [show ((c : ℂ) * ((l2norm u ^ 2 : ℝ) : ℂ)).re =
    ((c * l2norm u ^ 2 : ℝ) : ℂ).re by push_cast; ring_nf]
  exact Complex.ofReal_re _

/-- Lean implementation helper: eigenvalue shift, `λ_max(A + c·I) = λ_max(A) + c`. -/
lemma lambdaMax_add_smul_one [Nonempty n] (hA : A.IsHermitian) (c : ℝ) :
    lambdaMax (isHermitian_add_smul_one hA c) = lambdaMax hA + c := by
  refine le_antisymm ?_ ?_
  · refine lambdaMax_le_of_forall_rayleigh _ fun u hu => ?_
    rw [rayleigh_add_smul_one, hu, one_pow, mul_one]
    have := rayleigh_le_lambdaMax_of_unit hA hu
    linarith
  · obtain ⟨u, hu, hval⟩ := exists_unit_rayleigh_eq_lambdaMax hA
    have h := rayleigh_le_lambdaMax_of_unit (isHermitian_add_smul_one hA c) hu
    rw [rayleigh_add_smul_one, hu, one_pow, mul_one, hval] at h
    exact h

/-- Lean implementation helper: `A + ‖A‖·I ≽ 0` (more generally with any `R ≥ ‖A‖`). -/
lemma posSemidef_add_smul_one_of_norm_le (hA : A.IsHermitian) {R : ℝ}
    (hR : ‖A‖ ≤ R) : (A + (R : ℂ) • (1 : Matrix n n ℂ)).PosSemidef := by
  rw [posSemidef_iff_isHermitian_quadratic]
  refine ⟨isHermitian_add_smul_one hA R, fun u => ?_⟩
  show 0 ≤ rayleigh (A + (R : ℂ) • (1 : Matrix n n ℂ)) u
  rw [rayleigh_add_smul_one]
  have h1 := abs_rayleigh_le A u
  have h2 : 0 ≤ l2norm u ^ 2 := sq_nonneg _
  nlinarith [abs_le.mp h1, mul_le_mul_of_nonneg_right hR h2, norm_nonneg A]

/-- Lean implementation helper (C3-09): the shift identity
`λ_max(A) = ‖A + R·I‖ − R` for `‖A‖ ≤ R`, reducing `λ_max` to the (continuous)
spectral norm on the psd cone. -/
lemma lambdaMax_eq_norm_shift [Nonempty n] (hA : A.IsHermitian) {R : ℝ}
    (hR : ‖A‖ ≤ R) :
    lambdaMax hA = ‖A + (R : ℂ) • (1 : Matrix n n ℂ)‖ - R := by
  have hpsd := posSemidef_add_smul_one_of_norm_le hA hR
  have h1 := posSemidef_l2_opNorm_eq_lambdaMax hpsd
  have h2 : lambdaMax hpsd.1 = lambdaMax hA + R :=
    (lambdaMax_congr rfl hpsd.1 (isHermitian_add_smul_one hA R)).trans
      (lambdaMax_add_smul_one hA R)
  rw [h1, h2]
  ring

/-- Lean implementation helper: the hidden measurability obligation of §3.2 (C3-09),
`ω ↦ λ_max(Y(ω))` is measurable
for a bounded measurable family of Hermitian matrices. -/
lemma measurable_lambdaMax [Nonempty n] (hY : Measurable Y)
    (hHerm : ∀ ω, (Y ω).IsHermitian) {R : ℝ} (hR : ∀ ω, ‖Y ω‖ ≤ R) :
    Measurable fun ω => lambdaMax (hHerm ω) := by
  have heq : (fun ω => lambdaMax (hHerm ω)) =
      fun ω => ‖Y ω + (R : ℂ) • (1 : Matrix n n ℂ)‖ - R :=
    funext fun ω => lambdaMax_eq_norm_shift (hHerm ω) (hR ω)
  rw [heq]
  have hshift : Measurable fun ω => Y ω + (R : ℂ) • (1 : Matrix n n ℂ) := by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    show Measurable fun ω => Y ω i j + ((R : ℂ) • (1 : Matrix n n ℂ)) i j
    exact ((measurable_entry i j).comp hY).add_const _
  exact ((continuous_l2_opNorm.measurable).comp hshift).sub_const R

/-- Lean implementation helper: integrability of `λ_max(Y)` under the standing
boundedness convention (C3-09). -/
lemma integrable_lambdaMax [IsProbabilityMeasure μ] [Nonempty n] (hY : Measurable Y)
    (hHerm : ∀ ω, (Y ω).IsHermitian) {R : ℝ} (hR : ∀ ω, ‖Y ω‖ ≤ R) :
    Integrable (fun ω => lambdaMax (hHerm ω)) μ := by
  refine Integrable.of_bound
    (measurable_lambdaMax hY hHerm hR).aestronglyMeasurable R
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs]
  exact (abs_lambdaMax_le (hHerm ω)).trans (hR ω)

/-- Lean implementation helper: measurability of `λ_min`, via
`λ_min(A) = −λ_max(−A)` from Book eq. (2.1.5) (C3-09). -/
lemma measurable_lambdaMin [Nonempty n] (hY : Measurable Y)
    (hHerm : ∀ ω, (Y ω).IsHermitian) {R : ℝ} (hR : ∀ ω, ‖Y ω‖ ≤ R) :
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
  have hnegbnd : ∀ ω, ‖-(Y ω)‖ ≤ R := fun ω => by
    rw [norm_neg]
    exact hR ω
  exact (measurable_lambdaMax hnegY (fun ω => (hHerm ω).neg) hnegbnd).neg

/-- Lean implementation helper: integrability of `λ_min(Y)` (C3-09). -/
lemma integrable_lambdaMin [IsProbabilityMeasure μ] [Nonempty n] (hY : Measurable Y)
    (hHerm : ∀ ω, (Y ω).IsHermitian) {R : ℝ} (hR : ∀ ω, ‖Y ω‖ ≤ R) :
    Integrable (fun ω => lambdaMin (hHerm ω)) μ := by
  refine Integrable.of_bound
    (measurable_lambdaMin hY hHerm hR).aestronglyMeasurable R
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs]
  exact (abs_lambdaMin_le (hHerm ω)).trans (hR ω)

end LambdaMaxToolkit

section SpectralMapping

/-- **Book eq. (3.2.3)**, equality half:
`λ_max(e^A) = e^{λ_max(A)}` (Spectral Mapping Theorem + monotonicity of `exp`, as the
source says).  Implicit source declaration. -/
lemma lambdaMax_exp [Nonempty n] (hA : A.IsHermitian) :
    lambdaMax (isHermitian_exp hA) = Real.exp (lambdaMax hA) := by
  have h1 := lambdaMax_cfc_of_monotone hA Real.exp_monotone
  have h2 := lambdaMax_congr (matrixExp_eq_cfc hA) (isHermitian_exp hA)
    (isHermitian_cfc Real.exp A)
  rw [h2, h1]

/-- **Book eq. (3.2.3)** (C3-07):
`e^{λ_max(A)} = λ_max(e^A) ≤ tr e^A` — "the exponential of an Hermitian matrix is
positive definite, and (2.1.13) shows that the maximum eigenvalue of a positive
definite matrix is dominated by the trace."  Explicit (unnumbered) proof display. -/
lemma exp_lambdaMax_le_trace_exp [Nonempty n] (hA : A.IsHermitian) :
    Real.exp (lambdaMax hA) ≤ ((NormedSpace.exp A).trace).re := by
  rw [← lambdaMax_exp hA]
  exact lambdaMax_le_trace_re_of_posSemidef (posDef_exp hA).posSemidef

/-- **Book eqs. (2.1.4) and (2.1.5)**, implicit combination used in
Propositions 3.2.1 and 3.2.2 (C3-08): `λ_max(θ·Y) = θ·λ_min(Y)` for `θ ≤ 0`—the
homogeneity (2.1.4) and the sign-reversal (2.1.5) used silently in the λ_min halves
of Propositions 3.2.1/3.2.2.  Implicit source declaration. -/
lemma lambdaMax_smul_nonpos (hA : A.IsHermitian) {θ : ℝ} (hθ : θ ≤ 0)
    (hθA : (θ • A).IsHermitian) : lambdaMax hθA = θ * lambdaMin hA := by
  have hmat : θ • A = (-θ) • (-A) := by
    rw [smul_neg, neg_smul, neg_neg]
  have h1 := lambdaMax_congr hmat hθA
    (isHermitian_real_smul hA.neg (-θ))
  have h2 := lambdaMax_smul_nonneg hA.neg (by linarith : (0:ℝ) ≤ -θ)
    (isHermitian_real_smul hA.neg (-θ))
  rw [h1, h2, lambdaMax_neg hA]
  ring

/-- Lean implementation helper: measurability of `ω ↦ (tr e^{Y ω}).re` (C3-10). -/
lemma measurable_trace_exp_re (hY : Measurable Y) :
    Measurable fun ω => ((NormedSpace.exp (Y ω)).trace).re := by
  have h1 : Measurable fun ω => NormedSpace.exp (Y ω) :=
    measurable_matrixExp_comp hY
  have h2 : (fun ω => ((NormedSpace.exp (Y ω)).trace).re) =
      fun ω => ∑ i, (NormedSpace.exp (Y ω) i i).re := by
    funext ω
    rw [Matrix.trace, Complex.re_sum]
    rfl
  rw [h2]
  exact Finset.measurable_sum _ fun i _ =>
    Complex.measurable_re.comp ((measurable_entry i i).comp h1)

/-- Lean implementation helper: integrability of `ω ↦ (tr e^{Y ω}).re` under the
standing convention (C3-10). -/
lemma integrable_trace_exp_re [IsProbabilityMeasure μ] (hY : Measurable Y)
    (hHerm : ∀ ω, (Y ω).IsHermitian) {R : ℝ} (hR : ∀ ω, ‖Y ω‖ ≤ R) :
    Integrable (fun ω => ((NormedSpace.exp (Y ω)).trace).re) μ := by
  refine Integrable.of_bound (measurable_trace_exp_re hY).aestronglyMeasurable
    ((Fintype.card n : ℝ) * Real.exp R)
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs]
  have h1 : |((NormedSpace.exp (Y ω)).trace).re| ≤
      ∑ i : n, ‖NormedSpace.exp (Y ω) i i‖ := by
    rw [Matrix.trace, Complex.re_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    exact Finset.sum_le_sum fun i _ => Complex.abs_re_le_norm _
  refine h1.trans ?_
  have h2 : ∀ i : n, ‖NormedSpace.exp (Y ω) i i‖ ≤ Real.exp R := fun i =>
    (norm_entry_le_l2_opNorm _ i i).trans
      ((l2_opNorm_exp_le (hHerm ω)).trans (Real.exp_le_exp.mpr (hR ω)))
  calc (∑ i : n, ‖NormedSpace.exp (Y ω) i i‖) ≤ ∑ _i : n, Real.exp R :=
        Finset.sum_le_sum fun i _ => h2 i
  _ = (Fintype.card n : ℝ) * Real.exp R := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Lean implementation helper: the trace of the exponential of a Hermitian matrix is
(strictly)
positive when `d ≥ 1`. -/
lemma trace_exp_re_pos [Nonempty n] (hA : A.IsHermitian) :
    0 < ((NormedSpace.exp A).trace).re := by
  rw [trace_exp_re_eq_sum hA]
  exact Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty

end SpectralMapping

section ScalarJensen

/-- **Book eq. (2.2.2)**, the scalar Jensen instance recovered for the proof of
Proposition 3.2.2): `𝔼 log Z ≤ log 𝔼 Z` for a random variable with values in a
positive interval `[c, C]`.  Tangent-line proof at `m = 𝔼Z`
(`log z ≤ log m + z/m − 1`). -/
lemma integral_log_le_log_integral [IsProbabilityMeasure μ] {Z : Ω → ℝ} {c C : ℝ}
    (hc : 0 < c) (hZmeas : Measurable Z) (hlow : ∀ ω, c ≤ Z ω)
    (hhigh : ∀ ω, Z ω ≤ C) :
    ∫ ω, Real.log (Z ω) ∂μ ≤ Real.log (∫ ω, Z ω ∂μ) := by
  have hZint : Integrable Z μ := by
    refine Integrable.of_bound hZmeas.aestronglyMeasurable (max |c| |C|)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    rcases abs_cases (Z ω) with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
      exact le_max_of_le_right ((hhigh ω).trans (le_abs_self C))
    · rw [h]
      exact le_max_of_le_left (by
        have := hlow ω
        have := hc
        rcases abs_cases c with ⟨hc', _⟩ | ⟨hc', _⟩ <;> linarith)
  set m : ℝ := ∫ ω, Z ω ∂μ with hm
  have hmc : c ≤ m := by
    have h1 : (∫ _ω, c ∂μ) ≤ ∫ ω, Z ω ∂μ :=
      integral_mono (integrable_const c) hZint hlow
    simpa using h1
  have hmpos : 0 < m := lt_of_lt_of_le hc hmc
  have hlogint : Integrable (fun ω => Real.log (Z ω)) μ := by
    refine Integrable.of_bound
      ((Real.measurable_log.comp hZmeas).aestronglyMeasurable)
      (max |Real.log c| |Real.log C|) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    have hzpos : 0 < Z ω := lt_of_lt_of_le hc (hlow ω)
    have h1 : Real.log c ≤ Real.log (Z ω) := Real.log_le_log hc (hlow ω)
    have h2 : Real.log (Z ω) ≤ Real.log C := Real.log_le_log hzpos (hhigh ω)
    rcases abs_cases (Real.log (Z ω)) with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
      exact le_max_of_le_right (h2.trans (le_abs_self _))
    · rw [h]
      exact le_max_of_le_left ((neg_le_neg h1).trans (neg_le_abs _))
  have htangent : ∀ ω, Real.log (Z ω) ≤ Real.log m + (Z ω / m - 1) := by
    intro ω
    have hzpos : 0 < Z ω := lt_of_lt_of_le hc (hlow ω)
    have h1 : Real.log (Z ω / m) ≤ Z ω / m - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hzpos hmpos)
    rw [Real.log_div (ne_of_gt hzpos) (ne_of_gt hmpos)] at h1
    linarith
  have hint2 : Integrable (fun ω => Real.log m + (Z ω / m - 1)) μ := by
    refine Integrable.add (integrable_const _) ?_
    exact (hZint.div_const m).sub (integrable_const 1)
  have h3 := integral_mono hlogint hint2 htangent
  have hint3 : Integrable (fun ω => Z ω / m - 1) μ :=
    (hZint.div_const m).sub (integrable_const 1)
  have h4 : (∫ ω, (Real.log m + (Z ω / m - 1)) ∂μ) = Real.log m := by
    rw [integral_add (integrable_const _) hint3]
    have h5 : (∫ ω, (Z ω / m - 1) ∂μ) = 0 := by
      rw [integral_sub (hZint.div_const m) (integrable_const 1), integral_div,
        integral_const]
      simp only [measure_univ, ENNReal.toReal_one, one_smul, smul_eq_mul]
      rw [← hm]
      field_simp
      rw [MeasureTheory.measureReal_univ_eq_one]
      norm_num
    rw [h5, add_zero, integral_const]
    simp
  rw [h4] at h3
  exact h3

end ScalarJensen

section Prop321

variable [IsProbabilityMeasure μ] [Nonempty n]

/-- **Book Proposition 3.2.1**, eq. (3.2.1) (§3.2, p. 32), pointwise-in-θ form
(the form consumed by
Chapters 4–7): for a bounded random Hermitian matrix `Y`, `t ∈ ℝ`, and `θ > 0`,
`P(λ_max(Y) ≥ t) ≤ e^{-θt}·𝔼 tr e^{θY}`.  Explicit source declaration; faithful
translation of the source proof (Markov (2.2.1), (2.1.4), and (3.2.3)). -/
theorem matrix_laplace_tail_upper (hY : Measurable Y)
    (hHerm : ∀ ω, (Y ω).IsHermitian) {R : ℝ} (hR : ∀ ω, ‖Y ω‖ ≤ R) (t : ℝ)
    {θ : ℝ} (hθ : 0 < θ) :
    μ.real {ω | t ≤ lambdaMax (hHerm ω)} ≤
      Real.exp (-θ * t) * ∫ ω, ((NormedSpace.exp (θ • Y ω)).trace).re ∂μ := by
  have hHermθ : ∀ ω, (θ • Y ω).IsHermitian := fun ω =>
    isHermitian_real_smul (hHerm ω) θ
  -- the event rewrites through the increasing map a ↦ e^{θa}
  have hevent : {ω | t ≤ lambdaMax (hHerm ω)} =
      {ω | Real.exp (θ * t) ≤ Real.exp (θ * lambdaMax (hHerm ω))} := by
    ext ω
    simp only [Set.mem_setOf_eq, Real.exp_le_exp]
    exact ⟨fun h => mul_le_mul_of_nonneg_left h hθ.le,
      fun h => le_of_mul_le_mul_left h hθ⟩
  -- pointwise: e^{θ λ_max(Y)} = e^{λ_max(θY)} = λ_max(e^{θY}) ≤ tr e^{θY}
  have hpoint : ∀ ω, Real.exp (θ * lambdaMax (hHerm ω)) ≤
      ((NormedSpace.exp (θ • Y ω)).trace).re := fun ω => by
    have h1 : θ * lambdaMax (hHerm ω) = lambdaMax (hHermθ ω) :=
      (lambdaMax_smul_nonneg (hHerm ω) hθ.le (hHermθ ω)).symm
    rw [h1]
    exact exp_lambdaMax_le_trace_exp (hHermθ ω)
  -- integrability of the exponential of λ_max
  have hmeasZ : Measurable fun ω => Real.exp (θ * lambdaMax (hHerm ω)) :=
    Real.measurable_exp.comp ((measurable_lambdaMax hY hHerm hR).const_mul θ)
  have hZbd : ∀ ω, Real.exp (θ * lambdaMax (hHerm ω)) ≤ Real.exp (θ * R) :=
    fun ω => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
      ((le_abs_self _).trans ((abs_lambdaMax_le (hHerm ω)).trans (hR ω))) hθ.le)
  have hZint : Integrable (fun ω => Real.exp (θ * lambdaMax (hHerm ω))) μ := by
    refine Integrable.of_bound hmeasZ.aestronglyMeasurable (Real.exp (θ * R))
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hZbd ω
  -- Markov at level e^{θt}
  have hmarkov := markov_inequality
    (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le) hZint
    (Real.exp_pos (θ * t))
  have hmono : (∫ ω, Real.exp (θ * lambdaMax (hHerm ω)) ∂μ) ≤
      ∫ ω, ((NormedSpace.exp (θ • Y ω)).trace).re ∂μ := by
    refine integral_mono hZint ?_ hpoint
    exact integrable_trace_exp_re (μ := μ) (hY.const_smul θ) hHermθ
      (norm_smul_le_of_bound hR)
  rw [hevent, show Real.exp (-θ * t) = (Real.exp (θ * t))⁻¹ by
    rw [show -θ * t = -(θ * t) by ring, Real.exp_neg], inv_mul_eq_div]
  refine hmarkov.trans ?_
  gcongr

/-- **Book Proposition 3.2.1**, eq. (3.2.2), pointwise
form: for `θ < 0`, `P(λ_min(Y) ≤ t) ≤ e^{-θt}·𝔼 tr e^{θY}`.  Explicit source
declaration; the source's proof ("a similar approach", using that `a ↦ e^{θa}`
reverses the event and (2.1.5)) is followed via `lambdaMax_smul_nonpos`. -/
theorem matrix_laplace_tail_lower (hY : Measurable Y)
    (hHerm : ∀ ω, (Y ω).IsHermitian) {R : ℝ} (hR : ∀ ω, ‖Y ω‖ ≤ R) (t : ℝ)
    {θ : ℝ} (hθ : θ < 0) :
    μ.real {ω | lambdaMin (hHerm ω) ≤ t} ≤
      Real.exp (-θ * t) * ∫ ω, ((NormedSpace.exp (θ • Y ω)).trace).re ∂μ := by
  have hHermθ : ∀ ω, (θ • Y ω).IsHermitian := fun ω =>
    isHermitian_real_smul (hHerm ω) θ
  have hevent : {ω | lambdaMin (hHerm ω) ≤ t} =
      {ω | Real.exp (θ * t) ≤ Real.exp (θ * lambdaMin (hHerm ω))} := by
    ext ω
    simp only [Set.mem_setOf_eq, Real.exp_le_exp]
    constructor
    · intro h
      nlinarith
    · intro h
      nlinarith
  have hpoint : ∀ ω, Real.exp (θ * lambdaMin (hHerm ω)) ≤
      ((NormedSpace.exp (θ • Y ω)).trace).re := fun ω => by
    rw [show θ * lambdaMin (hHerm ω) = lambdaMax (hHermθ ω) from
      (lambdaMax_smul_nonpos (hHerm ω) hθ.le (hHermθ ω)).symm]
    exact exp_lambdaMax_le_trace_exp (hHermθ ω)
  have hmeasZ : Measurable fun ω => Real.exp (θ * lambdaMin (hHerm ω)) :=
    Real.measurable_exp.comp ((measurable_lambdaMin hY hHerm hR).const_mul θ)
  have hZbd : ∀ ω, Real.exp (θ * lambdaMin (hHerm ω)) ≤ Real.exp (|θ| * R) :=
    fun ω => Real.exp_le_exp.mpr (by
      have h1 := abs_le.mp ((abs_lambdaMin_le (hHerm ω)).trans (hR ω))
      have h2 := abs_nonneg θ
      rcases abs_cases θ with ⟨ha, _⟩ | ⟨ha, _⟩ <;> nlinarith)
  have hZint : Integrable (fun ω => Real.exp (θ * lambdaMin (hHerm ω))) μ := by
    refine Integrable.of_bound hmeasZ.aestronglyMeasurable (Real.exp (|θ| * R))
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hZbd ω
  have hmarkov := markov_inequality
    (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le) hZint
    (Real.exp_pos (θ * t))
  have hmono : (∫ ω, Real.exp (θ * lambdaMin (hHerm ω)) ∂μ) ≤
      ∫ ω, ((NormedSpace.exp (θ • Y ω)).trace).re ∂μ := by
    refine integral_mono hZint ?_ hpoint
    exact integrable_trace_exp_re (μ := μ) (hY.const_smul θ) hHermθ
      (norm_smul_le_of_bound hR)
  rw [hevent, show Real.exp (-θ * t) = (Real.exp (θ * t))⁻¹ by
    rw [show -θ * t = -(θ * t) by ring, Real.exp_neg], inv_mul_eq_div]
  refine hmarkov.trans ?_
  gcongr

/-- **Book Proposition 3.2.1**, eq. (3.2.1), exact infimum form of the source
display. -/
theorem matrix_laplace_tail_upper_inf (hY : Measurable Y)
    (hHerm : ∀ ω, (Y ω).IsHermitian) {R : ℝ} (hR : ∀ ω, ‖Y ω‖ ≤ R) (t : ℝ) :
    μ.real {ω | t ≤ lambdaMax (hHerm ω)} ≤
      ⨅ θ : {θ : ℝ // 0 < θ}, Real.exp (-(θ : ℝ) * t) *
        ∫ ω, ((NormedSpace.exp ((θ : ℝ) • Y ω)).trace).re ∂μ := by
  haveI : Nonempty {θ : ℝ // 0 < θ} := ⟨⟨1, one_pos⟩⟩
  exact le_ciInf fun θ => matrix_laplace_tail_upper hY hHerm hR t θ.2

/-- **Book Proposition 3.2.1**, eq. (3.2.2), exact infimum form of the source
display. -/
theorem matrix_laplace_tail_lower_inf (hY : Measurable Y)
    (hHerm : ∀ ω, (Y ω).IsHermitian) {R : ℝ} (hR : ∀ ω, ‖Y ω‖ ≤ R) (t : ℝ) :
    μ.real {ω | lambdaMin (hHerm ω) ≤ t} ≤
      ⨅ θ : {θ : ℝ // θ < 0}, Real.exp (-(θ : ℝ) * t) *
        ∫ ω, ((NormedSpace.exp ((θ : ℝ) • Y ω)).trace).re ∂μ := by
  haveI : Nonempty {θ : ℝ // θ < 0} := ⟨⟨-1, by norm_num⟩⟩
  exact le_ciInf fun θ => matrix_laplace_tail_lower hY hHerm hR t θ.2

end Prop321

section Prop322

variable [IsProbabilityMeasure μ] [Nonempty n]

/-- **Book Proposition 3.2.2**, eq. (3.2.4) (§3.2, p. 33), pointwise-in-θ form:
`𝔼 λ_max(Y) ≤ θ⁻¹·log 𝔼 tr e^{θY}` for `θ > 0`.  Explicit source declaration;
faithful translation of the source proof (positive homogeneity (2.1.4), scalar Jensen
(2.2.2) for the logarithm, spectral mapping, (2.1.13)). -/
theorem matrix_laplace_expectation_upper (hY : Measurable Y)
    (hHerm : ∀ ω, (Y ω).IsHermitian) {R : ℝ} (hR : ∀ ω, ‖Y ω‖ ≤ R)
    {θ : ℝ} (hθ : 0 < θ) :
    ∫ ω, lambdaMax (hHerm ω) ∂μ ≤
      θ⁻¹ * Real.log (∫ ω, ((NormedSpace.exp (θ • Y ω)).trace).re ∂μ) := by
  have hHermθ : ∀ ω, (θ • Y ω).IsHermitian := fun ω =>
    isHermitian_real_smul (hHerm ω) θ
  have hbdθ : ∀ ω, ‖θ • Y ω‖ ≤ |θ| * R := norm_smul_le_of_bound hR
  set Z : Ω → ℝ := fun ω => lambdaMax (isHermitian_exp (hHermθ ω)) with hZdef
  have hZeq : ∀ ω, Z ω = Real.exp (lambdaMax (hHermθ ω)) := fun ω =>
    lambdaMax_exp (hHermθ ω)
  have habs : ∀ ω, |lambdaMax (hHermθ ω)| ≤ |θ| * R := fun ω =>
    (abs_lambdaMax_le (hHermθ ω)).trans (hbdθ ω)
  have hZlow : ∀ ω, Real.exp (-(|θ| * R)) ≤ Z ω := fun ω => by
    rw [hZeq]
    exact Real.exp_le_exp.mpr (by linarith [abs_le.mp (habs ω) |>.1])
  have hZhigh : ∀ ω, Z ω ≤ Real.exp (|θ| * R) := fun ω => by
    rw [hZeq]
    exact Real.exp_le_exp.mpr (abs_le.mp (habs ω)).2
  have hexpY : Measurable fun ω => NormedSpace.exp (θ • Y ω) :=
    measurable_matrixExp_comp (hY.const_smul θ)
  have hexpbd : ∀ ω, ‖NormedSpace.exp (θ • Y ω)‖ ≤ Real.exp (|θ| * R) := fun ω =>
    (l2_opNorm_exp_le (hHermθ ω)).trans (Real.exp_le_exp.mpr (hbdθ ω))
  have hZmeas : Measurable Z :=
    measurable_lambdaMax hexpY (fun ω => isHermitian_exp (hHermθ ω)) hexpbd
  have hZint : Integrable Z μ := by
    refine Integrable.of_bound hZmeas.aestronglyMeasurable (Real.exp (|θ| * R))
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    rcases abs_cases (Z ω) with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]; exact hZhigh ω
    · rw [h]
      have := (Real.exp_pos (-(|θ| * R))).le.trans (hZlow ω)
      linarith
  have htrint : Integrable
      (fun ω => ((NormedSpace.exp (θ • Y ω)).trace).re) μ :=
    integrable_trace_exp_re (μ := μ) (hY.const_smul θ) hHermθ hbdθ
  have hchain : θ * (∫ ω, lambdaMax (hHerm ω) ∂μ) ≤
      Real.log (∫ ω, ((NormedSpace.exp (θ • Y ω)).trace).re ∂μ) := by
    have h1 : θ * (∫ ω, lambdaMax (hHerm ω) ∂μ) = ∫ ω, Real.log (Z ω) ∂μ := by
      rw [← MeasureTheory.integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      show θ * lambdaMax (hHerm ω) = Real.log (Z ω)
      rw [hZeq, Real.log_exp]
      exact (lambdaMax_smul_nonneg (hHerm ω) hθ.le (hHermθ ω)).symm
    have h2 : (∫ ω, Real.log (Z ω) ∂μ) ≤ Real.log (∫ ω, Z ω ∂μ) :=
      integral_log_le_log_integral (Real.exp_pos (-(|θ| * R))) hZmeas hZlow hZhigh
    have h3 : (∫ ω, Z ω ∂μ) ≤
        ∫ ω, ((NormedSpace.exp (θ • Y ω)).trace).re ∂μ := by
      refine integral_mono hZint htrint fun ω => ?_
      exact lambdaMax_le_trace_re_of_posSemidef (posDef_exp (hHermθ ω)).posSemidef
    have hZpos : 0 < ∫ ω, Z ω ∂μ := by
      have hlow2 : (∫ _ω, Real.exp (-(|θ| * R)) ∂μ) ≤ ∫ ω, Z ω ∂μ :=
        integral_mono (integrable_const _) hZint hZlow
      rw [integral_const, MeasureTheory.measureReal_univ_eq_one, one_smul] at hlow2
      exact lt_of_lt_of_le (Real.exp_pos _) hlow2
    have h4 : Real.log (∫ ω, Z ω ∂μ) ≤
        Real.log (∫ ω, ((NormedSpace.exp (θ • Y ω)).trace).re ∂μ) :=
      Real.log_le_log hZpos h3
    rw [h1]
    exact h2.trans h4
  rw [inv_mul_eq_div, le_div_iff₀ hθ, mul_comm]
  exact hchain

/-- **Book Proposition 3.2.2**, eq. (3.2.5), pointwise
form: `𝔼 λ_min(Y) ≥ θ⁻¹·log 𝔼 tr e^{θY}` for `θ < 0` ("the proof is quite
similar"). -/
theorem matrix_laplace_expectation_lower (hY : Measurable Y)
    (hHerm : ∀ ω, (Y ω).IsHermitian) {R : ℝ} (hR : ∀ ω, ‖Y ω‖ ≤ R)
    {θ : ℝ} (hθ : θ < 0) :
    θ⁻¹ * Real.log (∫ ω, ((NormedSpace.exp (θ • Y ω)).trace).re ∂μ) ≤
      ∫ ω, lambdaMin (hHerm ω) ∂μ := by
  have hHermθ : ∀ ω, (θ • Y ω).IsHermitian := fun ω =>
    isHermitian_real_smul (hHerm ω) θ
  have hbdθ : ∀ ω, ‖θ • Y ω‖ ≤ |θ| * R := norm_smul_le_of_bound hR
  set Z : Ω → ℝ := fun ω => lambdaMax (isHermitian_exp (hHermθ ω)) with hZdef
  have hZeq : ∀ ω, Z ω = Real.exp (lambdaMax (hHermθ ω)) := fun ω =>
    lambdaMax_exp (hHermθ ω)
  have habs : ∀ ω, |lambdaMax (hHermθ ω)| ≤ |θ| * R := fun ω =>
    (abs_lambdaMax_le (hHermθ ω)).trans (hbdθ ω)
  have hZlow : ∀ ω, Real.exp (-(|θ| * R)) ≤ Z ω := fun ω => by
    rw [hZeq]
    exact Real.exp_le_exp.mpr (by linarith [abs_le.mp (habs ω) |>.1])
  have hZhigh : ∀ ω, Z ω ≤ Real.exp (|θ| * R) := fun ω => by
    rw [hZeq]
    exact Real.exp_le_exp.mpr (abs_le.mp (habs ω)).2
  have hexpY : Measurable fun ω => NormedSpace.exp (θ • Y ω) :=
    measurable_matrixExp_comp (hY.const_smul θ)
  have hexpbd : ∀ ω, ‖NormedSpace.exp (θ • Y ω)‖ ≤ Real.exp (|θ| * R) := fun ω =>
    (l2_opNorm_exp_le (hHermθ ω)).trans (Real.exp_le_exp.mpr (hbdθ ω))
  have hZmeas : Measurable Z :=
    measurable_lambdaMax hexpY (fun ω => isHermitian_exp (hHermθ ω)) hexpbd
  have hZint : Integrable Z μ := by
    refine Integrable.of_bound hZmeas.aestronglyMeasurable (Real.exp (|θ| * R))
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    rcases abs_cases (Z ω) with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]; exact hZhigh ω
    · rw [h]
      have := (Real.exp_pos (-(|θ| * R))).le.trans (hZlow ω)
      linarith
  have htrint : Integrable
      (fun ω => ((NormedSpace.exp (θ • Y ω)).trace).re) μ :=
    integrable_trace_exp_re (μ := μ) (hY.const_smul θ) hHermθ hbdθ
  have hchain : θ * (∫ ω, lambdaMin (hHerm ω) ∂μ) ≤
      Real.log (∫ ω, ((NormedSpace.exp (θ • Y ω)).trace).re ∂μ) := by
    have h1 : θ * (∫ ω, lambdaMin (hHerm ω) ∂μ) = ∫ ω, Real.log (Z ω) ∂μ := by
      rw [← MeasureTheory.integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      show θ * lambdaMin (hHerm ω) = Real.log (Z ω)
      rw [hZeq, Real.log_exp]
      exact (lambdaMax_smul_nonpos (hHerm ω) hθ.le (hHermθ ω)).symm
    have h2 : (∫ ω, Real.log (Z ω) ∂μ) ≤ Real.log (∫ ω, Z ω ∂μ) :=
      integral_log_le_log_integral (Real.exp_pos (-(|θ| * R))) hZmeas hZlow hZhigh
    have h3 : (∫ ω, Z ω ∂μ) ≤
        ∫ ω, ((NormedSpace.exp (θ • Y ω)).trace).re ∂μ := by
      refine integral_mono hZint htrint fun ω => ?_
      exact lambdaMax_le_trace_re_of_posSemidef (posDef_exp (hHermθ ω)).posSemidef
    have hZpos : 0 < ∫ ω, Z ω ∂μ := by
      have hlow2 : (∫ _ω, Real.exp (-(|θ| * R)) ∂μ) ≤ ∫ ω, Z ω ∂μ :=
        integral_mono (integrable_const _) hZint hZlow
      rw [integral_const, MeasureTheory.measureReal_univ_eq_one, one_smul] at hlow2
      exact lt_of_lt_of_le (Real.exp_pos _) hlow2
    have h4 : Real.log (∫ ω, Z ω ∂μ) ≤
        Real.log (∫ ω, ((NormedSpace.exp (θ • Y ω)).trace).re ∂μ) :=
      Real.log_le_log hZpos h3
    rw [h1]
    exact h2.trans h4
  rw [inv_mul_eq_div, div_le_iff_of_neg hθ, mul_comm]
  exact hchain

/-- **Book Proposition 3.2.2**, eq. (3.2.4), exact infimum form. -/
theorem matrix_laplace_expectation_upper_inf (hY : Measurable Y)
    (hHerm : ∀ ω, (Y ω).IsHermitian) {R : ℝ} (hR : ∀ ω, ‖Y ω‖ ≤ R) :
    ∫ ω, lambdaMax (hHerm ω) ∂μ ≤
      ⨅ θ : {θ : ℝ // 0 < θ}, (θ : ℝ)⁻¹ *
        Real.log (∫ ω, ((NormedSpace.exp ((θ : ℝ) • Y ω)).trace).re ∂μ) := by
  haveI : Nonempty {θ : ℝ // 0 < θ} := ⟨⟨1, one_pos⟩⟩
  exact le_ciInf fun θ => matrix_laplace_expectation_upper hY hHerm hR θ.2

/-- **Book Proposition 3.2.2**, eq. (3.2.5), exact supremum form. -/
theorem matrix_laplace_expectation_lower_sup (hY : Measurable Y)
    (hHerm : ∀ ω, (Y ω).IsHermitian) {R : ℝ} (hR : ∀ ω, ‖Y ω‖ ≤ R) :
    (⨆ θ : {θ : ℝ // θ < 0}, (θ : ℝ)⁻¹ *
        Real.log (∫ ω, ((NormedSpace.exp ((θ : ℝ) • Y ω)).trace).re ∂μ)) ≤
      ∫ ω, lambdaMin (hHerm ω) ∂μ := by
  haveI : Nonempty {θ : ℝ // θ < 0} := ⟨⟨-1, by norm_num⟩⟩
  exact ciSup_le fun θ => matrix_laplace_expectation_lower hY hHerm hR θ.2

end Prop322

end MatrixConcentration


set_option linter.unusedSectionVars false

/-!
# The failure of the matrix mgf (Tropp §3.3)

* `scalar_mgf_sum` — **Book eq. (3.3.1)** (C3-13): the scalar multiplication
  rule for the mgf of an independent sum (Mathlib correspondence
  `ProbabilityTheory.iIndepFun.mgf_sum`);
* `matrix_exp_add_of_commute` — the positive content of the display
  "`e^{A+H} ≠ e^A e^H` **unless** `A` and `H` commute" (C3-14): commuting matrices
  do satisfy the addition rule (Mathlib correspondence
  `NormedSpace.exp_add_of_commute`).  The `≠` half is an informal observation with no
  witness given and no later use;
* `golden_thompson` — **Book eq. (3.3.3)** (C3-15):
  `tr e^{A+H} ≤ tr(e^A e^H)`.  The source presents this as "a famous theorem from
  statistical physics" with citations only (Bhatia IX.3, Thirring) and **no proof**;
  it is never used by any later result in the book;
* `scalar_cgf_sum` — **Book eq. (3.3.4)** (C3-17): the scalar additivity rule
  for cgfs, derived by "extracting the logarithm of (3.3.1)" exactly as the source
  does.

The `?=` displays (3.3.2) and the matrix-cgf `?=` display, and the three-matrix
failure of Golden–Thompson, are rhetorical/negative claims — see the inventory
(C3-16, C3-18).
-/

namespace MatrixConcentration

open Matrix Finset MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
variable {n : Type*} [Fintype n] [DecidableEq n]

section ScalarRules

variable [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι] {S : ι → Ω → ℝ}

/-- **Book §3.3, eq. (3.3.1)** (p. 34): the multiplication rule for
the scalar mgf of an independent sum,
`M_{ΣX_k}(θ) = ∏ M_{X_k}(θ)`.  Explicit (unnumbered) source display (scalar recap);
Mathlib correspondence `ProbabilityTheory.iIndepFun.mgf_sum`. -/
theorem scalar_mgf_sum (h_indep : ProbabilityTheory.iIndepFun S μ)
    (h_meas : ∀ k, Measurable (S k)) (θ : ℝ) :
    ProbabilityTheory.mgf (fun ω => ∑ k, S k ω) μ θ =
      ∏ k, ProbabilityTheory.mgf (S k) μ θ := by
  have h1 := ProbabilityTheory.iIndepFun.mgf_sum h_indep h_meas Finset.univ (t := θ)
  have h2 : (∑ k, S k) = fun ω => ∑ k, S k ω := by
    funext ω
    exact Finset.sum_apply ω Finset.univ S
  rwa [h2] at h1

/-- **Book §3.3, eq. (3.3.4)** (p. 34): the addition rule for scalar
cgfs of an independent sum, `Ξ_{ΣX_k}(θ) = Σ Ξ_{X_k}(θ)`.  Explicit (unnumbered)
source display; proved, as the source says, "when we extract the logarithm of the
multiplication rule (3.3.1)". -/
theorem scalar_cgf_sum (h_indep : ProbabilityTheory.iIndepFun S μ)
    (h_meas : ∀ k, Measurable (S k)) {θ : ℝ}
    (h_int : ∀ k, Integrable (fun ω => Real.exp (θ * S k ω)) μ) :
    Real.log (ProbabilityTheory.mgf (fun ω => ∑ k, S k ω) μ θ) =
      ∑ k, Real.log (ProbabilityTheory.mgf (S k) μ θ) := by
  rw [scalar_mgf_sum h_indep h_meas θ]
  exact Real.log_prod fun k _ => (ProbabilityTheory.mgf_pos (h_int k)).ne'

end ScalarRules

section MatrixExpAdd

/-- **Book §3.3, display** "`e^{A+H} ≠ e^A e^H` unless `A` and `H` commute" (p. 34),
positive content (C3-14): for commuting matrices the exponential converts sums to
products.  Implicit source declaration; Mathlib correspondence
(`NormedSpace.exp_add_of_commute`). -/
theorem matrix_exp_add_of_commute {A H : Matrix n n ℂ} (hcomm : Commute A H) :
    NormedSpace.exp (A + H) = NormedSpace.exp A * NormedSpace.exp H :=
  NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℂ) hcomm
    (by rw [NormedSpace.expSeries_radius_eq_top]; exact edist_lt_top _ _)
    (by rw [NormedSpace.expSeries_radius_eq_top]; exact edist_lt_top _ _)

/-- **Book §3.3, eq. (3.3.3)** (p. 34): the Golden–Thompson
inequality `tr e^{A+H} ≤ tr(e^A e^H)` for Hermitian `A`, `H`.

The trace of `e^A e^H`—a product of two positive-definite matrices—is real; both
sides are compared through their real parts, which is the book's implicit reading. -/
theorem golden_thompson {A H : Matrix n n ℂ} (hA : A.IsHermitian)
    (hH : H.IsHermitian) :
    ((NormedSpace.exp (A + H)).trace).re ≤
      ((NormedSpace.exp A * NormedSpace.exp H).trace).re :=
  golden_thompson_trace A H hA hH

end MatrixExpAdd

end MatrixConcentration


set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# A theorem of Lieb (Tropp §3.4)

* `lieb_trace_exp_log_concave` — **Book Theorem 3.4.1 (Lieb)** (C3-19): for a
  fixed Hermitian `H`, the map `A ↦ tr exp(H + log A)` is concave on the convex cone
  of positive-definite matrices. The source presents its proof in Chapter 8;
* `convex_posDef` — the hidden obligation that the pd matrices form a convex set
  (C3-21; the cone part is C2-25);
* `scalar_exp_add_log` — the scalar remark below Theorem 3.4.1 (C3-20):
  `a ↦ e^{h + log a}` is linear on `(0, ∞)`;
* `concaveOn_posDef_expectation_le` — the matrix Jensen instance (C3-23) invoked by
  the source's proof of Corollary 3.4.2 ("Jensen's inequality (2.2.2) allows us to
  draw the expectation inside the function"): for `f` concave on the pd cone and a
  random Hermitian matrix pinched between `a·I` and `b·I` (`0 < a`),
  `𝔼 f(A) ≤ f(𝔼A)`.  Proved with **no** unproved input: concavity on the (relatively)
  open pd cone of the Hermitian subspace gives continuity for free in finite
  dimension (`ConcaveOn.continuousOn`), and Mathlib's Jensen inequality
  (`ConcaveOn.le_map_integral`) applies on the closed convex Loewner interval;
* `expectation_trace_exp_add_le` — **Book Corollary 3.4.2** (C3-22):
  `𝔼 tr exp(H + X) ≤ tr exp(H + log 𝔼 e^X)`.  Faithful translation of the source
  proof (`Y = e^X`, Lieb + Jensen).
-/

namespace MatrixConcentration

open Matrix Finset MeasureTheory
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {A : Matrix n n ℂ}

section Cone

/-- **Book Theorem 3.4.1**, hidden domain obligation (C3-21): the
positive-definite matrices form a convex set ("the convex cone of `d × d`
positive-definite matrices"; the cone part is C2-25).  Implicit source
declaration. -/
lemma convex_posDef : Convex ℝ {A : Matrix n n ℂ | A.PosDef} := by
  intro A hA B hB a b ha hb hab
  rcases ha.eq_or_lt with ha0 | ha0
  · have hb1 : b = 1 := by linarith
    simp only [← ha0, hb1, zero_smul, one_smul, zero_add, Set.mem_setOf_eq]
    exact hB
  · have h1 : (a • A).PosDef := hA.smul ha0
    have h2 : (b • B).PosSemidef := hB.posSemidef.smul hb
    exact h1.add_posSemidef h2

/-- **Book §3.4**, remark below Theorem 3.4.1 (C3-20): "In the scalar case, the analogous
function `a ↦ exp(h + log a)` is linear" — indeed it is `e^h · a` on `(0, ∞)`.
Implicit source declaration. -/
lemma scalar_exp_add_log {a : ℝ} (ha : 0 < a) (h : ℝ) :
    Real.exp (h + Real.log a) = Real.exp h * a := by
  rw [Real.exp_add, Real.exp_log ha]

end Cone

/-- **Book Theorem 3.4.1 (Lieb)** (§3.4, p. 35): for a fixed Hermitian
matrix `H`, the map `A ↦ tr exp(H + log A)` is concave on the convex cone of
positive-definite matrices. -/
theorem lieb_trace_exp_log_concave (Hm : Matrix n n ℂ) (hHm : Hm.IsHermitian) :
    ConcaveOn ℝ {A : Matrix n n ℂ | A.PosDef}
      (fun A => ((NormedSpace.exp (Hm + CFC.log A)).trace).re) :=
  lieb_theorem Hm hHm

section HermitianSubspace

variable (n) in
/-- Lean implementation helper: the Hermitian matrices as a real submodule of the
matrix space (the ambient space for the convexity/continuity arguments of §3.4). -/
noncomputable def hermSubspace : Submodule ℝ (Matrix n n ℂ) :=
  selfAdjoint.submodule ℝ (Matrix n n ℂ)

/-- Lean implementation helper: membership in the Hermitian subspace is matrix
Hermiticity. -/
lemma mem_hermSubspace_iff {A : Matrix n n ℂ} :
    A ∈ hermSubspace n ↔ A.IsHermitian := by
  rw [Matrix.isHermitian_iff_isSelfAdjoint]
  rfl

/-- Lean implementation helper: openness of the pd cone inside the Hermitian
subspace (from the metric stability C2-25). -/
lemma isOpen_posDef_herm :
    IsOpen {x : ↥(hermSubspace n) | (x : Matrix n n ℂ).PosDef} := by
  rw [Metric.isOpen_iff]
  rintro x hx
  obtain ⟨δ, hδ, hball⟩ := posDef_stable_under_hermitian_perturbation hx
  refine ⟨δ, hδ, fun y hy => ?_⟩
  have hyH : (y : Matrix n n ℂ).IsHermitian := mem_hermSubspace_iff.mp y.2
  refine hball (y : Matrix n n ℂ) hyH ?_
  have : dist y x < δ := hy
  rwa [Subtype.dist_eq, dist_eq_norm] at this

/-- Lean implementation helper: `c·I` is Hermitian. -/
lemma isHermitian_smul_one (c : ℝ) :
    ((c : ℂ) • (1 : Matrix n n ℂ)).IsHermitian := by
  have h := isHermitian_add_smul_one (Matrix.isHermitian_zero (n := n)) c
  simpa using h

/-- Lean implementation helper: the Rayleigh value of `c·I`. -/
lemma rayleigh_smul_one (c : ℝ) (u : n → ℂ) :
    rayleigh ((c : ℂ) • (1 : Matrix n n ℂ)) u = c * l2norm u ^ 2 := by
  have h := rayleigh_add_smul_one (0 : Matrix n n ℂ) c u
  have h0 : rayleigh (0 : Matrix n n ℂ) u = 0 := by
    show ((star u) ⬝ᵥ ((0 : Matrix n n ℂ) *ᵥ u)).re = 0
    rw [Matrix.zero_mulVec, dotProduct_zero]
    rfl
  rw [zero_add, h0, zero_add] at h
  exact h

/-- Lean implementation helper: `λ_max(c·I) = c`. -/
lemma lambdaMax_smul_one [Nonempty n] (c : ℝ) :
    lambdaMax (isHermitian_smul_one (n := n) c) = c := by
  refine le_antisymm ?_ ?_
  · refine lambdaMax_le_of_forall_rayleigh _ fun u hu => ?_
    rw [rayleigh_smul_one, hu, one_pow, mul_one]
  · obtain ⟨u, hu, hval⟩ :=
      exists_unit_rayleigh_eq_lambdaMax (isHermitian_smul_one (n := n) c)
    rw [← hval, rayleigh_smul_one, hu, one_pow, mul_one]

/-- Lean implementation helper: `λ_min(c·I) = c`. -/
lemma lambdaMin_smul_one [Nonempty n] (c : ℝ) :
    lambdaMin (isHermitian_smul_one (n := n) c) = c := by
  refine le_antisymm ?_ ?_
  · obtain ⟨u, hu, hval⟩ :=
      exists_unit_rayleigh_eq_lambdaMin (isHermitian_smul_one (n := n) c)
    rw [← hval, rayleigh_smul_one, hu, one_pow, mul_one]
  · refine le_lambdaMin_of_forall_rayleigh _ fun u hu => ?_
    rw [rayleigh_smul_one, hu, one_pow, mul_one]

/-- Lean implementation helper: matrices Loewner-above a real multiple of `I` are
Hermitian. -/
lemma isHermitian_of_smul_one_le {a : ℝ} {A : Matrix n n ℂ}
    (h : (a : ℂ) • (1 : Matrix n n ℂ) ≤ A) : A.IsHermitian := by
  have h1 := (Matrix.le_iff.mp h).1
  have h2 : A - (a : ℂ) • 1 + (a : ℂ) • 1 = A := sub_add_cancel _ _
  rw [← h2]
  exact h1.add (isHermitian_smul_one a)

/-- Lean implementation helper: the Loewner order interval `{A | a·I ≼ A ≼ b·I}` in
the matrix space (its members are automatically Hermitian). -/
def loewnerIcc (n : Type*) [Fintype n] [DecidableEq n] (a b : ℝ) :
    Set (Matrix n n ℂ) :=
  {A | (a : ℂ) • (1 : Matrix n n ℂ) ≤ A ∧ A ≤ (b : ℂ) • (1 : Matrix n n ℂ)}

/-- Lean implementation helper: the Loewner interval is closed. -/
lemma isClosed_loewnerIcc (a b : ℝ) : IsClosed (loewnerIcc n a b) := by
  have h1 : loewnerIcc n a b =
      ({A : Matrix n n ℂ | (a : ℂ) • (1 : Matrix n n ℂ) ≤ A} ∩
        {A : Matrix n n ℂ | A ≤ (b : ℂ) • (1 : Matrix n n ℂ)}) := rfl
  rw [h1]
  refine IsClosed.inter ?_ ?_
  · have h2 : {A : Matrix n n ℂ | (a : ℂ) • (1 : Matrix n n ℂ) ≤ A} =
        (fun A : Matrix n n ℂ => A - (a : ℂ) • (1 : Matrix n n ℂ)) ⁻¹'
          {M : Matrix n n ℂ | M.PosSemidef} := by
      ext A
      simp only [Set.mem_setOf_eq, Set.mem_preimage]
      exact Matrix.le_iff
    rw [h2]
    exact IsClosed.preimage (continuous_id.sub continuous_const) isClosed_posSemidef
  · have h2 : {A : Matrix n n ℂ | A ≤ (b : ℂ) • (1 : Matrix n n ℂ)} =
        (fun A : Matrix n n ℂ => (b : ℂ) • (1 : Matrix n n ℂ) - A) ⁻¹'
          {M : Matrix n n ℂ | M.PosSemidef} := by
      ext A
      simp only [Set.mem_setOf_eq, Set.mem_preimage]
      exact Matrix.le_iff
    rw [h2]
    exact IsClosed.preimage (continuous_const.sub continuous_id) isClosed_posSemidef

/-- Lean implementation helper: the Loewner interval is convex. -/
lemma convex_loewnerIcc (a b : ℝ) : Convex ℝ (loewnerIcc n a b) := by
  rintro x ⟨hx1, hx2⟩ y ⟨hy1, hy2⟩ s t hs ht hst
  constructor
  · show (a : ℂ) • (1 : Matrix n n ℂ) ≤ s • x + t • y
    rw [Matrix.le_iff]
    have hkey : s • ((a : ℂ) • (1 : Matrix n n ℂ)) +
        t • ((a : ℂ) • (1 : Matrix n n ℂ)) = (a : ℂ) • (1 : Matrix n n ℂ) := by
      rw [← add_smul, hst, one_smul]
    have hdecomp : s • x + t • y - (a : ℂ) • (1 : Matrix n n ℂ) =
        s • (x - (a : ℂ) • 1) + t • (y - (a : ℂ) • 1) := by
      rw [smul_sub, smul_sub]
      conv_lhs => rw [← hkey]
      abel
    rw [hdecomp]
    exact ((Matrix.le_iff.mp hx1).smul hs).add ((Matrix.le_iff.mp hy1).smul ht)
  · show s • x + t • y ≤ (b : ℂ) • (1 : Matrix n n ℂ)
    rw [Matrix.le_iff]
    have hkey : s • ((b : ℂ) • (1 : Matrix n n ℂ)) +
        t • ((b : ℂ) • (1 : Matrix n n ℂ)) = (b : ℂ) • (1 : Matrix n n ℂ) := by
      rw [← add_smul, hst, one_smul]
    have hdecomp : (b : ℂ) • (1 : Matrix n n ℂ) - (s • x + t • y) =
        s • ((b : ℂ) • 1 - x) + t • ((b : ℂ) • 1 - y) := by
      rw [smul_sub, smul_sub]
      conv_lhs => rw [← hkey]
      abel
    rw [hdecomp]
    exact ((Matrix.le_iff.mp hx2).smul hs).add ((Matrix.le_iff.mp hy2).smul ht)

/-- Lean implementation helper: members of the Loewner interval are pd when
`0 < a`. -/
lemma posDef_of_mem_loewnerIcc {a b : ℝ} (ha : 0 < a) {x : Matrix n n ℂ}
    (hx : x ∈ loewnerIcc n a b) : x.PosDef := by
  have h1 : ((a : ℂ) • (1 : Matrix n n ℂ)).PosDef :=
    Matrix.PosDef.one.smul (Complex.zero_lt_real.mpr ha)
  have h2 := Matrix.le_iff.mp hx.1
  have := h1.add_posSemidef h2
  rwa [add_sub_cancel] at this

/-- Lean implementation helper: the Loewner interval is norm-bounded
(`‖x‖ ≤ max |a| |b|`, via the eigenvalue bounds from the order pinch). -/
lemma norm_le_of_mem_loewnerIcc {a b : ℝ} {x : Matrix n n ℂ}
    (hx : x ∈ loewnerIcc n a b) : ‖x‖ ≤ max |a| |b| := by
  rcases isEmpty_or_nonempty n with h | h
  · have h0 : x = 0 := by
      ext i j
      exact h.elim i
    rw [h0, norm_zero]
    positivity
  · have hxH : x.IsHermitian := isHermitian_of_smul_one_le hx.1
    rw [l2_opNorm_eq_max_lambda hxH]
    have hIa : ((a : ℂ) • (1 : Matrix n n ℂ)).IsHermitian := isHermitian_smul_one a
    have hIb : ((b : ℂ) • (1 : Matrix n n ℂ)).IsHermitian := isHermitian_smul_one b
    have hub : lambdaMax hxH ≤ b := by
      have h1 := lambdaMax_le_of_loewner_le hxH hIb hx.2
      have h2 : lambdaMax hIb = b := lambdaMax_smul_one b
      linarith
    have hlb : a ≤ lambdaMin hxH := by
      have h1 := lambdaMin_le_of_loewner_le hIa hxH hx.1
      have h2 : lambdaMin hIa = a := lambdaMin_smul_one a
      linarith
    apply max_le
    · exact hub.trans ((le_abs_self b).trans (le_max_right _ _))
    · have : -lambdaMin hxH ≤ -a := by linarith
      exact this.trans ((neg_le_abs a).trans (le_max_left _ _))

end HermitianSubspace

section HermPart

/-- Lean implementation helper (C3-23): the Hermitian-part projection
`p(x) = (x + x*)/2` as a real-linear map on the matrix space (used to transport the
relative openness of the pd cone into the full matrix space). -/
noncomputable def hermPart : Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ where
  toFun x := (2⁻¹ : ℝ) • (x + xᴴ)
  map_add' x y := by
    rw [Matrix.conjTranspose_add, ← smul_add]
    congr 1
    abel
  map_smul' r x := by
    show (2⁻¹ : ℝ) • (r • x + (r • x)ᴴ) = r • ((2⁻¹ : ℝ) • (x + xᴴ))
    have h1 : (r • x)ᴴ = r • xᴴ := by
      ext i j
      rw [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.smul_apply,
        star_smul, star_trivial, ← Matrix.conjTranspose_apply]
    rw [h1, ← smul_add, smul_comm]

/-- Lean implementation helper: evaluation of the Hermitian-part projection. -/
lemma hermPart_apply (x : Matrix n n ℂ) :
    hermPart x = (2⁻¹ : ℝ) • (x + xᴴ) := rfl

/-- Lean implementation helper: the Hermitian part is Hermitian. -/
lemma isHermitian_hermPart (x : Matrix n n ℂ) : (hermPart x).IsHermitian := by
  rw [hermPart_apply]
  refine isHermitian_real_smul ?_ _
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.add_apply, star_add, star_star]
  exact add_comm _ _

/-- Lean implementation helper: the Hermitian-part projection fixes Hermitian matrices. -/
lemma hermPart_of_isHermitian {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    hermPart A = A := by
  rw [hermPart_apply, hA, ← two_smul ℝ A, smul_smul]
  norm_num

/-- Lean implementation helper: the Hermitian part is a contraction. -/
lemma norm_hermPart_le (x : Matrix n n ℂ) : ‖hermPart x‖ ≤ ‖x‖ := by
  rw [hermPart_apply, norm_smul]
  have h1 : ‖x + xᴴ‖ ≤ ‖x‖ + ‖xᴴ‖ := norm_add_le _ _
  rw [Matrix.l2_opNorm_conjTranspose] at h1
  calc ‖(2⁻¹ : ℝ)‖ * ‖x + xᴴ‖ ≤ ‖(2⁻¹ : ℝ)‖ * (‖x‖ + ‖x‖) :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
  _ = ‖x‖ := by
      rw [Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 2⁻¹)]
      ring

/-- Lean implementation helper: continuity of the Hermitian-part projection. -/
lemma continuous_hermPart :
    Continuous (hermPart : Matrix n n ℂ → Matrix n n ℂ) := by
  haveI : FiniteDimensional ℝ (Matrix n n ℂ) :=
    Module.Finite.trans (R := ℝ) ℂ (Matrix n n ℂ)
  exact hermPart.continuous_of_finiteDimensional

/-- Lean implementation helper (C3-23): the preimage of the pd cone under the
Hermitian-part projection is **open** in the full matrix space (the relative
openness of the pd cone, C2-25, transported through the projection). -/
lemma isOpen_hermPart_preimage_posDef :
    IsOpen (hermPart ⁻¹' {A : Matrix n n ℂ | A.PosDef}) := by
  rw [Metric.isOpen_iff]
  intro x hx
  obtain ⟨δ, hδ, hball⟩ := posDef_stable_under_hermitian_perturbation hx
  refine ⟨δ, hδ, fun y hy => ?_⟩
  refine hball (hermPart y) (isHermitian_hermPart y) ?_
  have h1 : hermPart y - hermPart x = hermPart (y - x) := (map_sub _ _ _).symm
  rw [h1]
  refine lt_of_le_of_lt (norm_hermPart_le _) ?_
  rwa [mem_ball_iff_norm] at hy

end HermPart

section MatrixJensen

/-- **Book Corollary 3.4.2**, the matrix Jensen instance (C3-23) invoked by its proof
(citing Jensen (2.2.2)): for `f` concave on the cone of pd matrices
and a random Hermitian matrix pinched between `a·I` and `b·I` with `0 < a`,
`𝔼 f(A) ≤ f(𝔼A)`.  Recovered source prerequisite; complete proof (composition with
`hermPart` + `ConcaveOn.continuousOn` + `ConcaveOn.le_map_integral`).

**Author note.** No separate continuity hypothesis on `f` is needed: finite-dimensional
concavity on the open positive-definite cone supplies it. -/
theorem concaveOn_posDef_expectation_le [IsProbabilityMeasure μ]
    {f : Matrix n n ℂ → ℝ}
    (hf : ConcaveOn ℝ {A : Matrix n n ℂ | A.PosDef} f)
    {A : Ω → Matrix n n ℂ} (hAmeas : Measurable A)
    {a b : ℝ} (ha : 0 < a)
    (hlow : ∀ ω, (a : ℂ) • (1 : Matrix n n ℂ) ≤ A ω)
    (hhigh : ∀ ω, A ω ≤ (b : ℂ) • (1 : Matrix n n ℂ)) :
    ∫ ω, f (A ω) ∂μ ≤ f (expectation μ A) := by
  classical
  haveI : FiniteDimensional ℝ (Matrix n n ℂ) :=
    Module.Finite.trans (R := ℝ) ℂ (Matrix n n ℂ)
  set g : Matrix n n ℂ → ℝ := fun x => f (hermPart x) with hgdef
  -- g is concave on the open convex preimage of the pd cone
  have hgconc : ConcaveOn ℝ (hermPart ⁻¹' {A : Matrix n n ℂ | A.PosDef}) g :=
    hf.comp_affineMap hermPart.toAffineMap
  have hgcont : ContinuousOn g (hermPart ⁻¹' {A : Matrix n n ℂ | A.PosDef}) :=
    hgconc.continuousOn isOpen_hermPart_preimage_posDef
  -- restrict to the closed convex Loewner interval
  have hKsub : loewnerIcc n a b ⊆ hermPart ⁻¹' {A : Matrix n n ℂ | A.PosDef} := by
    intro x hxK
    have hxH : x.IsHermitian := isHermitian_of_smul_one_le hxK.1
    show hermPart x ∈ {A : Matrix n n ℂ | A.PosDef}
    rw [hermPart_of_isHermitian hxH]
    exact posDef_of_mem_loewnerIcc ha hxK
  have hKco : ConcaveOn ℝ (loewnerIcc n a b) g :=
    hgconc.subset hKsub (convex_loewnerIcc a b)
  have hKcont : ContinuousOn g (loewnerIcc n a b) := hgcont.mono hKsub
  have hKclosed := isClosed_loewnerIcc (n := n) a b
  -- membership, integrability
  have hAK : ∀ ω, A ω ∈ loewnerIcc n a b := fun ω => ⟨hlow ω, hhigh ω⟩
  have hAbd : ∀ ω, ‖A ω‖ ≤ max |a| |b| := fun ω => norm_le_of_mem_loewnerIcc (hAK ω)
  have hAint : Integrable A μ := integrable_of_norm_bound hAmeas hAbd
  -- integrability of g ∘ A via compactness of the interval
  have hKcompact : IsCompact (loewnerIcc n a b) := by
    refine Metric.isCompact_of_isClosed_isBounded hKclosed ?_
    rw [Metric.isBounded_iff_subset_closedBall (0 : Matrix n n ℂ)]
    exact ⟨max |a| |b|, fun x hx => by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact norm_le_of_mem_loewnerIcc hx⟩
  have hrestr : Continuous ((loewnerIcc n a b).restrict g) :=
    continuousOn_iff_continuous_restrict.mp hKcont
  have hA' : Measurable fun ω => (⟨A ω, hAK ω⟩ : loewnerIcc n a b) :=
    hAmeas.subtype_mk
  have hgAmeas : Measurable fun ω => g (A ω) := hrestr.measurable.comp hA'
  obtain ⟨C, hC⟩ : ∃ C, ∀ y ∈ g '' loewnerIcc n a b, ‖y‖ ≤ C := by
    have himg := (hKcompact.image_of_continuousOn hKcont).isBounded
    exact isBounded_iff_forall_norm_le.mp himg
  have hgAint : Integrable (fun ω => g (A ω)) μ :=
    Integrable.of_bound hgAmeas.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun ω => hC _ ⟨A ω, hAK ω, rfl⟩)
  -- Jensen (Mathlib, closed convex set)
  have hjensen := hKco.le_map_integral hKcont hKclosed
    (Filter.Eventually.of_forall hAK) hAint hgAint
  -- identify both sides through `hermPart = id` on Hermitian matrices
  have hEA : expectation μ A = ∫ ω, A ω ∂μ := expectation_eq_integral hAint
  have hLHS : (∫ ω, g (A ω) ∂μ) = ∫ ω, f (A ω) ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    show g (A ω) = f (A ω)
    rw [hgdef]
    show f (hermPart (A ω)) = f (A ω)
    rw [hermPart_of_isHermitian (isHermitian_of_smul_one_le (hlow ω))]
  have hRHS : g (∫ ω, A ω ∂μ) = f (expectation μ A) := by
    rw [hgdef]
    show f (hermPart (∫ ω, A ω ∂μ)) = f (expectation μ A)
    rw [← hEA]
    congr 1
    refine hermPart_of_isHermitian ?_
    refine isHermitian_expectation (Filter.Eventually.of_forall fun ω => ?_)
    exact isHermitian_of_smul_one_le (hlow ω)
  rw [← hLHS, ← hRHS]
  exact hjensen

end MatrixJensen

section Cor342

/-- **Book Corollary 3.4.2** (§3.4, p. 35): for a fixed Hermitian `H`
and a (bounded) random Hermitian matrix `X`,
`𝔼 tr exp(H + X) ≤ tr exp(H + log 𝔼 e^X)`.  Explicit source declaration; faithful
translation of the source proof (`Y = e^X`, interpretation (2.1.17) of the
logarithm, Lieb's Theorem 3.4.1, and Jensen (2.2.2)).

The Lean statement makes the source's standing boundedness assumptions explicit. -/
theorem expectation_trace_exp_add_le [IsProbabilityMeasure μ]
    {Hm : Matrix n n ℂ} (hHm : Hm.IsHermitian)
    {X : Ω → Matrix n n ℂ} (hX : Measurable X) (hHerm : ∀ ω, (X ω).IsHermitian)
    {R : ℝ} (hR : ∀ ω, ‖X ω‖ ≤ R) :
    ∫ ω, ((NormedSpace.exp (Hm + X ω)).trace).re ∂μ ≤
      ((NormedSpace.exp (Hm + CFC.log
        (expectation μ fun ω => NormedSpace.exp (X ω)))).trace).re := by
  have hf := lieb_trace_exp_log_concave Hm hHm
  have hAmeas : Measurable fun ω => NormedSpace.exp (X ω) :=
    measurable_matrixExp_comp hX
  have hlow : ∀ ω, ((Real.exp (-R) : ℝ) : ℂ) • (1 : Matrix n n ℂ) ≤
      NormedSpace.exp (X ω) := fun ω => (exp_loewner_bounds (hHerm ω) (hR ω)).1
  have hhigh : ∀ ω, NormedSpace.exp (X ω) ≤ ((Real.exp R : ℝ) : ℂ) • 1 := fun ω =>
    (exp_loewner_bounds (hHerm ω) (hR ω)).2
  have hjensen := concaveOn_posDef_expectation_le (μ := μ) hf hAmeas
    (Real.exp_pos (-R)) hlow hhigh
  have hLHS : (∫ ω, ((NormedSpace.exp (Hm +
      CFC.log (NormedSpace.exp (X ω)))).trace).re ∂μ) =
      ∫ ω, ((NormedSpace.exp (Hm + X ω)).trace).re ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    show ((NormedSpace.exp (Hm + CFC.log (NormedSpace.exp (X ω)))).trace).re = _
    rw [log_exp_eq (hHerm ω)]
  rw [← hLHS]
  exact hjensen

end Cor342

end MatrixConcentration


set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# Subadditivity of the matrix cgf (Tropp §3.5)

* `trace_exp_sum_le_trace_exp_sum_cgf` — **Book Lemma 3.5.1 (Subadditivity of Matrix
  Cgfs)**, eq. (3.5.1) (C3-25):
  `𝔼 tr exp(Σ θX_k) ≤ tr exp(Σ log 𝔼 e^{θX_k})` for all real θ;
* `trace_exp_cgf_sum_le` — **Book eq. (3.5.2)**:
  `tr exp(Ξ_{ΣX}(θ)) ≤ tr exp(Σ Ξ_{X_k}(θ))`, obtained by
  "substituting the expression (3.1.1) for the matrix cgf" via `exp(log M) = M` on
  the pd mgf (C3-28, Mathlib correspondence `CFC.exp_log`);
* `indep_peel_trace_exp` — the one-variable peeling step (C3-26).  The book's proof
  iterates `𝔼 = 𝔼 𝔼_k` ("the tower property of conditional expectation") and applies
  Corollary 3.4.2 at each fixed partial sum. Here the same argument is rendered without
  conditional expectations: for an independent pair, the joint law is the product of
  the laws (`indepFun_iff_map_prod_eq_prod_map_map`), so the expectation is an
  iterated integral over an independent ghost copy (Fubini, `integral_prod`), and
  Corollary 3.4.2 applies at each fixed value of the first coordinate — exactly the
  book's `𝔼_m` step with `H_m` held fixed.  The equivalence is documented in the
  proof audit;
* the "WLOG θ = 1" absorption of the source proof (C3-27) is realized by proving the
  θ = 1 core (`trace_exp_sum_le_aux`) and instantiating it at the family `θ • X_k`.

-/

namespace MatrixConcentration

open Matrix Finset MeasureTheory
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
variable {n : Type*} [Fintype n] [DecidableEq n]

section Helpers

/-- Lean implementation helper: the matrix logarithm of any matrix is Hermitian
(`CFC.log` is the standard matrix function of `Real.log`). -/
lemma isHermitian_cfc_log (M : Matrix n n ℂ) : (CFC.log M).IsHermitian := by
  unfold CFC.log
  exact isHermitian_cfc Real.log M

/-- Lean implementation helper (C3-28): `exp(log M) = M` for a positive-definite
matrix — the interpretation (2.1.17) of the logarithm as the functional inverse of
the exponential.  Mathlib correspondence (`CFC.exp_log`). -/
lemma exp_log_eq {M : Matrix n n ℂ} (hM : M.PosDef) :
    NormedSpace.exp (CFC.log M) = M :=
  CFC.exp_log M hM.isStrictlyPositive

/-- Lean implementation helper: sums of measurable random matrices are measurable. -/
lemma measurable_matsum {ι : Type*} (s : Finset ι) {X : ι → Ω → Matrix n n ℂ}
    (hX : ∀ k, Measurable (X k)) :
    Measurable fun ω => ∑ k ∈ s, X k ω := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  have h : (fun ω => (∑ k ∈ s, X k ω) i j) = fun ω => ∑ k ∈ s, X k ω i j := by
    funext ω
    rw [Matrix.sum_apply]
  rw [h]
  exact Finset.measurable_sum _ fun k _ => (measurable_entry i j).comp (hX k)

/-- Lean implementation helper: finite sums of Hermitian matrices are Hermitian. -/
lemma isHermitian_matsum {ι : Type*} (s : Finset ι) {M : ι → Matrix n n ℂ}
    (hM : ∀ k, (M k).IsHermitian) : (∑ k ∈ s, M k).IsHermitian := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Matrix.isHermitian_zero
  | insert b t hb iht =>
    rw [Finset.sum_insert hb]
    exact (hM b).add iht

/-- Lean implementation helper: matrix addition is measurable (entrywise). -/
lemma measurable_matadd {α : Type*} [MeasurableSpace α]
    {Y Z : α → Matrix n n ℂ} (hY : Measurable Y) (hZ : Measurable Z) :
    Measurable fun a => Y a + Z a := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  show Measurable fun a => Y a i j + Z a i j
  exact ((measurable_entry i j).comp hY).add ((measurable_entry i j).comp hZ)

/-- Lean implementation helper: uniform bound for `|tr e^M|` under a norm bound. -/
lemma abs_trace_exp_re_le {M : Matrix n n ℂ} {D : ℝ} (hM : M.IsHermitian)
    (hD : ‖M‖ ≤ D) :
    |((NormedSpace.exp M).trace).re| ≤ (Fintype.card n : ℝ) * Real.exp D := by
  have h1 : |((NormedSpace.exp M).trace).re| ≤
      ∑ i : n, ‖NormedSpace.exp M i i‖ := by
    rw [Matrix.trace, Complex.re_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    exact Finset.sum_le_sum fun i _ => Complex.abs_re_le_norm _
  refine h1.trans ?_
  have h2 : ∀ i : n, ‖NormedSpace.exp M i i‖ ≤ Real.exp D := fun i =>
    (norm_entry_le_l2_opNorm _ i i).trans
      ((l2_opNorm_exp_le hM).trans (Real.exp_le_exp.mpr hD))
  calc (∑ i : n, ‖NormedSpace.exp M i i‖) ≤ ∑ _i : n, Real.exp D :=
        Finset.sum_le_sum fun i _ => h2 i
  _ = (Fintype.card n : ℝ) * Real.exp D := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end Helpers

section Peel

variable [IsProbabilityMeasure μ]

/-- Lean implementation helper: the one-variable peeling step of Book Lemma 3.5.1
(C3-26), for an **independent**
pair `U`, `V` of bounded random Hermitian matrices,
`𝔼 tr exp(U + V) ≤ 𝔼 tr exp(U + log 𝔼 e^V)`.

This renders the book's conditional-expectation step (`𝔼_m` with `H_m` fixed,
justified by "the tower property") through the equivalent change-of-variables/ghost
copy argument: the joint law of `(U, V)` is the product of the laws, so
`𝔼 f(U, V) = ∫∫ f(U ω, V ω') dμ dμ`, and Corollary 3.4.2 applies for each fixed
`ω`. -/
theorem indep_peel_trace_exp {U V : Ω → Matrix n n ℂ}
    (hUmeas : Measurable U) (hVmeas : Measurable V)
    (hUherm : ∀ ω, (U ω).IsHermitian) (hVherm : ∀ ω, (V ω).IsHermitian)
    {RU RV : ℝ} (hRU : ∀ ω, ‖U ω‖ ≤ RU) (hRV : ∀ ω, ‖V ω‖ ≤ RV)
    (hindep : ProbabilityTheory.IndepFun U V μ) :
    ∫ ω, ((NormedSpace.exp (U ω + V ω)).trace).re ∂μ ≤
      ∫ ω, ((NormedSpace.exp (U ω + CFC.log
        (expectation μ fun ω' => NormedSpace.exp (V ω')))).trace).re ∂μ := by
  classical
  -- the real-valued test function
  set F : Matrix n n ℂ × Matrix n n ℂ → ℝ :=
    fun q => ((NormedSpace.exp (q.1 + q.2)).trace).re with hFdef
  have hFmeas : Measurable F :=
    measurable_trace_exp_re (measurable_matadd measurable_fst measurable_snd)
  -- ghost-copy identity: 𝔼 F(U, V) = ∫∫ F(U ω, V ω') dμ dμ
  have hpairmeas : Measurable fun ω => (U ω, V ω) := hUmeas.prodMk hVmeas
  have hlaw : μ.map (fun ω => (U ω, V ω)) =
      (μ.prod μ).map (Prod.map U V) := by
    rw [hindep.map_prod_eq_prod_map_map hUmeas.aemeasurable hVmeas.aemeasurable]
    exact MeasureTheory.Measure.map_prod_map μ μ hUmeas hVmeas
  have hghost : (∫ ω, F (U ω, V ω) ∂μ) =
      ∫ p, F (U p.1, V p.2) ∂(μ.prod μ) := by
    have h1 : (∫ ω, F (U ω, V ω) ∂μ) =
        ∫ q, F q ∂(μ.map fun ω => (U ω, V ω)) :=
      (integral_map hpairmeas.aemeasurable hFmeas.aestronglyMeasurable).symm
    have h2 : (∫ q, F q ∂((μ.prod μ).map (Prod.map U V))) =
        ∫ p, F (Prod.map U V p) ∂(μ.prod μ) :=
      integral_map (hUmeas.prodMap hVmeas).aemeasurable hFmeas.aestronglyMeasurable
    rw [h1, hlaw, h2]
    rfl
  -- Fubini over the ghost copy
  have hGmeas : Measurable fun p : Ω × Ω => F (U p.1, V p.2) :=
    hFmeas.comp ((hUmeas.comp measurable_fst).prodMk (hVmeas.comp measurable_snd))
  have hGint : Integrable (fun p : Ω × Ω => F (U p.1, V p.2)) (μ.prod μ) := by
    refine Integrable.of_bound hGmeas.aestronglyMeasurable
      ((Fintype.card n : ℝ) * Real.exp (RU + RV))
      (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs]
    refine abs_trace_exp_re_le ((hUherm p.1).add (hVherm p.2)) ?_
    calc ‖U p.1 + V p.2‖ ≤ ‖U p.1‖ + ‖V p.2‖ := norm_add_le _ _
    _ ≤ RU + RV := add_le_add (hRU p.1) (hRV p.2)
  have hfubini : (∫ p, F (U p.1, V p.2) ∂(μ.prod μ)) =
      ∫ ω, (∫ ω', F (U ω, V ω') ∂μ) ∂μ :=
    MeasureTheory.integral_prod _ hGint
  -- the inner integral is Corollary 3.4.2 at the fixed Hermitian matrix `U ω`
  have hinner : ∀ ω, (∫ ω', F (U ω, V ω') ∂μ) ≤
      ((NormedSpace.exp (U ω + CFC.log
        (expectation μ fun ω' => NormedSpace.exp (V ω')))).trace).re := fun ω =>
    expectation_trace_exp_add_le (hUherm ω) hVmeas hVherm hRV
  -- integrate the inner bound
  have hInt1 : Integrable (fun ω => ∫ ω', F (U ω, V ω') ∂μ) μ :=
    hGint.integral_prod_left
  have hInt2 : Integrable (fun ω => ((NormedSpace.exp (U ω + CFC.log
      (expectation μ fun ω' => NormedSpace.exp (V ω')))).trace).re) μ := by
    set L := CFC.log (expectation μ fun ω' => NormedSpace.exp (V ω')) with hLdef
    refine Integrable.of_bound
      ((measurable_trace_exp_re (measurable_matadd hUmeas measurable_const))
        |>.aestronglyMeasurable)
      ((Fintype.card n : ℝ) * Real.exp (RU + ‖L‖))
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    refine abs_trace_exp_re_le ((hUherm ω).add (isHermitian_cfc_log _)) ?_
    calc ‖U ω + L‖ ≤ ‖U ω‖ + ‖L‖ := norm_add_le _ _
    _ ≤ RU + ‖L‖ := by
        have := hRU ω
        linarith
  calc (∫ ω, ((NormedSpace.exp (U ω + V ω)).trace).re ∂μ)
      = ∫ ω, (∫ ω', F (U ω, V ω') ∂μ) ∂μ := by rw [← hfubini, ← hghost]
  _ ≤ ∫ ω, ((NormedSpace.exp (U ω + CFC.log
        (expectation μ fun ω' => NormedSpace.exp (V ω')))).trace).re ∂μ :=
      integral_mono hInt1 hInt2 hinner

end Peel

section Subadditivity

variable [IsProbabilityMeasure μ]
variable {ι : Type*} [DecidableEq ι]

/-- The θ = 1 core of Lemma 3.5.1 with an accumulator matrix `H` (the book's `H_m`):
for an independent family of bounded random Hermitian matrices,
`𝔼 tr exp(H + Σ_{k ∈ s} X_k) ≤ tr exp(H + Σ_{k ∈ s} log 𝔼 e^{X_k})`.
Induction peels one summand at a time using `indep_peel_trace_exp`, exactly the
book's repeated application of Corollary 3.4.2 with `H_m` independent from `X_m`.
Lean implementation helper. -/
theorem trace_exp_sum_le_aux (s : Finset ι) {X : ι → Ω → Matrix n n ℂ}
    (hmeas : ∀ k, Measurable (X k)) (hherm : ∀ k ω, (X k ω).IsHermitian)
    {R : ι → ℝ} (hR : ∀ k ω, ‖X k ω‖ ≤ R k)
    (hindep : ProbabilityTheory.iIndepFun X μ)
    {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    ∫ ω, ((NormedSpace.exp (H + ∑ k ∈ s, X k ω)).trace).re ∂μ ≤
      ((NormedSpace.exp (H + ∑ k ∈ s,
        CFC.log (expectation μ fun ω => NormedSpace.exp (X k ω)))).trace).re := by
  classical
  induction s using Finset.induction_on generalizing H with
  | empty =>
    simp only [Finset.sum_empty, add_zero]
    rw [MeasureTheory.integral_const, MeasureTheory.probReal_univ, one_smul]
  | insert a s ha ih =>
    -- peel the summand `a`
    have hUmeas : Measurable fun ω => H + ∑ k ∈ s, X k ω :=
      measurable_matadd measurable_const (measurable_matsum s hmeas)
    have hUherm : ∀ ω, (H + ∑ k ∈ s, X k ω).IsHermitian := fun ω =>
      hH.add (isHermitian_matsum s fun k => hherm k ω)
    have hUbd : ∀ ω, ‖H + ∑ k ∈ s, X k ω‖ ≤ ‖H‖ + ∑ k ∈ s, R k := fun ω => by
      have h1 : ‖∑ k ∈ s, X k ω‖ ≤ ∑ k ∈ s, R k := by
        calc ‖∑ k ∈ s, X k ω‖ ≤ ∑ k ∈ s, ‖X k ω‖ := norm_sum_le _ _
        _ ≤ ∑ k ∈ s, R k := Finset.sum_le_sum fun k _ => hR k ω
      calc ‖H + ∑ k ∈ s, X k ω‖ ≤ ‖H‖ + ‖∑ k ∈ s, X k ω‖ := norm_add_le _ _
      _ ≤ ‖H‖ + ∑ k ∈ s, R k := by linarith
    have hVindep : ProbabilityTheory.IndepFun
        (fun ω => H + ∑ k ∈ s, X k ω) (X a) μ := by
      have h1 : ProbabilityTheory.IndepFun
          (fun ω => ∑ k ∈ s, X k ω) (X a) μ := by
        have h2 := ProbabilityTheory.iIndepFun.indepFun_finsetSum_of_notMem
          hindep hmeas ha
        have h3 : (∑ k ∈ s, X k) = fun ω => ∑ k ∈ s, X k ω := by
          funext ω
          exact Finset.sum_apply ω s X
        rwa [h3] at h2
      have h4 := h1.comp (φ := fun M : Matrix n n ℂ => H + M)
        (ψ := id) (measurable_matadd measurable_const measurable_id) measurable_id
      exact h4
    have hpeel := indep_peel_trace_exp (μ := μ) hUmeas (hmeas a) hUherm
      (hherm a) hUbd (hR a) hVindep
    -- rearrange and apply the induction hypothesis with the enlarged accumulator
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
    have hih := ih (H := H + CFC.log (expectation μ fun ω' => NormedSpace.exp (X a ω')))
      (hH.add (isHermitian_cfc_log _))
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

/-- **Book Lemma 3.5.1 (Subadditivity of Matrix Cgfs)**, eq. (3.5.1)
(§3.5, p. 35): for a finite sequence of independent,
random, Hermitian matrices and every `θ ∈ ℝ`,
`𝔼 tr exp(Σ_k θX_k) ≤ tr exp(Σ_k log 𝔼 e^{θX_k})`.
Explicit source declaration; the "θ = 1 WLOG by absorbing the parameter" step of the
source proof is realized by instantiating the θ = 1 core at the family `θ • X_k`. -/
theorem trace_exp_sum_le_trace_exp_sum_cgf [Fintype ι]
    {X : ι → Ω → Matrix n n ℂ}
    (hmeas : ∀ k, Measurable (X k)) (hherm : ∀ k ω, (X k ω).IsHermitian)
    {R : ι → ℝ} (hR : ∀ k ω, ‖X k ω‖ ≤ R k)
    (hindep : ProbabilityTheory.iIndepFun X μ) (θ : ℝ) :
    ∫ ω, ((NormedSpace.exp (∑ k, θ • X k ω)).trace).re ∂μ ≤
      ((NormedSpace.exp (∑ k, matrixCgf μ (X k) θ)).trace).re := by
  classical
  have hmeasθ : ∀ k, Measurable fun ω => θ • X k ω := fun k =>
    (hmeas k).const_smul θ
  have hhermθ : ∀ k ω, (θ • X k ω).IsHermitian := fun k ω =>
    isHermitian_real_smul (hherm k ω) θ
  have hRθ : ∀ k ω, ‖θ • X k ω‖ ≤ |θ| * R k := fun k ω => by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hR k ω) (abs_nonneg θ)
  have hsmulmeas : Measurable fun M : Matrix n n ℂ => θ • M := by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    show Measurable fun M : Matrix n n ℂ => θ • M i j
    exact (measurable_entry i j).const_smul θ
  have hindepθ : ProbabilityTheory.iIndepFun (fun k ω => θ • X k ω) μ :=
    hindep.comp _ fun _ => hsmulmeas
  have h := trace_exp_sum_le_aux (μ := μ) Finset.univ hmeasθ hhermθ hRθ hindepθ
    (Matrix.isHermitian_zero (n := n))
  simp only [zero_add] at h
  exact h

/-- **Book Lemma 3.5.1**, eq. (3.5.2): equivalently,
`tr exp(Ξ_{Σ X_k}(θ)) ≤ tr exp(Σ_k Ξ_{X_k}(θ))` — "The formulation (3.5.2) follows
from (3.5.1) when we substitute the expression (3.1.1) for the matrix cgf and make
some algebraic simplifications" (via `exp(log M) = M` on the pd mgf, C3-28). -/
theorem trace_exp_cgf_sum_le [Fintype ι] [Nonempty n]
    {X : ι → Ω → Matrix n n ℂ}
    (hmeas : ∀ k, Measurable (X k)) (hherm : ∀ k ω, (X k ω).IsHermitian)
    {R : ι → ℝ} (hR : ∀ k ω, ‖X k ω‖ ≤ R k)
    (hindep : ProbabilityTheory.iIndepFun X μ) (θ : ℝ) :
    ((NormedSpace.exp (matrixCgf μ (fun ω => ∑ k, X k ω) θ)).trace).re ≤
      ((NormedSpace.exp (∑ k, matrixCgf μ (X k) θ)).trace).re := by
  classical
  have hsummeas : Measurable fun ω => ∑ k, X k ω :=
    measurable_matsum Finset.univ hmeas
  have hsumherm : ∀ ω, (∑ k, X k ω).IsHermitian := fun ω =>
    isHermitian_matsum Finset.univ fun k => hherm k ω
  have hsumbd : ∀ ω, ‖∑ k, X k ω‖ ≤ ∑ k, R k := fun ω => by
    calc ‖∑ k, X k ω‖ ≤ ∑ k, ‖X k ω‖ := norm_sum_le _ _
    _ ≤ ∑ k, R k := Finset.sum_le_sum fun k _ => hR k ω
  have hpd : (matrixMgf μ (fun ω => ∑ k, X k ω) θ).PosDef :=
    posDef_matrixMgf hsummeas hsumherm hsumbd θ
  -- LHS: exp(log M_{ΣX}(θ)) = M_{ΣX}(θ), whose trace is `𝔼 tr e^{θΣX}`
  have hLHS : ((NormedSpace.exp (matrixCgf μ (fun ω => ∑ k, X k ω) θ)).trace).re =
      ∫ ω, ((NormedSpace.exp (∑ k, θ • X k ω)).trace).re ∂μ := by
    rw [show matrixCgf μ (fun ω => ∑ k, X k ω) θ =
      CFC.log (matrixMgf μ (fun ω => ∑ k, X k ω) θ) from rfl]
    rw [exp_log_eq hpd]
    have h1 : MIntegrable (fun ω => NormedSpace.exp (θ • ∑ k, X k ω)) μ :=
      mintegrable_matrixExp_of_bound (hsummeas.const_smul θ)
        (fun ω => isHermitian_real_smul (hsumherm ω) θ)
        (fun ω => by
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (hsumbd ω) (abs_nonneg θ))
    have h2 := expectation_trace (μ := μ) h1
    rw [show matrixMgf μ (fun ω => ∑ k, X k ω) θ =
      expectation μ (fun ω => NormedSpace.exp (θ • ∑ k, X k ω)) from rfl, ← h2]
    have h3 : (∫ ω, (NormedSpace.exp (θ • ∑ k, X k ω)).trace ∂μ).re =
        ∫ ω, ((NormedSpace.exp (θ • ∑ k, X k ω)).trace).re ∂μ := by
      rw [← RCLike.re_to_complex, ← integral_re]
      · rfl
      · -- integrability of the complex trace
        have h4 : (fun ω => (NormedSpace.exp (θ • ∑ k, X k ω)).trace) =
            fun ω => ∑ i, NormedSpace.exp (θ • ∑ k, X k ω) i i := by
          funext ω
          rfl
        rw [h4]
        exact MeasureTheory.integrable_finsetSum _ fun i _ => h1 i i
    rw [h3]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    show ((NormedSpace.exp (θ • ∑ k, X k ω)).trace).re =
      ((NormedSpace.exp (∑ k, θ • X k ω)).trace).re
    rw [Finset.smul_sum (r := θ) (f := fun k => X k ω) (s := Finset.univ)]
  rw [hLHS]
  exact trace_exp_sum_le_trace_exp_sum_cgf hmeas hherm hR hindep θ

end Subadditivity

end MatrixConcentration


set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# Master bounds for sums of independent random matrices (Tropp §3.6)

**Book Theorem 3.6.1 (Master Bounds for a Sum of Independent Random Matrices)**
(C3-29), eqs. (3.6.1)–(3.6.4): for a finite sequence `{X_k}` of
independent random Hermitian matrices,

* `master_expectation_upper` — **Book eq. (3.6.1)**:
  `𝔼 λ_max(Σ X_k) ≤ inf_{θ>0} θ⁻¹ log tr exp(Σ log 𝔼 e^{θX_k})`;
* `master_expectation_lower` — **Book eq. (3.6.2)**:
  `𝔼 λ_min(Σ X_k) ≥ sup_{θ<0} θ⁻¹ log tr exp(Σ log 𝔼 e^{θX_k})`;
* `master_tail_upper` — **Book eq. (3.6.3)**:
  `P(λ_max(Σ X_k) ≥ t) ≤ inf_{θ>0} e^{-θt} tr exp(Σ log 𝔼 e^{θX_k})`;
* `master_tail_lower` — **Book eq. (3.6.4)**:
  `P(λ_min(Σ X_k) ≤ t) ≤ inf_{θ<0} e^{-θt} tr exp(Σ log 𝔼 e^{θX_k})`.

Each is given in the pointwise-in-θ form (the form consumed by Chapters 4–7) plus
the exact inf/sup form of the source display (`_inf`/`_sup`).  The proofs are the
source's: "Substitute the subadditivity rule for matrix cgfs, Lemma 3.5.1, into the
two matrix Laplace transform results, Proposition 3.2.1 and Proposition 3.2.2."
`Σ log 𝔼 e^{θX_k}` is written `Σ matrixCgf μ (X k) θ` (Definition 3.1.1).

The closing remark of §3.6 (extension to rectangular matrices via the Hermitian
dilation (2.1.26)) introduces no formal statement — the source explicitly declines
("Instead of presenting a general theorem, we find it more natural to extend
individual results"); the dilation interface is C2-60..C2-67/C2-97/C2-98 (C3-30).
-/

namespace MatrixConcentration

open Matrix Finset MeasureTheory
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section Helpers

/-- Lean implementation helper: lower bound for the trace exponential,
`d·e^{-D} ≤ tr e^M` when `‖M‖ ≤ D` (all eigenvalues are at least `−D`). -/
lemma trace_exp_re_ge {M : Matrix n n ℂ} {D : ℝ} (hM : M.IsHermitian)
    (hD : ‖M‖ ≤ D) :
    (Fintype.card n : ℝ) * Real.exp (-D) ≤ ((NormedSpace.exp M).trace).re := by
  rw [trace_exp_re_eq_sum hM]
  have h1 : ∀ i, Real.exp (-D) ≤ Real.exp (hM.eigenvalues i) := fun i => by
    refine Real.exp_le_exp.mpr ?_
    have h2 := abs_le.mp ((abs_eigenvalues_le_l2_opNorm hM i).trans hD)
    linarith [h2.1]
  calc (Fintype.card n : ℝ) * Real.exp (-D) = ∑ _i : n, Real.exp (-D) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  _ ≤ ∑ i, Real.exp (hM.eigenvalues i) := Finset.sum_le_sum fun i _ => h1 i

end Helpers

section MasterBounds

variable [IsProbabilityMeasure μ] [Nonempty n]
variable {X : ι → Ω → Matrix n n ℂ}

/-- Lean implementation helper: exchange scalar multiplication and a finite sum inside
the expected trace exponential. -/
private lemma integral_trace_exp_smul_sum_eq
    (hmeas : ∀ k, Measurable (X k)) (θ : ℝ) :
    (∫ ω, ((NormedSpace.exp (θ • ∑ k, X k ω)).trace).re ∂μ) =
      ∫ ω, ((NormedSpace.exp (∑ k, θ • X k ω)).trace).re ∂μ := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  show ((NormedSpace.exp (θ • ∑ k, X k ω)).trace).re =
    ((NormedSpace.exp (∑ k, θ • X k ω)).trace).re
  rw [Finset.smul_sum (r := θ) (f := fun k => X k ω) (s := Finset.univ)]

/-- **Book Theorem 3.6.1**, eq. (3.6.3) (§3.6, p. 36),
pointwise-in-θ form: for `θ > 0` and all real `t`,
`P(λ_max(Σ X_k) ≥ t) ≤ e^{-θt}·tr exp(Σ_k log 𝔼 e^{θX_k})`.
Explicit source declaration (proof: substitute Lemma 3.5.1 into Proposition 3.2.1). -/
theorem master_tail_upper
    (hmeas : ∀ k, Measurable (X k)) (hherm : ∀ k ω, (X k ω).IsHermitian)
    {R : ι → ℝ} (hR : ∀ k ω, ‖X k ω‖ ≤ R k)
    (hindep : ProbabilityTheory.iIndepFun X μ) (t : ℝ) {θ : ℝ} (hθ : 0 < θ) :
    μ.real {ω | t ≤ lambdaMax (isHermitian_matsum Finset.univ
        (fun k => hherm k ω))} ≤
      Real.exp (-θ * t) *
        ((NormedSpace.exp (∑ k, matrixCgf μ (X k) θ)).trace).re := by
  have hYmeas : Measurable fun ω => ∑ k, X k ω :=
    measurable_matsum Finset.univ hmeas
  have hYbd : ∀ ω, ‖∑ k, X k ω‖ ≤ ∑ k, R k := fun ω => by
    calc ‖∑ k, X k ω‖ ≤ ∑ k, ‖X k ω‖ := norm_sum_le _ _
    _ ≤ ∑ k, R k := Finset.sum_le_sum fun k _ => hR k ω
  have h1 := matrix_laplace_tail_upper (μ := μ) hYmeas
    (fun ω => isHermitian_matsum Finset.univ fun k => hherm k ω) hYbd t hθ
  have h2 := trace_exp_sum_le_trace_exp_sum_cgf (μ := μ) hmeas hherm hR hindep θ
  refine h1.trans ?_
  rw [integral_trace_exp_smul_sum_eq hmeas θ]
  exact mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le

/-- **Book Theorem 3.6.1**, eq. (3.6.4), pointwise form: for `θ < 0`,
`P(λ_min(Σ X_k) ≤ t) ≤ e^{-θt}·tr exp(Σ_k log 𝔼 e^{θX_k})`. -/
theorem master_tail_lower
    (hmeas : ∀ k, Measurable (X k)) (hherm : ∀ k ω, (X k ω).IsHermitian)
    {R : ι → ℝ} (hR : ∀ k ω, ‖X k ω‖ ≤ R k)
    (hindep : ProbabilityTheory.iIndepFun X μ) (t : ℝ) {θ : ℝ} (hθ : θ < 0) :
    μ.real {ω | lambdaMin (isHermitian_matsum Finset.univ
        (fun k => hherm k ω)) ≤ t} ≤
      Real.exp (-θ * t) *
        ((NormedSpace.exp (∑ k, matrixCgf μ (X k) θ)).trace).re := by
  have hYmeas : Measurable fun ω => ∑ k, X k ω :=
    measurable_matsum Finset.univ hmeas
  have hYbd : ∀ ω, ‖∑ k, X k ω‖ ≤ ∑ k, R k := fun ω => by
    calc ‖∑ k, X k ω‖ ≤ ∑ k, ‖X k ω‖ := norm_sum_le _ _
    _ ≤ ∑ k, R k := Finset.sum_le_sum fun k _ => hR k ω
  have h1 := matrix_laplace_tail_lower (μ := μ) hYmeas
    (fun ω => isHermitian_matsum Finset.univ fun k => hherm k ω) hYbd t hθ
  have h2 := trace_exp_sum_le_trace_exp_sum_cgf (μ := μ) hmeas hherm hR hindep θ
  refine h1.trans ?_
  rw [integral_trace_exp_smul_sum_eq hmeas θ]
  exact mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le

/-- **Book Theorem 3.6.1**, eq. (3.6.1), pointwise form: for `θ > 0`,
`𝔼 λ_max(Σ X_k) ≤ θ⁻¹·log tr exp(Σ_k log 𝔼 e^{θX_k})`. -/
theorem master_expectation_upper
    (hmeas : ∀ k, Measurable (X k)) (hherm : ∀ k ω, (X k ω).IsHermitian)
    {R : ι → ℝ} (hR : ∀ k ω, ‖X k ω‖ ≤ R k)
    (hindep : ProbabilityTheory.iIndepFun X μ) {θ : ℝ} (hθ : 0 < θ) :
    ∫ ω, lambdaMax (isHermitian_matsum Finset.univ
        (fun k => hherm k ω)) ∂μ ≤
      θ⁻¹ * Real.log
        ((NormedSpace.exp (∑ k, matrixCgf μ (X k) θ)).trace).re := by
  have hYmeas : Measurable fun ω => ∑ k, X k ω :=
    measurable_matsum Finset.univ hmeas
  have hYherm : ∀ ω, (∑ k, X k ω).IsHermitian := fun ω =>
    isHermitian_matsum Finset.univ fun k => hherm k ω
  have hYbd : ∀ ω, ‖∑ k, X k ω‖ ≤ ∑ k, R k := fun ω => by
    calc ‖∑ k, X k ω‖ ≤ ∑ k, ‖X k ω‖ := norm_sum_le _ _
    _ ≤ ∑ k, R k := Finset.sum_le_sum fun k _ => hR k ω
  have h1 := matrix_laplace_expectation_upper (μ := μ) hYmeas hYherm hYbd hθ
  refine h1.trans ?_
  -- the trace-mgf is positive, so the logarithm is monotone
  have h2 := trace_exp_sum_le_trace_exp_sum_cgf (μ := μ) hmeas hherm hR hindep θ
  have hpos : 0 < ∫ ω, ((NormedSpace.exp (θ • ∑ k, X k ω)).trace).re ∂μ := by
    have hlow : ∀ ω, (Fintype.card n : ℝ) * Real.exp (-(|θ| * ∑ k, R k)) ≤
        ((NormedSpace.exp (θ • ∑ k, X k ω)).trace).re := fun ω =>
      trace_exp_re_ge (isHermitian_real_smul (hYherm ω) θ)
        (by
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (hYbd ω) (abs_nonneg θ))
    have hint : Integrable
        (fun ω => ((NormedSpace.exp (θ • ∑ k, X k ω)).trace).re) μ :=
      integrable_trace_exp_re (μ := μ) (hYmeas.const_smul θ)
        (fun ω => isHermitian_real_smul (hYherm ω) θ)
        (fun ω => by
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (hYbd ω) (abs_nonneg θ))
    have hmono := integral_mono (integrable_const _) hint hlow
    rw [integral_const, MeasureTheory.probReal_univ, one_smul] at hmono
    refine lt_of_lt_of_le ?_ hmono
    have hcard : (0 : ℝ) < (Fintype.card n : ℝ) := by
      exact_mod_cast Fintype.card_pos
    positivity
  have h3 : Real.log (∫ ω, ((NormedSpace.exp (θ • ∑ k, X k ω)).trace).re ∂μ) ≤
      Real.log ((NormedSpace.exp (∑ k, matrixCgf μ (X k) θ)).trace).re := by
    refine Real.log_le_log hpos ?_
    rw [integral_trace_exp_smul_sum_eq hmeas θ]
    exact h2
  calc θ⁻¹ * Real.log (∫ ω, ((NormedSpace.exp (θ • ∑ k, X k ω)).trace).re ∂μ)
      ≤ θ⁻¹ * Real.log
        ((NormedSpace.exp (∑ k, matrixCgf μ (X k) θ)).trace).re :=
      mul_le_mul_of_nonneg_left h3 (inv_pos.mpr hθ).le

/-- **Book Theorem 3.6.1**, eq. (3.6.2), pointwise form: for `θ < 0`,
`𝔼 λ_min(Σ X_k) ≥ θ⁻¹·log tr exp(Σ_k log 𝔼 e^{θX_k})`. -/
theorem master_expectation_lower
    (hmeas : ∀ k, Measurable (X k)) (hherm : ∀ k ω, (X k ω).IsHermitian)
    {R : ι → ℝ} (hR : ∀ k ω, ‖X k ω‖ ≤ R k)
    (hindep : ProbabilityTheory.iIndepFun X μ) {θ : ℝ} (hθ : θ < 0) :
    θ⁻¹ * Real.log
        ((NormedSpace.exp (∑ k, matrixCgf μ (X k) θ)).trace).re ≤
      ∫ ω, lambdaMin (isHermitian_matsum Finset.univ
        (fun k => hherm k ω)) ∂μ := by
  have hYmeas : Measurable fun ω => ∑ k, X k ω :=
    measurable_matsum Finset.univ hmeas
  have hYherm : ∀ ω, (∑ k, X k ω).IsHermitian := fun ω =>
    isHermitian_matsum Finset.univ fun k => hherm k ω
  have hYbd : ∀ ω, ‖∑ k, X k ω‖ ≤ ∑ k, R k := fun ω => by
    calc ‖∑ k, X k ω‖ ≤ ∑ k, ‖X k ω‖ := norm_sum_le _ _
    _ ≤ ∑ k, R k := Finset.sum_le_sum fun k _ => hR k ω
  have h1 := matrix_laplace_expectation_lower (μ := μ) hYmeas hYherm hYbd hθ
  refine le_trans ?_ h1
  have h2 := trace_exp_sum_le_trace_exp_sum_cgf (μ := μ) hmeas hherm hR hindep θ
  have hpos : 0 < ∫ ω, ((NormedSpace.exp (θ • ∑ k, X k ω)).trace).re ∂μ := by
    have hlow : ∀ ω, (Fintype.card n : ℝ) * Real.exp (-(|θ| * ∑ k, R k)) ≤
        ((NormedSpace.exp (θ • ∑ k, X k ω)).trace).re := fun ω =>
      trace_exp_re_ge (isHermitian_real_smul (hYherm ω) θ)
        (by
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (hYbd ω) (abs_nonneg θ))
    have hint : Integrable
        (fun ω => ((NormedSpace.exp (θ • ∑ k, X k ω)).trace).re) μ :=
      integrable_trace_exp_re (μ := μ) (hYmeas.const_smul θ)
        (fun ω => isHermitian_real_smul (hYherm ω) θ)
        (fun ω => by
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (hYbd ω) (abs_nonneg θ))
    have hmono := integral_mono (integrable_const _) hint hlow
    rw [integral_const, MeasureTheory.probReal_univ, one_smul] at hmono
    refine lt_of_lt_of_le ?_ hmono
    have hcard : (0 : ℝ) < (Fintype.card n : ℝ) := by
      exact_mod_cast Fintype.card_pos
    positivity
  have h3 : Real.log (∫ ω, ((NormedSpace.exp (θ • ∑ k, X k ω)).trace).re ∂μ) ≤
      Real.log ((NormedSpace.exp (∑ k, matrixCgf μ (X k) θ)).trace).re := by
    refine Real.log_le_log hpos ?_
    rw [integral_trace_exp_smul_sum_eq hmeas θ]
    exact h2
  exact mul_le_mul_of_nonpos_left h3 (by
    rw [inv_nonpos]
    exact hθ.le)

/-- **Book Theorem 3.6.1**, eq. (3.6.1), exact infimum form. -/
theorem master_expectation_upper_inf
    (hmeas : ∀ k, Measurable (X k)) (hherm : ∀ k ω, (X k ω).IsHermitian)
    {R : ι → ℝ} (hR : ∀ k ω, ‖X k ω‖ ≤ R k)
    (hindep : ProbabilityTheory.iIndepFun X μ) :
    ∫ ω, lambdaMax (isHermitian_matsum Finset.univ
        (fun k => hherm k ω)) ∂μ ≤
      ⨅ θ : {θ : ℝ // 0 < θ}, (θ : ℝ)⁻¹ * Real.log
        ((NormedSpace.exp (∑ k, matrixCgf μ (X k) (θ : ℝ))).trace).re := by
  haveI : Nonempty {θ : ℝ // 0 < θ} := ⟨⟨1, one_pos⟩⟩
  exact le_ciInf fun θ => master_expectation_upper hmeas hherm hR hindep θ.2

/-- **Book Theorem 3.6.1**, eq. (3.6.2), exact supremum form. -/
theorem master_expectation_lower_sup
    (hmeas : ∀ k, Measurable (X k)) (hherm : ∀ k ω, (X k ω).IsHermitian)
    {R : ι → ℝ} (hR : ∀ k ω, ‖X k ω‖ ≤ R k)
    (hindep : ProbabilityTheory.iIndepFun X μ) :
    (⨆ θ : {θ : ℝ // θ < 0}, (θ : ℝ)⁻¹ * Real.log
        ((NormedSpace.exp (∑ k, matrixCgf μ (X k) (θ : ℝ))).trace).re) ≤
      ∫ ω, lambdaMin (isHermitian_matsum Finset.univ
        (fun k => hherm k ω)) ∂μ := by
  haveI : Nonempty {θ : ℝ // θ < 0} := ⟨⟨-1, by norm_num⟩⟩
  exact ciSup_le fun θ => master_expectation_lower hmeas hherm hR hindep θ.2

/-- **Book Theorem 3.6.1**, eq. (3.6.3), exact infimum form. -/
theorem master_tail_upper_inf
    (hmeas : ∀ k, Measurable (X k)) (hherm : ∀ k ω, (X k ω).IsHermitian)
    {R : ι → ℝ} (hR : ∀ k ω, ‖X k ω‖ ≤ R k)
    (hindep : ProbabilityTheory.iIndepFun X μ) (t : ℝ) :
    μ.real {ω | t ≤ lambdaMax (isHermitian_matsum Finset.univ
        (fun k => hherm k ω))} ≤
      ⨅ θ : {θ : ℝ // 0 < θ}, Real.exp (-(θ : ℝ) * t) *
        ((NormedSpace.exp (∑ k, matrixCgf μ (X k) (θ : ℝ))).trace).re := by
  haveI : Nonempty {θ : ℝ // 0 < θ} := ⟨⟨1, one_pos⟩⟩
  exact le_ciInf fun θ => master_tail_upper hmeas hherm hR hindep t θ.2

/-- **Book Theorem 3.6.1**, eq. (3.6.4), exact infimum form. -/
theorem master_tail_lower_inf
    (hmeas : ∀ k, Measurable (X k)) (hherm : ∀ k ω, (X k ω).IsHermitian)
    {R : ι → ℝ} (hR : ∀ k ω, ‖X k ω‖ ≤ R k)
    (hindep : ProbabilityTheory.iIndepFun X μ) (t : ℝ) :
    μ.real {ω | lambdaMin (isHermitian_matsum Finset.univ
        (fun k => hherm k ω)) ≤ t} ≤
      ⨅ θ : {θ : ℝ // (θ : ℝ) < 0}, Real.exp (-(θ : ℝ) * t) *
        ((NormedSpace.exp (∑ k, matrixCgf μ (X k) (θ : ℝ))).trace).re := by
  haveI : Nonempty {θ : ℝ // θ < 0} := ⟨⟨-1, by norm_num⟩⟩
  exact le_ciInf fun θ => master_tail_lower hmeas hherm hR hindep t θ.2

end MasterBounds

end MatrixConcentration
