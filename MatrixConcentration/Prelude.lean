import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order

/-!
# Matrix concentration prelude

This merged prelude collects the foundational finite-dimensional matrix tools
used throughout the development:

1. **Book §§2.1.1 and 2.1.14:** the Euclidean vector norm and spectral/operator-norm toolkit;
2. **Book §§2.1.6–2.1.7:** extreme eigenvalues, Rayleigh quotients, and spectral identities;
3. **Book §§2.1.8–2.1.10:** the Loewner order and positive-semidefinite/positive-definite calculus.

The declarations are ordered by dependency: operator-norm tools, extreme
eigenvalues, then the Loewner-order calculus.
-/


set_option linter.unusedSectionVars false

/-!
# L2 operator norm toolkit

Supporting lemmas for the spectral norm (the L2 operator norm) of complex matrices,
as used throughout Tropp, *An Introduction to Matrix Concentration Inequalities*.
The book fixes `‖·‖` to be the spectral norm from §1.6 on ("Here and elsewhere,
`‖·‖` denotes the spectral norm"); in Lean this is the scoped
`Matrix.Norms.L2Operator` instance.

Contents:
* `l2norm` and its basic identities — Book §2.1.2, equation (2.1.1);
* the `mulVec`/dot-product characterizations of the operator norm;
* unitary invariance of the spectral norm (recovered prerequisite);
* `l2_opNorm_sq_mul_conjTranspose_self` — Book equation (2.1.24);
* `l2_opNorm_vecMulVec_star_self` — the implicit identity `‖xx*‖ = ‖x‖²` of §1.6.3;
* `l2_opNorm_replicateCol`/`l2_opNorm_replicateRow` — Book §2.1.14;
* `l2_opNorm_fromBlocks_diagonal` — the block-diagonal norm identity used
  for equation (2.2.10).
-/

namespace MatrixConcentration

open Matrix WithLp Finset
open scoped Matrix.Norms.L2Operator ComplexOrder

variable {m n l m₁ m₂ n₁ n₂ : Type*}
  [Fintype m] [Fintype n] [Fintype l] [Fintype m₁] [Fintype m₂] [Fintype n₁] [Fintype n₂]
  [DecidableEq m] [DecidableEq n] [DecidableEq l]
  [DecidableEq m₁] [DecidableEq m₂] [DecidableEq n₁] [DecidableEq n₂]

/-- **Book equation (2.1.1).**

Implicit source declaration. The ℓ₂ norm of a complex
vector, realized as the `EuclideanSpace` norm. -/
noncomputable def l2norm (x : n → ℂ) : ℝ := ‖(toLp 2 x : EuclideanSpace ℂ n)‖

/-- **Book equation (2.1.1).**

Mathlib correspondence lemma: `‖x‖ = √(∑ |xᵢ|²)`. -/
lemma l2norm_eq_sqrt_sum (x : n → ℂ) : l2norm x = √(∑ i, ‖x i‖ ^ 2) :=
  EuclideanSpace.norm_eq _

/-- **Book equation (2.1.1).**

Mathlib correspondence lemma: `‖x‖² = ∑ |xᵢ|²`. -/
lemma l2norm_sq (x : n → ℂ) : l2norm x ^ 2 = ∑ i, ‖x i‖ ^ 2 :=
  EuclideanSpace.norm_sq_eq _

/-- Lean implementation helper. -/
lemma l2norm_nonneg (x : n → ℂ) : 0 ≤ l2norm x := norm_nonneg _

/-- Lean implementation helper. -/
@[simp] lemma l2norm_zero : l2norm (0 : n → ℂ) = 0 := by
  simp [l2norm_eq_sqrt_sum]

/-- Lean implementation helper. -/
lemma l2norm_smul (c : ℂ) (x : n → ℂ) : l2norm (c • x) = ‖c‖ * l2norm x := by
  simp only [l2norm_eq_sqrt_sum, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, ← mul_sum]
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg c)]

/-- **Book §2.1.2, display before equation (2.1.1).** The book's inner
product `⟨x, y⟩ = x*y = ∑ x̄ᵢ yᵢ` is the `EuclideanSpace` inner product (conjugate-linear
in the first argument in both conventions). -/
lemma inner_toLp_eq_dotProduct (x y : n → ℂ) :
    (inner ℂ (toLp 2 x : EuclideanSpace ℂ n) (toLp 2 y)) = star x ⬝ᵥ y := by
  rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm]

/-- **Book equation (2.1.1).**

The identity `‖x‖² = ⟨x, x⟩`. -/
lemma dotProduct_star_self_eq (x : n → ℂ) :
    star x ⬝ᵥ x = ((l2norm x ^ 2 : ℝ) : ℂ) := by
  rw [← inner_toLp_eq_dotProduct, inner_self_eq_norm_sq_to_K]
  norm_num [l2norm]

/-- Lean implementation helper.

Cauchy–Schwarz for the ℓ₂ structure (source prerequisite recovered from context;
used for eq. (2.1.30) and the Rayleigh bounds). -/
lemma norm_dotProduct_le (x y : n → ℂ) : ‖star x ⬝ᵥ y‖ ≤ l2norm x * l2norm y := by
  rw [← inner_toLp_eq_dotProduct]
  exact norm_inner_le_norm (𝕜 := ℂ) _ _

/-- Lean implementation helper: `‖A *ᵥ x‖₂ ≤ ‖A‖ ‖x‖₂`, the defining property of the
operator norm in book coordinates. -/
lemma l2norm_mulVec_le (A : Matrix m n ℂ) (x : n → ℂ) :
    l2norm (A *ᵥ x) ≤ ‖A‖ * l2norm x := by
  simpa [l2norm] using A.l2_opNorm_mulVec (toLp 2 x)

/-- Lean implementation helper: upper bounds on the operator norm from vector bounds. -/
lemma l2_opNorm_le_bound (A : Matrix m n ℂ) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x : n → ℂ, l2norm (A *ᵥ x) ≤ c * l2norm x) : ‖A‖ ≤ c := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun x => ?_
  simpa [l2norm, Matrix.toLpLin_apply] using h (ofLp x)

/-- Lean implementation helper: lower bounds on the operator norm from a witness vector. -/
lemma le_l2_opNorm_of_witness (A : Matrix m n ℂ) {c : ℝ} (x : n → ℂ)
    (hx : l2norm x ≤ 1) (hc : c ≤ l2norm (A *ᵥ x)) : c ≤ ‖A‖ :=
  hc.trans ((l2norm_mulVec_le A x).trans
    (mul_le_of_le_one_right (norm_nonneg A) hx))

/-- Lean implementation helper.

Source prerequisite recovered from context (used at §2.1.16 line "the second
identity relies on a direct calculation"): a matrix is bounded by `c` on the quadratic
form level iff it is in operator norm. -/
lemma l2_opNorm_le_of_forall_dotProduct (A : Matrix m n ℂ) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ (u : m → ℂ) (v : n → ℂ), ‖star u ⬝ᵥ (A *ᵥ v)‖ ≤ c * l2norm u * l2norm v) :
    ‖A‖ ≤ c := by
  refine l2_opNorm_le_bound A hc fun x => ?_
  rcases eq_or_lt_of_le (l2norm_nonneg (A *ᵥ x)) with h0 | h0
  · rw [← h0]
    exact mul_nonneg hc (l2norm_nonneg x)
  · have h1 := h (A *ᵥ x) x
    rw [dotProduct_star_self_eq] at h1
    have h2 : ‖(((l2norm (A *ᵥ x) ^ 2 : ℝ)) : ℂ)‖ = l2norm (A *ᵥ x) ^ 2 := by
      rw [Complex.norm_real, Real.norm_of_nonneg (pow_nonneg (l2norm_nonneg _) 2)]
    rw [h2] at h1
    nlinarith [l2norm_nonneg x]

/-- Lean implementation helper.

Dot-product bound through a matrix (source prerequisite recovered from context;
used for Jensen's inequality (2.2.2) and the dilation identity (2.1.27)). -/
lemma norm_dotProduct_mulVec_le (A : Matrix m n ℂ) (u : m → ℂ) (v : n → ℂ) :
    ‖star u ⬝ᵥ (A *ᵥ v)‖ ≤ ‖A‖ * l2norm u * l2norm v := by
  calc ‖star u ⬝ᵥ (A *ᵥ v)‖ ≤ l2norm u * l2norm (A *ᵥ v) := norm_dotProduct_le _ _
    _ ≤ l2norm u * (‖A‖ * l2norm v) := by
        gcongr
        · exact l2norm_nonneg u
        · exact l2norm_mulVec_le A v
    _ = ‖A‖ * l2norm u * l2norm v := by ring

section Unitary

/-- Lean implementation helper.

Source prerequisite recovered from context (book §2.1.5: unitary matrices preserve
the ℓ₂ geometry). Multiplication by a unitary matrix preserves the ℓ₂ norm. -/
lemma l2norm_unitary_mulVec {U : Matrix m m ℂ} (hU : U ∈ Matrix.unitaryGroup m ℂ)
    (x : m → ℂ) : l2norm (U *ᵥ x) = l2norm x := by
  have hUU : Uᴴ * U = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.mp hU
    simpa [star_eq_conjTranspose] using h
  have key : star (U *ᵥ x) ⬝ᵥ (U *ᵥ x) = star x ⬝ᵥ x := by
    rw [star_mulVec, dotProduct_mulVec, vecMul_vecMul, hUU, vecMul_one]
  rw [dotProduct_star_self_eq, dotProduct_star_self_eq] at key
  have key' : l2norm (U *ᵥ x) ^ 2 = l2norm x ^ 2 := by exact_mod_cast key
  nlinarith [l2norm_nonneg (U *ᵥ x), l2norm_nonneg x]

/-- Lean implementation helper. -/
private lemma l2_opNorm_unitary_mul_le {U : Matrix m m ℂ}
    (hU : U ∈ Matrix.unitaryGroup m ℂ) (M : Matrix m n ℂ) : ‖U * M‖ ≤ ‖M‖ := by
  refine l2_opNorm_le_bound _ (norm_nonneg M) fun x => ?_
  rw [← Matrix.mulVec_mulVec, l2norm_unitary_mulVec hU]
  exact l2norm_mulVec_le M x

/-- Lean implementation helper.

Source prerequisite recovered from context: the spectral norm is invariant under
left multiplication by a unitary matrix. -/
lemma l2_opNorm_unitary_mul {U : Matrix m m ℂ} (hU : U ∈ Matrix.unitaryGroup m ℂ)
    (M : Matrix m n ℂ) : ‖U * M‖ = ‖M‖ := by
  refine le_antisymm (l2_opNorm_unitary_mul_le hU M) ?_
  have h1 : star U * (U * M) = M := by
    rw [← Matrix.mul_assoc, Matrix.mem_unitaryGroup_iff'.mp hU, Matrix.one_mul]
  calc ‖M‖ = ‖star U * (U * M)‖ := by rw [h1]
    _ ≤ ‖U * M‖ := l2_opNorm_unitary_mul_le (Unitary.star_mem hU) _

/-- Lean implementation helper.

Source prerequisite recovered from context: the spectral norm is invariant under
right multiplication by a unitary matrix. -/
lemma l2_opNorm_mul_unitary (M : Matrix m n ℂ) {V : Matrix n n ℂ}
    (hV : V ∈ Matrix.unitaryGroup n ℂ) : ‖M * V‖ = ‖M‖ := by
  have h1 : Vᴴ ∈ Matrix.unitaryGroup n ℂ := by
    simpa [star_eq_conjTranspose] using Unitary.star_mem hV
  calc ‖M * V‖ = ‖(M * V)ᴴ‖ := (Matrix.l2_opNorm_conjTranspose _).symm
    _ = ‖Vᴴ * Mᴴ‖ := by rw [conjTranspose_mul]
    _ = ‖Mᴴ‖ := l2_opNorm_unitary_mul h1 _
    _ = ‖M‖ := Matrix.l2_opNorm_conjTranspose _

/-- Lean implementation helper.

Source prerequisite recovered from context: unitary conjugation invariance. -/
lemma l2_opNorm_unitary_conj {U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ)
    (M : Matrix n n ℂ) : ‖U * M * Uᴴ‖ = ‖M‖ := by
  have h1 : Uᴴ ∈ Matrix.unitaryGroup n ℂ := by
    simpa [star_eq_conjTranspose] using Unitary.star_mem hU
  rw [l2_opNorm_mul_unitary _ h1, l2_opNorm_unitary_mul hU]

end Unitary

/-- **Book equation (2.1.24).**

First half: `‖B‖² = ‖BB*‖`. -/
lemma l2_opNorm_sq_mul_conjTranspose_self (B : Matrix m n ℂ) : ‖B * Bᴴ‖ = ‖B‖ ^ 2 := by
  calc ‖B * Bᴴ‖ = ‖(Bᴴ)ᴴ * Bᴴ‖ := by rw [conjTranspose_conjTranspose]
    _ = ‖Bᴴ‖ * ‖Bᴴ‖ := Matrix.l2_opNorm_conjTranspose_mul_self _
    _ = ‖B‖ ^ 2 := by rw [Matrix.l2_opNorm_conjTranspose, sq]

/-- **Book equation (2.1.24).**

Second half: `‖B‖² = ‖B*B‖`. -/
lemma l2_opNorm_sq_conjTranspose_mul_self (B : Matrix m n ℂ) : ‖Bᴴ * B‖ = ‖B‖ ^ 2 := by
  rw [Matrix.l2_opNorm_conjTranspose_mul_self, sq]

/-- **Book §1.6.3, p. 9.** The implicit identity
`‖xx*‖ = ‖x‖²` for the rank-one matrix `xx*`. Implicit source declaration. -/
lemma l2_opNorm_vecMulVec_star_self (x : n → ℂ) :
    ‖vecMulVec x (star x)‖ = l2norm x ^ 2 := by
  by_cases hx : x = 0
  · subst hx
    have hz : vecMulVec (0 : n → ℂ) (0 : n → ℂ) = 0 := by
      ext i j
      simp [vecMulVec_apply]
    simp [hz]
  · have hxn : 0 < l2norm x := by
      have hz : (toLp 2 x : EuclideanSpace ℂ n) ≠ 0 := by
        intro h
        apply hx
        have h' := congrArg ofLp h
        simpa using h'
      simpa [l2norm] using norm_pos_iff.mpr hz
    refine le_antisymm ?_ ?_
    · refine l2_opNorm_le_bound _ (by positivity) fun w => ?_
      rw [vecMulVec_mulVec, op_smul_eq_smul, l2norm_smul]
      calc ‖star x ⬝ᵥ w‖ * l2norm x ≤ (l2norm x * l2norm w) * l2norm x := by
            gcongr
            exact norm_dotProduct_le x w
        _ = l2norm x ^ 2 * l2norm w := by ring
    · have h1 : vecMulVec x (star x) *ᵥ x = ((l2norm x ^ 2 : ℝ) : ℂ) • x := by
        rw [vecMulVec_mulVec, op_smul_eq_smul, dotProduct_star_self_eq]
      have h2 : l2norm (vecMulVec x (star x) *ᵥ x) = l2norm x ^ 2 * l2norm x := by
        rw [h1, l2norm_smul, Complex.norm_real,
          Real.norm_of_nonneg (pow_nonneg (l2norm_nonneg _) 2)]
      have h3 := l2norm_mulVec_le (vecMulVec x (star x)) x
      rw [h2] at h3
      calc l2norm x ^ 2 = l2norm x ^ 2 * l2norm x / l2norm x := by field_simp
        _ ≤ ‖vecMulVec x (star x)‖ * l2norm x / l2norm x := by gcongr
        _ = ‖vecMulVec x (star x)‖ := by field_simp

/-- **Book §2.1.14, p. 24.**  "When applied to a … column vector, the spectral norm coincides
with the ℓ₂ norm (2.1.1)." Implicit source declaration. -/
lemma l2_opNorm_replicateCol (x : m → ℂ) :
    ‖Matrix.replicateCol Unit x‖ = l2norm x := by
  have h1 : ‖Matrix.replicateCol Unit x * (Matrix.replicateCol Unit x)ᴴ‖ =
      ‖Matrix.replicateCol Unit x‖ ^ 2 := l2_opNorm_sq_mul_conjTranspose_self _
  have h2 : Matrix.replicateCol Unit x * (Matrix.replicateCol Unit x)ᴴ =
      vecMulVec x (star x) := by
    ext i j
    simp [Matrix.mul_apply, vecMulVec_apply]
  rw [h2, l2_opNorm_vecMulVec_star_self] at h1
  have h3 : (0 : ℝ) ≤ ‖Matrix.replicateCol Unit x‖ := norm_nonneg _
  nlinarith [l2norm_nonneg x]

/-- **Book §2.1.14, p. 24.**  the row-vector case. Implicit source declaration. -/
lemma l2_opNorm_replicateRow (x : n → ℂ) :
    ‖Matrix.replicateRow Unit x‖ = l2norm (star x) := by
  have h1 : (Matrix.replicateRow Unit x)ᴴ = Matrix.replicateCol Unit (star x) := by
    ext i j
    simp
  calc ‖Matrix.replicateRow Unit x‖ = ‖(Matrix.replicateRow Unit x)ᴴ‖ :=
        (Matrix.l2_opNorm_conjTranspose _).symm
    _ = l2norm (star x) := by rw [h1, l2_opNorm_replicateCol]

section Blocks

/-- Lean implementation helper: the ℓ₂ norm of a concatenated vector. -/
lemma l2norm_sq_sum_elim (u : m₁ → ℂ) (v : m₂ → ℂ) :
    l2norm (Sum.elim u v) ^ 2 = l2norm u ^ 2 + l2norm v ^ 2 := by
  simp [l2norm_sq, Fintype.sum_sum_type]

/-- **Book §2.2.8, p. 29 ("the spectral norm of a block-diagonal matrix is the maximum
norm achieved by one of the diagonal blocks"). Implicit source declaration, stated in
prose in the source and used for eq. (2.2.10).**. -/
lemma l2_opNorm_fromBlocks_diagonal (A : Matrix m₁ n₁ ℂ) (D : Matrix m₂ n₂ ℂ) :
    ‖Matrix.fromBlocks A 0 0 D‖ = max ‖A‖ ‖D‖ := by
  refine le_antisymm ?_ (max_le ?_ ?_)
  · refine l2_opNorm_le_bound _ (le_max_of_le_left (norm_nonneg A)) fun x => ?_
    rw [fromBlocks_mulVec]
    simp only [Matrix.zero_mulVec, add_zero, zero_add]
    have hc0 : (0 : ℝ) ≤ max ‖A‖ ‖D‖ := le_max_of_le_left (norm_nonneg A)
    have hs : l2norm (Sum.elim (A *ᵥ (x ∘ Sum.inl)) (D *ᵥ (x ∘ Sum.inr))) ^ 2 ≤
        (max ‖A‖ ‖D‖ * l2norm x) ^ 2 := by
      rw [l2norm_sq_sum_elim]
      have hA1 : l2norm (A *ᵥ (x ∘ Sum.inl)) ≤ max ‖A‖ ‖D‖ * l2norm (x ∘ Sum.inl) :=
        (l2norm_mulVec_le A _).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (l2norm_nonneg _))
      have hD1 : l2norm (D *ᵥ (x ∘ Sum.inr)) ≤ max ‖A‖ ‖D‖ * l2norm (x ∘ Sum.inr) :=
        (l2norm_mulVec_le D _).trans
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (l2norm_nonneg _))
      have hA2 := mul_self_le_mul_self (l2norm_nonneg (A *ᵥ (x ∘ Sum.inl))) hA1
      have hD2 := mul_self_le_mul_self (l2norm_nonneg (D *ᵥ (x ∘ Sum.inr))) hD1
      have hxsplit : l2norm x ^ 2 = l2norm (x ∘ Sum.inl) ^ 2 + l2norm (x ∘ Sum.inr) ^ 2 := by
        conv_lhs => rw [← Sum.elim_comp_inl_inr x]
        exact l2norm_sq_sum_elim _ _
      have key : (max ‖A‖ ‖D‖ * l2norm x) ^ 2 =
          (max ‖A‖ ‖D‖ * l2norm (x ∘ Sum.inl)) ^ 2 +
            (max ‖A‖ ‖D‖ * l2norm (x ∘ Sum.inr)) ^ 2 := by
        rw [mul_pow, mul_pow, mul_pow, hxsplit]
        ring
      nlinarith [hA2, hD2, key]
    have h1 : 0 ≤ max ‖A‖ ‖D‖ * l2norm x := mul_nonneg hc0 (l2norm_nonneg x)
    nlinarith [l2norm_nonneg (Sum.elim (A *ᵥ (x ∘ Sum.inl)) (D *ᵥ (x ∘ Sum.inr))), hs, h1]
  · refine l2_opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    have h1 : Matrix.fromBlocks A 0 0 D *ᵥ Sum.elim x (0 : n₂ → ℂ) =
        Sum.elim (A *ᵥ x) (0 : m₂ → ℂ) := by
      rw [fromBlocks_mulVec]
      simp [Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.zero_mulVec, Matrix.mulVec_zero]
    have h2 : l2norm (A *ᵥ x) =
        l2norm (Matrix.fromBlocks A 0 0 D *ᵥ Sum.elim x (0 : n₂ → ℂ)) := by
      rw [h1]
      have := l2norm_sq_sum_elim (A *ᵥ x) (0 : m₂ → ℂ)
      simp only [l2norm_zero] at this
      nlinarith [l2norm_nonneg (Sum.elim (A *ᵥ x) (0 : m₂ → ℂ)), l2norm_nonneg (A *ᵥ x)]
    have h3 : l2norm (Sum.elim x (0 : n₂ → ℂ)) = l2norm x := by
      have := l2norm_sq_sum_elim x (0 : n₂ → ℂ)
      simp only [l2norm_zero] at this
      nlinarith [l2norm_nonneg (Sum.elim x (0 : n₂ → ℂ)), l2norm_nonneg x]
    rw [h2, ← h3]
    exact l2norm_mulVec_le _ _
  · refine l2_opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    have h1 : Matrix.fromBlocks A 0 0 D *ᵥ Sum.elim (0 : n₁ → ℂ) x =
        Sum.elim (0 : m₁ → ℂ) (D *ᵥ x) := by
      rw [fromBlocks_mulVec]
      simp [Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.zero_mulVec, Matrix.mulVec_zero]
    have h2 : l2norm (D *ᵥ x) =
        l2norm (Matrix.fromBlocks A 0 0 D *ᵥ Sum.elim (0 : n₁ → ℂ) x) := by
      rw [h1]
      have := l2norm_sq_sum_elim (0 : m₁ → ℂ) (D *ᵥ x)
      simp only [l2norm_zero] at this
      nlinarith [l2norm_nonneg (Sum.elim (0 : m₁ → ℂ) (D *ᵥ x)), l2norm_nonneg (D *ᵥ x)]
    have h3 : l2norm (Sum.elim (0 : n₁ → ℂ) x) = l2norm x := by
      have := l2norm_sq_sum_elim (0 : n₁ → ℂ) x
      simp only [l2norm_zero] at this
      nlinarith [l2norm_nonneg (Sum.elim (0 : n₁ → ℂ) x), l2norm_nonneg x]
    rw [h2, ← h3]
    exact l2norm_mulVec_le _ _

end Blocks

end MatrixConcentration


set_option linter.unusedSectionVars false

/-!
# Extreme eigenvalues of Hermitian matrices

Formalizes the eigenvalue material of Tropp §2.1.6 (book pp. 19–20) together with
the Rayleigh-quotient toolkit that the book uses implicitly (e.g. at §2.1.16:
"the variational representation of the maximum eigenvalue as a Rayleigh quotient").

* `lambdaMax`/`lambdaMin` — the maps `λ_max`, `λ_min` of §2.1.6 (implicit definitions);
* `spectral_decomposition` — book eq. (2.1.3) `2.1.3`;
* `eigenvalues_multiset_unique` — "the list of eigenvalues is unique modulo
  permutations" (implicit well-definedness claim, p. 19);
* `lambdaMax_smul_nonneg`, `lambdaMin_smul_nonneg` — book eq. (2.1.4) `2.1.4`;
* `lambdaMin_neg`, `lambdaMax_neg` — book eq. (2.1.5) `2.1.5`;
* `l2_opNorm_eq_max_lambda` — book eq. (2.1.22) `2.1.22`;
* `posSemidef_l2_opNorm_eq_lambdaMax`, `lambdaMax_le_of_loewner_le`,
  `trace_cfc_eq_sum` — recovered prerequisites for §2.1.11 and Chapter 3.
-/

namespace MatrixConcentration

open Matrix WithLp Finset
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {A B H : Matrix n n ℂ}

/-- **Book §2.1.6, p. 19. Implicit source declaration.**  the algebraic maximum eigenvalue
`λ_max(A)` of a Hermitian matrix. (Junk value `0` for `0 × 0` matrices.) -/
noncomputable def lambdaMax (hA : A.IsHermitian) : ℝ := ⨆ i, hA.eigenvalues i

/-- **Book §2.1.6, p. 19. Implicit source declaration.**  the algebraic minimum eigenvalue. -/
noncomputable def lambdaMin (hA : A.IsHermitian) : ℝ := ⨅ i, hA.eigenvalues i

/-- Lean implementation helper. -/
lemma lambdaMax_of_isEmpty [IsEmpty n] (hA : A.IsHermitian) : lambdaMax hA = 0 :=
  Real.iSup_of_isEmpty _

/-- Lean implementation helper. -/
lemma lambdaMin_of_isEmpty [IsEmpty n] (hA : A.IsHermitian) : lambdaMin hA = 0 :=
  Real.iInf_of_isEmpty _

/-- Lean implementation helper. -/
lemma eigenvalues_le_lambdaMax (hA : A.IsHermitian) (i : n) :
    hA.eigenvalues i ≤ lambdaMax hA :=
  le_ciSup (Set.Finite.bddAbove (Set.finite_range _)) i

/-- Lean implementation helper. -/
lemma lambdaMin_le_eigenvalues (hA : A.IsHermitian) (i : n) :
    lambdaMin hA ≤ hA.eigenvalues i :=
  ciInf_le (Set.Finite.bddBelow (Set.finite_range _)) i

/-- Lean implementation helper. -/
lemma lambdaMax_le [Nonempty n] (hA : A.IsHermitian) {c : ℝ}
    (h : ∀ i, hA.eigenvalues i ≤ c) : lambdaMax hA ≤ c := ciSup_le h

/-- Lean implementation helper. -/
lemma le_lambdaMin [Nonempty n] (hA : A.IsHermitian) {c : ℝ}
    (h : ∀ i, c ≤ hA.eigenvalues i) : c ≤ lambdaMin hA := le_ciInf h

/-- Lean implementation helper. -/
lemma lambdaMin_le_lambdaMax [Nonempty n] (hA : A.IsHermitian) :
    lambdaMin hA ≤ lambdaMax hA :=
  (lambdaMin_le_eigenvalues hA (Classical.arbitrary n)).trans
    (eigenvalues_le_lambdaMax hA _)

/-- Lean implementation helper. -/
lemma exists_eigenvalues_eq_lambdaMax [Nonempty n] (hA : A.IsHermitian) :
    ∃ i, hA.eigenvalues i = lambdaMax hA := by
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ hA.eigenvalues univ_nonempty
  exact ⟨i, le_antisymm (eigenvalues_le_lambdaMax hA i)
    (lambdaMax_le hA fun j => hi j (mem_univ j))⟩

/-- Lean implementation helper. -/
lemma exists_eigenvalues_eq_lambdaMin [Nonempty n] (hA : A.IsHermitian) :
    ∃ i, hA.eigenvalues i = lambdaMin hA := by
  obtain ⟨i, -, hi⟩ := Finset.exists_min_image Finset.univ hA.eigenvalues univ_nonempty
  exact ⟨i, le_antisymm (le_lambdaMin hA fun j => hi j (mem_univ j))
    (lambdaMin_le_eigenvalues hA i)⟩

section Spectral

/-- Lean implementation helper: for `ℂ`, the `RCLike` real embedding is the standard one. -/
lemma ofReal_eq_complex (r : ℝ) : (RCLike.ofReal r : ℂ) = (r : ℂ) := rfl

/-- **Book equation (2.1.3).**

`2.1.3` (§2.1.6): every Hermitian matrix has
an eigenvalue decomposition `A = Q Λ Q*` with `Q` unitary and `Λ` real diagonal.
Explicit (unnumbered) source statement; Mathlib correspondence
(`Matrix.IsHermitian.spectral_theorem`) restated in the book's orientation. -/
lemma spectral_decomposition (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix n n ℂ) *
      diagonal (RCLike.ofReal ∘ hA.eigenvalues) *
      (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
  conv_lhs => rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply]
  rfl

/-- Lean implementation helper: unitary conjugation seen through the quadratic form. -/
lemma star_dotProduct_conj_mulVec (M U : Matrix n n ℂ) (u : n → ℂ) :
    star u ⬝ᵥ ((U * M * Uᴴ) *ᵥ u) = star (Uᴴ *ᵥ u) ⬝ᵥ (M *ᵥ (Uᴴ *ᵥ u)) := by
  have hst : star (Uᴴ *ᵥ u) = star u ᵥ* U := by
    rw [star_mulVec, conjTranspose_conjTranspose]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec, hst]

/-- Lean implementation helper: the quadratic form of a real-diagonal matrix. -/
lemma star_dotProduct_diagonal_mulVec (d : n → ℝ) (c : n → ℂ) :
    star c ⬝ᵥ (diagonal (RCLike.ofReal ∘ d) *ᵥ c) = ((∑ i, d i * ‖c i‖ ^ 2 : ℝ) : ℂ) := by
  have key : ∀ i, (star c) i * (diagonal (RCLike.ofReal ∘ d) *ᵥ c) i
      = ((d i * ‖c i‖ ^ 2 : ℝ) : ℂ) := fun i => by
    rw [Matrix.mulVec_diagonal]
    have h2 : (starRingEnd ℂ) (c i) * c i = ((‖c i‖ ^ 2 : ℝ) : ℂ) := by
      rw [RCLike.conj_mul (c i)]
      simp only [ofReal_eq_complex]
      norm_cast
    calc (star c) i * ((RCLike.ofReal ∘ d) i * c i)
        = ((d i : ℝ) : ℂ) * ((starRingEnd ℂ) (c i) * c i) := by
          simp only [Pi.star_apply, RCLike.star_def, Function.comp_apply, ofReal_eq_complex]
          ring
      _ = ((d i : ℝ) : ℂ) * ((‖c i‖ ^ 2 : ℝ) : ℂ) := by rw [h2]
      _ = ((d i * ‖c i‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [dotProduct, Finset.sum_congr rfl fun i _ => key i]
  push_cast
  ring

/-- Lean implementation helper.

Source prerequisite recovered from context (workhorse for the Rayleigh bounds of
§2.1.6/§2.1.16): the quadratic form expands over any unitary real-diagonalization. -/
lemma star_dotProduct_mulVec_eq_sum {U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ)
    {d : n → ℝ} (hAeq : A = U * diagonal (RCLike.ofReal ∘ d) * Uᴴ) (u : n → ℂ) :
    star u ⬝ᵥ (A *ᵥ u) = ((∑ i, d i * ‖(Uᴴ *ᵥ u) i‖ ^ 2 : ℝ) : ℂ) := by
  rw [hAeq, star_dotProduct_conj_mulVec, star_dotProduct_diagonal_mulVec]

/-- Lean implementation helper: coordinates w.r.t. a unitary basis carry the ℓ₂ mass. -/
lemma sum_norm_sq_conjTranspose_mulVec {U : Matrix n n ℂ}
    (hU : U ∈ Matrix.unitaryGroup n ℂ) (u : n → ℂ) :
    ∑ i, ‖(Uᴴ *ᵥ u) i‖ ^ 2 = l2norm u ^ 2 := by
  have h1 : Uᴴ ∈ Matrix.unitaryGroup n ℂ := by
    simpa [star_eq_conjTranspose] using Unitary.star_mem hU
  rw [← l2norm_sq, l2norm_unitary_mulVec h1]

end Spectral

section Rayleigh

/-- Lean implementation helper.

Source prerequisite recovered from context (book §2.1.16, "the variational
representation of the maximum eigenvalue as a Rayleigh quotient"): the (real)
Rayleigh value `u*Au` of a matrix at a vector. -/
noncomputable def rayleigh (A : Matrix n n ℂ) (u : n → ℂ) : ℝ :=
  (star u ⬝ᵥ (A *ᵥ u)).re

/-- Lean implementation helper.

For Hermitian `A`, the quadratic form `u*Au` is real, with value `rayleigh A u`. -/
lemma rayleigh_eq_sum (hA : A.IsHermitian) (u : n → ℂ) :
    rayleigh A u = ∑ i, hA.eigenvalues i *
      ‖((hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ *ᵥ u) i‖ ^ 2 := by
  have h := star_dotProduct_mulVec_eq_sum hA.eigenvectorUnitary.2
    (spectral_decomposition hA) u
  rw [show rayleigh A u = (star u ⬝ᵥ (A *ᵥ u)).re from rfl, h]
  exact Complex.ofReal_re _

/-- Lean implementation helper. -/
lemma star_dotProduct_mulVec_eq_rayleigh (hA : A.IsHermitian) (u : n → ℂ) :
    star u ⬝ᵥ (A *ᵥ u) = ((rayleigh A u : ℝ) : ℂ) := by
  have h := star_dotProduct_mulVec_eq_sum hA.eigenvectorUnitary.2
    (spectral_decomposition hA) u
  rw [h, rayleigh_eq_sum hA u]

/-- Lean implementation helper.

Rayleigh upper bound: `u*Au ≤ λ_max(A) ‖u‖²`. Source prerequisite recovered from
context (used implicitly throughout §2.1 and Chapter 3). -/
lemma rayleigh_le_lambdaMax (hA : A.IsHermitian) (u : n → ℂ) :
    rayleigh A u ≤ lambdaMax hA * l2norm u ^ 2 := by
  rw [rayleigh_eq_sum hA u, ← sum_norm_sq_conjTranspose_mulVec hA.eigenvectorUnitary.2 u,
    Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_right (eigenvalues_le_lambdaMax hA i) (by positivity)

/-- Lean implementation helper.

Rayleigh lower bound: `λ_min(A) ‖u‖² ≤ u*Au`. -/
lemma lambdaMin_le_rayleigh (hA : A.IsHermitian) (u : n → ℂ) :
    lambdaMin hA * l2norm u ^ 2 ≤ rayleigh A u := by
  rw [rayleigh_eq_sum hA u, ← sum_norm_sq_conjTranspose_mulVec hA.eigenvectorUnitary.2 u,
    Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_right (lambdaMin_le_eigenvalues hA i) (by positivity)

/-- Lean implementation helper: eigenvector columns are ℓ₂-unit vectors. -/
lemma l2norm_eigenvectorBasis (hA : A.IsHermitian) (i : n) :
    l2norm (⇑(hA.eigenvectorBasis i)) = 1 := by
  have h1 : l2norm (⇑(hA.eigenvectorBasis i)) ^ 2 = ‖hA.eigenvectorBasis i‖ ^ 2 := by
    rw [l2norm_sq, EuclideanSpace.norm_sq_eq]
  have h2 : ‖hA.eigenvectorBasis i‖ = 1 := hA.eigenvectorBasis.orthonormal.1 i
  rw [h2] at h1
  nlinarith [l2norm_nonneg (⇑(hA.eigenvectorBasis i))]

/-- Lean implementation helper.

Every eigenvalue is a Rayleigh value at a unit eigenvector. -/
lemma rayleigh_eigenvectorBasis (hA : A.IsHermitian) (i : n) :
    rayleigh A (⇑(hA.eigenvectorBasis i)) = hA.eigenvalues i := by
  have h1 : A *ᵥ ⇑(hA.eigenvectorBasis i) = hA.eigenvalues i • ⇑(hA.eigenvectorBasis i) :=
    hA.mulVec_eigenvectorBasis i
  rw [rayleigh, h1, dotProduct_smul]
  rw [dotProduct_star_self_eq, l2norm_eigenvectorBasis hA i]
  norm_num

/-- Lean implementation helper.

Attainment of `λ_max` as a Rayleigh value at a unit vector. -/
lemma exists_unit_rayleigh_eq_lambdaMax [Nonempty n] (hA : A.IsHermitian) :
    ∃ u : n → ℂ, l2norm u = 1 ∧ rayleigh A u = lambdaMax hA := by
  obtain ⟨i, hi⟩ := exists_eigenvalues_eq_lambdaMax hA
  exact ⟨⇑(hA.eigenvectorBasis i), l2norm_eigenvectorBasis hA i,
    (rayleigh_eigenvectorBasis hA i).trans hi⟩

/-- Lean implementation helper.

Attainment of `λ_min` as a Rayleigh value at a unit vector. -/
lemma exists_unit_rayleigh_eq_lambdaMin [Nonempty n] (hA : A.IsHermitian) :
    ∃ u : n → ℂ, l2norm u = 1 ∧ rayleigh A u = lambdaMin hA := by
  obtain ⟨i, hi⟩ := exists_eigenvalues_eq_lambdaMin hA
  exact ⟨⇑(hA.eigenvectorBasis i), l2norm_eigenvectorBasis hA i,
    (rayleigh_eigenvectorBasis hA i).trans hi⟩

/-- Lean implementation helper. -/
lemma lambdaMax_le_of_forall_rayleigh [Nonempty n] (hA : A.IsHermitian) {c : ℝ}
    (h : ∀ u : n → ℂ, l2norm u = 1 → rayleigh A u ≤ c) : lambdaMax hA ≤ c := by
  obtain ⟨u, hu1, hu2⟩ := exists_unit_rayleigh_eq_lambdaMax hA
  rw [← hu2]
  exact h u hu1

/-- Lean implementation helper. -/
lemma le_lambdaMin_of_forall_rayleigh [Nonempty n] (hA : A.IsHermitian) {c : ℝ}
    (h : ∀ u : n → ℂ, l2norm u = 1 → c ≤ rayleigh A u) : c ≤ lambdaMin hA := by
  obtain ⟨u, hu1, hu2⟩ := exists_unit_rayleigh_eq_lambdaMin hA
  rw [← hu2]
  exact h u hu1

/-- Lean implementation helper. -/
lemma rayleigh_le_lambdaMax_of_unit (hA : A.IsHermitian) {u : n → ℂ}
    (hu : l2norm u = 1) : rayleigh A u ≤ lambdaMax hA := by
  have := rayleigh_le_lambdaMax hA u
  rwa [hu, one_pow, mul_one] at this

/-- Lean implementation helper. -/
lemma lambdaMin_le_rayleigh_of_unit (hA : A.IsHermitian) {u : n → ℂ}
    (hu : l2norm u = 1) : lambdaMin hA ≤ rayleigh A u := by
  have := lambdaMin_le_rayleigh hA u
  rwa [hu, one_pow, mul_one] at this

/-- Algebraic behaviour of the Rayleigh value. Lean implementation helpers. -/
lemma rayleigh_neg (A : Matrix n n ℂ) (u : n → ℂ) : rayleigh (-A) u = - rayleigh A u := by
  simp [rayleigh, Matrix.neg_mulVec]

/-- Lean implementation helper. -/
lemma rayleigh_smul (α : ℝ) (A : Matrix n n ℂ) (u : n → ℂ) :
    rayleigh (α • A) u = α * rayleigh A u := by
  rw [rayleigh, Matrix.smul_mulVec, dotProduct_smul, rayleigh]
  simp [Complex.real_smul]

/-- Lean implementation helper. -/
lemma rayleigh_sub (A B : Matrix n n ℂ) (u : n → ℂ) :
    rayleigh (A - B) u = rayleigh A u - rayleigh B u := by
  simp [rayleigh, Matrix.sub_mulVec, dotProduct_sub]

end Rayleigh

section Comparisons

/-- **Book equation (2.1.4).**

`2.1.4` (§2.1.6): `λ_max(αA) = α λ_max(A)` for `α ≥ 0`.
Explicit (unnumbered) source statement. -/
lemma lambdaMax_smul_nonneg (hA : A.IsHermitian) {α : ℝ} (hα : 0 ≤ α)
    (hαA : (α • A).IsHermitian) : lambdaMax hαA = α * lambdaMax hA := by
  cases isEmpty_or_nonempty n
  · rw [lambdaMax_of_isEmpty, lambdaMax_of_isEmpty, mul_zero]
  · refine le_antisymm ?_ ?_
    · refine lambdaMax_le_of_forall_rayleigh hαA fun u hu => ?_
      rw [rayleigh_smul]
      exact mul_le_mul_of_nonneg_left (rayleigh_le_lambdaMax_of_unit hA hu) hα
    · obtain ⟨u, hu1, hu2⟩ := exists_unit_rayleigh_eq_lambdaMax hA
      calc α * lambdaMax hA = rayleigh (α • A) u := by rw [rayleigh_smul, hu2]
        _ ≤ lambdaMax hαA := rayleigh_le_lambdaMax_of_unit hαA hu1

/-- **Book equation (2.1.4).**

`2.1.4`: the `λ_min` half. -/
lemma lambdaMin_smul_nonneg (hA : A.IsHermitian) {α : ℝ} (hα : 0 ≤ α)
    (hαA : (α • A).IsHermitian) : lambdaMin hαA = α * lambdaMin hA := by
  cases isEmpty_or_nonempty n
  · rw [lambdaMin_of_isEmpty, lambdaMin_of_isEmpty, mul_zero]
  · refine le_antisymm ?_ ?_
    · obtain ⟨u, hu1, hu2⟩ := exists_unit_rayleigh_eq_lambdaMin hA
      calc lambdaMin hαA ≤ rayleigh (α • A) u := lambdaMin_le_rayleigh_of_unit hαA hu1
        _ = α * lambdaMin hA := by rw [rayleigh_smul, hu2]
    · refine le_lambdaMin_of_forall_rayleigh hαA fun u hu => ?_
      rw [rayleigh_smul]
      exact mul_le_mul_of_nonneg_left (lambdaMin_le_rayleigh_of_unit hA hu) hα

/-- **Book equation (2.1.5).**

`2.1.5` (§2.1.6): `λ_min(−A) = −λ_max(A)`.
Explicit (unnumbered) source statement. -/
lemma lambdaMin_neg (hA : A.IsHermitian) : lambdaMin hA.neg = - lambdaMax hA := by
  cases isEmpty_or_nonempty n
  · rw [lambdaMin_of_isEmpty, lambdaMax_of_isEmpty, neg_zero]
  · refine le_antisymm ?_ ?_
    · obtain ⟨u, hu1, hu2⟩ := exists_unit_rayleigh_eq_lambdaMax hA
      calc lambdaMin hA.neg ≤ rayleigh (-A) u := lambdaMin_le_rayleigh_of_unit hA.neg hu1
        _ = - lambdaMax hA := by rw [rayleigh_neg, hu2]
    · refine le_lambdaMin_of_forall_rayleigh hA.neg fun u hu => ?_
      rw [rayleigh_neg, neg_le_neg_iff]
      exact rayleigh_le_lambdaMax_of_unit hA hu

/-- **Book §2.1.5.**

Companion to (2.1.5): `λ_max(−A) = −λ_min(A)`. Implicit source declaration. -/
lemma lambdaMax_neg (hA : A.IsHermitian) : lambdaMax hA.neg = - lambdaMin hA := by
  cases isEmpty_or_nonempty n
  · rw [lambdaMax_of_isEmpty, lambdaMin_of_isEmpty, neg_zero]
  · refine le_antisymm ?_ ?_
    · refine lambdaMax_le_of_forall_rayleigh hA.neg fun u hu => ?_
      rw [rayleigh_neg]
      exact neg_le_neg (lambdaMin_le_rayleigh_of_unit hA hu)
    · obtain ⟨u, hu1, hu2⟩ := exists_unit_rayleigh_eq_lambdaMin hA
      calc -(lambdaMin hA) = rayleigh (-A) u := by rw [rayleigh_neg, hu2]
        _ ≤ lambdaMax hA.neg := rayleigh_le_lambdaMax_of_unit hA.neg hu1

/-- Lean implementation helper.

Monotonicity of `λ_max` in the semidefinite order (source prerequisite recovered
from context; used by Chapter 3 and by (2.1.16)). -/
lemma lambdaMax_le_of_loewner_le (hA : A.IsHermitian) (hH : H.IsHermitian)
    (hle : A ≤ H) : lambdaMax hA ≤ lambdaMax hH := by
  cases isEmpty_or_nonempty n
  · rw [lambdaMax_of_isEmpty, lambdaMax_of_isEmpty]
  · refine lambdaMax_le_of_forall_rayleigh hA fun u hu => ?_
    have h1 : rayleigh A u ≤ rayleigh H u := by
      have h2 : (0 : ℝ) ≤ rayleigh (H - A) u :=
        (Matrix.le_iff.mp hle).re_dotProduct_nonneg u
      rw [rayleigh_sub] at h2
      linarith
    exact h1.trans (rayleigh_le_lambdaMax_of_unit hH hu)

/-- Lean implementation helper.

Monotonicity of `λ_min` in the semidefinite order. -/
lemma lambdaMin_le_of_loewner_le (hA : A.IsHermitian) (hH : H.IsHermitian)
    (hle : A ≤ H) : lambdaMin hA ≤ lambdaMin hH := by
  cases isEmpty_or_nonempty n
  · rw [lambdaMin_of_isEmpty, lambdaMin_of_isEmpty]
  · obtain ⟨u, hu1, hu2⟩ := exists_unit_rayleigh_eq_lambdaMin hH
    rw [← hu2]
    have h1 : rayleigh A u ≤ rayleigh H u := by
      have h2 : (0 : ℝ) ≤ rayleigh (H - A) u :=
        (Matrix.le_iff.mp hle).re_dotProduct_nonneg u
      rw [rayleigh_sub] at h2
      linarith
    exact (lambdaMin_le_rayleigh_of_unit hA hu1).trans h1

/-- Invariance of `λ_max` under unitary conjugation. Lean implementation helper
(used for the Hermitian dilation, §2.1.16). -/
lemma lambdaMax_unitary_conj {U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ)
    (hA : A.IsHermitian) (hB : (U * A * Uᴴ).IsHermitian) :
    lambdaMax hB = lambdaMax hA := by
  cases isEmpty_or_nonempty n
  · rw [lambdaMax_of_isEmpty, lambdaMax_of_isEmpty]
  · have hUs : Uᴴ ∈ Matrix.unitaryGroup n ℂ := by
      simpa [star_eq_conjTranspose] using Unitary.star_mem hU
    have hray : ∀ u : n → ℂ, rayleigh (U * A * Uᴴ) u = rayleigh A (Uᴴ *ᵥ u) := fun u => by
      rw [rayleigh, star_dotProduct_conj_mulVec, rayleigh]
    refine le_antisymm ?_ ?_
    · refine lambdaMax_le_of_forall_rayleigh hB fun u hu => ?_
      rw [hray u]
      have h1 : l2norm (Uᴴ *ᵥ u) = 1 := by rw [l2norm_unitary_mulVec hUs, hu]
      exact rayleigh_le_lambdaMax_of_unit hA h1
    · obtain ⟨u, hu1, hu2⟩ := exists_unit_rayleigh_eq_lambdaMax hA
      have h1 : l2norm (U *ᵥ u) = 1 := by rw [l2norm_unitary_mulVec hU, hu1]
      have h2 : rayleigh (U * A * Uᴴ) (U *ᵥ u) = rayleigh A u := by
        rw [hray (U *ᵥ u)]
        congr 2
        rw [Matrix.mulVec_mulVec]
        have hUU : Uᴴ * U = 1 := by
          have h := Matrix.mem_unitaryGroup_iff'.mp hU
          simpa [star_eq_conjTranspose] using h
        rw [hUU, Matrix.one_mulVec]
      calc lambdaMax hA = rayleigh (U * A * Uᴴ) (U *ᵥ u) := by rw [h2, hu2]
        _ ≤ lambdaMax hB := rayleigh_le_lambdaMax_of_unit hB h1

end Comparisons

section Uniqueness

/-- **Book §2.1.6, p. 19.**  "The unitary matrix Q in the eigenvalue decomposition is not
determined completely, but the list of eigenvalues is unique modulo permutations."
Implicit source declaration (well-definedness of the eigenvalue list): any unitary
real-diagonalization of `A` exhibits the same multiset of diagonal values as
`hA.eigenvalues`. -/
theorem eigenvalues_multiset_unique (hA : A.IsHermitian) {U : Matrix n n ℂ}
    (hU : U ∈ Matrix.unitaryGroup n ℂ) {d : n → ℝ}
    (hAeq : A = U * diagonal (RCLike.ofReal ∘ d) * Uᴴ) :
    Multiset.map d Finset.univ.val = Multiset.map hA.eigenvalues Finset.univ.val := by
  have hUU : Uᴴ * U = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.mp hU
    simpa [star_eq_conjTranspose] using h
  have hchar : A.charpoly = (diagonal (RCLike.ofReal ∘ d)).charpoly := by
    rw [hAeq, Matrix.mul_assoc, Matrix.charpoly_mul_comm, Matrix.mul_assoc, hUU,
      Matrix.mul_one]
  have hmap : Multiset.map (fun i => Polynomial.X - Polynomial.C ((RCLike.ofReal ∘ d) i : ℂ))
      Finset.univ.val =
      Multiset.map (fun a => Polynomial.X - Polynomial.C a)
        (Multiset.map (fun i => ((RCLike.ofReal ∘ d) i : ℂ)) Finset.univ.val) := by
    rw [Multiset.map_map]
    rfl
  have hroots : A.charpoly.roots =
      Multiset.map (fun i => ((RCLike.ofReal ∘ d) i : ℂ)) Finset.univ.val := by
    rw [hchar, Matrix.charpoly_diagonal, Finset.prod_eq_multiset_prod, hmap,
      Polynomial.roots_multiset_prod_X_sub_C]
  rw [hA.roots_charpoly_eq_eigenvalues] at hroots
  have hinj : Function.Injective (RCLike.ofReal : ℝ → ℂ) := RCLike.ofReal_injective
  apply Multiset.map_injective hinj
  rw [Multiset.map_map, Multiset.map_map]
  exact hroots.symm.trans rfl

end Uniqueness

section Norms

/-- Lean implementation helper: `max(λ_max, −λ_min) ≥ 0`. -/
lemma max_lambdaMax_neg_lambdaMin_nonneg (hA : A.IsHermitian) :
    0 ≤ max (lambdaMax hA) (-(lambdaMin hA)) := by
  cases isEmpty_or_nonempty n
  · rw [lambdaMax_of_isEmpty, lambdaMin_of_isEmpty, neg_zero, max_self]
  · rcases le_total 0 (lambdaMax hA) with h | h
    · exact le_max_of_le_left h
    · refine le_max_of_le_right ?_
      have := lambdaMin_le_lambdaMax hA
      linarith

/-- **Book equation (2.1.22).**

`2.1.22` (§2.1.14): for a Hermitian matrix,
`‖A‖ = max{λ_max(A), −λ_min(A)}`. Explicit (unnumbered) source statement; this is the
correspondence between the book's definition of the spectral norm on Hermitian matrices
and Mathlib's L2 operator norm. -/
theorem l2_opNorm_eq_max_lambda (hA : A.IsHermitian) :
    ‖A‖ = max (lambdaMax hA) (-(lambdaMin hA)) := by
  refine le_antisymm ?_ (max_le ?_ ?_)
  · have hnorm : ‖A‖ =
        ‖(diagonal (RCLike.ofReal ∘ hA.eigenvalues) : Matrix n n ℂ)‖ := by
      conv_lhs => rw [spectral_decomposition hA]
      exact l2_opNorm_unitary_conj hA.eigenvectorUnitary.2 _
    rw [hnorm, Matrix.l2_opNorm_diagonal]
    refine (pi_norm_le_iff_of_nonneg (max_lambdaMax_neg_lambdaMin_nonneg hA)).mpr fun i => ?_
    rw [Function.comp_apply, RCLike.norm_ofReal, abs_le]
    constructor
    · have := lambdaMin_le_eigenvalues hA i
      have h2 : -(max (lambdaMax hA) (-(lambdaMin hA))) ≤ lambdaMin hA := by
        have h3 : -(lambdaMin hA) ≤ max (lambdaMax hA) (-(lambdaMin hA)) := le_max_right _ _
        linarith
      linarith
    · exact (eigenvalues_le_lambdaMax hA i).trans (le_max_left _ _)
  · cases isEmpty_or_nonempty n
    · rw [lambdaMax_of_isEmpty]
      exact norm_nonneg A
    · refine lambdaMax_le_of_forall_rayleigh hA fun u hu => ?_
      calc rayleigh A u ≤ ‖star u ⬝ᵥ (A *ᵥ u)‖ := Complex.re_le_norm _
        _ ≤ ‖A‖ * l2norm u * l2norm u := norm_dotProduct_mulVec_le A u u
        _ = ‖A‖ := by rw [hu, mul_one, mul_one]
  · cases isEmpty_or_nonempty n
    · rw [lambdaMin_of_isEmpty, neg_zero]
      exact norm_nonneg A
    · rw [neg_le]
      refine le_lambdaMin_of_forall_rayleigh hA fun u hu => ?_
      have h1 : ‖star u ⬝ᵥ (A *ᵥ u)‖ ≤ ‖A‖ := by
        have := norm_dotProduct_mulVec_le A u u
        rwa [hu, mul_one, mul_one] at this
      have h2 : -(rayleigh A u) ≤ ‖star u ⬝ᵥ (A *ᵥ u)‖ := by
        rw [rayleigh]
        calc -(star u ⬝ᵥ (A *ᵥ u)).re ≤ |(star u ⬝ᵥ (A *ᵥ u)).re| := neg_le_abs _
          _ ≤ ‖star u ⬝ᵥ (A *ᵥ u)‖ := Complex.abs_re_le_norm _
      linarith

/-- Lean implementation helper.

Source prerequisite recovered from context: for a positive-semidefinite matrix the
spectral norm is `λ_max` (used at §1.6.3 "Extract the spectral norm" and §2.2.6). -/
theorem posSemidef_l2_opNorm_eq_lambdaMax (hM : A.PosSemidef) :
    ‖A‖ = lambdaMax hM.1 := by
  rw [l2_opNorm_eq_max_lambda hM.1, max_eq_left]
  cases isEmpty_or_nonempty n
  · rw [lambdaMax_of_isEmpty, lambdaMin_of_isEmpty, neg_zero]
  · have h1 : 0 ≤ lambdaMin hM.1 :=
      le_lambdaMin hM.1 fun i => hM.eigenvalues_nonneg i
    have h2 := lambdaMin_le_lambdaMax hM.1
    linarith

end Norms

section Trace

/-- Lean implementation helper.

Source prerequisite recovered from context (needed for (2.1.16) and Chapter 3):
the trace of a standard matrix function is the sum of `f` over the eigenvalues. -/
theorem trace_cfc_eq_sum (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace = ((∑ i, f (hA.eigenvalues i) : ℝ) : ℂ) := by
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc]
  rw [Unitary.conjStarAlgAut_apply]
  have h1 : ((hA.eigenvectorUnitary : Matrix n n ℂ) *
      diagonal (RCLike.ofReal ∘ f ∘ hA.eigenvalues) *
      (star hA.eigenvectorUnitary : Matrix n n ℂ)).trace =
      (diagonal (RCLike.ofReal ∘ f ∘ hA.eigenvalues)).trace := by
    rw [Matrix.trace_mul_cycle]
    have h2 : (star hA.eigenvectorUnitary : Matrix n n ℂ) *
        (hA.eigenvectorUnitary : Matrix n n ℂ) = 1 := Unitary.coe_star_mul_self _
    rw [Matrix.mul_assoc]
    rw [show ((star hA.eigenvectorUnitary : Matrix n n ℂ) *
      ((hA.eigenvectorUnitary : Matrix n n ℂ) *
        diagonal (RCLike.ofReal ∘ f ∘ hA.eigenvalues))) =
      diagonal (RCLike.ofReal ∘ f ∘ hA.eigenvalues) from by
        rw [← Matrix.mul_assoc, h2, Matrix.one_mul]]
  rw [h1, Matrix.trace_diagonal]
  push_cast
  rfl

end Trace

end MatrixConcentration


set_option linter.unusedSectionVars false

/-!
# The semidefinite partial order (Tropp §2.1.8)

Formalizes the material of §2.1.8, pp. 20–21. The order `A ≼ H` of eq. (2.1.11)
`2.1.11` is Mathlib's scoped Loewner order (`open scoped MatrixOrder`):
`A ≤ H ↔ (H - A).PosSemidef` (`Matrix.le_iff`), and Mathlib's `Matrix.instPartialOrder`
establishes the proof obligation that ≼ is a genuine partial order (reflexivity,
transitivity, and — the substantive part — antisymmetry).

* `conjugation_rule` — **Proposition 2.1.1** (stated without proof in the source);
* `posSemidef_iff_isHermitian_quadratic` — book eq. (2.1.9) in the book's quantifier form;
* `posSemidef_iff_exists_eigenvalues_nonneg`, `posDef_iff_exists_eigenvalues_pos` —
  the two prose equivalences of §2.1.8 ("Equivalently, …");
* `posSemidef_sq`, `posDef_sq_of_det_ne_zero` — "the square of an Hermitian matrix is
  always positive semidefinite. The square of a nonsingular Hermitian matrix is always
  positive definite" (p. 21);
* `posSemidef_smul_nonneg`, `isClosed_posSemidef` — the closed-convex-cone facts of
  p. 21, proved by the book's own halfspace-intersection argument (`PosSemidef.add`
  supplies convexity from Mathlib);
* `posDef_stable_under_hermitian_perturbation` — openness of the positive-definite
  cone (p. 21, "an (open) convex cone"), phrased metrically;
* `posSemidef_diagonal_real_iff` — "For a diagonal matrix Λ, the expression Λ ≽ 0 means
  that each entry of Λ is nonnegative" (p. 21);
* `lambdaMax_le_trace_re_of_posSemidef` — book eq. (2.1.13) `2.1.13`;
* `norm_le_norm_of_loewner_le` — the implicit lemma of §1.6.3 ("Extract the spectral
  norm"): `0 ≼ M ≼ N` implies `‖M‖ ≤ ‖N‖`.
-/

namespace MatrixConcentration

open Matrix WithLp Finset
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
variable {A B H M N : Matrix n n ℂ}

/-- **Book Proposition 2.1.1 (Conjugation Rule)**, §2.1.8, eq. (2.1.12).

Explicit source declaration; the source states it without proof ("a simple fact whose
importance cannot be overstated"). `B` may be rectangular ("a general matrix with
compatible dimensions"). Reconstructed proof via Mathlib's
`PosSemidef.mul_mul_conjTranspose_same`.

Author note: Lean proves the rule for an arbitrary rectangular conjugating matrix, stronger than the square-matrix formulation used in the book. -/
theorem conjugation_rule (hAH : A ≤ H) (B : Matrix m n ℂ) :
    B * A * Bᴴ ≤ B * H * Bᴴ := by
  rw [Matrix.le_iff] at hAH ⊢
  have h1 := hAH.mul_mul_conjTranspose_same B
  have h2 : B * H * Bᴴ - B * A * Bᴴ = B * (H - A) * Bᴴ := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
  rwa [h2]

/-- **Book equation (2.1.9).**

`2.1.9` (§2.1.8): a matrix is positive semidefinite iff
it is Hermitian and `u*Au ≥ 0` for every vector `u`. Mathlib correspondence lemma in the
book's exact quantifier form (the quadratic form of a Hermitian matrix is real, so the
inequality is read on the real part). -/
theorem posSemidef_iff_isHermitian_quadratic :
    A.PosSemidef ↔ A.IsHermitian ∧ ∀ u : n → ℂ, 0 ≤ (star u ⬝ᵥ (A *ᵥ u)).re := by
  constructor
  · exact fun h => ⟨h.1, fun u => h.re_dotProduct_nonneg u⟩
  · rintro ⟨hH, hq⟩
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨hH, fun x => ?_⟩
    rw [star_dotProduct_mulVec_eq_rayleigh hH x]
    exact Complex.zero_le_real.mpr (hq x)

/-- **Book §2.1.8, p. 20.**  "Equivalently, a matrix A is positive semidefinite when it is
Hermitian and its eigenvalues are all nonnegative." Explicit (prose) equivalence. -/
theorem posSemidef_iff_exists_eigenvalues_nonneg :
    A.PosSemidef ↔ ∃ h : A.IsHermitian, ∀ i, 0 ≤ h.eigenvalues i := by
  constructor
  · exact fun h => ⟨h.1, h.eigenvalues_nonneg⟩
  · rintro ⟨h, he⟩
    exact h.posSemidef_iff_eigenvalues_nonneg.mpr he

/-- **Book equation (2.1.10).**

`2.1.10` + p. 21: "Equivalently, A is positive definite
when it is Hermitian and its eigenvalues are all positive." Explicit (prose)
equivalence. -/
theorem posDef_iff_exists_eigenvalues_pos :
    A.PosDef ↔ ∃ h : A.IsHermitian, ∀ i, 0 < h.eigenvalues i := by
  constructor
  · exact fun h => ⟨h.1, h.eigenvalues_pos⟩
  · rintro ⟨h, he⟩
    exact h.posDef_iff_eigenvalues_pos.mpr he

/-- **Book §2.1.8, p. 21.**  "the square of an Hermitian matrix is always positive
semidefinite." Implicit source declaration. -/
theorem posSemidef_sq (hA : A.IsHermitian) : (A * A).PosSemidef := by
  have h := Matrix.posSemidef_self_mul_conjTranspose A
  rwa [hA] at h

/-- **Book §2.1.8, p. 21.**  "The square of a nonsingular Hermitian matrix is always positive
definite." Implicit source declaration. -/
theorem posDef_sq_of_det_ne_zero (hA : A.IsHermitian) (hdet : A.det ≠ 0) :
    (A * A).PosDef := by
  refine ((posSemidef_sq hA).posDef_iff_det_ne_zero).mpr ?_
  rw [Matrix.det_mul]
  exact mul_ne_zero hdet hdet

/-- **Book §2.1.8, p. 21 (cone property).**  a nonnegative real multiple of a positive-
semidefinite matrix is positive semidefinite. Explicit (prose) statement. -/
theorem posSemidef_smul_nonneg (hA : A.PosSemidef) {α : ℝ} (hα : 0 ≤ α) :
    (α • A).PosSemidef :=
  hA.smul hα

/-- **Book §2.1.8, p. 21.**  "The family of positive-semidefinite matrices in ℍ_d forms a
closed convex cone." The closedness, proved by the book's own argument: the psd set is
the intersection of the (closed) Hermitian subspace with closed halfspaces indexed by
vectors `u`. Convexity is Mathlib's `Matrix.PosSemidef.add`/`smul`. Explicit (prose)
statement; closedness is w.r.t. the (product) topology of the matrix space. -/
theorem isClosed_posSemidef : IsClosed {A : Matrix n n ℂ | A.PosSemidef} := by
  have h1 : {A : Matrix n n ℂ | A.PosSemidef} =
      {A : Matrix n n ℂ | A.IsHermitian} ∩
        ⋂ u : n → ℂ, {A : Matrix n n ℂ | 0 ≤ (star u ⬝ᵥ (A *ᵥ u)).re} := by
    ext A
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    exact posSemidef_iff_isHermitian_quadratic
  rw [h1]
  refine IsClosed.inter ?_ (isClosed_iInter fun u => ?_)
  · have h2 : {A : Matrix n n ℂ | A.IsHermitian} =
        (fun A : Matrix n n ℂ => Aᴴ - A) ⁻¹' {0} := by
      ext A
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff, sub_eq_zero]
      rfl
    rw [h2]
    have hcont : Continuous fun A : Matrix n n ℂ => Aᴴ - A := by
      refine Continuous.sub ?_ continuous_id
      refine continuous_pi fun i => continuous_pi fun j => ?_
      have h3 : (fun A : Matrix n n ℂ => Aᴴ i j) =
          fun A : Matrix n n ℂ => (starRingEnd ℂ) (A j i) := rfl
      rw [h3]
      exact Complex.continuous_conj.comp
        ((continuous_apply i).comp (continuous_apply j))
    exact isClosed_singleton.preimage hcont
  · have hlin : (fun A : Matrix n n ℂ => star u ⬝ᵥ (A *ᵥ u)) =
        fun A : Matrix n n ℂ => ∑ i, (star u) i * ∑ j, A i j * u j := by
      funext A
      rfl
    have hcont : Continuous fun A : Matrix n n ℂ => (star u ⬝ᵥ (A *ᵥ u)).re := by
      refine Complex.continuous_re.comp ?_
      rw [hlin]
      refine continuous_finsetSum _ fun i _ => Continuous.mul continuous_const ?_
      exact continuous_finsetSum _ fun j _ =>
        Continuous.mul ((continuous_apply j).comp (continuous_apply i)) continuous_const
    exact isClosed_le continuous_const hcont

/-- Lean implementation helper: nonzero vectors have positive ℓ₂ norm. -/
lemma l2norm_pos_of_ne_zero {x : n → ℂ} (hx : x ≠ 0) : 0 < l2norm x := by
  have hz : (toLp 2 x : EuclideanSpace ℂ n) ≠ 0 := by
    intro h
    apply hx
    have h' := congrArg ofLp h
    simpa using h'
  simpa [l2norm] using norm_pos_iff.mpr hz

/-- **Book §2.1.8, p. 21.**  "the family of positive-definite matrices in ℍ_d forms an
(open) convex cone." Implicit source declaration ("similar considerations show").
Openness within the Hermitian matrices, phrased metrically: every Hermitian matrix
sufficiently close (in spectral norm) to a positive-definite matrix is positive
definite. Convexity is Mathlib's `Matrix.PosDef.add`/`smul`. -/
theorem posDef_stable_under_hermitian_perturbation (hA : A.PosDef) :
    ∃ ε > 0, ∀ H : Matrix n n ℂ, H.IsHermitian → ‖H - A‖ < ε → H.PosDef := by
  cases isEmpty_or_nonempty n
  · refine ⟨1, one_pos, fun H hH _ => ?_⟩
    refine Matrix.PosDef.of_dotProduct_mulVec_pos hH fun x hx => ?_
    exact absurd (funext fun i => (IsEmpty.false i).elim) hx
  · refine ⟨lambdaMin hA.1, ?_, fun H hH hnear => ?_⟩
    · obtain ⟨i, hi⟩ := exists_eigenvalues_eq_lambdaMin hA.1
      rw [← hi]
      exact hA.eigenvalues_pos i
    · refine Matrix.PosDef.of_dotProduct_mulVec_pos hH fun x hx => ?_
      rw [star_dotProduct_mulVec_eq_rayleigh hH x]
      rw [Complex.zero_lt_real]
      have hxpos : 0 < l2norm x := l2norm_pos_of_ne_zero hx
      have h1 : lambdaMin hA.1 * l2norm x ^ 2 ≤ rayleigh A x := lambdaMin_le_rayleigh hA.1 x
      have h2 : rayleigh H x = rayleigh A x + rayleigh (H - A) x := by
        rw [rayleigh_sub]
        ring
      have h3 : -(‖H - A‖ * l2norm x ^ 2) ≤ rayleigh (H - A) x := by
        have h4 : |rayleigh (H - A) x| ≤ ‖H - A‖ * l2norm x ^ 2 := by
          calc |rayleigh (H - A) x| = |(star x ⬝ᵥ ((H - A) *ᵥ x)).re| := rfl
            _ ≤ ‖star x ⬝ᵥ ((H - A) *ᵥ x)‖ := Complex.abs_re_le_norm _
            _ ≤ ‖H - A‖ * l2norm x * l2norm x := norm_dotProduct_mulVec_le _ x x
            _ = ‖H - A‖ * l2norm x ^ 2 := by ring
        linarith [neg_abs_le (rayleigh (H - A) x)]
      have h5 : ‖H - A‖ * l2norm x ^ 2 < lambdaMin hA.1 * l2norm x ^ 2 := by
        have := sq_pos_of_ne_zero (a := l2norm x) (by positivity)
        exact mul_lt_mul_of_pos_right hnear (by positivity)
      linarith

/-- **Book §2.1.8, p. 21.**  "For a diagonal matrix Λ, the expression Λ ≽ 0 means that each
entry of Λ is nonnegative." Explicit (prose) statement, for real diagonals as in the
book's eigenvalue matrices. -/
theorem posSemidef_diagonal_real_iff (d : n → ℝ) :
    (diagonal (RCLike.ofReal ∘ d) : Matrix n n ℂ).PosSemidef ↔ ∀ i, 0 ≤ d i := by
  rw [Matrix.posSemidef_diagonal_iff]
  constructor
  · intro h i
    have h1 := h i
    rw [Function.comp_apply, ofReal_eq_complex] at h1
    exact Complex.zero_le_real.mp h1
  · intro h i
    rw [Function.comp_apply, ofReal_eq_complex]
    exact Complex.zero_le_real.mpr (h i)

/-- Lean implementation helper: the trace of a Hermitian matrix is (the coercion of)
the real number `∑ λᵢ`; book §2.1.7, "the trace of an Hermitian matrix equals the sum
of its eigenvalues" read on the real part. -/
lemma trace_re_eq_sum_eigenvalues (hA : A.IsHermitian) :
    (A.trace).re = ∑ i, hA.eigenvalues i := by
  rw [hA.trace_eq_sum_eigenvalues, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ofReal_eq_complex]
  exact Complex.ofReal_re _

/-- **Book §2.1.7, p. 20 (display around (2.1.7)).**  the trace of a Hermitian matrix equals
the sum of its eigenvalues. Implicit source declaration (ℂ-valued form). -/
theorem trace_eq_sum_eigenvalues_complex (hA : A.IsHermitian) :
    A.trace = ((∑ i, hA.eigenvalues i : ℝ) : ℂ) := by
  rw [hA.trace_eq_sum_eigenvalues]
  simp only [ofReal_eq_complex]
  norm_cast

/-- **Book equation (2.1.13).**

`2.1.13` (§2.1.8): `λ_max(A) ≤ tr A` for positive-
semidefinite `A`. Explicit (unnumbered) source statement; source sketches the proof
("follows from the definition … and the fact that the trace equals the sum of the
eigenvalues"), which is the proof formalized here. -/
theorem lambdaMax_le_trace_re_of_posSemidef (hM : M.PosSemidef) :
    lambdaMax hM.1 ≤ (M.trace).re := by
  rw [trace_re_eq_sum_eigenvalues hM.1]
  cases isEmpty_or_nonempty n
  · rw [lambdaMax_of_isEmpty]
    simp
  · obtain ⟨i, hi⟩ := exists_eigenvalues_eq_lambdaMax hM.1
    rw [← hi]
    exact Finset.single_le_sum (f := fun j => hM.1.eigenvalues j)
      (fun j _ => hM.eigenvalues_nonneg j) (Finset.mem_univ i)

/-- **Book §1.6.3, p. 11.** The implicit lemma used when the book extracts
the spectral norm: it is monotone on the positive-semidefinite cone,
`0 ≼ M ≼ N` implies `‖M‖ ≤ ‖N‖`. Implicit source declaration. -/
theorem norm_le_norm_of_loewner_le (hM : M.PosSemidef) (hMN : M ≤ N) : ‖M‖ ≤ ‖N‖ := by
  have hN : N.PosSemidef := by
    rw [← Matrix.nonneg_iff_posSemidef] at hM ⊢
    exact hM.trans hMN
  rw [posSemidef_l2_opNorm_eq_lambdaMax hM, posSemidef_l2_opNorm_eq_lambdaMax hN]
  exact lambdaMax_le_of_loewner_le hM.1 hN.1 hMN

/-- Lean implementation helper: trace monotonicity in the Loewner order. -/
lemma trace_re_le_of_loewner_le (h : M ≤ N) : (M.trace).re ≤ (N.trace).re := by
  have h1 : (0 : ℂ) ≤ (N - M).trace := (Matrix.le_iff.mp h).trace_nonneg
  have h2 : 0 ≤ ((N - M).trace).re := (RCLike.nonneg_iff.mp h1).1
  rw [Matrix.trace_sub, Complex.sub_re] at h2
  linarith

end MatrixConcentration
